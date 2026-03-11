use std::collections::{BTreeMap, BTreeSet, HashMap};

use sbpf_common::{
    instruction::Instruction,
    opcode::Opcode,
};

use crate::cfg::ControlFlowGraph;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DfgNode {
    Instruction(usize),
    Phi(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DataResource {
    Register(u8),
    Memory,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DfgEdgeKind {
    Filled,
    Empty,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DfgEdge {
    pub source: DfgNode,
    pub destination: DfgNode,
    pub kind: DfgEdgeKind,
    pub resource: DataResource,
}

pub struct DataFlowGraph {
    pub forward: BTreeMap<DfgNode, BTreeSet<DfgEdge>>,
    pub reverse: BTreeMap<DfgNode, BTreeSet<DfgEdge>>,
}

impl DataFlowGraph {
    pub fn build(instructions: &[Instruction], cfg: &ControlFlowGraph) -> Self {
        let (block_outputs, mut forward) =
            intra_block_data_flow(instructions, cfg);
        inter_block_data_flow(cfg, block_outputs, &mut forward);

        // Build reverse index.
        let mut reverse: BTreeMap<DfgNode, BTreeSet<DfgEdge>> = BTreeMap::new();
        for edges in forward.values() {
            for edge in edges {
                reverse
                    .entry(edge.destination.clone())
                    .or_default()
                    .insert(edge.clone());
            }
        }

        Self { forward, reverse }
    }
}

type Forward = BTreeMap<DfgNode, BTreeSet<DfgEdge>>;
type BlockOutputs = BTreeMap<usize, HashMap<DataResource, usize>>;

fn intra_block_data_flow(
    instructions: &[Instruction],
    cfg: &ControlFlowGraph,
) -> (BlockOutputs, Forward) {
    let mut forward: Forward = BTreeMap::new();
    let mut block_outputs: BlockOutputs = BTreeMap::new();

    for (&block_start, block) in &cfg.blocks {
        let mut last_writer: HashMap<DataResource, usize> = HashMap::new();

        for pc in block.start..block.end {
            let inst = &instructions[pc];
            process_instruction(inst, pc, block_start, &mut last_writer, &mut forward);
        }

        block_outputs.insert(block_start, last_writer);
    }

    (block_outputs, forward)
}

fn bind(
    pc: usize,
    block_start: usize,
    is_write: bool,
    resource: DataResource,
    last_writer: &mut HashMap<DataResource, usize>,
    forward: &mut Forward,
) {
    let source = if let Some(&writer_pc) = last_writer.get(&resource) {
        DfgNode::Instruction(writer_pc)
    } else {
        DfgNode::Phi(block_start)
    };

    let destination = DfgNode::Instruction(pc);
    let kind = if is_write {
        DfgEdgeKind::Empty
    } else {
        DfgEdgeKind::Filled
    };

    forward.entry(source.clone()).or_default().insert(DfgEdge {
        source,
        destination,
        kind,
        resource: resource.clone(),
    });

    if is_write {
        last_writer.insert(resource, pc);
    }
}

#[inline]
fn read_reg(
    pc: usize,
    block_start: usize,
    reg: u8,
    last_writer: &mut HashMap<DataResource, usize>,
    forward: &mut Forward,
) {
    bind(pc, block_start, false, DataResource::Register(reg), last_writer, forward);
}

#[inline]
fn write_reg(
    pc: usize,
    block_start: usize,
    reg: u8,
    last_writer: &mut HashMap<DataResource, usize>,
    forward: &mut Forward,
) {
    bind(pc, block_start, true, DataResource::Register(reg), last_writer, forward);
}

#[inline]
fn read_mem(
    pc: usize,
    block_start: usize,
    last_writer: &mut HashMap<DataResource, usize>,
    forward: &mut Forward,
) {
    bind(pc, block_start, false, DataResource::Memory, last_writer, forward);
}

#[inline]
fn write_mem(
    pc: usize,
    block_start: usize,
    last_writer: &mut HashMap<DataResource, usize>,
    forward: &mut Forward,
) {
    bind(pc, block_start, true, DataResource::Memory, last_writer, forward);
}

fn process_instruction(
    inst: &Instruction,
    pc: usize,
    block_start: usize,
    last_writer: &mut HashMap<DataResource, usize>,
    forward: &mut Forward,
) {
    use Opcode::*;

    let dst = inst.dst.as_ref().map(|r| r.n);
    let src = inst.src.as_ref().map(|r| r.n);

    match inst.opcode {
        Ldxb | Ldxh | Ldxw | Ldxdw => {
            // dst = mem[src + off]
            read_mem(pc, block_start, last_writer, forward);
            read_reg(pc, block_start, src.unwrap(), last_writer, forward);
            write_reg(pc, block_start, dst.unwrap(), last_writer, forward);
        }

        // Load immediate (lddw)
        Lddw => {
            write_reg(pc, block_start, dst.unwrap(), last_writer, forward);
        }

        Stb | Sth | Stw | Stdw => {
            // mem[dst + off] = imm
            read_reg(pc, block_start, dst.unwrap(), last_writer, forward);
            write_mem(pc, block_start, last_writer, forward);
        }

        Stxb | Stxh | Stxw | Stxdw => {
            // mem[dst + off] = src
            read_reg(pc, block_start, src.unwrap(), last_writer, forward);
            read_reg(pc, block_start, dst.unwrap(), last_writer, forward);
            write_mem(pc, block_start, last_writer, forward);
        }

        Add32Imm | Sub32Imm | Mul32Imm | Div32Imm | Or32Imm | And32Imm
        | Lsh32Imm | Rsh32Imm | Mod32Imm | Xor32Imm | Arsh32Imm
        | Lmul32Imm | Udiv32Imm | Urem32Imm | Sdiv32Imm | Srem32Imm
        | Add64Imm | Sub64Imm | Mul64Imm | Div64Imm | Or64Imm | And64Imm
        | Lsh64Imm | Rsh64Imm | Mod64Imm | Xor64Imm | Arsh64Imm | Hor64Imm
        | Lmul64Imm | Uhmul64Imm | Udiv64Imm | Urem64Imm | Shmul64Imm
        | Sdiv64Imm | Srem64Imm | Le | Be | Neg32 | Neg64 => {
            // dst = dst op imm  (read then write dst)
            read_reg(pc, block_start, dst.unwrap(), last_writer, forward);
            write_reg(pc, block_start, dst.unwrap(), last_writer, forward);
        }

        Mov32Imm | Mov64Imm => {
            write_reg(pc, block_start, dst.unwrap(), last_writer, forward);
        }

        Add32Reg | Sub32Reg | Mul32Reg | Div32Reg | Or32Reg | And32Reg
        | Lsh32Reg | Rsh32Reg | Mod32Reg | Xor32Reg | Arsh32Reg
        | Lmul32Reg | Udiv32Reg | Urem32Reg | Sdiv32Reg | Srem32Reg
        | Add64Reg | Sub64Reg | Mul64Reg | Div64Reg | Or64Reg | And64Reg
        | Lsh64Reg | Rsh64Reg | Mod64Reg | Xor64Reg | Arsh64Reg
        | Lmul64Reg | Uhmul64Reg | Udiv64Reg | Urem64Reg | Shmul64Reg
        | Sdiv64Reg | Srem64Reg => {
            read_reg(pc, block_start, src.unwrap(), last_writer, forward);
            read_reg(pc, block_start, dst.unwrap(), last_writer, forward);
            write_reg(pc, block_start, dst.unwrap(), last_writer, forward);
        }

        Mov32Reg | Mov64Reg => {
            read_reg(pc, block_start, src.unwrap(), last_writer, forward);
            write_reg(pc, block_start, dst.unwrap(), last_writer, forward);
        }

        JeqImm | JgtImm | JgeImm | JltImm | JleImm | JsetImm | JneImm
        | JsgtImm | JsgeImm | JsltImm | JsleImm => {
            read_reg(pc, block_start, dst.unwrap(), last_writer, forward);
        }

        JeqReg | JgtReg | JgeReg | JltReg | JleReg | JsetReg | JneReg
        | JsgtReg | JsgeReg | JsltReg | JsleReg => {
            read_reg(pc, block_start, dst.unwrap(), last_writer, forward);
            read_reg(pc, block_start, src.unwrap(), last_writer, forward);
        }

        Ja => {}

        Call => {
            // callx uses dst; call imm has no register source.
            // Both clobber r0 (return value) and r1-r5 (args/scratch).
            read_mem(pc, block_start, last_writer, forward);
            write_mem(pc, block_start, last_writer, forward);
            // Caller-saved: r0-r5 are clobbered.
            for reg in 0u8..=5 {
                read_reg(pc, block_start, reg, last_writer, forward);
                write_reg(pc, block_start, reg, last_writer, forward);
            }
            // Frame pointer r10 is also preserved across calls; read it.
            read_reg(pc, block_start, 10, last_writer, forward);
        }

        Callx => {
            // The target register is read (encoded in dst for Blueshift).
            if let Some(d) = dst {
                read_reg(pc, block_start, d, last_writer, forward);
            }
            read_mem(pc, block_start, last_writer, forward);
            write_mem(pc, block_start, last_writer, forward);
            for reg in 0u8..=5 {
                read_reg(pc, block_start, reg, last_writer, forward);
                write_reg(pc, block_start, reg, last_writer, forward);
            }
            read_reg(pc, block_start, 10, last_writer, forward);
        }

        Exit => {
            read_mem(pc, block_start, last_writer, forward);
            for reg in [0u8, 6, 7, 8, 9, 10] {
                read_reg(pc, block_start, reg, last_writer, forward);
            }
        }
    }
}

fn inter_block_data_flow(
    cfg: &ControlFlowGraph,
    block_outputs: BlockOutputs,
    forward: &mut Forward,
) {
    let mut continue_propagation = true;
    while continue_propagation {
        continue_propagation = false;

        for &block_start in cfg.topological_order.iter().rev() {
            if !forward.contains_key(&DfgNode::Phi(block_start)) {
                continue;
            }

            let block = &cfg.blocks[&block_start];
            let mut edges: BTreeSet<DfgEdge> = BTreeSet::new();
            // Swap out to avoid borrow conflict.
            std::mem::swap(
                forward.entry(DfgNode::Phi(block_start)).or_default(),
                &mut edges,
            );

            for &predecessor in &block.predecessors {
                let pred_outputs = &block_outputs[&predecessor];
                for edge in &edges {
                    let mut source_is_phi = false;
                    let source = if let Some(&writer_pc) = pred_outputs.get(&edge.resource) {
                        DfgNode::Instruction(writer_pc)
                    } else {
                        source_is_phi = true;
                        DfgNode::Phi(predecessor)
                    };

                    let mut new_edge = edge.clone();
                    // If the block has multiple predecessors, destination stays
                    // as a Phi; otherwise it can be rewired to the instruction.
                    if block.predecessors.len() != 1 {
                        new_edge.destination = DfgNode::Phi(block_start);
                    }
                    new_edge.source = source.clone();

                    if forward
                        .entry(source.clone())
                        .or_default()
                        .insert(new_edge)
                        && source_is_phi
                        && source != DfgNode::Phi(block_start)
                    {
                        continue_propagation = true;
                    }
                }
            }

            // Check for any new edges that appeared in the Phi slot.
            let phi_edges: BTreeSet<DfgEdge> = forward
                .get(&DfgNode::Phi(block_start))
                .cloned()
                .unwrap_or_default();
            for edge in phi_edges {
                if edges.insert(edge) {
                    continue_propagation = true;
                }
            }

            std::mem::swap(
                forward.entry(DfgNode::Phi(block_start)).or_default(),
                &mut edges,
            );
        }
    }

    // Remove Phi-nodes for blocks that have exactly one predecessor
    // (they were never real merge points).
    let single_pred_blocks: Vec<usize> = cfg
        .blocks
        .iter()
        .filter(|(_, b)| b.predecessors.len() == 1)
        .map(|(&pc, _)| pc)
        .collect();

    for pc in single_pred_blocks {
        forward.remove(&DfgNode::Phi(pc));
    }
}
