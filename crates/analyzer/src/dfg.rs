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

#[cfg(test)]
mod tests {
    use crate::{Analysis, dfg::{DataResource, DfgEdge, DfgEdgeKind, DfgNode}};
    use crate::tests::{ELF_WITH_LABELS, analyze_asm};

    #[test]
    fn with_labels_dfg_lddw_feeds_call() {
        let a = Analysis::from_elf_bytes(ELF_WITH_LABELS).unwrap();
        // lddw r1,1 at PC 2 writes r1; call sol_log_64_ at PC 3 reads it.
        let edges_into_3: Vec<&DfgEdge> = a.dfg.forward.values().flatten()
            .filter(|e| e.destination == DfgNode::Instruction(3))
            .collect();
        assert!(
            edges_into_3.iter().any(|e| e.kind == DfgEdgeKind::Filled
                && e.resource == DataResource::Register(1)
                && e.source == DfgNode::Instruction(2)),
            "expected Filled r1 edge from PC 2 to PC 3, got {edges_into_3:?}"
        );
    }

    #[test]
    fn with_labels_dfg_non_empty() {
        let a = Analysis::from_elf_bytes(ELF_WITH_LABELS).unwrap();
        assert!(!a.dfg.forward.is_empty());
    }

    #[test]
    fn v3_dfg_lddw_feeds_call() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            lddw r1, 1
            call sol_log_64_
            exit
        "#);
        let edges: Vec<&DfgEdge> = a.dfg.forward.values().flatten()
            .filter(|e| e.destination == DfgNode::Instruction(1)
                && e.resource == DataResource::Register(1)
                && e.kind == DfgEdgeKind::Filled)
            .collect();
        assert!(!edges.is_empty(), "expected Filled r1 edge PC 0→1, got none");
    }

    #[test]
    fn dfg_register_read_after_write() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r1, 42
            mov64 r2, r1
            exit
        "#);
        let filled: Vec<&DfgEdge> = a.dfg.forward.values().flatten()
            .filter(|e| e.kind == DfgEdgeKind::Filled && e.resource == DataResource::Register(1))
            .collect();
        assert!(!filled.is_empty(), "expected a Filled r1 edge, got none");
        let e = filled[0];
        assert_eq!(e.source, DfgNode::Instruction(0));
        assert_eq!(e.destination,   DfgNode::Instruction(1));
    }

    #[test]
    fn dfg_write_after_write_edge_exists() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r1, 1
            mov64 r1, 2
            exit
        "#);
        let waw: Vec<&DfgEdge> = a.dfg.forward.values().flatten()
            .filter(|e| e.resource == DataResource::Register(1)
                && e.source == DfgNode::Instruction(0)
                && e.destination   == DfgNode::Instruction(1))
            .collect();
        assert!(!waw.is_empty(), "expected WAW edge on r1 from PC 0 to PC 1");
    }

    #[test]
    fn dfg_mov_imm_is_pure_write() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r1, 99
            exit
        "#);
        let self_read: Vec<&DfgEdge> = a.dfg.forward.values().flatten()
            .filter(|e| e.source == DfgNode::Instruction(0)
                && e.destination == DfgNode::Instruction(0)
                && e.resource == DataResource::Register(1))
            .collect();
        assert!(self_read.is_empty(), "mov imm must not create a self-read edge");
    }

    #[test]
    fn dfg_memory_store_reads_register() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r1, 42
            stxdw [r10-8], r1
            exit
        "#);
        let filled: Vec<&DfgEdge> = a.dfg.forward.values().flatten()
            .filter(|e| e.destination == DfgNode::Instruction(1)
                && e.kind == DfgEdgeKind::Filled
                && e.resource == DataResource::Register(1))
            .collect();
        assert!(!filled.is_empty(), "stxdw must read r1 from PC 0");
    }

    #[test]
    fn dfg_memory_load_reads_memory() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            ldxdw r1, [r10-8]
            exit
        "#);
        let mem: Vec<&DfgEdge> = a.dfg.forward.values().flatten()
            .filter(|e| e.destination == DfgNode::Instruction(0)
                && matches!(e.resource, DataResource::Memory))
            .collect();
        assert!(!mem.is_empty(), "ldxdw must have an incoming memory edge");
    }

    #[test]
    fn dfg_conditional_jump_reads_register() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r2, 5
            jeq r2, 5, done
            mov64 r0, 1
        done:
            exit
        "#);
        let filled: Vec<&DfgEdge> = a.dfg.forward.values().flatten()
            .filter(|e| e.destination == DfgNode::Instruction(1)
                && e.kind == DfgEdgeKind::Filled
                && e.resource == DataResource::Register(2))
            .collect();
        assert!(!filled.is_empty(), "jeq imm must read r2");
    }

    #[test]
    fn dfg_conditional_jump_reg_reads_both_registers() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r1, 3
            mov64 r2, 3
            jeq r1, r2, done
            mov64 r0, 1
        done:
            exit
        "#);
        let reads_r1 = a.dfg.forward.values().flatten()
            .any(|e| e.destination == DfgNode::Instruction(2)
                && e.resource == DataResource::Register(1)
                && e.kind == DfgEdgeKind::Filled);
        let reads_r2 = a.dfg.forward.values().flatten()
            .any(|e| e.destination == DfgNode::Instruction(2)
                && e.resource == DataResource::Register(2)
                && e.kind == DfgEdgeKind::Filled);
        assert!(reads_r1, "jeq reg must read r1");
        assert!(reads_r2, "jeq reg must read r2");
    }

    #[test]
    fn dfg_phi_node_at_merge_point() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r0, 1
            jeq r0, 1, merge
            mov64 r1, 0
        merge:
            mov64 r2, r1
            exit
        "#);
        let has_phi = a.dfg.forward.keys()
            .any(|n| matches!(n, DfgNode::Phi(_)));
        assert!(has_phi, "merge block must have at least one Phi node");
    }

    #[test]
    fn dfg_forward_reverse_consistent() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r1, 1
            mov64 r2, r1
            add64 r2, r1
            exit
        "#);
        for (from_node, edges) in &a.dfg.forward {
            for edge in edges {
                let reverse_has = a.dfg.reverse.get(&edge.destination)
                    .map(|rev| rev.iter().any(|e| e.source == *from_node && e.resource == edge.resource))
                    .unwrap_or(false);
                assert!(reverse_has, "forward edge {from_node:?}→{:?} missing from reverse", edge.destination);
            }
        }
    }

    #[test]
    fn counter_example_dfg_non_empty() {
        let src = include_str!(
            "../../../examples/sbpf-asm-counter/src/sbpf-asm-counter/sbpf-asm-counter.s"
        );
        let a = analyze_asm(src);
        assert!(!a.dfg.forward.is_empty(), "DFG must be non-empty");
    }
}