use std::collections::{BTreeMap, BTreeSet};

use sbpf_common::{
    instruction::Instruction,
    opcode::{Opcode},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CfgEdgeKind {
    Fallthrough,
    Jump,
    BranchTaken,
    BranchNotTaken,
    Call,
    CallIndirect,
}

#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub label: String,
    pub start: usize,
    pub end: usize,
    pub predecessors: Vec<usize>,
    pub successors: Vec<usize>,
    pub topo_index: TopoIndex,
    pub dominator_parent: usize,
    pub dominated_children: Vec<usize>,
}

impl Default for BasicBlock {
    fn default() -> Self {
        Self {
            label: String::new(),
            start: 0,
            end: 0,
            predecessors: Vec::new(),
            successors: Vec::new(),
            topo_index: TopoIndex::default(),
            dominator_parent: usize::MAX,
            dominated_children: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TopoIndex {
    pub scc_id: usize,
    pub discovery: usize,
}

impl Default for TopoIndex {
    fn default() -> Self {
        Self {
            scc_id: usize::MAX,
            discovery: usize::MAX,
        }
    }
}

impl PartialOrd for TopoIndex {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TopoIndex {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.scc_id
            .cmp(&other.scc_id)
            .then(self.discovery.cmp(&other.discovery))
    }
}

pub struct ControlFlowGraph {
    pub blocks: BTreeMap<usize, BasicBlock>,
    pub topological_order: Vec<usize>,
    pub entry: usize,
}

impl ControlFlowGraph {
    pub fn build(instructions: &[Instruction]) -> Self {
        if instructions.is_empty() {
            return Self {
                blocks: BTreeMap::new(),
                topological_order: Vec::new(),
                entry: 0,
            };
        }

        let mut block_starts: BTreeSet<usize> = BTreeSet::new();
        block_starts.insert(0);

        let mut explicit_edges: BTreeMap<usize, Vec<usize>> = BTreeMap::new();

        for (pc, inst) in instructions.iter().enumerate() {
            match inst.opcode {
                Opcode::Ja => {
                    let target = jump_target(pc, inst);
                    block_starts.insert(pc + 1); // start of "dead" fall-through slot
                    if let Some(t) = target {
                        block_starts.insert(t);
                        explicit_edges.insert(pc, vec![t]);
                    } else {
                        explicit_edges.insert(pc, vec![]);
                    }
                }

                op if is_conditional_jump(op) => {
                    let ft = pc + 1; // fall-through (not-taken)
                    block_starts.insert(ft);
                    if let Some(t) = jump_target(pc, inst) {
                        block_starts.insert(t);
                        explicit_edges.insert(pc, vec![ft, t]);
                    } else {
                        explicit_edges.insert(pc, vec![ft]);
                    }
                }

                Opcode::Call => {
                    let ft = pc + 1;
                    block_starts.insert(ft);
                    explicit_edges.insert(pc, vec![ft]);
                }

                Opcode::Callx => {
                    let ft = pc + 1;
                    block_starts.insert(ft);
                    explicit_edges.insert(pc, vec![ft]);
                }

                Opcode::Exit => {
                    block_starts.insert(pc + 1);
                    explicit_edges.insert(pc, vec![]);
                }

                _ => {}
            }
        }

        let n = instructions.len();
        let valid_starts: Vec<usize> = block_starts
            .iter()
            .copied()
            .filter(|&s| s < n)
            .collect();

        let mut blocks: BTreeMap<usize, BasicBlock> = BTreeMap::new();
        for &s in &valid_starts {
            blocks.insert(s, BasicBlock::default());
        }

        let starts_vec: Vec<usize> = blocks.keys().copied().collect();
        for (i, &block_start) in starts_vec.iter().enumerate() {
            let block_end = if i + 1 < starts_vec.len() {
                starts_vec[i + 1]
            } else {
                n
            };

            let last_pc = block_end - 1;
            // Look up explicit edge from last instruction.
            let successors = if let Some(dests) = explicit_edges.get(&last_pc) {
                dests
                    .iter()
                    .copied()
                    .filter(|&d| blocks.contains_key(&d) || valid_starts.binary_search(&d).is_ok())
                    .collect::<Vec<_>>()
            } else {
                // Implicit fall-through to next block (if there is one and the
                // last instruction is not a terminator).
                if let Some(&next_start) = starts_vec.get(i + 1) {
                    vec![next_start]
                } else {
                    vec![]
                }
            };
            
            let block = blocks.get_mut(&block_start).unwrap();
            block.start = block_start;
            block.end = block_end;

            block.successors = successors;
        }

        let all_starts: Vec<usize> = blocks.keys().copied().collect();
        for src in all_starts {
            let succs: Vec<usize> = blocks[&src].successors.clone();
            for dst in succs {
                if let Some(dst_block) = blocks.get_mut(&dst) {
                    dst_block.predecessors.push(src);
                }
            }
        }

        for (&pc, block) in blocks.iter_mut() {
            block.label = if pc == 0 {
                "entrypoint".to_string()
            } else {
                format!("lbb_{pc}")
            };
        }

        let topological_order = tarjan_topo(&mut blocks);

        dominance(&mut blocks, &topological_order);

        Self {
            blocks,
            topological_order,
            entry: 0,
        }
    }
}

fn jump_target(pc: usize, inst: &Instruction) -> Option<usize> {
    use either::Either;
    let off = match &inst.off {
        Some(Either::Right(o)) => *o as isize,
        _ => return None,
    };
    // target = (pc + 1) + off
    let target = (pc as isize + 1 + off) as usize;
    Some(target)
}

fn is_conditional_jump(op: Opcode) -> bool {
    matches!(
        op,
        Opcode::JeqImm
            | Opcode::JeqReg
            | Opcode::JgtImm
            | Opcode::JgtReg
            | Opcode::JgeImm
            | Opcode::JgeReg
            | Opcode::JltImm
            | Opcode::JltReg
            | Opcode::JleImm
            | Opcode::JleReg
            | Opcode::JsetImm
            | Opcode::JsetReg
            | Opcode::JneImm
            | Opcode::JneReg
            | Opcode::JsgtImm
            | Opcode::JsgtReg
            | Opcode::JsgeImm
            | Opcode::JsgeReg
            | Opcode::JsltImm
            | Opcode::JsltReg
            | Opcode::JsleImm
            | Opcode::JsleReg
    )
}

fn tarjan_topo(blocks: &mut BTreeMap<usize, BasicBlock>) -> Vec<usize> {
    if blocks.is_empty() {
        return vec![];
    }

    let pcs: Vec<usize> = blocks.keys().copied().collect();
    let n = pcs.len();
    let pc_to_idx: BTreeMap<usize, usize> = pcs.iter().enumerate().map(|(i, &p)| (p, i)).collect();

    for (i, &pc) in pcs.iter().enumerate() {
        blocks.get_mut(&pc).unwrap().topo_index.scc_id = i;
    }

    struct NS {
        pc: usize,
        discovery: usize,
        lowlink: usize,
        scc_id: usize,
        on_stack: bool,
    }

    let mut nodes: Vec<NS> = pcs
        .iter()
        .map(|&pc| NS {
            pc,
            discovery: usize::MAX,
            lowlink: usize::MAX,
            scc_id: usize::MAX,
            on_stack: false,
        })
        .collect();

    let mut scc_id = 0usize;
    let mut scc_stack: Vec<usize> = Vec::new(); 
    let mut disc_counter = 0usize;
    let mut next_v = 1usize;
    let mut call_stack: Vec<(usize, usize)> = vec![(0, 0)]; 

    'dfs: while let Some((v, edge_idx)) = call_stack.pop() {
        if edge_idx == 0 {
            nodes[v].discovery = disc_counter;
            nodes[v].lowlink = disc_counter;
            nodes[v].on_stack = true;
            scc_stack.push(v);
            disc_counter += 1;
        }

        let succs: Vec<usize> = blocks[&nodes[v].pc]
            .successors
            .iter()
            .filter_map(|s| pc_to_idx.get(s).copied())
            .collect();

        for j in edge_idx..succs.len() {
            let w = succs[j];
            if nodes[w].discovery == usize::MAX {
                // Push continuation then recurse into w.
                call_stack.push((v, j + 1));
                call_stack.push((w, 0));
                continue 'dfs;
            } else if nodes[w].on_stack {
                nodes[v].lowlink = nodes[v].lowlink.min(nodes[w].discovery);
            }
        }

        // Root of an SCC?
        if nodes[v].discovery == nodes[v].lowlink {
            let mut idx_in_scc = 0;
            while let Some(w) = scc_stack.pop() {
                nodes[w].on_stack = false;
                nodes[w].scc_id = scc_id;
                nodes[w].discovery = idx_in_scc; // repurpose as intra-SCC index
                idx_in_scc += 1;
                if w == v {
                    break;
                }
            }
            scc_id += 1;
        }

        // Propagate lowlink to caller.
        if let Some((w, _)) = call_stack.last() {
            let lowlink_v = nodes[v].lowlink;
            nodes[*w].lowlink = nodes[*w].lowlink.min(lowlink_v);
        } else {
            // Find next unvisited root.
            loop {
                if next_v == n {
                    break 'dfs;
                }
                if nodes[next_v].discovery == usize::MAX {
                    break;
                }
                next_v += 1;
            }
            call_stack.push((next_v, 0));
            next_v += 1;
        }
    }

    for node in &nodes {
        let block = blocks.get_mut(&node.pc).unwrap();
        block.topo_index = TopoIndex {
            scc_id: node.scc_id,
            discovery: node.discovery,
        };
    }

    let mut order = pcs.clone();
    order.sort_by(|a, b| {
        blocks[b]
            .topo_index
            .cmp(&blocks[a].topo_index)
    });
    order
}

fn dominance(blocks: &mut BTreeMap<usize, BasicBlock>, topo_order: &[usize]) {
    if topo_order.is_empty() {
        return;
    }
    let entry = topo_order[0];
    blocks.get_mut(&entry).unwrap().dominator_parent = entry;

    loop {
        let mut changed = false;
        for &b in topo_order.iter() {
            let preds: Vec<usize> = blocks[&b].predecessors.clone();
            let mut dom = usize::MAX;
            for p in preds {
                if blocks[&p].dominator_parent == usize::MAX {
                    continue;
                }
                dom = if dom == usize::MAX {
                    p
                } else {
                    intersect(blocks, p, dom)
                };
            }
            if blocks[&b].dominator_parent != dom {
                blocks.get_mut(&b).unwrap().dominator_parent = dom;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let pcs: Vec<usize> = blocks.keys().copied().collect();
    for b in pcs {
        let parent = blocks[&b].dominator_parent;
        if parent != usize::MAX && parent != b {
            blocks
                .get_mut(&parent)
                .unwrap()
                .dominated_children
                .push(b);
        }
    }
}

fn intersect(
    blocks: &BTreeMap<usize, BasicBlock>,
    mut a: usize,
    mut b: usize,
) -> usize {
    while a != b {
        match blocks[&a].topo_index.cmp(&blocks[&b].topo_index) {
            std::cmp::Ordering::Greater => b = blocks[&b].dominator_parent,
            std::cmp::Ordering::Less => a = blocks[&a].dominator_parent,
            std::cmp::Ordering::Equal => unreachable!(),
        }
    }
    b
}