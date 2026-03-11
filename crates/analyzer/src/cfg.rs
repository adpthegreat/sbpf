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

#[cfg(test)]
mod tests {
    use sbpf_assembler::{Assembler, AssemblerOption};
    use std::collections::BTreeSet;
    use crate::{Analysis, cfg::CfgEdgeKind};
    use crate::tests::{ELF_WITH_LABELS, ELF_SAME_TARGET, ELF_V3, analyze_asm};

    #[test]
    fn with_labels_parses() {
        Analysis::from_elf_bytes(ELF_WITH_LABELS).unwrap();
    }

    #[test]
    fn with_labels_instruction_count() {
        let a = Analysis::from_elf_bytes(ELF_WITH_LABELS).unwrap();
        assert_eq!(a.instructions.len(), 17, "expected 17 logical instructions, got {}", a.instructions.len());
    }

    #[test]
    fn same_target_cfg_block_count() {
        let a = Analysis::from_elf_bytes(ELF_SAME_TARGET).unwrap();
        // PC0: call → splits to PC1. PC1: ja → splits to PC2.
        // PC2: lddw (no split). PC3: call → splits to PC4. PC4: exit.
        // Blocks: {0},{1},{2,3},{4} = 4 blocks.
        assert_eq!(a.cfg.blocks.len(), 4);
    }

    #[test]
    fn with_labels_cfg_no_empty_blocks() {
        let a = Analysis::from_elf_bytes(ELF_WITH_LABELS).unwrap();
        for (pc, block) in &a.cfg.blocks {
            assert!(block.start < block.end, "empty block at PC {pc}");
        }
    }

   #[test]
   fn with_labels_entry_calls_fn_0068() {
       let a = Analysis::from_elf_bytes(ELF_WITH_LABELS).unwrap();       
       // PC 0 is `call fn_0068` — call splits the block, successor is the
       // fall-through PC 1.
       assert_eq!(a.cfg.blocks[&0].successors, vec![1]);
   }

    #[test]
    fn with_labels_back_edge_to_jmp_0010() {
        let a = Analysis::from_elf_bytes(ELF_WITH_LABELS).unwrap();
        // jmp_0038 block ends with `ja jmp_0010` at PC 9.
        // `call fn_0088` at PC 8 splits the block so PC 9 is its own block.
        assert_eq!(a.cfg.blocks[&9].successors, vec![2]);
    }

    #[test]
    fn with_labels_topological_order_complete() {
        let a = Analysis::from_elf_bytes(ELF_WITH_LABELS).unwrap();
        let topo: BTreeSet<usize> = a.cfg.topological_order.iter().copied().collect();
        let block_starts: BTreeSet<usize> = a.cfg.blocks.keys().copied().collect();
        assert_eq!(topo, block_starts);
    }

    #[test]
    fn same_target_parses() {
        Analysis::from_elf_bytes(ELF_SAME_TARGET).unwrap();
    }

    #[test]
    fn same_target_instruction_count() {
        let a = Analysis::from_elf_bytes(ELF_SAME_TARGET).unwrap();
        assert_eq!(a.instructions.len(), 5, "expected 5 logical instructions, got {}", a.instructions.len());
    }

     #[test]
    fn same_target_entry_successor() {
        let a = Analysis::from_elf_bytes(ELF_SAME_TARGET).unwrap();
        // PC0 is `call fn_0010`, splits to fall-through PC1.
        assert_eq!(a.cfg.blocks[&0].successors, vec![1]);
    }

    #[test]
    fn same_target_exit_block_no_successors() {
        let a = Analysis::from_elf_bytes(ELF_SAME_TARGET).unwrap();
        // PC4 is `exit` — the last block, no successors.
        assert!(a.cfg.blocks[&4].successors.is_empty());
    }

    #[test]
    fn v3_parses() {
        Analysis::from_elf_bytes(ELF_V3).unwrap();
    }

    #[test]
    fn v3_instruction_count() {
        let a = Analysis::from_elf_bytes(ELF_V3).unwrap();
        assert_eq!(a.instructions.len(), 3, "expected 3 logical instructions, got {}", a.instructions.len());
    }

   #[test]
    fn v3_block_structure() {
        let a = Analysis::from_elf_bytes(ELF_V3).unwrap();
        // PC0: lddw. PC1: call sol_log_64_ → splits to PC2. PC2: exit.
        // Blocks: {0,1},{2} = 2 blocks.
        assert_eq!(a.cfg.blocks.len(), 2);
        assert!(a.cfg.blocks[&2].successors.is_empty());
    }

    #[test]
    fn cfg_single_block_sequential() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r0, 1
            mov64 r1, 2
            add64 r0, r1
            exit
        "#);
        assert_eq!(a.cfg.blocks.len(), 1);
        assert!(a.cfg.blocks[&0].successors.is_empty());
    }

    #[test]
    fn cfg_unconditional_jump() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            ja target
        target:
            mov64 r0, 0
            exit
        "#);
        assert_eq!(a.cfg.blocks.len(), 2);
        let entry = &a.cfg.blocks[&0];
        assert_eq!(entry.successors.len(), 1);
    }

    #[test]
    fn cfg_conditional_branch_two_successors() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r0, 1
            jeq r0, 1, taken
            mov64 r1, 0
            exit
        taken:
            mov64 r1, 1
            exit
        "#);
        let entry_block = a.cfg.blocks.values().next().unwrap();
        let entry_pc = entry_block.start;
        let jeq_block = a.cfg.blocks.iter()
            .find(|(_, b)| b.end - b.start >= 2)
            .map(|(_, b)| b)
            .unwrap();
        assert_eq!(jeq_block.successors.len(), 2);
    }

    #[test]
    fn cfg_loop_back_edge() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r0, 0
        loop:
            add64 r0, 1
            jlt r0, 10, loop
            exit
        "#);
        assert!(a.cfg.blocks.len() >= 2);
        let has_back_edge = a.cfg.blocks.values()
            .any(|b| b.successors.iter().any(|&s| s <= b.start));
        assert!(has_back_edge, "expected at least one back-edge");
    }

    #[test]
    fn cfg_multiple_branches() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r0, 5
            jeq r0, 1, a
            jeq r0, 2, b
            ja done
        a:
            mov64 r1, 10
            ja done
        b:
            mov64 r1, 20
        done:
            exit
        "#);
        assert!(a.cfg.blocks.len() >= 4);
    }

    #[test]
    fn cfg_correct_jump_target() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            ja skip
            mov64 r0, 99
        skip:
            mov64 r0, 1
            exit
        "#);
        let entry = &a.cfg.blocks[&0];
        assert_eq!(entry.successors.len(), 1);
        assert_ne!(entry.successors[0], 1, "must skip over PC 1");
    }

    #[test]
    fn cfg_block_boundaries_are_contiguous() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r0, 5
            jeq r0, 1, a
            jeq r0, 2, b
            ja done
        a:
            mov64 r1, 10
            ja done
        b:
            mov64 r1, 20
        done:
            exit
        "#);
        let mut starts: Vec<usize> = a.cfg.blocks.keys().copied().collect();
        starts.sort();
        for i in 0..starts.len() - 1 {
            assert_eq!(a.cfg.blocks[&starts[i]].end, starts[i + 1]);
        }
    }

    #[test]
    fn cfg_topological_order_covers_all_blocks() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r0, 5
            jeq r0, 1, a
            jeq r0, 2, b
            ja done
        a:
            mov64 r1, 10
            ja done
        b:
            mov64 r1, 20
        done:
            exit
        "#);
        let topo: BTreeSet<usize> = a.cfg.topological_order.iter().copied().collect();
        let keys: BTreeSet<usize> = a.cfg.blocks.keys().copied().collect();
        assert_eq!(topo, keys);
    }

    #[test]
    fn cfg_no_empty_blocks() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r0, 5
            jeq r0, 3, done
            mov64 r1, 0
        done:
            exit
        "#);
        for (pc, block) in &a.cfg.blocks {
            assert!(block.start < block.end, "empty block at PC {pc}");
        }
    }

    #[test]
    fn counter_example_cfg_generation() {
        let src = include_str!(
            "../../../examples/sbpf-asm-counter/src/sbpf-asm-counter/sbpf-asm-counter.s"
        );
        let a = analyze_asm(src);
        assert!(a.cfg.blocks.len() >= 5, "counter: expected >=5 blocks, got {}", a.cfg.blocks.len());
        for (pc, block) in &a.cfg.blocks {
            assert!(block.start < block.end, "empty block at PC {pc}");
        }
    }

    #[test]
    fn counter_example_topological_order_complete() {
        let src = include_str!(
            "../../../examples/sbpf-asm-counter/src/sbpf-asm-counter/sbpf-asm-counter.s"
        );
        let a = analyze_asm(src);
        let topo: BTreeSet<usize> = a.cfg.topological_order.iter().copied().collect();
        let keys: BTreeSet<usize> = a.cfg.blocks.keys().copied().collect();
        assert_eq!(topo, keys);
    }

    #[test]
    fn vault_example_cfg_generation() {
        let src = include_str!(
            "../../../examples/sbpf-asm-vault/src/sbpf-asm-vault/sbpf-asm-vault.s"
        );
        let a = analyze_asm(src);
        assert!(a.cfg.blocks.len() >= 3, "vault: expected >=3 blocks, got {}", a.cfg.blocks.len());
        for (pc, block) in &a.cfg.blocks {
            assert!(block.start < block.end, "empty block at PC {pc}");
        }
    }

    #[test]
    fn cpi_example_cfg_generation() {
        let src = include_str!(
            "../../../examples/sbpf-asm-cpi/src/sbpf-asm-cpi/sbpf-asm-cpi.s"
        );
        let a = analyze_asm(src);
        assert!(a.cfg.blocks.len() >= 2, "cpi: expected >=2 blocks, got {}", a.cfg.blocks.len());
    }
}