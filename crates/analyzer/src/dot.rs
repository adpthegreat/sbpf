use crate::{
    cfg::ControlFlowGraph,
    dfg::{DataFlowGraph, DfgEdgeKind, DfgNode},
};
use sbpf_common::instruction::Instruction;

pub fn cfg_to_dot(cfg: &ControlFlowGraph, instructions: &[Instruction]) -> String {
    let mut out = String::from("digraph CFG {\n    node [shape=box fontname=\"Courier\"];\n");

    for (&start, block) in &cfg.blocks {
        let insts: String = (block.start..block.end)
            .map(|pc| {
                let inst = &instructions[pc];
                let asm = inst.to_asm().unwrap_or_else(|_| format!("{:?}", inst.opcode));
                format!("{}\\l", escape_dot(&format!("{pc}: {asm}")))
            })
            .collect();

        let label = format!(
            "{{{}|{}}}",
            escape_dot(&block.label),
            insts
        );
        out.push_str(&format!(
            "    bb_{start} [label=\"{label}\" shape=record];\n"
        ));
    }

    out.push('\n');

    for (&start, block) in &cfg.blocks {
        for &succ in &block.successors {
            out.push_str(&format!("    bb_{start} -> bb_{succ};\n"));
        }
    }

    out.push_str("}\n");
    out
}

pub fn dfg_to_dot(dfg: &DataFlowGraph) -> String {
    let mut out = String::from("digraph DFG {\n    node [shape=ellipse];\n");

    for (source, edges) in &dfg.forward {
        let src_name = node_name(source);
        out.push_str(&format!("    {src_name};\n"));

        for edge in edges {
            let dst_name = node_name(&edge.destination);
            let style = match edge.kind {
                DfgEdgeKind::Filled => "solid",
                DfgEdgeKind::Empty => "dashed",
            };
            let res_label = match &edge.resource {
                crate::dfg::DataResource::Register(r) => format!("r{r}"),
                crate::dfg::DataResource::Memory => "mem".to_string(),
            };
            out.push_str(&format!(
                "    {src_name} -> {dst_name} [label=\"{res_label}\" style={style}];\n"
            ));
        }
    }

    out.push_str("}\n");
    out
}

fn node_name(node: &DfgNode) -> String {
    match node {
        DfgNode::Instruction(pc) => format!("insn_{pc}"),
        DfgNode::Phi(pc) => format!("phi_{pc}"),
    }
}

fn escape_dot(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('{', "\\{")
        .replace('}', "\\}")
        .replace('|', "\\|")
        .replace('<', "\\<")
        .replace('>', "\\>")
}

#[cfg(test)]
mod tests {
    use crate::{Analysis, dot};
    use crate::tests::{ELF_WITH_LABELS, analyze_asm};

    #[test]
    fn with_labels_dot_cfg_valid() {
        let a = Analysis::from_elf_bytes(ELF_WITH_LABELS).unwrap();
        let out = dot::cfg_to_dot(&a.cfg, &a.instructions);
        assert!(out.starts_with("digraph"), "DOT output must start with 'digraph'");
        assert!(out.contains("->"), "DOT CFG must contain edges");
    }

    #[test]
    fn dot_cfg_output_is_valid_graphviz() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r0, 1
            exit
        "#);
        let out = dot::cfg_to_dot(&a.cfg, &a.instructions);
        assert!(out.starts_with("digraph"));
        assert!(out.contains('{'));
        assert!(out.contains('}'));
    }

    #[test]
    fn dot_dfg_output_is_valid_graphviz() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r1, 1
            mov64 r2, r1
            exit
        "#);
        let out = dot::dfg_to_dot(&a.dfg);
        assert!(out.starts_with("digraph"));
        assert!(out.contains('{'));
        assert!(out.contains('}'));
    }

    #[test]
    fn dot_cfg_contains_edges() {
        let a = analyze_asm(r#"
        .globl entrypoint
        entrypoint:
            mov64 r0, 1
            jeq r0, 1, done
            mov64 r1, 0
        done:
            exit
        "#);
        let out = dot::cfg_to_dot(&a.cfg, &a.instructions);
        assert!(out.contains("->"), "DOT output must contain edges for a branching program");
    }
    #[test]
    #[ignore]
    fn print_dot() {
        let a = Analysis::from_elf_bytes(crate::tests::ELF_WITH_LABELS).unwrap();
        println!("{}", dot::cfg_to_dot(&a.cfg, &a.instructions));
    }
}
