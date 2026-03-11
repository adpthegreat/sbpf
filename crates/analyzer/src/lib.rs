pub mod cfg;
pub mod dfg;
pub mod dot;

pub use cfg::{BasicBlock, CfgEdgeKind, ControlFlowGraph};
pub use dfg::{DataFlowGraph, DataResource, DfgEdge, DfgEdgeKind, DfgNode};

use sbpf_common::instruction::Instruction;
use sbpf_disassembler::{errors::DisassemblerError, program::Program};

#[derive(Debug)]
pub enum AnalysisError {
    Disassembler(DisassemblerError),
}

impl std::fmt::Display for AnalysisError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AnalysisError::Disassembler(e) => write!(f, "disassembler error: {e}"),
        }
    }
}

impl std::error::Error for AnalysisError {}

impl From<DisassemblerError> for AnalysisError {
    fn from(e: DisassemblerError) -> Self {
        AnalysisError::Disassembler(e)
    }
}

pub struct Analysis {
    pub instructions: Vec<Instruction>,
    pub cfg: ControlFlowGraph,
    pub dfg: DataFlowGraph,
}

impl Analysis {
    pub fn from_elf_bytes(elf: &[u8]) -> Result<Self, AnalysisError> {
        let program = Program::from_bytes(elf)?;

        let (instructions, _rodata) = program.to_ixs()?;

        let cfg = ControlFlowGraph::build(&instructions);
        let dfg = DataFlowGraph::build(&instructions, &cfg);

        Ok(Self { instructions: instructions.to_vec(), cfg, dfg })
    }
}

#[cfg(test)]
mod tests;
