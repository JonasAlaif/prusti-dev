use crate::encoder::{
    errors::SpannedEncodingResult, mir::procedures::MirProcedureEncoderInterface,
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_span::Span;
use vir_crate::{high as vir_high, middle as vir_mid};

pub(crate) trait HighProcedureEncoderInterface<'tcx> {
    fn encode_procedure_core_proof(
        &mut self,
        proc_def_id: DefId,
    ) -> SpannedEncodingResult<vir_mid::ProcedureDecl>;
}

impl<'v, 'tcx: 'v> HighProcedureEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_procedure_core_proof(
        &mut self,
        proc_def_id: DefId,
    ) -> SpannedEncodingResult<vir_mid::ProcedureDecl> {
        let procedure_high = self.encode_procedure_core_proof_high(proc_def_id)?;
        eprintln!("procedure_high:\n{}", procedure_high);
        let procedure =
            super::inference::infer_shape_operations(self, proc_def_id, procedure_high)?;
        Ok(procedure)
    }
}
