use super::{ToViper, ToViperDecl};
use viper::{self, AstFactory};
use vir::{
    legacy::RETURN_LABEL,
    low::{
        ast::position::Position,
        cfg::{method::Successor, Label, ProcedureDecl},
    },
};

impl<'a, 'v> ToViper<'v, viper::Method<'v>> for &'a ProcedureDecl {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Method<'v> {
        let mut statements: Vec<viper::Stmt> = vec![];
        let mut declarations: Vec<viper::Declaration> = vec![];
        for local in &self.locals {
            declarations.push(local.to_viper_decl(ast).into());
            eprintln!("local: {}", local);
        }
        for block in &self.basic_blocks {
            declarations.push(block.label.to_viper_decl(ast).into());
            statements.push(block.label.to_viper(ast));
            statements.extend(block.statements.to_viper(ast));
            statements.push(block.successor.to_viper(ast));
        }
        statements.push(ast.label(RETURN_LABEL, &[]));
        declarations.push(ast.label(RETURN_LABEL, &[]).into());
        let body = Some(ast.seqn(&statements, &declarations));
        ast.method(&self.name, &[], &[], &[], &[], body)
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for Successor {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        match self {
            Successor::Goto(target) => ast.goto(&target.name),
            Successor::GotoSwitch(targets) => {
                let mut statements = Vec::new();
                for (test, target) in targets {
                    let goto = ast.goto(&target.name);
                    let skip = ast.seqn(&[], &[]);
                    let conditional_goto = ast.if_stmt(test.to_viper(ast), goto, skip);
                    statements.push(conditional_goto);
                }
                let position = Position::default(); // FIXME
                let assert_false = ast.assert(
                    ast.false_lit_with_pos(position.to_viper(ast)),
                    position.to_viper(ast),
                );
                statements.push(assert_false);
                ast.seqn(&statements, &[])
            }
            Successor::Return => ast.goto(RETURN_LABEL),
        }
    }
}

impl<'v> ToViperDecl<'v, viper::Stmt<'v>> for Label {
    fn to_viper_decl(&self, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        ast.label(&self.name, &[])
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for Label {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        ast.label(&self.name, &[])
    }
}
