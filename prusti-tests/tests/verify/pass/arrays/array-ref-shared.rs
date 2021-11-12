use prusti_contracts::*;
fn main() {}

type Link = Option<Box<Node>>;
struct Node(i32, Link);

#[pure]
fn len(x: &Link) -> usize {
    if let Some(n) = x {
        1 + len(&n.1)
    } else { 0 }
}
#[pure]
#[requires(idx >= 0 && idx < len(x))]
fn get(x: &Link, idx: usize) -> i32 {
    if let Some(n) = x {
        if idx == 0 {
            n.0
        } else { get(&n.1, idx-1) }
    } else { panic!() }
}

#[ensures(forall(|i: usize| 0 <= i && i < len(x) ==> result >= get(x, i)))]
fn sll_max(x: &Link) -> i32 {
    if let Some(n) = x {
        let m = sll_max(&n.1);
        if m > n.0 { m }
        else { n.0 }
    } else { 0 }
}

domain SOBNG {
  
    function discriminant_SOBNG(self: SOBNG): Int
    
    function cons_0(): SOBNG
    
    function cons_1(_0: Snap_Node): SOBNG
    
    function SOBNG_field_f(self: SOBNG): Snap_Node
    
    axiom SOBNG$discriminant_range {
      (forall self: SOBNG :: { discriminant_SOBNG(self) } 0 <= discriminant_SOBNG(self) && discriminant_SOBNG(self) <= 1)
    }
    
    axiom SOBNG$0$discriminant_axiom {
      discriminant_SOBNG(cons_0()) == 0
    }
    
    axiom SOBNG$1$injectivity {
      (forall _l_0: Snap_Node, _r_0: Snap_Node :: { cons_1(_l_0),cons_1(_r_0) } cons_1(_l_0) == cons_1(_r_0) ==> _l_0 == _r_0)
    }
    
    axiom SOBNG$1$discriminant_axiom {
      (forall _0: Snap_Node :: { cons_1(_0) } discriminant_SOBNG(cons_1(_0)) == 1)
    }
    
    axiom SOBNG$1$field$f_0$axiom {
      (forall _0: Snap_Node :: { SOBNG_field_f(cons_1(_0)) } SOBNG_field_f(cons_1(_0)) == _0)
    }
  }
  
  domain Snap_Node {
    
    function cons_0_SN(_0: Int, _1: SOBNG): Snap_Node
    
    function SN_field_0(self: Snap_Node): Int
    
    function SN_field_1(self: Snap_Node): SOBNG
    
    axiom Snap_Node$0$injectivity {
      (forall _l_0: Int, _l_1: SOBNG, _r_0: Int, _r_1: SOBNG :: { cons_0_SN(_l_0, _l_1),cons_0_SN(_r_0, _r_1) } cons_0_SN(_l_0, _l_1) == cons_0_SN(_r_0, _r_1) ==> _l_0 == _r_0 && _l_1 == _r_1)
    }
    
    axiom Snap_Node$0$field$f_0$axiom {
      (forall _0: Int, _1: SOBNG :: { SN_field_0(cons_0_SN(_0, _1)) } SN_field_0(cons_0_SN(_0, _1)) == _0)
    }
    
    axiom Snap_Node$0$field$f_0$valid {
      (forall self: Snap_Node :: { SN_field_0(self) } -2147483648 <= SN_field_0(self) && SN_field_0(self) <= 2147483647)
    }
    
    axiom Snap_Node$0$field$f_1$axiom {
      (forall _0: Int, _1: SOBNG :: { SN_field_1(cons_0_SN(_0, _1)) } SN_field_1(cons_0_SN(_0, _1)) == _1)
    }
  }
  
  field discriminant: Int
  
  field enum_Some: Ref
  
  field f_0: Ref
  
  field f_1: Ref
  
  field val_bool: Bool
  
  field val_int: Int
  
  field val_ref: Ref
  
  function builtin$unreach_int__$TY$__$int$(): Int
    requires false
  
  
  function OBNG_discriminant(self: Ref): Int
    requires acc(OBNG(self), read$())
    ensures 0 <= result && result <= 1
    ensures discriminant_SOBNG(OBNG_to_SOBNG(self)) == result
  {
    (unfolding acc(OBNG(self), read$()) in self.discriminant)
  }
  
  function m_get__$TY$__Snap$OBNG$$int$$$int$(_1: SOBNG, _2: Int): Int
    requires true
    requires _2 >= 0 && _2 < m_len__$TY$__Snap$OBNG$$int$(_1)
    ensures true
    ensures [result == mirror_simple$m_get__$TY$__Snap$OBNG$$int$$$int$(_1, _2), true]
  {
    (discriminant_SOBNG(_1) == 1 ? (_2 != 0 ? m_get__$TY$__Snap$OBNG$$int$$$int$(SN_field_1(SOBNG_field_f(_1)), _2 - 1) : SN_field_0(SOBNG_field_f(_1))) : builtin$unreach_int__$TY$__$int$())
  }
  
  function m_len__$TY$__Snap$OBNG$$int$(_1: SOBNG): Int
    requires true
    requires true
    ensures true
    ensures [result == mirror_simple$m_len__$TY$__Snap$OBNG$$int$(_1), true]
  {
    (discriminant_SOBNG(_1) == 1 ? 1 + m_len__$TY$__Snap$OBNG$$int$(SN_field_1(SOBNG_field_f(_1))) : 0)
  }
  
  function OBNG_to_SOBNG(self: Ref): SOBNG
    requires acc(OBNG(self), read$())
  {
    (unfolding acc(OBNG(self), read$()) in (self.discriminant == 1 ? (unfolding acc(m_Option$_beg_$struct$m_Box$struct$m_Node$struct$m_Global$_end_Some(self.enum_Some), read$()) in (unfolding acc(struct$m_Box$struct$m_Node$struct$m_Global(self.enum_Some.f_0), read$()) in cons_1(snap$__$TY$__struct$m_Node$Snap_Node(self.enum_Some.f_0.val_ref)))) : cons_0()))
  }
  
  function snap$__$TY$__struct$m_Node$Snap_Node(self: Ref): Snap_Node
    requires acc(struct$m_Node(self), read$())
  {
    (unfolding acc(struct$m_Node(self), read$()) in (unfolding acc(i32(self.f_0), read$()) in cons_0_SN(self.f_0.val_int, OBNG_to_SOBNG(self.f_1))))
  }
  
  function read$(): Perm
    ensures none < result
    ensures result < write
  
  
  predicate DeadBorrowToken$(borrow: Int) 
  
  predicate i32(self: Ref) {
    acc(self.val_int, write)
  }
  
  predicate OBNG(self: Ref) {
    acc(self.discriminant, write) && (0 <= self.discriminant && self.discriminant <= 1 && (acc(self.enum_Some, write) && (self.discriminant == 1 ==> acc(m_Option$_beg_$struct$m_Box$struct$m_Node$struct$m_Global$_end_Some(self.enum_Some), write))))
  }
  
  predicate m_Option$_beg_$struct$m_Box$struct$m_Node$struct$m_Global$_end_Some(self: Ref) {
    acc(self.f_0, write) && acc(struct$m_Box$struct$m_Node$struct$m_Global(self.f_0), write)
  }
  
  predicate struct$m_Box$struct$m_Node$struct$m_Global(self: Ref) {
    acc(self.val_ref, write) && acc(struct$m_Node(self.val_ref), write)
  }
  
  predicate struct$m_Node(self: Ref) {
    acc(self.f_0, write) && (acc(i32(self.f_0), write) && (acc(self.f_1, write) && acc(OBNG(self.f_1), write)))
  }
