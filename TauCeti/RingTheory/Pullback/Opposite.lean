/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.CompTypeclasses
public import TauCeti.RingTheory.Pullback

/-!
# Opposites of fibre products of rings

Taking the opposite of a fibre product agrees with taking the opposite of each ring in
the defining cospan. The comparison preserves the two projections in their given order.
-/

public section

namespace RingHom

open MulOpposite

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T] (f : R →+* T) (g : S →+* T)

/-- The fibre product of the opposite rings is the opposite of the original fibre product. -/
def pullbackOpEquiv : f.op.pullback g.op ≃+* (f.pullback g)ᵐᵒᵖ where
  toFun x := MulOpposite.op ⟨(x.val.1.unop, x.val.2.unop), op_injective x.property⟩
  invFun x := ⟨(MulOpposite.op x.unop.val.1, MulOpposite.op x.unop.val.2),
    congrArg MulOpposite.op x.unop.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The comparison returns both pullback coordinates to their original rings. -/
@[simp]
theorem coe_unop_pullbackOpEquiv_apply (x : f.op.pullback g.op) :
    ((f.pullbackOpEquiv g x).unop : R × S) = (x.val.1.unop, x.val.2.unop) :=
  (rfl)

/-- The inverse comparison takes the opposite of each pullback coordinate. -/
@[simp]
theorem coe_pullbackOpEquiv_symm_apply (x : (f.pullback g)ᵐᵒᵖ) :
    ((f.pullbackOpEquiv g).symm x : Rᵐᵒᵖ × Sᵐᵒᵖ) =
      (MulOpposite.op x.unop.val.1, MulOpposite.op x.unop.val.2) :=
  (rfl)

/-- The opposite-ring comparison intertwines the first projections. -/
@[simp]
theorem op_pullbackFst_comp_pullbackOpEquiv :
    (f.pullbackFst g).op.comp ↑(f.pullbackOpEquiv g) = f.op.pullbackFst g.op :=
  (rfl)

/-- The opposite-ring comparison intertwines the second projections. -/
@[simp]
theorem op_pullbackSnd_comp_pullbackOpEquiv :
    (f.pullbackSnd g).op.comp ↑(f.pullbackOpEquiv g) = f.op.pullbackSnd g.op :=
  (rfl)

/-- The left-module scalar rings are identified by returning both coordinates to the
original endpoint rings. -/
def pullbackOpOpEquiv : (f.op.pullback g.op)ᵐᵒᵖ ≃+* f.pullback g :=
  (RingEquiv.op (f.pullbackOpEquiv g)).trans (RingEquiv.opOp _).symm

@[simp]
theorem coe_pullbackOpOpEquiv_apply (d : (f.op.pullback g.op)ᵐᵒᵖ) :
    (f.pullbackOpOpEquiv g d : R × S) = (d.unop.val.1.unop, d.unop.val.2.unop) :=
  (rfl)

@[simp]
theorem coe_unop_pullbackOpOpEquiv_symm_apply (d : f.pullback g) :
    ((f.pullbackOpOpEquiv g).symm d).unop.val =
      (MulOpposite.op d.val.1, MulOpposite.op d.val.2) :=
  (rfl)

/-- The scalar comparison for left patches has the inverse given by taking opposite
coordinates in both endpoints. -/
instance pullbackOpOpEquiv_ringHomInvPair :
    RingHomInvPair (f.pullbackOpOpEquiv g).toRingHom (f.pullbackOpOpEquiv g).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (f.pullbackOpOpEquiv g)

/-- The reverse scalar comparison also forms an inverse pair. -/
instance pullbackOpOpEquiv_symm_ringHomInvPair :
    RingHomInvPair (f.pullbackOpOpEquiv g).symm.toRingHom (f.pullbackOpOpEquiv g).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (f.pullbackOpOpEquiv g)

end RingHom
