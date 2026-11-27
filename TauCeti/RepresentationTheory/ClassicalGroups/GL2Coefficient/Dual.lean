/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GL2Coefficient
public import TauCeti.RepresentationTheory.ClassicalGroups.UnitaryTrick
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Character

/-!
# The contragredient of `V_(a,b)` is `V_(-b,-a)`

For integers `a ≥ b`, the contragredient of the algebraic coefficient
`V_(a,b) = Sym^{a-b}(Std) ⊗ det^b` of `GL₂(ℂ)` (`TauCeti.gl2CoefficientRep ℂ a b`) is equivalent to
`V_(-b,-a)`.

Both are rational representations (`TauCeti.isRationalRep_gl2CoefficientRep` and
`TauCeti.IsRationalRep.dual`), so it suffices that their characters agree on the diagonal torus
(`TauCeti.IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq`). A torus character is the
sum of the weight characters with their multiplicities
(`Representation.character_diagGL_eq_finsum_finrank_weightSpace`). The character of the
contragredient at `t` is that of `V_(a,b)` at `t⁻¹`, whose weights are the negatives of those of
`V_(a,b)`, and the weight multiplicities of `V_(-b,-a)` are those of the contragredient
(`TauCeti.finrank_weightSpace_dual_gl2CoefficientRep`).

## Main results

* `TauCeti.nonempty_equiv_dual_gl2CoefficientRep`: the contragredient of `V_(a,b)` is equivalent
  to `V_(-b,-a)`.
-/

public section

noncomputable section

open Module

namespace TauCeti

/-- **The contragredient of `V_(a,b)` is `V_(-b,-a)`.** For integers `a ≥ b`, the contragredient
of the algebraic coefficient `V_(a,b)` of `GL₂(ℂ)` is equivalent to `V_(-b,-a)`: both are rational
with the same character on the diagonal torus. -/
theorem nonempty_equiv_dual_gl2CoefficientRep {a b : ℤ} (hab : b ≤ a) :
    Nonempty ((gl2CoefficientRep ℂ a b).dual.Equiv (gl2CoefficientRep ℂ (-b) (-a))) := by
  have hchar := weightChar_injective (K := ℂ) (κ := Fin 2)
  refine IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    (W' := GL2CoefficientSpace ℂ (-b) (-a)) (isRationalRep_gl2CoefficientRep a b).dual
    (isRationalRep_gl2CoefficientRep (-b) (-a)) fun t ↦ ?_
  refine (Representation.char_dual (V := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b)
    (diagGL t)).trans ?_
  rw [← map_inv,
    Representation.character_diagGL_eq_finsum_finrank_weightSpace _ hchar
      iSup_weightSpace_gl2CoefficientRep_eq_top,
    Representation.character_diagGL_eq_finsum_finrank_weightSpace _ hchar
      iSup_weightSpace_gl2CoefficientRep_eq_top,
    ← finsum_comp_equiv (Equiv.neg (Fin 2 → ℤ))]
  refine finsum_congr fun l ↦ ?_
  rw [Equiv.neg_apply, ← finrank_weightSpace_dual_gl2CoefficientRep hchar hab,
    finrank_weightSpace_dual hchar iSup_weightSpace_gl2CoefficientRep_eq_top]
  simp [weightChar_neg]

end TauCeti
