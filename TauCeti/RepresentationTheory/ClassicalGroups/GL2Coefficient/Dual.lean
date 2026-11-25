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

* `Representation.character_diagGL_eq_finsum_finrank_weightSpace`: the torus character as a
  `finsum` over all weights.
* `TauCeti.isRationalRep_gl2CoefficientRep`: `V_(a,b)` is a rational representation of `GL₂(ℂ)`.
* `TauCeti.nonempty_equiv_dual_gl2CoefficientRep`: the contragredient of `V_(a,b)` is equivalent
  to `V_(-b,-a)`.
-/

public section

noncomputable section

open Module

namespace Representation

open TauCeti

variable {K : Type*} [Field K] {n : ℕ} {W : Type*} [AddCommGroup W] [Module K W]
  [Module.Finite K W]

/-- The torus character is the sum, over all weights, of the weight characters with their
multiplicities, provided the integer weight spaces span the representation and weight characters
separate weights. -/
theorem character_diagGL_eq_finsum_finrank_weightSpace
    (ρ : Representation K (Matrix.GeneralLinearGroup (Fin n) K) W)
    (hchar : Function.Injective (weightChar K (κ := Fin n)))
    (hρ : ⨆ l : Fin n → ℤ, weightSpace ρ l = ⊤) (t : Fin n → Kˣ) :
    ρ.character (diagGL t) =
      ∑ᶠ l : Fin n → ℤ, (finrank K (weightSpace ρ l) : K) * weightCharHom K l t := by
  rw [character_diagGL_eq_sum_finrank_weightSpace ρ hchar hρ t, eq_comm]
  refine finsum_eq_sum_of_support_subset _ fun l hl ↦ ?_
  rw [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
  rintro hbot
  apply hl
  simp only [Submodule.finrank_eq_zero.mpr hbot, Nat.cast_zero, zero_mul]

end Representation

namespace TauCeti

/-- **`V_(a,b)` is a rational representation of `GL₂(ℂ)`**: it is the tensor product of a
symmetric power of the standard representation, which is polynomial, and a power of the
determinant. -/
theorem isRationalRep_gl2CoefficientRep (a b : ℤ) : IsRationalRep (gl2CoefficientRep ℂ a b) :=
  (isPolynomialRep_symPowerRep 2 _).isRationalRep.tprod (isRationalRep_detPowerRep b)

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
