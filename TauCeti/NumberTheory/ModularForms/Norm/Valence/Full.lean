/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Norm.Cusps
public import TauCeti.NumberTheory.ModularForms.Norm.Valence.Basic

/-!
# The full general-level valence formula

Combining the interior push-forward (`TauCeti.ModularForm.valence_formula_finiteIndex_norm` in
`TauCeti/NumberTheory/ModularForms/Norm/Valence/Basic.lean`) with the cusp distribution
(`TauCeti.ModularForm.qExpansionOrderAtCusp_one_norm_eq_sum_orderAtCuspTranslationOrbit` in
`TauCeti/NumberTheory/ModularForms/Norm/Cusps.lean`) yields the general-level valence formula
over full coset representatives and cusp translation orbits:

`Σ_{P ∈ Γ \ ℍ} (2 / |Stab_Γ P|) · ord_P f + Σ_{c ∈ CuspTranslationOrbit Γ} ord_c f =
  k · [SL(2, ℤ) : Γ] / 12`.

## Main results

* `TauCeti.ModularForm.valence_formula_finiteIndex`: **the valence formula at general level**,
  with both halves distributed.
* `TauCeti.ModularForm.twelve_mul_orderAtCuspTranslationOrbit_le_weight_mul_index`: the mass at
  one cusp translation orbit is bounded by the total mass.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §3.
-/

public section

open UpperHalfPlane MulAction

open scoped ModularForm MatrixGroups

namespace TauCeti.ModularForm

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
  [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

/-- **The valence formula at general level**: for a nonzero weight-`k` form on a finite-index
`Γ ≤ SL(2, ℤ)`, the interior orders — weighted by `2 / |Stab_Γ P|` — together with the orders
indexed by the cusp translation orbits add up to `k · [SL(2, ℤ) : Γ] / 12`.

This is `valence_formula_finiteIndex_norm` with its cusp term, an order at `∞` on the norm,
distributed over the cusps of `Γ`. -/
theorem valence_formula_finiteIndex (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
          weightedOrderOfVanishingOnSubgroupOrbit f o) +
        ∑ c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)),
          (orderAtCuspTranslationOrbit f c : ℚ) =
      (k : ℚ) * Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) / 12 := by
  rw [← valence_formula_finiteIndex_norm f hf,
    qExpansionOrderAtCusp_one_norm_eq_sum_orderAtCuspTranslationOrbit f]
  push_cast
  ring

/-- **The mass at one cusp is bounded by the total mass.** Every other term of the general-level
valence formula is nonnegative, so `12 · ord_c f ≤ k · [SL(2, ℤ) : Γ]` for a nonzero form — the
cusp counterpart of the interior bound
`twentyFour_mul_orderOfVanishingOnSubgroupOrbit_le_weight_mul_index_mul_cardStabilizer`,
with `12` in place of `24` because a cusp carries no stabiliser weight. -/
theorem twelve_mul_orderAtCuspTranslationOrbit_le_weight_mul_index (f : F)
    (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) :
    12 * orderAtCuspTranslationOrbit f c ≤
      k * Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  have hinterior : (0 : ℚ) ≤ ∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
      weightedOrderOfVanishingOnSubgroupOrbit f o :=
    finsum_nonneg (weightedOrderOfVanishingOnSubgroupOrbit_nonneg f)
  have hsingle : (orderAtCuspTranslationOrbit f c : ℚ) ≤
      ∑ c' : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)),
        (orderAtCuspTranslationOrbit f c' : ℚ) :=
    Finset.single_le_sum (f := fun c' ↦ (orderAtCuspTranslationOrbit f c' : ℚ))
      (fun c' _ ↦ by exact_mod_cast orderAtCuspTranslationOrbit_nonneg f c')
      (Finset.mem_univ c)
  have htotal := valence_formula_finiteIndex f hf
  have hq : (12 : ℚ) * (orderAtCuspTranslationOrbit f c : ℚ) ≤
      (k : ℚ) * Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by linarith
  exact_mod_cast hq

end TauCeti.ModularForm

end
