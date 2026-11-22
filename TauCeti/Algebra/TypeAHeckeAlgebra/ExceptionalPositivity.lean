/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.GNS
import TauCeti.Algebra.Ring.Units
import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.ExceptionalPositivity
import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.MarkovTrace
import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Star
import TauCeti.Algebra.TypeAHeckeAlgebra.RepeatedRoot
import TauCeti.Analysis.Complex.Basic

/-!
# Exceptional-parameter positivity of the infinite type-A Hecke algebra

This file classifies algebraically positive functionals and positive Markov traces on the
unit-circle fiber `InfiniteTypeAHeckeAlgebra.UnitCircle` (`Fact ((q : ℂ) ∈ unitary ℂ)`) in the
exceptional regimes:
* at the repeated-root parameters `q + q⁻¹ = 0` (`q = ±i`), proper-star collapse
  (`TauCeti.Algebra.TypeAHeckeAlgebra.RepeatedRoot`) forces `gnsRepresentation φ` to factor
  through `indexCharacter ℂ q`, so `indexCharacter ℂ q` is the unique normalized positive
  functional;
* for `(q + q⁻¹) ^ 2 ≤ 1` (including `q = ±i` and `l = 3`, `q ^ 4 + q ^ 2 + 1 = 0`),
  balanced-projection collapse for `τ = ((q + q⁻¹) ^ 2)⁻¹ ∉ [0, 1)` shows that the only
  positive Markov traces are `indexCharacter ℂ q` and `signCharacter ℂ q`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.UnitCircle.gnsRepresentation_eq_smul_one`,
  `UnitCircle.apply_eq_indexCharacter_mul_apply_one`: GNS and functional collapse at `q = ±i`.
* `UnitCircle.apply_one_eq_one_and_forall_star_mul_self_nonneg_iff_of_add_inv_eq_zero`,
  `UnitCircle.apply_one_eq_one_and_forall_star_mul_self_nonneg_iff_of_sq_eq_neg_one`:
  uniqueness of the normalized positive functional at `q = ±i`.
* `UnitCircle.isMarkovTrace_and_forall_star_mul_self_nonneg_iff_of_add_inv_sq_le_one`,
  `UnitCircle.isMarkovTrace_and_forall_star_mul_self_nonneg_iff_of_pow_four_add_sq_add_one_eq_zero`:
  positive Markov trace classification for `(q + q⁻¹) ^ 2 ≤ 1` and `l = 3`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§4, 5, 11.
-/

public section

noncomputable section

open scoped ComplexOrder

namespace TauCeti.InfiniteTypeAHeckeAlgebra.UnitCircle

variable {q : ℂˣ} [hq : Fact ((q : ℂ) ∈ unitary ℂ)]

/-- At `q + q⁻¹ = 0` (`q = ±i`), the bounded GNS representation collapses to scalars via
`indexCharacter ℂ q`. -/
theorem gnsRepresentation_eq_smul_one
    (φ : StarPositiveFunctional (InfiniteTypeAHeckeAlgebra ℂ q)) (hq0 : (q : ℂ) + ↑q⁻¹ = 0)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    gnsRepresentation φ x = indexCharacter ℂ q x • 1 := by
  have : IsProperStar (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) := by
    let _ : CStarAlgebra (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) := inferInstance
    exact inferInstance
  have hnorm (i : ℕ) : IsStarNormal (gnsRepresentation φ (T q i)) :=
    isStarNormal_of_mem_unitary (gnsRepresentation_T_mem_unitary φ i)
  exact map_eq_smul_one_indexCharacter_of_isStarNormal hq0 (gnsRepresentation φ) hnorm x

/-- At `q + q⁻¹ = 0` (`q = ±i`), every algebraically positive functional `φ` is a scalar multiple
of `indexCharacter ℂ q`. -/
theorem apply_eq_indexCharacter_mul_apply_one
    (φ : StarPositiveFunctional (InfiniteTypeAHeckeAlgebra ℂ q)) (hq0 : (q : ℂ) + ↑q⁻¹ = 0)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    φ x = indexCharacter ℂ q x * φ 1 := by
  simpa only [hilbertPositiveLinearMap_gnsRepresentation, map_smul, φ.hilbertPositiveLinearMap_one,
    smul_eq_mul] using congrArg φ.hilbertPositiveLinearMap (gnsRepresentation_eq_smul_one φ hq0 x)

/-- **Unique normalized positive functional at `q + q⁻¹ = 0` (`q = ±i`).** -/
theorem apply_one_eq_one_and_forall_star_mul_self_nonneg_iff_of_add_inv_eq_zero
    (hq0 : (q : ℂ) + ↑q⁻¹ = 0) {μ : InfiniteTypeAHeckeAlgebra ℂ q →ₗ[ℂ] ℂ} :
    (μ 1 = 1 ∧ ∀ x, 0 ≤ μ (star x * x)) ↔ μ = (indexCharacter ℂ q).toLinearMap := by
  constructor
  · rintro ⟨h1, hpos⟩
    let φ : StarPositiveFunctional (InfiniteTypeAHeckeAlgebra ℂ q) := ⟨μ, hpos⟩
    exact LinearMap.ext fun x ↦ by
      simpa [φ, h1] using apply_eq_indexCharacter_mul_apply_one φ hq0 x
  · rintro rfl
    exact ⟨map_one (indexCharacter ℂ q), indexCharacter_star_mul_self_nonneg⟩

/-- **Unique normalized positive functional at `Q = q ^ 2 = -1` (`q = ±i`).** -/
theorem apply_one_eq_one_and_forall_star_mul_self_nonneg_iff_of_sq_eq_neg_one
    (hsq : (q : ℂ) ^ 2 = -1) {μ : InfiniteTypeAHeckeAlgebra ℂ q →ₗ[ℂ] ℂ} :
    (μ 1 = 1 ∧ ∀ x, 0 ≤ μ (star x * x)) ↔ μ = (indexCharacter ℂ q).toLinearMap :=
  apply_one_eq_one_and_forall_star_mul_self_nonneg_iff_of_add_inv_eq_zero <|
    mul_left_cancel₀ q.ne_zero (by linear_combination hsq + q.mul_inv)

/-- **Classification of positive Markov traces on the unit circle for `(q + q⁻¹) ^ 2 ≤ 1`.**
This covers both `q = ±i` (`(q + q⁻¹) ^ 2 = 0`) and `0 < (q + q⁻¹) ^ 2 ≤ 1` (including `l = 3`):
the only positive Markov traces are `indexCharacter ℂ q` and `signCharacter ℂ q`. -/
theorem isMarkovTrace_and_forall_star_mul_self_nonneg_iff_of_add_inv_sq_le_one
    (hsq : ((q : ℂ) + ↑q⁻¹) ^ 2 ≤ 1) {z : ℂ}
    {μ : InfiniteTypeAHeckeAlgebra ℂ q →ₗ[ℂ] ℂ} :
    (IsMarkovTrace z μ ∧ ∀ x, 0 ≤ μ (star x * x)) ↔
      (z = q ∧ μ = (indexCharacter ℂ q).toLinearMap) ∨
        (z = -↑q⁻¹ ∧ μ = (signCharacter ℂ q).toLinearMap) := by
  constructor
  · rintro ⟨hμ, hpos⟩
    by_cases hs0 : (q : ℂ) + ↑q⁻¹ = 0
    · have hμ_eq : μ = (indexCharacter ℂ q).toLinearMap :=
        (apply_one_eq_one_and_forall_star_mul_self_nonneg_iff_of_add_inv_eq_zero hs0).mp
          ⟨hμ.map_one, hpos⟩
      have hz : z = q := by
        simpa [hμ.map_one, hμ_eq] using (hμ.map_mul_T (n := 0) (Subalgebra.one_mem _)).symm
      exact Or.inl ⟨hz, hμ_eq⟩
    · have hs_sa : IsSelfAdjoint ((q : ℂ) + ↑q⁻¹) :=
        Units.isSelfAdjoint_add_inv_of_mem_unitary hq.out
      let τ : ℂ := (((q : ℂ) + ↑q⁻¹) ^ 2)⁻¹
      have hτ : τ * ((q : ℂ) + ↑q⁻¹) ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hs0)
      have : Fact (IsSelfAdjoint τ) := ⟨(hs_sa.pow 2).inv₀⟩
      have hτ_notMem := Complex.notMem_Ico_inv_sq_of_sq_le_one hs_sa hs0 hsq
      let η : ℂ := τ * ((q : ℂ) + ↑q⁻¹) * (z + ↑q⁻¹)
      have hz : z = (q : ℂ) * η - ↑q⁻¹ * (1 - η) := by
        dsimp [η]; linear_combination -(z + ↑q⁻¹) * hτ
      let E := BalancedProjectionAlgebra.heckeEquiv q hτ
      have hmarkov_bp : BalancedProjectionAlgebra.IsMarkovTrace η (μ.comp E.toLinearMap) :=
        (BalancedProjectionAlgebra.isMarkovTrace_comp_heckeEquiv_iff hτ hz).mpr hμ
      have hpos_bp : ∀ x : BalancedProjectionAlgebra ℂ τ,
          0 ≤ (μ.comp E.toLinearMap) (star x * x) := fun x ↦ by
        simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, E,
          BalancedProjectionAlgebra.UnitCircle.heckeEquiv_star] using hpos (E x)
      have cancel_comp {ν : InfiniteTypeAHeckeAlgebra ℂ q →ₗ[ℂ] ℂ}
          (h : μ.comp E.toLinearMap = ν.comp E.toLinearMap) : μ = ν :=
        LinearMap.ext (E.surjective.forall.mpr (LinearMap.congr_fun h))
      rcases (BalancedProjectionAlgebra.isMarkovTrace_and_forall_star_mul_self_nonneg_iff
          hτ_notMem).mp ⟨hmarkov_bp, hpos_bp⟩ with ⟨hη, hchar⟩ | ⟨hη, hchar⟩
      · exact Or.inr ⟨by rw [hη] at hz; linear_combination hz,
          cancel_comp (hchar.trans <| LinearMap.ext fun x ↦
            (BalancedProjectionAlgebra.signCharacter_heckeEquiv hτ x).symm)⟩
      · exact Or.inl ⟨by rw [hη] at hz; linear_combination hz,
          cancel_comp (hchar.trans <| LinearMap.ext fun x ↦
            (BalancedProjectionAlgebra.indexCharacter_heckeEquiv hτ x).symm)⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨isMarkovTrace_indexCharacter, indexCharacter_star_mul_self_nonneg⟩
    · exact ⟨isMarkovTrace_signCharacter, signCharacter_star_mul_self_nonneg⟩

/-- **Classification of positive Markov traces at `l = 3` (`q ^ 4 + q ^ 2 + 1 = 0`).** Since
`(q + q⁻¹) ^ 2 = 1`, the only positive Markov traces are `indexCharacter ℂ q` and
`signCharacter ℂ q`. -/
theorem isMarkovTrace_and_forall_star_mul_self_nonneg_iff_of_pow_four_add_sq_add_one_eq_zero
    (h : (q : ℂ) ^ 4 + (q : ℂ) ^ 2 + 1 = 0) {z : ℂ}
    {μ : InfiniteTypeAHeckeAlgebra ℂ q →ₗ[ℂ] ℂ} :
    (IsMarkovTrace z μ ∧ ∀ x, 0 ≤ μ (star x * x)) ↔
      (z = q ∧ μ = (indexCharacter ℂ q).toLinearMap) ∨
        (z = -↑q⁻¹ ∧ μ = (signCharacter ℂ q).toLinearMap) := by
  have hsq : ((q : ℂ) + ↑q⁻¹) ^ 2 = 1 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 q.ne_zero) ?_
    rw [← mul_pow, Units.val_mul_add_inv q]
    linear_combination h
  exact isMarkovTrace_and_forall_star_mul_self_nonneg_iff_of_add_inv_sq_le_one hsq.le

end TauCeti.InfiniteTypeAHeckeAlgebra.UnitCircle
