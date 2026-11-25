/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.RCLike.ContinuousMap
import Mathlib.Topology.ContinuousMap.StarOrdered
import Mathlib.Topology.PartitionOfUnity
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
import TauCeti.Analysis.CStarAlgebra.GelfandDuality

/-!
# Positive maps with commutative unital domain or commutative codomain are completely positive

A positive linear map `φ : A → B` between C⋆-algebras is completely positive as soon as `A` is
commutative and unital, or `B` is commutative.

*Commutative codomain* (`B` commutative, possibly nonunital). Positivity in `B` is tested by
characters (`TauCeti.nonneg_iff_forall_characterSpace_nonneg`, in
`TauCeti.Analysis.CStarAlgebra.GelfandDuality`). For a character `χ` of `B`, the quadratic form
`∑ᵢⱼ zᵢ⋆ φ(aᵢⱼ) zⱼ` of `[φ(aᵢⱼ)]` maps to the quadratic form `∑ᵢⱼ ξᵢ⋆ ω(aᵢⱼ) ξⱼ` of the
positive functional `ω = χ ∘ φ`, with `ξᵢ = χ(zᵢ)`, and positive functionals are completely
positive (`PositiveLinearMap.toCompletelyPositiveMap`).

*Commutative domain* (`A` commutative and unital; Stinespring 1955, Theorem 4). Through the
Gelfand transform, `A = C(X)` for the compact character space `X`. Given a positive matrix
`[aᵢⱼ]` and `ε > 0`, cover `X` by finitely many sets on which every `aᵢⱼ` varies by less than
`ε` around its value at a point `xₖ`, and take a subordinate partition of unity `gₖ`. Then
`[∑ₖ aᵢⱼ(xₖ) gₖ]` is within `ε` of `[aᵢⱼ]` entrywise, and its image `∑ₖ [aᵢⱼ(xₖ)] ⊗ φ(gₖ)` is a
sum of Kronecker products of positive scalar matrices with positive elements, which are positive
(`CStarMatrix.ofMatrix_smul_nonneg`). Letting `ε → 0` gives the positivity of `[φ(aᵢⱼ)]`.

## Main declarations

* `TauCeti.isNPositive_of_commCodomain` and
  `PositiveLinearMap.toCompletelyPositiveMapOfCommCodomain`: a positive map into a commutative
  C⋆-algebra is completely positive.
* `TauCeti.isNPositive_of_commDomain` and
  `PositiveLinearMap.toCompletelyPositiveMapOfCommDomain`: a positive map on a commutative unital
  C⋆-algebra is completely positive.

## References

* W. F. Stinespring, *Positive functions on C⋆-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  211–216, Theorem 4.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Chapter 3.
-/

public section

open Filter Topology WeakDual
open scoped CStarAlgebra ComplexOrder


namespace TauCeti

section CommCodomain

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A positive map into a commutative C⋆-algebra is `n`-positive for every `n`. -/
theorem isNPositive_of_commCodomain [NonUnitalCommCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {φ : A →ₗ[ℂ] B} (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) (n : ℕ) :
    IsNPositive n φ := by
  refine isNPositive_iff.mpr fun M hM => CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun z => ?_
  rw [nonneg_iff_forall_characterSpace_nonneg]
  intro χ
  let ω : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ ((CharacterSpace.toCLM χ : B →ₗ[ℂ] ℂ) ∘ₗ φ)
    fun a ha => nonneg_iff_forall_characterSpace_nonneg.mp (hφ a ha) χ
  have hχ := CStarMatrix.nonneg_iff_forall_sum_nonneg.mp
    ((ω.toCompletelyPositiveMap.isNPositive n).map_cstarMatrix_nonneg hM) fun i => χ (z i)
  convert hχ using 1
  simp only [map_sum, map_mul, map_star, CStarMatrix.map_apply,
    CompletelyPositiveMap.coe_toLinearMap, PositiveLinearMap.toCompletelyPositiveMap_apply]
  -- `ω a = χ (φ a)`: `PositiveLinearMap.mk₀` keeps the underlying linear map.
  rfl

end CommCodomain

section CommDomain

variable {A B : Type*} [CommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A matrix over a commutative unital C⋆-algebra is approximated entrywise, to within `ε`, by a
matrix `[∑ₖ aᵢⱼ(xₖ) gₖ]` for finitely many characters `xₖ` and positive `gₖ`. -/
private theorem exists_sum_smul_approx {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) A) {ε : ℝ}
    (hε : 0 < ε) : ∃ (t : Finset (characterSpace ℂ A)) (g : t → A), (∀ k, 0 ≤ g k) ∧
      ∀ i j, ‖M i j - ∑ k : t, (k : characterSpace ℂ A) (M i j) • g k‖ ≤ ε := by
  classical
  let U : characterSpace ℂ A → Set (characterSpace ℂ A) :=
    fun x => {y | ∀ i j, ‖y (M i j) - x (M i j)‖ < ε}
  have hcont (a : A) : Continuous fun y : characterSpace ℂ A => y a :=
    map_continuous (gelfandTransform ℂ A a)
  have hUo (x) : IsOpen (U x) := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt (continuous_norm.comp ((hcont _).sub continuous_const)) continuous_const
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    fun x _ => Set.mem_iUnion.mpr ⟨x, fun i j => by simpa using hε⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun k : t => U k)
    (fun k => hUo k) fun y hy => by
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hyx⟩
  let g : t → A := fun k => (gelfandStarTransform A).symm ((ρ k).realToRCLike ℂ)
  have hg (k : t) (y : characterSpace ℂ A) : y (g k) = ρ k y := by
    simp only [g]
    rw [characterSpace_apply_gelfandStarTransform_symm, ContinuousMap.realToRCLike_apply,
      RCLike.ofReal_eq_complex_ofReal]
  refine ⟨t, g, fun k => ?_, fun i j => ?_⟩
  · rw [← map_le_map_iff (gelfandStarTransform A), map_zero, ContinuousMap.le_def]
    intro y
    simp only [g, StarAlgEquiv.apply_symm_apply, ContinuousMap.realToRCLike_apply,
      ContinuousMap.zero_apply]
    exact Complex.zero_le_real.mpr (ρ.nonneg k y)
  have hsum (y : characterSpace ℂ A) : ∑ k, (ρ k y : ℂ) = 1 := by
    have h := ρ.sum_eq_one (Set.mem_univ y)
    rw [finsum_eq_sum_of_fintype] at h
    exact_mod_cast h
  rw [← (gelfandTransform_isometry A).norm_map_of_map_zero (map_zero _),
    ContinuousMap.norm_le _ hε.le]
  intro y
  simp only [map_sub, map_sum, map_smul, ContinuousMap.sub_apply, ContinuousMap.coe_sum,
    Finset.sum_apply, ContinuousMap.smul_apply, gelfandTransform_apply_apply, hg, smul_eq_mul]
  calc ‖y (M i j) - ∑ k : t, (k : characterSpace ℂ A) (M i j) * ρ k y‖
      = ‖∑ k, (ρ k y : ℂ) * (y (M i j) - (k : characterSpace ℂ A) (M i j))‖ := by
        rw [Finset.sum_congr rfl fun k _ => mul_sub (ρ k y : ℂ) _ _, Finset.sum_sub_distrib,
          ← Finset.sum_mul, hsum, one_mul]
        simp only [mul_comm]
    _ ≤ ∑ k, ρ k y * ε := by
        refine (norm_sum_le _ _).trans <| Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ρ.nonneg k y)]
        by_cases h : ρ k y = 0
        · simp [h]
        exact mul_le_mul_of_nonneg_left (hρ k (subset_tsupport _ h) i j).le (ρ.nonneg k y)
    _ = ε := by
        rw [← Finset.sum_mul, show ∑ k, ρ k y = 1 by exact_mod_cast hsum y, one_mul]

/-- A positive map on a commutative unital C⋆-algebra is `n`-positive for every `n`
(Stinespring). -/
theorem isNPositive_of_commDomain [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {φ : A →ₗ[ℂ] B} (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) (n : ℕ) : IsNPositive n φ := by
  refine isNPositive_iff.mpr fun M hM => ?_
  have hcont : Continuous φ := map_continuous (PositiveLinearMap.mk₀ φ hφ)
  have hN (k : ℕ) : ∃ N : CStarMatrix (Fin n) (Fin n) A,
      0 ≤ N.map φ ∧ ∀ i j, ‖M i j - N i j‖ ≤ 1 / (k + 1) := by
    obtain ⟨t, g, hg, hle⟩ := exists_sum_smul_approx M (ε := 1 / (k + 1)) (by positivity)
    refine ⟨CStarMatrix.ofMatrix
      (Matrix.of fun i j => ∑ l : t, (l : characterSpace ℂ A) (M i j) • g l), ?_,
      fun i j => by simpa using hle i j⟩
    have h : (CStarMatrix.ofMatrix (Matrix.of fun i j =>
        ∑ l : t, (l : characterSpace ℂ A) (M i j) • g l)).map φ =
        ∑ l : t, CStarMatrix.ofMatrix (Matrix.of fun i j =>
          (M.map (l : characterSpace ℂ A)) i j • φ (g l)) := by
      ext i j
      simp [CStarMatrix.sum_apply, map_sum, map_smul]
    rw [h]
    exact Finset.sum_nonneg fun l _ => CStarMatrix.ofMatrix_smul_nonneg
      (CompletelyPositiveMapClass.map_cstarMatrix_nonneg' (l : characterSpace ℂ A) n M hM)
      (hφ _ (hg l))
  choose N hN0 hNle using hN
  refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun w => ?_
  have hlim : Tendsto (fun k => ∑ i, ∑ j, star (w i) * (N k).map φ i j * w j) atTop
      (𝓝 (∑ i, ∑ j, star (w i) * M.map φ i j * w j)) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    refine ((hcont.tendsto _).comp ?_ |>.const_mul _).mul_const _
    refine tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun _ => norm_nonneg _)
      (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [norm_sub_rev] using hNle k i j
  exact ge_of_tendsto' hlim fun k => CStarMatrix.nonneg_iff_forall_sum_nonneg.mp (hN0 k) w

end CommDomain

end TauCeti

namespace PositiveLinearMap

open TauCeti

variable {A B : Type*}

/-- A positive linear map into a commutative C⋆-algebra, as a completely positive map. -/
def toCompletelyPositiveMapOfCommCodomain [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NonUnitalCommCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : A →ₚ[ℂ] B) : A →CP B :=
  CompletelyPositiveMap.ofIsNPositive φ.toLinearMap
    (isNPositive_of_commCodomain fun _ ha => map_nonneg φ ha)

@[simp]
theorem coe_toCompletelyPositiveMapOfCommCodomain [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NonUnitalCommCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : A →ₚ[ℂ] B) : ⇑φ.toCompletelyPositiveMapOfCommCodomain = φ :=
  CompletelyPositiveMap.coe_ofIsNPositive _ _

/-- A positive linear map on a commutative unital C⋆-algebra, as a completely positive map. -/
noncomputable def toCompletelyPositiveMapOfCommDomain [CommCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : A →ₚ[ℂ] B) : A →CP B :=
  CompletelyPositiveMap.ofIsNPositive φ.toLinearMap
    (isNPositive_of_commDomain fun _ ha => map_nonneg φ ha)

@[simp]
theorem coe_toCompletelyPositiveMapOfCommDomain [CommCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : A →ₚ[ℂ] B) : ⇑φ.toCompletelyPositiveMapOfCommDomain = φ :=
  CompletelyPositiveMap.coe_ofIsNPositive _ _

end PositiveLinearMap
