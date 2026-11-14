/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Uniqueness of s-number sequences on Hilbert spaces

On Hilbert spaces over `ℝ` or `ℂ`, every s-number sequence coincides with the approximation
numbers, and between finite-dimensional inner product spaces every s-number sequence gives the
classical singular values.

The upper bound `s T n ≤ aₙ(T)` holds on all normed spaces
(`TauCeti.SNumbers.IsSNumberSequence.le_singularValue`). For the reverse inequality on a complete
inner product domain `H₁`, each `0 ≤ c < aₙ(T)` yields an `(n + 1)`-dimensional subspace of `H₁`
on which `T` is coercively bounded below above `c`
(`TauCeti.HasMinMaxLowerBound.of_completeSpace`). Identifying that subspace isometrically with
`EuclideanSpace 𝕜 (Fin (n + 1))` and projecting the target orthogonally onto its finite-dimensional
image gives contractions `A` and `B` with `B ∘L T ∘L A = c • id`
(`ContinuousLinearMap.exists_comp_comp_eq_smul_id`). Chaining the ideal inequality, scalar
homogeneity and Euclidean normalization of `s` forces `c ≤ s T n`. Completeness of the target inner
product space is not required, because the image of the `(n + 1)`-dimensional subspace is finite
dimensional and therefore complete.

## Main declarations

* `ContinuousLinearMap.exists_comp_comp_eq_smul_id`: scalar factorization of `c • id` on
  `EuclideanSpace 𝕜 (Fin (n + 1))` through `T` by contractions whenever `0 ≤ c < aₙ(T)`.
* `TauCeti.SNumbers.IsSNumberSequence.eq_singularValue`: every s-number sequence agrees with
  `ContinuousLinearMap.singularValue` on operators from a complete inner product space into an
  inner product space.
* `TauCeti.SNumbers.IsSNumberSequence.eq_linearMap_singularValues`: between finite-dimensional
  inner product spaces, every s-number sequence equals `LinearMap.singularValues`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §5, Theorem 5.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.11.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Uniqueness.lean` and `SNumbers/SingularValuesFinDim.lean`: an earlier Lean
  formalization of Hilbert-space uniqueness and finite-dimensional singular-value identification.
-/

public section

open Module
open scoped NNReal

namespace ContinuousLinearMap

/-- **Scalar factorization below an approximation number.** For a bounded operator `T : H₁ →L[𝕜] H₂`
from a complete inner product space into an inner product space over `ℝ` or `ℂ`, and every
`0 ≤ c < aₙ(T)`, there exist contractions `A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁` and
`B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))` such that `B ∘L T ∘L A = c • id`. Completeness of
`H₂` is not needed, since the orthogonal projection used to construct `B` has finite-dimensional
range. -/
theorem exists_comp_comp_eq_smul_id {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < T.singularValue n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        B ∘L T ∘L A = (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
  obtain ⟨s, hcs, v, hv, hvs⟩ :=
    TauCeti.hasMinMaxLowerBound_iff.mp TauCeti.HasMinMaxLowerBound.of_completeSpace T n hc0 hc
  have hs0 : 0 < s := hc0.trans_lt hcs
  set V : Submodule 𝕜 H₁ := Submodule.span 𝕜 (Set.range v)
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have hfin : finrank 𝕜 V = n + 1 := by rw [finrank_span_eq_card hv, Fintype.card_fin]
  -- Parameterize `V` isometrically by `EuclideanSpace 𝕜 (Fin (n + 1))`.
  set e : EuclideanSpace 𝕜 (Fin (n + 1)) ≃ₗᵢ[𝕜] V :=
    ((stdOrthonormalBasis 𝕜 V).reindex (finCongr hfin)).repr.symm
  set A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁ :=
    V.subtypeL ∘L e.toLinearIsometry.toContinuousLinearMap
  have hA_norm : ∀ x, ‖A x‖ = ‖x‖ := fun x ↦ by
    simp [A, Submodule.norm_coe]
  have hA : ‖A‖ ≤ 1 := opNorm_le_bound _ zero_le_one fun x ↦ by simp [hA_norm]
  have hTA_coercive : ∀ x, s * ‖x‖ ≤ ‖(T ∘L A) x‖ := fun x ↦ by
    have h := hvs (e x) (e x).2
    rwa [Submodule.norm_coe, e.norm_map] at h
  -- Restrict `T ∘L A` to its finite-dimensional range `W ≤ H₂`, where it is a linear isomorphism.
  set W : Submodule 𝕜 H₂ := LinearMap.range (T ∘L A).toLinearMap
  have : FiniteDimensional 𝕜 W := inferInstance
  set S : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] W := (T ∘L A).toLinearMap.rangeRestrict
  have hS_inj : Function.Injective S := by
    refine (injective_iff_map_eq_zero S).mpr fun x hx ↦ ?_
    have h0 : (T ∘L A) x = 0 := congrArg Subtype.val hx
    have hle := hTA_coercive x
    rw [h0, norm_zero] at hle
    exact norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right hle hs0) (norm_nonneg x))
  set eS : EuclideanSpace 𝕜 (Fin (n + 1)) ≃ₗ[𝕜] W :=
    LinearEquiv.ofBijective S ⟨hS_inj, LinearMap.surjective_rangeRestrict _⟩
  set B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    ((c : 𝕜) • eS.symm.toLinearMap.toContinuousLinearMap) ∘L W.orthogonalProjectionOnto
  refine ⟨A, B, hA, opNorm_le_bound _ zero_le_one fun y ↦ ?_, ?_⟩
  · set w : W := W.orthogonalProjectionOnto y
    have hw : s * ‖eS.symm w‖ ≤ ‖y‖ := by
      have hSw : (T ∘L A) (eS.symm w) = (w : H₂) :=
        congrArg Subtype.val (eS.apply_symm_apply w)
      calc s * ‖eS.symm w‖ ≤ ‖(T ∘L A) (eS.symm w)‖ := hTA_coercive _
        _ = ‖w‖ := by rw [hSw, Submodule.norm_coe]
        _ ≤ ‖y‖ := W.norm_orthogonalProjectionOnto_apply_le y
    calc ‖B y‖ = |c| * ‖eS.symm w‖ := by simp [B, w, norm_smul]
      _ = c * ‖eS.symm w‖ := by rw [abs_of_nonneg hc0]
      _ ≤ s * ‖eS.symm w‖ := mul_le_mul_of_nonneg_right hcs.le (norm_nonneg _)
      _ ≤ 1 * ‖y‖ := by simpa using hw
  · ext x
    have hmem : T (A x) ∈ W := LinearMap.mem_range_self (T ∘L A).toLinearMap x
    have hproj : W.orthogonalProjectionOnto (T (A x)) = eS x :=
      W.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T (A x), hmem⟩
    simp [B, hproj]

end ContinuousLinearMap

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]

/-- **Uniqueness of s-number sequences on Hilbert spaces.** Every s-number sequence agrees with the
approximation numbers on bounded operators from a complete inner product space into an inner
product space. -/
theorem IsSNumberSequence.eq_singularValue {s : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s) {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) : s T n = T.singularValue n := by
  refine (hs.le_singularValue T n).antisymm ?_
  by_contra! hlt
  set c : ℝ := ((s T n : ℝ) + T.singularValue n) / 2 with hc_def
  have hc0 : 0 ≤ c := by positivity
  have hsc : (s T n : ℝ) < c := by
    have : (s T n : ℝ) < T.singularValue n := by exact_mod_cast hlt
    linarith
  have hca : c < T.singularValue n := by
    have : (s T n : ℝ) < T.singularValue n := by exact_mod_cast hlt
    linarith
  obtain ⟨A, B, hA, hB, hfac⟩ := T.exists_comp_comp_eq_smul_id n hc0 hca
  have hA' : ‖A‖₊ ≤ 1 := by exact_mod_cast hA
  have hB' : ‖B‖₊ ≤ 1 := by exact_mod_cast hB
  have hle : ‖(c : 𝕜)‖₊ ≤ s T n := by
    calc ‖(c : 𝕜)‖₊ =
            s ((c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
          rw [hs.smul, hs.normalize, mul_one]
      _ = s (B ∘L T ∘L A) n := by rw [hfac]
      _ ≤ ‖B‖₊ * s T n * ‖A‖₊ := hs.comp_le B T A n
      _ ≤ 1 * s T n * 1 := by gcongr
      _ = s T n := by simp
  have hle' : c ≤ s T n := by
    have h := NNReal.coe_le_coe.mpr hle
    rwa [coe_nnNorm, RCLike.norm_ofReal, abs_of_nonneg hc0] at h
  exact hsc.not_ge hle'

/-- **Identification with singular values in finite dimension.** Between finite-dimensional inner
product spaces over `ℝ` or `ℂ`, every s-number sequence coincides with
`LinearMap.singularValues`. -/
theorem IsSNumberSequence.eq_linearMap_singularValues {s : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s) {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [FiniteDimensional 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    (s T n : ℝ) = (T : H₁ →ₗ[𝕜] H₂).singularValues n := by
  have := FiniteDimensional.completeSpace 𝕜 H₁
  rw [hs.eq_singularValue, T.singularValue_eq_linearMap_singularValues]

end TauCeti.SNumbers
