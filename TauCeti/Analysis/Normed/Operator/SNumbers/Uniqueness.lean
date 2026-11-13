/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Uniqueness of s-numbers on Hilbert spaces

Over `ℝ` or `ℂ`, every s-number sequence coincides with the approximation numbers on bounded
operators from a complete inner product space into an inner product space.

The upper bound `s T n ≤ aₙ(T)` holds on all normed spaces
(`TauCeti.SNumbers.IsSNumberSequence.le_singularValue`). For the reverse inequality, converse
min–max localization (`TauCeti.HasMinMaxLowerBound.of_completeSpace`) produces for every
`0 ≤ c < aₙ(T)` a constant `s > c` and `n + 1` linearly independent vectors in the source on whose
span `V` the map `T` is `s`-coercive. An orthonormal basis of `V` identifies `V` isometrically
with `EuclideanSpace 𝕜 (Fin (n + 1))`, giving a contractive inclusion `A` onto `V` such that
`T ∘L A` is injective with inverse bounded by `s⁻¹` on its range `W`. Because `W` is
finite-dimensional, it is complete and admits an orthogonal projection without assuming
completeness of the target space. Scaling that inverse composed with the orthogonal projection onto
`W` by `c` yields a contraction `B` with `B ∘L T ∘L A = c • id`
(`ContinuousLinearMap.exists_comp_comp_eq_smul_id`). Chaining the ideal inequality, scalar
homogeneity, and Euclidean normalization along this factorization forces `c ≤ s T n`, hence
`s T n = aₙ(T)`.

In finite dimension, combining uniqueness with the Eckart–Young theorem identifies every s-number
sequence with the singular values `LinearMap.singularValues`.

## Main declarations

* `ContinuousLinearMap.exists_comp_comp_eq_smul_id`: scalar factorization `B ∘L T ∘L A = c • id`
  through `EuclideanSpace 𝕜 (Fin (n + 1))` by contractions whenever `0 ≤ c < aₙ(T)`.
* `TauCeti.SNumbers.IsSNumberSequence.eq_singularValue`: `s T n = aₙ(T)` when the source is a
  complete inner product space and the target is an inner product space.
* `TauCeti.SNumbers.IsSNumberSequence.eq_of_innerProductSpace`: any two s-number sequences agree
  on operators from a complete inner product space into an inner product space.
* `TauCeti.SNumbers.IsSNumberSequence.eq_singularValues`: in finite dimension, `s T n = σₙ(T)`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §5, Theorem 5.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.11.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Uniqueness.lean` and `SNumbers/SingularValuesFinDim.lean`: an earlier Lean
  formalization of Hilbert-space uniqueness and finite-dimensional singular values.
-/

public section

open Module
open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- **Scalar factorization below an approximation number.** If `H₁` is a complete inner product
space, `H₂` is an inner product space, and `0 ≤ c < aₙ(T)` for `T : H₁ →L[𝕜] H₂`, then `c • id` on
`EuclideanSpace 𝕜 (Fin (n + 1))` factors as `B ∘L T ∘L A` for contractions `A` and `B`. -/
theorem exists_comp_comp_eq_smul_id (T : H₁ →L[𝕜] H₂) {n : ℕ} {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < T.singularValue n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        B ∘L T ∘L A = (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
  obtain ⟨s, hcs, v, hv, hs⟩ :=
    TauCeti.hasMinMaxLowerBound_iff.mp TauCeti.HasMinMaxLowerBound.of_completeSpace T n hc₀ hc
  have hs₀ : 0 < s := hc₀.trans_lt hcs
  set V : Submodule 𝕜 H₁ := Submodule.span 𝕜 (Set.range v)
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have hdimV : finrank 𝕜 V = n + 1 := by rw [finrank_span_eq_card hv, Fintype.card_fin]
  -- Embed `EuclideanSpace 𝕜 (Fin (n + 1))` isometrically onto `V` via an orthonormal basis.
  let eV : EuclideanSpace 𝕜 (Fin (n + 1)) ≃ₗᵢ[𝕜] V :=
    ((stdOrthonormalBasis 𝕜 V).reindex (finCongr hdimV)).repr.symm
  let j : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗᵢ[𝕜] H₁ := V.subtypeₗᵢ.comp eV.toLinearIsometry
  let A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁ := j.toContinuousLinearMap
  have hTA_coercive (x : EuclideanSpace 𝕜 (Fin (n + 1))) : s * ‖x‖ ≤ ‖(T ∘L A) x‖ := by
    rw [← j.norm_map x]
    exact hs (j x) (eV x).2
  have hinj : Function.Injective (T ∘L A : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] H₂) := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ norm_le_zero_iff.mp ?_
    have hx' : (T ∘L A) x = 0 := hx
    have h0 : s * ‖x‖ ≤ 0 := by simpa [hx'] using hTA_coercive x
    exact nonpos_of_mul_nonpos_right h0 hs₀
  -- Invert `T ∘L A` on its finite-dimensional range `W`, and project `H₂` orthogonally onto `W`.
  let eW : EuclideanSpace 𝕜 (Fin (n + 1)) ≃ₗ[𝕜] (T ∘L A).range :=
    LinearEquiv.ofInjective (T ∘L A : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] H₂) hinj
  let g : (T ∘L A).range →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    eW.symm.toLinearMap.mkContinuous s⁻¹ fun y ↦ by
      rw [le_inv_mul_iff₀ hs₀, LinearEquiv.coe_toLinearMap, ← Submodule.norm_coe]
      have hy : (T ∘L A) (eW.symm y) = (y : H₂) := congrArg Subtype.val (eW.apply_symm_apply y)
      rw [← hy]
      exact hTA_coercive (eW.symm y)
  let B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    (c : 𝕜) • (g ∘L (T ∘L A).range.orthogonalProjectionOnto)
  refine ⟨A, B, j.norm_toContinuousLinearMap_le, ?_, ?_⟩
  · calc ‖B‖ = ‖(c : 𝕜)‖ * ‖g ∘L (T ∘L A).range.orthogonalProjectionOnto‖ := norm_smul _ _
      _ ≤ c * (‖g‖ * ‖(T ∘L A).range.orthogonalProjectionOnto‖) := by
        rw [RCLike.norm_ofReal, abs_of_nonneg hc₀]
        gcongr
        exact opNorm_comp_le _ _
      _ ≤ s * (s⁻¹ * 1) := by
        gcongr
        · exact g.mkContinuous_norm_le (inv_nonneg.mpr hs₀.le) _
        · exact Submodule.orthogonalProjectionOnto_norm_le _
      _ = 1 := by rw [mul_one, mul_inv_cancel₀ hs₀.ne']
  · refine ContinuousLinearMap.ext fun x ↦ ?_
    have hproj : (T ∘L A).range.orthogonalProjectionOnto ((T ∘L A) x) = eW x := by
      apply Subtype.ext
      rw [Submodule.coe_orthogonalProjectionOnto_apply]
      exact (T ∘L A).range.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self _ x)
    change (c : 𝕜) • g ((T ∘L A).range.orthogonalProjectionOnto ((T ∘L A) x)) = (c : 𝕜) • x
    rw [hproj]
    exact congrArg ((c : 𝕜) • ·) (eW.symm_apply_apply x)

end ContinuousLinearMap

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]

/-- **Uniqueness on Hilbert spaces.** Every s-number sequence coincides with the approximation
numbers on bounded operators from a complete inner product space into an inner product space. -/
theorem IsSNumberSequence.eq_singularValue {s : SNumberFamily 𝕜} (hs : IsSNumberSequence s)
    {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) : s T n = T.singularValue n := by
  refine (hs.le_singularValue T n).antisymm ?_
  by_contra! hlt
  have hlt' : (s T n : ℝ) < T.singularValue n := mod_cast hlt
  set c : ℝ := ((s T n : ℝ) + T.singularValue n) / 2 with hc_def
  have hc₀ : 0 ≤ c := by positivity
  have hc₁ : (s T n : ℝ) < c := by rw [hc_def]; linarith
  have hc₂ : c < T.singularValue n := by rw [hc_def]; linarith
  obtain ⟨A, B, hA, hB, hBTA⟩ := T.exists_comp_comp_eq_smul_id hc₀ hc₂
  have hle : ‖(c : 𝕜)‖₊ ≤ s T n :=
    calc ‖(c : 𝕜)‖₊
        = s ((c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
          rw [hs.smul, hs.normalize, mul_one]
      _ = s (B ∘L T ∘L A) n := by rw [hBTA]
      _ ≤ ‖B‖₊ * s T n * ‖A‖₊ := hs.comp_le B T A n
      _ ≤ 1 * s T n * 1 := by
          gcongr
          · exact_mod_cast hB
          · exact_mod_cast hA
      _ = s T n := by rw [one_mul, mul_one]
  have hle' : c ≤ s T n := by
    simpa [coe_nnNorm, RCLike.norm_ofReal, abs_of_nonneg hc₀] using NNReal.coe_le_coe.mpr hle
  exact hc₁.not_ge hle'

/-- Any two s-number sequences agree on bounded operators from a complete inner product space into
an inner product space. -/
theorem IsSNumberSequence.eq_of_innerProductSpace {s t : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s) (ht : IsSNumberSequence t) {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) : s T n = t T n :=
  (hs.eq_singularValue T n).trans (ht.eq_singularValue T n).symm

/-- **Finite-dimensional singular values.** Between finite-dimensional inner product spaces, every
s-number sequence agrees with the linear-algebraic singular values `LinearMap.singularValues`. -/
theorem IsSNumberSequence.eq_singularValues {s : SNumberFamily 𝕜} (hs : IsSNumberSequence s)
    {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [FiniteDimensional 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) : (s T n : ℝ) = (T : H₁ →ₗ[𝕜] H₂).singularValues n := by
  have : CompleteSpace H₁ := FiniteDimensional.completeSpace 𝕜 H₁
  rw [hs.eq_singularValue, T.singularValue_eq_linearMap_singularValues]

end TauCeti.SNumbers
