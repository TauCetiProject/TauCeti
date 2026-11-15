/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation
public import TauCeti.Analysis.Normed.Operator.SNumbers.Bernstein
public import TauCeti.Analysis.Normed.Operator.SNumbers.Gelfand
public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Completion
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Uniqueness of s-number sequences on inner product spaces

Whereas distinct s-number sequences separate on general Banach spaces, Pietsch proved that on
Hilbert spaces every s-number sequence coincides with the approximation numbers. This file
establishes that uniqueness theorem without completeness assumptions on the inner product spaces,
together with its operator-level and spectral consequences:

* **Scalar factorization through Euclidean space**
  (`ContinuousLinearMap.exists_comp_comp_eq_smul_id`). For a bounded operator `T : H₁ →L[𝕜] H₂`
  between seminormed inner product spaces over `𝕜` (`ℝ` or `ℂ`) and every `0 ≤ c < aₙ(T)`, there
  exist contractions `A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁` and
  `B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))` with `B ∘L T ∘L A = c • id`. Passing to
  `T.completion` preserves `aₙ(T)` (`ContinuousLinearMap.singularValue_completion`); the converse
  min–max localization on the complete space `Completion H₁`
  (`TauCeti.HasMinMaxLowerBound.of_completeSpace`) supplies an `(n + 1)`-dimensional subspace on
  which `T.completion` is `s`-coercive for some `s > c`, perturbing an orthonormal basis into the
  dense subspace `H₁` and rescaling gives a contraction `A` on which `T` remains `c`-coercive, and
  `B` projects orthogonally in `Completion H₂` onto the `(n + 1)`-dimensional image of `T ∘L A`
  before applying `(c : 𝕜) • (T ∘L A)⁻¹`.
* **Uniqueness of s-number sequences** (`TauCeti.SNumbers.IsSNumberSequence.eq_singularValue`).
  Every s-number sequence `s` satisfies `s T n ≤ aₙ(T)` on all normed spaces
  (`TauCeti.SNumbers.IsSNumberSequence.le_singularValue`); conversely, for any `c < aₙ(T)` the
  factorization `c • id = B ∘L T ∘L A`, homogeneity, Euclidean normalization, and the two-sided
  ideal inequality force `c ≤ s T n`. In particular, any two s-number sequences agree on inner
  product spaces (`TauCeti.SNumbers.IsSNumberSequence.eq_of_innerProductSpace`), and even an
  ordinary s-number sequence satisfies strict identity normalization on every inner product space
  (`TauCeti.SNumbers.IsSNumberSequence.apply_id`).
* **Multi-universe specializations** (`ContinuousLinearMap.gelfandNumber_eq_singularValue`,
  `ContinuousLinearMap.kolmogorovNumber_eq_singularValue`,
  `ContinuousLinearMap.bernsteinNumber_eq_singularValue`). Because `SNumberFamily 𝕜` lives in the
  scalar field's universe, we also record the equality of Gelfand, Kolmogorov, and Bernstein
  numbers with approximation numbers across independent universes and seminormed inner product
  spaces.
* **Finite-dimensional singular values and compactness**
  (`TauCeti.SNumbers.IsSNumberSequence.eq_linearMap_singularValues`,
  `TauCeti.SNumbers.IsSNumberSequence.tendsto_of_isCompactOperator`,
  `TauCeti.SNumbers.IsSNumberSequence.isCompactOperator_iff_tendsto`). Combining uniqueness with
  the Eckart–Young theorem identifies `(s T n : ℝ)` with `(T : H₁ →ₗ[𝕜] H₂).singularValues n` in
  finite dimension, and combining it with
  `ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue` characterizes compact operators
  into complete inner product spaces by `s T n → 0`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §5, Theorem 5.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §2.11.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Uniqueness.lean` and `SNumbers/SingularValuesFinDim.lean`: an earlier Lean
  formalization of Hilbert-space uniqueness on complete spaces.
-/

public section

open Filter UniformSpace
open scoped NNReal Topology

namespace ContinuousLinearMap

section Seminormed

variable {𝕜 H₁ : Type*} [RCLike 𝕜] [SeminormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] in
/-- Perturbation estimate for approximating a finite family `u` in `Completion H₁` within `δ` by
vectors `v` in `H₁`, evaluated on `EuclideanSpace 𝕜 (Fin m)`. -/
private theorem norm_coe_sum_proj_sub_le {m : ℕ} (u : Fin m → Completion H₁) (v : Fin m → H₁)
    {δ : ℝ} (huv : ∀ i, ‖(v i : Completion H₁) - u i‖ ≤ δ) (z : EuclideanSpace 𝕜 (Fin m)) :
    ‖(((∑ i, (EuclideanSpace.proj i).smulRight (v i)) z : H₁) : Completion H₁) -
        ∑ i, z i • u i‖ ≤ (m : ℝ) * δ * ‖z‖ := by
  have heq : (((∑ i, (EuclideanSpace.proj i).smulRight (v i)) z : H₁) : Completion H₁) -
      ∑ i, z i • u i = ∑ i, z i • ((v i : Completion H₁) - u i) := by
    have hsum : ((∑ i, (EuclideanSpace.proj i).smulRight (v i)) z : H₁) = ∑ i, z i • v i := by simp
    have hcoe : ((∑ i, z i • v i : H₁) : Completion H₁) = ∑ i, z i • (v i : Completion H₁) :=
      (map_sum (Completion.toCompl : H₁ →+ Completion H₁) (fun i ↦ z i • v i) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ ↦ Completion.coe_smul (z i) (v i))
    rw [hsum, hcoe, ← Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
  rw [heq]
  calc ‖∑ i, z i • ((v i : Completion H₁) - u i)‖
      ≤ ∑ i, ‖z i • ((v i : Completion H₁) - u i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, ‖z‖ * δ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [norm_smul]
        exact mul_le_mul (PiLp.norm_apply_le z i) (huv i) (norm_nonneg _) (norm_nonneg z)
    _ = (m : ℝ) * δ * ‖z‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

variable {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [SeminormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- Rescaling an operator `A₀` within relative error `η` of an isometric `s`-coercive embedding into
`Completion H₁` produces a contraction `A` on which `T` is `c`-coercive whenever
`(c + ‖T‖) * η ≤ s - c`. -/
private theorem rescale_coercive_of_approx {m : ℕ} (T : H₁ →L[𝕜] H₂)
    (A₀ : EuclideanSpace 𝕜 (Fin m) →L[𝕜] H₁) (g : EuclideanSpace 𝕜 (Fin m) → Completion H₁)
    {c s η : ℝ} (hη : 0 ≤ η) (hsc : (c + ‖T‖) * η ≤ s - c)
    (hg_norm : ∀ z, ‖g z‖ = ‖z‖) (hg_coer : ∀ z, s * ‖z‖ ≤ ‖T.completion (g z)‖)
    (herr : ∀ z, ‖(A₀ z : Completion H₁) - g z‖ ≤ η * ‖z‖) :
    let A : EuclideanSpace 𝕜 (Fin m) →L[𝕜] H₁ := (((1 + η)⁻¹ : ℝ) : 𝕜) • A₀
    ‖A‖ ≤ 1 ∧ ∀ z, c * ‖z‖ ≤ ‖T (A z)‖ := by
  have hη₁ : 0 < 1 + η := by linarith
  refine ⟨opNorm_le_bound _ zero_le_one fun z ↦ ?_, fun z ↦ ?_⟩
  · have hA₀ : ‖A₀ z‖ ≤ (1 + η) * ‖z‖ := by
      calc ‖A₀ z‖ = ‖g z + ((A₀ z : Completion H₁) - g z)‖ := by
            rw [← Completion.norm_coe, add_sub_cancel]
        _ ≤ ‖g z‖ + ‖(A₀ z : Completion H₁) - g z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + η * ‖z‖ := by rw [hg_norm]; gcongr; exact herr z
        _ = (1 + η) * ‖z‖ := by ring
    rw [smul_apply, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hη₁), one_mul]
    exact (mul_le_mul_of_nonneg_left hA₀ (inv_nonneg.mpr hη₁.le)).trans_eq
      (inv_mul_cancel_left₀ hη₁.ne' ‖z‖)
  · have hsz : s * ‖z‖ ≤ ‖T (A₀ z)‖ + ‖T‖ * (η * ‖z‖) := by
      calc s * ‖z‖ ≤ ‖T.completion (g z)‖ := hg_coer z
        _ = ‖(T (A₀ z) : Completion H₂) - T.completion ((A₀ z : Completion H₁) - g z)‖ := by
            rw [map_sub, completion_apply_coe, sub_sub_cancel]
        _ ≤ ‖(T (A₀ z) : Completion H₂)‖ + ‖T.completion ((A₀ z : Completion H₁) - g z)‖ :=
            norm_sub_le _ _
        _ ≤ ‖T (A₀ z)‖ + ‖T‖ * (η * ‖z‖) := by
            rw [Completion.norm_coe, ← T.norm_completion]
            gcongr
            exact (T.completion.le_opNorm _).trans (by gcongr; exact herr z)
    rw [smul_apply, map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hη₁)]
    exact (le_inv_mul_iff₀ hη₁).mpr (by
      nlinarith [norm_nonneg z, mul_le_mul_of_nonneg_right hsc (norm_nonneg z)])

/-- If `0 ≤ c < aₙ(T)`, there is a contraction `A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁` on
which `T` is `c`-coercive. -/
private theorem exists_norm_le_one_coercive (T : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < T.singularValue n) :
    ∃ A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁,
      ‖A‖ ≤ 1 ∧ ∀ z, c * ‖z‖ ≤ ‖T (A z)‖ := by
  rw [← T.singularValue_completion] at hc
  obtain ⟨s, hcs, w, hw, hws⟩ :=
    (TauCeti.hasMinMaxLowerBound_iff.mp TauCeti.HasMinMaxLowerBound.of_completeSpace)
      T.completion n hc₀ hc
  let U : Submodule 𝕜 (Completion H₁) := Submodule.span 𝕜 (Set.range w)
  have : FiniteDimensional 𝕜 U := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range w)
  have hU : Module.finrank 𝕜 U = n + 1 := by rw [finrank_span_eq_card hw, Fintype.card_fin]
  let b : OrthonormalBasis (Fin (n + 1)) 𝕜 U := (stdOrthonormalBasis 𝕜 U).reindex (finCongr hU)
  let eU : EuclideanSpace 𝕜 (Fin (n + 1)) ≃ₗᵢ[𝕜] U :=
    (EuclideanSpace.basisFun (Fin (n + 1)) 𝕜).equiv b (.refl _)
  set D : ℝ := 2 * (c + ‖T‖ + 1) * ((n + 1 : ℕ) : ℝ)
  have hD : 0 < D := by dsimp only [D]; positivity
  set δ : ℝ := (s - c) / D
  have hδ : 0 < δ := div_pos (sub_pos.mpr hcs) hD
  choose v hv using fun i : Fin (n + 1) ↦
    Metric.denseRange_iff.mp Completion.denseRange_coe (b i : Completion H₁) δ hδ
  have hv' (i : Fin (n + 1)) : ‖(v i : Completion H₁) - (b i : Completion H₁)‖ ≤ δ := by
    rw [← dist_eq_norm, dist_comm]
    exact (hv i).le
  set η : ℝ := ((n + 1 : ℕ) : ℝ) * δ
  have hη : 0 ≤ η := mul_nonneg (Nat.cast_nonneg _) hδ.le
  have hsc : (c + ‖T‖) * η ≤ s - c := by
    have h1 : (c + ‖T‖ + 1) * η = (s - c) / 2 := by
      dsimp only [η, δ, D]
      field_simp [hD.ne']
    nlinarith [norm_nonneg T]
  refine ⟨_, rescale_coercive_of_approx T (∑ i, (EuclideanSpace.proj i).smulRight (v i))
    (fun z ↦ (eU z : Completion H₁)) hη hsc
    (fun z ↦ by rw [Submodule.norm_coe, eU.norm_map])
    (fun z ↦ by simpa only [Submodule.norm_coe, eU.norm_map] using hws (eU z) (eU z).2)
    fun z ↦ ?_⟩
  have heU : (eU z : Completion H₁) = ∑ i, z i • (b i : Completion H₁) :=
    (congrArg U.subtype (OrthonormalBasis.equiv_apply_euclideanSpace b z)).trans
      ((map_sum U.subtype (fun i ↦ z i • b i) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ ↦ U.subtype.map_smul (z i) (b i)))
  simpa only [η, heU] using
    norm_coe_sum_proj_sub_le (fun i ↦ (b i : Completion H₁)) v hv' z

/-- **Scalar factorization through Euclidean space.** For a bounded linear map `T : H₁ →L[𝕜] H₂`
between seminormed inner product spaces over `ℝ` or `ℂ` and every `0 ≤ c < aₙ(T)`, the scaled
identity `(c : 𝕜) • id` on `EuclideanSpace 𝕜 (Fin (n + 1))` factors as `B ∘L T ∘L A` with
`‖A‖ ≤ 1` and `‖B‖ ≤ 1`. Neither `H₁` nor `H₂` need be complete or Hausdorff. -/
theorem exists_comp_comp_eq_smul_id (T : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < T.singularValue n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        B ∘L T ∘L A = (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
  rcases hc₀.eq_or_lt with rfl | hc_pos
  · exact ⟨0, 0, by simp, by simp, by ext; simp⟩
  obtain ⟨A, hA, hTA⟩ := T.exists_norm_le_one_coercive n hc_pos.le hc
  let S : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] Completion H₂ :=
    (Completion.toComplL : H₂ →L[𝕜] Completion H₂) ∘L T ∘L A
  have hS_inj : Function.Injective S.toLinearMap :=
    (injective_iff_map_eq_zero _).mpr fun z hz ↦ norm_le_zero_iff.mp <| by
      have h0 : ‖T (A z)‖ = 0 := by simpa [S] using congrArg norm hz
      exact nonpos_of_mul_nonpos_right ((hTA z).trans_eq h0) hc_pos
  let W : Submodule 𝕜 (Completion H₂) := LinearMap.range S.toLinearMap
  let e : EuclideanSpace 𝕜 (Fin (n + 1)) ≃ₗ[𝕜] W := LinearEquiv.ofInjective S.toLinearMap hS_inj
  let B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    ((c : 𝕜) • e.symm.toLinearMap.toContinuousLinearMap) ∘L W.orthogonalProjectionOnto ∘L
      (Completion.toComplL : H₂ →L[𝕜] Completion H₂)
  refine ⟨A, B, hA, opNorm_le_bound B zero_le_one fun y ↦ ?_, ContinuousLinearMap.ext fun z ↦ ?_⟩
  · set w : W := W.orthogonalProjectionOnto (y : Completion H₂)
    set z : EuclideanSpace 𝕜 (Fin (n + 1)) := e.symm w
    have hSz : S z = (w : Completion H₂) := LinearEquiv.ofInjective_symm_apply S.toLinearMap w
    have hcz : c * ‖z‖ ≤ ‖y‖ := by
      calc c * ‖z‖ ≤ ‖T (A z)‖ := hTA z
        _ = ‖S z‖ := by simp [S]
        _ = ‖W.starProjection (y : Completion H₂)‖ := by
            rw [hSz, Submodule.coe_orthogonalProjectionOnto_apply]
        _ ≤ ‖(y : Completion H₂)‖ := W.norm_starProjection_apply_le _
        _ = ‖y‖ := Completion.norm_coe y
    simpa [B, w, z, norm_smul, RCLike.norm_ofReal, abs_of_pos hc_pos] using hcz
  · have hmem : (T (A z) : Completion H₂) ∈ W := LinearMap.mem_range_self S.toLinearMap z
    have hproj : W.orthogonalProjectionOnto (T (A z) : Completion H₂) = e z :=
      Subtype.ext <| (Submodule.coe_orthogonalProjectionOnto_apply W _).trans
        (Submodule.starProjection_eq_self_iff.mpr hmem)
    simp [B, hproj]

/-- Common lower-bound step deducing `aₙ(T) ≤ a` from scalar factorizations of `α • id` on
`EuclideanSpace 𝕜 (Fin (n + 1))` through `T`. -/
private theorem singularValue_le_of_smul_id_le (T : H₁ →L[𝕜] H₂) (n : ℕ) {a : ℝ≥0}
    (h : ∀ (α : 𝕜) (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖₊ ≤ 1 → ‖B‖₊ ≤ 1 →
      B ∘L T ∘L A = α • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) →
      ‖α‖₊ ≤ a) :
    T.singularValue n ≤ a := by
  by_contra! hlt
  obtain ⟨c, hac, hc⟩ := exists_between hlt
  obtain ⟨A, B, hA, hB, hfac⟩ :=
    T.exists_comp_comp_eq_smul_id n c.coe_nonneg (NNReal.coe_lt_coe.mpr hc)
  have hc_norm : ‖((c : ℝ) : 𝕜)‖₊ = c := Subtype.ext (RCLike.norm_of_nonneg c.coe_nonneg)
  exact hac.not_ge
    (hc_norm ▸ h ((c : ℝ) : 𝕜) A B (by exact_mod_cast hA) (by exact_mod_cast hB) hfac)

/-- Between seminormed inner product spaces over `ℝ` or `ℂ`, the Gelfand numbers coincide with the
approximation numbers across arbitrary universes. -/
theorem gelfandNumber_eq_singularValue (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    T.gelfandNumber n = T.singularValue n := by
  refine le_antisymm (le_singularValue_iff.mpr fun R hR ↦ ?_)
    (T.singularValue_le_of_smul_id_le n fun α A B hA hB hfac ↦ ?_)
  · simpa [gelfandNumber_eq_zero_of_rank_le hR] using R.gelfandNumber_add_le (T - R) n
  · have hg := TauCeti.SNumbers.isStrictSNumberSequence_gelfand (𝕜 := 𝕜).toIsSNumberSequence
    calc ‖α‖₊
        = TauCeti.SNumbers.gelfand
            (α • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
          rw [hg.smul, hg.normalize, mul_one]
      _ = (B ∘L T ∘L A).gelfandNumber n := by rw [hfac, TauCeti.SNumbers.gelfand_apply]
      _ ≤ ‖B‖₊ * T.gelfandNumber n * ‖A‖₊ := B.gelfandNumber_comp_comp_le T A n
      _ ≤ 1 * T.gelfandNumber n * 1 := by gcongr
      _ = T.gelfandNumber n := by simp

/-- Between seminormed inner product spaces over `ℝ` or `ℂ`, the Kolmogorov numbers coincide with
the approximation numbers across arbitrary universes. -/
theorem kolmogorovNumber_eq_singularValue (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    T.kolmogorovNumber n = T.singularValue n := by
  refine le_antisymm (le_singularValue_iff.mpr fun R hR ↦ ?_)
    (T.singularValue_le_of_smul_id_le n fun α A B hA hB hfac ↦ ?_)
  · simpa [kolmogorovNumber_eq_zero_of_rank_le hR] using R.kolmogorovNumber_add_le (T - R) n
  · have hk := TauCeti.SNumbers.isSNumberSequence_kolmogorov (𝕜 := 𝕜)
    calc ‖α‖₊
        = TauCeti.SNumbers.kolmogorov
            (α • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
          rw [hk.smul, hk.normalize, mul_one]
      _ = (B ∘L T ∘L A).kolmogorovNumber n := by rw [hfac, TauCeti.SNumbers.kolmogorov_apply]
      _ ≤ ‖B‖₊ * T.kolmogorovNumber n * ‖A‖₊ := B.kolmogorovNumber_comp_comp_le T A n
      _ ≤ 1 * T.kolmogorovNumber n * 1 := by gcongr
      _ = T.kolmogorovNumber n := by simp

end Seminormed

section NormedSource

variable {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [SeminormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- From a normed inner product space into a seminormed inner product space over `ℝ` or `ℂ`, the
Bernstein numbers coincide with the approximation numbers across arbitrary universes. -/
theorem bernsteinNumber_eq_singularValue (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    T.bernsteinNumber n = T.singularValue n := by
  refine le_antisymm (le_singularValue_iff.mpr fun R hR ↦ ?_)
    (T.singularValue_le_of_smul_id_le n fun α A B hA hB hfac ↦ ?_)
  · simpa [bernsteinNumber_eq_zero_of_rank_le hR] using R.bernsteinNumber_add_le (T - R) n
  · have hb := TauCeti.SNumbers.isStrictSNumberSequence_bernstein (𝕜 := 𝕜).toIsSNumberSequence
    calc ‖α‖₊
        = TauCeti.SNumbers.bernstein
            (α • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
          rw [hb.smul, hb.normalize, mul_one]
      _ = (B ∘L T ∘L A).bernsteinNumber n := by rw [hfac, TauCeti.SNumbers.bernstein_apply]
      _ ≤ ‖B‖₊ * T.bernsteinNumber n * ‖A‖₊ := B.bernsteinNumber_comp_comp_le T A n
      _ ≤ 1 * T.bernsteinNumber n * 1 := by gcongr
      _ = T.bernsteinNumber n := by simp

end NormedSource

end ContinuousLinearMap

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]

/-- **Uniqueness of s-number sequences on inner product spaces.** Over `ℝ` or `ℂ`, every s-number
sequence agrees with the approximation numbers on bounded operators between inner product spaces,
without completeness assumptions on the domain or codomain. -/
theorem IsSNumberSequence.eq_singularValue {s : SNumberFamily 𝕜} (hs : IsSNumberSequence s)
    {H₁ H₂ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) : s T n = T.singularValue n := by
  refine (hs.le_singularValue T n).antisymm
    (T.singularValue_le_of_smul_id_le n fun α A B hA hB hfac ↦ ?_)
  calc ‖α‖₊
      = s (α • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
        rw [hs.smul, hs.normalize, mul_one]
    _ = s (B ∘L T ∘L A) n := by rw [hfac]
    _ ≤ ‖B‖₊ * s T n * ‖A‖₊ := hs.comp_le B T A n
    _ ≤ 1 * s T n * 1 := by gcongr
    _ = s T n := by simp

/-- Any two s-number sequences agree on bounded operators between inner product spaces. -/
theorem IsSNumberSequence.eq_of_innerProductSpace {s t : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s) (ht : IsSNumberSequence t)
    {H₁ H₂ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) : s T n = t T n := by
  rw [hs.eq_singularValue, ht.eq_singularValue]

/-- Every s-number sequence, strict or not, satisfies strict identity normalization on all inner
product spaces: `s (id_H) n` is `1` strictly below `Module.rank 𝕜 H` and `0` from it on. -/
theorem IsSNumberSequence.apply_id {s : SNumberFamily 𝕜} (hs : IsSNumberSequence s)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (n : ℕ) :
    s (ContinuousLinearMap.id 𝕜 H) n = if (n : Cardinal) < Module.rank 𝕜 H then 1 else 0 := by
  rw [hs.eq_singularValue, ContinuousLinearMap.singularValue_id]

/-- **Finite-dimensional singular values.** Between finite-dimensional inner product spaces, every
s-number sequence equals `LinearMap.singularValues`. -/
theorem IsSNumberSequence.eq_linearMap_singularValues {s : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s)
    {H₁ H₂ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [FiniteDimensional 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    (s T n : ℝ) = (T : H₁ →ₗ[𝕜] H₂).singularValues n := by
  rw [hs.eq_singularValue, T.singularValue_eq_linearMap_singularValues]

/-- For a compact operator between inner product spaces, every s-number sequence tends to zero.
Neither space need be complete. -/
theorem IsSNumberSequence.tendsto_of_isCompactOperator {s : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s)
    {H₁ H₂ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    {T : H₁ →L[𝕜] H₂} (hT : IsCompactOperator T) :
    Tendsto (s T) atTop (𝓝 0) := by
  simpa only [funext (hs.eq_singularValue T)] using hT.tendsto_singularValue

/-- **Compactness criterion on Hilbert spaces.** A bounded operator from an inner product space
into a complete inner product space is compact if and only if its s-numbers tend to zero, for any
s-number sequence `s`. The domain need not be complete. -/
theorem IsSNumberSequence.isCompactOperator_iff_tendsto {s : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s)
    {H₁ H₂ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    {T : H₁ →L[𝕜] H₂} :
    IsCompactOperator T ↔ Tendsto (s T) atTop (𝓝 0) := by
  simpa only [funext (hs.eq_singularValue T)] using
    ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue

end TauCeti.SNumbers
