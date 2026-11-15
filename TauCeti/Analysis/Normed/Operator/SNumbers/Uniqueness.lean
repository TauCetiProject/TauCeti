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
import TauCeti.Analysis.InnerProductSpace.Gram.Factor
import TauCeti.Analysis.Normed.Operator.FiniteDimensional

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
  which `T.completion` is `s`-coercive for some `s > c`, approximating an isometric embedding into
  `H₁` via `ContinuousLinearMap.denseRange_comp` and rescaling gives a contraction `A` on which `T`
  remains `c`-coercive, and Douglas factorization (`ContinuousLinearMap.factorThru`) in
  `Completion H₂` constructs the contraction `B`.
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
  scalar field's universe, we also record across independent universes that Gelfand numbers equal
  approximation numbers from any seminormed inner product space into any seminormed space,
  Kolmogorov numbers equal approximation numbers from any seminormed space into any seminormed
  inner product space, and Bernstein numbers equal approximation numbers from any normed inner
  product space into any seminormed inner product space.
* **Finite-dimensional singular values and compactness**
  (`TauCeti.SNumbers.IsSNumberSequence.eq_linearMap_singularValues`,
  `TauCeti.SNumbers.IsSNumberSequence.tendsto_of_isCompactOperator`,
  `TauCeti.SNumbers.IsSNumberSequence.isCompactOperator_iff_tendsto`). Combining uniqueness with
  the Eckart–Young theorem identifies `(s T n : ℝ)` with `(T : H₁ →ₗ[𝕜] H₂).singularValues n` in
  finite dimension, `IsCompactOperator.tendsto_singularValue` forces `s T n → 0` for compact
  operators from normed spaces into inner product spaces, and
  `ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue` characterizes compact operators
  from inner product spaces into complete inner product spaces by `s T n → 0`.

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
  let G : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] Completion H₁ :=
    U.subtypeL ∘L eU.toLinearIsometry.toContinuousLinearMap
  set η : ℝ := (s - c) / (2 * (c + ‖T‖ + 1))
  have hη_pos : 0 < η := div_pos (sub_pos.mpr hcs) (by positivity)
  have hdense : DenseRange (Completion.toComplL : H₁ →L[𝕜] Completion H₁) :=
    Completion.denseRange_coe
  obtain ⟨A₀, hA₀⟩ := Metric.denseRange_iff.mp (denseRange_comp hdense) G η hη_pos
  have hsc : (c + ‖T‖) * η ≤ s - c := by
    have h1 : (c + ‖T‖ + 1) * η = (s - c) / 2 := by
      dsimp only [η]
      field_simp [show (2 * (c + ‖T‖ + 1) : ℝ) ≠ 0 by positivity]
    nlinarith [norm_nonneg T]
  have hG_norm (z : EuclideanSpace 𝕜 (Fin (n + 1))) : ‖G z‖ = ‖z‖ :=
    (Submodule.norm_coe (eU z)).trans (eU.norm_map z)
  refine ⟨_, rescale_coercive_of_approx T A₀ G hη_pos.le hsc hG_norm
    (fun z ↦ by rw [← hG_norm]; exact hws (eU z) (eU z).2)
    fun z ↦ ?_⟩
  rw [dist_comm, dist_eq_norm] at hA₀
  exact (((Completion.toComplL : H₁ →L[𝕜] Completion H₁) ∘L A₀ - G).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hA₀.le (norm_nonneg z))

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
  obtain ⟨A, hA, hTA⟩ := T.exists_norm_le_one_coercive n hc₀ hc
  let T₀ : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))
  let S : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] Completion H₂ :=
    (Completion.toComplL : H₂ →L[𝕜] Completion H₂) ∘L T ∘L A
  have hbound (z : EuclideanSpace 𝕜 (Fin (n + 1))) : ‖T₀ z‖ ≤ 1 * ‖S z‖ := by
    simpa [T₀, S, norm_smul, abs_of_nonneg hc₀] using hTA z
  let B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    (T₀.factorThru S) ∘L (Completion.toComplL : H₂ →L[𝕜] Completion H₂)
  have hB : ‖B‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans ?_
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (Completion.toComplₗᵢ : H₂ →ₗᵢ[𝕜] Completion H₂).norm_toContinuousLinearMap_le).trans
        (norm_factorThru_le zero_le_one hbound)
  refine ⟨A, B, hA, hB, ?_⟩
  calc B ∘L T ∘L A = (T₀.factorThru S) ∘L S := by simp only [B, S, comp_assoc]
    _ = T₀ := factorThru_comp ⟨1, hbound⟩

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

end Seminormed

section Gelfand

variable {𝕜 H₁ F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

omit [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] in
/-- Mapping a submodule `M` of codimension at most `n` into `Completion H₁` leaves an orthogonal
complement of dimension at most `n`: the orthogonal projection onto `M₀ᗮ` descends to `H₁ ⧸ M`
with dense, finite-dimensional, hence closed range. -/
private theorem rank_orthogonal_map_toComplL_le {M : Submodule 𝕜 H₁} {n : ℕ}
    (hM : Module.rank 𝕜 (H₁ ⧸ M) ≤ n) :
    Module.rank 𝕜 (M.map (Completion.toComplL : H₁ →L[𝕜] Completion H₁).toLinearMap)ᗮ ≤ n := by
  let j : H₁ →L[𝕜] Completion H₁ := Completion.toComplL
  let M₀ : Submodule 𝕜 (Completion H₁) := M.map j.toLinearMap
  let φ : H₁ →L[𝕜] M₀ᗮ := M₀ᗮ.orthogonalProjectionOnto ∘L j
  have hker : M ≤ LinearMap.ker φ.toLinearMap := fun x hx ↦
    LinearMap.mem_ker.mpr <| M₀ᗮ.orthogonalProjectionOnto_eq_zero_iff.mpr
      (M₀.le_orthogonal_orthogonal (Submodule.mem_map_of_mem hx))
  let ψ : (H₁ ⧸ M) →ₗ[𝕜] M₀ᗮ := M.liftQ φ.toLinearMap hker
  have hrange_le : Module.rank 𝕜 (LinearMap.range φ.toLinearMap) ≤ n := by
    rw [← M.liftQ_mkQ φ.toLinearMap hker]
    exact (LinearMap.rank_comp_le_left M.mkQ ψ).trans ((LinearMap.rank_le_domain ψ).trans hM)
  have : FiniteDimensional 𝕜 (LinearMap.range φ.toLinearMap) :=
    Module.rank_lt_aleph0_iff.mp (hrange_le.trans_lt Cardinal.natCast_lt_aleph0)
  have hsurj : Function.Surjective M₀ᗮ.orthogonalProjectionOnto :=
    fun y ↦ ⟨y, M₀ᗮ.orthogonalProjectionOnto_mem_subspace_eq_self y⟩
  have hdense : DenseRange φ :=
    hsurj.denseRange.comp Completion.denseRange_coe M₀ᗮ.orthogonalProjectionOnto.continuous
  have htop : LinearMap.range φ.toLinearMap = ⊤ :=
    SetLike.coe_injective <|
      (LinearMap.range φ.toLinearMap).isClosed_of_finiteDimensional.closure_eq.symm.trans
        hdense.closure_range
  rwa [← rank_top, ← htop]

/-- From a seminormed inner product space into an arbitrary seminormed space over `ℝ` or `ℂ`, the
Gelfand numbers coincide with the approximation numbers across arbitrary universes. -/
theorem gelfandNumber_eq_singularValue (T : H₁ →L[𝕜] F) (n : ℕ) :
    T.gelfandNumber n = T.singularValue n := by
  refine le_antisymm (le_singularValue_iff.mpr fun R hR ↦ ?_)
    (le_gelfandNumber_iff.mpr fun M _ hM ↦ ?_)
  · simpa [gelfandNumber_eq_zero_of_rank_le hR] using R.gelfandNumber_add_le (T - R) n
  · let M₀ : Submodule 𝕜 (Completion H₁) :=
      M.map (Completion.toComplL : H₁ →L[𝕜] Completion H₁).toLinearMap
    calc T.singularValue n
        = T.completion.singularValue n := (T.singularValue_completion n).symm
      _ ≤ ‖T.completion ∘L M₀ᗮᗮ.subtypeL‖₊ :=
          T.completion.singularValue_le_nnnorm_comp_orthogonal (rank_orthogonal_map_toComplL_le hM)
      _ = ‖T.completion ∘L M₀.topologicalClosure.subtypeL‖₊ := by
          rw [M₀.orthogonal_orthogonal_eq_closure]
      _ = ‖T.completion ∘L M₀.subtypeL‖₊ :=
          T.completion.nnnorm_comp_subtypeL_topologicalClosure M₀
      _ ≤ ‖T ∘L M.subtypeL‖₊ := by
          rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]
          refine opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_
          rcases y with ⟨_, m, hm, rfl⟩
          simpa only [comp_apply, Submodule.coe_subtypeL, Submodule.coe_subtype, coe_coe,
            Completion.coe_toComplL, completion_apply_coe, Completion.norm_coe,
            ← Submodule.norm_coe] using (T ∘L M.subtypeL).le_opNorm ⟨m, hm⟩

end Gelfand

section Kolmogorov

variable {𝕜 E H₂ : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- From an arbitrary seminormed space into a seminormed inner product space over `ℝ` or `ℂ`, the
Kolmogorov numbers coincide with the approximation numbers across arbitrary universes. -/
theorem kolmogorovNumber_eq_singularValue (T : E →L[𝕜] H₂) (n : ℕ) :
    T.kolmogorovNumber n = T.singularValue n := by
  refine le_antisymm (le_singularValue_iff.mpr fun R hR ↦ ?_)
    (le_kolmogorovNumber_iff.mpr fun V hV ↦ ?_)
  · simpa [kolmogorovNumber_eq_zero_of_rank_le hR] using R.kolmogorovNumber_add_le (T - R) n
  · let j : H₂ →L[𝕜] Completion H₂ := Completion.toComplL
    let T' : E →L[𝕜] Completion H₂ := j ∘L T
    let W : Submodule 𝕜 (Completion H₂) := V.map j.toLinearMap
    have hW : Module.rank 𝕜 W ≤ n := (rank_map_le _ _).trans hV
    have : FiniteDimensional 𝕜 W :=
      Module.rank_lt_aleph0_iff.mp (hW.trans_lt Cardinal.natCast_lt_aleph0)
    let R' : E →L[𝕜] Completion H₂ := W.starProjection ∘L T'
    have hR' : R'.rank ≤ n := by
      refine (LinearMap.rank_comp_le_left _ _).trans ?_
      rwa [LinearMap.rank, Submodule.range_starProjection]
    rw [← T.singularValue_toComplL_comp]
    refine (T'.singularValue_le_nnnorm_sub hR').trans ?_
    rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]
    refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    calc ‖(T' - R') x‖
        = dist (T' x) (W.starProjection (T' x)) := by rw [sub_apply, dist_eq_norm]; rfl
      _ = Metric.infDist (T' x) (W : Set (Completion H₂)) :=
          Submodule.dist_starProjection_eq_infDist W (T' x)
      _ ≤ Metric.infDist (T x) (V : Set H₂) :=
          (Metric.le_infDist ⟨0, V.zero_mem⟩).mpr fun v hv ↦
            (Metric.infDist_le_dist_of_mem (Submodule.mem_map_of_mem hv)).trans_eq
              (Completion.dist_eq (T x) v)
      _ = ‖(V.mkQL ∘L T) x‖ := by rw [comp_apply, V.norm_mkQL_apply]
      _ ≤ ‖V.mkQL ∘L T‖ * ‖x‖ := (V.mkQL ∘L T).le_opNorm x

end Kolmogorov

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

/-- For a compact operator from a normed space into an inner product space, every s-number sequence
tends to zero. Neither space need be complete. -/
theorem IsSNumberSequence.tendsto_of_isCompactOperator {s : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s)
    {X H₂ : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    {T : X →L[𝕜] H₂} (hT : IsCompactOperator T) :
    Tendsto (s T) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT.tendsto_singularValue
    (fun _ ↦ zero_le) (hs.le_singularValue T)

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
