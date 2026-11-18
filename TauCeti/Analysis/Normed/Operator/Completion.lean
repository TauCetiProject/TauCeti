/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Group.ControlledClosure
public import Mathlib.Analysis.Normed.Group.HomCompletion
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Normed.Group.BallSphere
public import TauCeti.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Normed.Operator.FiniteDimensional

/-!
# Operator norms, finite rank, and coercivity of bounded maps extended to completions

A bounded semilinear map `f : E →SL[σ₁₂] F` between seminormed spaces extends to the bounded
map `f.completion` between the completions, and, when `F` is complete and Hausdorff, to the
bounded map `f.fromCompletion` from the completion of `E` to `F`. Since `E` has dense image in
its completion and the canonical map preserves norms, neither extension changes the operator norm.

These are the continuous semilinear analogues of Mathlib's `NormedAddGroupHom.norm_completion`.
They make extension to completions an isometric operation, as needed for the norm-preserving
universal properties of completed normed constructions. Likewise, a linear isometric equivalence
extends to the linear isometric equivalence `e.completion` between the completions, the analogue
for equivalences of Mathlib's `LinearIsometry.completion`.

Extension to completions also preserves metric quotient maps. If `f` lifts every vector of norm
less than `r` to a vector of norm less than `r`, so does `f.completion`; the lifts in the
completion come from Mathlib's `controlled_closure_range_of_complete`. An operator of norm at most
one with this lifting property maps each open ball about `0` onto the open ball of the same radius
(`ContinuousLinearMap.image_ball_eq_ball`), so by `ContinuousLinearMap.norm_completion` its
extension to the completions has the same property.

Over a complete scalar field, finite rank bounds are also preserved: if `T : E →L[𝕜] F` has rank at
most `n`, its image in `Completion F` is finite-dimensional and hence closed, so by density of `E`
in `Completion E` the extensions `T.completion` and (for complete Hausdorff `F`) `T.fromCompletion`
have rank at most `n`. Completeness of `𝕜` cannot be omitted (`id : ℚ →L[ℚ] ℚ` has `ℚ`-rank `1`,
whereas its completion `ℝ →L[ℚ] ℝ` has infinite `ℚ`-rank), and the bound does not extend to
infinite cardinals (`id` on finitely supported `ℓ²`-sequences has rank `ℵ₀`, whereas `ℓ²(ℕ)` has
uncountable Hamel dimension).

Over `ℝ` or `ℂ`, coercivity bounds for `T.completion` on finite-dimensional domains also pull back
into the uncompleted space `E` without increasing the norm bound, at an arbitrarily small loss in
the coercivity constant: if `T.completion ∘L A'` is `s`-coercive on a finite-dimensional normed
space `V` and `c < s`, then `ContinuousLinearMap.denseRange_comp` and rescaling produce
`A : V →L[𝕜] E` with `‖A‖ ≤ ‖A'‖` such that `T ∘L A` is `c`-coercive.

## Main results

* `ContinuousLinearMap.norm_completion`: `‖f.completion‖ = ‖f‖`.
* `ContinuousLinearMap.norm_fromCompletion`: `‖f.fromCompletion‖ = ‖f‖`.
* `ContinuousLinearMap.norm_toComplL_comp` and `ContinuousLinearMap.eNorm_toComplL_comp`:
  composing with the embedding of the codomain into its completion preserves the operator norm.
* `ContinuousLinearMap.ball_subset_image_completion_ball` and
  `ContinuousLinearMap.image_completion_ball`: the extension of a metric quotient map to the
  completions is a metric quotient map.
* `ContinuousLinearMap.rank_completion_le_of_rank_le` and
  `ContinuousLinearMap.rank_fromCompletion_le_of_rank_le`: over a complete field, extending a
  bounded linear map of rank at most `n` (`n : ℕ`) to completions preserves `rank ≤ n`.
* `ContinuousLinearMap.exists_norm_le_and_mul_norm_le_norm_apply_of_completion`: over `ℝ` or `ℂ`,
  a finite-dimensional map into `Completion E` making `T.completion` strictly more than
  `c`-coercive can be pulled back to `E` with norm at most `‖A'‖` and `T` still `c`-coercive.
* `LinearIsometryEquiv.completion`: the extension of a linear isometric equivalence to the
  completions.
* `LinearIsometryEquiv.toLinearIsometry_completion`: as a linear isometry, it is
  `LinearIsometry.completion`.
* `LinearIsometryEquiv.completion_symm`, `LinearIsometryEquiv.completion_refl`,
  `LinearIsometryEquiv.completion_trans`: extension to completions is compatible with inverses,
  identities and composites.
* `UniformSpace.Completion.separationQuotientEquiv`: the canonical linear isometric equivalence
  `Completion (SeparationQuotient E) ≃ₗᵢ[𝕜] Completion E`, together with its equivariance
  (`separationQuotientEquiv_smul`, `separationQuotientEquiv_symm_smul`) for uniformly continuous
  scalar actions.
-/

public section

open UniformSpace

namespace ContinuousLinearMap

section Semilinear

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

omit [RingHomIsometric σ₁₂] in
/-- Extending a bounded semilinear map to the completions of its domain and codomain preserves
its operator norm. -/
@[simp]
theorem norm_completion (f : E →SL[σ₁₂] F) : ‖f.completion‖ = ‖f‖ := by
  rw [norm_def, norm_def]
  congr 1
  ext c
  refine and_congr_right fun _ ↦ ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · simpa only [completion_apply_coe, Completion.norm_coe] using h x
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simpa only [completion_apply_coe, Completion.norm_coe] using h x

omit [RingHomIsometric σ₁₂] in
/-- Extending a bounded semilinear map into a complete Hausdorff space to the completion of its
domain preserves its operator norm. -/
@[simp]
theorem norm_fromCompletion [T0Space F] [CompleteSpace F] (f : E →SL[σ₁₂] F) :
    ‖f.fromCompletion‖ = ‖f‖ := by
  rw [norm_def, norm_def]
  congr 1
  ext c
  refine and_congr_right fun _ ↦ ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · simpa only [fromCompletion_apply_coe, Completion.norm_coe] using h x
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simpa only [fromCompletion_apply_coe, Completion.norm_coe] using h x

/-- If `f` lifts every vector of norm less than `r` to a vector of norm less than `r`, then so
does its extension `f.completion` to the completions. -/
theorem ball_subset_image_completion_ball {f : E →SL[σ₁₂] F}
    (hf : ∀ r, Metric.ball (0 : F) r ⊆ f '' Metric.ball 0 r) (r : ℝ) :
    Metric.ball (0 : Completion F) r ⊆ f.completion '' Metric.ball 0 r := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  -- Choose `δ > 0` with `(1 + δ + δ) * ‖w‖ < r`.
  obtain ⟨δ, hδ, hδw⟩ := exists_pos_mul_lt (sub_pos.2 hw) (2 * ‖w‖)
  have hδr : (1 + δ + δ) * ‖w‖ < r := by linarith
  -- Points of `F` lift with constant `1 + δ`, so points of the completion lift with `1 + δ + δ`.
  let g := f.completion.toLinearMap.toAddMonoidHom.mkNormedAddGroupHom ‖f.completion‖
    f.completion.le_opNorm
  have hyp (k : F) : ∃ x, g x = NormedAddCommGroup.toCompl k ∧ ‖x‖ ≤ (1 + δ) * ‖k‖ := by
    rcases (norm_nonneg k).eq_or_lt with hk | hk
    · refine ⟨0, ?_, by rw [norm_zero]; positivity⟩
      rw [map_zero, eq_comm, ← norm_eq_zero, NormedAddCommGroup.norm_toCompl, hk]
    · obtain ⟨x, hfx, hx⟩ := TauCeti.exists_apply_eq_norm_lt_add hf k (mul_pos hδ hk)
      refine ⟨x, ?_, by rw [Completion.norm_coe]; linarith⟩
      -- `g` is `f.completion` as a bundled normed group hom, so they agree by definition.
      change f.completion x = k
      rw [completion_apply_coe, hfx]
  obtain ⟨x, hx, hxw⟩ := controlled_closure_range_of_complete NormedAddCommGroup.norm_toCompl
    (by positivity) hδ hyp w (NormedAddCommGroup.denseRange_toCompl w)
  exact ⟨x, mem_ball_zero_iff.2 (hxw.trans_lt hδr), hx⟩

/-- The extension to the completions of a **metric quotient map** is a metric quotient map: if
`‖f‖ ≤ 1` and `f` lifts every vector of norm less than `r` to a vector of norm less than `r`,
then `f.completion` maps each open ball about `0` onto the open ball of the same radius. -/
theorem image_completion_ball {f : E →SL[σ₁₂] F} (hf₁ : ‖f‖ ≤ 1)
    (hf : ∀ r, Metric.ball (0 : F) r ⊆ f '' Metric.ball 0 r) (r : ℝ) :
    f.completion '' Metric.ball 0 r = Metric.ball 0 r :=
  image_ball_eq_ball (f.norm_completion.trans_le hf₁) (ball_subset_image_completion_ball hf) r

omit [RingHomIsometric σ₁₂] in
/-- Composing a bounded semilinear map with the embedding of its codomain into the completion does
not change its operator norm. -/
@[simp]
theorem norm_toComplL_comp (f : E →SL[σ₁₂] F) :
    ‖(Completion.toComplL : F →L[𝕜₂] Completion F) ∘SL f‖ = ‖f‖ := by
  simp only [norm_def, comp_apply, Completion.coe_toComplL, Completion.norm_coe]

/-- Composing a bounded semilinear map with the embedding of its codomain into the completion does
not change its operator `ℝ≥0∞`-norm. -/
@[simp]
theorem eNorm_toComplL_comp (f : E →SL[σ₁₂] F) :
    ‖(Completion.toComplL : F →L[𝕜₂] Completion F) ∘SL f‖ₑ = ‖f‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_toComplL_comp]

end Semilinear

section Rank

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over a complete scalar field, extending a bounded linear map of rank at most `n` to the
completions of its domain and codomain preserves the bound `rank ≤ n`. -/
theorem rank_completion_le_of_rank_le (T : E →L[𝕜] F) {n : ℕ} (hT : T.rank ≤ n) :
    T.completion.rank ≤ n := by
  set W : Submodule 𝕜 (Completion F) :=
    LinearMap.range ((Completion.toComplL : F →L[𝕜] Completion F) ∘L T : E →ₗ[𝕜] Completion F)
  have hW : Module.rank 𝕜 W ≤ n :=
    (LinearMap.rank_comp_le_right _ _).trans hT
  have : FiniteDimensional 𝕜 W :=
    Module.rank_lt_aleph0_iff.mp (hW.trans_lt Cardinal.natCast_lt_aleph0)
  have hrange : LinearMap.range (T.completion : Completion E →ₗ[𝕜] Completion F) ≤ W := by
    rintro _ ⟨x, rfl⟩
    refine Completion.induction_on x
      (W.isClosed_of_finiteDimensional.preimage T.completion.continuous) fun a ↦ ?_
    simp [W]
  exact (Submodule.rank_mono hrange).trans hW

/-- Over a complete scalar field, extending a bounded linear map of rank at most `n` into a
complete Hausdorff space to `Completion E` preserves the bound `rank ≤ n`. -/
theorem rank_fromCompletion_le_of_rank_le [T0Space F] [CompleteSpace F] (T : E →L[𝕜] F) {n : ℕ}
    (hT : T.rank ≤ n) : T.fromCompletion.rank ≤ n := by
  rw [T.fromCompletion_unique ((ContinuousLinearMap.id 𝕜 F).fromCompletion ∘L T.completion)
    fun _ ↦ by simp]
  exact (LinearMap.rank_comp_le_right _ _).trans (T.rank_completion_le_of_rank_le hT)

end Rank

section Coercive

variable {𝕜 V E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `s * ‖u‖ ≤ ‖T.completion (A' u)‖` for all `u` in a finite-dimensional normed space `V` and
`c < s`, then there exists `A : V →L[𝕜] E` with `‖A‖ ≤ ‖A'‖` such that `c * ‖u‖ ≤ ‖T (A u)‖` for
all `u`. -/
theorem exists_norm_le_and_mul_norm_le_norm_apply_of_completion
    (T : E →L[𝕜] F) {A' : V →L[𝕜] Completion E} {c s : ℝ} (hcs : c < s)
    (hs : ∀ u : V, s * ‖u‖ ≤ ‖T.completion (A' u)‖) :
    ∃ A : V →L[𝕜] E, ‖A‖ ≤ ‖A'‖ ∧ ∀ u : V, c * ‖u‖ ≤ ‖T (A u)‖ := by
  -- Trivial case `c ≤ 0`: `A = 0` satisfies both bounds.
  rcases le_or_gt c 0 with hc | hc_pos
  · exact ⟨0, by simp, fun u ↦ (mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg u)).trans
      (norm_nonneg _)⟩
  -- Trivial case `‖A'‖ = 0`: `A' = 0`, so `hs` forces `‖u‖ = 0` for every `u`.
  rcases (norm_nonneg A').eq_or_lt with hR0 | hR
  · refine ⟨0, by simp, fun u ↦ ?_⟩
    have hu : s * ‖u‖ ≤ 0 := by simpa [norm_eq_zero.mp hR0.symm] using hs u
    simp [le_antisymm (nonpos_of_mul_nonpos_right hu (hc_pos.trans hcs)) (norm_nonneg u)]
  -- Nondegenerate case `0 < c` and `0 < ‖A'‖`: approximate `A'` by `toComplL ∘L A₀` and rescale.
  set R : ℝ := ‖A'‖
  let ι : E →L[𝕜] Completion E := Completion.toComplL
  have hD : 0 < c + R * ‖T‖ + 1 := by positivity
  set δ : ℝ := R * (s - c) / (c + R * ‖T‖ + 1)
  have hδ : 0 < δ := div_pos (mul_pos hR (sub_pos.mpr hcs)) hD
  obtain ⟨A₀, hA₀_dist⟩ := Metric.denseRange_iff.mp
    (ContinuousLinearMap.denseRange_comp (g := ι) Completion.denseRange_coe) A' δ hδ
  have hA₀_err : ‖A' - ι ∘L A₀‖ ≤ δ := (dist_eq_norm A' (ι ∘L A₀)).symm.trans_le hA₀_dist.le
  have hA₀_norm : ‖A₀‖ ≤ R + δ := by
    rw [← norm_toComplL_comp (f := A₀)]
    exact (norm_le_insert A' (ι ∘L A₀)).trans (add_le_add le_rfl hA₀_err)
  have hRδ : 0 < R + δ := by positivity
  have hδ_le : (c + R * ‖T‖) * δ ≤ R * (s - c) :=
    (mul_le_mul_of_nonneg_right (by linarith) hδ.le).trans_eq (mul_div_cancel₀ _ hD.ne')
  let A : V →L[𝕜] E := ((R / (R + δ) : ℝ) : 𝕜) • A₀
  refine ⟨A, ?_, fun u ↦ ?_⟩
  · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (div_pos hR hRδ)]
    exact (mul_le_mul_of_nonneg_left hA₀_norm (by positivity)).trans_eq (div_mul_cancel₀ R hRδ.ne')
  · have herr : ‖T.completion (A' u) - T.completion (ι (A₀ u))‖ ≤ ‖T‖ * (δ * ‖u‖) := by
      calc ‖T.completion (A' u) - T.completion (ι (A₀ u))‖
          = ‖T.completion ((A' - ι ∘L A₀) u)‖ := by simp [map_sub]
        _ ≤ ‖T.completion‖ * ‖(A' - ι ∘L A₀) u‖ := T.completion.le_opNorm _
        _ ≤ ‖T‖ * (δ * ‖u‖) := by
          rw [T.norm_completion]
          exact mul_le_mul_of_nonneg_left
            (((A' - ι ∘L A₀).le_opNorm u).trans (by gcongr)) (norm_nonneg _)
    have htri : s * ‖u‖ - ‖T‖ * (δ * ‖u‖) ≤ ‖T (A₀ u)‖ := by
      have h := norm_le_insert (T.completion (ι (A₀ u))) (T.completion (A' u))
      rw [norm_sub_rev] at h
      have hnorm : ‖T.completion (ι (A₀ u))‖ = ‖T (A₀ u)‖ := by simp [ι]
      linarith [hs u]
    have hTA : ‖T (A u)‖ = R / (R + δ) * ‖T (A₀ u)‖ := by
      dsimp only [A]
      rw [smul_apply, map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos (div_pos hR hRδ)]
    rw [hTA, div_mul_eq_mul_div, le_div_iff₀ hRδ]
    calc c * ‖u‖ * (R + δ) = c * (R + δ) * ‖u‖ := by ring
      _ ≤ R * (s - ‖T‖ * δ) * ‖u‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg u)
      _ = R * (s * ‖u‖ - ‖T‖ * (δ * ‖u‖)) := by ring
      _ ≤ R * ‖T (A₀ u)‖ := by gcongr

end Coercive

end ContinuousLinearMap

namespace LinearIsometryEquiv

variable {𝕜 𝕜₂ E F : Type*} [NormedField 𝕜] [NormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- Extend a linear isometric equivalence `e : E ≃ₛₗᵢ[σ₁₂] F` to a linear isometric equivalence
between the completions of `E` and `F`. -/
noncomputable def completion (e : E ≃ₛₗᵢ[σ₁₂] F) : Completion E ≃ₛₗᵢ[σ₁₂] Completion F :=
  e.toLinearEquiv.extendOfIsometry Completion.toComplₗᵢ.toLinearMap
    Completion.toComplₗᵢ.toLinearMap Completion.denseRange_coe Completion.denseRange_coe
    fun x ↦ by simp

/-- On `E`, the extension of `e` to the completions is `e`. -/
@[simp]
theorem completion_apply_coe (e : E ≃ₛₗᵢ[σ₁₂] F) (x : E) : e.completion x = e x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- On `F`, the inverse of the extension of `e` to the completions is `e.symm`. -/
theorem completion_symm_apply_coe (e : E ≃ₛₗᵢ[σ₁₂] F) (y : F) :
    e.completion.symm y = e.symm y :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ y

/-- The extension of `e` to the completions is `UniformSpace.Completion.map e`. -/
@[simp low]
theorem coe_completion (e : E ≃ₛₗᵢ[σ₁₂] F) : ⇑e.completion = Completion.map e :=
  Completion.ext e.completion.continuous Completion.continuous_map fun x ↦ by
    rw [completion_apply_coe, Completion.map_coe e.isometry.uniformContinuous]

/-- The inverse of the extension of `e` to the completions is the extension of `e.symm`. -/
@[simp]
theorem completion_symm (e : E ≃ₛₗᵢ[σ₁₂] F) : e.completion.symm = e.symm.completion := by
  ext y
  induction y using Completion.induction_on with
  | hp => exact isClosed_eq e.completion.symm.continuous e.symm.completion.continuous
  | ih y => rw [completion_symm_apply_coe, completion_apply_coe]

variable (𝕜 E) in
/-- The extension of the identity to the completion is the identity. -/
@[simp]
theorem completion_refl :
    (LinearIsometryEquiv.refl 𝕜 E).completion = LinearIsometryEquiv.refl 𝕜 (Completion E) := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (LinearIsometryEquiv.refl 𝕜 E).completion.continuous continuous_id
  | ih x => simp

/-- Extending a composite of linear isometric equivalences to the completions is the composite
of their extensions. -/
@[simp]
theorem completion_trans {𝕜₃ G : Type*} [NormedField 𝕜₃] [SeminormedAddCommGroup G]
    [NormedSpace 𝕜₃ G] {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₃₂ : 𝕜₃ →+* 𝕜₂} {σ₁₃ : 𝕜 →+* 𝕜₃}
    {σ₃₁ : 𝕜₃ →+* 𝕜} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
    [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
    [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] (e : E ≃ₛₗᵢ[σ₁₂] F) (e' : F ≃ₛₗᵢ[σ₂₃] G) :
    (e.trans e').completion = e.completion.trans e'.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (e.trans e').completion.continuous
      (e.completion.trans e'.completion).continuous
  | ih x => simp

end SeminormedAddCommGroup

section NormedAddCommGroup

variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- As a linear isometry, the extension of `e` to the completions is the extension
`LinearIsometry.completion` of `e` viewed as a linear isometry. -/
@[simp]
theorem toLinearIsometry_completion (e : E ≃ₛₗᵢ[σ₁₂] F) :
    e.completion.toLinearIsometry = e.toLinearIsometry.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq e.completion.continuous e.toLinearIsometry.completion.continuous
  | ih x => simp [LinearIsometry.completion_apply_coe]

end NormedAddCommGroup

end LinearIsometryEquiv

namespace UniformSpace.Completion

variable (𝕜 E : Type*) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The completion of the separation quotient of a seminormed space is canonically linearly
isometrically equivalent to the completion of the space itself. -/
noncomputable def separationQuotientEquiv : Completion (SeparationQuotient E) ≃ₗᵢ[𝕜] Completion E :=
  (LinearEquiv.refl 𝕜 E).extendOfIsometry
    (toComplₗᵢ.toLinearMap.comp (SeparationQuotient.mkCLM 𝕜 E).toLinearMap) toComplₗᵢ.toLinearMap
    (denseRange_coe.comp SeparationQuotient.surjective_mk.denseRange (continuous_coe _))
    denseRange_coe fun x ↦ by simp

variable {𝕜 E}

/-- On classes from `E`, `separationQuotientEquiv` sends `(mk x : Completion _)` to `↑x`. -/
@[simp] theorem separationQuotientEquiv_coe_mk (x : E) :
    separationQuotientEquiv 𝕜 E
        ((SeparationQuotient.mk x : SeparationQuotient E) : Completion (SeparationQuotient E)) =
      (x : Completion E) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- The inverse of `separationQuotientEquiv` sends `↑x` to `(mk x : Completion _)`. -/
@[simp] theorem separationQuotientEquiv_symm_coe (x : E) :
    (separationQuotientEquiv 𝕜 E).symm (x : Completion E) =
      ((SeparationQuotient.mk x : SeparationQuotient E) : Completion (SeparationQuotient E)) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ x

/-- `separationQuotientEquiv 𝕜 E` commutes with any uniformly continuous scalar action on `E`. -/
@[simp] theorem separationQuotientEquiv_smul {M : Type*} [SMul M E] [UniformContinuousConstSMul M E]
    (a : M) (x : Completion (SeparationQuotient E)) :
    separationQuotientEquiv 𝕜 E (a • x) = a • separationQuotientEquiv 𝕜 E x := by
  have : UniformContinuousConstSMul M (SeparationQuotient E) :=
    ⟨fun m ↦ SeparationQuotient.uniformContinuous_dom.mpr <|
      SeparationQuotient.uniformContinuous_mk.comp (uniformContinuous_const_smul m)⟩
  refine Completion.induction_on x
    (isClosed_eq ((separationQuotientEquiv 𝕜 E).continuous.comp (continuous_const_smul a))
      ((continuous_const_smul a).comp (separationQuotientEquiv 𝕜 E).continuous))
    (SeparationQuotient.surjective_mk.forall.2 fun u ↦ by
      rw [← Completion.coe_smul, ← SeparationQuotient.mk_smul, separationQuotientEquiv_coe_mk,
        separationQuotientEquiv_coe_mk, Completion.coe_smul])

/-- The inverse of `separationQuotientEquiv 𝕜 E` commutes with any uniformly continuous action. -/
@[simp] theorem separationQuotientEquiv_symm_smul {M : Type*} [SMul M E]
    [UniformContinuousConstSMul M E] (a : M) (x : Completion E) :
    (separationQuotientEquiv 𝕜 E).symm (a • x) = a • (separationQuotientEquiv 𝕜 E).symm x :=
  (separationQuotientEquiv 𝕜 E).injective <| by
    rw [LinearIsometryEquiv.apply_symm_apply, separationQuotientEquiv_smul,
      LinearIsometryEquiv.apply_symm_apply]

end UniformSpace.Completion
