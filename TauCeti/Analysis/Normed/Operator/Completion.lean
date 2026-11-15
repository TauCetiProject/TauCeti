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
public import TauCeti.Analysis.Normed.Group.BallSphere
public import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Normed.Operator.FiniteDimensional

/-!
# Operator norms and finite-rank approximation of bounded maps extended to completions

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

Over a complete scalar field `𝕜`, finite-rank bounds and finite-rank approximants also transfer
between `(E →L[𝕜] F)` and `(Completion E →L[𝕜] Completion F)`: if `R.rank ≤ n`, the image of
`LinearMap.range R` in `Completion F` is finite-dimensional and hence closed, giving
`R.completion.rank ≤ n`; conversely, applying `ContinuousLinearMap.denseRange_comp` to the
inclusion of the finite-dimensional range of `R'` approximates `R'` arbitrarily closely in operator
norm by `R.completion` with `R.rank ≤ n`.

## Main results

* `ContinuousLinearMap.norm_completion`: `‖f.completion‖ = ‖f‖`.
* `ContinuousLinearMap.norm_fromCompletion`: `‖f.fromCompletion‖ = ‖f‖`.
* `ContinuousLinearMap.norm_toComplL_comp` and `ContinuousLinearMap.eNorm_toComplL_comp`:
  composing with the embedding of the codomain into its completion preserves the operator norm.
* `ContinuousLinearMap.ball_subset_image_completion_ball` and
  `ContinuousLinearMap.image_completion_ball`: the extension of a metric quotient map to the
  completions is a metric quotient map.
* `ContinuousLinearMap.rank_completion_le_of_le`: over a complete scalar field,
  `R.rank ≤ n → R.completion.rank ≤ n`.
* `ContinuousLinearMap.exists_rank_le_norm_completion_sub_lt`: over a complete scalar field,
  operators `R.completion` with `R.rank ≤ n` are operator-norm dense in operators of rank at most
  `n` between the completions.
* `LinearIsometryEquiv.completion`: the extension of a linear isometric equivalence to the
  completions.
* `LinearIsometryEquiv.toLinearIsometry_completion`: as a linear isometry, it is
  `LinearIsometry.completion`.
* `LinearIsometryEquiv.completion_symm`, `LinearIsometryEquiv.completion_refl`,
  `LinearIsometryEquiv.completion_trans`: extension to completions is compatible with inverses,
  identities and composites.
-/

public section

open UniformSpace

namespace ContinuousLinearMap

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

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over a complete scalar field, extending a bounded linear map of rank at most `n` to the
completions preserves the rank bound `n`: the image of its range in `Completion F` is
finite-dimensional, hence closed. -/
theorem rank_completion_le_of_le {R : E →L[𝕜] F} {n : ℕ} (hR : R.rank ≤ n) :
    R.completion.rank ≤ n := by
  let V : Submodule 𝕜 (Completion F) :=
    (LinearMap.range (R : E →ₗ[𝕜] F)).map (Completion.toComplL : F →L[𝕜] Completion F).toLinearMap
  have : FiniteDimensional 𝕜 (LinearMap.range (R : E →ₗ[𝕜] F)) :=
    Module.rank_lt_aleph0_iff.mp (hR.trans_lt Cardinal.natCast_lt_aleph0)
  have hrange : LinearMap.range (R.completion : Completion E →ₗ[𝕜] Completion F) ≤ V := by
    rintro _ ⟨x, rfl⟩
    induction x using Completion.induction_on with
    | hp => exact V.isClosed_of_finiteDimensional.preimage R.completion.continuous
    | ih x =>
      rw [coe_coe, completion_apply_coe]
      exact Submodule.mem_map_of_mem (LinearMap.mem_range_self _ x)
  exact (Submodule.rank_mono hrange).trans ((rank_map_le _ _).trans hR)

/-- Over a complete scalar field, every bounded linear map `R'` of rank at most `n` between the
completions can be approximated within any `ε > 0` in operator norm by the completion of a bounded
linear map `R : E →L[𝕜] F` of rank at most `n`. -/
theorem exists_rank_le_norm_completion_sub_lt
    {R' : Completion E →L[𝕜] Completion F} {n : ℕ} (hR' : R'.rank ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : E →L[𝕜] F, R.rank ≤ n ∧ ‖R.completion - R'‖ < ε := by
  let W : Submodule 𝕜 (Completion F) := LinearMap.range (R' : Completion E →ₗ[𝕜] Completion F)
  have : FiniteDimensional 𝕜 W :=
    Module.rank_lt_aleph0_iff.mp (hR'.trans_lt Cardinal.natCast_lt_aleph0)
  let R'₀ : Completion E →L[𝕜] W := R'.codRestrict W (LinearMap.mem_range_self _)
  have hdense : DenseRange (Completion.toComplL : F →L[𝕜] Completion F) :=
    Completion.denseRange_coe
  obtain ⟨L, hL⟩ := Metric.denseRange_iff.mp (denseRange_comp hdense) W.subtypeL
    (ε / (‖R'‖ + 1)) (div_pos hε (by positivity))
  let R : E →L[𝕜] F := L ∘L R'₀ ∘L (Completion.toComplL : E →L[𝕜] Completion E)
  have hR_rank : R.rank ≤ n :=
    (LinearMap.rank_comp_le_left _ _).trans ((LinearMap.rank_le_domain L.toLinearMap).trans hR')
  have hR_compl : R.completion = ((Completion.toComplL : F →L[𝕜] Completion F) ∘L L) ∘L R'₀ := by
    ext x
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq R.completion.continuous (by fun_prop)
    | ih x => simp [R]
  have hR'_eq : R' = W.subtypeL ∘L R'₀ := by
    ext x
    simp [R'₀]
  have hR'₀ : ‖R'₀‖ ≤ ‖R'‖ := opNorm_le_bound _ (norm_nonneg _) fun x ↦ R'.le_opNorm x
  refine ⟨R, hR_rank, ?_⟩
  rw [hR_compl, hR'_eq, ← sub_comp]
  calc ‖((Completion.toComplL : F →L[𝕜] Completion F) ∘L L - W.subtypeL) ∘L R'₀‖
      ≤ ‖(Completion.toComplL : F →L[𝕜] Completion F) ∘L L - W.subtypeL‖ * ‖R'₀‖ :=
        opNorm_comp_le _ _
    _ ≤ (ε / (‖R'‖ + 1)) * ‖R'‖ := by
        rw [dist_comm, dist_eq_norm _ W.subtypeL] at hL
        gcongr
    _ < (ε / (‖R'‖ + 1)) * (‖R'‖ + 1) :=
        mul_lt_mul_of_pos_left (lt_add_one _) (div_pos hε (by positivity))
    _ = ε := div_mul_cancel₀ ε (by positivity)

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
