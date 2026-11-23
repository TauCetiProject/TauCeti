/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Completion
import TauCeti.Analysis.Fredholm.Adjoint
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Kernels of amplified operators on completed tensor products

Let `f : E →L[𝕜] E'` and `g : F →L[𝕜] F'` be bounded operators between Hilbert spaces, and let
`f ⊗ 1` and `1 ⊗ g` be their amplifications to the completed Hilbert tensor products
`E ⊗̂ F = UniformSpace.Completion (E ⊗[𝕜] F)` (`ContinuousLinearMap.rTensorCompletion` and
`ContinuousLinearMap.lTensorCompletion`). This file computes their kernels in terms of the
kernels of `f` and `g`.

For the algebraic tensor product over a field, `ker (f ⊗ 1)` is the image of `ker f ⊗ F`, since
tensoring with `F` is exact. On the completion this description is replaced by projections: `f ⊗ 1`
and `Πᗮ ⊗ 1` have the same kernel, where `Πᗮ` is the orthogonal projection onto `(ker f)ᗮ`
(`ContinuousLinearMap.rTensorCompletion_apply_eq_zero_iff`), so the kernel of `f ⊗ 1` is the set of
fixed points of `Π ⊗ 1` for the orthogonal projection `Π` onto `ker f`
(`ContinuousLinearMap.rTensorCompletion_apply_eq_zero_iff_eq`). The proof
uses that `(ker f)ᗮ` is the closure of the range of `f†`, and that `f† ⊗ 1` is the adjoint of
`f ⊗ 1`: a vector killed by `f ⊗ 1` is orthogonal to every `f† x ⊗ y`, hence to every `z ⊗ y` with
`z ∈ (ker f)ᗮ`.

So the common kernel of `f ⊗ 1` and `1 ⊗ g` is the range of the tensor product `Π_f ⊗ Π_g` of the
two kernel projections
(`ContinuousLinearMap.rTensorCompletion_apply_eq_zero_and_lTensorCompletion_apply_eq_zero_iff`).
When both kernels are finite-dimensional, this range is the image of the algebraic tensor product
`ker f ⊗ ker g`, embedded isometrically in `E ⊗̂ F`, so that

`ker (f ⊗ 1) ∩ ker (1 ⊗ g) ≃ ker f ⊗ ker g`

(`ContinuousLinearMap.ker_rTensorCompletion_inf_ker_lTensorCompletion`), the completed form of
`LinearMap.ker_rTensor_inf_ker_lTensor`, with dimension `dim ker f · dim ker g`. It is the step
that computes the kernel and the cokernel of the product of two Fredholm operators.

When `f` has closed range, `f ⊗ 1` is moreover bounded below on the orthogonal complement of its
kernel (`ContinuousLinearMap.exists_norm_rTensorCompletion_starProjection_apply_le`): `f` has a
bounded left inverse there, and so does `f ⊗ 1`. For closed-range `f` and `g`, every vector then
lies within `C (‖(f ⊗ 1) w‖ + ‖(1 ⊗ g) w‖)` of the common kernel
(`ContinuousLinearMap.exists_norm_sub_mapLCompletion_starProjection_apply_le`), which is what makes
ranges of operators built from `f ⊗ 1` and `1 ⊗ g` closed.

## Main declarations

* `ContinuousLinearMap.rTensorCompletion_apply_eq_zero_iff`,
  `ContinuousLinearMap.lTensorCompletion_apply_eq_zero_iff` (and the submodule forms
  `ContinuousLinearMap.ker_rTensorCompletion`, `ContinuousLinearMap.ker_lTensorCompletion`): the
  kernels of `f ⊗ 1` and `1 ⊗ g`, also as the fixed points of `Π ⊗ 1` and `1 ⊗ Π`
  (`ContinuousLinearMap.rTensorCompletion_apply_eq_zero_iff_eq`,
  `ContinuousLinearMap.lTensorCompletion_apply_eq_zero_iff_eq`).
* `ContinuousLinearMap.rTensorCompletion_apply_eq_zero_and_lTensorCompletion_apply_eq_zero_iff`:
  the common kernel of `f ⊗ 1` and `1 ⊗ g` is the range of the tensor product of the kernel
  projections.
* `ContinuousLinearMap.ker_rTensorCompletion_inf_ker_lTensorCompletion` and
  `ContinuousLinearMap.finrank_ker_rTensorCompletion_inf_ker_lTensorCompletion`: for
  finite-dimensional kernels, the common kernel is the image of `ker f ⊗ ker g`, of dimension
  `dim ker f · dim ker g`.
* `ContinuousLinearMap.exists_norm_rTensorCompletion_starProjection_apply_le`,
  `ContinuousLinearMap.exists_norm_lTensorCompletion_starProjection_apply_le` and
  `ContinuousLinearMap.exists_norm_sub_mapLCompletion_starProjection_apply_le`: lower bounds for
  amplifications of closed-range operators.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press, 1980, §II.4 and §VIII.10.
-/

public section

noncomputable section

open UniformSpace TensorProduct
open scoped InnerProductSpace

variable {𝕜 E E' F F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']

namespace ContinuousLinearMap

section rTensor

variable [CompleteSpace E] [CompleteSpace E']

/-- A vector killed by `f ⊗ 1` is orthogonal to every pure tensor whose first factor lies in the
orthogonal complement of `ker f`, the closure of the range of `f†`. -/
private theorem inner_coe_tmul_eq_zero_of_rTensorCompletion_apply_eq_zero (f : E →L[𝕜] E')
    {w : Completion (E ⊗[𝕜] F)} (hw : f.rTensorCompletion F w = 0) {z : E} (hz : z ∈ f.kerᗮ)
    (y : F) : ⟪((z ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)), w⟫_𝕜 = 0 := by
  -- `z ↦ ⟪w, z ⊗ y⟫` is a continuous linear functional vanishing on the range of `f†`.
  let φ : E →L[𝕜] 𝕜 := innerSL 𝕜 w ∘L Completion.toComplL ∘L (mkL 𝕜 E F).flip y
  have hφ (z : E) : φ z = ⟪w, ((z ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))⟫_𝕜 := rfl
  have hrange : f.adjoint.range ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, coe_coe, hφ]
    rw [← rTensorCompletion_tmul, ← adjoint_rTensorCompletion, adjoint_inner_right, hw,
      inner_zero_left]
  have hzφ : z ∈ φ.ker := by
    rw [orthogonal_ker] at hz
    exact Submodule.topologicalClosure_minimal _ hrange φ.isClosed_ker hz
  rw [LinearMap.mem_ker, coe_coe, hφ] at hzφ
  rw [← inner_conj_symm, hzφ, map_zero]

/-- **The kernel of an amplification.** `f ⊗ 1` kills `w` exactly when `Πᗮ ⊗ 1` does, where `Πᗮ`
is the orthogonal projection onto the orthogonal complement of `ker f`. Equivalently, `w` is fixed
by `Π ⊗ 1` for the orthogonal projection `Π` onto `ker f`
(`ContinuousLinearMap.rTensorCompletion_apply_eq_zero_iff_eq`). -/
theorem rTensorCompletion_apply_eq_zero_iff (f : E →L[𝕜] E') (w : Completion (E ⊗[𝕜] F)) :
    f.rTensorCompletion F w = 0 ↔ f.kerᗮ.starProjection.rTensorCompletion F w = 0 := by
  constructor
  · intro hw
    refine eq_zero_of_forall_inner_coe_tmul fun x y ↦ ?_
    rw [← (isSelfAdjoint_starProjection f.kerᗮ).adjoint_eq, ← adjoint_rTensorCompletion,
      adjoint_inner_right, rTensorCompletion_tmul]
    exact inner_coe_tmul_eq_zero_of_rTensorCompletion_apply_eq_zero f hw
      (f.kerᗮ.starProjection_apply_mem x) y
  · intro hw
    -- `f` vanishes on `ker f`, so `f ⊗ 1 = (f ∘ Πᗮ) ⊗ 1 = (f ⊗ 1) ∘ (Πᗮ ⊗ 1)`.
    rw [← f.comp_starProjection_orthogonal_ker, rTensorCompletion_comp, comp_apply, hw, map_zero]

/-- The kernel of `f ⊗ 1` is the kernel of `Πᗮ ⊗ 1` for the orthogonal projection `Πᗮ` onto the
orthogonal complement of `ker f`. -/
theorem ker_rTensorCompletion (f : E →L[𝕜] E') :
    (f.rTensorCompletion F).ker = (f.kerᗮ.starProjection.rTensorCompletion F).ker :=
  Submodule.ext fun w ↦ rTensorCompletion_apply_eq_zero_iff f w

/-- `f ⊗ 1` kills `w` exactly when `w` is fixed by `Π ⊗ 1`, for the orthogonal projection `Π`
onto `ker f`: the kernel of `f ⊗ 1` is the set of fixed points, that is the range, of `Π ⊗ 1`. -/
theorem rTensorCompletion_apply_eq_zero_iff_eq (f : E →L[𝕜] E') (w : Completion (E ⊗[𝕜] F)) :
    f.rTensorCompletion F w = 0 ↔ f.ker.starProjection.rTensorCompletion F w = w := by
  have hsum := DFunLike.congr_fun
    (rTensorCompletion_starProjection_add_rTensorCompletion_starProjection_orthogonal
      (F := F) f.ker) w
  rw [rTensorCompletion_apply_eq_zero_iff]
  exact ⟨fun h ↦ by simpa [h] using hsum, fun h ↦ by simpa [h] using hsum⟩

end rTensor

section lTensor

variable [CompleteSpace F] [CompleteSpace F']

/-- **The kernel of an amplification.** `1 ⊗ g` kills `w` exactly when `1 ⊗ Πᗮ` does, where `Πᗮ`
is the orthogonal projection onto the orthogonal complement of `ker g`. -/
theorem lTensorCompletion_apply_eq_zero_iff (g : F →L[𝕜] F') (w : Completion (E ⊗[𝕜] F)) :
    g.lTensorCompletion E w = 0 ↔ g.kerᗮ.starProjection.lTensorCompletion E w = 0 := by
  -- The flip `E ⊗̂ F ≃ F ⊗̂ E` turns `1 ⊗ g` into `g ⊗ 1`.
  simpa only [rTensorCompletion_commIsometry_completion, LinearIsometryEquiv.map_eq_zero_iff]
    using rTensorCompletion_apply_eq_zero_iff g ((commIsometry 𝕜 E F).completion w)

/-- The kernel of `1 ⊗ g` is the kernel of `1 ⊗ Πᗮ` for the orthogonal projection `Πᗮ` onto the
orthogonal complement of `ker g`. -/
theorem ker_lTensorCompletion (g : F →L[𝕜] F') :
    (g.lTensorCompletion E).ker = (g.kerᗮ.starProjection.lTensorCompletion E).ker :=
  Submodule.ext fun w ↦ lTensorCompletion_apply_eq_zero_iff g w

/-- `1 ⊗ g` kills `w` exactly when `w` is fixed by `1 ⊗ Π`, for the orthogonal projection `Π`
onto `ker g`: the kernel of `1 ⊗ g` is the set of fixed points, that is the range, of `1 ⊗ Π`. -/
theorem lTensorCompletion_apply_eq_zero_iff_eq (g : F →L[𝕜] F') (w : Completion (E ⊗[𝕜] F)) :
    g.lTensorCompletion E w = 0 ↔ g.ker.starProjection.lTensorCompletion E w = w := by
  have hsum := DFunLike.congr_fun
    (lTensorCompletion_starProjection_add_lTensorCompletion_starProjection_orthogonal
      (E := E) g.ker) w
  rw [lTensorCompletion_apply_eq_zero_iff]
  exact ⟨fun h ↦ by simpa [h] using hsum, fun h ↦ by simpa [h] using hsum⟩

end lTensor

section CommonKernel

variable [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F']

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- `Π_f ⊗ Π_g` maps into the kernel of `f ⊗ 1`. -/
theorem rTensorCompletion_mapLCompletion_starProjection_apply_eq_zero (f : E →L[𝕜] E')
    (g : F →L[𝕜] F')
    (w : Completion (E ⊗[𝕜] F)) :
    f.rTensorCompletion F (mapLCompletion f.ker.starProjection g.ker.starProjection w) = 0 := by
  have hf : f ∘L f.ker.starProjection = 0 := ext fun x ↦ f.ker.starProjection_apply_mem x
  rw [rTensorCompletion_eq_mapLCompletion, ← comp_apply, ← mapLCompletion_comp, hf,
    mapLCompletion_zero_left, zero_apply]

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- `Π_f ⊗ Π_g` maps into the kernel of `1 ⊗ g`. -/
theorem lTensorCompletion_mapLCompletion_starProjection_apply_eq_zero (f : E →L[𝕜] E')
    (g : F →L[𝕜] F')
    (w : Completion (E ⊗[𝕜] F)) :
    g.lTensorCompletion E (mapLCompletion f.ker.starProjection g.ker.starProjection w) = 0 := by
  have hg : g ∘L g.ker.starProjection = 0 := ext fun y ↦ g.ker.starProjection_apply_mem y
  rw [lTensorCompletion_eq_mapLCompletion, ← comp_apply, ← mapLCompletion_comp, hg,
    mapLCompletion_zero_right, zero_apply]

/-- **The common kernel of two amplifications.** `f ⊗ 1` and `1 ⊗ g` both kill `w` exactly when
`w` is fixed by `Π_f ⊗ Π_g`, the tensor product of the orthogonal projections onto `ker f` and
`ker g`. -/
theorem rTensorCompletion_apply_eq_zero_and_lTensorCompletion_apply_eq_zero_iff (f : E →L[𝕜] E')
    (g : F →L[𝕜] F') (w : Completion (E ⊗[𝕜] F)) :
    f.rTensorCompletion F w = 0 ∧ g.lTensorCompletion E w = 0 ↔
      mapLCompletion f.ker.starProjection g.ker.starProjection w = w := by
  set P := f.ker.starProjection.rTensorCompletion F
  set Q := g.ker.starProjection.lTensorCompletion E
  have hPQ (v) : mapLCompletion f.ker.starProjection g.ker.starProjection v = P (Q v) :=
    congr($((rTensorCompletion_comp_lTensorCompletion _ _).symm) v)
  have hQP (v) : mapLCompletion f.ker.starProjection g.ker.starProjection v = Q (P v) :=
    congr($((lTensorCompletion_comp_rTensorCompletion _ _).symm) v)
  -- Both amplified projections are idempotent.
  have hP (v) : P (P v) = P v := by
    rw [← comp_apply, ← rTensorCompletion_comp, ← mul_def, f.ker.isIdempotentElem_starProjection.eq]
  have hQ (v) : Q (Q v) = Q v := by
    rw [← comp_apply, ← lTensorCompletion_comp, ← mul_def, g.ker.isIdempotentElem_starProjection.eq]
  rw [rTensorCompletion_apply_eq_zero_iff_eq, lTensorCompletion_apply_eq_zero_iff_eq]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ by rw [hPQ, h₂, h₁], fun h ↦ ⟨?_, ?_⟩⟩
  · rw [← h, hPQ, hP]
  · rw [← h, hQP, hQ]

/-- **The common kernel of two amplifications, for finite-dimensional kernels.** If `ker f` and
`ker g` are finite-dimensional, the common kernel of `f ⊗ 1` and `1 ⊗ g` on `E ⊗̂ F` is the image
of `ker f ⊗ ker g` under its isometric inclusion. This is the completed form of
`LinearMap.ker_rTensor_inf_ker_lTensor`. -/
theorem ker_rTensorCompletion_inf_ker_lTensorCompletion (f : E →L[𝕜] E') (g : F →L[𝕜] F')
    [FiniteDimensional 𝕜 f.ker] [FiniteDimensional 𝕜 g.ker] :
    (f.rTensorCompletion F).ker ⊓ (g.lTensorCompletion E).ker =
      LinearMap.range (Completion.toComplₗᵢ.comp (mapInclIsometry f.ker g.ker)).toLinearMap := by
  set ι := (Completion.toComplₗᵢ.comp (mapInclIsometry f.ker g.ker)).toLinearMap
  set p := mapLCompletion f.ker.starProjection g.ker.starProjection
  -- `Π_f ⊗ Π_g` fixes the image of `ker f ⊗ ker g`.
  have hfix : (p : _ →ₗ[𝕜] _) ∘ₗ ι = ι := TensorProduct.ext' fun x y ↦ by
    simp [ι, p, Submodule.starProjection_eq_self_iff.2 x.property,
      Submodule.starProjection_eq_self_iff.2 y.property]
  ext w
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, coe_coe, coe_coe,
    rTensorCompletion_apply_eq_zero_and_lTensorCompletion_apply_eq_zero_iff]
  refine ⟨fun h ↦ h ▸ ?_, ?_⟩
  · -- The range of `ι` is finite-dimensional, hence closed, and contains the image of every pure
    -- tensor under `Π_f ⊗ Π_g`.
    refine apply_mem_of_forall_apply_coe_tmul_mem (Submodule.isClosed_of_finiteDimensional _)
      (fun x y ↦ LinearMap.mem_range.2
        ⟨⟨f.ker.starProjection x, f.ker.starProjection_apply_mem x⟩ ⊗ₜ
          ⟨g.ker.starProjection y, g.ker.starProjection_apply_mem y⟩, ?_⟩) w
    simp [ι]
  · rintro ⟨t, rfl⟩
    exact congr($hfix t)

/-- The common kernel of `f ⊗ 1` and `1 ⊗ g`, for finite-dimensional kernels, has dimension
`dim ker f · dim ker g`. -/
theorem finrank_ker_rTensorCompletion_inf_ker_lTensorCompletion (f : E →L[𝕜] E')
    (g : F →L[𝕜] F') [FiniteDimensional 𝕜 f.ker] [FiniteDimensional 𝕜 g.ker] :
    Module.finrank 𝕜 ↥((f.rTensorCompletion F).ker ⊓ (g.lTensorCompletion E).ker) =
      Module.finrank 𝕜 f.ker * Module.finrank 𝕜 g.ker := by
  let X : f.ker ⊗[𝕜] g.ker →ₗᵢ[𝕜] Completion (E ⊗[𝕜] F) :=
    Completion.toComplₗᵢ.comp (mapInclIsometry f.ker g.ker)
  rw [ker_rTensorCompletion_inf_ker_lTensorCompletion,
    LinearMap.finrank_range_of_inj (f := X.toLinearMap)
      X.isometry.injective,
    Module.finrank_tensorProduct]

end CommonKernel

section LowerBound

/-- **Amplification of a closed-range operator.** If `f` has closed range, then `f ⊗ 1` controls
the component orthogonal to its kernel: `‖(Πᗮ ⊗ 1) w‖ ≤ C ‖(f ⊗ 1) w‖`, where `Πᗮ` is the
orthogonal projection onto the orthogonal complement of `ker f`. -/
theorem exists_norm_rTensorCompletion_starProjection_apply_le [CompleteSpace E] [CompleteSpace E']
    (f : E →L[𝕜] E') (hf : IsClosed (f.range : Set E')) :
    ∃ C, 0 ≤ C ∧ ∀ w : Completion (E ⊗[𝕜] F),
      ‖f.kerᗮ.starProjection.rTensorCompletion F w‖ ≤ C * ‖f.rTensorCompletion F w‖ := by
  obtain ⟨R, hR⟩ := f.exists_comp_eq_starProjection_orthogonal_ker hf
  refine ⟨‖R‖, norm_nonneg R, fun w ↦ ?_⟩
  rw [← hR, rTensorCompletion_comp, comp_apply]
  exact (le_opNorm _ _).trans (by gcongr; exact norm_rTensorCompletion_le R)

/-- **Amplification of a closed-range operator.** If `g` has closed range, then `1 ⊗ g` controls
the component orthogonal to its kernel: `‖(1 ⊗ Πᗮ) w‖ ≤ C ‖(1 ⊗ g) w‖`, where `Πᗮ` is the
orthogonal projection onto the orthogonal complement of `ker g`. -/
theorem exists_norm_lTensorCompletion_starProjection_apply_le [CompleteSpace F] [CompleteSpace F']
    (g : F →L[𝕜] F') (hg : IsClosed (g.range : Set F')) :
    ∃ C, 0 ≤ C ∧ ∀ w : Completion (E ⊗[𝕜] F),
      ‖g.kerᗮ.starProjection.lTensorCompletion E w‖ ≤ C * ‖g.lTensorCompletion E w‖ := by
  -- The flip `E ⊗̂ F ≃ F ⊗̂ E` turns `1 ⊗ g` into `g ⊗ 1` and preserves norms.
  obtain ⟨C, hC, h⟩ := exists_norm_rTensorCompletion_starProjection_apply_le (F := E) g hg
  refine ⟨C, hC, fun w ↦ ?_⟩
  simpa only [rTensorCompletion_commIsometry_completion, LinearIsometryEquiv.norm_map]
    using h ((commIsometry 𝕜 E F).completion w)

/-- **Distance to the common kernel.** If `f` and `g` have closed range, then the distance from
`w` to its image under `Π_f ⊗ Π_g`, a vector of the common kernel of `f ⊗ 1` and `1 ⊗ g`
(`ContinuousLinearMap.rTensorCompletion_mapLCompletion_starProjection_apply_eq_zero`), is at most
`C (‖(f ⊗ 1) w‖ + ‖(1 ⊗ g) w‖)`. -/
theorem exists_norm_sub_mapLCompletion_starProjection_apply_le [CompleteSpace E]
    [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F'] (f : E →L[𝕜] E') (g : F →L[𝕜] F')
    (hf : IsClosed (f.range : Set E')) (hg : IsClosed (g.range : Set F')) :
    ∃ C, 0 ≤ C ∧ ∀ w : Completion (E ⊗[𝕜] F),
      ‖w - mapLCompletion f.ker.starProjection g.ker.starProjection w‖ ≤
        C * (‖f.rTensorCompletion F w‖ + ‖g.lTensorCompletion E w‖) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_rTensorCompletion_starProjection_apply_le (F := F) f hf
  obtain ⟨C₂, -, h₂⟩ := exists_norm_lTensorCompletion_starProjection_apply_le (E := E) g hg
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun w ↦ ?_⟩
  set P := f.ker.starProjection.rTensorCompletion F
  -- `w - (Π_f ⊗ Π_g) w = (Πᗮ_f ⊗ 1) w + (Π_f ⊗ 1) ((1 ⊗ Πᗮ_g) w)`.
  have hsplit : w - mapLCompletion f.ker.starProjection g.ker.starProjection w =
      f.kerᗮ.starProjection.rTensorCompletion F w +
        P (g.kerᗮ.starProjection.lTensorCompletion E w) := by
    have hf' := DFunLike.congr_fun
      (rTensorCompletion_starProjection_add_rTensorCompletion_starProjection_orthogonal
        (F := F) f.ker) w
    have hg' := DFunLike.congr_fun
      (lTensorCompletion_starProjection_add_lTensorCompletion_starProjection_orthogonal
        (E := E) g.ker) w
    rw [add_apply, id_apply] at hf' hg'
    rw [← rTensorCompletion_comp_lTensorCompletion, comp_apply, eq_sub_of_add_eq hg', map_sub,
      ← sub_eq_of_eq_add' hf'.symm]
    abel
  have hP : ‖P (g.kerᗮ.starProjection.lTensorCompletion E w)‖ ≤
      ‖g.kerᗮ.starProjection.lTensorCompletion E w‖ :=
    (le_opNorm _ _).trans <| mul_le_of_le_one_left (norm_nonneg _) <|
      (norm_rTensorCompletion_le _).trans f.ker.starProjection_norm_le
  rw [hsplit]
  calc _ ≤ C₁ * ‖f.rTensorCompletion F w‖ + C₂ * ‖g.lTensorCompletion E w‖ :=
        (norm_add_le _ _).trans (add_le_add (h₁ w) (hP.trans (h₂ w)))
    _ ≤ _ := by
      rw [mul_add]
      gcongr
      exacts [le_max_left _ _, le_max_right _ _]

end LowerBound

end ContinuousLinearMap
