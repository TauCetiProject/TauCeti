/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module

/-!
# Cut-off local-frame coefficients of smooth sections

Let `V` be a smooth real vector bundle of finite rank over a finite-dimensional Hausdorff manifold
`M`, let `e` be a trivialization of `V`, let `b` be a basis of the model fibre and let `ρ` be a
smooth bump function supported in `e.baseSet`. The `i`-th coefficient of a smooth section `s` in
the local frame `e.localFrame b`, multiplied by `ρ`, is a globally smooth function. This file
bundles it as a `C^∞(M)`-linear map `Γ(V) → C^∞(M)`.

## Main results

* `Bundle.Trivialization.cutoffLocalFrameCoeff`: the cut-off frame coefficient as a
  `C^∞(M)`-linear map from smooth sections to smooth functions.
* `Bundle.Trivialization.cutoffLocalFrameCoeff_mem_of_mem_smul_top`: it sends `J Γ(V)` into `J`
  for every ideal `J` of `C^∞(M)`.
* `Bundle.Trivialization.apply_eq_sum_cutoffLocalFrameCoeff_smul`: where `ρ = 1`, a smooth section
  is the sum of its cut-off frame coefficients times sections agreeing with the local frame.
-/

public section

open Bundle Module
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.Trivialization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {ι : Type*} (e : Trivialization F (π F V)) [MemTrivializationAtlas e] (b : Basis ι ℝ F)
  {x₀ : M} (ρ : SmoothBumpFunction I x₀) (hρ : tsupport ρ ⊆ e.baseSet)

/-- The `i`-th coefficient of a smooth section in the local frame of `e`, cut off by a bump
function `ρ` supported in `e.baseSet`, as a `C^∞(M)`-linear map to smooth functions. -/
def cutoffLocalFrameCoeff (i : ι) : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯ where
  toFun s := ⟨fun y ↦ ρ y * e.localFrameCoeff I b i y (s y),
    e.contMDiff_mul_localFrameCoeff b ρ hρ s.contMDiff i⟩
  -- Sums and products of smooth functions are evaluated pointwise by definition.
  map_add' s t := by
    ext y
    change ρ y * _ = ρ y * _ + ρ y * _
    rw [ContMDiffSection.coe_add, Pi.add_apply, map_add, mul_add]
  map_smul' f s := by
    ext y
    change ρ y * _ = f y * (ρ y * _)
    rw [ContMDiffSection.smul_apply, map_smul, smul_eq_mul, mul_left_comm]

/-- The cut-off frame coefficient of `s` at `y` is `ρ y` times the frame coefficient of `s y`. -/
@[simp]
theorem cutoffLocalFrameCoeff_apply (i : ι) (s : Cₛ^∞⟮I; F, V⟯) (y : M) :
    e.cutoffLocalFrameCoeff b ρ hρ i s y = ρ y * e.localFrameCoeff I b i y (s y) :=
  (rfl)

/-- The cut-off frame coefficients send `J Γ(V)` into `J`, for every ideal `J` of `C^∞(M)`. -/
theorem cutoffLocalFrameCoeff_mem_of_mem_smul_top (i : ι) {J : Ideal C^∞⟮I, M; ℝ⟯}
    {s : Cₛ^∞⟮I; F, V⟯} (hs : s ∈ J • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)) :
    e.cutoffLocalFrameCoeff b ρ hρ i s ∈ J := by
  refine Submodule.smul_induction_on hs (fun f hf t _ ↦ ?_) fun s t hs ht ↦ ?_
  · rw [map_smul, smul_eq_mul]
    exact J.mul_mem_right _ hf
  · rw [map_add]
    exact J.add_mem hs ht

/-- At a point where `ρ = 1` and the sections `fr i` agree with the local frame of `e`, a smooth
section is the sum of its cut-off frame coefficients times the `fr i`. -/
theorem apply_eq_sum_cutoffLocalFrameCoeff_smul [Fintype ι] (fr : ι → Cₛ^∞⟮I; F, V⟯)
    (s : Cₛ^∞⟮I; F, V⟯) {y : M} (hy : ρ y = 1) (hfr : ∀ i, fr i y = e.localFrame b i y) :
    s y = (∑ i, e.cutoffLocalFrameCoeff b ρ hρ i s • fr i : Cₛ^∞⟮I; F, V⟯) y := by
  have hyb : y ∈ e.baseSet := hρ (subset_tsupport _ (by simp [hy]))
  have h := congrFun (map_sum (ContMDiffSection.coeAddHom I F ∞ V)
    (fun i ↦ e.cutoffLocalFrameCoeff b ρ hρ i s • fr i) Finset.univ) y
  simp only [ContMDiffSection.coeAddHom_apply, Finset.sum_apply, ContMDiffSection.smul_apply,
    cutoffLocalFrameCoeff_apply, hfr, hy, one_mul] at h
  rw [h]
  exact e.eq_sum_localFrameCoeff_smul hyb

end Bundle.Trivialization
