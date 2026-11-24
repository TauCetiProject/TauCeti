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

Let `V` be a `C^n` vector bundle of finite rank over a manifold `M`, over a complete nontrivially
normed field `𝕜`, let `e` be a trivialization of `V`, let `b` be a basis of the model fibre and let
`ρ` be a `C^n` function supported in `e.baseSet`. The `i`-th coefficient of a `C^n` section `s` in
the local frame `e.localFrame b`, multiplied by `ρ`, is a globally `C^n` function. This file
bundles it as a `C^n(M)`-linear map `Γ(V) → C^n(M)`. Every ideal `J` of `C^n(M)` is then sent
into itself: `LinearMap.apply_mem_of_mem_smul_top` carries `J Γ(V)` into `J`.

## Main results

* `Bundle.Trivialization.cutoffLocalFrameCoeff`: the cut-off frame coefficient as a
  `C^n(M)`-linear map from `C^n` sections to `C^n` functions.
* `Bundle.Trivialization.apply_eq_sum_cutoffLocalFrameCoeff_smul`: where `ρ = 1`, a smooth section
  is the sum of its cut-off frame coefficients times sections agreeing with the local frame.
-/

public section

open Bundle Module
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] {n : ℕ∞ω} [ContMDiffVectorBundle 1 F V I]
  [ContMDiffVectorBundle n F V I]
  {ι : Type*} (e : Trivialization F (π F V)) [MemTrivializationAtlas e] (b : Basis ι 𝕜 F)
  (ρ : C^n⟮I, M; 𝕜⟯) (hρ : tsupport ρ ⊆ e.baseSet)

/-- The `i`-th coefficient of a `C^n` section in the local frame of `e`, multiplied by a `C^n`
function `ρ` supported in `e.baseSet`, as a `C^n(M)`-linear map to `C^n` functions. -/
def cutoffLocalFrameCoeff (i : ι) : Cₛ^n⟮I; F, V⟯ →ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯ where
  toFun s := ⟨fun y ↦ ρ y * e.localFrameCoeff I b i y (s y),
    e.contMDiff_mul_localFrameCoeff b ρ.contMDiff.contMDiffOn hρ s.contMDiff.contMDiffOn i⟩
  map_add' s t := by
    ext y
    exact congrArg (ρ y * ·) (map_add (e.localFrameCoeff I b i y) (s y) (t y)) |>.trans
      (mul_add _ _ _)
  map_smul' f s := by
    ext y
    have h := congrArg (e.localFrameCoeff I b i y) (ContMDiffSection.smul_apply f s y)
    rw [map_smul, smul_eq_mul] at h
    exact (congrArg (ρ y * ·) h).trans (mul_left_comm _ _ _)

/-- The cut-off frame coefficient of `s` at `y` is `ρ y` times the frame coefficient of `s y`. -/
@[simp]
theorem cutoffLocalFrameCoeff_apply (i : ι) (s : Cₛ^n⟮I; F, V⟯) (y : M) :
    e.cutoffLocalFrameCoeff b ρ hρ i s y = ρ y * e.localFrameCoeff I b i y (s y) :=
  (rfl)

/-- At a point where `ρ = 1` and the sections `fr i` agree with the local frame of `e`, a smooth
section is the sum of its cut-off frame coefficients times the `fr i`. -/
theorem apply_eq_sum_cutoffLocalFrameCoeff_smul [Fintype ι] (fr : ι → Cₛ^n⟮I; F, V⟯)
    (s : Cₛ^n⟮I; F, V⟯) {y : M} (hy : ρ y = 1) (hfr : ∀ i, fr i y = e.localFrame b i y) :
    s y = (∑ i, e.cutoffLocalFrameCoeff b ρ hρ i s • fr i : Cₛ^n⟮I; F, V⟯) y := by
  have hyb : y ∈ e.baseSet := hρ (subset_tsupport _ (by simp [hy]))
  have h := congrFun (map_sum (ContMDiffSection.coeAddHom I F n V)
    (fun i ↦ e.cutoffLocalFrameCoeff b ρ hρ i s • fr i) Finset.univ) y
  simp only [ContMDiffSection.coeAddHom_apply, Finset.sum_apply, ContMDiffSection.smul_apply,
    cutoffLocalFrameCoeff_apply, hfr, hy, one_mul] at h
  rw [h]
  exact e.eq_sum_localFrameCoeff_smul hyb

end Bundle.Trivialization
