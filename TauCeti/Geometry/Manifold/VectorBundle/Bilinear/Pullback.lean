/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Bilinear
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Pullback and chart expressions of covariant two-tensors on manifolds

For a manifold `M` with model with corners `I` over a nontrivially normed field `𝕜` and a normed
space `G`, a covariant two-tensor with values in `G` is a family
`b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G` of continuous bilinear maps on the
tangent spaces. Along a map `f : M → M'`, the pullback `TauCeti.mpullbackBilin I I' f b` precomposes
`b (f x)` in both arguments with `mfderiv I I' f x`.

Specializing to the inverse extended chart at `x₀` within `range I` gives the coordinate expression
`TauCeti.inChartAtBilin I x₀ b : E → E →L[𝕜] E →L[𝕜] G`, which agrees on `(extChartAt I x₀).target`
with the fibre coordinate of `b` in the canonical trivialization of `TM →L[𝕜] TM →L[𝕜] G`.

## Main declarations

* `TauCeti.mpullbackBilinWithin`, `TauCeti.mpullbackBilin`: pullback of covariant two-tensors along
  manifold maps.
* `TauCeti.inChartAtBilin`: coordinate expression of a covariant two-tensor in the preferred
  extended chart at `x₀`.
* `TauCeti.inChartAtBilin_eq_trivializationAt`: agreement with the hom-bundle trivialization on the
  extended chart target.
* `TauCeti.differentiableWithinAt_inChartAtBilin`, `TauCeti.contDiffWithinAt_inChartAtBilin`:
  transfer of section regularity to the coordinate expression.
* `TauCeti.mpullbackBilin_eq_pullbackBilinL`: expressing `mpullbackBilin` in charts via
  `ContinuousLinearMap.pullbackBilinL`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 12.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped ContDiff Manifold Topology

-- Resolve normed-space vs seminormed-space diamonds on nested continuous linear map spaces.
attribute [local instance 1001] NormedAddCommGroup.toSeminormedAddCommGroup
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid NormedSpace.toModule

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedAddCommGroup (V →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedSpace 𝕜 (V →L[𝕜] G) := ContinuousLinearMap.toNormedSpace

namespace TauCeti

section Pullback

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H'']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Pullback of a covariant two-tensor along `f` using the manifold derivative within `s`. Uses
`ContinuousLinearMap.precomp` and `comp` so no norm structure is imposed on `TangentSpace`. -/
def mpullbackBilinWithin (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (f : M → M') (s : Set M)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G :=
  (ContinuousLinearMap.precomp G (mfderivWithin I I' f s x)).comp
    ((b (f x)).comp (mfderivWithin I I' f s x))

/-- Pullback of a covariant two-tensor along `f` using the manifold derivative. -/
def mpullbackBilin (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (f : M → M') (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G :=
  (ContinuousLinearMap.precomp G (mfderiv I I' f x)).comp
    ((b (f x)).comp (mfderiv I I' f x))

variable {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {I'' : ModelWithCorners 𝕜 E'' H''}

@[simp]
theorem mpullbackBilinWithin_apply (f : M → M') (s : Set M)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G)
    (x : M) (v w : TangentSpace I x) :
    mpullbackBilinWithin I I' f s b x v w =
      b (f x) (mfderivWithin I I' f s x v) (mfderivWithin I I' f s x w) := by
  rfl

@[simp]
theorem mpullbackBilin_apply (f : M → M')
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G)
    (x : M) (v w : TangentSpace I x) :
    mpullbackBilin I I' f b x v w = b (f x) (mfderiv I I' f x v) (mfderiv I I' f x w) := by
  rfl

/-- Pointwise pullback along `f`, viewed on the model tangent spaces, is the continuous linear
operator `ContinuousLinearMap.pullbackBilinL` of `mfderiv I I' f x`. -/
theorem mpullbackBilin_apply_eq_pullbackBilinL (f : M → M')
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) (x : M) :
    (mpullbackBilin I I' f b x : E →L[𝕜] E →L[𝕜] G) =
      ContinuousLinearMap.pullbackBilinL (V := E') (W := E) (G := G)
        (mfderiv I I' f x) (b (f x)) := by
  ext v w
  exact (ContinuousLinearMap.pullbackBilinL_apply (V := E') (W := E) (G := G)
    (mfderiv I I' f x) (b (f x)) v w).symm

@[simp]
theorem mpullbackBilinWithin_univ (f : M → M')
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilinWithin I I' f univ b = mpullbackBilin I I' f b := by
  funext x; ext v w; simp

theorem mpullbackBilinWithin_eq_mpullbackBilin {f : M → M'} {s : Set M} {x : M}
    (hs : UniqueMDiffWithinAt I s x) (hf : MDifferentiableAt I I' f x)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilinWithin I I' f s b x = mpullbackBilin I I' f b x := by
  ext v w; simp [mfderivWithin_eq_mfderiv hs hf]

@[simp]
theorem mpullbackBilin_id (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mpullbackBilin I I id b = b := by
  funext x; ext v w; simp

/-- Maps that agree near `x` within `s`, and at `x`, pull back a covariant two-tensor identically
at `x`. -/
theorem _root_.Filter.EventuallyEq.mpullbackBilinWithin_eq {f₁ f₂ : M → M'} {s : Set M} {x : M}
    (h : f₁ =ᶠ[𝓝[s] x] f₂) (hx : f₁ x = f₂ x)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilinWithin I I' f₁ s b x = mpullbackBilinWithin I I' f₂ s b x := by
  ext v w
  rw [mpullbackBilinWithin_apply, mpullbackBilinWithin_apply, h.mfderivWithin_eq hx]
  change b (f₁ x) (mfderivWithin I I' f₂ s x v) (mfderivWithin I I' f₂ s x w) =
    b (f₂ x) (mfderivWithin I I' f₂ s x v) (mfderivWithin I I' f₂ s x w)
  rw [hx]

/-- Maps that agree near `x` pull back a covariant two-tensor identically at `x`. -/
theorem _root_.Filter.EventuallyEq.mpullbackBilin_eq {f₁ f₂ : M → M'} {x : M}
    (h : f₁ =ᶠ[𝓝 x] f₂)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilin I I' f₁ b x = mpullbackBilin I I' f₂ b x := by
  rw [← mpullbackBilinWithin_univ, ← mpullbackBilinWithin_univ]
  exact (h.filter_mono nhdsWithin_le_nhds).mpullbackBilinWithin_eq h.eq_of_nhds b

/-- Contravariant functoriality `(g ∘ f)^* b = f^* (g^* b)` at a point where `f` and `g` are
differentiable. -/
theorem mpullbackBilin_comp_at {f : M → M'} {g : M' → M''} {x : M}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I' I'' g (f x))
    (b : (z : M'') → TangentSpace I'' z →L[𝕜] TangentSpace I'' z →L[𝕜] G) :
    mpullbackBilin I I'' (g ∘ f) b x = mpullbackBilin I I' f (mpullbackBilin I' I'' g b) x := by
  ext v w; simp [mfderiv_comp x hg hf]

@[simp]
theorem mpullbackBilinWithin_zero (f : M → M') (s : Set M) :
    mpullbackBilinWithin I I' f s
      (0 : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) = 0 := by
  funext x; ext v w; simp

@[simp]
theorem mpullbackBilin_zero (f : M → M') :
    mpullbackBilin I I' f
      (0 : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) = 0 := by
  funext x; ext v w; simp

@[simp]
theorem mpullbackBilinWithin_add (f : M → M') (s : Set M)
    (b₁ b₂ : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilinWithin I I' f s (b₁ + b₂) =
      mpullbackBilinWithin I I' f s b₁ + mpullbackBilinWithin I I' f s b₂ := by
  funext x; ext v w; simp

@[simp]
theorem mpullbackBilin_add (f : M → M')
    (b₁ b₂ : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilin I I' f (b₁ + b₂) = mpullbackBilin I I' f b₁ + mpullbackBilin I I' f b₂ := by
  funext x; ext v w; simp

@[simp]
theorem mpullbackBilin_neg (f : M → M')
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilin I I' f (-b) = -mpullbackBilin I I' f b := by
  funext x; ext v w; simp

@[simp]
theorem mpullbackBilin_smul (f : M → M') (c : 𝕜)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilin I I' f (c • b) = c • mpullbackBilin I I' f b := by
  funext x; ext v w; simp

/-- Pulling back a symmetric covariant two-tensor produces a symmetric covariant two-tensor. -/
theorem mpullbackBilin_symm (f : M → M')
    {b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G}
    (hb : ∀ y v w, b y v w = b y w v) (x : M) (v w : TangentSpace I x) :
    mpullbackBilin I I' f b x v w = mpullbackBilin I I' f b x w v := by
  rw [mpullbackBilin_apply, mpullbackBilin_apply, hb]

end Pullback

section InChart

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Coordinate expression of a covariant two-tensor `b` in the preferred extended chart at `x₀`:
its pullback along `(extChartAt I x₀).symm` within `range I`. -/
def inChartAtBilin (I : ModelWithCorners 𝕜 E H) (x₀ : M)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    E → E →L[𝕜] E →L[𝕜] G :=
  mpullbackBilinWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) b

@[simp]
theorem inChartAtBilin_apply (x₀ : M)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) (z v w : E) :
    inChartAtBilin I x₀ b z v w =
      b ((extChartAt I x₀).symm z)
        (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) z v)
        (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) z w) := by
  rfl

private theorem hasMFDerivWithinAt_extChartAt_symm_self (x : M) :
    HasMFDerivWithinAt 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (extChartAt I x x)
      (ContinuousLinearMap.id 𝕜 E) := by
  refine ⟨(continuousAt_extChartAt_symm'' (mem_extChartAt_target x)).continuousWithinAt, ?_⟩
  simp only [writtenInExtChartAt, extChartAt_to_inv, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, PartialEquiv.refl_symm, preimage_id, modelWithCornersSelf_coe,
    range_id, inter_univ]
  have hev : (extChartAt I x ∘ (extChartAt I x).symm ∘ id) =ᶠ[𝓝[range I] (extChartAt I x x)]
      id := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (mem_extChartAt_target x)] with u hu
    exact (extChartAt I x).right_inv hu
  exact (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq hev
    ((extChartAt I x).right_inv (mem_extChartAt_target x))

/-- At the chart centre, the coordinate expression of `b` evaluates to `b x`. -/
theorem inChartAtBilin_extChartAt_self (x : M)
    (b : (y : M) → TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] G) :
    inChartAtBilin I x b (extChartAt I x x) = b x := by
  have hu : UniqueMDiffWithinAt 𝓘(𝕜, E) (range I) (extChartAt I x x) :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2
      (I.uniqueDiffOn _ (extChartAt_target_subset_range x (mem_extChartAt_target x)))
  ext v w
  rw [inChartAtBilin_apply]
  have hd : (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (extChartAt I x x) :
      E →L[𝕜] E) = ContinuousLinearMap.id 𝕜 E :=
    (hasMFDerivWithinAt_extChartAt_symm_self (I := I) x).mfderivWithin hu
  have hb_eq : (b ((extChartAt I x).symm (extChartAt I x x)) : E →L[𝕜] E →L[𝕜] G) = b x := by
    rw [extChartAt_to_inv]
  exact congrArg₂ (fun (B : E →L[𝕜] E →L[𝕜] G) (L : E →L[𝕜] E) ↦ B (L v) (L w)) hb_eq hd

/-- Over the model space `𝓘(𝕜, E)`, the chart expression is `b` itself. -/
@[simp]
theorem inChartAtBilin_modelSpace (x₀ : E)
    (b : (x : E) → TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E) x →L[𝕜] G) :
    inChartAtBilin 𝓘(𝕜, E) x₀ b = b := by
  funext z; ext v w; simp [inChartAtBilin]

@[simp]
theorem inChartAtBilin_zero (x₀ : M) :
    inChartAtBilin I x₀ (0 : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) = 0 :=
  mpullbackBilinWithin_zero _ _

@[simp]
theorem inChartAtBilin_add (x₀ : M)
    (b₁ b₂ : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    inChartAtBilin I x₀ (b₁ + b₂) = inChartAtBilin I x₀ b₁ + inChartAtBilin I x₀ b₂ :=
  mpullbackBilinWithin_add _ _ b₁ b₂

@[simp]
theorem inChartAtBilin_neg (x₀ : M)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    inChartAtBilin I x₀ (-b) = -inChartAtBilin I x₀ b := by
  funext z; ext v w; simp only [inChartAtBilin_apply, Pi.neg_apply, neg_apply]

@[simp]
theorem inChartAtBilin_smul (x₀ : M) (c : 𝕜)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    inChartAtBilin I x₀ (c • b) = c • inChartAtBilin I x₀ b := by
  funext z; ext v w; simp only [inChartAtBilin_apply, Pi.smul_apply, smul_apply]

theorem inChartAtBilin_fun_smul (x₀ : M) (f : M → 𝕜)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    inChartAtBilin I x₀ (fun y ↦ f y • b y) =
      fun z ↦ f ((extChartAt I x₀).symm z) • inChartAtBilin I x₀ b z := by
  funext z; ext v w; simp only [inChartAtBilin_apply, smul_apply]

variable [IsManifold I 1 M]

/-- On the extended chart target at `x₀`, `inChartAtBilin I x₀ b` is the fibre coordinate of `b` in
the canonical trivialization of the hom bundle `TM →L[𝕜] TM →L[𝕜] G`. -/
theorem inChartAtBilin_eq_trivializationAt (x₀ : M)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G)
    {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    inChartAtBilin I x₀ b z =
      (trivializationAt (E →L[𝕜] E →L[𝕜] G)
        (fun y : M ↦ TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] G) x₀
          ⟨(extChartAt I x₀).symm z, b ((extChartAt I x₀).symm z)⟩).2 := by
  have hy : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
    simpa only [extChartAt_source] using (extChartAt I x₀).map_target hz
  have hy' : (extChartAt I x₀).symm z ∈
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by simpa using hy
  ext v w
  simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hy' hy' (by simp)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]
  rw [← Trivialization.symmL_apply (R := 𝕜) _ hy', ← Trivialization.symmL_apply (R := 𝕜) _ hy',
    TangentBundle.symmL_trivializationAt hy, (extChartAt I x₀).right_inv hz, inChartAtBilin_apply]
  rfl

/-- Near `extChartAt I x₀ x₀` within `range I`, the hom-bundle fibre coordinate of `b` agrees with
`inChartAtBilin I x₀ b`. -/
theorem trivializationAt_snd_eventuallyEq_inChartAtBilin (x₀ : M)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    (fun z ↦ (trivializationAt (E →L[𝕜] E →L[𝕜] G)
      (fun y : M ↦ TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] G) x₀
        ⟨(extChartAt I x₀).symm z, b ((extChartAt I x₀).symm z)⟩).2)
      =ᶠ[𝓝[range I] (extChartAt I x₀ x₀)] inChartAtBilin I x₀ b := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with z hz
  exact (inChartAtBilin_eq_trivializationAt x₀ b hz).symm

/-- A section of the bilinear-map bundle differentiable within `s` at `x` has a differentiable
coordinate expression in the preferred chart at `x`. -/
theorem differentiableWithinAt_inChartAtBilin
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {s : Set M} {x : M}
    (hb : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) s x) :
    DifferentiableWithinAt 𝕜 (inChartAtBilin I x b)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  let _ : ∀ y : M, IsNormableSpace 𝕜 (TangentSpace I y) := fun y ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 E (TangentSpace I : M → Type _) y).isNormableSpace
  have heq := trivializationAt_snd_eventuallyEq_inChartAtBilin (I := I) x b
  have hflat := ((mdifferentiableWithinAt_section I b).mp hb
    ).differentiableWithinAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.comp_def, id_eq] at hflat
  exact hflat.congr_of_eventuallyEq (heq.symm.filter_mono (nhdsWithin_mono _ inter_subset_right))
    (heq.self_of_nhdsWithin (extChartAt_target_subset_range x (mem_extChartAt_target x))).symm

/-- At any point `z ∈ (extChartAt I x₀).target`, differentiability of `b` as a section at
`(extChartAt I x₀).symm z` gives differentiability of `inChartAtBilin I x₀ b` within `range I` at
`z`. -/
theorem differentiableWithinAt_inChartAtBilin_of_mem [IsManifold I 2 M] (x₀ : M)
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hb : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun q ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) q (b q)) ((extChartAt I x₀).symm z)) :
    DifferentiableWithinAt 𝕜 (inChartAtBilin I x₀ b) (range I) z := by
  let _ : IsManifold I (1 + 1) M := by simpa only [one_add_one_eq_two] using ‹IsManifold I 2 M›
  let _ : ∀ q : M, IsNormableSpace 𝕜 (TangentSpace I q) := fun q ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 E (TangentSpace I : M → Type _) q).isNormableSpace
  have hy_hom : (extChartAt I x₀).symm z ∈ (trivializationAt (E →L[𝕜] E →L[𝕜] G)
      (fun q : M ↦ TangentSpace I q →L[𝕜] TangentSpace I q →L[𝕜] G) x₀).baseSet := by
    simpa [extChartAt_source] using (extChartAt I x₀).map_target hz
  have hm := (((trivializationAt (E →L[𝕜] E →L[𝕜] G)
    (fun q : M ↦ TangentSpace I q →L[𝕜] TangentSpace I q →L[𝕜] G) x₀
    ).mdifferentiableAt_section_iff I b hy_hom).mp hb).comp_mdifferentiableWithinAt z
      (mdifferentiableWithinAt_extChartAt_symm hz) |>.differentiableWithinAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, preimage_id, modelWithCornersSelf_coe, range_id, inter_univ,
    Function.comp_def, id_eq] at hm
  refine hm.congr_of_eventuallyEq ?_ (inChartAtBilin_eq_trivializationAt x₀ b hz)
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz] with ζ hζ
  exact inChartAtBilin_eq_trivializationAt x₀ b hζ

/-- A `C^n` section of the bilinear-map bundle within `s` at `x` has a `C^n` coordinate expression
in the preferred chart at `x`. -/
theorem contDiffWithinAt_inChartAtBilin {n : ℕ∞ω}
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {s : Set M} {x : M}
    (hb : ContMDiffWithinAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) s x) :
    ContDiffWithinAt 𝕜 n (inChartAtBilin I x b)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  let _ : ∀ y : M, IsNormableSpace 𝕜 (TangentSpace I y) := fun y ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 E (TangentSpace I : M → Type _) y).isNormableSpace
  have heq := trivializationAt_snd_eventuallyEq_inChartAtBilin (I := I) x b
  rw [contMDiffWithinAt_section_iff, contMDiffWithinAt_iff_source,
    contMDiffWithinAt_iff_contDiffWithinAt] at hb
  exact hb.congr_of_eventuallyEq (heq.symm.filter_mono (nhdsWithin_mono _ inter_subset_right))
    (heq.self_of_nhdsWithin (extChartAt_target_subset_range x (mem_extChartAt_target x))).symm

omit [IsManifold I 1 M] in
private theorem mpullbackBilinWithin_eq_pullbackBilinL [IsManifold I' 1 M']
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G)
    {f : E → M'} {s : Set E} {z : E} (c : M')
    (hfc : f z ∈ (extChartAt I' c).source)
    (hf : MDifferentiableWithinAt 𝓘(𝕜, E) I' f s z) (hs : UniqueDiffWithinAt 𝕜 s z) :
    (mpullbackBilinWithin 𝓘(𝕜, E) I' f s b z : E →L[𝕜] E →L[𝕜] G) =
      ContinuousLinearMap.pullbackBilinL
        (fderivWithin 𝕜 (extChartAt I' c ∘ f) s z)
        (inChartAtBilin I' c b (extChartAt I' c (f z))) := by
  set e := extChartAt I' c
  have hpre : f ⁻¹' e.source ∈ 𝓝[s] z :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds' hfc)
  have hfe : f =ᶠ[𝓝[s] z] e.symm ∘ (e ∘ f) := by
    filter_upwards [hpre] with a ha; exact (e.left_inv ha).symm
  have hg : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') (e ∘ f) s z :=
    (mdifferentiableAt_extChartAt (by simpa only [e, extChartAt_source] using hfc))
      |>.comp_mdifferentiableWithinAt z hf
  have hrange : (e ∘ f) ⁻¹' range I' ∈ 𝓝[s] z := by
    filter_upwards [hpre] with a ha; exact extChartAt_target_subset_range c (e.map_source ha)
  have hd : mfderivWithin 𝓘(𝕜, E) I' f s z =
      (mfderivWithin 𝓘(𝕜, E') I' e.symm (range I') (e (f z))).comp
        (mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') (e ∘ f) s z) := by
    rw [hfe.mfderivWithin_eq (e.left_inv hfc).symm]
    exact mfderivWithin_comp_of_preimage_mem_nhdsWithin z
      (mdifferentiableWithinAt_extChartAt_symm (e.map_source hfc)) hg hrange
      hs.uniqueMDiffWithinAt
  ext v w
  have h := inChartAtBilin_apply c b (e (f z))
    (fderivWithin 𝕜 (e ∘ f) s z v) (fderivWithin 𝕜 (e ∘ f) s z w)
  rw [e.left_inv hfc] at h
  rw [mpullbackBilinWithin_apply, hd, mfderivWithin_eq_fderivWithin]
  exact h.symm.trans (ContinuousLinearMap.pullbackBilinL_apply
    (V := E') (W := E) (G := G) (fderivWithin 𝕜 (e ∘ f) s z)
    (inChartAtBilin I' c b (e (f z))) v w).symm

/-- Pulling `b` back along a map `f` differentiable at `x` with `f x ∈ (extChartAt I' c).source`
equals the flat pullback of `inChartAtBilin I' c b` along the coordinate representation of `f` from
the chart at `x` to the chart at `c`. -/
theorem mpullbackBilin_eq_pullbackBilinL [IsManifold I' 1 M']
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G)
    {f : M → M'} {x : M} (c : M')
    (hf : MDifferentiableAt I I' f x) (hfc : f x ∈ (extChartAt I' c).source) :
    (mpullbackBilin I I' f b x : E →L[𝕜] E →L[𝕜] G) =
      ContinuousLinearMap.pullbackBilinL
        (fderivWithin 𝕜 (extChartAt I' c ∘ f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x))
        (inChartAtBilin I' c b (extChartAt I' c (f x))) := by
  set z₀ := extChartAt I x x
  have hu : UniqueDiffWithinAt 𝕜 (range I) z₀ :=
    I.uniqueDiffOn _ (extChartAt_target_subset_range x (mem_extChartAt_target x))
  have hf' : MDifferentiableAt I I' f ((extChartAt I x).symm z₀) := by rwa [extChartAt_to_inv]
  have hfc' : (f ∘ (extChartAt I x).symm) z₀ ∈ (extChartAt I' c).source := by
    simpa only [Function.comp_apply, z₀, extChartAt_to_inv] using hfc
  have hchain : (mfderivWithin 𝓘(𝕜, E) I' (f ∘ (extChartAt I x).symm) (range I) z₀ :
      E →L[𝕜] E') =
      (mfderiv I I' f ((extChartAt I x).symm z₀) : E →L[𝕜] E').comp
        (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) z₀ : E →L[𝕜] E) := by
    rw [← mfderivWithin_univ]
    exact mfderivWithin_comp z₀ hf'.mdifferentiableWithinAt
      (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x)) (subset_univ _)
      hu.uniqueMDiffWithinAt
  have hcomp : inChartAtBilin I x (mpullbackBilin I I' f b) z₀ =
      (mpullbackBilinWithin 𝓘(𝕜, E) I' (f ∘ (extChartAt I x).symm) (range I) b z₀ :
        E →L[𝕜] E →L[𝕜] G) := by
    ext v w
    change (b (f ((extChartAt I x).symm z₀)) : E' →L[𝕜] E' →L[𝕜] G)
        (((mfderiv I I' f ((extChartAt I x).symm z₀) : E →L[𝕜] E').comp
          (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) z₀ : E →L[𝕜] E)) v)
        (((mfderiv I I' f ((extChartAt I x).symm z₀) : E →L[𝕜] E').comp
          (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) z₀ : E →L[𝕜] E)) w) =
      (b (f ((extChartAt I x).symm z₀)) : E' →L[𝕜] E' →L[𝕜] G)
        ((mfderivWithin 𝓘(𝕜, E) I' (f ∘ (extChartAt I x).symm) (range I) z₀ : E →L[𝕜] E') v)
        ((mfderivWithin 𝓘(𝕜, E) I' (f ∘ (extChartAt I x).symm) (range I) z₀ : E →L[𝕜] E') w)
    rw [hchain]
  rw [← inChartAtBilin_extChartAt_self x (mpullbackBilin I I' f b)]
  refine hcomp.trans ?_
  have key := mpullbackBilinWithin_eq_pullbackBilinL b c hfc'
    (hf'.comp_mdifferentiableWithinAt z₀
      (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x))) hu
  simp only [Function.comp_apply, z₀, extChartAt_to_inv] at key
  exact key

end InChart

end TauCeti
