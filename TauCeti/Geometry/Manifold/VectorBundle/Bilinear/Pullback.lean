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

Defines `TauCeti.mpullbackBilinWithin`, `TauCeti.mpullbackBilin`, and the preferred-chart expression
`TauCeti.inChartAtBilin` for covariant two-tensors
`b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G`, proves agreement of
`inChartAtBilin` with the hom-bundle trivialization (`inChartAtBilin_eq_trivializationAt`),
transfers section regularity (`differentiableWithinAt_inChartAtBilin`,
`contDiffWithinAt_inChartAtBilin`), and relates manifold pullback to `pullbackBilinL`
(`mpullbackBilin_eq_pullbackBilinL`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 12.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped ContDiff Manifold Topology

attribute [local instance 1001] NormedAddCommGroup.toSeminormedAddCommGroup
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid NormedSpace.toModule

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedAddCommGroup (V →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedSpace 𝕜 (V →L[𝕜] G) := ContinuousLinearMap.toNormedSpace

namespace TauCeti

variable {𝕜 E H M E' H' M' E'' H'' M'' G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H'']
  [TopologicalSpace M''] [ChartedSpace H'' M'']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

section Pullback

/-- Pullback of a covariant two-tensor along `f` using `mfderivWithin`. -/
def mpullbackBilinWithin (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (f : M → M') (s : Set M)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G :=
  (ContinuousLinearMap.precomp G (mfderivWithin I I' f s x)).comp
    ((b (f x)).comp (mfderivWithin I I' f s x))

/-- Pullback of a covariant two-tensor along `f` using `mfderiv`. -/
def mpullbackBilin (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (f : M → M') (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G :=
  (ContinuousLinearMap.precomp G (mfderiv I I' f x)).comp ((b (f x)).comp (mfderiv I I' f x))

variable {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {I'' : ModelWithCorners 𝕜 E'' H''}

@[simp] theorem mpullbackBilinWithin_apply (f : M → M') (s : Set M)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G)
    (x : M) (v w : TangentSpace I x) :
    mpullbackBilinWithin I I' f s b x v w =
      b (f x) (mfderivWithin I I' f s x v) (mfderivWithin I I' f s x w) := by rfl

@[simp] theorem mpullbackBilin_apply (f : M → M')
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G)
    (x : M) (v w : TangentSpace I x) :
    mpullbackBilin I I' f b x v w = b (f x) (mfderiv I I' f x v) (mfderiv I I' f x w) := by rfl

theorem mpullbackBilin_apply_eq_pullbackBilinL (f : M → M')
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) (x : M) :
    (mpullbackBilin I I' f b x : E →L[𝕜] E →L[𝕜] G) =
      ContinuousLinearMap.pullbackBilinL (V := E') (W := E) (G := G)
        (mfderiv I I' f x) (b (f x)) := by
  ext v w; exact (ContinuousLinearMap.pullbackBilinL_apply (V := E') (W := E) (G := G)
    (mfderiv I I' f x) (b (f x)) v w).symm

@[simp] theorem mpullbackBilinWithin_univ (f : M → M')
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilinWithin I I' f univ b = mpullbackBilin I I' f b := by funext x; ext v w; simp

theorem mpullbackBilinWithin_eq_mpullbackBilin {f : M → M'} {s : Set M} {x : M}
    (hs : UniqueMDiffWithinAt I s x) (hf : MDifferentiableAt I I' f x)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilinWithin I I' f s b x = mpullbackBilin I I' f b x := by
  ext v w; simp [mfderivWithin_eq_mfderiv hs hf]

@[simp] theorem mpullbackBilin_id (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mpullbackBilin I I id b = b := by funext x; ext v w; simp

theorem _root_.Filter.EventuallyEq.mpullbackBilinWithin_eq {f₁ f₂ : M → M'} {s : Set M} {x : M}
    (h : f₁ =ᶠ[𝓝[s] x] f₂) (hx : f₁ x = f₂ x)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilinWithin I I' f₁ s b x = mpullbackBilinWithin I I' f₂ s b x := by
  ext v w; rw [mpullbackBilinWithin_apply, mpullbackBilinWithin_apply, h.mfderivWithin_eq hx]
  exact congrArg (fun y ↦ (b y : E' →L[𝕜] E' →L[𝕜] G) _ _) hx

theorem _root_.Filter.EventuallyEq.mpullbackBilin_eq {f₁ f₂ : M → M'} {x : M} (h : f₁ =ᶠ[𝓝 x] f₂)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilin I I' f₁ b x = mpullbackBilin I I' f₂ b x := by
  rw [← mpullbackBilinWithin_univ, ← mpullbackBilinWithin_univ]
  exact (h.filter_mono nhdsWithin_le_nhds).mpullbackBilinWithin_eq h.eq_of_nhds b

theorem mpullbackBilin_comp_at {f : M → M'} {g : M' → M''} {x : M}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I' I'' g (f x))
    (b : (z : M'') → TangentSpace I'' z →L[𝕜] TangentSpace I'' z →L[𝕜] G) :
    mpullbackBilin I I'' (g ∘ f) b x = mpullbackBilin I I' f (mpullbackBilin I' I'' g b) x := by
  ext v w; simp [mfderiv_comp x hg hf]

@[simp] theorem mpullbackBilinWithin_zero (f : M → M') (s : Set M) :
    mpullbackBilinWithin I I' f s
      (0 : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) = 0 := by
  funext x; ext v w; simp

@[simp] theorem mpullbackBilin_zero (f : M → M') :
    mpullbackBilin I I' f
      (0 : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) = 0 := by
  funext x; ext v w; simp

@[simp] theorem mpullbackBilinWithin_add (f : M → M') (s : Set M)
    (b₁ b₂ : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilinWithin I I' f s (b₁ + b₂) =
      mpullbackBilinWithin I I' f s b₁ + mpullbackBilinWithin I I' f s b₂ := by
  funext x; ext v w; simp

@[simp] theorem mpullbackBilin_add (f : M → M')
    (b₁ b₂ : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilin I I' f (b₁ + b₂) = mpullbackBilin I I' f b₁ + mpullbackBilin I I' f b₂ := by
  funext x; ext v w; simp

@[simp] theorem mpullbackBilin_neg (f : M → M')
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilin I I' f (-b) = -mpullbackBilin I I' f b := by funext x; ext v w; simp

@[simp] theorem mpullbackBilin_smul (f : M → M') (c : 𝕜)
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G) :
    mpullbackBilin I I' f (c • b) = c • mpullbackBilin I I' f b := by funext x; ext v w; simp

theorem mpullbackBilin_symm (f : M → M')
    {b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G}
    (hb : ∀ y v w, b y v w = b y w v) (x : M) (v w : TangentSpace I x) :
    mpullbackBilin I I' f b x v w = mpullbackBilin I I' f b x w v := by
  rw [mpullbackBilin_apply, mpullbackBilin_apply, hb]

end Pullback

section InChart

variable {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}

/-- Coordinate expression of `b` in the preferred extended chart at `x₀`. -/
def inChartAtBilin (I : ModelWithCorners 𝕜 E H) (x₀ : M)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) : E → E →L[𝕜] E →L[𝕜] G :=
  mpullbackBilinWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) b

@[simp] theorem inChartAtBilin_apply (x₀ : M)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) (z v w : E) :
    inChartAtBilin I x₀ b z v w = b ((extChartAt I x₀).symm z)
      (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) z v)
      (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) z w) := by rfl

theorem inChartAtBilin_extChartAt_self (x : M)
    (b : (y : M) → TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] G) :
    inChartAtBilin I x b (extChartAt I x x) = b x := by
  have hm := mem_extChartAt_target (I := I) x
  have hmf : HasMFDerivWithinAt 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (extChartAt I x x)
      (ContinuousLinearMap.id 𝕜 E) := by
    refine ⟨(continuousAt_extChartAt_symm'' hm).continuousWithinAt, ?_⟩
    simp only [writtenInExtChartAt, extChartAt_to_inv, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, PartialEquiv.refl_symm, preimage_id, modelWithCornersSelf_coe,
      range_id, inter_univ]
    refine (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq ?_ ((extChartAt I x).right_inv hm)
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hm] with u hu
    exact (extChartAt I x).right_inv hu
  have hd : (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (extChartAt I x x) :
      E →L[𝕜] E) = ContinuousLinearMap.id 𝕜 E :=
    hmf.mfderivWithin (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2
      (I.uniqueDiffOn _ (extChartAt_target_subset_range x hm)))
  ext v w; rw [inChartAtBilin_apply]
  exact congrArg₂ (fun (B : E →L[𝕜] E →L[𝕜] G) (L : E →L[𝕜] E) ↦ B (L v) (L w))
    (by rw [extChartAt_to_inv]) hd

@[simp] theorem inChartAtBilin_modelSpace (x₀ : E)
    (b : (x : E) → TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E) x →L[𝕜] G) :
    inChartAtBilin 𝓘(𝕜, E) x₀ b = b := by funext z; ext v w; simp [inChartAtBilin]

@[simp] theorem inChartAtBilin_zero (x₀ : M) :
    inChartAtBilin I x₀ (0 : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) = 0 :=
  mpullbackBilinWithin_zero _ _

@[simp] theorem inChartAtBilin_add (x₀ : M)
    (b₁ b₂ : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    inChartAtBilin I x₀ (b₁ + b₂) = inChartAtBilin I x₀ b₁ + inChartAtBilin I x₀ b₂ :=
  mpullbackBilinWithin_add _ _ b₁ b₂

@[simp] theorem inChartAtBilin_neg (x₀ : M)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    inChartAtBilin I x₀ (-b) = -inChartAtBilin I x₀ b := by
  funext z; ext v w; simp only [inChartAtBilin_apply, Pi.neg_apply, neg_apply]

@[simp] theorem inChartAtBilin_smul (x₀ : M) (c : 𝕜)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    inChartAtBilin I x₀ (c • b) = c • inChartAtBilin I x₀ b := by
  funext z; ext v w; simp only [inChartAtBilin_apply, Pi.smul_apply, smul_apply]

theorem inChartAtBilin_fun_smul (x₀ : M) (f : M → 𝕜)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    inChartAtBilin I x₀ (fun y ↦ f y • b y) =
      fun z ↦ f ((extChartAt I x₀).symm z) • inChartAtBilin I x₀ b z := by
  funext z; ext v w; simp only [inChartAtBilin_apply, smul_apply]

variable [IsManifold I 1 M]

/-- On `(extChartAt I x₀).target`, `inChartAtBilin I x₀ b` agrees with the hom-bundle
trivialization of `TM →L[𝕜] TM →L[𝕜] G`. -/
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
  ext v w; simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hy' hy' (by simp)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]
  rw [← Trivialization.symmL_apply (R := 𝕜) _ hy', ← Trivialization.symmL_apply (R := 𝕜) _ hy',
    TangentBundle.symmL_trivializationAt hy, (extChartAt I x₀).right_inv hz, inChartAtBilin_apply]
  rfl

theorem trivializationAt_snd_eventuallyEq_inChartAtBilin (x₀ : M)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    (fun z ↦ (trivializationAt (E →L[𝕜] E →L[𝕜] G)
      (fun y : M ↦ TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] G) x₀
        ⟨(extChartAt I x₀).symm z, b ((extChartAt I x₀).symm z)⟩).2)
      =ᶠ[𝓝[range I] (extChartAt I x₀ x₀)] inChartAtBilin I x₀ b := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with z hz
  exact (inChartAtBilin_eq_trivializationAt x₀ b hz).symm

variable {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {s : Set M} {x : M}

/-- Differentiability of `b` within `s` at `x` transfers to `inChartAtBilin I x b`. -/
theorem differentiableWithinAt_inChartAtBilin
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

theorem differentiableWithinAt_inChartAtBilin_of_mem [IsManifold I 2 M] (x₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hb : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun q ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) q (b q)) ((extChartAt I x₀).symm z)) :
    DifferentiableWithinAt 𝕜 (inChartAtBilin I x₀ b) (range I) z := by
  let _ : IsManifold I (1 + 1) M := by simpa only [one_add_one_eq_two] using ‹IsManifold I 2 M›
  let _ : ∀ q : M, IsNormableSpace 𝕜 (TangentSpace I q) := fun q ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 E (TangentSpace I : M → Type _) q).isNormableSpace
  set t := trivializationAt (E →L[𝕜] E →L[𝕜] G)
    (fun q : M ↦ TangentSpace I q →L[𝕜] TangentSpace I q →L[𝕜] G) x₀
  have hy_hom : (extChartAt I x₀).symm z ∈ t.baseSet := by
    simpa [t, extChartAt_source] using (extChartAt I x₀).map_target hz
  have hm := ((t.mdifferentiableAt_section_iff I b hy_hom).mp hb).comp_mdifferentiableWithinAt z
    (mdifferentiableWithinAt_extChartAt_symm hz) |>.differentiableWithinAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, preimage_id, modelWithCornersSelf_coe, range_id, inter_univ,
    Function.comp_def, id_eq] at hm
  refine hm.congr_of_eventuallyEq ?_ (inChartAtBilin_eq_trivializationAt x₀ b hz)
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz] with ζ hζ
  exact inChartAtBilin_eq_trivializationAt x₀ b hζ

/-- `C^n` section regularity of `b` within `s` at `x` transfers to `inChartAtBilin I x b`. -/
theorem contDiffWithinAt_inChartAtBilin {n : ℕ∞ω}
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
/-- Pulling `b` back along `f` differentiable at `x` with `f x ∈ (extChartAt I' c).source` equals
the flat pullback of `inChartAtBilin I' c b` along the coordinate representation of `f`. -/
theorem mpullbackBilin_eq_pullbackBilinL [IsManifold I' 1 M']
    (b : (y : M') → TangentSpace I' y →L[𝕜] TangentSpace I' y →L[𝕜] G)
    {f : M → M'} {x : M} (c : M')
    (hf : MDifferentiableAt I I' f x) (hfc : f x ∈ (extChartAt I' c).source) :
    (mpullbackBilin I I' f b x : E →L[𝕜] E →L[𝕜] G) =
      ContinuousLinearMap.pullbackBilinL
        (fderivWithin 𝕜 (extChartAt I' c ∘ f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x))
        (inChartAtBilin I' c b (extChartAt I' c (f x))) := by
  set e := extChartAt I' c
  have hpre : f ⁻¹' e.source ∈ 𝓝 x :=
    hf.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds' hfc)
  have hfe : f =ᶠ[𝓝 x] e.symm ∘ (e ∘ f) := by
    filter_upwards [hpre] with a ha; exact (e.left_inv ha).symm
  have hg : MDifferentiableAt I 𝓘(𝕜, E') (e ∘ f) x :=
    (mdifferentiableAt_extChartAt (by simpa only [e, extChartAt_source] using hfc)).comp x hf
  have hrange : (e ∘ f) ⁻¹' range I' ∈ 𝓝[univ] x := by
    rw [nhdsWithin_univ]
    filter_upwards [hpre] with a ha; exact extChartAt_target_subset_range c (e.map_source ha)
  have hd : (mfderiv I I' f x : E →L[𝕜] E') =
      (mfderivWithin 𝓘(𝕜, E') I' e.symm (range I') (e (f x)) : E' →L[𝕜] E').comp
        (fderivWithin 𝕜 (e ∘ f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x)) := by
    have h1 : (mfderiv I I' f x : E →L[𝕜] E') =
        (mfderivWithin 𝓘(𝕜, E') I' e.symm (range I') (e (f x)) : E' →L[𝕜] E').comp
          (mfderiv I 𝓘(𝕜, E') (e ∘ f) x : E →L[𝕜] E') := by
      rw [← mfderivWithin_univ, (hfe.filter_mono nhdsWithin_le_nhds).mfderivWithin_eq
        (e.left_inv hfc).symm]
      exact (mfderivWithin_comp_of_preimage_mem_nhdsWithin x
        (mdifferentiableWithinAt_extChartAt_symm (e.map_source hfc)) hg.mdifferentiableWithinAt
        hrange (uniqueMDiffWithinAt_univ I)).trans (by rw [mfderivWithin_univ]; rfl)
    have hgf : (mfderiv I 𝓘(𝕜, E') (e ∘ f) x : E →L[𝕜] E') =
        fderivWithin 𝕜 (e ∘ f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) := by
      rw [hg.mfderiv]
      simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
        Function.id_comp]; rfl
    exact h1.trans (congrArg _ hgf)
  ext v w
  have h := inChartAtBilin_apply c b (e (f x))
    (fderivWithin 𝕜 (e ∘ f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) v)
    (fderivWithin 𝕜 (e ∘ f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) w)
  rw [e.left_inv hfc] at h
  change (b (f x) : E' →L[𝕜] E' →L[𝕜] G) ((mfderiv I I' f x : E →L[𝕜] E') v)
    ((mfderiv I I' f x : E →L[𝕜] E') w) = _
  rw [hd]
  exact h.symm.trans (ContinuousLinearMap.pullbackBilinL_apply (V := E') (W := E) (G := G) _
    (inChartAtBilin I' c b (e (f x))) v w).symm

end InChart

end TauCeti
