/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Complexification

/-!
# Complexification of real Hom bundles

For a real vector bundles `V` and `L`, complexification of the real Hom bundle
is complex-linearly equivalent, on each original fibre, to complex Hom between the complexified
bundles. `bundleHomComplexificationEquiv` sends `(z ⊗ T)(w ⊗ v)` to `(z*w) ⊗ T(v)`.
Its inverse reads real and imaginary parts on the real inclusion. The comparison commutes with
conjugation and real changes of fibres, and its native bundle frames satisfy the stated
commuting square. Both coefficient models may be infinite-dimensional or incomplete.
The intrinsic algebraic map `homComplexificationLinearEquiv` has no model or frame parameters.
The fibre topological-group and scalar-continuity instances form the native Hom carrier;
they follow from `VectorBundle.isTopologicalAddGroup` and `VectorBundle.continuousSMul`.
-/

public section
noncomputable section
open Bundle FiberBundle Set TauCeti
open scoped TensorProduct TauCeti.Complexification
namespace TauCeti

variable {W D F G : Type*}
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W]
  [TopologicalSpace (ℂ ⊗[ℝ] D)] [IsComplexificationTopology D]

/-- A real fibre frame extended to the existing complexification model. -/
private def frameComplex (e : W ≃L[ℝ] F) : (ℂ ⊗[ℝ] W) ≃L[ℂ] Complexification F :=
  e.baseChangeComplex.trans (tensorContinuousLinearEquivComplexification F)

@[simp] private theorem frameComplex_tmul (e : W ≃L[ℝ] F) (z : ℂ) (v : W) :
    frameComplex e (z ⊗ₜ[ℝ] v) = ⟨z.re • e v, z.im • e v⟩ := by
  ext <;> simp [frameComplex]

variable [IsTopologicalAddGroup D] [ContinuousSMul ℝ D]
  [TopologicalSpace (ℂ ⊗[ℝ] (W →L[ℝ] D))]
  [IsComplexificationTopology (W →L[ℝ] D)]

/-- Complexifying real continuous Hom into a real target agrees with complex Hom between
the complexified original spaces. The equivalence is independent of the real frames `e`, `d`. -/
private def homComplexificationEquiv (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] G) :
    (ℂ ⊗[ℝ] (W →L[ℝ] D)) ≃L[ℂ]
      ((ℂ ⊗[ℝ] W) →L[ℂ] (ℂ ⊗[ℝ] D)) :=
  ((frameComplex (e.arrowCongr d)).trans (Complexification.continuousLinearMapEquiv F G)).trans
    ((frameComplex e).symm.arrowCongr (frameComplex d).symm)

private theorem homComplexificationEquiv_apply (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] G)
    (u : ℂ ⊗[ℝ] (W →L[ℝ] D)) :
    homComplexificationEquiv e d u = homComplexificationLinearEquiv u := by
  ext v
  apply complexification_ext <;>
    simp [homComplexificationEquiv, frameComplex]


section Topological
variable {B F G : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V L : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace G L)] [FiberBundle G L] [VectorBundle ℝ G L]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] L x)] [∀ x, IsComplexificationTopology (L x)]

variable [∀ x, IsTopologicalAddGroup (L x)] [∀ x, ContinuousSMul ℝ (L x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))]
  [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)]

private def preferredHomComplexificationEquiv (x : B) :
    (ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃L[ℂ]
      ((ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :=
  homComplexificationEquiv ((trivializationAt F V x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt F V x))
    ((trivializationAt G L x).continuousLinearEquivAt ℝ x
      (mem_baseSet_trivializationAt G L x))

/-- The intrinsic complexification comparison on the original native Hom fibre sends its real
and imaginary coefficient maps to their scalar extensions. -/
def bundleHomComplexificationEquiv (x : B) : (ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃L[ℂ]
    ((ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) := by
  let A := preferredHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x
  have hA (u) : A u = homComplexificationLinearEquiv u :=
    homComplexificationEquiv_apply _ _ u
  have hS (T) : A.symm T = homComplexificationLinearEquiv.symm T := by
    apply homComplexificationLinearEquiv.injective
    rw [← hA, A.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact
    { toLinearEquiv := homComplexificationLinearEquiv
      continuous_toFun := A.continuous.congr hA
      continuous_invFun := A.symm.continuous.congr hS }

/-- The native continuous comparison has the intrinsic algebraic comparison as its function. -/
@[simp] theorem bundleHomComplexificationEquiv_coe (x : B) :
    (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x :
      (ℂ ⊗[ℝ] (V x →L[ℝ] L x)) → ((ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) =
      homComplexificationLinearEquiv := by rfl

/-- Exact commuting square for the native frames, with no compatibility hypothesis. -/
theorem bundleHomComplexificationEquiv_in_trivializations (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] (d : Trivialization G (π G L))
    [MemTrivializationAtlas d] {x : B} (hx : x ∈ e.baseSet ∩ d.baseSet)
    (u : ℂ ⊗[ℝ] (V x →L[ℝ] L x)) :
    (e.complexification.continuousLinearMap (RingHom.id ℂ) d.complexification
      ⟨x, bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x u⟩).2 =
      Complexification.continuousLinearMapEquiv F G ((e.continuousLinearMap (RingHom.id ℝ)
        d).complexification
        ⟨x, u⟩).2 := by
  have h := homComplexificationLinearEquiv_in_frames
    (e.continuousLinearEquivAt ℝ x hx.1) (d.continuousLinearEquivAt ℝ x hx.2) u
  rw [← e.continuousLinearEquivAt_complexification hx.1,
    ← d.continuousLinearEquivAt_complexification hx.2,
    ← e.complexification.continuousLinearEquivAt_continuousLinearMap d.complexification
      (by simpa using hx)] at h
  rw [← e.continuousLinearEquivAt_continuousLinearMap d hx,
    ← (e.continuousLinearMap (RingHom.id ℝ) d).continuousLinearEquivAt_complexification
      (by simpa using hx)] at h
  simpa only [Trivialization.continuousLinearEquivAt_apply,
    bundleHomComplexificationEquiv_coe] using h

/-- The preferred native chart square. -/
theorem bundleHomComplexificationEquiv_in_trivializationAt (a x : B)
    (hx : x ∈ (trivializationAt F V a).baseSet ∩ (trivializationAt G L a).baseSet)
    (u : ℂ ⊗[ℝ] (V x →L[ℝ] L x)) :
    (trivializationAt (Complexification F →L[ℂ] Complexification G)
      (fun y ↦ (ℂ ⊗[ℝ] V y) →L[ℂ] (ℂ ⊗[ℝ] L y)) a
      ⟨x, bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x u⟩).2 =
    Complexification.continuousLinearMapEquiv F G ((trivializationAt (Complexification (F →L[ℝ] G))
      (fun y ↦ ℂ ⊗[ℝ] (V y →L[ℝ] L y)) a) ⟨x, u⟩).2 := by
  simpa only [hom_trivializationAt, trivializationAt_complexification] using
    bundleHomComplexificationEquiv_in_trivializations (G := G) (trivializationAt F V a)
      (trivializationAt
      G L a) hx u

/-- The inverse coefficient comparison has the inverse model map in native frames. -/
theorem bundleHomComplexificationEquiv_symm_in_trivializationAt (a x : B)
    (hx : x ∈ (trivializationAt F V a).baseSet ∩ (trivializationAt G L a).baseSet)
    (A : (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :
    ((trivializationAt (Complexification (F →L[ℝ] G))
      (fun y ↦ ℂ ⊗[ℝ] (V y →L[ℝ] L y)) a)
        ⟨x, (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x).symm A⟩).2 =
    (Complexification.continuousLinearMapEquiv F G).symm ((trivializationAt (Complexification F
      →L[ℂ]
      Complexification G)
      (fun y ↦ (ℂ ⊗[ℝ] V y) →L[ℂ] (ℂ ⊗[ℝ] L y)) a) ⟨x, A⟩).2 := by
  have h := bundleHomComplexificationEquiv_in_trivializationAt (G := G) a x hx
    ((bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x).symm A)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact (Complexification.continuousLinearMapEquiv F G).eq_symm_apply.mpr h.symm

/-- The same original atlas, restricted from complex to real scalars. -/
instance instVectorBundleRealComplexificationHom :
    VectorBundle ℝ (Complexification F →L[ℂ] Complexification G)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :=
  VectorBundle.restrictScalars ℝ ℂ _ _

omit [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))] in
/-- Atlas frames of complex Hom between complexifications come from real bundle frames. -/
theorem mem_trivializationAtlas_complexificationHom_iff
    {t : Trivialization (Complexification F →L[ℂ] Complexification G)
      (π (Complexification F →L[ℂ] Complexification G)
        (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)))} :
    MemTrivializationAtlas t ↔
      ∃ (e : Trivialization F (π F V)) (d : Trivialization G (π G L))
        (he : MemTrivializationAtlas e) (hd : MemTrivializationAtlas d),
        t = e.complexification.continuousLinearMap (RingHom.id ℂ) d.complexification := by
  constructor
  · rintro ⟨⟨_, ⟨e, d, he, hd, rfl⟩, rfl⟩⟩
    obtain ⟨e0, he0, rfl⟩ := mem_trivializationAtlas_complexification_iff.mp he
    obtain ⟨d0, hd0, rfl⟩ := mem_trivializationAtlas_complexification_iff.mp hd
    exact ⟨e0, d0, he0, hd0, rfl⟩
  · rintro ⟨e, d, he, hd, rfl⟩
    infer_instance

/-- Transition functions in the existing complex-Hom atlas are conjugate to those of
complexified real Hom, by the fixed native model equivalence. -/
theorem coordChangeL_complexificationHom (e e' : Trivialization F (π F V))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    (d d' : Trivialization G (π G L))
    [MemTrivializationAtlas d] [MemTrivializationAtlas d'] {x : B}
    (hx : x ∈ (e.baseSet ∩ d.baseSet) ∩ (e'.baseSet ∩ d'.baseSet)) :
    ((e.complexification.continuousLinearMap (RingHom.id ℂ) d.complexification).coordChangeL ℝ
      (e'.complexification.continuousLinearMap (RingHom.id ℂ) d'.complexification) x :
        (Complexification F →L[ℂ] Complexification G) →L[ℝ]
          (Complexification F →L[ℂ] Complexification G)) =
    ((Complexification.continuousLinearMapEquiv F G).toContinuousLinearMap.restrictScalars ℝ).comp
      (((e.continuousLinearMap (RingHom.id ℝ) d).complexification.coordChangeL ℝ
        (e'.continuousLinearMap (RingHom.id ℝ) d').complexification x :
          Complexification (F →L[ℝ] G) →L[ℝ] Complexification (F →L[ℝ] G)).comp
        ((Complexification.continuousLinearMapEquiv F
          G).symm.toContinuousLinearMap.restrictScalars ℝ))
          := by
  let t := e.complexification.continuousLinearMap (RingHom.id ℂ) d.complexification
  let t' := e'.complexification.continuousLinearMap (RingHom.id ℂ) d'.complexification
  let s := (e.continuousLinearMap (RingHom.id ℝ) d).complexification
  let s' := (e'.continuousLinearMap (RingHom.id ℝ) d').complexification
  have hxt : x ∈ t.baseSet ∩ t'.baseSet := by simpa [t, t'] using hx
  have hxs : x ∈ s.baseSet ∩ s'.baseSet := by simpa [s, s'] using hx
  apply DFunLike.ext
  intro f
  let u := (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x).symm (t.symm x f)
  have h0 := bundleHomComplexificationEquiv_in_trivializations (G := G) e d hx.1 u
  have h1 := bundleHomComplexificationEquiv_in_trivializations (G := G) e' d' hx.2 u
  have htu : bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x u = t.symm x f :=
    (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x).apply_symm_apply _
  rw [htu] at h0 h1
  have hs : (s ⟨x, u⟩).2 = (Complexification.continuousLinearMapEquiv F G).symm f := by
    apply (Complexification.continuousLinearMapEquiv F G).injective
    rw [← h0]
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      congrArg Prod.snd (t.apply_mk_symm hxt.1 f)
  have hu : u = s.symm x ((Complexification.continuousLinearMapEquiv F G).symm f) := by
    rw [← hs]
    exact (s.symm_apply_apply_mk hxs.1 u).symm
  -- The local names t and t' denote exactly these native Hom trivializations;
  -- the CLM coercion and application are definitional and have no local-name rewrite law.
  change t.coordChangeL ℝ t' x f = _
  rw [t.coordChangeL_apply t' hxt]
  rw [h1, hu]
  -- Composition of the local native transition maps evaluates by CLM.comp_apply;
  -- this reduction exposes their local abbreviations for the native coordChangeL rewrite.
  change Complexification.continuousLinearMapEquiv F G (s' ⟨x, s.symm x
    ((Complexification.continuousLinearMapEquiv
    F G).symm f)⟩).2 = _
  rw [← s.coordChangeL_apply (R := ℝ) s' hxs]
  rfl

end Topological
end TauCeti
