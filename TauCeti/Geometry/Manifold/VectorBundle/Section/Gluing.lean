/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Seminorm

/-!
# Smooth sections as closed compatible tuples of frame coordinates

For any covering family of smooth bundle trivializations, a section is determined by its
coefficient functions on the frame domains. A tuple of `C^n` coefficient functions comes from
a section exactly when it obeys the bundle transition law on every overlap. In the product
of weak Whitney map spaces these equations define a closed subspace. Thus gluing smooth
coefficient limits requires no additional derivative compatibility equations: equality of
smooth functions on the overlaps already supplies them.

`sectionFrameCoordinates` uses the existing `Bundle.Trivialization.frameCoordinates` maps.
`mem_range_sectionFrameCoordinates_iff` reconstructs the section from compatible local data;
`isClosed_range_sectionFrameCoordinates` proves closedness in the native weak Whitney topology.
These are the gluing and closed-image inputs for constructing complete smooth-section spaces.
No topology on global sections, or completeness of the coefficient spaces, is assumed here.
The results allow arbitrary regularity, boundary charts, and normed model fibres.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for the compact derivative
  topology on coefficient functions.
-/

public section

noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]

/-- The coefficient functions of a `C^n` section in a family of smooth bundle frames. -/
def sectionFrameCoordinates : Cₛ^n⟮I; F, V⟯ →ₗ[𝕜]
    ∀ i, C^n⟮I, (⟨(e i).baseSet, (e i).open_baseSet⟩ : Opens M); 𝓘(𝕜, F), F⟯ :=
  LinearMap.pi fun i ↦ (e i).frameCoordinates (U := ⟨_, (e i).open_baseSet⟩) (fun _ h ↦ h)

/-- The local coordinates of a section are its fibre component in the specified frame. -/
@[simp]
theorem sectionFrameCoordinates_apply (s : Cₛ^n⟮I; F, V⟯) (i : ι)
    (x : (⟨(e i).baseSet, (e i).open_baseSet⟩ : Opens M)) :
    sectionFrameCoordinates e s i x = (e i ⟨(x : M), s x⟩).2 :=
  Trivialization.frameCoordinates_apply _ _ _ _

/-- Coefficients on a covering family of frames determine a section uniquely. -/
theorem sectionFrameCoordinates_injective (hcover : ∀ x, ∃ i, x ∈ (e i).baseSet) :
    Function.Injective (sectionFrameCoordinates (I := I) (n := n) e) := by
  intro s t h
  ext x
  obtain ⟨i, hi⟩ := hcover x
  exact ((e i).frameCoordinates_eq_iff (U := ⟨_, (e i).open_baseSet⟩)
    (fun _ h ↦ h) s t ⟨x, hi⟩).mp (congrArg (fun f ↦ f i ⟨x, hi⟩) h)

/-- A tuple of smooth coefficient functions is the coordinates of a global smooth section
exactly when it satisfies the bundle's transition law on every overlap. -/
theorem mem_range_sectionFrameCoordinates_iff
    (hcover : ∀ x, ∃ i, x ∈ (e i).baseSet)
    (f : ∀ i, C^n⟮I, (⟨(e i).baseSet, (e i).open_baseSet⟩ : Opens M); 𝓘(𝕜, F), F⟯) :
    f ∈ LinearMap.range (sectionFrameCoordinates (I := I) e) ↔
      ∀ (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet),
        (e i).coordChangeL 𝕜 (e j) x (f i ⟨x, hi⟩) = f j ⟨x, hj⟩ := by
  constructor
  · rintro ⟨s, rfl⟩ i j x hi hj
    simp only [sectionFrameCoordinates_apply, (e i).coordChangeL_apply (e j) ⟨hi, hj⟩,
      (e i).symm_apply_apply_mk hi]
  · intro hf
    classical
    let a (x : M) : ι := (hcover x).choose
    have ha (x : M) : x ∈ (e (a x)).baseSet := (hcover x).choose_spec
    let s (x : M) : V x := (e (a x)).symm x (f (a x) ⟨x, ha x⟩)
    have hs (i : ι) (x : M) (hi : x ∈ (e i).baseSet) :
        (e i ⟨x, s x⟩).2 = f i ⟨x, hi⟩ := by
      rw [← (e (a x)).coordChangeL_apply (R := 𝕜) (e i) ⟨ha x, hi⟩]
      exact hf (a x) i x (ha x) hi
    have hsm : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) := by
      intro x
      obtain ⟨i, hi⟩ := hcover x
      apply ((e i).contMDiffAt_section_iff hi).mpr
      apply (contMDiffAt_subtype_iff (x := (⟨x, hi⟩ :
        (⟨(e i).baseSet, (e i).open_baseSet⟩ : Opens M)))).mp
      have heq : (fun y : (⟨(e i).baseSet, (e i).open_baseSet⟩ : Opens M) ↦
          (e i ⟨(y : M), s y⟩).2) = f i := funext fun y ↦ hs i y y.2
      rw [heq]
      exact (f i).contMDiff _
    refine ⟨⟨s, hsm⟩, ?_⟩
    funext i
    ext x
    rw [sectionFrameCoordinates_apply]
    exact hs i x x.2

section Closed

variable [IsManifold I n M]

open scoped TauCeti.ManifoldWeakWhitney

/-- The tuples which glue to smooth sections form a closed subspace of the product of
weak Whitney coefficient spaces. The cover need not be finite or locally finite. -/
theorem isClosed_range_sectionFrameCoordinates
    (hcover : ∀ x, ∃ i, x ∈ (e i).baseSet) :
    IsClosed (LinearMap.range (sectionFrameCoordinates (I := I) (n := n) e) :
      Set (∀ i, C^n⟮I, (⟨(e i).baseSet, (e i).open_baseSet⟩ : Opens M); 𝓘(𝕜, F), F⟯)) := by
  have heq : (LinearMap.range (sectionFrameCoordinates (I := I) (n := n) e) :
      Set (∀ i, C^n⟮I, (⟨(e i).baseSet, (e i).open_baseSet⟩ : Opens M); 𝓘(𝕜, F), F⟯)) =
      ⋂ i, ⋂ j, ⋂ x, ⋂ (hi : x ∈ (e i).baseSet), ⋂ (hj : x ∈ (e j).baseSet),
        {f | (e i).coordChangeL 𝕜 (e j) x (f i ⟨x, hi⟩) = f j ⟨x, hj⟩} := by
    ext f
    simp only [mem_iInter, mem_ofPred_eq]
    exact mem_range_sectionFrameCoordinates_iff e hcover f
  rw [heq]
  refine isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun x ↦
    isClosed_iInter fun hi ↦ isClosed_iInter fun hj ↦ ?_
  exact isClosed_eq
    (((e i).coordChangeL 𝕜 (e j) x).continuous.comp
      ((ContMDiffMap.continuous_eval_const_manifoldWeakWhitney
        (I := I) (J := 𝓘(𝕜, F)) (n := n)
        (⟨x, hi⟩ : (⟨(e i).baseSet, (e i).open_baseSet⟩ : Opens M))).comp
        (continuous_apply i)))
    ((ContMDiffMap.continuous_eval_const_manifoldWeakWhitney
      (I := I) (J := 𝓘(𝕜, F)) (n := n)
      (⟨x, hj⟩ : (⟨(e j).baseSet, (e j).open_baseSet⟩ : Opens M))).comp
      (continuous_apply j))

end Closed

end TauCeti.Manifold
