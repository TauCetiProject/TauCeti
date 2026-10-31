/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Gluing.GlueData
public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Smooth maps out of an open gluing

A compatible family of smooth maps on the pieces of `TopCat.GlueData` descends uniquely to a
smooth map on its glued manifold. `TopCat.GlueData.IsCompatible.descContMDiffMap` uses the
existing topological colimit, not a new quotient or a choice of representatives.
`TopCat.GlueData.IsCompatible.contMDiffMapEquiv` expresses its universal property as an
equivalence with families agreeing on the overlaps. Descent commutes with postcomposition.
`TopCat.GlueData.IsCompatible.mapContMDiff` constructs maps between compatible gluings
piecewise, with identity and composition laws.

No separation, countability, or nonemptiness hypothesis is needed. Taking the scalar field
to be `ℂ` gives the holomorphic universal property on exactly the same carrier and atlas.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 1, for smooth
  maps defined on an open cover.
* The topological descent is Mathlib's `CategoryTheory.Limits.Multicoequalizer.desc`.
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped Manifold ContDiff

namespace TopCat.GlueData

universe u

variable {D : TopCat.GlueData.{u}} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}

/-- Smooth maps on a glued space are determined by their values on all pieces. -/
@[ext]
theorem contMDiffMap_ext (D : TopCat.GlueData.{u}) [ChartedSpace H D.toGlueData.glued]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {f g : C^n⟮I, D.toGlueData.glued; I', N⟯}
    (hfg : ∀ i (x : D.U i), f (D.toGlueData.ι i x) = g (D.toGlueData.ι i x)) : f = g := by
  ext x
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  exact hfg i y

namespace IsCompatible

variable [∀ i, ChartedSpace H (D.U i)] [∀ ij, ChartedSpace H (D.V ij)]
  [∀ i, IsManifold I n (D.U i)]
  {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  (h : D.IsCompatible I n)

/-- Descend smooth maps on the pieces which agree on every overlap to the glued manifold.
The underlying continuous map is supplied by the topological colimit. -/
noncomputable def descContMDiffMap
    (f : ∀ i, C^n⟮I, D.U i; I', N⟯)
    (hf : ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x))) :
    letI := D.chartedSpace H
    C^n⟮I, D.toGlueData.glued; I', N⟯ := by
  letI := D.chartedSpace H
  let F : D.toGlueData.glued ⟶ TopCat.of N :=
    Multicoequalizer.desc D.toGlueData.diagram (TopCat.of N)
      (fun (i : D.J) ↦ TopCat.ofHom (X := D.U i) ⟨f i, (f i).contMDiff.continuous⟩)
      (by rintro ⟨i, j⟩; ext x; exact hf i j x)
  refine ⟨F, (h.contMDiff_iff le_rfl).mpr fun i ↦ ?_⟩
  have hi := Multicoequalizer.π_desc D.toGlueData.diagram (TopCat.of N)
    (fun (i : D.J) ↦ TopCat.ofHom (X := D.U i) ⟨f i, (f i).contMDiff.continuous⟩)
    (by rintro ⟨i, j⟩; ext x; exact hf i j x) i
  have heq : F ∘ D.toGlueData.ι i = f i := funext (ConcreteCategory.congr_hom hi)
  rw [heq]
  exact (f i).contMDiff

/-- Descent recovers the prescribed map on each piece. -/
@[simp]
theorem descContMDiffMap_ι
    (f : ∀ i, C^n⟮I, D.U i; I', N⟯)
    (hf : ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x)))
    (i : D.J) (x : D.U i) :
    h.descContMDiffMap f hf (D.toGlueData.ι i x) = f i x := by
  exact ConcreteCategory.congr_hom
    (Multicoequalizer.π_desc D.toGlueData.diagram (TopCat.of N)
      (fun (i : D.J) ↦ TopCat.ofHom (X := D.U i) ⟨f i, (f i).contMDiff.continuous⟩)
      (by rintro ⟨i, j⟩; ext x; exact hf i j x) i) x

/-- The smooth universal property of compatible open gluing: smooth maps on the glued
manifold are equivalent to smooth maps on the pieces agreeing on overlaps. -/
noncomputable def contMDiffMapEquiv :
    letI := D.chartedSpace H
    C^n⟮I, D.toGlueData.glued; I', N⟯ ≃
      {f : ∀ i, C^n⟮I, D.U i; I', N⟯ //
        ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x))} := by
  letI := D.chartedSpace H
  exact
    { toFun := fun g ↦ ⟨fun i ↦ ⟨g ∘ D.toGlueData.ι i,
        g.contMDiff.comp (h.contMDiff_ι i)⟩, fun i j x ↦
          congrArg g (D.glue_condition_apply i j x).symm⟩
      invFun := fun f ↦ h.descContMDiffMap f.1 f.2
      left_inv := fun g ↦ D.contMDiffMap_ext fun i x ↦ h.descContMDiffMap_ι _ _ i x
      right_inv := fun f ↦ by
        apply Subtype.ext
        funext i
        ext x
        exact h.descContMDiffMap_ι f.1 f.2 i x }

/-- The forward universal-property equivalence restricts a map to each piece. -/
@[simp]
theorem contMDiffMapEquiv_apply :
    letI := D.chartedSpace H
    ∀ (g : C^n⟮I, D.toGlueData.glued; I', N⟯) (i : D.J) (x : D.U i),
      (h.contMDiffMapEquiv g).1 i x = g (D.toGlueData.ι i x) := by
  intros
  rfl

/-- The inverse universal-property equivalence evaluates to the prescribed map on a piece. -/
@[simp]
theorem contMDiffMapEquiv_symm_apply_ι
    (f : {f : ∀ i, C^n⟮I, D.U i; I', N⟯ //
      ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x))})
    (i : D.J) (x : D.U i) :
    h.contMDiffMapEquiv.symm f (D.toGlueData.ι i x) = f.1 i x :=
  h.descContMDiffMap_ι f.1 f.2 i x

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {P : Type u} [TopologicalSpace P] [ChartedSpace H'' P]

/-- Descent is natural in the target: postcomposing the descended map is the same as
postcomposing all its piece maps and then descending. -/
@[simp]
theorem comp_descContMDiffMap (g : C^n⟮I', N; I'', P⟯)
    (f : ∀ i, C^n⟮I, D.U i; I', N⟯)
    (hf : ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x))) :
    letI := D.chartedSpace H
    g.comp (h.descContMDiffMap f hf) =
      h.descContMDiffMap (fun i ↦ g.comp (f i))
        (fun i j x ↦ congrArg g (hf i j x)) := by
  let := D.chartedSpace H
  apply D.contMDiffMap_ext
  intro i x
  rw [h.descContMDiffMap_ι (fun i ↦ g.comp (f i))
    (fun i j x ↦ congrArg g (hf i j x)) i x]
  simp

section Maps

variable {D' : TopCat.GlueData.{u}} [∀ i, ChartedSpace H' (D'.U i)]
  [∀ ij, ChartedSpace H' (D'.V ij)] [∀ i, IsManifold I' n (D'.U i)]
  (h' : D'.IsCompatible I' n)

/-- A family of smooth maps into pieces of another compatible gluing induces a smooth map
of glued manifolds, provided the images of identified points are identified. The index map
need not be injective or surjective. -/
noncomputable def mapContMDiff (a : D.J → D'.J)
    (f : ∀ i, C^n⟮I, D.U i; I', D'.U (a i)⟯)
    (hf : ∀ i j (x : D.V (i, j)),
      D'.toGlueData.ι (a i) (f i (D.f i j x)) =
        D'.toGlueData.ι (a j) (f j (D.f j i (D.t i j x)))) :
    letI := D.chartedSpace H
    letI := D'.chartedSpace H'
    C^n⟮I, D.toGlueData.glued; I', D'.toGlueData.glued⟯ := by
  letI := D'.chartedSpace H'
  exact h.descContMDiffMap
    (fun i ↦ ⟨D'.toGlueData.ι (a i) ∘ f i,
      (h'.contMDiff_ι (a i)).comp (f i).contMDiff⟩) hf

/-- The map induced between gluings has the prescribed value on each piece. -/
@[simp]
theorem mapContMDiff_ι (a : D.J → D'.J)
    (f : ∀ i, C^n⟮I, D.U i; I', D'.U (a i)⟯)
    (hf : ∀ i j (x : D.V (i, j)),
      D'.toGlueData.ι (a i) (f i (D.f i j x)) =
        D'.toGlueData.ι (a j) (f j (D.f j i (D.t i j x))))
    (i : D.J) (x : D.U i) :
    h.mapContMDiff h' a f hf (D.toGlueData.ι i x) = D'.toGlueData.ι (a i) (f i x) := by
  let := D'.chartedSpace H'
  exact h.descContMDiffMap_ι _ hf i x

/-- Identity piece maps induce the identity map of the glued manifold. -/
@[simp]
theorem mapContMDiff_id :
    h.mapContMDiff h id (fun i ↦ ContMDiffMap.id (I := I) (M := D.U i))
      (fun i j x ↦ (D.glue_condition_apply i j x).symm) =
        (letI := D.chartedSpace H; ContMDiffMap.id (I := I) (M := D.toGlueData.glued)) := by
  let := D.chartedSpace H
  apply D.contMDiffMap_ext
  intro i x
  exact h.mapContMDiff_ι h _ _ _ i x

variable {D'' : TopCat.GlueData.{u}} [∀ i, ChartedSpace H'' (D''.U i)]
  [∀ ij, ChartedSpace H'' (D''.V ij)] [∀ i, IsManifold I'' n (D''.U i)]

/-- Composition of piece maps induces composition on the glued manifolds. The overlap
condition on the composite follows from those of the two families. -/
@[simp]
theorem mapContMDiff_comp (h'' : D''.IsCompatible I'' n)
    (a : D.J → D'.J) (b : D'.J → D''.J)
    (f : ∀ i, C^n⟮I, D.U i; I', D'.U (a i)⟯)
    (g : ∀ j, C^n⟮I', D'.U j; I'', D''.U (b j)⟯)
    (hf : ∀ i j (x : D.V (i, j)),
      D'.toGlueData.ι (a i) (f i (D.f i j x)) =
        D'.toGlueData.ι (a j) (f j (D.f j i (D.t i j x))))
    (hg : ∀ i j (x : D'.V (i, j)),
      D''.toGlueData.ι (b i) (g i (D'.f i j x)) =
        D''.toGlueData.ι (b j) (g j (D'.f j i (D'.t i j x)))) :
    letI := D.chartedSpace H
    letI := D'.chartedSpace H'
    letI := D''.chartedSpace H''
    (h'.mapContMDiff h'' b g hg).comp (h.mapContMDiff h' a f hf) =
      h.mapContMDiff h'' (b ∘ a) (fun i ↦ (g (a i)).comp (f i))
        (fun i j x ↦ by
          have heq := congrArg (h'.mapContMDiff h'' b g hg) (hf i j x)
          simpa only [mapContMDiff_ι, ContMDiffMap.comp_apply, Function.comp_apply] using heq) := by
  let := D.chartedSpace H
  let := D'.chartedSpace H'
  let := D''.chartedSpace H''
  apply D.contMDiffMap_ext
  intro i x
  simp only [ContMDiffMap.comp_apply, mapContMDiff_ι, Function.comp_apply]

end Maps

end IsCompatible

end TopCat.GlueData
