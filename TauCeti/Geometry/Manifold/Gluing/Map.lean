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
Descent and this equivalence require target manifolds in the same universe as the glue data,
since they use the colimit in `TopCat.{u}`. Extensionality has no target-universe restriction.
`TopCat.GlueData.IsCompatible.mapContMDiffMap` constructs maps between compatible gluings
piecewise, with identity and composition laws. Map regularity `m` may be any `m ≤ n`, where
`n` is the regularity of the compatible gluing and its piece manifolds.

No separation, countability, or nonemptiness hypothesis is needed. Taking the scalar field
to be `ℂ` gives the holomorphic universal property on exactly the same carrier and atlas.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 2,
  Corollary 2.8 (Gluing Lemma for Smooth Maps).
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
  (h : D.IsCompatible I n) {m : ℕ∞ω} (hm : m ≤ n)

private noncomputable def descContinuous
    (f : ∀ i, C^m⟮I, D.U i; I', N⟯)
    (hf : ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x))) :
    D.toGlueData.glued ⟶ TopCat.of N :=
  Multicoequalizer.desc D.toGlueData.diagram (TopCat.of N)
    (fun (i : D.J) ↦ TopCat.ofHom (X := D.U i) ⟨f i, (f i).contMDiff.continuous⟩)
    (by rintro ⟨i, j⟩; ext x; exact hf i j x)

omit [∀ ij, ChartedSpace H (D.V ij)] in
private theorem descContinuous_ι
    (f : ∀ i, C^m⟮I, D.U i; I', N⟯)
    (hf : ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x)))
    (i : D.J) (x : D.U i) :
    descContinuous f hf (D.toGlueData.ι i x) = f i x := by
  unfold descContinuous
  exact ConcreteCategory.congr_hom
    (Multicoequalizer.π_desc D.toGlueData.diagram (TopCat.of N)
      (fun (i : D.J) ↦ TopCat.ofHom (X := D.U i) ⟨f i, (f i).contMDiff.continuous⟩)
      (by rintro ⟨i, j⟩; ext x; exact hf i j x) i) x

/-- Descend smooth maps on the pieces which agree on every overlap to a map from the glued
manifold into a manifold in the same universe as `D`.
The underlying continuous map is supplied by the topological colimit. -/
noncomputable def descContMDiffMap
    (f : ∀ i, C^m⟮I, D.U i; I', N⟯)
    (hf : ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x))) :
    letI := D.chartedSpace H
    C^m⟮I, D.toGlueData.glued; I', N⟯ := by
  letI := D.chartedSpace H
  refine ⟨descContinuous f hf, (h.contMDiff_iff hm).mpr fun i ↦ ?_⟩
  have heq : descContinuous f hf ∘ D.toGlueData.ι i = f i :=
    funext (descContinuous_ι f hf i)
  rw [heq]
  exact (f i).contMDiff

/-- Descent recovers the prescribed map on each piece. -/
@[simp]
theorem descContMDiffMap_ι
    (f : ∀ i, C^m⟮I, D.U i; I', N⟯)
    (hf : ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x)))
    (i : D.J) (x : D.U i) :
    h.descContMDiffMap hm f hf (D.toGlueData.ι i x) = f i x := by
  -- The bundled constructor retains descContinuous as its underlying function.
  exact descContinuous_ι f hf i x

/-- The smooth universal property of compatible open gluing: smooth maps from the glued
manifold into a manifold in the same universe as `D` are equivalent to smooth maps on the
pieces agreeing on overlaps. -/
noncomputable def contMDiffMapEquiv :
    letI := D.chartedSpace H
    C^m⟮I, D.toGlueData.glued; I', N⟯ ≃
      {f : ∀ i, C^m⟮I, D.U i; I', N⟯ //
        ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x))} := by
  letI := D.chartedSpace H
  exact
    { toFun := fun g ↦ ⟨fun i ↦ ⟨g ∘ D.toGlueData.ι i,
        g.contMDiff.comp ((h.contMDiff_ι i).of_le hm)⟩, fun i j x ↦
          congrArg g (D.glue_condition_apply i j x).symm⟩
      invFun := fun f ↦ h.descContMDiffMap hm f.1 f.2
      left_inv := fun g ↦ D.contMDiffMap_ext fun i x ↦ h.descContMDiffMap_ι hm _ _ i x
      right_inv := fun f ↦ by
        apply Subtype.ext
        funext i
        ext x
        exact h.descContMDiffMap_ι hm f.1 f.2 i x }

/-- The forward universal-property equivalence restricts a map to each piece. -/
@[simp]
theorem contMDiffMapEquiv_apply :
    letI := D.chartedSpace H
    ∀ (g : C^m⟮I, D.toGlueData.glued; I', N⟯) (i : D.J) (x : D.U i),
      (h.contMDiffMapEquiv hm g).1 i x = g (D.toGlueData.ι i x) := by
  intros
  rfl

/-- The inverse universal-property equivalence evaluates to the prescribed map on a piece. -/
@[simp]
theorem contMDiffMapEquiv_symm_apply_ι
    (f : {f : ∀ i, C^m⟮I, D.U i; I', N⟯ //
      ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x))})
    (i : D.J) (x : D.U i) :
    (h.contMDiffMapEquiv hm).symm f (D.toGlueData.ι i x) = f.1 i x :=
  h.descContMDiffMap_ι hm f.1 f.2 i x

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {P : Type u} [TopologicalSpace P] [ChartedSpace H'' P]

/-- Descent is natural in the target: postcomposing the descended map is the same as
postcomposing all its piece maps and then descending. Both targets lie in the same universe
as `D`. -/
@[simp]
theorem comp_descContMDiffMap (g : C^m⟮I', N; I'', P⟯)
    (f : ∀ i, C^m⟮I, D.U i; I', N⟯)
    (hf : ∀ i j (x : D.V (i, j)), f i (D.f i j x) = f j (D.f j i (D.t i j x))) :
    letI := D.chartedSpace H
    g.comp (h.descContMDiffMap hm f hf) =
      h.descContMDiffMap hm (fun i ↦ g.comp (f i))
        (fun i j x ↦ congrArg g (hf i j x)) := by
  let := D.chartedSpace H
  apply D.contMDiffMap_ext
  intro i x
  rw [h.descContMDiffMap_ι hm (fun i ↦ g.comp (f i))
    (fun i j x ↦ congrArg g (hf i j x)) i x]
  simp

section Maps

variable {D' : TopCat.GlueData.{u}} [∀ i, ChartedSpace H' (D'.U i)]
  [∀ ij, ChartedSpace H' (D'.V ij)] [∀ i, IsManifold I' n (D'.U i)]
  (h' : D'.IsCompatible I' n)

/-- A family of smooth maps into pieces of another compatible gluing induces a smooth map
of glued manifolds, provided the images of identified points are identified. The index map
need not be injective or surjective. -/
noncomputable def mapContMDiffMap (a : D.J → D'.J)
    (f : ∀ i, C^m⟮I, D.U i; I', D'.U (a i)⟯)
    (hf : ∀ i j (x : D.V (i, j)),
      D'.toGlueData.ι (a i) (f i (D.f i j x)) =
        D'.toGlueData.ι (a j) (f j (D.f j i (D.t i j x)))) :
    letI := D.chartedSpace H
    letI := D'.chartedSpace H'
    C^m⟮I, D.toGlueData.glued; I', D'.toGlueData.glued⟯ := by
  letI := D'.chartedSpace H'
  exact h.descContMDiffMap hm
    (fun i ↦ ⟨D'.toGlueData.ι (a i) ∘ f i,
      ((h'.contMDiff_ι (a i)).of_le hm).comp (f i).contMDiff⟩) hf

/-- The map induced between gluings has the prescribed value on each piece. -/
@[simp]
theorem mapContMDiffMap_ι (a : D.J → D'.J)
    (f : ∀ i, C^m⟮I, D.U i; I', D'.U (a i)⟯)
    (hf : ∀ i j (x : D.V (i, j)),
      D'.toGlueData.ι (a i) (f i (D.f i j x)) =
        D'.toGlueData.ι (a j) (f j (D.f j i (D.t i j x))))
    (i : D.J) (x : D.U i) :
    h.mapContMDiffMap hm h' a f hf (D.toGlueData.ι i x) = D'.toGlueData.ι (a i) (f i x) := by
  let := D'.chartedSpace H'
  -- By definition, mapContMDiffMap descends the maps ι (a i) ∘ f i;
  -- the bundled constructors coerce to these functions, evaluated as ι (a i) (f i x).
  exact h.descContMDiffMap_ι hm _ hf i x

/-- Identity piece maps induce the identity map of the glued manifold. -/
@[simp]
theorem mapContMDiffMap_id :
    h.mapContMDiffMap hm h id (fun i ↦ ContMDiffMap.id (I := I) (M := D.U i))
      (fun i j x ↦ (D.glue_condition_apply i j x).symm) =
        (letI := D.chartedSpace H; ContMDiffMap.id (I := I) (M := D.toGlueData.glued)) := by
  let := D.chartedSpace H
  apply D.contMDiffMap_ext
  intro i x
  exact h.mapContMDiffMap_ι hm h _ _ _ i x

variable {D'' : TopCat.GlueData.{u}} [∀ i, ChartedSpace H'' (D''.U i)]
  [∀ ij, ChartedSpace H'' (D''.V ij)] [∀ i, IsManifold I'' n (D''.U i)]

include hm h' in
omit [∀ ij, ChartedSpace H (D.V ij)] [∀ i, IsManifold I n (D.U i)] in
/-- Composing two families of piece maps preserves agreement of their images on overlaps. -/
theorem mapContMDiffMap_comp_compatible (h'' : D''.IsCompatible I'' n)
    (a : D.J → D'.J) (b : D'.J → D''.J)
    (f : ∀ i, C^m⟮I, D.U i; I', D'.U (a i)⟯)
    (g : ∀ j, C^m⟮I', D'.U j; I'', D''.U (b j)⟯)
    (hf : ∀ i j (x : D.V (i, j)),
      D'.toGlueData.ι (a i) (f i (D.f i j x)) =
        D'.toGlueData.ι (a j) (f j (D.f j i (D.t i j x))))
    (hg : ∀ i j (x : D'.V (i, j)),
      D''.toGlueData.ι (b i) (g i (D'.f i j x)) =
        D''.toGlueData.ι (b j) (g j (D'.f j i (D'.t i j x))))
    (i j : D.J) (x : D.V (i, j)) :
    D''.toGlueData.ι (b (a i)) (g (a i) (f i (D.f i j x))) =
      D''.toGlueData.ι (b (a j)) (g (a j) (f j (D.f j i (D.t i j x)))) := by
  let := D'.chartedSpace H'
  let := D''.chartedSpace H''
  have heq := congrArg (h'.mapContMDiffMap hm h'' b g hg) (hf i j x)
  simpa only [mapContMDiffMap_ι] using heq

/-- Composition of piece maps induces composition on the glued manifolds. The overlap
condition on the composite follows from those of the two families. -/
@[simp]
theorem mapContMDiffMap_comp (h'' : D''.IsCompatible I'' n)
    (a : D.J → D'.J) (b : D'.J → D''.J)
    (f : ∀ i, C^m⟮I, D.U i; I', D'.U (a i)⟯)
    (g : ∀ j, C^m⟮I', D'.U j; I'', D''.U (b j)⟯)
    (hf : ∀ i j (x : D.V (i, j)),
      D'.toGlueData.ι (a i) (f i (D.f i j x)) =
        D'.toGlueData.ι (a j) (f j (D.f j i (D.t i j x))))
    (hg : ∀ i j (x : D'.V (i, j)),
      D''.toGlueData.ι (b i) (g i (D'.f i j x)) =
        D''.toGlueData.ι (b j) (g j (D'.f j i (D'.t i j x)))) :
    letI := D.chartedSpace H
    letI := D'.chartedSpace H'
    letI := D''.chartedSpace H''
    (h'.mapContMDiffMap hm h'' b g hg).comp (h.mapContMDiffMap hm h' a f hf) =
      h.mapContMDiffMap hm h'' (b ∘ a) (fun i ↦ (g (a i)).comp (f i))
        (mapContMDiffMap_comp_compatible hm h' h'' a b f g hf hg) := by
  let := D.chartedSpace H
  let := D'.chartedSpace H'
  let := D''.chartedSpace H''
  apply D.contMDiffMap_ext
  intro i x
  rw [h.mapContMDiffMap_ι hm h'' (b ∘ a) (fun i ↦ (g (a i)).comp (f i))
    (mapContMDiffMap_comp_compatible hm h' h'' a b f g hf hg) i x]
  simp only [ContMDiffMap.comp_apply, mapContMDiffMap_ι, Function.comp_apply]

end Maps

end IsCompatible

end TopCat.GlueData
