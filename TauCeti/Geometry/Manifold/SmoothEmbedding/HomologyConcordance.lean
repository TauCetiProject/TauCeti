/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.HomologyCobordism
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Homology concordance of smooth embeddings

Let `f₀ : M → Y₀` and `f₁ : M → Y₁` be smooth embeddings of a boundaryless manifold `M`, modelled
on `I'`, into two manifolds modelled on `I`. They are `R`-*homology concordant* when there is an
`R`-homology cobordism `W` between `Y₀` and `Y₁` (`TauCeti.IsHomologyCobordism`) containing a
properly embedded copy of the cylinder `M × [0, 1]` whose two ends are `f₀` and `f₁`. For knots,
`M` is the circle and the cylinder is an annulus; for `Y₀ = Y₁ = S³` and the product cobordism
`S³ × [0, 1]` this is ordinary concordance, while for knots in homology spheres the cobordism may
be any homology cobordism.

The cylinder is a smooth embedding `A : M × [0, 1] → W` of manifolds with boundary, the source
modelled on `I'.prod (𝓡∂ 1)`, which is properly embedded: the preimage of the boundary of `W` is the
boundary `M × {0, 1}` of the cylinder. Its bottom is `f₀` followed by the first end of `W` and its
top is `f₁` followed by the second end (`TauCeti.SmoothEmbedding.IsHomologyConcordance`). The
relation `TauCeti.SmoothEmbedding.HomologyConcordant R J n f₀ f₁` asks for some compact Hausdorff
`W` modelled on `J` with such a cylinder.

No orientations are imposed on the cobordism, the ends, or the cylinder. Between integral homology
spheres this changes the relation only by mirroring and reversal: an integral homology cobordism
`W` has the homology of its ends, so it is connected with `H₁(W; ℤ) = 0`, hence orientable. Then
`W` and the cylinder may be oriented to induce the given orientations of `Y₀` and of `f₀`, at the
cost of reversing the orientation of `Y₁` or of `f₁`.

Every embedding of a boundaryless manifold into a compact Hausdorff boundaryless manifold is
homology concordant to itself through the cylinder over the target
(`TauCeti.SmoothEmbedding.HomologyConcordant.refl`), so the relation is not vacuous.

## Main definitions

* `TauCeti.SmoothEmbedding.IsHomologyConcordance R J n ι₀ ι₁ f₀ f₁ A`: the cylinder `A` is a
  homology concordance from `f₀` to `f₁` in the homology cobordism with ends `ι₀` and `ι₁`.
* `TauCeti.SmoothEmbedding.HomologyConcordant R J n f₀ f₁`: `f₀` and `f₁` are `R`-homology
  concordant.

## Main results

* `TauCeti.SmoothEmbedding.isHomologyConcordance_cylinder`: the product cylinder `f × id` is a
  homology concordance from `f` to itself in the cylinder over a compact boundaryless target.
* `TauCeti.SmoothEmbedding.HomologyConcordant.refl`: every embedding of a boundaryless manifold
  into a compact Hausdorff boundaryless manifold is homology concordant to itself.
* `TauCeti.SmoothEmbedding.HomologyConcordant.transDiffeomorph`: homology concordance is preserved
  by transporting the second embedding along a diffeomorphism of its target.
* `TauCeti.SmoothEmbedding.homologyConcordant_transDiffeomorph`: every embedding of a boundaryless
  manifold into a compact Hausdorff boundaryless manifold is homology concordant to its transport
  along a diffeomorphism of the target.

## References

* A. S. Levine, *Nonsurjective satellite operators and piecewise-linear concordance*, Forum Math.
  Sigma 4 (2016), e34, Remark 1.5, for homology concordance of knots in homology spheres.
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2, for knot concordance.
-/

public section

noncomputable section

open Manifold Set
open scoped Manifold ContDiff

universe u

namespace TauCeti

namespace SmoothEmbedding

variable (R : Type u) [Ring R]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) (n : ℕ∞ω)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {Y₀ Y₁ W : Type u} [TopologicalSpace Y₀] [ChartedSpace H Y₀] [TopologicalSpace Y₁]
  [ChartedSpace H Y₁] [TopologicalSpace W] [ChartedSpace G W]

/-- The map `A : M × [0, 1] → W` is an **`R`-homology concordance** from the smooth embedding
`f₀ : M → Y₀` to `f₁ : M → Y₁` in the homology cobordism `W` with ends `ι₀` and `ι₁`: it is a
properly embedded smooth cylinder, meeting the boundary of `W` exactly in its two ends, whose
bottom is `ι₀ ∘ f₀` and whose top is `ι₁ ∘ f₁`. -/
structure IsHomologyConcordance (ι₀ : SmoothEmbedding I J n Y₀ W)
    (ι₁ : SmoothEmbedding I J n Y₁ W) (f₀ : SmoothEmbedding I' I n M Y₀)
    (f₁ : SmoothEmbedding I' I n M Y₁) (A : M × Icc (0 : ℝ) 1 → W) : Prop
    extends IsHomologyCobordism R I J n ι₀ ι₁ where
  /-- The cylinder is smoothly embedded, as a manifold with boundary. -/
  isSmoothEmbedding : IsSmoothEmbedding (I'.prod (𝓡∂ 1)) J n A
  /-- The cylinder is properly embedded: it meets the boundary of `W` exactly along its own
  boundary. -/
  preimage_boundary : A ⁻¹' J.boundary W = (I'.prod (𝓡∂ 1)).boundary (M × Icc (0 : ℝ) 1)
  /-- The bottom of the cylinder is the first embedding, in the first end. -/
  apply_bot (x : M) : A (x, ⊥) = ι₀ (f₀ x)
  /-- The top of the cylinder is the second embedding, in the second end. -/
  apply_top (x : M) : A (x, ⊤) = ι₁ (f₁ x)

/-- Two smooth embeddings `f₀ : M → Y₀` and `f₁ : M → Y₁` are **`R`-homology concordant** when
some compact Hausdorff `C^n` manifold `W` modelled on `J` is an `R`-homology cobordism between `Y₀`
and `Y₁` containing a homology concordance from `f₀` to `f₁`. -/
def HomologyConcordant (f₀ : SmoothEmbedding I' I n M Y₀) (f₁ : SmoothEmbedding I' I n M Y₁) :
    Prop :=
  ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : ChartedSpace G W)
    (_ : IsManifold J n W) (ι₀ : SmoothEmbedding I J n Y₀ W) (ι₁ : SmoothEmbedding I J n Y₁ W)
    (A : M × Icc (0 : ℝ) 1 → W), IsHomologyConcordance R J n ι₀ ι₁ f₀ f₁ A

variable {R J n}

/-- Homology concordance spelled out. -/
theorem homologyConcordant_iff {f₀ : SmoothEmbedding I' I n M Y₀}
    {f₁ : SmoothEmbedding I' I n M Y₁} :
    HomologyConcordant R J n f₀ f₁ ↔
      ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : ChartedSpace G W)
        (_ : IsManifold J n W) (ι₀ : SmoothEmbedding I J n Y₀ W)
        (ι₁ : SmoothEmbedding I J n Y₁ W) (A : M × Icc (0 : ℝ) 1 → W),
        IsHomologyConcordance R J n ι₀ ι₁ f₀ f₁ A :=
  Iff.rfl

/-- A homology concordance in a Hausdorff `C^n` manifold witnesses homology concordance. -/
theorem IsHomologyConcordance.homologyConcordant [T2Space W] [IsManifold J n W]
    {ι₀ : SmoothEmbedding I J n Y₀ W} {ι₁ : SmoothEmbedding I J n Y₁ W}
    {f₀ : SmoothEmbedding I' I n M Y₀} {f₁ : SmoothEmbedding I' I n M Y₁}
    {A : M × Icc (0 : ℝ) 1 → W} (h : IsHomologyConcordance R J n ι₀ ι₁ f₀ f₁ A) :
    HomologyConcordant R J n f₀ f₁ :=
  ⟨W, _, ‹_›, _, ‹_›, ι₀, ι₁, A, h⟩

/-- **Transport of the second end.** A homology concordance from `f₀` to `f₁ : M → Y₁` is one
from `f₀` to the transport `e ∘ f₁ : M → Y₁'` along a diffeomorphism `e : Y₁ ≃ₘ Y₁'`, when the
second end of the cobordism is reparametrised to `ι₁ ∘ e⁻¹`. -/
theorem IsHomologyConcordance.transDiffeomorph {Y₁' : Type u} [TopologicalSpace Y₁']
    [ChartedSpace H Y₁'] [IsManifold I n Y₁'] {ι₀ : SmoothEmbedding I J n Y₀ W}
    {ι₁ : SmoothEmbedding I J n Y₁ W} {f₀ : SmoothEmbedding I' I n M Y₀}
    {f₁ : SmoothEmbedding I' I n M Y₁} {A : M × Icc (0 : ℝ) 1 → W}
    (h : IsHomologyConcordance R J n ι₀ ι₁ f₀ f₁ A) (e : Y₁ ≃ₘ^n⟮I, I⟯ Y₁') :
    IsHomologyConcordance R J n ι₀ (ι₁.compDiffeomorph e.symm) f₀ (f₁.transDiffeomorph e) A := by
  refine
    { h with
      disjoint_range := by
        rw [SmoothEmbedding.range_compDiffeomorph]
        exact h.disjoint_range
      range_union_range := by
        rw [SmoothEmbedding.range_compDiffeomorph]
        exact h.range_union_range
      isIso_right k := ?_
      apply_top x := by simp [h.apply_top] }
  have hcomp : (ι₁.compDiffeomorph e.symm).toContinuousMap =
      ι₁.toContinuousMap.comp (e.symm.toHomeomorph : C(Y₁', Y₁)) := by
    ext1 y
    simp
  have := h.isIso_right k
  have : CategoryTheory.IsIso (TopCat.ofHom (e.symm.toHomeomorph : C(Y₁', Y₁))) :=
    (TopCat.isoOfHomeo (X := .of Y₁') (Y := .of Y₁) e.symm.toHomeomorph).isIso_hom
  rw [hcomp, TopCat.ofHom_comp, CategoryTheory.Functor.map_comp]
  infer_instance

/-- **Homology concordance across a diffeomorphism of the second target.** If `f₀` and
`f₁ : M → Y₁` are `R`-homology concordant, then so are `f₀` and the transport `e ∘ f₁ : M → Y₁'`
along a diffeomorphism `e : Y₁ ≃ₘ Y₁'`. -/
theorem HomologyConcordant.transDiffeomorph {Y₁' : Type u} [TopologicalSpace Y₁']
    [ChartedSpace H Y₁'] [IsManifold I n Y₁'] {f₀ : SmoothEmbedding I' I n M Y₀}
    {f₁ : SmoothEmbedding I' I n M Y₁} (h : HomologyConcordant R J n f₀ f₁)
    (e : Y₁ ≃ₘ^n⟮I, I⟯ Y₁') :
    HomologyConcordant R J n f₀ (f₁.transDiffeomorph e) := by
  obtain ⟨W, _, _, _, _, ι₀, ι₁, A, h⟩ := h
  exact (h.transDiffeomorph e).homologyConcordant

/-! ### The product concordance -/

section Cylinder

variable (R) {Y : Type u} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
  [I.Boundaryless] [CompactSpace Y] [I'.Boundaryless] [IsManifold I' n M]

/-- **The product concordance.** For a smooth embedding `f : M → Y` of a boundaryless manifold into
a compact boundaryless manifold, the product cylinder `f × id : M × [0, 1] → Y × [0, 1]` is a
homology concordance from `f` to itself in the cylinder over `Y`. -/
theorem isHomologyConcordance_cylinder (f : SmoothEmbedding I' I n M Y) :
    IsHomologyConcordance R (I.prod (𝓡∂ 1)) n (SmoothEmbedding.cylinderBot I n 0 1 Y)
      (SmoothEmbedding.cylinderTop I n 0 1 Y) f f (Prod.map f _root_.id) where
  toIsHomologyCobordism := isHomologyCobordism_cylinder R
  isSmoothEmbedding := f.isSmoothEmbedding.prodMap .id
  preimage_boundary := by
    rw [boundary_product, boundary_product]
    ext ⟨x, t⟩
    simp [Set.prod]
  apply_bot x := by simp
  apply_top x := by simp

/-- **Homology concordance is reflexive.** A smooth embedding of a boundaryless manifold into a
compact Hausdorff boundaryless manifold `Y` is `R`-homology concordant to itself, through the
cylinder `Y × [0, 1]`. -/
theorem HomologyConcordant.refl [T2Space Y] (f : SmoothEmbedding I' I n M Y) :
    HomologyConcordant R (I.prod (𝓡∂ 1)) n f f :=
  (isHomologyConcordance_cylinder R f).homologyConcordant

/-- **Homology concordance across a diffeomorphism.** A smooth embedding `f : M → Y` of a
boundaryless manifold into a compact Hausdorff boundaryless manifold is `R`-homology concordant to
its transport `e ∘ f : M → Y'` along a diffeomorphism `e : Y ≃ₘ Y'`, through the cylinder
`Y × [0, 1]` with top end `y' ↦ (e⁻¹ y', 1)`. -/
theorem homologyConcordant_transDiffeomorph [T2Space Y] {Y' : Type u} [TopologicalSpace Y']
    [ChartedSpace H Y'] [IsManifold I n Y'] (f : SmoothEmbedding I' I n M Y)
    (e : Y ≃ₘ^n⟮I, I⟯ Y') :
    HomologyConcordant R (I.prod (𝓡∂ 1)) n f (f.transDiffeomorph e) :=
  (HomologyConcordant.refl R f).transDiffeomorph e

end Cylinder

end SmoothEmbedding

end TauCeti
