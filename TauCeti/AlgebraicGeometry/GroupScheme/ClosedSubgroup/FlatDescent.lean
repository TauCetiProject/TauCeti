/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Map

/-!
# Descent of closed subgroup schemes along flat surjective morphisms

Let `g : G' ⟶ G` be a morphism of group schemes lying over a flat surjective `f : S' ⟶ S`, such
that the square formed by `g`, `f` and the structure morphisms is a pullback square and `g` is
compatible with the identity, multiplication and inversion. Then a closed subscheme `V(D)` of `G`
is a subgroup scheme exactly when its inverse image in `G'` is a subgroup scheme
(`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective`).

No finiteness or flatness hypothesis is placed on `V(D)`, and `f` need not be quasi-compact, so
this is not an instance of effective fpqc descent. Each of the three conditions of the
closed-subgroup criterion (`TauCeti.GroupScheme.exists_grpObj_isMonHom_iff_ker_le`) says that a
family of points lies in `V(D)`, and the parameter scheme of the family changes by a flat
surjective base change. Flat surjective morphisms are scheme-theoretically dominant
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_flat_of_surjective`), so precomposition with
them does not change kernels. This makes reversible the closure checks in the base-change
argument for elliptic curves,
`TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_grpObj_isMonHom_comap`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.3.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Scheme.IdealSheafData
open scoped MonObj

namespace TauCeti.GroupScheme

universe u

variable {S S' : Scheme.{u}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
  {g : G'.left ⟶ G.left}

/-- **Subgroup schemes descend along flat surjective morphisms.** Let `g : G' ⟶ G` be a morphism
of group schemes lying over a flat surjective `f : S' ⟶ S`, forming a pullback square with the
structure morphisms and compatible with the identity, multiplication and inversion, and let
`V(D) ⊆ G` be a closed subscheme. Then `V(D)` is a subgroup scheme of `G` exactly when its inverse
image in `G'` is a subgroup scheme of `G'`. -/
theorem exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective [Flat f] [Surjective f]
    (hg : IsPullback g G'.hom G.hom f) (hη : η[G'].left ≫ g = f ≫ η[G].left)
    (hμ : μ[G'].left ≫ g = pullback.map _ _ _ _ g g f hg.w.symm hg.w.symm ≫ μ[G].left)
    (hι : ι[G'].left ≫ g = g ≫ ι[G].left) (D : G.left.IdealSheafData) :
    (∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ G'.hom)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ G'.hom) ⟶ G')) ↔
      ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ G.hom)),
        IsMonHom (Over.homMk D.subschemeι : Over.mk (D.subschemeι ≫ G.hom) ⟶ G) := by
  let i' : Over.mk ((D.comap g).subschemeι ≫ G'.hom) ⟶ G' := Over.homMk (D.comap g).subschemeι
  let i : Over.mk (D.subschemeι ≫ G.hom) ⟶ G := Over.homMk D.subschemeι
  have hi' : i'.left = (D.comap g).subschemeι := Over.homMk_left _ _
  have hi : i.left = D.subschemeι := Over.homMk_left _ _
  have : IsClosedImmersion i'.left := by rw [hi']; infer_instance
  have : IsClosedImmersion i.left := by rw [hi]; infer_instance
  -- `ρ : V(D.comap g) ⟶ V(D)` is the base change of `V(D)` along `f`
  let ρ := subschemeMap (D.comap g) D g (D.le_map_comap g)
  have hρ : ρ ≫ D.subschemeι = (D.comap g).subschemeι ≫ g := subschemeMap_subschemeι _ _ _ _
  have hD := D.isPullback_subschemeMap_comap G.hom hg
  rw [exists_grpObj_isMonHom_iff_ker_le i', exists_grpObj_isMonHom_iff_ker_le i, hi', hi,
    ker_subschemeι, ker_subschemeι]
  simp only [i', i, Over.comp_left, Over.homMk_left, Over.tensorHom_left, Over.tensorObj_left,
    Over.mk_hom]
  -- Each condition says that a family lies in `V(D)`; such a condition descends along a flat
  -- surjective base change of its parameter scheme, since that change is scheme-theoretically
  -- dominant.
  have key {X' X : Scheme.{u}} (p : X' ⟶ X) [IsSchemeTheoreticallyDominant p]
      {φ' : X' ⟶ G'.left} {φ : X ⟶ G.left} (w : φ' ≫ g = p ≫ φ) :
      D.comap g ≤ φ'.ker ↔ D ≤ φ.ker := by
    rw [← le_map_iff_comap_le, map_ker, w, p.ker_comp_of_isSchemeTheoreticallyDominant]
  refine and_congr (key f hη) (and_congr ?_ ?_)
  · -- sums of two points of `V(D)` lie in `V(D)`
    have hDD := hD.flip.pullback_map hD.flip
    have : Flat (pullback.map _ _ _ _ ρ ρ f hD.flip.w hD.flip.w) :=
      MorphismProperty.of_isPullback hDD ‹_›
    have : Surjective (pullback.map _ _ _ _ ρ ρ f hD.flip.w hD.flip.w) :=
      MorphismProperty.of_isPullback hDD ‹_›
    refine key (pullback.map _ _ _ _ ρ ρ f hD.flip.w hD.flip.w) ?_
    rw [Category.assoc, hμ, ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [hρ]
  · -- negatives of points of `V(D)` lie in `V(D)`
    have : Flat ρ := MorphismProperty.of_isPullback hD.flip ‹_›
    have : Surjective ρ := MorphismProperty.of_isPullback hD.flip ‹_›
    refine key ρ ?_
    rw [Category.assoc, hι, reassoc_of% hρ]

end TauCeti.GroupScheme
