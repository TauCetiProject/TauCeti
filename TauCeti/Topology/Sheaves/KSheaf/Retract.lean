/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import TauCeti.Topology.Sheaves.KSheaf.Homotopy

/-!
# Retracts of homotopy K-sheaves

A K-presheaf `G` of cochain complexes is a retract of a K-presheaf `F` when there are morphisms of
K-presheaves `i : G ⟶ F` and `r : F ⟶ G` with `i ≫ r = 𝟙 G`. This file proves that a retract of a
homotopy K-sheaf (`TopCat.KPresheaf.IsHomotopyKSheaf`, Pardon, Definition A.2.5) is a homotopy
K-sheaf (`TopCat.KPresheaf.IsHomotopyKSheaf.of_retract`). Each of the three axioms asks that some
morphism built naturally from the K-presheaf be a quasi-isomorphism, or that a complex be acyclic,
and quasi-isomorphisms are stable under retracts (Mathlib's
`HomologicalComplex.quasiIso` is `MorphismProperty.IsStableUnderRetracts`):

* `G(∅)` is a retract of the acyclic complex `F(∅)`, so its cohomology is a retract of zero;
* the Mayer–Vietoris map `mappingCone φ ⟶ G(K₂ ∩ K₃)` of `G` is a retract of that of `F`, through
  the maps of mapping cones induced by `i` and `r`
  (`TopCat.KPresheaf.mayerVietorisDescRetractArrow`), since the Mayer–Vietoris map is natural
  (`TopCat.KPresheaf.mappingConeMap_comp_mayerVietorisDesc`);
* the map from a colimit of the `G(L)`, over the compact neighbourhoods `L` of `K`, to `G(K)` is a
  retract of the corresponding map for `F`.

The main example is the complex of invariants of a finite group acting on a homotopy K-sheaf, with
coefficients in which the order of the group is invertible: averaging over the group retracts the
complex onto its invariants. In Pardon's construction of virtual fundamental cycles, the partial
virtual complexes of an implicit atlas are of this form.

## Main results

* `TopCat.KPresheaf.mayerVietorisDescRetractArrow`: the Mayer–Vietoris map of a retract is a
  retract of the Mayer–Vietoris map.
* `TopCat.KPresheaf.IsHomotopyKSheaf.of_retract`: a retract of a homotopy K-sheaf is a homotopy
  K-sheaf.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.2, Definition A.2.5.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace HomologicalComplex CochainComplex

universe w v u

namespace TopCat.KPresheaf

variable {X : TopCat.{w}} [T2Space X] {C : Type u} [Category.{v} C] [Abelian C]
  {F G : KPresheaf (CochainComplex C ℤ) X}

/-- **The Mayer–Vietoris map of a retract is a retract.** If `G` is a retract of `F`, then for a
bicartesian square `K₁ = K₂ ⊓ K₃`, `K₄ = K₂ ⊔ K₃` of compact sets, the Mayer–Vietoris map
`mappingCone φ ⟶ G(K₁)` of `G` is a retract of that of `F`, through the maps of mapping cones
induced by the two morphisms of the retract. -/
def mayerVietorisDescRetractArrow (e : Retract G F) {K₁ K₂ K₃ K₄ : Compacts X}
    (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    RetractArrow (G.mayerVietorisDesc h) (F.mayerVietorisDesc h) where
  i := Arrow.homMk (mappingCone.map _ _ (e.i.app (op K₄))
      (biprod.map (e.i.app (op K₂)) (e.i.app (op K₃))) (by apply biprod.hom_ext <;> simp))
    (e.i.app (op K₁)) (mappingConeMap_comp_mayerVietorisDesc e.i h)
  r := Arrow.homMk (mappingCone.map _ _ (e.r.app (op K₄))
      (biprod.map (e.r.app (op K₂)) (e.r.app (op K₃))) (by apply biprod.hom_ext <;> simp))
    (e.r.app (op K₁)) (mappingConeMap_comp_mayerVietorisDesc e.r h)
  retract := by
    refine Arrow.hom_ext _ _ ?_ (Retract.retract_app e _)
    dsimp only [Arrow.comp_left, Arrow.homMk_left, Arrow.id_left, Arrow.mk_left]
    have hb : biprod.map (e.i.app (op K₂)) (e.i.app (op K₃)) ≫
        biprod.map (e.r.app (op K₂)) (e.r.app (op K₃)) = 𝟙 _ := by
      apply biprod.hom_ext <;> simp
    rw [← mappingCone.map_comp, ← mappingCone.map_id]
    simp only [Retract.retract_app, hb]

variable [HasColimitsOfSize.{w, w} C]

/-- **A retract of a homotopy K-sheaf is a homotopy K-sheaf.** If `G` is a retract of a homotopy
K-sheaf `F`, in the category of K-presheaves of cochain complexes, then `G` is a homotopy K-sheaf:
each of its axioms is a retract of the corresponding axiom of `F`. The colimits over the compact
neighbourhoods of a compact set are assumed to exist in `C`. -/
theorem IsHomotopyKSheaf.of_retract (e : Retract G F) (hF : F.IsHomotopyKSheaf) :
    G.IsHomotopyKSheaf where
  acyclic_bot n := by
    have hFn := hF.acyclic_bot n
    rw [exactAt_iff_isZero_homology] at hFn ⊢
    exact IsZero.of_mono ((e.app (op ⊥)).map (homologyFunctor C (ComplexShape.up ℤ) n)).i hFn
  quasiIso_mayerVietorisDesc h := by
    have := hF.quasiIso_mayerVietorisDesc h
    rw [← mem_quasiIso_iff] at this ⊢
    exact MorphismProperty.of_retract (mayerVietorisDescRetractArrow e h) this
  exists_isColimit_quasiIso_desc K := by
    obtain ⟨c, hc, hq⟩ := hF.exists_isColimit_quasiIso_desc K
    let D := (Set.mono_coe K.compactNhds).functor.op
    refine ⟨colimit.cocone (D ⋙ G), colimit.isColimit _, ?_⟩
    -- the map from the colimit for `G` is a retract of the map from the colimit `c` for `F`
    have hir : colimit.desc (D ⋙ G) ((Cocone.precompose (Functor.whiskerLeft D e.i)).obj c) ≫
        hc.desc ((Cocone.precompose (Functor.whiskerLeft D e.r)).obj (colimit.cocone (D ⋙ G))) =
          𝟙 _ :=
      colimit.hom_ext fun L ↦ by simp
    let ρ : RetractArrow ((colimit.isColimit (D ⋙ G)).desc (G.coconeOfCompacts K))
        (hc.desc (F.coconeOfCompacts K)) :=
      { i := Arrow.homMk (colimit.desc (D ⋙ G)
            ((Cocone.precompose (Functor.whiskerLeft D e.i)).obj c)) (e.i.app (op K))
          (colimit.hom_ext fun L ↦ by simp; rfl)
        r := Arrow.homMk (hc.desc ((Cocone.precompose (Functor.whiskerLeft D e.r)).obj
            (colimit.cocone (D ⋙ G)))) (e.r.app (op K))
          (hc.hom_ext fun L ↦ by simp; rfl)
        retract := Arrow.hom_ext _ _ hir
          (Retract.retract_app e _) }
    rw [← mem_quasiIso_iff] at hq ⊢
    exact MorphismProperty.of_retract ρ hq

end TopCat.KPresheaf
