/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.Limit

/-!
# Finite-stage descent of line-bundle morphisms

A morphism between line bundles pulled back from one stage of a cofiltered limit
of quasi-compact quasi-separated schemes with affine transitions descends to a refinement.
This applies to arbitrary module maps, not only isomorphisms.

See the Stacks Project, Lemma 32.10.2 (Tag 01ZR), part (2).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Limits.IsLimit

open AlgebraicGeometry TauCeti.AlgebraicGeometry

local notation "PB" => InvertibleSheaf.pullback

universe u

/-- Every morphism between line bundles pulled back from stage `i` of a cofiltered limit of
qcqs schemes with affine transitions comes from a refinement `j ⟶ i`. The equality at the
limit uses the canonical comparison of the two pullbacks on the underlying modules. -/
theorem exists_pullback_map_eq_of_invertibleSheaf {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}} [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {c : Cone D} (hc : IsLimit c) {i : I} {L M : InvertibleSheaf (D.obj i)}
    (a : (PB (c.π.app i)).obj L ⟶ (PB (c.π.app i)).obj M) :
    ∃ (j : I) (f : j ⟶ i) (b : (PB (D.map f)).obj L ⟶ (PB (D.map f)).obj M),
      let e := Scheme.Modules.pullbackComp (c.π.app j) (D.map f) ≪≫
        Scheme.Modules.pullbackCongr (c.w f)
      e.inv.app L.obj ≫ ((PB (c.π.app j)).map b).hom ≫ e.hom.app M.obj = a.hom := by
  obtain ⟨j, f, b, hb⟩ := hc.exists_pullback_map_eq_of_finiteLocallyFree
    ((InvertibleSheaf.toFiniteLocallyFree _).obj L) ((InvertibleSheaf.toFiniteLocallyFree _).obj M)
    a.hom
  exact ⟨j, f, ObjectProperty.homMk b, hb⟩

end CategoryTheory.Limits.IsLimit
