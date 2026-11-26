/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.BaseChange
public import TauCeti.AlgebraicGeometry.Limits.GrpObj

/-!
# Spreading out closed subgroup schemes along cofiltered limits

Let `S = lim Dⱼ` be the limit of a cofiltered diagram of quasi-compact quasi-separated schemes with
affine transition maps, let `G` be a group scheme locally of finite type over a member `Dᵢ`, and let
`V(Z) ⊆ G` be a closed subscheme which is of finite presentation, quasi-compact and quasi-separated
over `Dᵢ`. Whether the inverse image of `V(Z)` in a base change of `G` is a subgroup scheme is a
scheme-theoretic condition, not a condition on points. This file shows that it spreads out: if the
inverse image of `V(Z)` in `G ×_{Dᵢ} S` is a subgroup scheme, then so is its inverse image in
`G ×_{Dᵢ} Dⱼ` for some `Dⱼ`.

The inverse image of `V(Z)` in a base change of `G` is the base change of `V(Z)`
(`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_pullback_fst_iff`), so the statement is the case
of the inclusion `V(Z) ⟶ G` in the spreading out of homomorphisms
(`CategoryTheory.Limits.IsLimit.exists_grpObj_isMonHom_overPullback`). It applies to the divisors
of points of an elliptic curve which define its level structures, for instance to the divisor
`[P] + [2P] + ⋯ + [NP]`, which is a subgroup scheme exactly when `P` has exact order `N`.

## Main results

* `CategoryTheory.Limits.IsLimit.exists_grpObj_isMonHom_comap`: a closed subscheme of finite
  presentation of a group scheme over `Dᵢ` whose inverse image in the base change to `S` is a
  subgroup scheme has a subgroup scheme as inverse image in the base change to some `Dⱼ`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Troisième partie, §8.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.3.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Obj

namespace CategoryTheory.Limits.IsLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- **Spreading out closed subgroup schemes.** Let `S = lim Dⱼ` be a cofiltered limit of
quasi-compact quasi-separated schemes with affine transition maps, let `G` be a monoid object, such
as a group scheme, locally of finite type over a member `Dᵢ`, and let `V(Z)` be a closed subscheme
of `G` which is of finite presentation, quasi-compact and quasi-separated over `Dᵢ`. If the inverse
image of `V(Z)` in the base change `G ×_{Dᵢ} S` is a subgroup scheme, then so is its inverse image
in `G ×_{Dᵢ} Dⱼ` for some `Dⱼ`. -/
theorem exists_grpObj_isMonHom_comap {i : I} {G : Over (D.obj i)} [MonObj G]
    [LocallyOfFiniteType G.hom] (Z : G.left.IdealSheafData)
    [LocallyOfFinitePresentation (Z.subschemeι ≫ G.hom)] [QuasiCompact (Z.subschemeι ≫ G.hom)]
    [QuasiSeparated (Z.subschemeι ≫ G.hom)]
    (h : ∃ _ : GrpObj (Over.mk ((Z.comap (pullback.fst G.hom (c.π.app i))).subschemeι ≫
        ((Over.pullback (c.π.app i)).obj G).hom)),
      IsMonHom (Over.homMk (Z.comap (pullback.fst G.hom (c.π.app i))).subschemeι :
        Over.mk ((Z.comap (pullback.fst G.hom (c.π.app i))).subschemeι ≫
          ((Over.pullback (c.π.app i)).obj G).hom) ⟶ (Over.pullback (c.π.app i)).obj G)) :
    ∃ (j : I) (g : j ⟶ i),
      ∃ _ : GrpObj (Over.mk ((Z.comap (pullback.fst G.hom (D.map g))).subschemeι ≫
          ((Over.pullback (D.map g)).obj G).hom)),
        IsMonHom (Over.homMk (Z.comap (pullback.fst G.hom (D.map g))).subschemeι :
          Over.mk ((Z.comap (pullback.fst G.hom (D.map g))).subschemeι ≫
            ((Over.pullback (D.map g)).obj G).hom) ⟶ (Over.pullback (D.map g)).obj G) := by
  obtain ⟨_, _⟩ := (TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_pullback_fst_iff Z
    (c.π.app i)).mp h
  -- The finiteness hypotheses, restated for the closed subscheme as an object over `Dᵢ`.
  have : LocallyOfFinitePresentation (Over.mk (Z.subschemeι ≫ G.hom)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (Z.subschemeι ≫ G.hom))
  have : QuasiCompact (Over.mk (Z.subschemeι ≫ G.hom)).hom :=
    inferInstanceAs (QuasiCompact (Z.subschemeι ≫ G.hom))
  have : QuasiSeparated (Over.mk (Z.subschemeι ≫ G.hom)).hom :=
    inferInstanceAs (QuasiSeparated (Z.subschemeι ≫ G.hom))
  obtain ⟨j, g, _, hg, -⟩ := hc.exists_grpObj_isMonHom_overPullback
    (Over.homMk Z.subschemeι rfl : Over.mk (Z.subschemeι ≫ G.hom) ⟶ G)
  exact ⟨j, g, (TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_pullback_fst_iff Z
    (D.map g)).mpr ⟨_, hg⟩⟩

end CategoryTheory.Limits.IsLimit
