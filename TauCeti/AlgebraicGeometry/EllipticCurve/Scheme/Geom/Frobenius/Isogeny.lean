/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.CommGrp
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Isogeny
public import TauCeti.AlgebraicGeometry.Frobenius.Smooth
public import TauCeti.AlgebraicGeometry.Frobenius.UniversalHomeomorphism
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank

/-!
# Frobenius and Verschiebung for elliptic curves over a scheme

Over any scheme of characteristic `p`, relative Frobenius is an isogeny of degree `p`
from an elliptic curve to its Frobenius twist. Its factorisation dual is Verschiebung.
Both composites are multiplication by `p`, on their respective source curves.
These are scheme-theoretic identities, including over nonreduced bases.

The target of Frobenius is the canonical elliptic base change, rather than just the
pullback of an abstract group object. No perfectness assumption on the base is made.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.8.
* The Stacks Project, Tag 0CC6, for the rank of relative Frobenius of a smooth morphism.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) (p : ℕ) [Fact p.Prime]
  (hS : (p : Γ(S, ⊤)) = 0)

/-- Relative Frobenius, as a homomorphism to the canonical Frobenius-twisted elliptic curve. -/
noncomputable def relativeFrobenius :
    E.toCommGrp ⟶ (E.baseChange (S.frobenius p hS)).toCommGrp :=
  S.relativeFrobeniusCommGrpHom p hS E.toCommGrp ≫
    (E.baseChangeCommGrpIso (S.frobenius p hS)).inv

/-- The underlying map of relative Frobenius is the usual relative Frobenius followed by the
comparison with the canonical elliptic base change. -/
theorem relativeFrobenius_left :
    (E.relativeFrobenius p hS).hom.hom.hom.left =
      E.structureMap.relativeFrobenius p hS ≫ (E.baseChangeIso (S.frobenius p hS)).inv := by
  -- The forgetful maps of the group-object categories project out the composite.
  simp [relativeFrobenius]
  rfl

/-- The elliptic relative Frobenius agrees with the scheme relative Frobenius through the
canonical base-change comparison. -/
@[reassoc (attr := simp)]
theorem relativeFrobenius_left_baseChangeIso_hom :
    (E.relativeFrobenius p hS).hom.hom.hom.left ≫
        (E.baseChangeIso (S.frobenius p hS)).hom =
      E.structureMap.relativeFrobenius p hS := by
  simp [relativeFrobenius_left]

/-- Relative Frobenius of an elliptic curve is a finite flat surjective homomorphism. -/
instance isIsogeny_relativeFrobenius : IsIsogeny (E.relativeFrobenius p hS) := by
  have : Smooth E.structureMap := SmoothOfRelativeDimension.smooth 1 _
  apply (isIsogeny_iff _).mpr
  rw [relativeFrobenius_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Relative Frobenius has rank `p` everywhere, not rank one, even though it is a universal
homeomorphism. -/
@[simp]
theorem finrank_relativeFrobenius (x : (E.baseChange (S.frobenius p hS)).carrier) :
    (E.relativeFrobenius p hS).hom.hom.hom.left.finrank x = p := by
  have h := Scheme.Hom.finrank_comp_right_of_isIso
    (E.relativeFrobenius p hS).hom.hom.hom.left (E.baseChangeIso (S.frobenius p hS)).hom x
  rw [relativeFrobenius_left_baseChangeIso_hom,
    Scheme.Hom.finrank_relativeFrobenius_of_smoothOfRelativeDimension _ hS 1] at h
  simpa using h.symm

/-- Relative Frobenius is an isogeny of constant degree `p` over an arbitrary base. -/
theorem isogenyOfDegree_relativeFrobenius :
    GroupScheme.IsogenyOfDegree (E.relativeFrobenius p hS).hom p where
  isIsogeny := (E.isIsogeny_relativeFrobenius p hS).isIsogeny
  degree_eq s := by
    rw [GroupScheme.degree_eq_finrank]
    exact E.finrank_relativeFrobenius p hS _

/-- Verschiebung is the factorisation dual of relative Frobenius. It goes from the
Frobenius-twisted elliptic curve back to the original elliptic curve. -/
noncomputable def verschiebung :
    (E.baseChange (S.frobenius p hS)).toCommGrp ⟶ E.toCommGrp :=
  GroupScheme.factorisationDual (E.relativeFrobenius p hS)
    (E.isogenyOfDegree_relativeFrobenius p hS)

/-- Frobenius followed by Verschiebung is multiplication by `p` on the original curve. -/
@[reassoc (attr := simp)]
theorem relativeFrobenius_verschiebung :
    E.relativeFrobenius p hS ≫ E.verschiebung p hS = (p : End E.toCommGrp).asHom :=
  GroupScheme.comp_factorisationDual _ _

/-- Verschiebung followed by Frobenius is multiplication by `p` on the twisted curve. -/
@[reassoc (attr := simp)]
theorem verschiebung_relativeFrobenius :
    E.verschiebung p hS ≫ E.relativeFrobenius p hS =
      (p : End (E.baseChange (S.frobenius p hS)).toCommGrp).asHom :=
  GroupScheme.factorisationDual_comp _ _

/-- Verschiebung is the unique homomorphism whose composite after Frobenius is `[p]`. -/
theorem eq_verschiebung (g : (E.baseChange (S.frobenius p hS)).toCommGrp ⟶ E.toCommGrp)
    (hg : E.relativeFrobenius p hS ≫ g = (p : End E.toCommGrp).asHom) :
    g = E.verschiebung p hS :=
  GroupScheme.eq_factorisationDual _ _ g hg

/-- Verschiebung is an isogeny of constant degree `p`. -/
theorem isogenyOfDegree_verschiebung :
    GroupScheme.IsogenyOfDegree (E.verschiebung p hS).hom p :=
  isogenyOfDegree_factorisationDual _ (E.isogenyOfDegree_relativeFrobenius p hS)

/-- Verschiebung is finite flat and surjective. -/
instance isIsogeny_verschiebung : IsIsogeny (E.verschiebung p hS) :=
  ⟨(E.isogenyOfDegree_verschiebung p hS).isIsogeny⟩

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
