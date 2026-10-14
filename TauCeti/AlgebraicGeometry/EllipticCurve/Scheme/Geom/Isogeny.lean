/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
public import TauCeti.AlgebraicGeometry.GroupScheme.Degree

/-!
# Isogenies of elliptic curves over a scheme

Let `E` and `E'` be elliptic curves over a scheme `S`. A homomorphism `f : E ⟶ E'` of elliptic
curves over `S` (a morphism `E.toCommGrp ⟶ E'.toCommGrp` of commutative group schemes) is an
**isogeny** when it is an isogeny of group schemes (`TauCeti.GroupScheme.IsIsogeny`): its
underlying morphism of schemes is finite, flat and surjective (`EllipticCurveGeom.IsIsogeny`).
Every homomorphism of elliptic curves is locally of finite presentation
(`EllipticCurveGeom.locallyOfFinitePresentation_hom_hom_hom_left`), so an isogeny is finite locally
free.

The degree of an isogeny is the degree `TauCeti.GroupScheme.degree f.hom` of the underlying
homomorphism of group schemes, the rank of its kernel, and an isogeny of constant degree `n` is
`TauCeti.GroupScheme.IsogenyOfDegree f.hom n`. The instances of this file supply the finiteness,
flatness, surjectivity and local finite presentation hypotheses of that API, so its results (local
constancy and positivity of the degree, multiplicativity under composition, the isogenies of degree
one being the isomorphisms, and the kernel of an isogeny of degree `n` being killed by `n`) apply
to every isogeny of elliptic curves directly. Multiplication by a nonzero integer `n` is an
isogeny of degree `n²` over any base.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsIsogeny f`: the homomorphism `f` is an isogeny.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isIsogeny_iff`: `f` is an isogeny exactly when its
  underlying morphism of schemes is finite, flat and surjective.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.degree_intCast` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isogenyOfDegree_intCast`: multiplication by a
  nonzero integer `n` is an isogeny of degree `n²`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.4 and 2.3.1.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} {E E' E'' : EllipticCurveGeom S}

/-! ### Isogenies -/

/-- **Isogenies of elliptic curves.** A homomorphism `f : E ⟶ E'` of elliptic curves over `S` is an
isogeny when it is an isogeny of group schemes, that is, its underlying morphism of schemes is
finite, flat and surjective (Katz–Mazur §2.4). It is then finite locally free, since it is locally
of finite presentation like every homomorphism of elliptic curves
(`locallyOfFinitePresentation_hom_hom_hom_left`). -/
class IsIsogeny (f : E.toCommGrp ⟶ E'.toCommGrp) : Prop where
  /-- The underlying homomorphism of group schemes is an isogeny. -/
  isIsogeny : GroupScheme.IsIsogeny f.hom

/-- A homomorphism of elliptic curves is an isogeny exactly when its underlying morphism of schemes
is finite, flat and surjective. -/
theorem isIsogeny_iff (f : E.toCommGrp ⟶ E'.toCommGrp) :
    IsIsogeny f ↔
      IsFinite f.hom.hom.hom.left ∧ Flat f.hom.hom.hom.left ∧ Surjective f.hom.hom.hom.left :=
  ⟨fun h ↦ (GroupScheme.isIsogeny_iff _).mp h.isIsogeny,
    fun h ↦ ⟨(GroupScheme.isIsogeny_iff _).mpr h⟩⟩

/-- The morphism of schemes underlying an isogeny is finite. -/
instance IsIsogeny.isFinite (f : E.toCommGrp ⟶ E'.toCommGrp) [IsIsogeny f] :
    IsFinite f.hom.hom.hom.left :=
  IsIsogeny.isIsogeny.isFinite

/-- The morphism of schemes underlying an isogeny is flat. -/
instance IsIsogeny.flat (f : E.toCommGrp ⟶ E'.toCommGrp) [IsIsogeny f] :
    Flat f.hom.hom.hom.left :=
  IsIsogeny.isIsogeny.flat

/-- The morphism of schemes underlying an isogeny is surjective. -/
instance IsIsogeny.surjective (f : E.toCommGrp ⟶ E'.toCommGrp) [IsIsogeny f] :
    Surjective f.hom.hom.hom.left :=
  IsIsogeny.isIsogeny.surjective

/-- An isomorphism of elliptic curves is an isogeny. -/
instance isIsogeny_of_isIso (f : E.toCommGrp ⟶ E'.toCommGrp) [IsIso f] : IsIsogeny f :=
  ⟨GroupScheme.isIsogeny_of_isIso f.hom⟩

/-- The composite of two isogenies is an isogeny. -/
instance isIsogeny_comp (f : E.toCommGrp ⟶ E'.toCommGrp) (g : E'.toCommGrp ⟶ E''.toCommGrp)
    [IsIsogeny f] [IsIsogeny g] : IsIsogeny (f ≫ g) :=
  ⟨IsIsogeny.isIsogeny.comp IsIsogeny.isIsogeny⟩

/-! ### Multiplication by an integer -/

variable (E : EllipticCurveGeom S)

/-- **Multiplication by a nonzero integer is an isogeny** (Katz–Mazur 2.3.1), over any base. -/
theorem isIsogeny_intCast {n : ℤ} (hn : n ≠ 0) : IsIsogeny (n : End E.toCommGrp) :=
  (isIsogeny_iff _).mpr ⟨by simpa using E.isFinite_mulBy_left hn,
    by simpa using E.flat_mulBy_left hn, by simpa using E.surjective_mulBy_left hn⟩

/-- **Multiplication by a nonzero integer `n` has degree `n²`** (Katz–Mazur 2.3.1): the rank of
its kernel `E[n]` is `n²` at every point of `S`. -/
@[simp]
theorem degree_intCast {n : ℤ} (hn : n ≠ 0) (s : S) :
    GroupScheme.degree (n : End E.toCommGrp).hom s = n.natAbs ^ 2 := by
  rw [GroupScheme.degree_apply]
  exact (congrArg (fun X : Over S ↦ X.hom.finrank s) (congrArg Grp.X (E.torsion_eq_kernel n))).symm
    |>.trans (E.finrank_torsion_hom hn s)

/-- **Multiplication by a nonzero integer `n` is an isogeny of degree `n²`.** -/
theorem isogenyOfDegree_intCast {n : ℤ} (hn : n ≠ 0) :
    GroupScheme.IsogenyOfDegree (n : End E.toCommGrp).hom (n.natAbs ^ 2) :=
  ⟨(E.isIsogeny_intCast hn).isIsogeny, E.degree_intCast hn⟩

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
