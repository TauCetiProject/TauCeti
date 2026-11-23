/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.HopfBaseChange
public import TauCeti.RingTheory.Smooth.GeometricallyReduced
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UnipotentRadical.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Descent
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.TorusQuotient
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Recognition
import TauCeti.Algebra.AlgebraicGroup.PseudoReductive.Basic
import TauCeti.Algebra.AlgebraicGroup.Reductive.Solvable
import TauCeti.Algebra.AlgebraicGroup.Solvable.FaithfullyFlat
import TauCeti.Algebra.AlgebraicGroup.Torus.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.DiagonalizableQuotient

/-!
# The unipotent radical of a solvable group over a perfect field

Let `G` be a smooth geometrically connected affine group of finite type over a perfect field `k`
whose geometric points form a solvable group. This file proves the perfect-field part of the
structure theorem for `G` (Milne, Theorem 16.33(a)–(c)):

* the affine quotient `G ⧸ R_u(G)` by the `k`-unipotent radical is a torus;
* `R_u(G)` is the only connected normal smooth unipotent subgroup with torus quotient;
* the formation of `R_u(G)` commutes with every field extension `K / k`, not only the separable
  algebraic ones of
  `TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal`.

Over a perfect field the quotient `G ⧸ R_u(G)` is reductive
(`TauCeti.FiniteTypeCommHopfAlgCat.reductive_coinvariants_unipotentRadical`) with solvable
geometric points, so it is a torus by
`TauCeti.reductiveCommHopfAlgProperty.torus_of_geometricallySolvable`.

The base-change statement holds over any field once `G ⧸ R_u(G)` is a torus. A torus stays a torus
after extension of scalars, and the points of a torus are semisimple; the image in a group with
semisimple geometric points of the smooth unipotent radical of `G_K` is trivial. Hence the
base change of `R_u(G)`, which is the kernel of `G_K → (G ⧸ R_u(G))_K`, is the unipotent radical
of `G_K` by `TauCeti.FiniteTypeCommHopfAlgCat.
unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_geometricallySemisimple`.

The field-independent steps are in
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.TorusQuotient`, and the torus theorem
`TauCeti.FiniteTypeCommHopfAlgCat.torus_coinvariants_unipotentRadical_of_perfectField` is in
`TauCeti.Algebra.AlgebraicGroup.Solvable.UnipotentRadical.Basic`.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_perfectField`:
  over a perfect field, `R_u(G)` of a smooth connected solvable `G` commutes with every field
  extension.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalBaseChangeIsoOfPerfectField` and
  `TauCeti.FiniteTypeCommHopfAlgCat.
    mapIso_baseChange_quotientClosedSubgroup_unipotentRadicalDefiningIdeal_of_perfectField`:
  the corresponding coordinate Hopf-algebra isomorphism and equality of closed subgroup schemes.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.33(a)–(c), pp. 335–336.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

variable [PerfectField k]

/-- **The unipotent radical of a smooth connected solvable group over a perfect field commutes
with every field extension** `K / k` (Milne, Theorem 16.33). For separable algebraic extensions
this holds for every finite-type group,
`TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal`. -/
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_perfectField
    {K : Type u} [Field K] [Algebra k K]
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k G]
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal G) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) G) :=
  baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_torus G
    (torus_coinvariants_unipotentRadical_of_perfectField G hconnected hsolv)

/-- **Base-change comparison for the unipotent radical of a smooth connected solvable group** over
a perfect field `k`, along an arbitrary field extension `K / k`: the scalar extension of the
coordinate Hopf algebra of `R_{u,k}(G)` is canonically isomorphic to that of `R_{u,K}(G_K)`. -/
def unipotentRadicalBaseChangeIsoOfPerfectField
    {K : Type u} [Field K] [Algebra k K]
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k G]
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj) :
    baseChange (K := K) (unipotentRadical G) ≅ unipotentRadical (baseChange (K := K) G) :=
  unipotentRadicalBaseChangeIsoOfEq G
    (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_perfectField G hconnected hsolv)

/-- The perfect-field base-change isomorphism commutes with the coordinate quotient maps. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_comp_unipotentRadicalBaseChangeIsoOfPerfectField_hom
    {K : Type u} [Field K] [Algebra k K]
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k G]
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj) :
    baseChangeMap (K := K) (unipotentRadicalCoordinateMap G) ≫
        (unipotentRadicalBaseChangeIsoOfPerfectField G hconnected hsolv).hom =
      unipotentRadicalCoordinateMap (baseChange (K := K) G) :=
  baseChangeMap_unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfEq_hom G _

/-- The inverse perfect-field base-change isomorphism commutes with the coordinate quotient maps. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_unipotentRadicalBaseChangeIsoOfPerfectField_inv
    {K : Type u} [Field K] [Algebra k K]
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k G]
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj) :
    unipotentRadicalCoordinateMap (baseChange (K := K) G) ≫
        (unipotentRadicalBaseChangeIsoOfPerfectField G hconnected hsolv).inv =
      baseChangeMap (K := K) (unipotentRadicalCoordinateMap G) :=
  unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfEq_inv G _

/-- **Scheme-level base change of the unipotent radical of a smooth connected solvable group**
over a perfect field `k`, along an arbitrary field extension `K / k`: the base change of the closed
subgroup scheme `R_{u,k}(G) ≤ G` along `Spec K ⟶ Spec k` agrees with `R_{u,K}(G_K) ≤ G_K`. -/
theorem mapIso_baseChange_quotientClosedSubgroup_unipotentRadicalDefiningIdeal_of_perfectField
    {K : Type u} [Field K] [Algebra k K]
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k G]
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj) :
    ClosedSubgroupScheme.mapIso (AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso (S := K) G.obj)
        ((CommHopfAlgCat.quotientClosedSubgroup G.obj (unipotentRadicalDefiningIdeal G)).baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) =
      CommHopfAlgCat.quotientClosedSubgroup (CommHopfAlgCat.baseChange (K := K) G.obj)
        (unipotentRadicalDefiningIdeal (baseChange (K := K) G)) :=
  mapIso_baseChange_quotientClosedSubgroup_unipotentRadicalDefiningIdeal_of_eq G
    (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_perfectField G hconnected hsolv)

end FiniteTypeCommHopfAlgCat

end

end TauCeti
