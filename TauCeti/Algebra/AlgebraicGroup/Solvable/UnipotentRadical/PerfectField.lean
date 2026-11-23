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

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_of_torus_coinvariants`: a
  connected normal smooth unipotent subgroup with torus quotient is the unipotent radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_torus`:
  if `G ⧸ R_u(G)` is a torus, the unipotent radical commutes with every field extension.
* `TauCeti.FiniteTypeCommHopfAlgCat.torus_coinvariants_unipotentRadical_of_perfectField`:
  over a perfect field, `G ⧸ R_u(G)` is a torus for smooth connected solvable `G`.
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

open torusCommHopfAlgProperty in
/-- **Uniqueness of the unipotent radical with torus quotient.** Over any field, a connected
normal smooth unipotent subgroup of a geometrically reduced group whose affine quotient is a torus
is the unipotent radical. -/
theorem unipotentRadicalDefiningIdeal_eq_of_torus_coinvariants
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.IsGeometricallyReduced k H]
    {I : HopfIdeal k H} (hI : HopfIdeal.IsUnipotentRadicalCandidate H I) :
    letI := hI.isNormal.isHopfSubalgebra_coinvariants.hopfAlgebra
    torusCommHopfAlgProperty k
        ⟨CommHopfAlgCat.coinvariants hI.isNormal,
          (finiteTypeCommHopfAlgProperty_iff _).mpr hI.isNormal.finiteType_coinvariants⟩ →
      unipotentRadicalDefiningIdeal H = I := by
  intro hT
  let D : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨CommHopfAlgCat.coinvariants hI.isNormal,
      (finiteTypeCommHopfAlgProperty_iff _).mpr hI.isNormal.finiteType_coinvariants⟩
  have hker := CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq hI.isNormal
  let _ : Algebra.IsGeometricallyReduced k D :=
    Algebra.IsGeometricallyReduced.of_injective
      (CommHopfAlgCat.coinvariantsι hI.isNormal).hom.toAlgHom
      (CommHopfAlgCat.hopfSubalgebraι_injective hI.isNormal.isHopfSubalgebra_coinvariants)
  have hT' :=
    (iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced k D).mp hT
  have hD : geometricallySemisimplePointsCommHopfAlgProperty k D.obj :=
    ((multiplicativeTypeCommHopfAlgProperty_iff_isCocomm_and_geometricallySemisimplePoints D).mp
      hT'.1).2
  rw [unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_geometricallySemisimple H D hD
    (CommHopfAlgCat.coinvariantsι hI.isNormal) (by rwa [hker]), hker]

/-- **Base change of the unipotent radical with torus quotient.** Over any field, if the affine
quotient of a smooth group by its unipotent radical is a torus, then the formation of the unipotent
radical commutes with every field extension `K / k`. -/
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_torus
    {K : Type u} [Field K] [Algebra k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k H] :
    letI := (isNormal_unipotentRadicalDefiningIdeal H).isHopfSubalgebra_coinvariants.hopfAlgebra
    torusCommHopfAlgProperty k
        ⟨CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal H),
          (finiteTypeCommHopfAlgProperty_iff _).mpr
            (isNormal_unipotentRadicalDefiningIdeal H).finiteType_coinvariants⟩ →
      CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
        unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  intro hT
  let hR := isNormal_unipotentRadicalDefiningIdeal H
  have hI := (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H).baseChange (K := K)
  refine (unipotentRadicalDefiningIdeal_eq_of_torus_coinvariants _ hI ?_).symm
  exact (torusCommHopfAlgProperty K).prop_of_iso
    (ObjectProperty.isoMk _ (CommHopfAlgCat.coinvariantsBaseChangeIso (K := K) hR))
    (hT.baseChange K)

variable [PerfectField k]

/-- **The quotient of a smooth connected solvable group by its unipotent radical is a torus**
over a perfect field, in every characteristic (Milne, Theorem 16.33). -/
theorem torus_coinvariants_unipotentRadical_of_perfectField
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k G]
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj) :
    let hR := isNormal_unipotentRadicalDefiningIdeal G
    letI := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    torusCommHopfAlgProperty k Q := by
  intro hR Q
  have hQ : geometricallySolvablePointsCommHopfAlgProperty k Q.obj :=
    hsolv.of_faithfullyFlat (CommHopfAlgCat.coinvariantsι hR)
      (AlgHom.FiniteType.of_finitePresentation
        (CommHopfAlgCat.finitePresentation_coinvariantsι hR))
      (CommHopfAlgCat.faithfullyFlat_coinvariantsι hR)
  exact (reductive_coinvariants_unipotentRadical G hconnected).torus_of_geometricallySolvable hQ

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
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.quotientBaseChangeIsoOfMapEq
      (unipotentRadicalDefiningIdeal G)
      (unipotentRadicalDefiningIdeal (baseChange (K := K) G))
      (Iso.refl (CommHopfAlgCat.baseChange (K := K) G.obj))
      (by
        rw [Iso.refl_hom, ← _root_.CommHopfAlgCat.ofHom_id, _root_.CommHopfAlgCat.hom_ofHom,
          HopfIdeal.map_id,
          baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_perfectField G hconnected hsolv])

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
        (unipotentRadicalDefiningIdeal (baseChange (K := K) G)) := by
  rw [_root_.CommHopfAlgCat.mapIso_baseChange_quotientClosedSubgroup,
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_perfectField G hconnected hsolv]

end FiniteTypeCommHopfAlgCat

end

end TauCeti
