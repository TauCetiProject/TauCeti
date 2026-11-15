/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

/-!
# Maximal tori in Hopf coordinates

A closed subgroup of an affine group is encoded contravariantly by a Hopf ideal in its
coordinate algebra. This file defines a maximal torus to be a torus closed subgroup which is
not properly contained in another torus. Thus, if `I` is maximal and `J ≤ I` defines a torus,
then `I = J`.

## Main declarations

* `TauCeti.HopfIdeal.IsMaximalTorus`: maximality among torus Hopf ideals.
* `TauCeti.HopfIdeal.isMaximalTorus_of_maximal_points`: maximal commutativity of geometric
  points implies maximality of a torus.
* `TauCeti.HopfIdeal.isMaximalTorus_of_baseChange`: maximality descends from an algebraic
  closure along a base-change isomorphism of the ambient coordinate Hopf algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 17.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.

The isomorphism-invariance API follows the formal organization of
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism` and
`TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Isomorphism`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace HopfIdeal

/-- A Hopf ideal defines a maximal torus when its quotient coordinate Hopf algebra is a torus
and every torus closed subgroup containing it is equal to it.

Because coordinate rings reverse arrows, `J ≤ I` says that the subgroup cut out by `I` is
contained in the subgroup cut out by `J`. -/
def IsMaximalTorus (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) : Prop :=
  Minimal (fun J : HopfIdeal k H ↦
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J)) I

/-- The Hopf-ideal criterion for a maximal torus: the quotient is a torus and no strictly larger
torus closed subgroup contains it. -/
@[simp]
theorem isMaximalTorus_iff (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) :
    IsMaximalTorus k H I ↔
      torusCommHopfAlgProperty k
          (FiniteTypeCommHopfAlgCat.quotient
            ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ I) ∧
        ∀ J : HopfIdeal k H,
          torusCommHopfAlgProperty k
              (FiniteTypeCommHopfAlgCat.quotient
                ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J) →
            J ≤ I → I ≤ J :=
  Iff.rfl

/-- A torus over an algebraically closed field is maximal if its points embed as a maximal
commutative subgroup of a group. -/
theorem isMaximalTorus_of_maximal_points {k : Type u} [Field k] [IsAlgClosed k]
    {H : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H]
    (T : HopfIdeal k H)
    (hT : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ T))
    {G : Type*} [Group G]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* G)
    (hφ : Function.Injective φ) {S : Subgroup G}
    (hpoints : (CommHopfAlgCat.quotientPointsSubgroup H T (CommAlgCat.of k k)).map φ = S)
    (hmax : ∀ (P : Subgroup G) [IsMulCommutative P], S ≤ P → P = S) :
    IsMaximalTorus k H T := by
  rw [isMaximalTorus_iff]
  refine ⟨hT, ?_⟩
  intro I hI hIT
  let _ : IsReduced (CommHopfAlgCat.quotient H I) := hI.geometricallyReduced.isReduced
  let _ : Coalgebra.IsCocomm k (CommHopfAlgCat.quotient H I) := hI.isCocomm k _
  exact (eq_of_le_of_isCocomm_of_maximal_points T φ hφ hpoints hmax I hIT).ge

namespace IsMaximalTorus

variable {k : Type u} [Field k]
variable {H K : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k K.obj}

/-- Pulling a maximal torus back across an ambient Hopf-algebra isomorphism gives a maximal
torus in the source. -/
theorem comapOfIso (hI : IsMaximalTorus k K.obj I) (e : H ≅ K) :
    IsMaximalTorus k H.obj
      (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  exact FiniteTypeCommHopfAlgCat.minimal_quotientProperty_comapOfIso
    (torusCommHopfAlgProperty k) I hI e

open FiniteTypeCommHopfAlgCat in
/-- Maximal-torus status is invariant under pulling the defining ideal back across an ambient
Hopf-algebra isomorphism. -/
theorem comapOfIso_iff (e : H ≅ K) (I : HopfIdeal k K.obj) :
    IsMaximalTorus k H.obj
        (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
          (ConcreteCategory.bijective_of_isIso e.hom).2) ↔
      IsMaximalTorus k K.obj I := by
  constructor
  · intro hI
    simpa only [HopfIdeal.comapOfSurjective_comapOfSurjective, ← toBialgHom_comp,
      Iso.symm_hom, e.inv_hom_id, toBialgHom_id, HopfIdeal.comapOfSurjective_id]
      using hI.comapOfIso e.symm
  · exact fun hI ↦ hI.comapOfIso e

end IsMaximalTorus

/-- **Maximality of a torus descends from an algebraic closure.** If `I` cuts out a torus over
`k` and its base change, transported along an isomorphism `e` of the base-changed ambient
coordinate Hopf algebra, is a maximal torus over the algebraic closure, then `I` is a maximal
torus over `k`. -/
theorem isMaximalTorus_of_baseChange {k : Type u} [Field k]
    {H : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H]
    {H' : _root_.CommHopfAlgCat.{u} (AlgebraicClosure k)}
    [Algebra.FiniteType (AlgebraicClosure k) H']
    (I : HopfIdeal k H) (I' : HopfIdeal (AlgebraicClosure k) H')
    (e : CommHopfAlgCat.baseChange (K := AlgebraicClosure k) H ≅ H')
    (hI : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ I))
    (hmap : (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) I).map e.hom.hom = I')
    (hmax : IsMaximalTorus (AlgebraicClosure k) H' I') :
    IsMaximalTorus k H I := by
  -- A competing torus is base-changed, compared over the algebraic closure, and the resulting
  -- containment is descended along the faithfully flat extension `k → AlgebraicClosure k`.
  rw [isMaximalTorus_iff]
  refine ⟨hI, ?_⟩
  intro J hJ hJI
  let K := AlgebraicClosure k
  let Hft : FiniteTypeCommHopfAlgCat k :=
    ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
  let H'ft : FiniteTypeCommHopfAlgCat K :=
    ⟨H', (finiteTypeCommHopfAlgProperty_iff H').2 inferInstance⟩
  let JK := (CommHopfAlgCat.baseChangeHopfIdeal (K := K) J).map e.hom.hom
  have hmapJ : (CommHopfAlgCat.baseChangeHopfIdeal (K := K) J).map e.hom.hom = JK := rfl
  let qIso : FiniteTypeCommHopfAlgCat.baseChange (K := K)
        (FiniteTypeCommHopfAlgCat.quotient Hft J) ≅
      FiniteTypeCommHopfAlgCat.quotient H'ft JK :=
    ObjectProperty.isoMk _
      (CommHopfAlgCat.quotientBaseChangeIsoOfMapEq J JK e hmapJ)
  have hsplit : splitTorusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K)
        (FiniteTypeCommHopfAlgCat.quotient Hft J)) := by
    rw [splitTorusCommHopfAlgProperty_iff]
    rw [torusCommHopfAlgProperty_iff] at hJ
    simpa only [Hft] using hJ
  have hJK : torusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient H'ft JK) :=
    ((splitTorusCommHopfAlgProperty K).prop_of_iso qIso hsplit).torus K _
  have hJKI : JK ≤ I' := by
    rw [← hmap]
    exact HopfIdeal.map_mono e.hom.hom (CommHopfAlgCat.baseChangeHopfIdeal_mono hJI)
  rw [isMaximalTorus_iff] at hmax
  have hIJK : I' ≤ JK := hmax.2 JK hJK hJKI
  have he : Function.Bijective e.hom.hom := ConcreteCategory.bijective_of_isIso e.hom
  have hbase :
      CommHopfAlgCat.baseChangeHopfIdeal (K := K) I ≤
        CommHopfAlgCat.baseChangeHopfIdeal (K := K) J := by
    have hcomap := HopfIdeal.comapOfSurjective_mono e.hom.hom he.2 hIJK
    rw [← hmap, HopfIdeal.comapOfSurjective_map_of_bijective _ _ he,
      HopfIdeal.comapOfSurjective_map_of_bijective _ _ he] at hcomap
    exact hcomap
  exact (CommHopfAlgCat.baseChangeHopfIdeal_le_iff (algebraMap k K).injective).mp hbase

end HopfIdeal

end TauCeti
