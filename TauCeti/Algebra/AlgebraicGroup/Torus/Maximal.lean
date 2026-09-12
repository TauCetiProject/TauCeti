/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic

/-!
# Maximal tori in Hopf coordinates

A closed subgroup of an affine group is encoded contravariantly by a Hopf ideal in its
coordinate algebra. This file defines a maximal torus to be a torus closed subgroup which is
not properly contained in another torus. Thus, if `I` is maximal and `J ≤ I` defines a torus,
then `I = J`.

## Main declarations

* `TauCeti.HopfIdeal.IsMaximalTorus`: maximality among torus Hopf ideals.
* `TauCeti.HopfIdeal.isMaximalTorus_of_baseChange`: maximality descends from an algebraic
  closure along a base-change isomorphism of the ambient coordinate Hopf algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 17.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.

The isomorphism-invariance API follows the formal organization of
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism` and
`TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Isomorphism`.

This supplies the Hopf-coordinate maximal-torus predicate required by Layer 7, "Borel subgroups,
maximal tori, and their conjugacy", of the ReductiveGroups roadmap. Existence and conjugacy of
maximal tori remain to be proved.
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

/-- Maximal-torus status is invariant under pulling the defining ideal back across an ambient
Hopf-algebra isomorphism. -/
theorem comapOfIso_iff (e : H ≅ K) (I : HopfIdeal k K.obj) :
    IsMaximalTorus k H.obj
        (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
          (ConcreteCategory.bijective_of_isIso e.hom).2) ↔
      IsMaximalTorus k K.obj I := by
  constructor
  · intro hI
    have hback := hI.comapOfIso e.symm
    let e' := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
      (_root_.CommHopfAlgCat.{u} k)).mapIso e
    let e'' := _root_.CommHopfAlgCat.ofIso e'
    -- `toBialgHom` for a finite-type morphism is definitionally the bialgebra morphism of
    -- its image under this forgetful functor. No propositional compatibility lemma exists
    -- for this reducible full-subcategory wrapper.
    change IsMaximalTorus k K.obj
      (HopfIdeal.comapOfSurjective
        (I.comapOfSurjective e''.toBialgHom
          (by simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
            EquivLike.surjective e''))
        e''.symm.toBialgHom
          (by simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
            EquivLike.surjective e''.symm)) at hback
    have he := HopfIdeal.comapOfSurjective_bialgEquiv_symm_apply I e''.symm
    have he_symm_symm : e''.symm.symm = e'' := by
      ext
      rfl
    simp only [he_symm_symm] at he
    rw [he] at hback
    exact hback
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
