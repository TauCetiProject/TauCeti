/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Orthogonal
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The Weyl quotient of simply-laced Chevalley data

For every Chevalley datum of simply-laced type over a field, the kernel of its Weyl
projection is exactly its actual character-lattice torus. Consequently the quotient of
`weylSubgroup` by that torus is the Weyl group of the pinned root datum. The equivalence
sends the class of each pinned simple Weyl representative to its simple reflection.

The argument uses the native rank-one square and single-bond braid relations. Modulo the
torus, the pinned representatives satisfy the Coxeter presentation; the induced map back
from the Weyl group is inverse to the quotient projection. No point-generation theorem,
Bruhat decomposition, infinitude assumption, or surjectivity of the full-weight torus
parametrization is needed. In particular, the result applies to adjoint data and finite
fields. Multiply-laced types require the additional length-four and length-six relations.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 22, and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

attribute [local instance] isReduced_simplyConnectedRootDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (A : Type*) [CommRing A]

local notation "N" => D.weylSubgroup A
local notation "H" => Subgroup.subgroupOf (MonoidHom.range (D.torusPoints A)) N
local notation "Q" => N ⧸ H

private def simpleLift (i : Fin t.rank) : N :=
  ⟨D.weylElement (t.simpleIndex ht i) A 1, D.weylElement_mem_weylSubgroup A i⟩

private def simpleClass (i : Fin t.rank) : Q :=
  QuotientGroup.mk (D.simpleLift A i)

private theorem simpleClass_mul_self (i : Fin t.rank) :
    D.simpleClass A i * D.simpleClass A i = 1 := by
  rw [simpleClass, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  exact ⟨D.simpleCorootParameter i A (-1),
    (D.simpleCorootPoints_eq_torusPoints i A (-1)).symm.trans
      (D.weylElement_mul_self i A).symm⟩

private theorem simpleClass_commute (i j : Fin t.rank) (hij : t.cartanMatrix i j = 0) :
    Commute (D.simpleClass A i) (D.simpleClass A j) := by
  have h : D.simpleLift A i * D.simpleLift A j = D.simpleLift A j * D.simpleLift A i := by
    apply Subtype.ext
    exact (D.commute_weylElement_simpleIndex A i j hij 1 1).eq
  exact congrArg (QuotientGroup.mk' H) h

private theorem simpleClass_braid (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1) :
    D.simpleClass A i * D.simpleClass A j * D.simpleClass A i =
      D.simpleClass A j * D.simpleClass A i * D.simpleClass A j := by
  have h : D.simpleLift A i * D.simpleLift A j * D.simpleLift A i =
      D.simpleLift A j * D.simpleLift A i * D.simpleLift A j := by
    apply Subtype.ext
    exact D.weylElement_braid_of_cartanMatrix_eq_neg_one i j hij hji A
  exact congrArg (QuotientGroup.mk' H) h

private theorem simpleClass_liftable (hs : t.IsSimplyLaced) :
    (coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).IsLiftable
      (fun i => D.simpleClass A ((t.simpleSupportEquivSimplyConnectedBase ht).symm i)) := by
  intro a b
  let e := t.simpleSupportEquivSimplyConnectedBase ht
  obtain ⟨i, rfl⟩ := e.surjective a
  obtain ⟨j, rfl⟩ := e.surjective b
  simp only [e, Equiv.symm_apply_apply]
  have hm : coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
      (e i) (e j) = coxeterOrder (t.cartanMatrix i j * t.cartanMatrix j i) := by
    simp only [coxeterMatrixOfBase_apply, RootPairing.Base.cartanMatrix,
      RootPairing.Base.cartanMatrixIn, Matrix.of_apply, e,
      coe_simpleSupportEquivSimplyConnectedBase, pairingIn_simpleIndex]
  rw [hm]
  by_cases h : i = j
  · subst j
    simp only [D.simpleClass_mul_self, one_pow]
  have hsym : t.cartanMatrix j i = t.cartanMatrix i j := hs.isSymm_cartanMatrix.apply _ _
  rcases ((isSimplyLaced_cartanMatrix_iff_of_valid ht).mpr hs) h with hij | hij
  · rw [hij, hsym, hij, mul_zero, coxeterOrder_zero,
      (D.simpleClass_commute A i j hij).mul_pow]
    simp only [pow_two, D.simpleClass_mul_self, one_mul]
  · simp only [hij, hsym, neg_mul_neg, one_mul, coxeterOrder_one]
    have hb := D.simpleClass_braid A i j hij (hsym.trans hij)
    calc
      _ = (D.simpleClass A i * D.simpleClass A j * D.simpleClass A i) *
          (D.simpleClass A j * D.simpleClass A i * D.simpleClass A j) := by
        simp only [pow_succ, pow_zero]
        group
      _ = D.simpleClass A j * D.simpleClass A i *
          (D.simpleClass A j * D.simpleClass A j) *
          D.simpleClass A i * D.simpleClass A j := by rw [hb]; group
      _ = D.simpleClass A j * (D.simpleClass A i * D.simpleClass A i) *
          D.simpleClass A j := by rw [D.simpleClass_mul_self]; group
      _ = 1 := by rw [D.simpleClass_mul_self, mul_one, D.simpleClass_mul_self]

private def quotientSection (hs : t.IsSimplyLaced) :
    (t.simplyConnectedRootDatum ht).weylGroup →* Q :=
  (weylCoxeterSystem (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).lift
    ⟨_, D.simpleClass_liftable A hs⟩

private theorem quotientSection_simple (hs : t.IsSimplyLaced) (i : Fin t.rank) :
    D.quotientSection A hs
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      D.simpleClass A i := by
  have h := (weylCoxeterSystem (t.simplyConnectedRootDatum ht)
    (t.simplyConnectedBase ht)).lift_apply_simple (D.simpleClass_liftable A hs)
      (t.simpleSupportEquivSimplyConnectedBase ht i)
  simpa only [quotientSection, weylCoxeterSystem_simple,
    coe_simpleSupportEquivSimplyConnectedBase, Equiv.symm_apply_apply] using h

end

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type*) [Field K]

local notation "Nₖ" => D.weylSubgroup K
local notation "Hₖ" => Subgroup.subgroupOf (MonoidHom.range (D.torusPoints K)) Nₖ

private theorem quotientSection_weylProjection (hs : t.IsSimplyLaced) (g : Nₖ) :
    D.quotientSection K hs (D.weylProjection K g) = QuotientGroup.mk' Hₖ g := by
  have hdense : Subgroup.closure ((D.weylSubgroup K).subtype ⁻¹'
      (Set.range (D.torusPoints K) ∪
        Set.range (fun i => D.weylElement (t.simpleIndex ht i) K 1))) = ⊤ := by
    rw [D.weylSubgroup_def]
    exact Subgroup.closure_preimage_eq_top _
  have hf : (D.quotientSection K hs).comp (D.weylProjection K) = QuotientGroup.mk' Hₖ := by
    apply MonoidHom.eq_of_eqOn_dense hdense
    rintro ⟨x, hx⟩ (⟨s, rfl⟩ | ⟨i, rfl⟩)
    · simp only [MonoidHom.comp_apply, D.weylProjection_torusPoints, map_one]
      exact ((QuotientGroup.eq_one_iff (N := Hₖ) _).mpr ⟨s, rfl⟩).symm
    · simp only [MonoidHom.comp_apply, D.weylProjection_weylElement,
        D.quotientSection_simple]
      rfl
  exact DFunLike.congr_fun hf g

/-- In simply-laced type, the Weyl projection has kernel exactly the actual torus,
regarded as a subgroup of the subgroup generated by the torus and Weyl representatives. -/
theorem ker_weylProjection_of_isSimplyLaced (hs : t.IsSimplyLaced) :
    (D.weylProjection K).ker = Hₖ := by
  ext g
  constructor
  · intro hg
    apply (QuotientGroup.eq_one_iff g).mp
    rw [← QuotientGroup.mk'_apply, ← D.quotientSection_weylProjection K hs g,
      MonoidHom.mem_ker.mp hg, map_one]
  · rintro ⟨s, hs⟩
    have hg : g = ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩ :=
      Subtype.ext hs.symm
    rw [hg, MonoidHom.mem_ker, D.weylProjection_torusPoints]

/-- The quotient of a simply-laced Chevalley datum's Weyl subgroup by its actual torus
is the Weyl group of the pinned root datum, over every field. -/
def weylQuotientEquivOfIsSimplyLaced (hs : t.IsSimplyLaced) :
    Nₖ ⧸ Hₖ ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_weylProjection_of_isSimplyLaced K hs).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.weylProjection K)
      (D.weylProjection_surjective K))

/-- The Weyl quotient equivalence is induced by the native Weyl projection. -/
@[simp]
theorem weylQuotientEquivOfIsSimplyLaced_mk (hs : t.IsSimplyLaced) (g : Nₖ) :
    D.weylQuotientEquivOfIsSimplyLaced K hs (QuotientGroup.mk g) = D.weylProjection K g := by
  simp only [weylQuotientEquivOfIsSimplyLaced, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk (D.weylProjection K) g

end

end TauCeti.DynkinType.ChevalleyDatum
