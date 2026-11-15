/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.DoubleBond
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Orthogonal
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coefficient

/-!
# The Weyl quotient of Chevalley data outside type G₂

For every Chevalley datum of type other than G₂ over a nontrivial commutative ring,
the quotient of `weylSubgroup` by its actual character-lattice torus is the Weyl group of
the pinned root datum. The equivalence sends the class of each pinned simple Weyl
representative to its simple reflection. Over a field, the kernel of the native Weyl
projection is exactly that torus.

The argument uses the native rank-one square, single-bond and double-bond braid relations.
Modulo the torus, the pinned representatives satisfy the Coxeter presentation; the induced map back
from the Weyl group is surjective by generation and injective by reduction to a residue
field. Over fields its inverse agrees with the native Weyl projection. No point-generation theorem,
Bruhat decomposition, infinitude assumption, or surjectivity of the full-weight torus
parametrization is needed. In particular, the result applies to adjoint data and finite
fields. Type G₂ still requires the additional length-six relation.

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
  rw [simpleClass, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  simp only [Subgroup.coe_mul, simpleLift]
  exact ⟨D.simpleCorootParameter i A (-1),
    (D.simpleCorootPoints_eq_torusPoints i A (-1)).symm.trans
      (D.weylElement_mul_self i A).symm⟩

private theorem simpleClass_commute (i j : Fin t.rank) (hij : t.cartanMatrix i j = 0) :
    Commute (D.simpleClass A i) (D.simpleClass A j) := by
  have h : D.simpleLift A i * D.simpleLift A j = D.simpleLift A j * D.simpleLift A i := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, simpleLift] using
      (D.commute_weylElement_simpleIndex A i j hij 1 1).eq
  simpa only [commute_iff_eq, simpleClass, map_mul, QuotientGroup.mk'_apply] using
    congrArg (QuotientGroup.mk' H) h

private theorem simpleClass_braid (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1) :
    D.simpleClass A i * D.simpleClass A j * D.simpleClass A i =
      D.simpleClass A j * D.simpleClass A i * D.simpleClass A j := by
  have h : D.simpleLift A i * D.simpleLift A j * D.simpleLift A i =
      D.simpleLift A j * D.simpleLift A i * D.simpleLift A j := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, simpleLift] using
      D.weylElement_braid_of_cartanMatrix_eq_neg_one i j hij hji A
  simpa only [simpleClass, map_mul, QuotientGroup.mk'_apply] using
    congrArg (QuotientGroup.mk' H) h

private theorem simpleClass_pow_three (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1) :
    (D.simpleClass A i * D.simpleClass A j) ^ 3 = 1 := by
  have hb := D.simpleClass_braid A i j hij hji
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

private theorem simpleClass_pow_four (i j : Fin t.rank)
    (hji : t.cartanMatrix j i = -2) :
    (D.simpleClass A i * D.simpleClass A j) ^ 4 = 1 := by
  have hb : (D.simpleClass A i * D.simpleClass A j) ^ 2 =
      (D.simpleClass A j * D.simpleClass A i) ^ 2 := by
    have h : D.simpleLift A i * D.simpleLift A j * D.simpleLift A i * D.simpleLift A j =
        D.simpleLift A j * D.simpleLift A i * D.simpleLift A j * D.simpleLift A i := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, simpleLift] using
        D.weylElement_braid_of_cartanMatrix_eq_neg_two i j hji A
    simpa only [simpleClass, map_mul, QuotientGroup.mk'_apply, pow_two, mul_assoc] using
      congrArg (QuotientGroup.mk' H) h
  have hinv (k : Fin t.rank) : (D.simpleClass A k)⁻¹ = D.simpleClass A k :=
    inv_eq_of_mul_eq_one_left (D.simpleClass_mul_self A k)
  calc
    _ = (D.simpleClass A i * D.simpleClass A j) ^ 2 *
        (D.simpleClass A i * D.simpleClass A j) ^ 2 := by group
    _ = (D.simpleClass A j * D.simpleClass A i) ^ 2 *
        (D.simpleClass A i * D.simpleClass A j) ^ 2 :=
      congrArg (fun z => z * (D.simpleClass A i * D.simpleClass A j) ^ 2) hb
    _ = ((D.simpleClass A i * D.simpleClass A j) ^ 2)⁻¹ *
        (D.simpleClass A i * D.simpleClass A j) ^ 2 := by
      rw [← inv_pow, mul_inv_rev, hinv, hinv]
    _ = 1 := inv_mul_cancel _

private theorem simpleClass_liftable (hs : t ≠ .G2) :
    (coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).IsLiftable
      (fun i => D.simpleClass A ((t.simpleSupportEquivSimplyConnectedBase ht).symm i)) := by
  intro a b
  let e := t.simpleSupportEquivSimplyConnectedBase ht
  obtain ⟨i, rfl⟩ := e.surjective a
  obtain ⟨j, rfl⟩ := e.surjective b
  simp only [e, Equiv.symm_apply_apply]
  have hm : coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
      (e i) (e j) = coxeterOrder (t.cartanMatrix i j * t.cartanMatrix j i) := by
    rw [coxeterMatrixOfBase_apply, cartanMatrix_simplyConnectedBase_apply,
      cartanMatrix_simplyConnectedBase_apply]
  rw [hm]
  by_cases h : i = j
  · subst j
    simp only [D.simpleClass_mul_self, one_pow]
  rcases cartanMatrix_eq_zero_and_eq_zero_or_of_ne_G2_of_ne hs h with
    ⟨hij, _⟩ | ⟨hij, hji⟩ | ⟨hij, hji⟩ | ⟨hij, hji⟩
  · rw [hij, zero_mul, coxeterOrder_zero, (D.simpleClass_commute A i j hij).mul_pow]
    simp only [pow_two, D.simpleClass_mul_self, one_mul]
  · simpa only [hij, hji, neg_mul_neg, one_mul, coxeterOrder_one] using
      D.simpleClass_pow_three A i j hij hji
  · simpa only [hij, hji, neg_mul_neg, one_mul, coxeterOrder_two] using
      D.simpleClass_pow_four A i j hji
  · simp only [hij, hji, neg_mul_neg, mul_one, coxeterOrder_two]
    calc
      _ = D.simpleClass A i * (D.simpleClass A j * D.simpleClass A i) ^ 4 *
          (D.simpleClass A i)⁻¹ := by
        simp only [pow_succ, pow_zero]
        group
      _ = 1 := by rw [D.simpleClass_pow_four A j i hij]; group

private def quotientSection (hs : t ≠ .G2) :
    (t.simplyConnectedRootDatum ht).weylGroup →* Q :=
  (weylCoxeterSystem (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).lift
    ⟨_, D.simpleClass_liftable A hs⟩

private theorem quotientSection_simple (hs : t ≠ .G2) (i : Fin t.rank) :
    D.quotientSection A hs
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      D.simpleClass A i := by
  have h := (weylCoxeterSystem (t.simplyConnectedRootDatum ht)
    (t.simplyConnectedBase ht)).lift_apply_simple (D.simpleClass_liftable A hs)
      (t.simpleSupportEquivSimplyConnectedBase ht i)
  simpa only [quotientSection, weylCoxeterSystem_simple,
    coe_simpleSupportEquivSimplyConnectedBase, Equiv.symm_apply_apply] using h

private theorem quotientSection_surjective (hs : t ≠ .G2) :
    Function.Surjective (D.quotientSection A hs) := by
  have hdense : Subgroup.closure ((D.weylSubgroup A).subtype ⁻¹'
      (Set.range (D.torusPoints A) ∪
        Set.range (fun i => D.weylElement (t.simpleIndex ht i) A 1))) = ⊤ := by
    rw [D.weylSubgroup_def]
    exact Subgroup.closure_preimage_eq_top _
  have hrange : (D.quotientSection A hs).range.comap (QuotientGroup.mk' H) = ⊤ := by
    apply top_unique
    rw [← hdense, Subgroup.closure_le]
    rintro ⟨x, hx⟩ (⟨s, rfl⟩ | ⟨i, rfl⟩)
    · have htorus : (QuotientGroup.mk' H) ⟨D.torusPoints A s, hx⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          Subgroup.mem_subgroupOf, MonoidHom.mem_range]
        exact ⟨s, rfl⟩
      -- Expose the comap membership hidden by the set coercion in closure_le.
      change (QuotientGroup.mk' H) ⟨D.torusPoints A s, hx⟩ ∈
        (D.quotientSection A hs).range
      rw [htorus]
      exact (D.quotientSection A hs).range.one_mem
    · exact ⟨_, D.quotientSection_simple A hs i⟩
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
  have hg : g ∈ (D.quotientSection A hs).range.comap (QuotientGroup.mk' H) := by
    rw [hrange]
    trivial
  exact hg

private theorem quotientSection_injective [Nontrivial A] (hs : t ≠ .G2) :
    Function.Injective (D.quotientSection A hs) := by
  -- A residue field detects the Weyl word, without requiring a projection over rings.
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let : M.IsMaximal := hM
  let := Ideal.Quotient.field M
  let f := (D.pointsPresentation A).map (D.pointsPresentation (A ⧸ M)) (Ideal.Quotient.mk M)
  have hw (i : Fin t.rank) : f (D.weylElement (t.simpleIndex ht i) A 1) =
      D.weylElement (t.simpleIndex ht i) (A ⧸ M) 1 := by
    apply Subtype.ext
    exact (GeneralLinear.IntegralPointsPresentation.coe_map
      (D.pointsPresentation A) (D.pointsPresentation (A ⧸ M)) (Ideal.Quotient.mk M) _).trans
        (by simpa only [map_one] using
          D.map_weylElement (Ideal.Quotient.mk M) (t.simpleIndex ht i) 1)
  -- Restrict scalar extension to the Weyl subgroups using their defining generators.
  have hf : N ≤ (D.weylSubgroup (A ⧸ M)).comap f := by
    rw [D.weylSubgroup_def, Subgroup.closure_le]
    rintro x (⟨s, rfl⟩ | ⟨i, rfl⟩)
    · -- Expose the comap membership hidden by the set coercion in closure_le.
      change f (D.torusPoints A s) ∈ D.weylSubgroup (A ⧸ M)
      simpa only [f, D.map_torusPoints] using
        D.torusPoints_mem_weylSubgroup (A ⧸ M) _
    · -- Likewise expose membership before rewriting the mapped representative.
      change f (D.weylElement (t.simpleIndex ht i) A 1) ∈ D.weylSubgroup (A ⧸ M)
      rw [hw]
      exact D.weylElement_mem_weylSubgroup (A ⧸ M) i
  let φ : N →* D.weylSubgroup (A ⧸ M) :=
    (f.comp (D.weylSubgroup A).subtype).codRestrict _ (fun g => hf g.property)
  -- Torus points still project trivially, so the residue-field projection descends.
  have hker : H ≤ ((D.weylProjection (A ⧸ M)).comp φ).ker := by
    intro g hg
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at hg
    obtain ⟨s, hsg⟩ := hg
    have hg : g = ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ :=
      Subtype.ext hsg.symm
    rw [hg, MonoidHom.mem_ker, MonoidHom.comp_apply]
    -- Evaluate the locally defined restriction φ; the remaining proof field is irrelevant.
    change D.weylProjection (A ⧸ M) ⟨f (D.torusPoints A s), _⟩ = 1
    simp only [f, D.map_torusPoints, D.weylProjection_torusPoints]
  let p : Q →* (t.simplyConnectedRootDatum ht).weylGroup :=
    QuotientGroup.lift H ((D.weylProjection (A ⧸ M)).comp φ) hker
  -- The descended map is a left inverse, as can be checked on simple reflections.
  have hp : p.comp (D.quotientSection A hs) = MonoidHom.id _ := by
    apply (weylCoxeterSystem (t.simplyConnectedRootDatum ht)
      (t.simplyConnectedBase ht)).ext_simple
    intro a
    obtain ⟨i, rfl⟩ := (t.simpleSupportEquivSimplyConnectedBase ht).surjective a
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, weylCoxeterSystem_simple,
      coe_simpleSupportEquivSimplyConnectedBase, D.quotientSection_simple]
    simp only [simpleClass, p, QuotientGroup.lift_mk', MonoidHom.comp_apply]
    -- Evaluate φ on the simple lift before applying the scalar-extension equation.
    change D.weylProjection (A ⧸ M)
      ⟨f (D.weylElement (t.simpleIndex ht i) A 1), _⟩ = _
    simp only [hw, D.weylProjection_weylElement]
  exact Function.LeftInverse.injective (fun w => DFunLike.congr_fun hp w)

/-- The quotient of a Chevalley datum's Weyl subgroup by its actual torus is the Weyl
group of the pinned root datum, over every nontrivial commutative ring, outside type G₂. -/
def weylQuotientEquivOfNeG2 [Nontrivial A] (hs : t ≠ .G2) :
    Q ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  (MulEquiv.ofBijective (D.quotientSection A hs)
    ⟨D.quotientSection_injective A hs, D.quotientSection_surjective A hs⟩).symm

/-- The inverse Weyl quotient equivalence sends a pinned simple reflection to the class
of its pinned Weyl representative. -/
@[simp↓]
theorem weylQuotientEquivOfNeG2_symm_ofIdx [Nontrivial A] (hs : t ≠ .G2)
    (i : Fin t.rank) :
    (D.weylQuotientEquivOfNeG2 A hs).symm
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      QuotientGroup.mk
        ⟨D.weylElement (t.simpleIndex ht i) A 1, D.weylElement_mem_weylSubgroup A i⟩ :=
  D.quotientSection_simple A hs i

/-- The Weyl quotient equivalence sends the class of a pinned simple Weyl representative
to its simple reflection. -/
@[simp↓]
theorem weylQuotientEquivOfNeG2_mk_weylElement [Nontrivial A] (hs : t ≠ .G2)
    (i : Fin t.rank) :
    D.weylQuotientEquivOfNeG2 A hs
        (QuotientGroup.mk
          ⟨D.weylElement (t.simpleIndex ht i) A 1, D.weylElement_mem_weylSubgroup A i⟩) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  apply (D.weylQuotientEquivOfNeG2 A hs).eq_symm_apply.mp
  exact (D.weylQuotientEquivOfNeG2_symm_ofIdx A hs i).symm

end

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type*) [Field K]

local notation "Nₖ" => D.weylSubgroup K
local notation "Hₖ" => Subgroup.subgroupOf (MonoidHom.range (D.torusPoints K)) Nₖ

private theorem quotientSection_weylProjection (hs : t ≠ .G2) (g : Nₖ) :
    D.quotientSection K hs (D.weylProjection K g) = QuotientGroup.mk' Hₖ g := by
  have hdense : Subgroup.closure ((D.weylSubgroup K).subtype ⁻¹'
      (Set.range (D.torusPoints K) ∪
        Set.range (fun i => D.weylElement (t.simpleIndex ht i) K 1))) = ⊤ := by
    rw [D.weylSubgroup_def]
    exact Subgroup.closure_preimage_eq_top _
  have hf : (D.quotientSection K hs).comp (D.weylProjection K) = QuotientGroup.mk' Hₖ := by
    apply MonoidHom.eq_of_eqOn_dense hdense
    rintro ⟨x, hx⟩ (⟨s, rfl⟩ | ⟨i, rfl⟩)
    · simp only [MonoidHom.comp_apply, D.weylProjection_torusPoints, map_one,
        QuotientGroup.mk'_apply]
      symm
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      exact ⟨s, rfl⟩
    · simp only [MonoidHom.comp_apply, D.weylProjection_weylElement,
        D.quotientSection_simple]
      rw [simpleClass, QuotientGroup.mk'_apply]
      -- Both lifts have the same underlying Weyl element; membership proofs are irrelevant.
      rfl
  exact DFunLike.congr_fun hf g

/-- Outside type G₂, the Weyl projection has kernel exactly the actual torus,
regarded as a subgroup of the subgroup generated by the torus and Weyl representatives. -/
theorem ker_weylProjection_of_ne_G2 (hs : t ≠ .G2) :
    (D.weylProjection K).ker = Hₖ := by
  ext g
  constructor
  · intro hg
    apply (QuotientGroup.eq_one_iff g).mp
    rw [← QuotientGroup.mk'_apply, ← D.quotientSection_weylProjection K hs g,
      MonoidHom.mem_ker.mp hg, map_one]
  · rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    rintro ⟨s, hsg⟩
    have hg : g = ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩ :=
      Subtype.ext hsg.symm
    rw [hg, MonoidHom.mem_ker, D.weylProjection_torusPoints]

/-- The Weyl quotient equivalence is induced by the native Weyl projection. -/
@[simp]
theorem weylQuotientEquivOfNeG2_mk (hs : t ≠ .G2) (g : Nₖ) :
    D.weylQuotientEquivOfNeG2 K hs (QuotientGroup.mk g) = D.weylProjection K g := by
  apply (D.weylQuotientEquivOfNeG2 K hs).eq_symm_apply.mp
  exact (D.quotientSection_weylProjection K hs g).symm

/-- The inverse Weyl quotient equivalence sends a Weyl projection to its quotient class. -/
@[simp]
theorem weylQuotientEquivOfNeG2_symm_weylProjection (hs : t ≠ .G2) (g : Nₖ) :
    (D.weylQuotientEquivOfNeG2 K hs).symm (D.weylProjection K g) =
      QuotientGroup.mk g := by
  apply (D.weylQuotientEquivOfNeG2 K hs).symm_apply_eq.mpr
  exact (D.weylQuotientEquivOfNeG2_mk K hs g).symm

end

end TauCeti.DynkinType.ChevalleyDatum
