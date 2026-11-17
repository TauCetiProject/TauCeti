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
import TauCeti.Algebra.Group.Pow
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

private theorem simpleClass_prod_eq (l l' : List (Fin t.rank))
    (h : (l.map (fun i => D.weylElement (t.simpleIndex ht i) A 1)).prod =
      (l'.map (fun i => D.weylElement (t.simpleIndex ht i) A 1)).prod) :
    (l.map (D.simpleClass A)).prod = (l'.map (D.simpleClass A)).prod := by
  have h' : (l.map (D.simpleLift A)).prod = (l'.map (D.simpleLift A)).prod := by
    apply Subtype.ext
    simpa only [Subgroup.val_list_prod, List.map_map, simpleLift, Function.comp_def] using h
  unfold simpleClass
  simpa only [map_list_prod, List.map_map, Function.comp_def, QuotientGroup.mk'_apply]
    using congrArg (QuotientGroup.mk' H) h'

private theorem simpleClass_commute (i j : Fin t.rank) (hij : t.cartanMatrix i j = 0) :
    Commute (D.simpleClass A i) (D.simpleClass A j) := by
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    commute_iff_eq] using
    D.simpleClass_prod_eq A [i, j] [j, i]
      (by simpa using (D.commute_weylElement_simpleIndex A i j hij 1 1).eq)

private theorem simpleClass_braid (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1) :
    D.simpleClass A i * D.simpleClass A j * D.simpleClass A i =
      D.simpleClass A j * D.simpleClass A i * D.simpleClass A j := by
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_assoc] using
    D.simpleClass_prod_eq A [i, j, i] [j, i, j]
      (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, mul_assoc] using
        D.weylElement_braid_of_cartanMatrix_eq_neg_one i j hij hji A)

private theorem simpleClass_pow_three (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1) :
    (D.simpleClass A i * D.simpleClass A j) ^ 3 = 1 := by
  exact mul_pow_three_eq_one_of_braid (D.simpleClass_mul_self A i)
    (D.simpleClass_mul_self A j) (D.simpleClass_braid A i j hij hji)

private theorem simpleClass_pow_four (i j : Fin t.rank)
    (hji : t.cartanMatrix j i = -2) :
    (D.simpleClass A i * D.simpleClass A j) ^ 4 = 1 := by
  have hb : (D.simpleClass A i * D.simpleClass A j) ^ 2 =
      (D.simpleClass A j * D.simpleClass A i) ^ 2 := by
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      pow_two, mul_assoc] using
      D.simpleClass_prod_eq A [i, j, i, j] [j, i, j, i]
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, mul_assoc] using
          D.weylElement_braid_of_cartanMatrix_eq_neg_two i j hji A)
  exact mul_pow_four_eq_one_of_sq_eq_sq (D.simpleClass_mul_self A i)
    (D.simpleClass_mul_self A j) hb

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
    apply mul_right_cancel (b := D.simpleClass A i)
    rw [one_mul, mul_pow_mul, D.simpleClass_pow_four A j i hij, mul_one]

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

private theorem closure_weylSubgroup_generators :
    Subgroup.closure ((D.weylSubgroup A).subtype ⁻¹'
      (Set.range (D.torusPoints A) ∪
        Set.range (fun i => D.weylElement (t.simpleIndex ht i) A 1))) = ⊤ := by
  rw [D.weylSubgroup_def]
  exact Subgroup.closure_preimage_eq_top _

private theorem mk_torusPoints (s : Fin t.rank → Aˣ)
    (hx : D.torusPoints A s ∈ N) :
    (QuotientGroup.mk ⟨D.torusPoints A s, hx⟩ : Q) = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  exact ⟨s, rfl⟩

private theorem quotientSection_surjective (hs : t ≠ .G2) :
    Function.Surjective (D.quotientSection A hs) := by
  have hrange : (D.quotientSection A hs).range.comap (QuotientGroup.mk' H) = ⊤ := by
    apply top_unique
    rw [← D.closure_weylSubgroup_generators A, Subgroup.closure_le]
    rintro ⟨x, hx⟩ (⟨s, rfl⟩ | ⟨i, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply,
        D.mk_torusPoints A s hx, MonoidHom.mem_range]
      exact ⟨1, map_one _⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply,
        MonoidHom.mem_range]
      exact ⟨_, D.quotientSection_simple A hs i⟩
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
  have hg : g ∈ (D.quotientSection A hs).range.comap (QuotientGroup.mk' H) := by
    rw [hrange]
    trivial
  rw [Subgroup.mem_comap, MonoidHom.mem_range] at hg
  exact hg

private theorem quotientSection_injective [Nontrivial A] (hs : t ≠ .G2) :
    Function.Injective (D.quotientSection A hs) := by
  -- A residue field detects the Weyl word, without requiring a projection over rings.
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let : M.IsMaximal := hM
  let := Ideal.Quotient.field M
  have hker : H ≤ ((D.weylProjection (A ⧸ M)).comp
      (D.weylSubgroupMap A (Ideal.Quotient.mk M))).ker := by
    intro g hg
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at hg
    obtain ⟨s, hsg⟩ := hg
    have hg : g = ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ :=
      Subtype.ext hsg.symm
    rw [hg, MonoidHom.mem_ker, MonoidHom.comp_apply, D.weylSubgroupMap_torusPoints,
      D.weylProjection_torusPoints]
  let p : Q →* (t.simplyConnectedRootDatum ht).weylGroup :=
    QuotientGroup.lift H ((D.weylProjection (A ⧸ M)).comp
      (D.weylSubgroupMap A (Ideal.Quotient.mk M))) hker
  -- The descended map is a left inverse, as can be checked on simple reflections.
  have hp : p.comp (D.quotientSection A hs) = MonoidHom.id _ := by
    apply (weylCoxeterSystem (t.simplyConnectedRootDatum ht)
      (t.simplyConnectedBase ht)).ext_simple
    intro a
    obtain ⟨i, rfl⟩ := (t.simpleSupportEquivSimplyConnectedBase ht).surjective a
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, weylCoxeterSystem_simple,
      coe_simpleSupportEquivSimplyConnectedBase, D.quotientSection_simple,
      simpleClass, p, QuotientGroup.lift_mk']
    rw [simpleLift, D.weylSubgroupMap_weylElement, D.weylProjection_weylElement]
  exact Function.LeftInverse.injective (g := p) fun w => by
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using DFunLike.congr_fun hp w

/-- The quotient of a Chevalley datum's Weyl subgroup by its actual torus is the Weyl
group of the pinned root datum, over every nontrivial commutative ring, outside type G₂. -/
def weylQuotientEquivOfNeG2 [Nontrivial A] (hs : t ≠ .G2) :
    Q ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  (MulEquiv.ofBijective (D.quotientSection A hs)
    ⟨D.quotientSection_injective A hs, D.quotientSection_surjective A hs⟩).symm

private theorem weylQuotientEquivOfNeG2_symm_apply [Nontrivial A] (hs : t ≠ .G2)
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    (D.weylQuotientEquivOfNeG2 A hs).symm w = D.quotientSection A hs w := by
  rw [weylQuotientEquivOfNeG2, MulEquiv.symm_symm]
  exact MulEquiv.ofBijective_apply _ _ _

/-- The inverse Weyl quotient equivalence sends a pinned simple reflection to the class
of its pinned Weyl representative. -/
@[simp↓]
theorem weylQuotientEquivOfNeG2_symm_ofIdx [Nontrivial A] (hs : t ≠ .G2)
    (i : Fin t.rank) :
    (D.weylQuotientEquivOfNeG2 A hs).symm
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      QuotientGroup.mk
        ⟨D.weylElement (t.simpleIndex ht i) A 1, D.weylElement_mem_weylSubgroup A i⟩ := by
  rw [D.weylQuotientEquivOfNeG2_symm_apply, D.quotientSection_simple, simpleClass,
    simpleLift]

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

private theorem quotientSection_comp_weylProjection (hs : t ≠ .G2) :
    (D.quotientSection K hs).comp (D.weylProjection K) = QuotientGroup.mk' Hₖ := by
  apply MonoidHom.eq_of_eqOn_dense (D.closure_weylSubgroup_generators K)
  rintro ⟨x, hx⟩ (⟨s, rfl⟩ | ⟨i, rfl⟩)
  · simp only [MonoidHom.comp_apply, D.weylProjection_torusPoints, map_one,
      QuotientGroup.mk'_apply, D.mk_torusPoints]
  · simp only [MonoidHom.comp_apply, D.weylProjection_weylElement,
      D.quotientSection_simple]
    rw [simpleClass, QuotientGroup.mk'_apply]
    -- Both lifts have the same underlying Weyl element; membership proofs are irrelevant.
    rfl

/-- Outside type G₂, the Weyl projection has kernel exactly the actual torus,
regarded as a subgroup of the subgroup generated by the torus and Weyl representatives. -/
theorem ker_weylProjection_of_ne_G2 (hs : t ≠ .G2) :
    (D.weylProjection K).ker = Hₖ := by
  rw [← MonoidHom.ker_comp_of_injective (D.weylProjection K) (D.quotientSection K hs)
    (D.quotientSection_injective K hs), D.quotientSection_comp_weylProjection K hs,
    QuotientGroup.ker_mk']

/-- The inverse Weyl quotient equivalence sends a Weyl projection to its quotient class. -/
@[simp]
theorem weylQuotientEquivOfNeG2_symm_weylProjection (hs : t ≠ .G2) (g : Nₖ) :
    (D.weylQuotientEquivOfNeG2 K hs).symm (D.weylProjection K g) =
      QuotientGroup.mk g := by
  rw [D.weylQuotientEquivOfNeG2_symm_apply, ← MonoidHom.comp_apply,
    D.quotientSection_comp_weylProjection, QuotientGroup.mk'_apply]

/-- The Weyl quotient equivalence is induced by the native Weyl projection. -/
@[simp]
theorem weylQuotientEquivOfNeG2_mk (hs : t ≠ .G2) (g : Nₖ) :
    D.weylQuotientEquivOfNeG2 K hs (QuotientGroup.mk g) = D.weylProjection K g := by
  apply (D.weylQuotientEquivOfNeG2 K hs).eq_symm_apply.mp
  exact (D.weylQuotientEquivOfNeG2_symm_weylProjection K hs g).symm

end

end TauCeti.DynkinType.ChevalleyDatum
