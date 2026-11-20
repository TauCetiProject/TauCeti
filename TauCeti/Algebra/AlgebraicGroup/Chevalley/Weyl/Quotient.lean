/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.DoubleBond
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Orthogonal
import TauCeti.Algebra.Group.Pow
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coefficient
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# The Weyl quotient of Chevalley data

For every Chevalley datum of type other than G₂ over a nontrivial commutative ring,
the quotient of `weylSubgroup` by its actual character-lattice torus is the Weyl group of
the pinned root datum. The equivalence sends the class of each pinned simple Weyl
representative to its simple reflection. Over a field, the kernel of the native Weyl
projection is exactly that torus.

The Coxeter-presentation argument uses the native rank-one square, single-bond and double-bond
braid relations outside type G₂. For every valid Dynkin type including G₂ over an arbitrary
commutative ring `A`, conjugating Steinberg's Weyl element `n_γ(s)` by `n_{αᵢ}(1)` produces
`n_{sᵢ γ}(ε s)` (`weylElement_conj_weylElement`), so `D.weylSubgroup A` contains `n_γ(s)` for
every root `γ` and unit `s` (`weylElement_mem_weylSubgroup_of_root`). Adapting the strong-exchange
word-deletion and identity inductions of `TauCeti.exists_wordProd_eraseIdx_eq_mul_ofIdx` and
`TauCeti.eq_one_of_inversions_eq_empty` from
`TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange` shows that any word of simple Weyl
representatives spelling `1` in the Weyl group lies in the actual torus `T_D(A)`
(`weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one`).

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19–22 and Chapter 6.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. III, §10.3.
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

section AllTypes

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- **Steinberg's Weyl element `n_γ(s)` lies in `D.weylSubgroup A` for every root `γ` and unit
`s`**, over every commutative ring `A`. -/
theorem weylElement_mem_weylSubgroup_of_root (γ : Fin t.numRoots) (A : Type v) [CommRing A]
    (s : Aˣ) : D.weylElement γ A s ∈ D.weylSubgroup A := by
  revert s
  refine (t.rationalBase ht).induction_simple_reflect γ
    (p := fun k => ∀ s : Aˣ, D.weylElement k A s ∈ D.weylSubgroup A)
    (fun k hk s => ?_) (fun k j hk hj s => ?_)
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hk
    rw [D.weylElement_eq_corootPoints_mul, ← D.simpleCorootPoints_eq_corootPoints,
      D.simpleCorootPoints_eq_torusPoints]
    exact Subgroup.mul_mem _ (D.torusPoints_mem_weylSubgroup A _)
      (D.weylElement_mem_weylSubgroup A i)
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hj
    rw [t.reflectionPerm_rationalRootSystem ht]
    let εA : Aˣ := Units.map (Int.castRingHom A).toMonoidHom
      (t.chevalleyWeylSign ht (t.simpleIndex ht i) k)
    have hconj := D.weylElement_conj_weylElement i k A (εA⁻¹ * s)
    rw [mul_inv_cancel_left] at hconj
    rw [← hconj]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (D.weylElement_mem_weylSubgroup A i) (hk _))
      (Subgroup.inv_mem _ (D.weylElement_mem_weylSubgroup A i))

/-- **Over a field, Steinberg's Weyl element `n_γ(s)` of any root `γ` projects to the reflection
`s_γ` in the Weyl group.** -/
-- Concrete Dynkin-type rules can normalize root indices inside `Subtype.mk` before matching.
@[simp↓]
theorem weylProjection_weylElement_of_root (k : Type v) [Field k] (γ : Fin t.numRoots) (s : kˣ) :
    D.weylProjection k ⟨D.weylElement γ k s, D.weylElement_mem_weylSubgroup_of_root γ k s⟩ =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ := by
  revert s
  refine (t.rationalBase ht).induction_simple_reflect γ
    (p := fun γ => ∀ s : kˣ,
      D.weylProjection k
          ⟨D.weylElement γ k s, D.weylElement_mem_weylSubgroup_of_root γ k s⟩ =
        RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ)
    (fun γ hγ s => ?_) (fun γ j hγ hj s => ?_)
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hγ
    have hsub :
        (⟨D.weylElement (t.simpleIndex ht i) k s,
            D.weylElement_mem_weylSubgroup_of_root _ k s⟩ : D.weylSubgroup k) =
          ⟨D.torusPoints k (D.simpleCorootParameter i k s),
            D.torusPoints_mem_weylSubgroup k _⟩ *
          ⟨D.weylElement (t.simpleIndex ht i) k 1, D.weylElement_mem_weylSubgroup k i⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      exact (D.weylElement_eq_corootPoints_mul (t.simpleIndex ht i) k s).trans <| by
        rw [← D.simpleCorootPoints_eq_corootPoints, D.simpleCorootPoints_eq_torusPoints]
    rw [hsub, map_mul, D.weylProjection_torusPoints, one_mul, D.weylProjection_weylElement]
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hj
    rw [t.reflectionPerm_rationalRootSystem ht]
    let εk : kˣ := Units.map (Int.castRingHom k).toMonoidHom
      (t.chevalleyWeylSign ht (t.simpleIndex ht i) γ)
    have hconj := D.weylElement_conj_weylElement i γ k (εk⁻¹ * s)
    rw [mul_inv_cancel_left] at hconj
    have hsub :
        (⟨D.weylElement
            ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ) k s,
            D.weylElement_mem_weylSubgroup_of_root _ k s⟩ : D.weylSubgroup k) =
          ⟨D.weylElement (t.simpleIndex ht i) k 1, D.weylElement_mem_weylSubgroup k i⟩ *
          ⟨D.weylElement γ k (εk⁻¹ * s), D.weylElement_mem_weylSubgroup_of_root γ k _⟩ *
          (⟨D.weylElement (t.simpleIndex ht i) k 1, D.weylElement_mem_weylSubgroup k i⟩)⁻¹ :=
      Subtype.ext hconj.symm
    rw [hsub, map_mul, map_mul, map_inv, D.weylProjection_weylElement, hγ,
      ← RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj,
      RootPairing.weylGroupToPerm_ofIdx_apply]

private theorem exists_unit_weylWord_conj_weylElement (A : Type v) [CommRing A]
    (l : List (Fin t.rank)) (γ : Fin t.numRoots) (s : Aˣ) :
    ∃ s' : Aˣ,
      (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.weylElement γ A s *
          ((l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod)⁻¹ =
        D.weylElement
          ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l) γ) A s' := by
  induction l generalizing γ s with
  | nil => exact ⟨s, by simp⟩
  | cons i l ih =>
    obtain ⟨s₁, hs₁⟩ := ih γ s
    refine ⟨Units.map (Int.castRingHom A).toMonoidHom
      (t.chevalleyWeylSign ht (t.simpleIndex ht i)
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm
          (t.geckWeylWordProd ht l) γ)) * s₁, ?_⟩
    rw [List.map_cons, List.prod_cons, mul_inv_rev, geckWeylWordProd_cons,
      RootPairing.weylGroupToPerm_ofIdx_mul_apply]
    calc
      D.weylElement (t.simpleIndex ht i) A 1 *
            (l.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod *
            D.weylElement γ A s *
            (((l.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod)⁻¹ *
              (D.weylElement (t.simpleIndex ht i) A 1)⁻¹)
          = D.weylElement (t.simpleIndex ht i) A 1 *
              ((l.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod *
                D.weylElement γ A s *
                ((l.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod)⁻¹) *
              (D.weylElement (t.simpleIndex ht i) A 1)⁻¹ := by group
      _ = _ := by rw [hs₁, D.weylElement_conj_weylElement]

/-- Head-deletion step for `exists_eraseIdx_weylWord_mul_weylElement` when the first inversion
occurs at the leading letter `j`. -/
private theorem exists_eraseIdx_weylWord_mul_weylElement_head (A : Type v) [CommRing A]
    {γ : Fin t.numRoots} (j : Fin t.rank) (l : List (Fin t.rank))
    (hpos : (t.simplyConnectedBase ht).IsPos
      ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l) γ))
    (hneg : ¬(t.simplyConnectedBase ht).IsPos
      ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht j)
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l) γ))) :
    t.geckWeylWordProd ht l =
        t.geckWeylWordProd ht (j :: l) *
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ ∧
      ∃ r : Fin t.rank → Aˣ,
        ((j :: l).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod *
            D.weylElement γ A 1 =
          D.torusPoints A r *
            (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  let P := t.simplyConnectedRootDatum ht
  let b := t.simplyConnectedBase ht
  have hkey : P.weylGroupToPerm (t.geckWeylWordProd ht l) γ = t.simpleIndex ht j := by
    by_contra hne
    have hmem : P.weylGroupToPerm (t.geckWeylWordProd ht l) γ ∈
        posRoots P b \ {t.simpleIndex ht j} :=
      ⟨(mem_posRoots P b _).mpr hpos, hne⟩
    have hjmem : t.simpleIndex ht j ∈ b.support := by
      rw [← support_rationalBase]
      exact simpleIndex_mem_support j
    exact hneg ((mem_posRoots P b _).mp
      ((reflectionPerm_mem_posRoots_diff_singleton_iff P b hjmem _).mpr hmem).1)
  refine ⟨?_, ?_⟩
  · rw [geckWeylWordProd_cons, ← hkey, RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj,
      inv_mul_cancel_right, mul_assoc, RootPairing.weylGroup.ofIdx_mul_self, mul_one]
  · obtain ⟨s', hs'⟩ := D.exists_unit_weylWord_conj_weylElement A l γ 1
    rw [hkey, D.weylElement_eq_corootPoints_mul (t.simpleIndex ht j) A s',
      ← D.simpleCorootPoints_eq_corootPoints, D.simpleCorootPoints_eq_torusPoints] at hs'
    have hW :
        (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.weylElement γ A 1 =
          D.torusPoints A (D.simpleCorootParameter j A s') *
            D.weylElement (t.simpleIndex ht j) A 1 *
            (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod :=
      mul_inv_eq_iff_eq_mul.mp hs'
    refine ⟨D.simpleReflectionTorusParameter j A (D.simpleCorootParameter j A s') *
        D.simpleCorootParameter j A (-1), ?_⟩
    rw [List.map_cons, List.prod_cons, mul_assoc, hW, map_mul,
      ← D.simpleCorootPoints_eq_torusPoints j A (-1), ← D.weylElement_mul_self,
      ← D.weylElement_conj_torusPoints]
    group

/-- **Strong-exchange shortening of Weyl words in `D.points A`.** If `l` spells a Weyl element
sending a positive root `γ` to a negative root, multiplying the lifted word on the right by
`n_γ(1)` deletes a letter from `l` up to a left factor in the actual torus `T_D(A)`. -/
private theorem exists_eraseIdx_weylWord_mul_weylElement (A : Type v) [CommRing A]
    {γ : Fin t.numRoots} (hγ : (t.simplyConnectedBase ht).IsPos γ) (l : List (Fin t.rank))
    (h : ¬(t.simplyConnectedBase ht).IsPos
      ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l) γ)) :
    ∃ p < l.length,
      t.geckWeylWordProd ht (l.eraseIdx p) =
        t.geckWeylWordProd ht l *
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ ∧
      ∃ r : Fin t.rank → Aˣ,
        (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.weylElement γ A 1 =
          D.torusPoints A r *
            ((l.eraseIdx p).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod := by
  induction l with
  | nil => exact absurd (by simpa using hγ) h
  | cons j l ih =>
    rw [geckWeylWordProd_cons, RootPairing.weylGroupToPerm_ofIdx_mul_apply] at h
    by_cases hpos : (t.simplyConnectedBase ht).IsPos
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l) γ)
    · obtain ⟨hw, r, hr⟩ := D.exists_eraseIdx_weylWord_mul_weylElement_head A j l hpos h
      exact ⟨0, by simp, hw, r, hr⟩
    · obtain ⟨p, hp, hw, r, hr⟩ := ih hpos
      refine ⟨p + 1, by simpa using hp, ?_, D.simpleReflectionTorusParameter j A r, ?_⟩
      · rw [List.eraseIdx_cons_succ, geckWeylWordProd_cons, hw, geckWeylWordProd_cons, mul_assoc]
      · rw [List.eraseIdx_cons_succ, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
          mul_assoc, hr, ← D.weylElement_conj_torusPoints]
        group

/-- **Any word of simple Weyl representatives spelling `1` in the Weyl group lies in the actual
torus `T_D(A)`**, over an arbitrary commutative ring `A` and for every valid Dynkin type. -/
theorem weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one (A : Type v) [CommRing A]
    (l : List (Fin t.rank)) (hl : t.geckWeylWordProd ht l = 1) :
    (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈ (D.torusPoints A).range := by
  let P := t.simplyConnectedRootDatum ht
  let b := t.simplyConnectedBase ht
  suffices ∀ n (l' : List (Fin t.rank)), l'.length = n → t.geckWeylWordProd ht l' = 1 →
      (l'.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈ (D.torusPoints A).range from
    this l.length l rfl hl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l' hlen hl'
    rcases List.eq_nil_or_concat l' with rfl | ⟨l₁, k, rfl⟩
    · exact ⟨1, by simp⟩
    · rw [List.concat_eq_append, geckWeylWordProd_append, geckWeylWordProd_cons,
        geckWeylWordProd_nil, mul_one] at hl'
      have hl₁ :
          t.geckWeylWordProd ht l₁ = RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k) := by
        calc
          t.geckWeylWordProd ht l₁
              = t.geckWeylWordProd ht l₁ *
                  (RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k) *
                    RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k)) := by
                rw [RootPairing.weylGroup.ofIdx_mul_self, mul_one]
          _ = (t.geckWeylWordProd ht l₁ * RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k)) *
                RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k) := (mul_assoc _ _ _).symm
          _ = RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k) := by rw [hl', one_mul]
      have hkpos : b.IsPos (t.simpleIndex ht k) := by
        rw [← mem_posRoots, ← posRoots_rationalRootSystem]
        exact simpleIndex_mem_posRoots k
      have hkneg :
          ¬b.IsPos (P.weylGroupToPerm (t.geckWeylWordProd ht l₁) (t.simpleIndex ht k)) := by
        rw [hl₁, RootPairing.weylGroupToPerm_ofIdx_apply, ← mem_posRoots]
        exact reflectionPerm_self_notMem_posRoots P b ((mem_posRoots P b _).mpr hkpos)
      obtain ⟨p, hp, hwp, r, hr⟩ :=
        D.exists_eraseIdx_weylWord_mul_weylElement A hkpos l₁ hkneg
      have hlen_lt : (l₁.eraseIdx p).length < n := by
        have hlen' := List.length_eraseIdx_add_one hp
        rw [← hlen, List.concat_eq_append, List.length_append]
        omega
      obtain ⟨s, hs⟩ := ih _ hlen_lt (l₁.eraseIdx p) rfl (hwp.trans hl')
      rw [List.concat_eq_append, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, hr, ← hs, ← map_mul]
      exact ⟨r * s, rfl⟩

end AllTypes

end TauCeti.DynkinType.ChevalleyDatum
