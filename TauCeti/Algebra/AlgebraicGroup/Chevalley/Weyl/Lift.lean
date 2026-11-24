/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Coxeter
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Weyl
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coxeter

/-!
# The Coxeter lift to the Weyl-subgroup quotient of a Chevalley datum

For a Chevalley datum `D` of valid Dynkin type `t` over any commutative ring `A`, the pinned
simple Weyl representatives `nᵢ(1) = D.weylElement (t.simpleIndex ht i) A 1` satisfy
`nᵢ(1)² = αᵢ∨(-1) ∈ T_D(A)` (`ChevalleyDatum.weylElement_mul_self`), normalize the actual
torus `T_D(A) = (D.torusPoints A).range`
(`ChevalleyDatum.weylSubgroup_le_normalizer_range_torusPoints`), and satisfy the Artin--Tits
braid relations in `D.points A` (`ChevalleyDatum.weylWord_braidWord_eq`). Together with the
word factorization `ChevalleyDatum.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints`, this
gives a Coxeter-presentation description of the Weyl-subgroup quotient over every commutative ring.

Consequently, the assignment `sᵢ ↦ [nᵢ(1)]` extends via Tits' Coxeter presentation
(`DynkinType.simplyConnectedWeylCoxeterSystem`) to a surjective group homomorphism
`ChevalleyDatum.weylQuotientLift A : W →* D.weylSubgroup A ⧸ T_D(A)`, sending each reflection
`s_γ` to the coset `[n_γ(1)]` (and `[n_γ(s)]` for every unit `s : Aˣ`). Over a nontrivial
ring it is inverse to `ChevalleyDatum.weylSubgroupQuotientMulEquiv`
(`Chevalley.Weyl.Quotient`).

## Main definitions

* `TauCeti.DynkinType.ChevalleyDatum.weylQuotientLift`: the surjective homomorphism
  `W →* D.weylSubgroup A ⧸ ((D.torusPoints A).range).subgroupOf (D.weylSubgroup A)` over any
  commutative ring `A`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.mk_eq_one_iff_mem_range_torusPoints`: characterization of
  trivial cosets in `D.weylSubgroup A ⧸ T_D(A)`.
* `TauCeti.DynkinType.ChevalleyDatum.mk_weylElement_eq_mk_weylElement_one`: `[n_γ(s)] = [n_γ(1)]`
  in `D.weylSubgroup A ⧸ T_D(A)` for every root `γ` and unit `s`.
* `TauCeti.DynkinType.ChevalleyDatum.weylQuotientLift_ofIdx_simpleIndex`,
  `TauCeti.DynkinType.ChevalleyDatum.weylQuotientLift_ofIdx`, and
  `TauCeti.DynkinType.ChevalleyDatum.weylQuotientLift_simplyConnectedWeylWordProd`: values on
  simple reflections, root reflections, and Bourbaki-numbered Weyl words.
* `TauCeti.DynkinType.ChevalleyDatum.weylQuotientLift_surjective`: surjectivity of
  `weylQuotientLift` over any commutative ring `A`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 22.
* R. W. Carter, *Simple Groups of Lie Type*, §7.2.
-/

public noncomputable section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- A coset in `D.weylSubgroup A ⧸ T_D(A)` is trivial if and only if its representative lies in
the actual torus `(D.torusPoints A).range`. -/
theorem mk_eq_one_iff_mem_range_torusPoints (A : Type v) [CommRing A] (n : D.weylSubgroup A) :
    (QuotientGroup.mk n :
        D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A))) = 1 ↔
      (n : D.points A) ∈ (D.torusPoints A).range := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

private theorem isLiftable_weylQuotient (A : Type v) [CommRing A] :
    t.coxeterMatrix.IsLiftable (fun i : Fin t.rank =>
      (QuotientGroup.mk (D.simpleWeylLift A i) :
        D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A)))) := by
  let q := QuotientGroup.mk' (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A))
  refine (t.coxeterMatrix.isLiftable_iff (f := fun i => q (D.simpleWeylLift A i))).mpr
    ⟨fun i => ?_, fun i j => ?_⟩
  · rw [← map_mul, QuotientGroup.mk'_apply, D.mk_eq_one_iff_mem_range_torusPoints,
      Subgroup.coe_mul, D.coe_simpleWeylLift, D.weylElement_mul_self i A,
      D.simpleCorootPoints_eq_torusPoints]
    exact ⟨_, rfl⟩
  · have hsub : ((CoxeterSystem.braidWord t.coxeterMatrix i j).map (D.simpleWeylLift A)).prod =
        ((CoxeterSystem.braidWord t.coxeterMatrix j i).map (D.simpleWeylLift A)).prod := by
      rw [D.list_prod_map_simpleWeylLift, D.list_prod_map_simpleWeylLift]
      exact Subtype.ext (D.weylWord_braidWord_eq i j A)
    simpa only [map_list_prod, List.map_map, Function.comp_def] using congrArg q hsub

/-- **The Coxeter lift from the Weyl group to the Weyl-subgroup quotient.** Over every
commutative ring `A`, sending the `i`-th simple reflection to the coset of the pinned simple
Weyl representative `n_i(1)` extends uniquely to a group homomorphism from
`(t.simplyConnectedRootDatum ht).weylGroup` to the quotient of `D.weylSubgroup A` by the
actual torus `(D.torusPoints A).range`. -/
def weylQuotientLift (A : Type v) [CommRing A] :
    (t.simplyConnectedRootDatum ht).weylGroup →*
      D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A)) :=
  (t.simplyConnectedWeylCoxeterSystem ht).lift ⟨_, D.isLiftable_weylQuotient A⟩

/-- Modulo the actual torus, every point of the actual torus has trivial coset. -/
@[simp]
theorem mk_torusPoints_eq_one (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    (QuotientGroup.mk ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ :
        D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A))) = 1 :=
  (D.mk_eq_one_iff_mem_range_torusPoints A _).mpr ⟨s, rfl⟩

/-- Modulo the actual torus, every coroot point `h_γ(s)` has trivial coset. -/
@[simp]
theorem mk_corootPoints_eq_one (A : Type v) [CommRing A] (γ : Fin t.numRoots) (s : Aˣ) :
    (QuotientGroup.mk ⟨D.corootPoints γ A s, D.corootPoints_mem_weylSubgroup A γ s⟩ :
        D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A))) = 1 :=
  (D.mk_eq_one_iff_mem_range_torusPoints A _).mpr ⟨_, (D.corootPoints_apply γ A s).symm⟩

/-- Modulo the actual torus, every Steinberg Weyl representative `n_γ(s)` lies in the same coset
as `n_γ(1)`. -/
theorem mk_weylElement_eq_mk_weylElement_one (A : Type v) [CommRing A] (γ : Fin t.numRoots)
    (s : Aˣ) :
    (QuotientGroup.mk ⟨D.weylElement γ A s, D.weylElement_mem_weylSubgroup γ A s⟩ :
        D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A))) =
      QuotientGroup.mk
        ⟨D.weylElement γ A 1, D.weylElement_mem_weylSubgroup γ A 1⟩ := by
  have hfac :
      (⟨D.weylElement γ A s, D.weylElement_mem_weylSubgroup γ A s⟩ : D.weylSubgroup A) =
        ⟨D.corootPoints γ A s, D.corootPoints_mem_weylSubgroup A γ s⟩ *
          ⟨D.weylElement γ A 1, D.weylElement_mem_weylSubgroup γ A 1⟩ :=
    Subtype.ext (D.weylElement_eq_corootPoints_mul γ A s)
  rw [hfac, QuotientGroup.mk_mul, D.mk_corootPoints_eq_one, one_mul]

/-- Modulo the actual torus, conjugating the coset of `n_γ(s)` by the coset of a pinned simple
Weyl representative `n_i(1)` produces the coset of `n_{s_i γ}(1)`. -/
theorem mk_weylElement_simpleIndex_conj (A : Type v) [CommRing A]
    (i : Fin t.rank) (γ : Fin t.numRoots) (s : Aˣ) :
    (QuotientGroup.mk (D.simpleWeylLift A i) :
        D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A))) *
      QuotientGroup.mk ⟨D.weylElement γ A s, D.weylElement_mem_weylSubgroup γ A s⟩ *
      (QuotientGroup.mk (D.simpleWeylLift A i))⁻¹ =
      QuotientGroup.mk
        ⟨D.weylElement ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ) A 1,
          D.weylElement_mem_weylSubgroup _ A 1⟩ := by
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  have hweyl :
      D.simpleWeylLift A i *
        ⟨D.weylElement γ A s, D.weylElement_mem_weylSubgroup γ A s⟩ *
        (D.simpleWeylLift A i)⁻¹ =
        ⟨D.weylElement ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ) A _,
          D.weylElement_mem_weylSubgroup _ A _⟩ :=
    Subtype.ext (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, D.coe_simpleWeylLift] using
        D.weylElement_conj_weylElement i γ A s)
  rw [hweyl, D.mk_weylElement_eq_mk_weylElement_one]

/-- `weylQuotientLift` sends each simple reflection `s_i` to the coset of `D.simpleWeylLift A i`.
-/
@[simp high]
theorem weylQuotientLift_ofIdx_simpleIndex (A : Type v) [CommRing A] (i : Fin t.rank) :
    D.weylQuotientLift A
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      QuotientGroup.mk (D.simpleWeylLift A i) := by
  rw [weylQuotientLift, ← t.simplyConnectedWeylCoxeterSystem_simple ht i,
    CoxeterSystem.lift_apply_simple]

/-- `weylQuotientLift` sends each root reflection `s_γ` to the coset of the Steinberg Weyl
representative `n_γ(1)`. -/
@[simp]
theorem weylQuotientLift_ofIdx (A : Type v) [CommRing A] (γ : Fin t.numRoots) :
    D.weylQuotientLift A
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ) =
      QuotientGroup.mk
        ⟨D.weylElement γ A 1, D.weylElement_mem_weylSubgroup γ A 1⟩ := by
  induction γ using (t.rationalBase ht).induction_simple_reflect with
  | h₁ γ hγ =>
    obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hγ
    rw [D.weylQuotientLift_ofIdx_simpleIndex A i, D.mk_weylElement_eq_simpleWeylLift]
  | h₂ γ j ih hj =>
    obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hj
    rw [t.reflectionPerm_rationalRootSystem ht]
    have hconj_w :
        RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
            ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ) =
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) *
            RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ *
            (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
              (t.simpleIndex ht i))⁻¹ := by
      simpa only [RootPairing.weylGroupToPerm_ofIdx_apply] using
        RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj (t.simplyConnectedRootDatum ht)
          (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) γ
    rw [hconj_w, map_mul, map_mul, map_inv, D.weylQuotientLift_ofIdx_simpleIndex A i, ih,
      D.mk_weylElement_simpleIndex_conj]

/-- `weylQuotientLift` sends the Weyl element spelled by a node word `l` to the coset of the
corresponding product of pinned simple Weyl representatives. -/
@[simp]
theorem weylQuotientLift_simplyConnectedWeylWordProd (A : Type v) [CommRing A]
    (l : List (Fin t.rank)) :
    D.weylQuotientLift A (t.simplyConnectedWeylWordProd ht l) =
      QuotientGroup.mk ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod,
        D.list_prod_map_weylElement_mem_weylSubgroup A l⟩ := by
  have hqprod :
      (l.map fun i =>
          (QuotientGroup.mk (D.simpleWeylLift A i) :
            D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A)))).prod =
        QuotientGroup.mk (l.map (D.simpleWeylLift A)).prod := by
    simp only [← QuotientGroup.mk'_apply, map_list_prod, List.map_map, Function.comp_def]
  rw [← t.simplyConnectedWeylCoxeterSystem_wordProd ht l, CoxeterSystem.wordProd, map_list_prod,
    List.map_map]
  simp only [Function.comp_def, t.simplyConnectedWeylCoxeterSystem_simple ht,
    D.weylQuotientLift_ofIdx_simpleIndex A]
  rw [hqprod, D.list_prod_map_simpleWeylLift]

/-- `weylQuotientLift` is surjective over every commutative ring `A`. -/
theorem weylQuotientLift_surjective (A : Type v) [CommRing A] :
    Function.Surjective (D.weylQuotientLift A) := by
  intro x
  obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨l, s, rfl⟩ := (D.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints A).mp hg
  refine ⟨t.simplyConnectedWeylWordProd ht l, ?_⟩
  have hfac : (⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.torusPoints A s,
      hg⟩ : D.weylSubgroup A) =
      ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod,
        D.list_prod_map_weylElement_mem_weylSubgroup A l⟩ *
        ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ := Subtype.ext (by simp)
  rw [D.weylQuotientLift_simplyConnectedWeylWordProd A l, hfac, QuotientGroup.mk_mul,
    D.mk_torusPoints_eq_one, mul_one]

end TauCeti.DynkinType.ChevalleyDatum
