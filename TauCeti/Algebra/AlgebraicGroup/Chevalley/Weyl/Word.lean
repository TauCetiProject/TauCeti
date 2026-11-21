/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Coxeter
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.GroupTheory.Coxeter.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coxeter

/-!
# Weyl-word decomposition and Coxeter lift for Chevalley data

For a Chevalley datum `D` of valid Dynkin type `t` over any commutative ring `A`, the pinned
simple Weyl representatives `nᵢ(1) = D.weylElement (t.simpleIndex ht i) A 1` satisfy
`nᵢ(1)² = αᵢ∨(-1) ∈ T_D(A)` (`ChevalleyDatum.weylElement_mul_self`), normalize the actual
torus `T_D(A) = (D.torusPoints A).range`
(`ChevalleyDatum.weylSubgroup_le_normalizer_range_torusPoints`), and satisfy the Artin--Tits
braid relations in `D.points A` (`ChevalleyDatum.weylWord_braidWord_eq`).

Consequently:
1. Every element of `D.weylSubgroup A` decomposes as a positive word in the pinned simple Weyl
   representatives followed by an actual torus point
   (`ChevalleyDatum.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints`).
2. The assignment `sᵢ ↦ [nᵢ(1)]` extends via Tits' Coxeter presentation
   (`DynkinType.simplyConnectedWeylCoxeterSystem`) to a surjective group homomorphism
   `ChevalleyDatum.weylQuotientLift A : W →* D.weylSubgroup A ⧸ T_D(A)`.
3. Any word in the pinned simple Weyl representatives spelling `1` in `W` lies in `T_D(A)`
   (`ChevalleyDatum.weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one`).

## Main definitions

* `TauCeti.DynkinType.ChevalleyDatum.weylQuotientLift`: the surjective homomorphism
  `W →* D.weylSubgroup A ⧸ ((D.torusPoints A).range).subgroupOf (D.weylSubgroup A)` over any
  commutative ring `A`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints`:
  word factorization of `D.weylSubgroup A`.
* `TauCeti.DynkinType.ChevalleyDatum.weylQuotientLift_surjective`: surjectivity of
  `weylQuotientLift` over any commutative ring `A`.
* `TauCeti.DynkinType.ChevalleyDatum.weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one`:
  words spelling `1` in `W` evaluate into `(D.torusPoints A).range`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 22.
* R. W. Carter, *Simple Groups of Lie Type*, §7.2.
-/

public noncomputable section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Every element of `D.weylSubgroup A` is a positive word in the pinned simple Weyl
representatives followed by a point of the actual torus, over every commutative ring. -/
theorem mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints (A : Type v) [CommRing A]
    {g : D.points A} :
    g ∈ D.weylSubgroup A ↔
      ∃ (l : List (Fin t.rank)) (s : Fin t.rank → Aˣ),
        (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod *
          D.torusPoints A s = g := by
  let r : Fin t.rank → D.points A := fun i => D.weylElement (t.simpleIndex ht i) A 1
  have htorus_mul (s₀ : Fin t.rank → Aˣ) (l : List (Fin t.rank)) (s : Fin t.rank → Aˣ) :
      ∃ s' : Fin t.rank → Aˣ,
        D.torusPoints A s₀ * ((l.map r).prod * D.torusPoints A s) =
          (l.map r).prod * D.torusPoints A s' := by
    have hnorm := D.weylSubgroup_le_normalizer_range_torusPoints A
      (inv_mem (D.list_prod_map_weylElement_mem_weylSubgroup A l))
    obtain ⟨s₁, hs₁⟩ := (Subgroup.mem_normalizer_iff.mp hnorm (D.torusPoints A s₀)).mp
      ⟨s₀, rfl⟩
    refine ⟨s₁ * s, ?_⟩
    have hcomm : D.torusPoints A s₀ * (l.map r).prod = (l.map r).prod * D.torusPoints A s₁ := by
      rw [hs₁]
      dsimp only [r]
      group
    rw [← mul_assoc, hcomm, mul_assoc, (D.torusPoints A).map_mul]
  constructor
  · intro hg
    rw [D.weylSubgroup_def] at hg
    induction hg using Subgroup.closure_induction_left with
    | one =>
      exact ⟨[], 1, by simp⟩
    | mul_left x hx y _ ih =>
      obtain ⟨l, s, rfl⟩ := ih
      rcases hx with ⟨s₀, rfl⟩ | ⟨i, rfl⟩
      · obtain ⟨s', hs'⟩ := htorus_mul s₀ l s
        exact ⟨l, s', hs'.symm⟩
      · exact ⟨i :: l, s, by simp [mul_assoc]⟩
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨l, s, rfl⟩ := ih
      rcases hx with ⟨s₀, rfl⟩ | ⟨i, rfl⟩
      · rw [← map_inv]
        obtain ⟨s', hs'⟩ := htorus_mul s₀⁻¹ l s
        exact ⟨l, s', hs'.symm⟩
      · have hri_inv : (r i)⁻¹ =
            r i * D.torusPoints A (D.simpleCorootParameter i A (-1))⁻¹ := by
          apply inv_eq_of_mul_eq_one_right
          rw [← mul_assoc, D.weylElement_mul_self i A, D.simpleCorootPoints_eq_torusPoints,
            ← (D.torusPoints A).map_mul, mul_inv_cancel, map_one]
        rw [hri_inv, mul_assoc]
        obtain ⟨s', hs'⟩ := htorus_mul (D.simpleCorootParameter i A (-1))⁻¹ l s
        refine ⟨i :: l, s', ?_⟩
        dsimp only [r] at hs' ⊢
        simp only [List.map_cons, List.prod_cons, mul_assoc]
        rw [← hs']
  · rintro ⟨l, s, rfl⟩
    exact mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup A l)
      (D.torusPoints_mem_weylSubgroup A s)

private theorem isLiftable_weylQuotient (A : Type v) [CommRing A] :
    t.coxeterMatrix.IsLiftable (fun i : Fin t.rank =>
      (QuotientGroup.mk
        ⟨D.weylElement (t.simpleIndex ht i) A 1, D.weylElement_mem_weylSubgroup A i⟩ :
        D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A)))) := by
  let n_sub (k : Fin t.rank) : D.weylSubgroup A :=
    ⟨D.weylElement (t.simpleIndex ht k) A 1, D.weylElement_mem_weylSubgroup A k⟩
  let q := QuotientGroup.mk' (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A))
  have hcoe (l : List (Fin t.rank)) :
      ((l.map n_sub).prod : D.points A) =
        (l.map fun k => D.weylElement (t.simpleIndex ht k) A 1).prod := by
    simpa only [Subgroup.coe_subtype, List.map_map, Function.comp_def] using
      (D.weylSubgroup A).subtype.map_list_prod (l.map n_sub)
  apply t.coxeterMatrix.isLiftable_of_mul_self_of_braidWord (f := fun i => q (n_sub i))
  · intro i
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, D.weylElement_mul_self i A, D.simpleCorootPoints_eq_torusPoints]
    exact ⟨_, rfl⟩
  · intro i j
    have hsub : ((CoxeterSystem.braidWord t.coxeterMatrix i j).map n_sub).prod =
        ((CoxeterSystem.braidWord t.coxeterMatrix j i).map n_sub).prod :=
      Subtype.ext <| (hcoe _).trans <|
        (D.weylWord_braidWord_eq i j A).trans (hcoe _).symm
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

/-- `weylQuotientLift` sends each Bourbaki simple reflection to the coset of its pinned simple
Weyl representative. -/
-- Concrete rank equations can normalize dependent indices before matching.
@[simp↓]
theorem weylQuotientLift_ofIdx (A : Type v) [CommRing A] (i : Fin t.rank) :
    D.weylQuotientLift A
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      QuotientGroup.mk
        ⟨D.weylElement (t.simpleIndex ht i) A 1, D.weylElement_mem_weylSubgroup A i⟩ := by
  rw [weylQuotientLift, ← t.simplyConnectedWeylCoxeterSystem_simple ht i,
    CoxeterSystem.lift_apply_simple]

/-- `weylQuotientLift` sends the Weyl element spelled by a node word `l` to the coset of the
corresponding product of pinned simple Weyl representatives. -/
@[simp]
theorem weylQuotientLift_geckWeylWordProd (A : Type v) [CommRing A] (l : List (Fin t.rank)) :
    D.weylQuotientLift A (t.geckWeylWordProd ht l) =
      QuotientGroup.mk ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod,
        D.list_prod_map_weylElement_mem_weylSubgroup A l⟩ := by
  induction l with
  | nil =>
    rw [geckWeylWordProd_nil, map_one, eq_comm, QuotientGroup.eq_one_iff]
    exact Subgroup.one_mem _
  | cons i l ih =>
    rw [geckWeylWordProd_cons, map_mul, D.weylQuotientLift_ofIdx A i, ih, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext (by simp [List.map_cons, List.prod_cons]))

/-- `weylQuotientLift` is surjective over every commutative ring `A`. -/
theorem weylQuotientLift_surjective (A : Type v) [CommRing A] :
    Function.Surjective (D.weylQuotientLift A) := by
  intro x
  obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨l, s, rfl⟩ := (D.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints A).mp hg
  refine ⟨t.geckWeylWordProd ht l, ?_⟩
  have hfac : (⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.torusPoints A s,
      hg⟩ : D.weylSubgroup A) =
      ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod,
        D.list_prod_map_weylElement_mem_weylSubgroup A l⟩ *
        ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ := Subtype.ext (by simp)
  have htorus : (QuotientGroup.mk ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ :
      D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A))) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨s, rfl⟩
  rw [D.weylQuotientLift_geckWeylWordProd A l, hfac, QuotientGroup.mk_mul, htorus, mul_one]

/-- Over every commutative ring `A`, any word in the pinned simple Weyl representatives that
spells `1` in the Weyl group lies in the actual torus `(D.torusPoints A).range`. -/
theorem weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one
    (A : Type v) [CommRing A] {l : List (Fin t.rank)} (hl : t.geckWeylWordProd ht l = 1) :
    (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈ (D.torusPoints A).range := by
  have hq := D.weylQuotientLift_geckWeylWordProd A l
  rw [hl, map_one, eq_comm, QuotientGroup.eq_one_iff] at hq
  exact hq

end TauCeti.DynkinType.ChevalleyDatum
