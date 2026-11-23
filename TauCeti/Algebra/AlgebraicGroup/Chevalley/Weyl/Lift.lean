/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Word
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Coxeter
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Weyl
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coxeter
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# The Coxeter lift to the Weyl-subgroup quotient of a Chevalley datum

For a Chevalley datum `D` of valid Dynkin type `t` over any commutative ring `A`, the pinned
simple Weyl representatives `nᵢ(1) = D.weylElement (t.simpleIndex ht i) A 1` satisfy
`nᵢ(1)² = αᵢ∨(-1) ∈ T_D(A)` (`ChevalleyDatum.weylElement_mul_self`), normalize the actual
torus `T_D(A) = (D.torusPoints A).range`
(`ChevalleyDatum.weylSubgroup_le_normalizer_range_torusPoints`), and satisfy the Artin--Tits
braid relations in `D.points A` (`ChevalleyDatum.weylWord_braidWord_eq`).

Consequently, the assignment `sᵢ ↦ [nᵢ(1)]` extends via Tits' Coxeter presentation
(`DynkinType.simplyConnectedWeylCoxeterSystem`) to a surjective group homomorphism
`ChevalleyDatum.weylQuotientLift A : W →* D.weylSubgroup A ⧸ T_D(A)`, sending each reflection
`s_γ` to the coset `[n_γ(1)]` (and `[n_γ(s)]` for every unit `s : Aˣ`), and any word in the
pinned simple Weyl representatives spelling `1` in `W` lies in `T_D(A)`
(`ChevalleyDatum.weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one`).

## Main definitions

* `TauCeti.DynkinType.ChevalleyDatum.weylQuotientLift`: the surjective homomorphism
  `W →* D.weylSubgroup A ⧸ ((D.torusPoints A).range).subgroupOf (D.weylSubgroup A)` over any
  commutative ring `A`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.mk_weylElement_eq_mk_one`: `[n_γ(s)] = [n_γ(1)]` in
  `D.weylSubgroup A ⧸ T_D(A)` for every root `γ` and unit `s`.
* `TauCeti.DynkinType.ChevalleyDatum.weylQuotientLift_ofIdx` and
  `TauCeti.DynkinType.ChevalleyDatum.weylQuotientLift_geckWeylWordProd`: values on root
  reflections and Bourbaki-numbered Weyl words.
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

/-- Modulo the actual torus, every Steinberg Weyl representative `n_γ(s)` lies in the same coset
as `n_γ(1)`. -/
theorem mk_weylElement_eq_mk_one (A : Type v) [CommRing A] (γ : Fin t.numRoots) (s : Aˣ) :
    (QuotientGroup.mk ⟨D.weylElement γ A s, D.weylElement_root_mem_weylSubgroup A γ s⟩ :
        D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A))) =
      QuotientGroup.mk
        ⟨D.weylElement γ A 1, D.weylElement_root_mem_weylSubgroup A γ 1⟩ := by
  have hfac :
      (⟨D.weylElement γ A s, D.weylElement_root_mem_weylSubgroup A γ s⟩ : D.weylSubgroup A) =
        ⟨D.corootPoints γ A s, by
          rw [D.corootPoints_apply]
          exact D.torusPoints_mem_weylSubgroup A _⟩ *
          ⟨D.weylElement γ A 1, D.weylElement_root_mem_weylSubgroup A γ 1⟩ :=
    Subtype.ext (D.weylElement_eq_corootPoints_mul γ A s)
  have htorus :
      (QuotientGroup.mk ⟨D.corootPoints γ A s, by
          rw [D.corootPoints_apply]
          exact D.torusPoints_mem_weylSubgroup A _⟩ :
          D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A))) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨_, (D.corootPoints_apply γ A s).symm⟩
  rw [hfac, QuotientGroup.mk_mul, htorus, one_mul]

/-- `weylQuotientLift` sends each root reflection `s_γ` to the coset of the Steinberg Weyl
representative `n_γ(1)`. -/
@[simp]
theorem weylQuotientLift_ofIdx (A : Type v) [CommRing A] (γ : Fin t.numRoots) :
    D.weylQuotientLift A
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ) =
      QuotientGroup.mk
        ⟨D.weylElement γ A 1, D.weylElement_root_mem_weylSubgroup A γ 1⟩ := by
  have hsimple (i : Fin t.rank) :
      D.weylQuotientLift A
          (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
        QuotientGroup.mk
          ⟨D.weylElement (t.simpleIndex ht i) A 1,
            D.weylElement_root_mem_weylSubgroup A (t.simpleIndex ht i) 1⟩ := by
    rw [weylQuotientLift, ← t.simplyConnectedWeylCoxeterSystem_simple ht i,
      CoxeterSystem.lift_apply_simple]
  induction γ using (t.rationalBase ht).induction_simple_reflect with
  | h₁ γ hγ =>
    obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hγ
    exact hsimple i
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
    rw [hconj_w, map_mul, map_mul, map_inv, hsimple i, ih, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    set γ' := (t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ
    set sε : Aˣ := Units.map (Int.castRingHom A).toMonoidHom
      (t.chevalleyWeylSign ht (t.simpleIndex ht i) γ)
    have hweyl :
        (⟨D.weylElement (t.simpleIndex ht i) A 1,
            D.weylElement_root_mem_weylSubgroup A (t.simpleIndex ht i) 1⟩ *
          ⟨D.weylElement γ A 1, D.weylElement_root_mem_weylSubgroup A γ 1⟩ *
          (⟨D.weylElement (t.simpleIndex ht i) A 1,
            D.weylElement_root_mem_weylSubgroup A (t.simpleIndex ht i) 1⟩)⁻¹ :
            D.weylSubgroup A) =
          ⟨D.corootPoints γ' A sε, by
            rw [D.corootPoints_apply]
            exact D.torusPoints_mem_weylSubgroup A _⟩ *
            ⟨D.weylElement γ' A 1, D.weylElement_root_mem_weylSubgroup A γ' 1⟩ :=
      Subtype.ext (D.weylElement_simpleIndex_conj_weylElement i γ A)
    have htorus :
        (QuotientGroup.mk ⟨D.corootPoints γ' A sε, by
            rw [D.corootPoints_apply]
            exact D.torusPoints_mem_weylSubgroup A _⟩ :
            D.weylSubgroup A ⧸ (((D.torusPoints A).range).subgroupOf (D.weylSubgroup A))) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨_, (D.corootPoints_apply γ' A sε).symm⟩
    rw [hweyl, QuotientGroup.mk_mul, htorus, one_mul]

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
    rw [geckWeylWordProd_cons, map_mul, D.weylQuotientLift_ofIdx A (t.simpleIndex ht i), ih,
      ← QuotientGroup.mk_mul]
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
