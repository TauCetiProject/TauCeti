/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.TitsSystem
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
public import TauCeti.GroupTheory.TitsSystem.Length
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Basic
import TauCeti.GroupTheory.TitsSystem.Bruhat.Length
import TauCeti.LinearAlgebra.RootSystem.Inversions.Exchange

/-!
# The Weyl quotient of a Chevalley datum over an arbitrary field

For every Chevalley datum `D` and every field `K`, the Weyl projection
`D.weylProjection K : D.weylSubgroup K →* (t.simplyConnectedRootDatum ht).weylGroup`
descends to a multiplicative isomorphism on both `(D.titsSystem K).WeylGroup` and the Weyl
quotient `N(K) / T(K)`. Unlike the naive torus-centralizer criterion, which requires an infinite
field so that characters separate weights, the kernel identification `ker (weylProjection K) = T(K)`
holds over every field `K`, including `𝔽₂`.

The proof matches the word length on `(D.titsSystem K).WeylGroup` with the root-inversion count on
`(t.simplyConnectedRootDatum ht).weylGroup`: along a reduced word `sᵢ y` in the Tits-system Weyl
group, `(B sᵢ B)(B y B) = B (sᵢ y) B` is disjoint from `B y B`, which rules out `w_y⁻¹(αᵢ)` being
negative by `weylElement_mul_rootSubgroupPoints_ofAdd_one_mul_mem_doubleCoset_of_mem_negRoots` and
shows that left multiplication by `sᵢ` adds one root inversion at each step. An element in the
kernel of the descended Weyl projection therefore has word length zero, hence equals `1`; combining
this with `B(K) ∩ N(K) = T(K)` identifies `ker (D.weylProjection K)` with `T(K)`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 22 and Corollary 2 to Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §8.2, Proposition 8.2.2.
-/

public section

open Multiplicative
open scoped Pointwise

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type v) [Field K]

/-! ## Descending `weylProjection` to the Tits-system Weyl group -/

private def subgroupNToWeylSubgroup : (D.titsSystem K).subgroupN →* D.weylSubgroup K where
  toFun n := ⟨((n : (D.titsSystem K).subgroupN) : D.extendedElementarySubgroup K), by
    simpa only [D.titsSystem_subgroupN K, Subgroup.mem_subgroupOf] using n.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def titsSystemWeylProjection :
    (D.titsSystem K).WeylGroup →* (t.simplyConnectedRootDatum ht).weylGroup :=
  QuotientGroup.lift (D.titsSystem K).intersection
    ((D.weylProjection K).comp (D.subgroupNToWeylSubgroup K)) fun n hn => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      apply D.weylProjection_eq_one_of_mem_borelSubgroup K
      have hb := ((D.titsSystem K).mem_intersection n).mp hn
      simpa only [subgroupNToWeylSubgroup, MonoidHom.coe_mk, OneHom.coe_mk,
        D.titsSystem_subgroupB K, Subgroup.mem_subgroupOf] using hb

private theorem titsSystemWeylProjection_mk (n : (D.titsSystem K).subgroupN) :
    D.titsSystemWeylProjection K (QuotientGroup.mk n) =
      D.weylProjection K (D.subgroupNToWeylSubgroup K n) :=
  (rfl)

private theorem titsSystemWeylProjection_titsSystemSimple (i : Fin t.rank) :
    D.titsSystemWeylProjection K (D.titsSystemSimple K i) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  rw [D.titsSystemSimple_def K i, D.titsSystemWeylProjection_mk K]
  have hsub : D.subgroupNToWeylSubgroup K (D.titsSystemSimpleRep K i) =
      ⟨D.weylElement (t.simpleIndex ht i) K 1, D.weylElement_mem_weylSubgroup K i⟩ :=
    Subtype.ext (D.coe_titsSystemSimpleRep K i)
  rw [hsub, D.weylProjection_weylElement]

private theorem ncard_inversions_titsSystemWeylProjection_eq_wordLength
    (x : (D.titsSystem K).WeylGroup) :
    (inversions (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
      (D.titsSystemWeylProjection K x)).ncard =
      (D.titsSystem K).simpleGenerators.wordLength x := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  let T := D.titsSystem K
  let P := t.simplyConnectedRootDatum ht
  let b := t.simplyConnectedBase ht
  suffices h : ∀ m : ℕ, ∀ x : T.WeylGroup, T.simpleGenerators.wordLength x = m →
      (inversions P b (D.titsSystemWeylProjection K x)).ncard = m from h _ x rfl
  intro m
  induction m with
  | zero =>
    intro x hx
    rw [(Group.Generators.wordLength_eq_zero_iff _).mp hx, map_one, ncard_inversions_one]
  | succ m ih =>
    intro x hx
    obtain ⟨l, hl, hlen, hprod⟩ := T.exists_prod_eq_of_wordLength x
    rw [hx] at hlen
    rcases l with _ | ⟨s, l'⟩
    · cases hlen
    rw [List.forall_mem_cons] at hl
    obtain ⟨hs, hl'⟩ := hl
    rw [List.length_cons, Nat.add_right_cancel_iff] at hlen
    rw [List.prod_cons] at hprod
    let y : T.WeylGroup := l'.prod
    have hyle : T.simpleGenerators.wordLength y ≤ m := hlen ▸ T.wordLength_prod_le hl'
    have hstep := T.wordLength_simple_mul hs y
    have hsy : T.simpleGenerators.wordLength (s * y) = m + 1 := by rwa [hprod]
    have hylen : T.simpleGenerators.wordLength y = m := by omega
    have hlt : T.simpleGenerators.wordLength y < T.simpleGenerators.wordLength (s * y) := by omega
    have hcell : T.bruhatCell s * T.bruhatCell y = T.bruhatCell (s * y) :=
      (T.bruhatCell_mul_eq_iff_wordLength_lt hs y).mpr hlt
    have hs' := hs
    rw [D.titsSystem_simple K] at hs'
    obtain ⟨i, rfl⟩ := hs'
    obtain ⟨ny, hny⟩ := QuotientGroup.mk_surjective y
    let n : D.weylSubgroup K := D.subgroupNToWeylSubgroup K ny
    have hy_proj : D.titsSystemWeylProjection K y = D.weylProjection K n := by
      rw [← hny, D.titsSystemWeylProjection_mk K]
    have hnotmem : t.simpleIndex ht i ∉ inversions P b (D.weylProjection K n)⁻¹ := by
      intro hmem
      have hneg : P.weylGroupToPerm (D.weylProjection K n)⁻¹ (t.simpleIndex ht i) ∈
          negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
        rw [← not_mem_posRoots_iff_mem_negRoots, t.posRoots_rationalRootSystem ht, mem_posRoots]
        exact ((mem_inversions P b _ _).mp hmem).2
      obtain ⟨_, hmem_dc⟩ :=
        D.weylElement_mul_rootSubgroupPoints_ofAdd_one_mul_mem_doubleCoset_of_mem_negRoots K i n
          hneg
      have hrootB : D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd 1) ∈ D.borelSubgroup K :=
        D.positivePoints_le_borelSubgroup K
          (D.rootSubgroupPoints_mem_positivePoints K (simpleIndex_mem_posRoots i) _)
      let xE : D.extendedElementarySubgroup K :=
        ⟨D.weylElement (t.simpleIndex ht i) K 1 *
            D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd 1),
          mul_mem
            (D.weylSubgroup_le_extendedElementarySubgroup K (D.weylElement_mem_weylSubgroup K i))
            (D.borelSubgroup_le_extendedElementarySubgroup K hrootB)⟩
      have hxE : xE ∈ T.bruhatCell (D.titsSystemSimple K i) := by
        rw [D.titsSystemSimple_def K i, T.bruhatCell_mk, D.titsSystem_subgroupB K,
          D.mem_doubleCoset_subgroupOf_extendedElementarySubgroup_iff K,
          D.coe_titsSystemSimpleRep K i]
        exact DoubleCoset.mem_doubleCoset.mpr ⟨1, (D.borelSubgroup K).one_mem, _, hrootB,
          by simp only [xE]; group⟩
      have hyE : (ny : D.extendedElementarySubgroup K) ∈ T.bruhatCell y := by
        rw [← hny, T.bruhatCell_mk]
        exact DoubleCoset.mem_doubleCoset_self _ _ _
      have hxy_sy : xE * (ny : D.extendedElementarySubgroup K) ∈
          T.bruhatCell (D.titsSystemSimple K i * y) := hcell ▸ Set.mul_mem_mul hxE hyE
      have hxy_y : xE * (ny : D.extendedElementarySubgroup K) ∈ T.bruhatCell y := by
        rwa [← hny, T.bruhatCell_mk, D.titsSystem_subgroupB K,
          D.mem_doubleCoset_subgroupOf_extendedElementarySubgroup_iff K]
      exact lt_irrefl _ (T.eq_of_mem_bruhatCell_of_mem hxy_sy hxy_y ▸ hlt)
    have hisupp : t.simpleIndex ht i ∈ b.support :=
      t.support_rationalBase ht ▸ simpleIndex_mem_support i
    rw [← hprod, map_mul, D.titsSystemWeylProjection_titsSystemSimple K i, hy_proj,
      ncard_inversions_ofIdx_mul P b (D.weylProjection K n) (t.simpleIndex ht i),
      ncard_inversions_mul_ofIdx_of_notMem P (D.weylProjection K n)⁻¹ b hisupp hnotmem,
      ncard_inversions_inv P b (D.weylProjection K n), ← hy_proj, ih y hylen]

private theorem titsSystemWeylProjection_bijective :
    Function.Bijective (D.titsSystemWeylProjection K) := by
  refine ⟨?_, fun w => ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hlen := (D.ncard_inversions_titsSystemWeylProjection_eq_wordLength K x).symm
    rw [MonoidHom.mem_ker.mp hx, ncard_inversions_one] at hlen
    exact Subgroup.mem_bot.mpr ((Group.Generators.wordLength_eq_zero_iff _).mp hlen)
  · obtain ⟨n, rfl⟩ := D.weylProjection_surjective K w
    exact ⟨QuotientGroup.mk ⟨⟨n.1, D.weylSubgroup_le_extendedElementarySubgroup K n.2⟩, by
      rw [D.titsSystem_subgroupN K]; exact n.2⟩, rfl⟩

/-- **The Weyl group of `D.titsSystem K` is canonically isomorphic to the root-datum Weyl group**
over every field `K`. -/
noncomputable def titsSystemWeylGroupEquiv :
    (D.titsSystem K).WeylGroup ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  MulEquiv.ofBijective (D.titsSystemWeylProjection K) (D.titsSystemWeylProjection_bijective K)

/-- On the quotient class of `n ∈ (D.titsSystem K).subgroupN`, `titsSystemWeylGroupEquiv` agrees
with `D.weylProjection K`. -/
@[simp]
theorem titsSystemWeylGroupEquiv_mk (n : (D.titsSystem K).subgroupN) :
    D.titsSystemWeylGroupEquiv K (QuotientGroup.mk n) =
      D.weylProjection K ⟨((n : (D.titsSystem K).subgroupN) : D.extendedElementarySubgroup K), by
        simpa only [D.titsSystem_subgroupN K, Subgroup.mem_subgroupOf] using n.property⟩ :=
  (rfl)

/-- `titsSystemWeylGroupEquiv` carries the `i`-th Tits-system simple reflection to the `i`-th
root-datum simple reflection. -/
@[simp]
theorem titsSystemWeylGroupEquiv_titsSystemSimple (i : Fin t.rank) :
    D.titsSystemWeylGroupEquiv K (D.titsSystemSimple K i) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) :=
  D.titsSystemWeylProjection_titsSystemSimple K i

/-- The inverse of `titsSystemWeylGroupEquiv` sends the `i`-th root-datum simple reflection to
`D.titsSystemSimple K i`. -/
@[simp]
theorem titsSystemWeylGroupEquiv_symm_ofIdx (i : Fin t.rank) :
    (D.titsSystemWeylGroupEquiv K).symm
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      D.titsSystemSimple K i :=
  (D.titsSystemWeylGroupEquiv K).symm_apply_eq.mpr
    (D.titsSystemWeylGroupEquiv_titsSystemSimple K i).symm

/-- `titsSystemWeylGroupEquiv` carries `(D.titsSystem K).simple` onto the set of simple reflections
of the root datum. -/
theorem image_titsSystemWeylGroupEquiv_simple :
    D.titsSystemWeylGroupEquiv K '' (D.titsSystem K).simple =
      Set.range fun i : Fin t.rank =>
        RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  rw [D.titsSystem_simple K, ← Set.range_comp]
  ext w
  simp only [Set.mem_range, Function.comp_apply, D.titsSystemWeylGroupEquiv_titsSystemSimple K]

/-- The root-inversion count of `D.titsSystemWeylGroupEquiv K x` equals the Tits word length of
`x`. -/
theorem ncard_inversions_titsSystemWeylGroupEquiv (x : (D.titsSystem K).WeylGroup) :
    (inversions (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
      (D.titsSystemWeylGroupEquiv K x)).ncard =
      (D.titsSystem K).simpleGenerators.wordLength x :=
  D.ncard_inversions_titsSystemWeylProjection_eq_wordLength K x

/-- Transporting a root-datum Weyl element to `(D.titsSystem K).WeylGroup` turns its inversion
count into its Tits word length. -/
@[simp]
theorem wordLength_titsSystemWeylGroupEquiv_symm
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    (D.titsSystem K).simpleGenerators.wordLength
        ((D.titsSystemWeylGroupEquiv K).symm w) =
      (inversions (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) w).ncard := by
  simpa only [MulEquiv.apply_symm_apply] using
    (D.ncard_inversions_titsSystemWeylGroupEquiv K ((D.titsSystemWeylGroupEquiv K).symm w)).symm

/-- Distinct Bourbaki nodes determine distinct simple reflections in `(D.titsSystem K).WeylGroup`
over every field `K`. -/
theorem titsSystemSimple_injective : Function.Injective (D.titsSystemSimple K) := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  intro i j hij
  have hidx : RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht j) := by
    rw [← D.titsSystemWeylGroupEquiv_titsSystemSimple K i,
      ← D.titsSystemWeylGroupEquiv_titsSystemSimple K j, hij]
  have hmem : t.simpleIndex ht i ∈
      inversions (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht j)) := by
    rw [← hidx]
    simpa only [one_mul, inversions_one, Set.mem_empty_iff_false, not_false_eq_true, iff_true] using
      (mem_inversions_mul_ofIdx_iff_not_mem (t.simplyConnectedRootDatum ht) 1
        (t.simplyConnectedBase ht)
        ((t.simplyConnectedBase ht).isPos_of_mem_support
          (t.support_rationalBase ht ▸ simpleIndex_mem_support i)))
  have hnot : t.simpleIndex ht i = t.simpleIndex ht j := by
    by_contra hne
    have hpos := ((mem_inversions _ _ _ _).mp hmem).2
    rw [RootPairing.weylGroupToPerm_ofIdx_apply] at hpos
    exact hpos ((mem_posRoots _ _ _).mp
      ((bijOn_reflectionPerm_posRoots_diff_singleton (t.simplyConnectedRootDatum ht)
        (t.simplyConnectedBase ht) (t.support_rationalBase ht ▸ simpleIndex_mem_support j)).mapsTo
        ⟨t.posRoots_rationalRootSystem ht ▸ simpleIndex_mem_posRoots i, hne⟩).1)
  exact (t.simpleSupportEquiv ht).injective (Subtype.ext (by
    simpa only [coe_simpleSupportEquiv] using hnot))

/-! ## Kernel of `weylProjection` and the quotient `N(K) / T(K) ≃* W` -/

/-- Over every field `K` (finite or infinite), an element of `D.weylSubgroup K` has trivial Weyl
projection if and only if it belongs to the actual character-lattice torus `T(K)`. -/
@[simp]
theorem weylProjection_eq_one_iff_mem_range_torusPoints (n : D.weylSubgroup K) :
    D.weylProjection K n = 1 ↔ (n : D.points K) ∈ (D.torusPoints K).range := by
  let nN : (D.titsSystem K).subgroupN :=
    ⟨⟨n.1, D.weylSubgroup_le_extendedElementarySubgroup K n.2⟩, by
      rw [D.titsSystem_subgroupN K]; exact n.2⟩
  have hmk : D.titsSystemWeylGroupEquiv K (QuotientGroup.mk nN) = D.weylProjection K n := (rfl)
  rw [← hmk, map_eq_one_iff _ (D.titsSystemWeylGroupEquiv K).injective, QuotientGroup.eq_one_iff,
    (D.titsSystem K).mem_intersection, D.titsSystem_subgroupB K, Subgroup.mem_subgroupOf,
    ← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints K, Subgroup.mem_inf]
  exact ⟨fun hb => ⟨hb, n.2⟩, fun h => h.1⟩

/-- The kernel of `D.weylProjection K` is the actual character-lattice torus regarded inside
`D.weylSubgroup K`, over every field `K`. -/
@[simp]
theorem ker_weylProjection :
    (D.weylProjection K).ker = ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) := by
  ext n
  rw [MonoidHom.mem_ker, D.weylProjection_eq_one_iff_mem_range_torusPoints K,
    Subgroup.mem_subgroupOf]

/-- **The Weyl quotient isomorphism `N(K) / T(K) ≃* W` over an arbitrary field.** -/
noncomputable def weylQuotientEquiv :
    D.weylSubgroup K ⧸ ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_weylProjection K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.weylProjection K)
      (D.weylProjection_surjective K))

/-- `weylQuotientEquiv` evaluates on the coset of `n ∈ D.weylSubgroup K` to `D.weylProjection K n`.
-/
@[simp]
theorem weylQuotientEquiv_mk (n : D.weylSubgroup K) :
    D.weylQuotientEquiv K (QuotientGroup.mk n) = D.weylProjection K n :=
  (rfl)

/-- `weylQuotientEquiv` sends the coset of the `i`-th pinned Weyl representative to the `i`-th
simple reflection. -/
@[simp↓]
theorem weylQuotientEquiv_mk_weylElement (i : Fin t.rank) :
    D.weylQuotientEquiv K
        (QuotientGroup.mk ⟨D.weylElement (t.simpleIndex ht i) K 1,
          D.weylElement_mem_weylSubgroup K i⟩) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) :=
  D.weylProjection_weylElement K i

end TauCeti.DynkinType.ChevalleyDatum
