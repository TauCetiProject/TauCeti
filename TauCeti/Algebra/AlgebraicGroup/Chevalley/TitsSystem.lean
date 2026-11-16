/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Generation
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Borel
public import TauCeti.GroupTheory.TitsSystem.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.GroupTheory.TitsSystem.Bruhat.Length
import TauCeti.GroupTheory.TitsSystem.Comap

/-!
# The Tits system and Weyl quotient of a Chevalley datum over a field

Let `D` be a Chevalley datum of valid Dynkin type `t`. Over an arbitrary field `k` — including
`𝔽₂`, with no hypothesis on `kˣ` — this file constructs and identifies the Tits systems and Weyl
quotients associated to `D.borelSubgroup k` and `D.weylSubgroup k`:

1. `D.extendedElementaryTitsSystem k`: the Tits system on `D.extendedElementarySubgroup k` formed
   by the subgroups induced by `D.borelSubgroup k` and `D.weylSubgroup k` together with the cosets
   of the pinned simple Weyl representatives `nᵢ(1)`.
2. `D.ker_weylProjection k`: the kernel of `D.weylProjection k` is precisely the actual torus
   `((D.torusPoints k).range).subgroupOf (D.weylSubgroup k)`, established by Steinberg's
   Tits-system length argument without assuming braid relations among the `nᵢ(1)`.
3. `D.weylSubgroupQuotientMulEquiv k` and `D.extendedElementaryTitsSystemWeylGroupMulEquiv k`:
   canonical multiplicative isomorphisms `N(k) / T(k) ≃* W` and `(N(k) / (B(k) ∩ N(k))) ≃* W` onto
   `(t.simplyConnectedRootDatum ht).weylGroup`, carrying the Tits-system simple reflections to the
   root-datum simple reflections.
4. `D.elementaryTitsSystem k` and `D.elementaryTitsSystemWeylGroupMulEquiv k`: the pulled-back Tits
   system on the elementary Chevalley group `D.elementarySubgroup k` via `TauCeti.TitsSystem.comap`
   along `E(k) = E'(k) T(k)`, together with its canonical Weyl-group isomorphism onto `W`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Theorem 4, Corollary 2, and Lemma 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.2 and 8.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter IV, §2.
-/

public section

open scoped Pointwise

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private theorem mem_doubleCoset_subgroupOf_iff (A : Type v) [CommRing A]
    (x z : D.extendedElementarySubgroup A) :
    z ∈ DoubleCoset.doubleCoset x
        ((D.borelSubgroup A).subgroupOf (D.extendedElementarySubgroup A))
        ((D.borelSubgroup A).subgroupOf (D.extendedElementarySubgroup A)) ↔
      (z : D.points A) ∈ DoubleCoset.doubleCoset (x : D.points A)
        (D.borelSubgroup A) (D.borelSubgroup A) := by
  constructor
  · intro hz
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hz
    exact DoubleCoset.mem_doubleCoset.mpr ⟨b₁.val, hb₁, b₂.val, hb₂, rfl⟩
  · intro hz
    obtain ⟨b₁, hb₁, b₂, hb₂, hmul⟩ := DoubleCoset.mem_doubleCoset.mp hz
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨⟨b₁, D.borelSubgroup_le_extendedElementarySubgroup A hb₁⟩, hb₁,
        ⟨b₂, D.borelSubgroup_le_extendedElementarySubgroup A hb₂⟩, hb₂, Subtype.ext hmul⟩

/-! ### The Tits system on the extended elementary subgroup -/

section Field

variable (k : Type v) [Field k]

/-- The pinned `i`-th simple Weyl representative inside `(D.weylSubgroup k).subgroupOf G`. -/
private noncomputable def simpleWeylRep (i : Fin t.rank) :
    (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k) :=
  ⟨⟨D.weylElement (t.simpleIndex ht i) k 1,
    D.weylSubgroup_le_extendedElementarySubgroup k (D.weylElement_mem_weylSubgroup k i)⟩,
    D.weylElement_mem_weylSubgroup k i⟩

private theorem subgroupOf_borelSubgroup_eq_comap_torusPoints :
    ((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
      ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)) =
    (((D.torusPoints k).range).subgroupOf (D.weylSubgroup k)).comap
      (Subgroup.subgroupOfEquivOfLe
        (D.weylSubgroup_le_extendedElementarySubgroup k)).toMonoidHom := by
  ext n
  have hn_weyl : ((n : D.extendedElementarySubgroup k) : D.points k) ∈ D.weylSubgroup k := n.2
  -- Unfold membership in the iterated `subgroupOf` and `comap` to point-group membership.
  change ((n : D.extendedElementarySubgroup k) : D.points k) ∈ D.borelSubgroup k ↔
    ((n : D.extendedElementarySubgroup k) : D.points k) ∈ (D.torusPoints k).range
  rw [← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints k]
  exact ⟨fun hb => ⟨hb, hn_weyl⟩, fun h => h.1⟩

private instance normal_borelSubgroup_subgroupOf_weylSubgroup_extendedElementarySubgroup :
    (((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
      ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k))).Normal := by
  rw [D.subgroupOf_borelSubgroup_eq_comap_torusPoints k]
  exact Subgroup.Normal.comap (D.normal_torusPoints_subgroupOf_weylSubgroup k) _

private theorem closure_borelSubgroup_union_weylSubgroup_subgroupOf :
    Subgroup.closure
      ((((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k) :
          Set (D.extendedElementarySubgroup k))) ∪
        (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)) = ⊤ := by
  apply Subgroup.map_injective (D.extendedElementarySubgroup k).subtype_injective
  have htop : Subgroup.map (D.extendedElementarySubgroup k).subtype ⊤ =
      D.extendedElementarySubgroup k := by
    ext x
    simp
  have hB : (D.extendedElementarySubgroup k).subtype ''
      ((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k) : Set _) =
      (D.borelSubgroup k : Set (D.points k)) := by
    rw [← Subgroup.coe_map,
      Subgroup.map_subgroupOf_eq_of_le (D.borelSubgroup_le_extendedElementarySubgroup k)]
  have hN : (D.extendedElementarySubgroup k).subtype ''
      ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k) : Set _) =
      (D.weylSubgroup k : Set (D.points k)) := by
    rw [← Subgroup.coe_map,
      Subgroup.map_subgroupOf_eq_of_le (D.weylSubgroup_le_extendedElementarySubgroup k)]
  rw [MonoidHom.map_closure, Set.image_union, hB, hN, htop, Subgroup.closure_union,
    Subgroup.closure_eq, Subgroup.closure_eq, D.borelSubgroup_sup_weylSubgroup k]

private theorem closure_range_simpleWeylRep :
    Subgroup.closure (Set.range fun i : Fin t.rank =>
      (QuotientGroup.mk (D.simpleWeylRep k i) :
        (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k) ⧸
          ((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
            ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)))) = ⊤ := by
  let S := Set.range fun i : Fin t.rank =>
    (QuotientGroup.mk (D.simpleWeylRep k i) :
      (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k) ⧸
        ((D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)).subgroupOf
          ((D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)))
  refine eq_top_iff.mpr fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H n =>
    suffices key : ∀ {g : D.points k}, g ∈ D.weylSubgroup k →
        ∀ (hgG : g ∈ D.extendedElementarySubgroup k) (hgN : g ∈ D.weylSubgroup k),
          (QuotientGroup.mk
            (⟨⟨g, hgG⟩, hgN⟩ : (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)) :
              _ ⧸ _) ∈ Subgroup.closure S from
      key n.2 n.1.2 n.2
    intro g hg
    rw [D.weylSubgroup_def] at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      intro hgG hgN
      rcases hg with ⟨s, rfl⟩ | ⟨i, rfl⟩
      · have hmk : (QuotientGroup.mk (⟨⟨D.torusPoints k s, hgG⟩, hgN⟩ :
            (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)) : _ ⧸ _) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr <| Subgroup.mem_subgroupOf.mpr <|
            Subgroup.mem_subgroupOf.mpr (D.range_torusPoints_le_borelSubgroup k ⟨s, rfl⟩)
        rw [hmk]
        exact one_mem _
      · exact Subgroup.subset_closure ⟨i, rfl⟩
    | one =>
      intro _ _
      exact one_mem _
    | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      intro _ _
      have hg₁N : g₁ ∈ D.weylSubgroup k := by rw [D.weylSubgroup_def]; exact hg₁
      have hg₂N : g₂ ∈ D.weylSubgroup k := by rw [D.weylSubgroup_def]; exact hg₂
      have hg₁G := D.weylSubgroup_le_extendedElementarySubgroup k hg₁N
      have hg₂G := D.weylSubgroup_le_extendedElementarySubgroup k hg₂N
      exact mul_mem (ih₁ hg₁G hg₁N) (ih₂ hg₂G hg₂N)
    | inv g hg ih =>
      intro _ _
      have hgN : g ∈ D.weylSubgroup k := by rw [D.weylSubgroup_def]; exact hg
      have hgG := D.weylSubgroup_le_extendedElementarySubgroup k hgN
      exact inv_mem (ih hgG hgN)

/-- **The Tits system on the extended elementary Chevalley subgroup over an arbitrary field.** -/
noncomputable def extendedElementaryTitsSystem :
    TauCeti.TitsSystem (D.extendedElementarySubgroup k) where
  subgroupB := (D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k)
  subgroupN := (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k)
  closure_subgroupB_union_subgroupN := D.closure_borelSubgroup_union_weylSubgroup_subgroupOf k
  intersection_normal := inferInstance
  simple := Set.range fun i : Fin t.rank => QuotientGroup.mk (D.simpleWeylRep k i)
  closure_simple := D.closure_range_simpleWeylRep k
  exists_simpleRep_mul_self_mem := by
    rintro _ ⟨i, rfl⟩
    refine ⟨D.simpleWeylRep k i, rfl, ?_⟩
    -- Unfold `subgroupOf` membership of the square to membership in `D.borelSubgroup k`.
    change D.weylElement (t.simpleIndex ht i) k 1 * D.weylElement (t.simpleIndex ht i) k 1 ∈
      D.borelSubgroup k
    rw [D.weylElement_mul_self i k, D.simpleCorootPoints_eq_torusPoints]
    exact D.range_torusPoints_le_borelSubgroup k ⟨_, rfl⟩
  mul_doubleCoset_subset := by
    rintro _ ⟨i, rfl⟩
    refine ⟨D.simpleWeylRep k i, rfl, fun w z hz => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hz
    have hx' := (D.mem_doubleCoset_subgroupOf_iff k _ _).mp hx
    have hy' := (D.mem_doubleCoset_subgroupOf_iff k _ _).mp hy
    have hmul := D.doubleCoset_weylElement_mul_subset k i
      ⟨((w : D.extendedElementarySubgroup k) : D.points k), w.2⟩
      (Set.mem_mul.mpr ⟨_, hx', _, hy', rfl⟩)
    rcases hmul with hleft | hright
    · exact Or.inl ((D.mem_doubleCoset_subgroupOf_iff k _ _).mpr hleft)
    · exact Or.inr ((D.mem_doubleCoset_subgroupOf_iff k _ _).mpr hright)
  exists_conj_not_mem := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨b, hb⟩ := D.exists_weylElement_conj_notMem_borelSubgroup k i
    exact ⟨D.simpleWeylRep k i, rfl,
      ⟨⟨b.val, D.borelSubgroup_le_extendedElementarySubgroup k b.2⟩, b.2⟩, hb⟩

/-- The `B` subgroup of `D.extendedElementaryTitsSystem k` is the subgroup induced by
`D.borelSubgroup k`. -/
@[simp]
theorem extendedElementaryTitsSystem_subgroupB :
    (D.extendedElementaryTitsSystem k).subgroupB =
      (D.borelSubgroup k).subgroupOf (D.extendedElementarySubgroup k) :=
  (rfl)

/-- The `N` subgroup of `D.extendedElementaryTitsSystem k` is the subgroup induced by
`D.weylSubgroup k`. -/
@[simp]
theorem extendedElementaryTitsSystem_subgroupN :
    (D.extendedElementaryTitsSystem k).subgroupN =
      (D.weylSubgroup k).subgroupOf (D.extendedElementarySubgroup k) :=
  (rfl)

/-! ### Kernel of the Weyl projection and the Weyl quotient isomorphisms -/

private theorem bruhatCell_mul_eq_of_weylProjection_eq_one (i : Fin t.rank)
    {r' n' : (D.extendedElementaryTitsSystem k).subgroupN}
    (hr' : ((r' : D.extendedElementarySubgroup k) : D.points k) =
      D.weylElement (t.simpleIndex ht i) k 1)
    {n : D.weylSubgroup k}
    (hn' : ((n' : D.extendedElementarySubgroup k) : D.points k) = n.val)
    (hn : D.weylProjection k n = 1) :
    (D.extendedElementaryTitsSystem k).bruhatCell (QuotientGroup.mk r') *
        (D.extendedElementaryTitsSystem k).bruhatCell (QuotientGroup.mk n') =
      (D.extendedElementaryTitsSystem k).bruhatCell
        (QuotientGroup.mk r' * QuotientGroup.mk n') := by
  let T := D.extendedElementaryTitsSystem k
  rw [T.bruhatCell_mk r', T.bruhatCell_mk n', ← QuotientGroup.mk_mul, T.bruhatCell_mk (r' * n')]
  have hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n)⁻¹
      (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [hn, inv_one, map_one, Equiv.Perm.one_apply]
    exact simpleIndex_mem_posRoots i
  have heq := D.doubleCoset_weylElement_mul_eq_of_mem_posRoots k i n hpos
  have hcoe_mul : (((r' * n' : T.subgroupN) : D.extendedElementarySubgroup k) : D.points k) =
      D.weylElement (t.simpleIndex ht i) k 1 * (n : D.points k) := by
    simp only [Subgroup.coe_mul, hr', hn']
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hz
    refine (D.mem_doubleCoset_subgroupOf_iff k _ _).mpr ?_
    rw [hcoe_mul, ← heq]
    exact Set.mem_mul.mpr ⟨x.val, hr' ▸ (D.mem_doubleCoset_subgroupOf_iff k _ _).mp hx,
      y.val, hn' ▸ (D.mem_doubleCoset_subgroupOf_iff k _ _).mp hy, rfl⟩
  · intro hz
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hz
    refine Set.mem_mul.mpr
      ⟨b₁ * (r' : D.extendedElementarySubgroup k),
        DoubleCoset.mem_doubleCoset.mpr ⟨b₁, hb₁, 1, one_mem _, by rw [mul_one]⟩,
        (n' : D.extendedElementarySubgroup k) * b₂,
        DoubleCoset.mem_doubleCoset.mpr ⟨1, one_mem _, b₂, hb₂, by rw [one_mul]⟩, ?_⟩
    simp only [Subgroup.coe_mul, mul_assoc]

/-- **Kernel of the Weyl projection.** Over every field `k`, an element of `D.weylSubgroup k` has
trivial Weyl projection if and only if it belongs to the actual character-lattice torus. -/
theorem ker_weylProjection :
    (D.weylProjection k).ker = ((D.torusPoints k).range).subgroupOf (D.weylSubgroup k) := by
  let T := D.extendedElementaryTitsSystem k
  apply le_antisymm
  · intro n hn
    rw [MonoidHom.mem_ker] at hn
    let n' : T.subgroupN :=
      ⟨⟨n.val, D.weylSubgroup_le_extendedElementarySubgroup k n.2⟩, n.2⟩
    let w' : T.WeylGroup := QuotientGroup.mk n'
    have hinc : ∀ s' ∈ T.simple,
        T.simpleGenerators.wordLength w' < T.simpleGenerators.wordLength (s' * w') := by
      rintro _ ⟨i, rfl⟩
      let r' : T.subgroupN := D.simpleWeylRep k i
      have hs' : (QuotientGroup.mk r' : T.WeylGroup) ∈ T.simple := ⟨i, rfl⟩
      exact (T.bruhatCell_mul_eq_iff_wordLength_lt hs' w').mp
        (D.bruhatCell_mul_eq_of_weylProjection_eq_one k i rfl rfl hn)
    have hw'_one : w' = 1 := by
      obtain ⟨l, hl, hlen, hprod⟩ := T.exists_prod_eq_of_wordLength w'
      rcases l with _ | ⟨s', l'⟩
      · simpa using hprod.symm
      · exfalso
        have hs' : s' ∈ T.simple := hl s' List.mem_cons_self
        have hlt := hinc s' hs'
        have hsw : s' * w' = l'.prod := by
          rw [← hprod, List.prod_cons, T.simple_mul_simple_cancel_left hs']
        have hle := T.wordLength_prod_le (fun x hx => hl x (List.mem_cons_of_mem s' hx))
        rw [← hsw] at hle
        rw [List.length_cons] at hlen
        omega
    have hn_borel : n.val ∈ D.borelSubgroup k := (QuotientGroup.eq_one_iff n').mp hw'_one
    have hn_inf : n.val ∈ D.borelSubgroup k ⊓ D.weylSubgroup k := ⟨hn_borel, n.2⟩
    rwa [D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints k] at hn_inf
  · rintro n ⟨s, hs⟩
    rw [MonoidHom.mem_ker]
    have hsub : n = ⟨D.torusPoints k s, D.torusPoints_mem_weylSubgroup k s⟩ := Subtype.ext hs.symm
    rw [hsub, D.weylProjection_torusPoints]

/-- An element of `D.weylSubgroup k` lies in the kernel of `D.weylProjection k` iff its underlying
point lies in the actual torus image. -/
theorem mem_ker_weylProjection_iff (n : D.weylSubgroup k) :
    n ∈ (D.weylProjection k).ker ↔ (n : D.points k) ∈ (D.torusPoints k).range := by
  rw [D.ker_weylProjection k]
  exact Iff.rfl

/-- An element of `D.weylSubgroup k` has trivial Weyl projection iff its underlying point lies in
the actual torus image. -/
theorem weylProjection_eq_one_iff_mem_range_torusPoints (n : D.weylSubgroup k) :
    D.weylProjection k n = 1 ↔ (n : D.points k) ∈ (D.torusPoints k).range := by
  rw [← MonoidHom.mem_ker, D.mem_ker_weylProjection_iff k]

/-- **Weyl quotient isomorphism.** Over every field `k`, the quotient of `D.weylSubgroup k` by the
actual torus is canonically isomorphic to `(t.simplyConnectedRootDatum ht).weylGroup`. -/
noncomputable def weylSubgroupQuotientMulEquiv :
    D.weylSubgroup k ⧸ ((D.torusPoints k).range).subgroupOf (D.weylSubgroup k) ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_weylProjection k).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.weylProjection k)
      (D.weylProjection_surjective k))

/-- `D.weylSubgroupQuotientMulEquiv k` sends the coset of `n` to `D.weylProjection k n`. -/
@[simp]
theorem weylSubgroupQuotientMulEquiv_mk (n : D.weylSubgroup k) :
    D.weylSubgroupQuotientMulEquiv k (QuotientGroup.mk n) = D.weylProjection k n :=
  (rfl)

private noncomputable def extendedElementaryWeylProjection :
    (D.extendedElementaryTitsSystem k).subgroupN →*
      (t.simplyConnectedRootDatum ht).weylGroup where
  toFun n := D.weylProjection k ⟨((n : D.extendedElementarySubgroup k) : D.points k), n.2⟩
  map_one' := (D.weylProjection k).map_one
  map_mul' x y := (D.weylProjection k).map_mul ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩

private theorem extendedElementaryWeylProjection_surjective :
    Function.Surjective (D.extendedElementaryWeylProjection k) := by
  intro w
  obtain ⟨n, rfl⟩ := D.weylProjection_surjective k w
  exact ⟨⟨⟨n.val, D.weylSubgroup_le_extendedElementarySubgroup k n.2⟩, n.2⟩, rfl⟩

private theorem ker_extendedElementaryWeylProjection :
    (D.extendedElementaryWeylProjection k).ker =
      (D.extendedElementaryTitsSystem k).intersection := by
  ext n
  have hn_ker :
      n ∈ (D.extendedElementaryWeylProjection k).ker ↔
        (⟨((n : D.extendedElementarySubgroup k) : D.points k), n.2⟩ : D.weylSubgroup k) ∈
          (D.weylProjection k).ker := Iff.rfl
  rw [hn_ker, D.mem_ker_weylProjection_iff k, TitsSystem.mem_intersection,
    extendedElementaryTitsSystem_subgroupB, Subgroup.mem_subgroupOf,
    ← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints k]
  exact ⟨fun h => h.1, fun hb => ⟨hb, n.2⟩⟩

/-- Canonical isomorphism between the Weyl group of `D.extendedElementaryTitsSystem k` and the
Weyl group of the root datum. -/
noncomputable def extendedElementaryTitsSystemWeylGroupMulEquiv :
    (D.extendedElementaryTitsSystem k).WeylGroup ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_extendedElementaryWeylProjection k).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.extendedElementaryWeylProjection k)
      (D.extendedElementaryWeylProjection_surjective k))

/-- `D.extendedElementaryTitsSystemWeylGroupMulEquiv k` sends the coset of `n` to its Weyl
projection. -/
@[simp]
theorem extendedElementaryTitsSystemWeylGroupMulEquiv_mk
    (n : (D.extendedElementaryTitsSystem k).subgroupN) :
    D.extendedElementaryTitsSystemWeylGroupMulEquiv k (QuotientGroup.mk n) =
      D.weylProjection k
        ⟨((n : D.extendedElementarySubgroup k) : D.points k),
          by simpa [Subgroup.mem_subgroupOf] using n.2⟩ :=
  (rfl)

/-- Under `D.extendedElementaryTitsSystemWeylGroupMulEquiv k`, the simple reflections of
`D.extendedElementaryTitsSystem k` correspond to the simple reflections of the root datum. -/
@[simp]
theorem image_extendedElementaryTitsSystem_simple :
    D.extendedElementaryTitsSystemWeylGroupMulEquiv k ''
        (D.extendedElementaryTitsSystem k).simple =
      Set.range fun i : Fin t.rank =>
        RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  ext w
  constructor
  · rintro ⟨s, ⟨i, rfl⟩, rfl⟩
    let r' : (D.extendedElementaryTitsSystem k).subgroupN := D.simpleWeylRep k i
    exact ⟨i, ((D.extendedElementaryTitsSystemWeylGroupMulEquiv_mk k r').trans
      (D.weylProjection_weylElement k i)).symm⟩
  · rintro ⟨i, rfl⟩
    let r' : (D.extendedElementaryTitsSystem k).subgroupN := D.simpleWeylRep k i
    exact ⟨QuotientGroup.mk r', ⟨i, rfl⟩,
      (D.extendedElementaryTitsSystemWeylGroupMulEquiv_mk k r').trans
        (D.weylProjection_weylElement k i)⟩

/-! ### The pulled-back Tits system on the elementary Chevalley subgroup -/

private theorem exists_mul_torus_eq_of_extendedElementarySubgroup
    (g : D.extendedElementarySubgroup k) :
    ∃ x : D.elementarySubgroup k,
      ∃ t ∈ (D.extendedElementaryTitsSystem k).subgroupB ⊓
          (D.extendedElementaryTitsSystem k).subgroupN,
        (D.elementarySubgroup k).inclusion
          (D.elementarySubgroup_le_extendedElementarySubgroup k) x * t = g := by
  obtain ⟨e, he, s, hmul⟩ := (D.mem_extendedElementarySubgroup_iff k g.val).mp g.2
  refine ⟨⟨e, he⟩, ⟨D.torusPoints k s, D.torusPoints_mem_extendedElementarySubgroup k s⟩,
    ⟨D.range_torusPoints_le_borelSubgroup k ⟨s, rfl⟩, D.torusPoints_mem_weylSubgroup k s⟩, ?_⟩
  exact Subtype.ext hmul

/-- **The Tits system on the elementary Chevalley subgroup over an arbitrary field**, obtained by
pulling back `D.extendedElementaryTitsSystem k` along `E'(k) ↪ E(k)`. -/
noncomputable def elementaryTitsSystem :
    TauCeti.TitsSystem (D.elementarySubgroup k) :=
  (D.extendedElementaryTitsSystem k).comap
    ((D.elementarySubgroup k).inclusion (D.elementarySubgroup_le_extendedElementarySubgroup k))
    (D.exists_mul_torus_eq_of_extendedElementarySubgroup k)

/-- The `B` subgroup of `D.elementaryTitsSystem k` is the subgroup induced by `D.borelSubgroup k`.
-/
@[simp]
theorem elementaryTitsSystem_subgroupB :
    (D.elementaryTitsSystem k).subgroupB =
      (D.borelSubgroup k).subgroupOf (D.elementarySubgroup k) := by
  rw [elementaryTitsSystem, TitsSystem.comap_subgroupB, extendedElementaryTitsSystem_subgroupB]
  ext x
  rfl

/-- The `N` subgroup of `D.elementaryTitsSystem k` is the subgroup induced by `D.weylSubgroup k`. -/
@[simp]
theorem elementaryTitsSystem_subgroupN :
    (D.elementaryTitsSystem k).subgroupN =
      (D.weylSubgroup k).subgroupOf (D.elementarySubgroup k) := by
  rw [elementaryTitsSystem, TitsSystem.comap_subgroupN, extendedElementaryTitsSystem_subgroupN]
  ext x
  rfl

/-- Canonical isomorphism between the Weyl group of `D.elementaryTitsSystem k` and the Weyl group
of the root datum. -/
noncomputable def elementaryTitsSystemWeylGroupMulEquiv :
    (D.elementaryTitsSystem k).WeylGroup ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  ((D.extendedElementaryTitsSystem k).comapWeylGroupMulEquiv
    ((D.elementarySubgroup k).inclusion (D.elementarySubgroup_le_extendedElementarySubgroup k))
    (D.exists_mul_torus_eq_of_extendedElementarySubgroup k)).trans
    (D.extendedElementaryTitsSystemWeylGroupMulEquiv k)

/-- `D.elementaryTitsSystemWeylGroupMulEquiv k` sends the coset of `n` to its Weyl projection. -/
@[simp]
theorem elementaryTitsSystemWeylGroupMulEquiv_mk (n : (D.elementaryTitsSystem k).subgroupN) :
    D.elementaryTitsSystemWeylGroupMulEquiv k (QuotientGroup.mk n) =
      D.weylProjection k
        ⟨((n : D.elementarySubgroup k) : D.points k),
          by simpa [Subgroup.mem_subgroupOf] using n.2⟩ :=
  (congrArg (D.extendedElementaryTitsSystemWeylGroupMulEquiv k)
    ((D.extendedElementaryTitsSystem k).comapWeylGroupMulEquiv_mk
      ((D.elementarySubgroup k).inclusion (D.elementarySubgroup_le_extendedElementarySubgroup k))
      (D.exists_mul_torus_eq_of_extendedElementarySubgroup k) n)).trans
    (D.extendedElementaryTitsSystemWeylGroupMulEquiv_mk k _)

/-- Under `D.elementaryTitsSystemWeylGroupMulEquiv k`, the simple reflections of
`D.elementaryTitsSystem k` correspond to the simple reflections of the root datum. -/
@[simp]
theorem image_elementaryTitsSystem_simple :
    D.elementaryTitsSystemWeylGroupMulEquiv k '' (D.elementaryTitsSystem k).simple =
      Set.range fun i : Fin t.rank =>
        RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  let f := (D.elementarySubgroup k).inclusion (D.elementarySubgroup_le_extendedElementarySubgroup k)
  let hf := D.exists_mul_torus_eq_of_extendedElementarySubgroup k
  let e₁ := (D.extendedElementaryTitsSystem k).comapWeylGroupMulEquiv f hf
  let e₂ := D.extendedElementaryTitsSystemWeylGroupMulEquiv k
  have hsimple : (D.elementaryTitsSystem k).simple =
      e₁ ⁻¹' (D.extendedElementaryTitsSystem k).simple :=
    (D.extendedElementaryTitsSystem k).comap_simple f hf
  ext w
  rw [← D.image_extendedElementaryTitsSystem_simple k]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [hsimple] at hs
    exact ⟨e₁ s, hs, rfl⟩
  · rintro ⟨s', hs', rfl⟩
    refine ⟨e₁.symm s', ?_, congrArg e₂ (e₁.apply_symm_apply s')⟩
    rw [hsimple]
    exact Set.mem_preimage.mpr ((e₁.apply_symm_apply s').symm ▸ hs')

end Field

end TauCeti.DynkinType.ChevalleyDatum
