/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Heisenberg
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentral.Powerful
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.CohomFp
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Product
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Torsion
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.Data.Nat.Pow
import TauCeti.GroupTheory.Index.Basic

/-!
# Uniform pro-`p` groups and constant lower-`p`-series indices

A pro-`p` group is **uniform** (`TauCeti.IsUniform`) when it is topologically finitely generated,
torsion-free and powerful (`TauCeti.IsPowerful`, with the fourth-power condition at `p = 2`).
Uniform groups are the open subgroups through which Lazard's theory describes compact `p`-adic
analytic groups: every compact `p`-adic analytic group has an open normal uniform subgroup, and the
completed group algebra of a uniform group behaves like a power series ring in `d` variables.

The **dimension** of a uniform group `U` is its topological generator rank
`TauCeti.topologicalGeneratorRankNat U`, the least number `d` of topological generators. In a
powerful group the commutators are already `p`-th powers, so the closed power subgroup `Uᵖ` is the
first term `λ_1 = Φ(U)` of the lower `p`-series; hence `[U : Uᵖ] = p ^ d`
(`TauCeti.IsUniform.index_closedPowerSubgroup`) and `d = log_p [U : Uᵖ]`. Torsion-freeness makes
every `p`-power operator `π : gr_k(U) → gr_{k+1}(U)` bijective, so every successive index
`[λ_k : λ_{k+1}]` of the lower `p`-series is `p ^ d` and `[U : U^{p^k}] = p ^ (d * k)`. Conversely
a topologically finitely generated powerful pro-`p` group with constant successive indices is
torsion-free (`TauCeti.IsProP.forall_eq_one_of_isOfFinOrder_iff`), so the predicate agrees with the
definition of uniformity by constant indices
(`TauCeti.IsProP.isUniform_iff_isPowerful_and_relIndex_eq`). Uniformity and dimension are
preserved under topological isomorphisms, trivial groups, binary and finite indexed products, and
canonical subgroups `λ_k(G) = G^{p^k}`.

Every topologically finitely generated powerful pro-`p` group is virtually uniform: its successive
indices are non-increasing, hence eventually constant, so `λ_k` is uniform for all large `k`. The
dimension is an invariant of the commensurability class: an open uniform subgroup of a uniform group
has the same dimension, since the indices `[G : G^{p^k}] = p ^ (d * k)` grow at the rate `d`, and
any two open uniform subgroups of a compact group share an open uniform subgroup.

For commutative groups the notion is classical: a commutative profinite group is uniform exactly
when it is topologically isomorphic to `ℤ_p ^ d` for some `d`
(`TauCeti.isUniform_iff_exists_continuousMulEquiv_pi_padicInt`), and then `d` is its dimension.
By contrast `ℤ/p` is powerful but not uniform, having indices `p, 1, 1, …`. Over `ℤ_p`, the
congruence levels `HeisenbergGroup.level p m` for `(if p = 2 then 2 else 1) ≤ m` give nonabelian
uniform pro-`p` groups of dimension `3`, while `level 2 1` is non-powerful and each uniform level
contains an open non-powerful subgroup showing non-inheritance.

## Main definitions

* `TauCeti.IsUniform p G`: `G` is pro-`p`, topologically finitely generated, torsion-free and
  powerful.

## Main results

* `TauCeti.IsProP.forall_eq_one_of_isOfFinOrder_iff`: in a profinite pro-`p` group,
  torsion-freeness is equivalent to having no elements of order `p`.
* `TauCeti.IsPowerful.index_closedPowerSubgroup`, `TauCeti.IsUniform.index_closedPowerSubgroup`:
  for a topologically finitely generated powerful pro-`p` group, `[G : Gᵖ] = p ^ d(G)`.
* `TauCeti.IsUniform.topologicalGeneratorRankNat_eq_log_index`: the dimension is
  `log_p [G : Gᵖ]`.
* `TauCeti.IsPowerful.relIndex_pLowerCentralSeries_le`: in a topologically finitely generated
  powerful pro-`p` group every successive index `[λ_k : λ_{k+1}]` of the lower `p`-series is at
  most `p ^ d(G)`.
* `TauCeti.isUniform_congr`, `TauCeti.IsUniform.prod`, `TauCeti.IsUniform.pi`, uniformity is
  invariant under topological group isomorphism and stable under binary and finite indexed products,
  with additive dimension (`TauCeti.IsUniform.topologicalGeneratorRankNat_prod`,
  `TauCeti.IsUniform.topologicalGeneratorRankNat_pi`); `TauCeti.isUniform_top_iff`,
  `TauCeti.isUniform_subgroupOf_iff` and `TauCeti.isUniform_map_subtype_iff` transport it between
  the ways of viewing a subgroup.
* `TauCeti.IsUniform.to_pLowerCentralSeries`, `TauCeti.IsUniform.to_closedPowerSubgroup_pow`: the
  terms `λ_k = G^{p^k}` of the lower `p`-series of a uniform group are uniform, of the same
  dimension (`TauCeti.IsUniform.topologicalGeneratorRankNat_pLowerCentralSeries`,
  `TauCeti.IsUniform.topologicalGeneratorRankNat_closedPowerSubgroup_pow`).
* `TauCeti.IsUniform.gradedPow_bijective`: the `p`-power operator of a uniform group is bijective
  in every degree.
* `TauCeti.IsUniform.relIndex_pLowerCentralSeries`, `TauCeti.IsUniform.index_pLowerCentralSeries`,
  `TauCeti.IsUniform.index_closedPowerSubgroup_pow`: `[λ_k : λ_{k+1}] = p ^ d` and
  `[G : G^{p^k}] = [G : λ_k] = p ^ (d * k)`.
* `TauCeti.IsProP.isUniform_iff_isPowerful_and_relIndex_eq`: a topologically finitely generated
  pro-`p` group is uniform exactly when it is powerful with every `[λ_k : λ_{k+1}]` equal to
  `[G : λ_1]` (DDMS Theorem 4.5).
* `TauCeti.IsPowerful.eventually_isUniform_pLowerCentralSeries`: in a topologically finitely
  generated powerful pro-`p` group, `λ_k` is uniform for all large `k`;
  `TauCeti.IsPowerful.exists_isUniform_map_pLowerCentralSeries_subset`: if such a group is an open
  subgroup of a compact totally disconnected group, every neighbourhood of the identity contains a
  term `λ_k` that is open and uniform in the ambient group.
* `TauCeti.IsUniform.topologicalGeneratorRankNat_subgroup_eq`,
  `TauCeti.IsUniform.topologicalGeneratorRankNat_eq_of_le`,
  `TauCeti.IsUniform.topologicalGeneratorRankNat_eq_of_isOpen`: open uniform subgroups of a
  uniform group, and any two open uniform subgroups of a compact totally disconnected group, have
  the same dimension.
* `TauCeti.isUniform_of_subsingleton`: the trivial group is uniform; its dimension is `0` by
  `TauCeti.topologicalGeneratorRankNat_of_subsingleton`.
* `TauCeti.isUniform_multiplicative_pi_padicInt`, `TauCeti.isUniform_multiplicative_padicInt`:
  `ℤ_p ^ X` for finite `X` is uniform, of dimension `#X`; in particular `ℤ_p` is uniform of
  dimension `1`.
* `TauCeti.IsUniform.nonempty_continuousMulEquiv_pi_padicInt`,
  `TauCeti.isUniform_iff_exists_continuousMulEquiv_pi_padicInt`: the commutative uniform groups are
  exactly the groups `ℤ_p ^ d`, with `d` the dimension.
* `TauCeti.not_isUniform_multiplicative_zmod`,
  `TauCeti.index_pLowerCentralSeries_one_multiplicative_zmod`,
  `TauCeti.relIndex_pLowerCentralSeries_multiplicative_zmod`: `ℤ/p` is powerful but not uniform,
  with indices `p, 1, 1, …`.
* `TauCeti.HeisenbergGroup.isPowerful_level`, `TauCeti.HeisenbergGroup.isUniform_level`,
  `TauCeti.HeisenbergGroup.index_closedPowerSubgroup_level`,
  `TauCeti.HeisenbergGroup.topologicalGeneratorRankNat_level`,
  `TauCeti.HeisenbergGroup.not_isUniform_level_two_one`,
  `TauCeti.HeisenbergGroup.exists_openSubgroup_not_isPowerful_and_not_isUniform_level`:
  nonabelian uniform witnesses of dimension `3` and open non-powerful counterexamples.

## References

* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, second
  edition, Chapter 4 (Theorem 4.5).
* K. Ardakov and K. A. Brown, *Ring-theoretic properties of Iwasawa algebras: a survey*, §2.3.
-/

public section

open Multiplicative Subgroup
open scoped commutatorElement

namespace TauCeti

universe u v

/-! ### Torsion in profinite pro-`p` groups -/

section Torsion

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- In a profinite pro-`p` group, every nontrivial element of finite order has a power of order
`p`. -/
theorem IsProP.exists_pow_eq_one_of_isOfFinOrder (hG : IsProP p G) {g : G} (hg : g ≠ 1)
    (hfin : IsOfFinOrder g) : ∃ m : ℕ, g ^ m ≠ 1 ∧ (g ^ m) ^ p = 1 := by
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := g)) hg.symm
  let q := QuotientGroup.mk' U.toSubgroup
  have hqg : q g ≠ 1 := fun h1 ↦ hU ((QuotientGroup.eq_one_iff g).mp h1) rfl
  have hp_dvd : p ∣ orderOf g := ((isProP_iff.mp hG U).dvd_orderOf hqg).trans (orderOf_map_dvd q g)
  have hord := orderOf_eq_prime_iff.mp (orderOf_pow_orderOf_div hfin.orderOf_pos.ne' hp_dvd)
  exact ⟨orderOf g / p, hord.2, hord.1⟩

/-- **Torsion-freeness in a profinite pro-`p` group** is equivalent to having no elements of order
`p`. -/
theorem IsProP.forall_eq_one_of_isOfFinOrder_iff (hG : IsProP p G) :
    (∀ g : G, IsOfFinOrder g → g = 1) ↔ (∀ g : G, g ^ p = 1 → g = 1) :=
  ⟨fun h g hgp ↦ h g (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.out.pos, hgp⟩), fun h g hfin ↦ by
    by_contra hg
    obtain ⟨m, hmne, hmp⟩ := hG.exists_pow_eq_one_of_isOfFinOrder hg hfin
    exact hmne (h (g ^ m) hmp)⟩

end Torsion

/-! ### Uniform pro-`p` groups -/

/-- A topological group is **uniform** at `p` when it is pro-`p`, topologically finitely
generated, torsion-free and powerful (`TauCeti.IsPowerful`, with the fourth-power condition at
`p = 2`). Its dimension is its topological generator rank `TauCeti.topologicalGeneratorRankNat`,
which is `log_p [G : Gᵖ]` by `TauCeti.IsUniform.topologicalGeneratorRankNat_eq_log_index`. -/
structure IsUniform (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Prop where
  /-- A uniform group is pro-`p`. -/
  isProP : IsProP p G
  /-- A uniform group is topologically finitely generated. -/
  isTopologicallyFinitelyGenerated : IsTopologicallyFinitelyGenerated G
  /-- A uniform group is torsion-free. -/
  isMulTorsionFree : IsMulTorsionFree G
  /-- A uniform group is powerful. -/
  isPowerful : IsPowerful p G

variable {p : ℕ}

section Index

variable [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The index of `Gᵖ` in a powerful group.** For a topologically finitely generated powerful
pro-`p` group, the closed power subgroup `Gᵖ` has index `p ^ d`, where `d` is the topological
generator rank: `Gᵖ` is the first term of the lower `p`-series, which is the Frattini
subgroup. -/
theorem IsPowerful.index_closedPowerSubgroup (hG : IsPowerful p G) (hP : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    (closedPowerSubgroup p G).index = p ^ topologicalGeneratorRankNat G hfg := by
  rw [hG.closedPowerSubgroup_eq_pLowerCentralSeries_one,
    pLowerCentralSeries_one_eq_proPFrattini hp.out, Subgroup.index_eq_card,
    hP.natCard_quotient_proPFrattini hfg]

/-- **The index of `Gᵖ` in a uniform group** is `p ^ d`, where `d` is the dimension. -/
theorem IsUniform.index_closedPowerSubgroup (hG : IsUniform p G) :
    (closedPowerSubgroup p G).index =
      p ^ topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated :=
  hG.isPowerful.index_closedPowerSubgroup hG.isProP _

/-- **The dimension of a uniform group** is `log_p [G : Gᵖ]`. -/
theorem IsUniform.topologicalGeneratorRankNat_eq_log_index (hG : IsUniform p G) :
    topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated =
      Nat.log p (closedPowerSubgroup p G).index := by
  rw [hG.index_closedPowerSubgroup, Nat.log_pow hp.out.one_lt]

/-- **The successive indices of the lower `p`-series of a powerful group are at most `p ^ d`**:
for a topologically finitely generated powerful pro-`p` group, `[λ_k : λ_{k+1}] ≤ p ^ d` for every
`k`, where `d` is the topological generator rank. At `k = 0` this is an equality, by
`TauCeti.IsPowerful.index_closedPowerSubgroup` and
`TauCeti.IsPowerful.closedPowerSubgroup_eq_pLowerCentralSeries_one`. -/
theorem IsPowerful.relIndex_pLowerCentralSeries_le (hG : IsPowerful p G) (hP : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (k : ℕ) :
    (pLowerCentralSeries p G (k + 1)).relIndex (pLowerCentralSeries p G k) ≤
      p ^ topologicalGeneratorRankNat G hfg := by
  induction k with
  | zero =>
    rw [pLowerCentralSeries_zero, Subgroup.relIndex_top_right,
      ← hG.closedPowerSubgroup_eq_pLowerCentralSeries_one, hG.index_closedPowerSubgroup hP hfg]
  | succ k ih => exact (hG.relIndex_pLowerCentralSeries_succ_le hp.out hfg k).trans ih

end Index

section Closure

variable {G : Type u} {H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Uniformity transfers across a topological group isomorphism. -/
theorem IsUniform.of_equiv (hG : IsUniform p G) (e : G ≃ₜ* H) : IsUniform p H where
  isProP := hG.isProP.of_equiv e
  isTopologicallyFinitelyGenerated :=
    (isTopologicallyFinitelyGenerated_congr e).mp hG.isTopologicallyFinitelyGenerated
  isMulTorsionFree :=
    have := hG.isMulTorsionFree
    Function.Injective.isMulTorsionFree (e.symm : H →* G) e.symm.injective
  isPowerful := (isPowerful_congr e).mp hG.isPowerful

/-- Uniformity is invariant under topological group isomorphism. -/
theorem isUniform_congr (e : G ≃ₜ* H) : IsUniform p G ↔ IsUniform p H :=
  ⟨fun hG ↦ hG.of_equiv e, fun hH ↦ hH.of_equiv e.symm⟩

variable (p G) in
/-- **The trivial group is uniform**, of dimension `0` by
`TauCeti.topologicalGeneratorRankNat_of_subsingleton`. -/
theorem isUniform_of_subsingleton [Subsingleton G] : IsUniform p G where
  isProP := IsPGroup.isProP fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  isTopologicallyFinitelyGenerated := (Set.finite_empty (α := G)).isTopologicallyFinitelyGenerated
    (Subsingleton.elim _ _)
  isMulTorsionFree := ⟨fun _ _ a b _ _ ↦ Subsingleton.elim a b⟩
  isPowerful := isPowerful_of_isMulCommutative

/-- **A product of two uniform groups is uniform.** -/
theorem IsUniform.prod (hG : IsUniform p G) (hH : IsUniform p H) : IsUniform p (G × H) where
  isProP := hG.isProP.prod hH.isProP
  isTopologicallyFinitelyGenerated :=
    hG.isTopologicallyFinitelyGenerated.prod hH.isTopologicallyFinitelyGenerated
  isMulTorsionFree :=
    have := hG.isMulTorsionFree
    have := hH.isMulTorsionFree
    inferInstance
  isPowerful := hG.isPowerful.prod hH.isPowerful

/-- The dimension of a binary product of uniform pro-`p` groups is the sum of their dimensions. -/
theorem IsUniform.topologicalGeneratorRankNat_prod [hp : Fact p.Prime]
    [CompactSpace G] [TotallyDisconnectedSpace G] [CompactSpace H] [TotallyDisconnectedSpace H]
    (hG : IsUniform p G) (hH : IsUniform p H) :
    topologicalGeneratorRankNat (G × H)
        (hG.isTopologicallyFinitelyGenerated.prod hH.isTopologicallyFinitelyGenerated) =
      topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated +
        topologicalGeneratorRankNat H hH.isTopologicallyFinitelyGenerated := by
  apply Nat.pow_right_injective hp.out.two_le
  dsimp only
  rw [← (hG.prod hH).index_closedPowerSubgroup, closedPowerSubgroup_prod, Subgroup.index_prod,
    hG.index_closedPowerSubgroup, hH.index_closedPowerSubgroup, pow_add]

/-- A finite indexed product of uniform pro-`p` groups is uniform. -/
theorem IsUniform.pi {ι : Type*} [Finite ι] {F : ι → Type*}
    [∀ i, Group (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, IsTopologicalGroup (F i)]
    (hF : ∀ i, IsUniform p (F i)) : IsUniform p (∀ i, F i) where
  isProP := IsProP.pi fun i ↦ (hF i).isProP
  isTopologicallyFinitelyGenerated :=
    IsTopologicallyFinitelyGenerated.pi fun i ↦ (hF i).isTopologicallyFinitelyGenerated
  isMulTorsionFree :=
    have := fun i ↦ (hF i).isMulTorsionFree
    inferInstance
  isPowerful := IsPowerful.pi fun i ↦ (hF i).isPowerful

/-- The dimension of a finite indexed product of uniform pro-`p` groups is the sum of their
dimensions. -/
theorem IsUniform.topologicalGeneratorRankNat_pi [hp : Fact p.Prime] {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Group (F i)] [∀ i, TopologicalSpace (F i)]
    [∀ i, IsTopologicalGroup (F i)] [∀ i, CompactSpace (F i)]
    [∀ i, TotallyDisconnectedSpace (F i)] (hF : ∀ i, IsUniform p (F i)) :
    topologicalGeneratorRankNat (∀ i, F i)
        (IsTopologicallyFinitelyGenerated.pi fun i ↦ (hF i).isTopologicallyFinitelyGenerated) =
      ∑ i, topologicalGeneratorRankNat (F i) (hF i).isTopologicallyFinitelyGenerated := by
  apply Nat.pow_right_injective hp.out.two_le
  dsimp only
  rw [← (IsUniform.pi hF).index_closedPowerSubgroup, closedPowerSubgroup_pi, Subgroup.index_pi',
    Finset.prod_congr rfl fun i _ ↦ (hF i).index_closedPowerSubgroup,
    Finset.prod_pow_eq_pow_sum]

/-- The top subgroup is uniform exactly when the group is. -/
@[simp]
theorem isUniform_top_iff : IsUniform p (⊤ : Subgroup G) ↔ IsUniform p G :=
  isUniform_congr
    { Subgroup.topEquiv (G := G) with
      continuous_toFun := continuous_subtypeVal
      continuous_invFun := continuous_induced_rng.mpr continuous_id }

/-- A subgroup `K ≤ H` is uniform as a subgroup of `H` exactly when it is uniform as a subgroup of
the ambient group. -/
theorem isUniform_subgroupOf_iff {H K : Subgroup G} (hKH : K ≤ H) :
    IsUniform p (K.subgroupOf H) ↔ IsUniform p K :=
  isUniform_congr (Subgroup.subgroupOfContinuousMulEquivOfLe hKH)

/-- A subgroup `K` of a subgroup `H` is uniform exactly when its image in the ambient group is
uniform. -/
@[simp]
theorem isUniform_map_subtype_iff {H : Subgroup G} {K : Subgroup H} :
    IsUniform p (K.map H.subtype) ↔ IsUniform p K := by
  rw [← isUniform_subgroupOf_iff (Subgroup.map_subtype_le K), Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

end Closure

section PowerSubgroups

variable [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The canonical power subgroups of a uniform group are uniform**: every term
`λ_k = G^{p^k}` (`TauCeti.IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup`) of the lower
`p`-series of a uniform group is uniform. It is open, hence topologically finitely generated, and
powerful by `TauCeti.IsPowerful.to_pLowerCentralSeries`. -/
theorem IsUniform.to_pLowerCentralSeries (hG : IsUniform p G) (k : ℕ) :
    IsUniform p (pLowerCentralSeries p G k) where
  isProP := hG.isProP.subgroup _
  isTopologicallyFinitelyGenerated := hG.isTopologicallyFinitelyGenerated.of_openSubgroup
    ⟨pLowerCentralSeries p G k, hG.isTopologicallyFinitelyGenerated.isOpen_pLowerCentralSeries
      hp.out k⟩
  isMulTorsionFree :=
    have := hG.isMulTorsionFree
    Function.Injective.isMulTorsionFree (pLowerCentralSeries p G k).subtype
      (pLowerCentralSeries p G k).subtype_injective
  isPowerful := hG.isPowerful.to_pLowerCentralSeries hp.out hG.isProP k

/-- **The closed power subgroups `G^{p^n}` of a uniform group are uniform**: they are the terms of
the lower `p`-series (`TauCeti.IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup`), which are
uniform by `TauCeti.IsUniform.to_pLowerCentralSeries`. -/
theorem IsUniform.to_closedPowerSubgroup_pow (hG : IsUniform p G) (n : ℕ) :
    IsUniform p (closedPowerSubgroup (p ^ n) G) :=
  hG.isPowerful.pLowerCentralSeries_eq_closedPowerSubgroup hp.out hG.isProP n ▸
    hG.to_pLowerCentralSeries n

/-! ### Constant indices along the lower `p`-series -/

/-- **The `p`-power operator of a uniform group is bijective**: `π` maps `gr_k(G)` bijectively onto
`gr_{k+1}(G)` in every degree. -/
theorem IsUniform.gradedPow_bijective (hG : IsUniform p G) (k : ℕ) :
    Function.Bijective (gradedPow p G k) :=
  have := hG.isMulTorsionFree
  ⟨hG.isPowerful.gradedPow_injective hp.out hG.isProP k,
    hG.isPowerful.gradedPow_surjective_of_isProP hp.out hG.isProP k⟩

/-- **The successive indices of the lower `p`-series of a uniform group are all `p ^ d`**:
`[λ_k : λ_{k+1}] = p ^ d` for every `k`, where `d` is the dimension. -/
theorem IsUniform.relIndex_pLowerCentralSeries (hG : IsUniform p G) (k : ℕ) :
    (pLowerCentralSeries p G (k + 1)).relIndex (pLowerCentralSeries p G k) =
      p ^ topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated := by
  induction k with
  | zero =>
    rw [pLowerCentralSeries_zero, Subgroup.relIndex_top_right,
      ← hG.isPowerful.closedPowerSubgroup_eq_pLowerCentralSeries_one, hG.index_closedPowerSubgroup]
  | succ k ih =>
    rw [← ih, ← natCard_gradedPiece, ← natCard_gradedPiece]
    exact (Nat.card_congr (Equiv.ofBijective _ (hG.gradedPow_bijective k))).symm

/-- **The index of `λ_k` in a uniform group** is `p ^ (d * k)`, where `d` is the dimension. -/
theorem IsUniform.index_pLowerCentralSeries (hG : IsUniform p G) (k : ℕ) :
    (pLowerCentralSeries p G k).index =
      p ^ (topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated * k) := by
  induction k with
  | zero => rw [pLowerCentralSeries_zero, Subgroup.index_top, mul_zero, pow_zero]
  | succ k ih =>
    rw [← Subgroup.relIndex_mul_index (pLowerCentralSeries_succ_le k),
      hG.relIndex_pLowerCentralSeries, ih, ← pow_add, mul_add_one, add_comm]

/-- **The index of `G^{p^k}` in a uniform group** is `p ^ (d * k)`, where `d` is the dimension:
`G^{p^k}` is the term `λ_k` of the lower `p`-series. -/
theorem IsUniform.index_closedPowerSubgroup_pow (hG : IsUniform p G) (k : ℕ) :
    (closedPowerSubgroup (p ^ k) G).index =
      p ^ (topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated * k) := by
  rw [← hG.isPowerful.pLowerCentralSeries_eq_closedPowerSubgroup hp.out hG.isProP,
    hG.index_pLowerCentralSeries]

/-- Every term `λ_k(G)` of the lower `p`-series of a uniform pro-`p` group `G` has the same
dimension as `G`. -/
theorem IsUniform.topologicalGeneratorRankNat_pLowerCentralSeries (hU : IsUniform p G) (k : ℕ) :
    topologicalGeneratorRankNat (pLowerCentralSeries p G k)
        (hU.to_pLowerCentralSeries k).isTopologicallyFinitelyGenerated =
      topologicalGeneratorRankNat G hU.isTopologicallyFinitelyGenerated := by
  apply Nat.pow_right_injective hp.out.two_le
  dsimp only
  rw [← (hU.to_pLowerCentralSeries k).index_closedPowerSubgroup,
    (hU.to_pLowerCentralSeries k).isPowerful.closedPowerSubgroup_eq_pLowerCentralSeries_one,
    hU.isPowerful.pLowerCentralSeries_pLowerCentralSeries_eq_subgroupOf hp.out hU.isProP k 1,
    ← Subgroup.relIndex, hU.relIndex_pLowerCentralSeries k]

/-- Every canonical closed power subgroup `G^{p^k}` of a uniform pro-`p` group `G` has the same
dimension as `G`. -/
theorem IsUniform.topologicalGeneratorRankNat_closedPowerSubgroup_pow (hU : IsUniform p G)
    (k : ℕ) :
    topologicalGeneratorRankNat (closedPowerSubgroup (p ^ k) G)
        (hU.to_closedPowerSubgroup_pow k).isTopologicallyFinitelyGenerated =
      topologicalGeneratorRankNat G hU.isTopologicallyFinitelyGenerated := by
  let e : closedPowerSubgroup (p ^ k) G ≃ₜ* pLowerCentralSeries p G k :=
    { toMulEquiv := MulEquiv.subgroupCongr
        (hU.isPowerful.pLowerCentralSeries_eq_closedPowerSubgroup hp.out hU.isProP k).symm
      continuous_toFun := continuous_induced_rng.mpr continuous_subtypeVal
      continuous_invFun := continuous_induced_rng.mpr continuous_subtypeVal }
  rw [topologicalGeneratorRankNat_congr e]
  exact hU.topologicalGeneratorRankNat_pLowerCentralSeries k

/-- **Uniformity is powerfulness with constant indices along the lower `p`-series**
(Dixon–du Sautoy–Mann–Segal, Theorem 4.5): a topologically finitely generated pro-`p` group is
uniform exactly when it is powerful and every successive index `[λ_k : λ_{k+1}]` equals `[G : λ_1]`.
This is the definition of uniform groups used by Dixon–du Sautoy–Mann–Segal (Definition 4.1). -/
theorem IsProP.isUniform_iff_isPowerful_and_relIndex_eq (hP : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    IsUniform p G ↔ IsPowerful p G ∧ ∀ k, (pLowerCentralSeries p G (k + 1)).relIndex
      (pLowerCentralSeries p G k) = (pLowerCentralSeries p G 1).index := by
  refine ⟨fun hG ↦ ⟨hG.isPowerful, fun k ↦ ?_⟩, fun ⟨hpow, hidx⟩ ↦ ⟨hP, hfg, ?_, hpow⟩⟩
  · rw [hG.relIndex_pLowerCentralSeries,
      ← hG.isPowerful.closedPowerSubgroup_eq_pLowerCentralSeries_one, hG.index_closedPowerSubgroup]
  · -- Constant indices make the surjections `π` between the finite graded pieces bijective.
    refine hP.isMulTorsionFree_of_gradedPow_injective hp.out fun k ↦ ?_
    have := hfg.finite_gradedPiece hp.out k
    refine ((hpow.gradedPow_surjective_of_isProP hp.out hP k).bijective_of_nat_card_le ?_).1
    rw [natCard_gradedPiece, natCard_gradedPiece, hidx, hidx]

/-! ### Uniform terms of the lower `p`-series of a powerful group -/

/-- **A powerful group is virtually uniform**: in a topologically finitely generated powerful
pro-`p` group, the term `λ_k` of the lower `p`-series is uniform for every large enough `k`
(Dixon–du Sautoy–Mann–Segal, Theorem 4.2). -/
theorem IsPowerful.eventually_isUniform_pLowerCentralSeries (hG : IsPowerful p G)
    (hP : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) :
    ∀ᶠ k in Filter.atTop, IsUniform p (pLowerCentralSeries p G k) := by
  let a : ℕ → ℕ := fun k ↦
    (pLowerCentralSeries p G (k + 1)).relIndex (pLowerCentralSeries p G k)
  have ha : Antitone a :=
    antitone_nat_of_succ_le fun k ↦ hG.relIndex_pLowerCentralSeries_succ_le hp.out hfg k
  -- The successive indices `[λ_k : λ_{k+1}]` are non-increasing, so they are constant from a
  -- point where they attain their minimum; from there on `λ_k` is powerful with constant indices.
  have hconst : ∀ k ≥ Function.argmin a, a k = a (Function.argmin a) := fun k hk ↦
    le_antisymm (ha hk) (Function.argmin_le a k)
  refine Filter.eventually_atTop.mpr ⟨Function.argmin a, fun k hk ↦ ?_⟩
  have hmap := hG.map_subtype_pLowerCentralSeries_pLowerCentralSeries hp.out hP k
  refine ((hP.subgroup _).isUniform_iff_isPowerful_and_relIndex_eq
    (hfg.of_openSubgroup ⟨_, hfg.isOpen_pLowerCentralSeries hp.out k⟩)).mpr
    ⟨hG.to_pLowerCentralSeries hp.out hP k, fun j ↦ ?_⟩
  rw [← Subgroup.relIndex_top_right, ← pLowerCentralSeries_zero,
    ← Subgroup.relIndex_map_map_of_injective _ _ (Subgroup.subtype_injective _),
    ← Subgroup.relIndex_map_map_of_injective _ _ (Subgroup.subtype_injective _),
    hmap, hmap, hmap, hmap]
  exact (hconst (k + j) (by omega)).trans (hconst (k + 0) (by omega)).symm

end PowerSubgroups

section Dimension

/-! ### The dimension of an open uniform subgroup -/

variable [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Open uniform subgroups inside a neighbourhood of the identity.** If an open subgroup `U` of a
compact totally disconnected group is a topologically finitely generated powerful pro-`p` group,
then every neighbourhood `S` of the identity contains a term `λ_k` of the lower `p`-series of `U`
that is open and uniform as a subgroup of the ambient group. -/
theorem IsPowerful.exists_isUniform_map_pLowerCentralSeries_subset {U : Subgroup G}
    (hU : IsPowerful p U) (hUo : IsOpen (U : Set G)) (hP : IsProP p U)
    (hfg : IsTopologicallyFinitelyGenerated U) {S : Set G} (hS : S ∈ nhds (1 : G)) :
    ∃ k, IsOpen ((pLowerCentralSeries p U k).map U.subtype : Set G) ∧
      IsUniform p ((pLowerCentralSeries p U k).map U.subtype) ∧
      ((pLowerCentralSeries p U k).map U.subtype : Set G) ⊆ S := by
  have : CompactSpace U :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen U hUo).isCompact
  obtain ⟨k, hk, hkS⟩ := ((hU.eventually_isUniform_pLowerCentralSeries hP hfg).and
    ((hP.hasAntitoneBasis_nhds_one_pLowerCentralSeries hfg hp.out).eventually_subset
      (continuous_subtypeVal.continuousAt.preimage_mem_nhds hS))).exists
  refine ⟨k, ?_, isUniform_map_subtype_iff.mpr hk, ?_⟩
  · rw [Subgroup.coe_map]
    exact hUo.isOpenMap_subtypeVal _ (hfg.isOpen_pLowerCentralSeries hp.out k)
  · rintro _ ⟨x, hx, rfl⟩
    exact hkS hx

/-- **An open uniform subgroup of a uniform group has the same dimension.** -/
theorem IsUniform.topologicalGeneratorRankNat_subgroup_eq (hG : IsUniform p G) {W : Subgroup G}
    (hWo : IsOpen (W : Set G)) (hW : IsUniform p W) :
    topologicalGeneratorRankNat W hW.isTopologicallyFinitelyGenerated =
      topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated := by
  -- The dimension is the exponential growth rate of the indices `[G : G^{p^k}] = p ^ (d * k)`,
  -- and `G^{p^{m+k}} ≤ W^{p^k} ≤ G^{p^k}` once `G^{p^m} ≤ W`.
  have hWc := Subgroup.isClosed_of_isOpen W hWo
  have : CompactSpace W := isCompact_iff_compactSpace.mp hWc.isCompact
  have : Finite (G ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWo
  have hWi : 0 < W.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨m, hm⟩ := (hG.isProP.hasAntitoneBasis_nhds_one_pLowerCentralSeries
    hG.isTopologicallyFinitelyGenerated hp.out).mem_iff.mp (hWo.mem_nhds W.one_mem)
  -- `W^{p^k}`, as a subgroup of `G`, has index `p ^ (dim W * k) * [G : W]`.
  have hidx (k : ℕ) : ((closedPowerSubgroup (p ^ k) W).map W.subtype).index =
      p ^ (topologicalGeneratorRankNat W hW.isTopologicallyFinitelyGenerated * k) * W.index := by
    rw [Subgroup.index_map_subtype, hW.index_closedPowerSubgroup_pow]
  refine le_antisymm (Nat.le_of_forall_pow_mul_le_mul_pow hp.out.one_lt
    (C := p ^ (topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated * m)) fun k ↦ ?_)
    (Nat.le_of_forall_pow_mul_le_mul_pow hp.out.one_lt (C := W.index) fun k ↦ ?_)
  · -- `G^{p^{m+k}} ≤ W^{p^k}`, since every `p^m`-th power lies in `λ_m ≤ W`.
    have hle : closedPowerSubgroup (p ^ m * p ^ k) G ≤
        (closedPowerSubgroup (p ^ k) W).map W.subtype :=
      closedPowerSubgroup_mul_le_map_subtype_closedPowerSubgroup hWc fun g ↦ hm (by
        simpa using pow_pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p g) m)
    rw [← pow_add] at hle
    have := Nat.le_of_dvd (by rw [hG.index_closedPowerSubgroup_pow]; exact pow_pos hp.out.pos _)
      (Subgroup.index_dvd_of_le hle)
    rw [hidx, hG.index_closedPowerSubgroup_pow, mul_add, pow_add] at this
    exact (Nat.le_mul_of_pos_right _ hWi).trans this
  · -- `W^{p^k} ≤ G^{p^k}`.
    have := Nat.le_of_dvd (by rw [hidx]; exact Nat.mul_pos (pow_pos hp.out.pos _) hWi)
      (Subgroup.index_dvd_of_le
        (W.subtype.map_closedPowerSubgroup_le (n := p ^ k) continuous_subtypeVal))
    rw [hidx, hG.index_closedPowerSubgroup_pow] at this
    exact this.trans_eq (mul_comm _ _)

/-- **A uniform subgroup has the dimension of each open uniform subgroup it contains.** -/
theorem IsUniform.topologicalGeneratorRankNat_eq_of_le {V W : Subgroup G} (hWV : W ≤ V)
    (hWo : IsOpen (W : Set G)) (hV : IsUniform p V) (hW : IsUniform p W) :
    topologicalGeneratorRankNat W hW.isTopologicallyFinitelyGenerated =
      topologicalGeneratorRankNat V hV.isTopologicallyFinitelyGenerated := by
  have : CompactSpace V := isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_of_isOpen V (Subgroup.isOpen_mono hWV hWo)).isCompact
  have e := Subgroup.subgroupOfContinuousMulEquivOfLe hWV
  exact (topologicalGeneratorRankNat_congr e _).symm.trans
    (hV.topologicalGeneratorRankNat_subgroup_eq (Subgroup.subgroupOf_isOpen V W hWo)
      ((isUniform_subgroupOf_iff hWV).mpr hW))

/-- **Two open uniform subgroups have the same dimension.** -/
theorem IsUniform.topologicalGeneratorRankNat_eq_of_isOpen {U V : Subgroup G} (hU : IsUniform p U)
    (hUo : IsOpen (U : Set G)) (hVo : IsOpen (V : Set G)) (hV : IsUniform p V) :
    topologicalGeneratorRankNat U hU.isTopologicallyFinitelyGenerated =
      topologicalGeneratorRankNat V hV.isTopologicallyFinitelyGenerated := by
  -- A term `λ_k(U)` of the lower `p`-series of `U` with large `k` is an open uniform subgroup of
  -- `G` contained in both.
  obtain ⟨k, hTo, hT, hTV⟩ := hU.isPowerful.exists_isUniform_map_pLowerCentralSeries_subset hUo
    hU.isProP hU.isTopologicallyFinitelyGenerated (hVo.mem_nhds V.one_mem)
  exact (hU.topologicalGeneratorRankNat_eq_of_le (Subgroup.map_subtype_le _) hTo hT).symm.trans
    (hV.topologicalGeneratorRankNat_eq_of_le hTV hTo hT)

end Dimension

/-! ### Commutative uniform pro-`p` groups -/

section PadicInt

variable (p) [hp : Fact p.Prime]

/-- **`ℤ_p ^ X` is uniform** for finite `X`, of dimension `#X` by
`TauCeti.topologicalGeneratorRankNat_multiplicative_pi_padicInt`. -/
theorem isUniform_multiplicative_pi_padicInt (X : Type*) [Finite X] :
    IsUniform p (Multiplicative (X → ℤ_[p])) where
  isProP := isProP_multiplicative_pi_padicInt p X
  isTopologicallyFinitelyGenerated :=
    isTopologicallyFinitelyGenerated_multiplicative_pi_padicInt p X
  isMulTorsionFree := inferInstance
  isPowerful := isPowerful_of_isMulCommutative

/-- **`ℤ_p` is uniform**, of dimension `1` by
`TauCeti.topologicalGeneratorRankNat_multiplicative_padicInt`. -/
theorem isUniform_multiplicative_padicInt : IsUniform p (Multiplicative ℤ_[p]) where
  isProP := isProP_multiplicative_padicInt p
  isTopologicallyFinitelyGenerated := isTopologicallyFinitelyGenerated_multiplicative_padicInt p
  isMulTorsionFree := inferInstance
  isPowerful := isPowerful_of_isMulCommutative

end PadicInt

section Commutative

variable [Fact p.Prime] {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [CompactSpace A] [TotallyDisconnectedSpace A]

/-- **A commutative uniform group is `ℤ_p ^ d`**, where `d` is its dimension: this is the
structure theorem for torsion-free topologically finitely generated abelian pro-`p` groups. -/
theorem IsUniform.nonempty_continuousMulEquiv_pi_padicInt (hA : IsUniform p A) :
    Nonempty (A ≃ₜ* Multiplicative
      (Fin (topologicalGeneratorRankNat A hA.isTopologicallyFinitelyGenerated) → ℤ_[p])) := by
  have := hA.isMulTorsionFree
  obtain ⟨r, ⟨e⟩⟩ := hA.isProP.exists_continuousMulEquiv_pi_padicInt
    hA.isTopologicallyFinitelyGenerated
  have hr : topologicalGeneratorRankNat A hA.isTopologicallyFinitelyGenerated = r := by
    rw [topologicalGeneratorRankNat_congr e, topologicalGeneratorRankNat_multiplicative_pi_padicInt,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hr]
  exact ⟨e⟩

/-- **The commutative uniform groups are exactly the groups `ℤ_p ^ d`.** -/
theorem isUniform_iff_exists_continuousMulEquiv_pi_padicInt :
    IsUniform p A ↔ ∃ d : ℕ, Nonempty (A ≃ₜ* Multiplicative (Fin d → ℤ_[p])) :=
  ⟨fun hA ↦ ⟨_, hA.nonempty_continuousMulEquiv_pi_padicInt⟩, fun ⟨d, ⟨e⟩⟩ ↦
    (isUniform_multiplicative_pi_padicInt p (Fin d)).of_equiv e.symm⟩

end Commutative

/-! ### Concrete examples and counterexamples -/

section Examples

variable (p) [hp : Fact p.Prime]

/-- **`ℤ/p` is not uniform**, for any group topology: the class of `1` is a nontrivial element of
order `p`. Being commutative, `ℤ/p` is nevertheless powerful, by
`TauCeti.isPowerful_of_isMulCommutative`. -/
theorem not_isUniform_multiplicative_zmod [TopologicalSpace (Multiplicative (ZMod p))]
    [IsTopologicalGroup (Multiplicative (ZMod p))] : ¬ IsUniform p (Multiplicative (ZMod p)) := by
  intro hG
  have := hG.isMulTorsionFree
  have h : (ofAdd (1 : ZMod p)) ^ p = 1 ^ p := by
    rw [one_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero]
  have h1 := eq_of_pow_eq_pow_of_commute (Fact.out : p.Prime).ne_zero (Commute.one_right _) h
  exact one_ne_zero (ofAdd_eq_one.mp h1)

/-- The index `[ℤ/p : λ_1(ℤ/p)]` is `p`. -/
theorem index_pLowerCentralSeries_one_multiplicative_zmod :
    (pLowerCentralSeries p (Multiplicative (ZMod p)) 1).index = p := by
  rw [pLowerCentralSeries_one_eq_proPFrattini hp.out, proPFrattini_multiplicative_zmod_eq_bot,
    Subgroup.index_bot, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- Every higher successive lower-`p`-series relative index `[λ_{k+1} : λ_{k+2}]` of `ℤ/p` is `1`,
so the lower-`p`-series indices of `ℤ/p` are `p, 1, 1, …`. -/
theorem relIndex_pLowerCentralSeries_multiplicative_zmod (k : ℕ) :
    (pLowerCentralSeries p (Multiplicative (ZMod p)) (k + 2)).relIndex
      (pLowerCentralSeries p (Multiplicative (ZMod p)) (k + 1)) = 1 := by
  have h1 : pLowerCentralSeries p (Multiplicative (ZMod p)) 1 = ⊥ :=
    (pLowerCentralSeries_one_eq_proPFrattini hp.out).trans
      (proPFrattini_multiplicative_zmod_eq_bot p)
  have hbot : ∀ m, 1 ≤ m → pLowerCentralSeries p (Multiplicative (ZMod p)) m = ⊥ := fun m hm ↦
    le_bot_iff.mp ((pLowerCentralSeries_antitone hm).trans h1.le)
  rw [Subgroup.relIndex, hbot (k + 2) (by omega), hbot (k + 1) (by omega),
    Subgroup.bot_subgroupOf, Subgroup.index_bot, Nat.card_unique]

/-! ### Nonabelian uniform witness: congruence levels of the `p`-adic Heisenberg group -/

namespace HeisenbergGroup

/-- For every prime `p` and every `m ≥ 1` (with `m ≥ 2` at `p = 2`), the congruence level
`HeisenbergGroup.level p m` is powerful. -/
theorem isPowerful_level {m : ℕ} (hm : (if p = 2 then 2 else 1) ≤ m) :
    IsPowerful p (level p m).toSubgroup := by
  set r : ℕ := if p = 2 then 2 else 1
  have hr : p ^ r = if p = 2 then 4 else p := by by_cases hp2 : p = 2 <;> simp [r, hp2]
  rw [isPowerful_iff, commutator_def, Subgroup.commutator_le]
  rintro a _ b _
  obtain ⟨⟨xa, hxa⟩, ⟨ya, hya⟩, -⟩ := (mem_level_iff p m).mp a.property
  obtain ⟨⟨xb, hxb⟩, ⟨yb, hyb⟩, -⟩ := (mem_level_iff p m).mp b.property
  let c : (level p m).toSubgroup :=
    ⟨⟨0, 0, (p : ℤ_[p]) ^ (2 * m - r) * (xa * yb - xb * ya)⟩, (mem_level_iff p m).mpr
      ⟨dvd_zero _, dvd_zero _, (pow_dvd_pow (p : ℤ_[p]) (by omega)).trans (dvd_mul_right _ _)⟩⟩
  have hcomm : ⁅a, b⁆ = c ^ (if p = 2 then 4 else p) := Subtype.ext <| by
    rw [Subgroup.coe_commutatorElement, commutatorElement_eq, Subgroup.coe_pow, ← hr, pow_eq]
    refine HeisenbergGroup.ext (by simp [c]) (by simp [c]) ?_
    simp only [c, nsmul_eq_mul, Nat.cast_pow, mul_zero, add_zero, hxa, hya, hxb, hyb]
    rw [← mul_assoc ((p : ℤ_[p]) ^ r), ← pow_add, show r + (2 * m - r) = m + m by omega, pow_add]
    ring
  exact hcomm ▸ pow_mem_closedPowerSubgroup c

/-- **Nonabelian uniform pro-`p` group of dimension `3`**: for every prime `p` and
`(if p = 2 then 2 else 1) ≤ m`, `HeisenbergGroup.level p m` is uniform. -/
theorem isUniform_level {m : ℕ} (hm : (if p = 2 then 2 else 1) ≤ m) :
    IsUniform p (level p m).toSubgroup where
  isProP := (isProP_padicInt p).subgroup _
  isTopologicallyFinitelyGenerated :=
    (isTopologicallyFinitelyGenerated_padicInt p).of_openSubgroup (level p m).toOpenSubgroup
  isMulTorsionFree := IsMulTorsionFree.of_not_isOfFinOrder fun _ hne ha ↦
    hne <| Subtype.ext <| eq_one_of_isOfFinOrder_padicInt p <|
      (level p m).toSubgroup.subtype.isOfFinOrder ha
  isPowerful := isPowerful_level p hm

/-- For `1 ≤ m`, the closed `p`-th power subgroup of `HeisenbergGroup.level p m` is precisely
`HeisenbergGroup.level p (m + 1)`. -/
theorem closedPowerSubgroup_level {m : ℕ} (hm : 1 ≤ m) :
    closedPowerSubgroup p (level p m).toSubgroup =
      (level p (m + 1)).toSubgroup.subgroupOf (level p m).toSubgroup := by
  refine le_antisymm ((closedPowerSubgroup_le_iff
    ((level p (m + 1)).isClosed.preimage continuous_subtypeVal)).mpr fun a ↦ ?_) fun a ha ↦ ?_
  · rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, pow_eq]
    obtain ⟨hx, hy, hz⟩ := (mem_level_iff p m).mp a.property
    have hmul : ∀ {w : ℤ_[p]}, (p : ℤ_[p]) ^ m ∣ w → (p : ℤ_[p]) ^ (m + 1) ∣ (p : ℤ_[p]) * w :=
      fun ⟨c, hc⟩ ↦ ⟨c, by rw [hc, pow_succ', mul_assoc]⟩
    have hxy : (p : ℤ_[p]) ^ (m + 1) ∣ (p.choose 2 : ℤ_[p]) * (a.val.x * a.val.y) :=
      ((pow_dvd_pow (p : ℤ_[p]) (by omega : m + 1 ≤ m + m)).trans
        (pow_add (p : ℤ_[p]) m m ▸ mul_dvd_mul hx hy)).trans (dvd_mul_left _ _)
    exact (mem_level_iff p (m + 1)).mpr ⟨by simpa [nsmul_eq_mul] using hmul hx,
      by simpa [nsmul_eq_mul] using hmul hy,
      by simpa [nsmul_eq_mul] using dvd_add (hmul hz) hxy⟩
  · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ :=
      (mem_level_iff p (m + 1)).mp (Subgroup.mem_subgroupOf.mp ha)
    let u : (level p m).toSubgroup := ⟨⟨(p : ℤ_[p]) ^ m * x, 0, 0⟩,
      (mem_level_iff p m).mpr ⟨dvd_mul_right _ _, dvd_zero _, dvd_zero _⟩⟩
    let v : (level p m).toSubgroup := ⟨⟨0, (p : ℤ_[p]) ^ m * y, 0⟩,
      (mem_level_iff p m).mpr ⟨dvd_zero _, dvd_mul_right _ _, dvd_zero _⟩⟩
    let w : (level p m).toSubgroup :=
      ⟨⟨0, 0, (p : ℤ_[p]) ^ m * (z - (p : ℤ_[p]) ^ (m + 1) * (x * y))⟩,
        (mem_level_iff p m).mpr ⟨dvd_zero _, dvd_zero _, dvd_mul_right _ _⟩⟩
    have hprod : w ^ p * u ^ p * v ^ p = a := Subtype.ext <| by
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, pow_eq, u, v, w]
      refine HeisenbergGroup.ext ?_ ?_ ?_
      · simp only [mul_x, mul_zero, zero_add, add_zero, nsmul_eq_mul, hx, pow_succ', mul_assoc]
      · simp only [mul_y, mul_zero, zero_add, nsmul_eq_mul, hy, pow_succ', mul_assoc]
      · simp only [mul_z, mul_zero, zero_add, add_zero, nsmul_eq_mul, hz, pow_succ', mul_assoc]
        ring
    exact hprod ▸ mul_mem (mul_mem (pow_mem_closedPowerSubgroup w)
      (pow_mem_closedPowerSubgroup u)) (pow_mem_closedPowerSubgroup v)

/-- For every `1 ≤ m`, `closedPowerSubgroup p (HeisenbergGroup.level p m)` has index `p ^ 3`. -/
@[simp]
theorem index_closedPowerSubgroup_level {m : ℕ} (hm : 1 ≤ m) :
    (closedPowerSubgroup p (level p m).toSubgroup).index = p ^ 3 := by
  have hmul := Subgroup.relIndex_mul_index (level_antitone p (Nat.le_succ m))
  rw [index_level, index_level] at hmul
  rw [closedPowerSubgroup_level p hm]
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos (3 * m))
  rw [← Subgroup.relIndex, hmul, ← pow_add]
  congr 1
  omega

/-- For every `(if p = 2 then 2 else 1) ≤ m`, `HeisenbergGroup.level p m` has topological
generator rank `3`. -/
@[simp]
theorem topologicalGeneratorRankNat_level {m : ℕ} (hm : (if p = 2 then 2 else 1) ≤ m) :
    topologicalGeneratorRankNat (level p m).toSubgroup
        (isUniform_level p hm).isTopologicallyFinitelyGenerated = 3 := by
  have hm1 : 1 ≤ m := by split_ifs at hm <;> omega
  rw [(isUniform_level p hm).topologicalGeneratorRankNat_eq_log_index,
    index_closedPowerSubgroup_level p hm1, Nat.log_pow hp.out.one_lt]

/-- At `p = 2`, `HeisenbergGroup.level 2 1` is not powerful: every fourth power lies in `level 2 3`,
whereas `⁅(2, 0, 0), (0, 2, 0)⁆ = (0, 0, 4) ∉ level 2 3`. -/
theorem not_isPowerful_level_two_one : ¬ IsPowerful 2 (level 2 1).toSubgroup := fun hpow ↦ by
  have hchoose : Nat.choose 4 2 = 6 := by decide
  have hle : closedPowerSubgroup 4 (level 2 1).toSubgroup ≤
      (level 2 3).toSubgroup.subgroupOf (level 2 1).toSubgroup :=
    (closedPowerSubgroup_le_iff ((level 2 3).isClosed.preimage continuous_subtypeVal)).mpr
      fun a ↦ by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, pow_eq]
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ := (mem_level_iff 2 1).mp a.property
        refine (mem_level_iff 2 3).mpr ⟨⟨x, ?_⟩, ⟨y, ?_⟩, ⟨z + 3 * (x * y), ?_⟩⟩
        · simp only [nsmul_eq_mul, Nat.cast_ofNat, pow_one, hx]
          ring
        · simp only [nsmul_eq_mul, Nat.cast_ofNat, pow_one, hy]
          ring
        · simp only [nsmul_eq_mul, Nat.cast_ofNat, hchoose, pow_one, hx, hy, hz]
          ring
  let a : (level 2 1).toSubgroup :=
    ⟨⟨2, 0, 0⟩, (mem_level_iff 2 1).mpr ⟨by simp, dvd_zero _, dvd_zero _⟩⟩
  let b : (level 2 1).toSubgroup :=
    ⟨⟨0, 2, 0⟩, (mem_level_iff 2 1).mpr ⟨dvd_zero _, by simp, dvd_zero _⟩⟩
  have hz := ((mem_level_iff 2 3).mp (Subgroup.mem_subgroupOf.mp <|
    hle ((isPowerful_two_iff.mp hpow) (_root_.commutator_def (level 2 1).toSubgroup ▸
      commutator_mem_commutator (mem_top a) (mem_top b))))).2.2
  rw [Subgroup.coe_commutatorElement, commutatorElement_eq] at hz
  have hdvd : (2 : ℤ_[2]) ^ 3 ∣ (2 : ℤ_[2]) ^ 2 := by simpa [a, b, sq] using hz
  exact absurd ((pow_dvd_pow_iff PadicInt.prime_p.ne_zero PadicInt.prime_p.not_isUnit).mp hdvd)
    (by omega)

/-- At `p = 2`, `HeisenbergGroup.level 2 1` is not uniform. -/
theorem not_isUniform_level_two_one : ¬ IsUniform 2 (level 2 1).toSubgroup :=
  fun hU ↦ not_isPowerful_level_two_one hU.isPowerful

private def deepCenterSubgroup (r : ℕ) : Subgroup (level p r).toSubgroup where
  carrier := {a | (p : ℤ_[p]) ^ (2 * r) ∣ a.val.z}
  one_mem' := dvd_zero _
  mul_mem' := fun {a b} ha hb ↦ dvd_add (dvd_add ha hb) <| two_mul r ▸ pow_add (p : ℤ_[p]) r r ▸
    mul_dvd_mul ((mem_level_iff p r).mp a.property).1 ((mem_level_iff p r).mp b.property).2.1
  inv_mem' := fun {a} ha ↦ dvd_add (dvd_neg.mpr ha) <| two_mul r ▸ pow_add (p : ℤ_[p]) r r ▸
    mul_dvd_mul ((mem_level_iff p r).mp a.property).1 ((mem_level_iff p r).mp a.property).2.1

private def deepCenterPowerBound (r : ℕ) (hr1 : 1 ≤ r) : Subgroup (HeisenbergGroup ℤ_[p]) where
  carrier := {a | (p : ℤ_[p]) ^ (2 * r) ∣ a.x ∧ (p : ℤ_[p]) ^ (2 * r) ∣ a.y ∧
    (p : ℤ_[p]) ^ (2 * r + 1) ∣ a.z}
  one_mem' := ⟨dvd_zero _, dvd_zero _, dvd_zero _⟩
  mul_mem' := fun {a b} ha hb ↦ ⟨dvd_add ha.1 hb.1, dvd_add ha.2.1 hb.2.1,
    dvd_add (dvd_add ha.2.2 hb.2.2) ((pow_dvd_pow (p : ℤ_[p]) (by omega : 2 * r + 1 ≤
      2 * r + 2 * r)).trans (pow_add (p : ℤ_[p]) (2 * r) (2 * r) ▸ mul_dvd_mul ha.1 hb.2.1))⟩
  inv_mem' := fun {a} ha ↦ ⟨dvd_neg.mpr ha.1, dvd_neg.mpr ha.2.1,
    dvd_add (dvd_neg.mpr ha.2.2) ((pow_dvd_pow (p : ℤ_[p]) (by omega : 2 * r + 1 ≤
      2 * r + 2 * r)).trans (pow_add (p : ℤ_[p]) (2 * r) (2 * r) ▸ mul_dvd_mul ha.1 ha.2.1))⟩

private theorem closedPowerSubgroup_deepCenterSubgroup_le :
    let r : ℕ := if p = 2 then 2 else 1
    let hr1 : 1 ≤ r := by dsimp [r]; split_ifs <;> omega
    closedPowerSubgroup (if p = 2 then 4 else p) (deepCenterSubgroup p r) ≤
      ((deepCenterPowerBound p r hr1).subgroupOf (level p r).toSubgroup).subgroupOf
        (deepCenterSubgroup p r) := by
  intro r hr1
  set e : ℕ := if p = 2 then 4 else p
  have hr : p ^ r = e := by by_cases hp2 : p = 2 <;> simp [r, e, hp2]
  have hdvd_choose : p ∣ e.choose 2 := by
    by_cases hp2 : p = 2
    · subst hp2; decide
    · simpa [e, hp2] using
        hp.out.dvd_choose_self two_ne_zero (lt_of_le_of_ne hp.out.two_le (Ne.symm hp2))
  have hM_closed : IsClosed (deepCenterPowerBound p r hr1 : Set (HeisenbergGroup ℤ_[p])) :=
    Subgroup.isClosed_of_isOpen _ <| Subgroup.isOpen_mono (H₁ := (level p (2 * r + 1)).toSubgroup)
      (fun a ha ↦ let ⟨hx, hy, hz⟩ := (mem_level_iff p (2 * r + 1)).mp ha
        ⟨(pow_dvd_pow _ (Nat.le_succ _)).trans hx, (pow_dvd_pow _ (Nat.le_succ _)).trans hy, hz⟩)
      (level p (2 * r + 1)).isOpen
  refine (closedPowerSubgroup_le_iff
    ((hM_closed.preimage continuous_subtypeVal).preimage continuous_subtypeVal)).mpr fun a ↦ ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_pow, Subgroup.coe_pow,
    pow_eq]
  obtain ⟨hax, hay, -⟩ := (mem_level_iff p r).mp a.val.property
  have he_eq : (e : ℤ_[p]) = (p : ℤ_[p]) ^ r := by rw [← hr, Nat.cast_pow]
  have hxy : (p : ℤ_[p]) ^ (2 * r) ∣ a.val.val.x * a.val.val.y :=
    two_mul r ▸ pow_add (p : ℤ_[p]) r r ▸ mul_dvd_mul hax hay
  obtain ⟨c, hc⟩ := hdvd_choose
  refine ⟨by simpa only [nsmul_eq_mul, he_eq, two_mul, pow_add] using mul_dvd_mul_left _ hax,
    by simpa only [nsmul_eq_mul, he_eq, two_mul, pow_add] using mul_dvd_mul_left _ hay,
    dvd_add ?_ ?_⟩
  · rw [nsmul_eq_mul, he_eq]
    exact (pow_dvd_pow (p : ℤ_[p]) (by omega : 2 * r + 1 ≤ r + 2 * r)).trans
      (pow_add (p : ℤ_[p]) r (2 * r) ▸ mul_dvd_mul_left _ a.property)
  · rw [nsmul_eq_mul, hc, Nat.cast_mul, mul_assoc, pow_succ']
    exact mul_dvd_mul_left _ (dvd_mul_of_dvd_right hxy _)

/-- **Uniformity does not pass to arbitrary open subgroups**: for every prime `p`, the uniform
pro-`p` group `HeisenbergGroup.level p (if p = 2 then 2 else 1)` contains an open subgroup that is
neither powerful nor uniform. -/
theorem exists_openSubgroup_not_isPowerful_and_not_isUniform_level :
    ∃ U : OpenSubgroup (level p (if p = 2 then 2 else 1)).toSubgroup,
      ¬ IsPowerful p U.toSubgroup ∧ ¬ IsUniform p U.toSubgroup := by
  set r : ℕ := if p = 2 then 2 else 1
  let U : OpenSubgroup (level p r).toSubgroup := ⟨deepCenterSubgroup p r, Subgroup.isOpen_mono
    (H₁ := (level p (2 * r)).toSubgroup.subgroupOf (level p r).toSubgroup)
    (fun _ ha ↦ ((mem_level_iff p (2 * r)).mp (Subgroup.mem_subgroupOf.mp ha)).2.2)
    ((level p (2 * r)).isOpen.preimage continuous_subtypeVal)⟩
  have hnotpow : ¬ IsPowerful p U.toSubgroup := fun hpow ↦ by
    let a : U.toSubgroup := ⟨⟨⟨(p : ℤ_[p]) ^ r, 0, 0⟩,
      (mem_level_iff p r).mpr ⟨dvd_rfl, dvd_zero _, dvd_zero _⟩⟩, dvd_zero _⟩
    let b : U.toSubgroup := ⟨⟨⟨0, (p : ℤ_[p]) ^ r, 0⟩,
      (mem_level_iff p r).mpr ⟨dvd_zero _, dvd_rfl, dvd_zero _⟩⟩, dvd_zero _⟩
    have hz := (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp <|
      closedPowerSubgroup_deepCenterSubgroup_le p
        ((isPowerful_iff.mp hpow) (_root_.commutator_def U.toSubgroup ▸
          commutator_mem_commutator (mem_top a) (mem_top b))))).2.2
    rw [Subgroup.coe_commutatorElement, Subgroup.coe_commutatorElement, commutatorElement_eq] at hz
    have hdvd : (p : ℤ_[p]) ^ (2 * r + 1) ∣ (p : ℤ_[p]) ^ (2 * r) := by
      simpa only [a, b, mul_zero, sub_zero, ← pow_add, ← two_mul] using hz
    exact absurd ((pow_dvd_pow_iff PadicInt.prime_p.ne_zero PadicInt.prime_p.not_isUnit).mp hdvd)
      (by omega)
  exact ⟨U, hnotpow, fun hU ↦ hnotpow hU.isPowerful⟩

end HeisenbergGroup

end Examples

end TauCeti
