/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log
public import TauCeti.Topology.Algebra.Group.Powerful
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Heisenberg
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentral.Powerful
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.CohomFp
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Frattini
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Powerful
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Product
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Torsion
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Separation.Connected
import TauCeti.GroupTheory.Index.Basic

/-!
# Uniform pro-`p` groups and constant lower-`p`-series indices

A topological group `G` is **uniform** for `p` (`TauCeti.IsUniform p G`) when `p` is prime and
`G` is profinite (compact and totally disconnected), pro-`p`, topologically finitely generated,
torsion-free, and powerful (`TauCeti.IsPowerful`, with `[G, G] ≤ closedPowerSubgroup 4 G` at
`p = 2`). Its **dimension** (`TauCeti.uniformDimension p G`) is
`Nat.log p (closedPowerSubgroup p G).index`, which equals its topological generator rank
`TauCeti.topologicalGeneratorRankNat`.

This file proves the constant lower-`p`-series index characterization (DDMS Theorem 4.5): a
topologically finitely generated profinite pro-`p` group is uniform iff it is powerful and all
successive lower-`p`-series indices `[λ_k : λ_{k+1}]` equal `[G : λ_1]`. For a uniform pro-`p`
group of dimension `d`, `[λ_k : λ_{k+1}] = p ^ d` and `[G : λ_k] = [G : G^{p^k}] = p ^ (d * k)`.
Uniformity and dimension are preserved under topological isomorphisms, trivial groups, finite
products, and canonical subgroups `λ_k(G) = G^{p^k}`.

For commutative groups the notion is classical: a commutative profinite group is uniform exactly
when it is topologically isomorphic to `ℤ_p ^ d` for some `d`
(`TauCeti.isUniform_iff_exists_continuousMulEquiv_pi_padicInt`), and then `d` is its dimension.

## Main definitions and results

* `TauCeti.IsUniform`, `TauCeti.uniformDimension`: uniform pro-`p` groups and their dimension.
* `TauCeti.IsPowerful.index_closedPowerSubgroup`, `TauCeti.IsUniform.index_closedPowerSubgroup`,
  `TauCeti.IsUniform.topologicalGeneratorRankNat_eq_log_index`,
  `TauCeti.IsUniform.uniformDimension_eq_topologicalGeneratorRankNat`: `[G : Gᵖ] = p ^ d(G)` and
  `d(G) = log_p [G : Gᵖ]`.
* `TauCeti.IsPowerful.relIndex_pLowerCentralSeries_le`: in a topologically finitely generated
  powerful pro-`p` group every successive index `[λ_k : λ_{k+1}]` is at most `p ^ d(G)`.
* `TauCeti.IsProP.forall_eq_one_of_isOfFinOrder_iff`: torsion-freeness iff no `p`-torsion.
* `TauCeti.IsUniform.gradedPow_bijective`: the `p`-power operator of a uniform group is bijective
  in every degree.
* `TauCeti.IsProP.isUniform_iff_isPowerful_and_relIndex_eq`,
  `TauCeti.IsProP.isUniform_iff_isPowerful_and_forall_natCard_gradedPiece_eq`: DDMS Thm. 4.5.
* `TauCeti.IsUniform.relIndex_pLowerCentralSeries`, `TauCeti.IsUniform.index_pLowerCentralSeries`,
  `TauCeti.IsUniform.index_closedPowerSubgroup_pow`, `TauCeti.IsUniform.natCard_gradedPiece`:
  dimension and index formulas.
* `TauCeti.isUniform_congr`, `TauCeti.IsUniform.prod`, `TauCeti.IsUniform.pi`,
  `TauCeti.IsUniform.to_pLowerCentralSeries`, `TauCeti.IsUniform.to_closedPowerSubgroup_pow`:
  invariance and closure properties with dimension formulas.
* `TauCeti.IsUniform.nonempty_continuousMulEquiv_pi_padicInt`,
  `TauCeti.isUniform_iff_exists_continuousMulEquiv_pi_padicInt`: the commutative uniform groups are
  exactly `ℤ_p ^ d`.
* Witnesses: `Multiplicative ℤ_[p]` (dim `1`), `Multiplicative (ι → ℤ_[p])` (dim `card ι`),
  `HeisenbergGroup.level p m` (nonabelian, dim `3` for `(if p = 2 then 2 else 1) ≤ m`, with
  `level 2 1` non-powerful and an open non-powerful subgroup showing non-inheritance), and
  `Multiplicative (ZMod p)` (powerful, non-uniform, indices `p, 1, 1, …`).

## References

* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, 2nd ed.,
  Cambridge University Press, 1999, Chapter 4 (Theorem 4.5).
* K. Ardakov and K. A. Brown, *Ring-theoretic properties of Iwasawa algebras: a survey*,
  Documenta Math. Extra Vol. Coates (2006), Section 2.3.
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

/-- In a profinite pro-`p` group, every nontrivial element of finite order has a power of
order `p`. -/
theorem IsProP.exists_pow_eq_one_of_isOfFinOrder (hG : IsProP p G) {g : G} (hg : g ≠ 1)
    (hfin : IsOfFinOrder g) : ∃ m : ℕ, g ^ m ≠ 1 ∧ (g ^ m) ^ p = 1 := by
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := g)) hg.symm
  let q := QuotientGroup.mk' U.toSubgroup
  have hqg : q g ≠ 1 := fun h1 ↦ hU ((QuotientGroup.eq_one_iff g).mp h1) rfl
  have hp_dvd : p ∣ orderOf g := ((isProP_iff.mp hG U).dvd_orderOf hqg).trans (orderOf_map_dvd q g)
  have hord := orderOf_eq_prime_iff.mp (orderOf_pow_orderOf_div hfin.orderOf_pos.ne' hp_dvd)
  exact ⟨orderOf g / p, hord.2, hord.1⟩

/-- **Torsion-freeness in a profinite pro-`p` group** is equivalent to having no elements of
order `p`. -/
theorem IsProP.forall_eq_one_of_isOfFinOrder_iff (hG : IsProP p G) :
    (∀ g : G, IsOfFinOrder g → g = 1) ↔ (∀ g : G, g ^ p = 1 → g = 1) :=
  ⟨fun h g hgp ↦ h g (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.out.pos, hgp⟩), fun h g hfin ↦ by
    by_contra hg
    obtain ⟨m, hmne, hmp⟩ := hG.exists_pow_eq_one_of_isOfFinOrder hg hfin
    exact hmne (h (g ^ m) hmp)⟩

end Torsion

/-! ### Uniform pro-`p` groups and their dimension -/

section Defs

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A topological group is **uniform** at `p` when `p` is prime and the group is profinite (compact
and totally disconnected), pro-`p`, topologically finitely generated, torsion-free and powerful
(`TauCeti.IsPowerful`, with the fourth-power condition at `p = 2`). Its dimension is its
topological generator rank `TauCeti.topologicalGeneratorRankNat`, which equals
`TauCeti.uniformDimension p G = Nat.log p (closedPowerSubgroup p G).index` by
`TauCeti.IsUniform.topologicalGeneratorRankNat_eq_log_index`. -/
structure IsUniform : Prop where
  /-- The parameter `p` of a uniform pro-`p` group is prime. -/
  prime : p.Prime
  /-- A uniform group is compact. -/
  compactSpace : CompactSpace G
  /-- A uniform group is totally disconnected. -/
  totallyDisconnectedSpace : TotallyDisconnectedSpace G
  /-- A uniform group is pro-`p`. -/
  isProP : IsProP p G
  /-- A uniform group is topologically finitely generated. -/
  isTopologicallyFinitelyGenerated : IsTopologicallyFinitelyGenerated G
  /-- A uniform group is torsion-free. -/
  isMulTorsionFree : IsMulTorsionFree G
  /-- A uniform group is powerful. -/
  isPowerful : IsPowerful p G

/-- The **dimension** of a uniform pro-`p` group `G`, defined as
`Nat.log p (closedPowerSubgroup p G).index`. -/
noncomputable def uniformDimension : ℕ :=
  Nat.log p (closedPowerSubgroup p G).index

variable {p G}

/-- Unfolding lemma for `TauCeti.uniformDimension`. -/
theorem uniformDimension_def :
    uniformDimension p G = Nat.log p (closedPowerSubgroup p G).index := by
  rw [uniformDimension]

/-- The cardinality of `gr_0(G)` is the index `[G : λ_1(G)]`. -/
theorem natCard_gradedPiece_zero_eq_index (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    Nat.card (gradedPiece p G 0) = (pLowerCentralSeries p G 1).index := by
  rw [Nat.card_congr (gradedPieceZeroEquiv p G).toEquiv, Nat.card_congr Additive.toMul,
    Subgroup.index_eq_card]

end Defs

/-! ### Index, dimension, and constant lower-`p`-series indices -/

section ConstantIndex

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Index

/-- **The index of `Gᵖ` in a powerful group.** For a topologically finitely generated powerful
pro-`p` group, the closed power subgroup `Gᵖ` has index `p ^ d`, where `d` is the topological
generator rank: `Gᵖ` is the first term of the lower `p`-series, which is the Frattini
subgroup. -/
theorem IsPowerful.index_closedPowerSubgroup [hp : Fact p.Prime] [CompactSpace G]
    [TotallyDisconnectedSpace G] (hG : IsPowerful p G) (hP : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    (closedPowerSubgroup p G).index = p ^ topologicalGeneratorRankNat G hfg := by
  rw [hG.closedPowerSubgroup_eq_pLowerCentralSeries_one,
    pLowerCentralSeries_one_eq_proPFrattini hp.out, Subgroup.index_eq_card,
    hP.natCard_quotient_proPFrattini hfg]

/-- **The index of `Gᵖ` in a uniform group** is `p ^ d`, where `d` is the topological generator
rank. -/
theorem IsUniform.index_closedPowerSubgroup (hG : IsUniform p G) :
    (closedPowerSubgroup p G).index =
      p ^ topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated :=
  have := Fact.mk hG.prime
  have := hG.compactSpace
  have := hG.totallyDisconnectedSpace
  hG.isPowerful.index_closedPowerSubgroup hG.isProP _

/-- **The topological generator rank of a uniform group** is `log_p [G : Gᵖ]`. -/
theorem IsUniform.topologicalGeneratorRankNat_eq_log_index (hG : IsUniform p G) :
    topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated =
      Nat.log p (closedPowerSubgroup p G).index := by
  rw [hG.index_closedPowerSubgroup, Nat.log_pow hG.prime.one_lt]

/-- **The dimension of a uniform pro-`p` group equals its topological generator rank.** -/
theorem IsUniform.uniformDimension_eq_topologicalGeneratorRankNat (hU : IsUniform p G) :
    uniformDimension p G =
      topologicalGeneratorRankNat G hU.isTopologicallyFinitelyGenerated :=
  hU.topologicalGeneratorRankNat_eq_log_index.symm

/-- In a uniform pro-`p` group `G`, `[G : G^p] = p ^ uniformDimension p G`. -/
theorem IsUniform.index_closedPowerSubgroup_eq_pow_uniformDimension (hU : IsUniform p G) :
    (closedPowerSubgroup p G).index = p ^ uniformDimension p G := by
  rw [hU.uniformDimension_eq_topologicalGeneratorRankNat, hU.index_closedPowerSubgroup]

/-- **The successive indices of the lower `p`-series of a powerful group are at most `p ^ d`**:
for a topologically finitely generated powerful pro-`p` group, `[λ_k : λ_{k+1}] ≤ p ^ d` for every
`k`, where `d` is the topological generator rank. At `k = 0` this is an equality, by
`TauCeti.IsPowerful.index_closedPowerSubgroup` and
`TauCeti.IsPowerful.closedPowerSubgroup_eq_pLowerCentralSeries_one`. -/
theorem IsPowerful.relIndex_pLowerCentralSeries_le [hp : Fact p.Prime] [CompactSpace G]
    [TotallyDisconnectedSpace G] (hG : IsPowerful p G) (hP : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (k : ℕ) :
    (pLowerCentralSeries p G (k + 1)).relIndex (pLowerCentralSeries p G k) ≤
      p ^ topologicalGeneratorRankNat G hfg := by
  induction k with
  | zero =>
    rw [pLowerCentralSeries_zero, Subgroup.relIndex_top_right,
      ← hG.closedPowerSubgroup_eq_pLowerCentralSeries_one, hG.index_closedPowerSubgroup hP hfg]
  | succ k ih => exact (hG.relIndex_pLowerCentralSeries_succ_le hp.out hfg k).trans ih

end Index

section PowerSubgroups

/-- **The canonical power subgroups of a uniform group are uniform**: every term
`λ_k = G^{p^k}` (`TauCeti.IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup`) of the lower
`p`-series of a uniform group is uniform. It is open, hence topologically finitely generated, and
powerful by `TauCeti.IsPowerful.to_pLowerCentralSeries`. -/
theorem IsUniform.to_pLowerCentralSeries (hG : IsUniform p G) (k : ℕ) :
    IsUniform p (pLowerCentralSeries p G k) :=
  have := Fact.mk hG.prime
  have := hG.compactSpace
  have := hG.totallyDisconnectedSpace
  { prime := hG.prime
    compactSpace := inferInstance
    totallyDisconnectedSpace := inferInstance
    isProP := hG.isProP.subgroup _
    isTopologicallyFinitelyGenerated := hG.isTopologicallyFinitelyGenerated.of_openSubgroup
      ⟨pLowerCentralSeries p G k, hG.isTopologicallyFinitelyGenerated.isOpen_pLowerCentralSeries
        hG.prime k⟩
    isMulTorsionFree :=
      have := hG.isMulTorsionFree
      Function.Injective.isMulTorsionFree (pLowerCentralSeries p G k).subtype
        (pLowerCentralSeries p G k).subtype_injective
    isPowerful := hG.isPowerful.to_pLowerCentralSeries hG.prime hG.isProP
      hG.isTopologicallyFinitelyGenerated k }

/-- **The closed power subgroups `G^{p^n}` of a uniform group are uniform**: they are the terms of
the lower `p`-series (`TauCeti.IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup`), which are
uniform by `TauCeti.IsUniform.to_pLowerCentralSeries`. -/
theorem IsUniform.to_closedPowerSubgroup_pow (hG : IsUniform p G) (n : ℕ) :
    IsUniform p (closedPowerSubgroup (p ^ n) G) :=
  have := Fact.mk hG.prime
  have := hG.compactSpace
  have := hG.totallyDisconnectedSpace
  hG.isPowerful.pLowerCentralSeries_eq_closedPowerSubgroup hG.prime hG.isProP
    hG.isTopologicallyFinitelyGenerated n ▸ hG.to_pLowerCentralSeries n

/-- **The `p`-power operator of a uniform group is bijective**: `π` maps `gr_k(G)` bijectively onto
`gr_{k+1}(G)` in every degree. -/
theorem IsUniform.gradedPow_bijective (hG : IsUniform p G) (k : ℕ) :
    Function.Bijective (gradedPow p G k) :=
  have := Fact.mk hG.prime
  have := hG.compactSpace
  have := hG.totallyDisconnectedSpace
  have := hG.isMulTorsionFree
  ⟨hG.isPowerful.gradedPow_injective hG.prime hG.isProP hG.isTopologicallyFinitelyGenerated k,
    hG.isPowerful.gradedPow_surjective hG.prime
      (hG.isTopologicallyFinitelyGenerated.isOpen_pLowerCentralSeries hG.prime _)⟩

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
  have := Fact.mk hG.prime
  have := hG.compactSpace
  have := hG.totallyDisconnectedSpace
  rw [← hG.isPowerful.pLowerCentralSeries_eq_closedPowerSubgroup hG.prime hG.isProP
    hG.isTopologicallyFinitelyGenerated, hG.index_pLowerCentralSeries]

end PowerSubgroups

section Characterization

variable [hp : Fact p.Prime] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Uniformity is powerfulness with constant indices along the lower `p`-series**: a
topologically finitely generated pro-`p` group is uniform exactly when it is powerful and every
successive index `[λ_k : λ_{k+1}]` equals `[G : λ_1]`. This is the definition of uniform groups
used by Dixon–du Sautoy–Mann–Segal (Definition 4.1). -/
theorem IsProP.isUniform_iff_isPowerful_and_relIndex_eq (hP : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    IsUniform p G ↔ IsPowerful p G ∧ ∀ k, (pLowerCentralSeries p G (k + 1)).relIndex
      (pLowerCentralSeries p G k) = (pLowerCentralSeries p G 1).index := by
  refine ⟨fun hG ↦ ⟨hG.isPowerful, fun k ↦ ?_⟩, fun ⟨hpow, hidx⟩ ↦
      ⟨hp.out, ‹_›, ‹_›, hP, hfg, ?_, hpow⟩⟩
  · rw [hG.relIndex_pLowerCentralSeries,
      ← hG.isPowerful.closedPowerSubgroup_eq_pLowerCentralSeries_one, hG.index_closedPowerSubgroup]
  · -- Constant indices make the surjections `π` between the finite graded pieces bijective.
    refine hP.isMulTorsionFree_of_gradedPow_injective hp.out fun k ↦ ?_
    have := hfg.finite_gradedPiece hp.out k
    refine ((hpow.gradedPow_surjective hp.out (hfg.isOpen_pLowerCentralSeries hp.out _))
      |>.bijective_of_nat_card_le ?_).1
    rw [natCard_gradedPiece, natCard_gradedPiece, hidx, hidx]

/-- **Constant lower-`p`-series indices characterize uniformity** (Dixon–du Sautoy–Mann–Segal,
Theorem 4.5): a topologically finitely generated profinite pro-`p` group is uniform if and only if
it is powerful and all graded pieces `gr_k(G)` have the same cardinality. -/
theorem IsProP.isUniform_iff_isPowerful_and_forall_natCard_gradedPiece_eq (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    IsUniform p G ↔
      IsPowerful p G ∧ ∀ k, Nat.card (gradedPiece p G k) = Nat.card (gradedPiece p G 0) := by
  rw [hG.isUniform_iff_isPowerful_and_relIndex_eq hfg]
  simp_rw [← natCard_gradedPiece, ← natCard_gradedPiece_zero_eq_index]

end Characterization

namespace IsUniform

/-- In a uniform pro-`p` group `G`, `[G : λ_1(G)] = p ^ uniformDimension p G`. -/
theorem index_pLowerCentralSeries_one (hU : IsUniform p G) :
    (pLowerCentralSeries p G 1).index = p ^ uniformDimension p G := by
  rw [hU.isPowerful.closedPowerSubgroup_eq_pLowerCentralSeries_one.symm,
    hU.index_closedPowerSubgroup_eq_pow_uniformDimension]

/-- The dimension of a uniform pro-`p` group is uniquely determined by `[G : λ_1(G)] = p ^ d`. -/
theorem index_pLowerCentralSeries_one_eq_pow_iff (hU : IsUniform p G) {d : ℕ} :
    (pLowerCentralSeries p G 1).index = p ^ d ↔ d = uniformDimension p G := by
  rw [hU.index_pLowerCentralSeries_one]
  exact ⟨fun h ↦ (Nat.pow_right_injective hU.prime.two_le h).symm, fun h ↦ by rw [h]⟩

/-- There is a unique `d : ℕ` with `[G : λ_1(G)] = p ^ d`, namely `uniformDimension p G`. -/
theorem existsUnique_index_pLowerCentralSeries_one_eq_pow (hU : IsUniform p G) :
    ∃! d : ℕ, (pLowerCentralSeries p G 1).index = p ^ d :=
  ⟨uniformDimension p G, hU.index_pLowerCentralSeries_one,
    fun _ hd ↦ hU.index_pLowerCentralSeries_one_eq_pow_iff.mp hd⟩

/-- Every graded piece `gr_k(G)` of a uniform pro-`p` group has cardinality
`p ^ uniformDimension p G`. -/
theorem natCard_gradedPiece (hU : IsUniform p G) (k : ℕ) :
    Nat.card (gradedPiece p G k) = p ^ uniformDimension p G := by
  rw [TauCeti.natCard_gradedPiece, hU.relIndex_pLowerCentralSeries,
    hU.uniformDimension_eq_topologicalGeneratorRankNat]

end IsUniform

end ConstantIndex

/-! ### Invariance and closure properties -/

section Closure

variable {p : ℕ} {G : Type u} {H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Uniformity transfers across a topological group isomorphism. -/
theorem IsUniform.of_equiv (hG : IsUniform p G) (e : G ≃ₜ* H) : IsUniform p H where
  prime := hG.prime
  compactSpace := have := hG.compactSpace; e.toHomeomorph.compactSpace
  totallyDisconnectedSpace := have := hG.totallyDisconnectedSpace
    e.toHomeomorph.totallyDisconnectedSpace
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

/-- `TauCeti.uniformDimension` is invariant under topological group isomorphism. -/
theorem uniformDimension_congr (e : G ≃ₜ* H) : uniformDimension p G = uniformDimension p H := by
  rw [uniformDimension_def, uniformDimension_def, ← e.map_closedPowerSubgroup_eq]
  exact congrArg (Nat.log p) (Subgroup.index_map_equiv (closedPowerSubgroup p G) e.toMulEquiv).symm

variable (p G) in
/-- **The trivial group is uniform**, of dimension `0` by `TauCeti.uniformDimension_of_subsingleton`
and `TauCeti.topologicalGeneratorRankNat_of_subsingleton`. -/
theorem isUniform_of_subsingleton [hp : Fact p.Prime] [Subsingleton G] : IsUniform p G where
  prime := hp.out
  compactSpace := inferInstance
  totallyDisconnectedSpace := inferInstance
  isProP := IsPGroup.isProP fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  isTopologicallyFinitelyGenerated := (Set.finite_empty (α := G)).isTopologicallyFinitelyGenerated
    (Subsingleton.elim _ _)
  isMulTorsionFree := ⟨fun _ _ a b _ _ ↦ Subsingleton.elim a b⟩
  isPowerful := isPowerful_of_isMulCommutative

/-- The dimension of a trivial (subsingleton) topological group is `0`. -/
@[simp]
theorem uniformDimension_of_subsingleton [Subsingleton G] : uniformDimension p G = 0 := by
  rw [uniformDimension_def, closedPowerSubgroup_of_subsingleton, Subgroup.index_top,
    Nat.log_one_right]

/-- **A product of two uniform groups is uniform.** -/
theorem IsUniform.prod (hG : IsUniform p G) (hH : IsUniform p H) : IsUniform p (G × H) where
  prime := hG.prime
  compactSpace := have := hG.compactSpace; have := hH.compactSpace; inferInstance
  totallyDisconnectedSpace :=
    have := hG.totallyDisconnectedSpace; have := hH.totallyDisconnectedSpace; inferInstance
  isProP := hG.isProP.prod hH.isProP
  isTopologicallyFinitelyGenerated :=
    hG.isTopologicallyFinitelyGenerated.prod hH.isTopologicallyFinitelyGenerated
  isMulTorsionFree :=
    have := hG.isMulTorsionFree
    have := hH.isMulTorsionFree
    inferInstance
  isPowerful := hG.isPowerful.prod hH.isPowerful

/-- The dimension of a binary product of uniform pro-`p` groups is the sum of their dimensions. -/
theorem IsUniform.uniformDimension_prod (hG : IsUniform p G) (hH : IsUniform p H) :
    uniformDimension p (G × H) = uniformDimension p G + uniformDimension p H := by
  rw [uniformDimension_def, closedPowerSubgroup_prod, Subgroup.index_prod,
    hG.index_closedPowerSubgroup_eq_pow_uniformDimension,
    hH.index_closedPowerSubgroup_eq_pow_uniformDimension, ← pow_add,
    Nat.log_pow hG.prime.one_lt]

/-- A finite indexed product of uniform pro-`p` groups is uniform. -/
theorem IsUniform.pi [hp : Fact p.Prime] {ι : Type*} [Finite ι] {F : ι → Type*}
    [∀ i, Group (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, IsTopologicalGroup (F i)]
    (hF : ∀ i, IsUniform p (F i)) : IsUniform p (∀ i, F i) where
  prime := hp.out
  compactSpace := have := fun i ↦ (hF i).compactSpace; inferInstance
  totallyDisconnectedSpace := have := fun i ↦ (hF i).totallyDisconnectedSpace; inferInstance
  isProP := IsProP.pi fun i ↦ (hF i).isProP
  isTopologicallyFinitelyGenerated :=
    IsTopologicallyFinitelyGenerated.pi fun i ↦ (hF i).isTopologicallyFinitelyGenerated
  isMulTorsionFree :=
    have := fun i ↦ (hF i).isMulTorsionFree
    inferInstance
  isPowerful := IsPowerful.pi fun i ↦ (hF i).isPowerful

/-- The dimension of a finite indexed product of uniform pro-`p` groups is the sum of their
dimensions. -/
theorem IsUniform.uniformDimension_pi {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, Group (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, IsTopologicalGroup (F i)]
    (hF : ∀ i, IsUniform p (F i)) :
    uniformDimension p (∀ i, F i) = ∑ i, uniformDimension p (F i) := by
  by_cases hne : Nonempty ι
  · rw [uniformDimension_def, closedPowerSubgroup_pi, Subgroup.index_pi',
      Finset.prod_congr rfl fun i _ ↦ (hF i).index_closedPowerSubgroup_eq_pow_uniformDimension,
      Finset.prod_pow_eq_pow_sum, Nat.log_pow (hF (Classical.arbitrary ι)).prime.one_lt]
  · have : IsEmpty ι := not_nonempty_iff.mp hne
    simp [uniformDimension_of_subsingleton]

section CanonicalSubgroups

/-- Every term `λ_k(G)` of the lower `p`-series of a uniform pro-`p` group `G` has the same
dimension as `G`. -/
theorem IsUniform.uniformDimension_pLowerCentralSeries (hU : IsUniform p G) (k : ℕ) :
    uniformDimension p (TauCeti.pLowerCentralSeries p G k) = uniformDimension p G := by
  have := Fact.mk hU.prime
  have := hU.compactSpace
  have := hU.totallyDisconnectedSpace
  have h1 := hU.isProP.pLowerCentralSeries_pLowerCentralSeries_eq_subgroupOf hU.isPowerful k 1
  exact Nat.pow_right_injective hU.prime.two_le <| by
    dsimp only
    rw [← (hU.to_pLowerCentralSeries k).index_pLowerCentralSeries_one, h1,
      ← Subgroup.relIndex, hU.relIndex_pLowerCentralSeries k,
      ← hU.uniformDimension_eq_topologicalGeneratorRankNat]

/-- Every canonical closed power subgroup `G^{p^k}` of a uniform pro-`p` group `G` has the same
dimension as `G`. -/
theorem IsUniform.uniformDimension_closedPowerSubgroup_pow (hU : IsUniform p G) (k : ℕ) :
    uniformDimension p (closedPowerSubgroup (p ^ k) G) = uniformDimension p G := by
  have := Fact.mk hU.prime
  have := hU.compactSpace
  have := hU.totallyDisconnectedSpace
  exact hU.isProP.pLowerCentralSeries_eq_closedPowerSubgroup hU.isPowerful k ▸
    hU.uniformDimension_pLowerCentralSeries k

end CanonicalSubgroups

end Closure

/-! ### Commutative uniform pro-`p` groups -/

section PadicInt

variable (p : ℕ) [hp : Fact p.Prime]

/-- **`ℤ_p ^ X` is uniform** for finite `X`, of dimension `#X` by
`TauCeti.topologicalGeneratorRankNat_multiplicative_pi_padicInt`. -/
theorem isUniform_multiplicative_pi_padicInt (X : Type*) [Finite X] :
    IsUniform p (Multiplicative (X → ℤ_[p])) where
  prime := hp.out
  compactSpace := inferInstance
  totallyDisconnectedSpace := inferInstance
  isProP := isProP_multiplicative_pi_padicInt p X
  isTopologicallyFinitelyGenerated :=
    isTopologicallyFinitelyGenerated_multiplicative_pi_padicInt p X
  isMulTorsionFree := inferInstance
  isPowerful := isPowerful_of_isMulCommutative

/-- **`ℤ_p` is uniform**, of dimension `1` by
`TauCeti.topologicalGeneratorRankNat_multiplicative_padicInt`. -/
theorem isUniform_multiplicative_padicInt :
    IsUniform p (Multiplicative ℤ_[p]) where
  prime := hp.out
  compactSpace := inferInstance
  totallyDisconnectedSpace := inferInstance
  isProP := isProP_multiplicative_padicInt p
  isTopologicallyFinitelyGenerated := isTopologicallyFinitelyGenerated_multiplicative_padicInt p
  isMulTorsionFree := inferInstance
  isPowerful := isPowerful_of_isMulCommutative

end PadicInt

section Commutative

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommGroup A] [TopologicalSpace A]
  [IsTopologicalGroup A] [CompactSpace A] [TotallyDisconnectedSpace A]

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

variable (p : ℕ) [hp : Fact p.Prime]

/-- The additive group `ℤ_p` has uniform dimension `1`. -/
@[simp]
theorem uniformDimension_multiplicative_padicInt :
    uniformDimension p (Multiplicative ℤ_[p]) = 1 := by
  rw [(isUniform_multiplicative_padicInt p).uniformDimension_eq_topologicalGeneratorRankNat,
    topologicalGeneratorRankNat_multiplicative_padicInt]

/-- For every `Fintype ι`, the free `ℤ_p`-module `ℤ_p^ι` has uniform dimension `Fintype.card ι`. -/
@[simp]
theorem uniformDimension_multiplicative_pi_padicInt (ι : Type*) [Fintype ι] :
    uniformDimension p (Multiplicative (ι → ℤ_[p])) = Fintype.card ι := by
  rw [← uniformDimension_congr (ContinuousMulEquiv.piMultiplicative fun _ : ι ↦ ℤ_[p]).symm,
    IsUniform.uniformDimension_pi fun _ : ι ↦ isUniform_multiplicative_padicInt p]
  simp

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

/-- The degree-zero lower-`p`-series index of `ℤ/p` is `p`. -/
theorem index_pLowerCentralSeries_multiplicative_zmod_zero :
    (pLowerCentralSeries p (Multiplicative (ZMod p)) 1).index = p := by
  rw [pLowerCentralSeries_one_eq_proPFrattini hp.out, proPFrattini_multiplicative_zmod_eq_bot,
    Subgroup.index_bot, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- Every higher successive lower-`p`-series index of `ℤ/p` is `1`, so the lower-`p`-series
indices of `ℤ/p` are `p, 1, 1, …`. -/
theorem index_pLowerCentralSeries_multiplicative_zmod_succ (k : ℕ) :
    ((pLowerCentralSeries p (Multiplicative (ZMod p)) (k + 2)).subgroupOf
      (pLowerCentralSeries p (Multiplicative (ZMod p)) (k + 1))).index = 1 := by
  have h1 : pLowerCentralSeries p (Multiplicative (ZMod p)) 1 = ⊥ :=
    (pLowerCentralSeries_one_eq_proPFrattini hp.out).trans
      (proPFrattini_multiplicative_zmod_eq_bot p)
  have hbot : ∀ m, 1 ≤ m → pLowerCentralSeries p (Multiplicative (ZMod p)) m = ⊥ := fun m hm ↦
    le_bot_iff.mp ((pLowerCentralSeries_antitone hm).trans h1.le)
  rw [hbot (k + 2) (by omega), hbot (k + 1) (by omega), Subgroup.bot_subgroupOf,
    Subgroup.index_bot, Nat.card_unique]

/-! ### Nonabelian uniform witness: congruence levels of the `p`-adic Heisenberg group -/

namespace HeisenbergGroup

/-- The Heisenberg group over `ℤ_[p]` is torsion-free. -/
theorem eq_one_of_isOfFinOrder_padicInt {a : HeisenbergGroup ℤ_[p]} (ha : IsOfFinOrder a) :
    a = 1 := by
  obtain ⟨n, hn, han⟩ := isOfFinOrder_iff_pow_eq_one.mp ha
  rw [pow_eq] at han
  have hn0 : (n : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx : a.x = 0 := by simpa [nsmul_eq_mul, hn0] using congrArg HeisenbergGroup.x han
  have hy : a.y = 0 := by simpa [nsmul_eq_mul, hn0] using congrArg HeisenbergGroup.y han
  have hz : a.z = 0 := by simpa [hx, hy, nsmul_eq_mul, hn0] using congrArg HeisenbergGroup.z han
  ext <;> simp [hx, hy, hz]

/-- The Heisenberg group over `ℤ_[p]` is topologically finitely generated, by the three elementary
unipotent generators `(1, 0, 0)`, `(0, 1, 0)`, `(0, 0, 1)`. -/
theorem isTopologicallyFinitelyGenerated_padicInt :
    IsTopologicallyFinitelyGenerated (HeisenbergGroup ℤ_[p]) := by
  let s : Set (HeisenbergGroup ℤ_[p]) := {⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩}
  refine (by simp [s] : s.Finite).isTopologicallyFinitelyGenerated (eq_top_iff.mpr fun a _ ↦ ?_)
  have hpow : ∀ {g : HeisenbergGroup ℤ_[p]}, g ∈ s → ∀ (c : ℤ_[p]),
      (isProP_padicInt p).padicPow g c ∈ (Subgroup.closure s).topologicalClosure := fun hg c ↦
    Subgroup.topologicalClosure_mono (Subgroup.closure_mono (Set.singleton_subset_iff.mpr hg))
      (((isProP_padicInt p).mem_topologicalClosure_closure_singleton_iff).mpr ⟨c, rfl⟩)
  exact (by ext <;> simp : a = ⟨0, 0, a.z - a.x * a.y⟩ * ⟨a.x, 0, 0⟩ * ⟨0, a.y, 0⟩) ▸
    mul_mem (mul_mem
      (by simpa [padicPow_eq] using hpow (g := ⟨0, 0, 1⟩) (by simp [s]) (a.z - a.x * a.y))
      (by simpa [padicPow_eq] using hpow (g := ⟨1, 0, 0⟩) (by simp [s]) a.x))
      (by simpa [padicPow_eq] using hpow (g := ⟨0, 1, 0⟩) (by simp [s]) a.y)

/-- Every congruence level `HeisenbergGroup.level p m` is nonabelian. -/
theorem not_isMulCommutative_level (m : ℕ) : ¬ IsMulCommutative (level p m).toSubgroup := by
  intro hcomm
  let a : (level p m).toSubgroup :=
    ⟨⟨(p : ℤ_[p]) ^ m, 0, 0⟩, (mem_level_iff p m).mpr ⟨dvd_rfl, dvd_zero _, dvd_zero _⟩⟩
  let b : (level p m).toSubgroup :=
    ⟨⟨0, (p : ℤ_[p]) ^ m, 0⟩, (mem_level_iff p m).mpr ⟨dvd_zero _, dvd_rfl, dvd_zero _⟩⟩
  have hz := congrArg (fun g : (level p m).toSubgroup ↦ g.val.z) (hcomm.is_comm.comm a b)
  simp only [Subgroup.coe_mul, mul_z, zero_add, add_zero, mul_zero, a, b] at hz
  exact pow_ne_zero (m + m) (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    (show (p : ℤ_[p]) ^ (m + m) = 0 by rw [pow_add]; exact hz)

/-- For every prime `p` and every `m ≥ 1` (with `m ≥ 2` at `p = 2`), the congruence level
`HeisenbergGroup.level p m` is powerful. -/
theorem isPowerful_level {m : ℕ} (hm : (if p = 2 then 2 else 1) ≤ m) :
    IsPowerful p (level p m).toSubgroup := by
  set r : ℕ := if p = 2 then 2 else 1
  have hr : p ^ r = if p = 2 then 4 else p := by by_cases hp2 : p = 2 <;> simp [r, hp2]
  rw [isPowerful_iff, commutator_def, commutator_le]; rintro a _ b _
  obtain ⟨⟨xa, hxa⟩, ⟨ya, hya⟩, -⟩ := (mem_level_iff p m).mp a.property
  obtain ⟨⟨xb, hxb⟩, ⟨yb, hyb⟩, -⟩ := (mem_level_iff p m).mp b.property
  let c : (level p m).toSubgroup :=
    ⟨⟨0, 0, (p : ℤ_[p]) ^ (2 * m - r) * (xa * yb - xb * ya)⟩, (mem_level_iff p m).mpr
      ⟨dvd_zero _, dvd_zero _, (pow_dvd_pow (p : ℤ_[p]) (by omega)).trans (dvd_mul_right _ _)⟩⟩
  have hcomm : ⁅a, b⁆ = c ^ (if p = 2 then 4 else p) := Subtype.ext <| by
    have hval : ((⁅a, b⁆ : (level p m).toSubgroup) : HeisenbergGroup ℤ_[p]) =
        ⁅(a : HeisenbergGroup ℤ_[p]), (b : HeisenbergGroup ℤ_[p])⁆ :=
      map_commutatorElement (level p m).toSubgroup.subtype a b
    rw [hval, commutatorElement_eq, Subgroup.coe_pow, ← hr, pow_eq]
    refine HeisenbergGroup.ext (by simp [c]) (by simp [c]) ?_
    simp only [c, nsmul_eq_mul, Nat.cast_pow, mul_zero, add_zero, hxa, hya, hxb, hyb]
    rw [← mul_assoc ((p : ℤ_[p]) ^ r), ← pow_add, show r + (2 * m - r) = m + m by omega, pow_add]
    ring
  exact hcomm ▸ pow_mem_closedPowerSubgroup c

/-- **Nonabelian uniform pro-`p` group of dimension `3`**: for every prime `p` and
`(if p = 2 then 2 else 1) ≤ m`, `HeisenbergGroup.level p m` is uniform. -/
theorem isUniform_level {m : ℕ} (hm : (if p = 2 then 2 else 1) ≤ m) :
    IsUniform p (level p m).toSubgroup where
  prime := hp.out
  compactSpace := inferInstance
  totallyDisconnectedSpace := inferInstance
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
  · rw [mem_subgroupOf, Subgroup.coe_pow, pow_eq]
    obtain ⟨hx, hy, hz⟩ := (mem_level_iff p m).mp a.property
    have hmul : ∀ {w : ℤ_[p]}, (p : ℤ_[p]) ^ m ∣ w → (p : ℤ_[p]) ^ (m + 1) ∣ (p : ℤ_[p]) * w :=
      fun ⟨c, hc⟩ ↦ ⟨c, by rw [hc, pow_succ', mul_assoc]⟩
    have hxy : (p : ℤ_[p]) ^ (m + 1) ∣ (p.choose 2 : ℤ_[p]) * (a.val.x * a.val.y) :=
      ((pow_dvd_pow (p : ℤ_[p]) (by omega : m + 1 ≤ m + m)).trans
        (pow_add (p : ℤ_[p]) m m ▸ mul_dvd_mul hx hy)).trans (dvd_mul_left _ _)
    exact (mem_level_iff p (m + 1)).mpr ⟨by simpa [nsmul_eq_mul] using hmul hx,
      by simpa [nsmul_eq_mul] using hmul hy,
      by simpa [nsmul_eq_mul] using dvd_add (hmul hz) hxy⟩
  · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ := (mem_level_iff p (m + 1)).mp (mem_subgroupOf.mp ha)
    let u : (level p m).toSubgroup := ⟨⟨(p : ℤ_[p]) ^ m * x, 0, 0⟩,
      (mem_level_iff p m).mpr ⟨dvd_mul_right _ _, dvd_zero _, dvd_zero _⟩⟩
    let v : (level p m).toSubgroup := ⟨⟨0, (p : ℤ_[p]) ^ m * y, 0⟩,
      (mem_level_iff p m).mpr ⟨dvd_zero _, dvd_mul_right _ _, dvd_zero _⟩⟩
    let w : (level p m).toSubgroup :=
      ⟨⟨0, 0, (p : ℤ_[p]) ^ m * (z - (p : ℤ_[p]) ^ (m + 1) * (x * y))⟩,
        (mem_level_iff p m).mpr ⟨dvd_zero _, dvd_zero _, dvd_mul_right _ _⟩⟩
    have hprod : w ^ p * u ^ p * v ^ p = a := Subtype.ext <| by
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, pow_eq, u, v, w]
      ext <;> simp [hx, hy, hz, nsmul_eq_mul, pow_succ', mul_assoc]; ring
    exact hprod ▸ mul_mem (mul_mem (pow_mem_closedPowerSubgroup w)
      (pow_mem_closedPowerSubgroup u)) (pow_mem_closedPowerSubgroup v)

/-- For every `1 ≤ m`, `HeisenbergGroup.level p m` has uniform dimension `3`. -/
@[simp]
theorem uniformDimension_level {m : ℕ} (hm : 1 ≤ m) :
    uniformDimension p (level p m).toSubgroup = 3 := by
  have hrel : ((level p (m + 1)).toSubgroup.subgroupOf (level p m).toSubgroup).index = p ^ 3 := by
    have hmul := Subgroup.relIndex_mul_index (level_antitone p (Nat.le_succ m))
    rw [index_level, index_level] at hmul
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos (3 * m))
    rw [← Subgroup.relIndex, hmul, ← pow_add]; congr 1; omega
  rw [uniformDimension_def, closedPowerSubgroup_level p hm, hrel, Nat.log_pow hp.out.one_lt]

/-- At `p = 2`, `HeisenbergGroup.level 2 1` is not powerful: every fourth power lies in `level 2 3`,
whereas `⁅(2, 0, 0), (0, 2, 0)⁆ = (0, 0, 4) ∉ level 2 3`. -/
theorem not_isPowerful_level_two_one : ¬ IsPowerful 2 (level 2 1).toSubgroup := fun hpow ↦ by
  have hle : closedPowerSubgroup 4 (level 2 1).toSubgroup ≤
      (level 2 3).toSubgroup.subgroupOf (level 2 1).toSubgroup :=
    (closedPowerSubgroup_le_iff ((level 2 3).isClosed.preimage continuous_subtypeVal)).mpr
      fun a ↦ by
        rw [mem_subgroupOf, Subgroup.coe_pow, pow_eq]
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ := (mem_level_iff 2 1).mp a.property
        refine (mem_level_iff 2 3).mpr ⟨⟨x, by simp [hx]; ring⟩, ⟨y, by simp [hy]; ring⟩,
          ⟨z + 3 * (x * y), by simp [show Nat.choose 4 2 = 6 from rfl, hx, hy, hz]; ring⟩⟩
  let a : (level 2 1).toSubgroup :=
    ⟨⟨2, 0, 0⟩, (mem_level_iff 2 1).mpr ⟨by simp, dvd_zero _, dvd_zero _⟩⟩
  let b : (level 2 1).toSubgroup :=
    ⟨⟨0, 2, 0⟩, (mem_level_iff 2 1).mpr ⟨dvd_zero _, by simp, dvd_zero _⟩⟩
  have hz := ((mem_level_iff 2 3).mp (mem_subgroupOf.mp <|
    hle ((isPowerful_two_iff.mp hpow) (_root_.commutator_def (level 2 1).toSubgroup ▸
      commutator_mem_commutator (mem_top a) (mem_top b))))).2.2
  have hval : ((⁅a, b⁆ : (level 2 1).toSubgroup) : HeisenbergGroup ℤ_[2]) =
      ⁅(a : HeisenbergGroup ℤ_[2]), (b : HeisenbergGroup ℤ_[2])⁆ :=
    map_commutatorElement (level 2 1).toSubgroup.subtype a b
  rw [hval, commutatorElement_eq] at hz
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
    let hr1 : 1 ≤ r := by by_cases hp2 : p = 2 <;> simp [r, hp2]
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
  rw [mem_subgroupOf, mem_subgroupOf, Subgroup.coe_pow, Subgroup.coe_pow, pow_eq]
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
    (fun _ ha ↦ ((mem_level_iff p (2 * r)).mp (mem_subgroupOf.mp ha)).2.2)
    ((level p (2 * r)).isOpen.preimage continuous_subtypeVal)⟩
  have hnotpow : ¬ IsPowerful p U.toSubgroup := fun hpow ↦ by
    let a : U.toSubgroup := ⟨⟨⟨(p : ℤ_[p]) ^ r, 0, 0⟩,
      (mem_level_iff p r).mpr ⟨dvd_rfl, dvd_zero _, dvd_zero _⟩⟩, dvd_zero _⟩
    let b : U.toSubgroup := ⟨⟨⟨0, (p : ℤ_[p]) ^ r, 0⟩,
      (mem_level_iff p r).mpr ⟨dvd_zero _, dvd_rfl, dvd_zero _⟩⟩, dvd_zero _⟩
    have hz := (mem_subgroupOf.mp (mem_subgroupOf.mp <|
      closedPowerSubgroup_deepCenterSubgroup_le p
        ((isPowerful_iff.mp hpow) (_root_.commutator_def U.toSubgroup ▸
          commutator_mem_commutator (mem_top a) (mem_top b))))).2.2
    have hval : ((⁅a, b⁆ : U.toSubgroup) : HeisenbergGroup ℤ_[p]) =
        ⁅(a.val : HeisenbergGroup ℤ_[p]), (b.val : HeisenbergGroup ℤ_[p])⁆ :=
      (map_commutatorElement U.toSubgroup.subtype a b ▸ rfl :
        ((⁅a, b⁆ : U.toSubgroup) : (level p r).toSubgroup).val = (⁅a.val, b.val⁆ : _).val).trans
        (map_commutatorElement (level p r).toSubgroup.subtype a.val b.val)
    rw [hval, commutatorElement_eq] at hz
    have hdvd : (p : ℤ_[p]) ^ (2 * r + 1) ∣ (p : ℤ_[p]) ^ (2 * r) := by
      simpa only [a, b, mul_zero, sub_zero, ← pow_add, ← two_mul] using hz
    exact absurd ((pow_dvd_pow_iff PadicInt.prime_p.ne_zero PadicInt.prime_p.not_isUnit).mp hdvd)
      (by omega)
  exact ⟨U, hnotpow, fun hU ↦ hnotpow hU.isPowerful⟩

end HeisenbergGroup

end Examples

end TauCeti
