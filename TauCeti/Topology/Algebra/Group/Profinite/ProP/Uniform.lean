/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Powerful
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentral.Powerful
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.CohomFp
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Product
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Torsion

/-!
# Uniform pro-`p` groups

A pro-`p` group is **uniform** when it is topologically finitely generated, torsion-free and
powerful (`TauCeti.IsPowerful`, with the fourth-power condition at `p = 2`). Uniform groups are the
open subgroups through which Lazard's theory describes compact `p`-adic analytic groups: every
compact `p`-adic analytic group has an open normal uniform subgroup, and the completed group
algebra of a uniform group behaves like a power series ring in `d` variables. This file sets up
the predicate, its closure properties and its first invariant.

The **dimension** of a uniform group `U` is its topological generator rank
`TauCeti.topologicalGeneratorRankNat U`, the least number `d` of topological generators. In a
powerful group the commutators are already `p`-th powers, so the closed power subgroup `Uᵖ` is the
first term `λ_1 = Φ(U)` of the lower `p`-series; hence `[U : Uᵖ] = p ^ d`
(`TauCeti.IsUniform.index_closedPowerSubgroup`) and `d = log_p [U : Uᵖ]`. Torsion-freeness makes
every `p`-power operator `π : gr_k(U) → gr_{k+1}(U)` bijective, so every successive index
`[λ_k : λ_{k+1}]` of the lower `p`-series is `p ^ d` and `[U : U^{p^k}] = p ^ (d * k)`. Conversely
a topologically finitely generated powerful pro-`p` group with constant successive indices is
torsion-free, so the predicate agrees with the definition of uniformity by constant indices.

For commutative groups the notion is classical: a commutative profinite group is uniform exactly
when it is topologically isomorphic to `ℤ_p ^ d` for some `d`
(`TauCeti.isUniform_iff_exists_continuousMulEquiv_pi_padicInt`), and then `d` is its dimension.
By contrast `ℤ/p` is powerful but not uniform, since it has torsion.

## Main definitions

* `TauCeti.IsUniform p G`: `G` is pro-`p`, topologically finitely generated, torsion-free and
  powerful.

## Main results

* `TauCeti.IsPowerful.index_closedPowerSubgroup`, `TauCeti.IsUniform.index_closedPowerSubgroup`:
  for a topologically finitely generated powerful pro-`p` group, `[G : Gᵖ] = p ^ d(G)`.
* `TauCeti.IsUniform.topologicalGeneratorRankNat_eq_log_index`: the dimension is
  `log_p [G : Gᵖ]`.
* `TauCeti.IsPowerful.relIndex_pLowerCentralSeries_le`: in a topologically finitely generated
  powerful pro-`p` group every successive index `[λ_k : λ_{k+1}]` of the lower `p`-series is at
  most `p ^ d(G)`.
* `TauCeti.isUniform_congr`, `TauCeti.IsUniform.prod`: uniformity is invariant under topological
  group isomorphism and stable under binary products.
* `TauCeti.IsUniform.to_pLowerCentralSeries`, `TauCeti.IsUniform.to_closedPowerSubgroup_pow`: the
  terms `λ_k = G^{p^k}` of the lower `p`-series of a uniform group are uniform.
* `TauCeti.IsUniform.gradedPow_bijective`: the `p`-power operator of a uniform group is bijective
  in every degree.
* `TauCeti.IsUniform.relIndex_pLowerCentralSeries`, `TauCeti.IsUniform.index_pLowerCentralSeries`,
  `TauCeti.IsUniform.index_closedPowerSubgroup_pow`: `[λ_k : λ_{k+1}] = p ^ d` and
  `[G : G^{p^k}] = [G : λ_k] = p ^ (d * k)`.
* `TauCeti.IsProP.isUniform_iff_isPowerful_and_relIndex_eq`: a topologically finitely generated
  pro-`p` group is uniform exactly when it is powerful with every `[λ_k : λ_{k+1}]` equal to
  `[G : λ_1]`.
* `TauCeti.isUniform_of_subsingleton`: the trivial group is uniform; its dimension is `0` by
  `TauCeti.topologicalGeneratorRankNat_of_subsingleton`.
* `TauCeti.isUniform_multiplicative_pi_padicInt`, `TauCeti.isUniform_multiplicative_padicInt`:
  `ℤ_p ^ X` for finite `X` is uniform, of dimension `#X`; in particular `ℤ_p` is uniform of
  dimension `1`.
* `TauCeti.IsUniform.nonempty_continuousMulEquiv_pi_padicInt`,
  `TauCeti.isUniform_iff_exists_continuousMulEquiv_pi_padicInt`: the commutative uniform groups are
  exactly the groups `ℤ_p ^ d`, with `d` the dimension.
* `TauCeti.not_isUniform_multiplicative_zmod`: `ℤ/p` is powerful but not uniform.

## References

* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, second
  edition, Chapter 4. Their Definition 4.1 asks instead for constant indices along the lower
  `p`-series; Theorem 4.5 shows that for finitely generated powerful pro-`p` groups this is
  equivalent to torsion-freeness, the form used here
  (`TauCeti.IsProP.isUniform_iff_isPowerful_and_relIndex_eq`).
* K. Ardakov and K. A. Brown, *Ring-theoretic properties of Iwasawa algebras: a survey*, §2.3.
-/

public section

namespace TauCeti

open Multiplicative

universe u v

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

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Uniformity is invariant under topological group isomorphism. -/
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

variable (p G) in
/-- **The trivial group is uniform**, of dimension `0` by
`TauCeti.topologicalGeneratorRankNat_of_subsingleton`. -/
theorem isUniform_of_subsingleton [Subsingleton G] : IsUniform p G where
  isProP := IsPGroup.isProP fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  isTopologicallyFinitelyGenerated := (Set.finite_empty (α := G)).isTopologicallyFinitelyGenerated
    (Subsingleton.elim _ _)
  isMulTorsionFree := ⟨fun _ _ a b _ _ ↦ Subsingleton.elim a b⟩
  isPowerful := (isPowerful_iff (p := p)).mpr fun g _ ↦ Subsingleton.elim g 1 ▸ one_mem _

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
  isPowerful := hG.isPowerful.to_pLowerCentralSeries hp.out hG.isProP
    hG.isTopologicallyFinitelyGenerated k

/-- **The closed power subgroups `G^{p^n}` of a uniform group are uniform**: they are the terms of
the lower `p`-series (`TauCeti.IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup`), which are
uniform by `TauCeti.IsUniform.to_pLowerCentralSeries`. -/
theorem IsUniform.to_closedPowerSubgroup_pow (hG : IsUniform p G) (n : ℕ) :
    IsUniform p (closedPowerSubgroup (p ^ n) G) :=
  hG.isPowerful.pLowerCentralSeries_eq_closedPowerSubgroup hp.out hG.isProP
    hG.isTopologicallyFinitelyGenerated n ▸ hG.to_pLowerCentralSeries n

/-! ### Constant indices along the lower `p`-series -/

/-- **The `p`-power operator of a uniform group is bijective**: `π` maps `gr_k(G)` bijectively onto
`gr_{k+1}(G)` in every degree. -/
theorem IsUniform.gradedPow_bijective (hG : IsUniform p G) (k : ℕ) :
    Function.Bijective (gradedPow p G k) :=
  have := hG.isMulTorsionFree
  ⟨hG.isPowerful.gradedPow_injective hp.out hG.isProP hG.isTopologicallyFinitelyGenerated k,
    hG.isPowerful.gradedPow_surjective hp.out
      (hG.isTopologicallyFinitelyGenerated.isOpen_pLowerCentralSeries hp.out _)⟩

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
  rw [← hG.isPowerful.pLowerCentralSeries_eq_closedPowerSubgroup hp.out hG.isProP
    hG.isTopologicallyFinitelyGenerated, hG.index_pLowerCentralSeries]

/-- **Uniformity is powerfulness with constant indices along the lower `p`-series**: a
topologically finitely generated pro-`p` group is uniform exactly when it is powerful and every
successive index `[λ_k : λ_{k+1}]` equals `[G : λ_1]`. This is the definition of uniform groups
used by Dixon–du Sautoy–Mann–Segal (Definition 4.1). -/
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
    refine ((hpow.gradedPow_surjective hp.out (hfg.isOpen_pLowerCentralSeries hp.out _))
      |>.bijective_of_nat_card_le ?_).1
    rw [natCard_gradedPiece, natCard_gradedPiece, hidx, hidx]

end PowerSubgroups

section PadicInt

variable (p) [Fact p.Prime]

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

end TauCeti
