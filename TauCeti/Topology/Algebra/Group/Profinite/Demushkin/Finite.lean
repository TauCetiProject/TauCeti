/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.QInvariant
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.RankOne
import Mathlib.Algebra.CharZero.Infinite
import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# `ℤ/2` is the unique finite Demushkin group

A Demushkin group `G` of rank `n` has topological abelianization `G^{ab} ≅ ℤ_p^{n-1} × ℤ_p ⧸ (q)`
(`TauCeti.IsDemushkin.nonempty_continuousMulEquiv_topologicalAbelianization`). If `G^{ab}` is
finite, the free factor `ℤ_p^{n-1}` is finite, so `n = 1`, and a Demushkin group of rank one is
`ℤ/2` (`TauCeti.IsDemushkin.demushkinRank_eq_one_iff`). Hence a Demushkin group is finite exactly
when it is `ℤ/2`, exactly when its rank is one, and exactly when its abelianization is finite;
every Demushkin group at an odd prime, and every Demushkin group of rank at least two, is infinite.
For the finite one the invariants are `n = 1` and `q = 2`, the values Labute lists for `ℤ/2`.

Finiteness is the hypothesis that separates `ℤ/2` from the Demushkin groups of the classification:
the rank formula `n(U) - 2 = [G : U] (n(G) - 2)` for open subgroups and the equality `cd_p G = 2`
hold for infinite Demushkin groups only, and the results here let those statements be read with
the hypothesis `2 ≤ demushkinRank` in place of `Infinite G`.

## Main results

* `TauCeti.IsDemushkin.demushkinRank_eq_one_of_finite_topologicalAbelianization`: a Demushkin group
  with finite abelianization has rank one.
* `TauCeti.IsDemushkin.finite_iff_demushkinRank_eq_one`,
  `TauCeti.IsDemushkin.finite_topologicalAbelianization_iff`: a Demushkin group is finite exactly
  when its rank is one, exactly when its abelianization is finite.
* `TauCeti.IsDemushkin.finite_iff_nonempty_continuousMulEquiv_multiplicative_zmod_two`: **`ℤ/2` is
  the unique finite Demushkin group.**
* `TauCeti.IsDemushkin.infinite_iff_two_le_demushkinRank`: a Demushkin group is infinite exactly
  when its rank is at least two.
* `TauCeti.IsDemushkin.eq_two_of_finite`, `TauCeti.IsDemushkin.infinite_of_ne_two`: a finite
  Demushkin group lives at `p = 2`; at an odd prime every Demushkin group is infinite.
* `TauCeti.IsDemushkin.natCard_eq_two_of_finite`, `TauCeti.IsDemushkin.demushkinQ_eq_two_of_finite`:
  a finite Demushkin group has two elements and `q`-invariant `2`;
  `TauCeti.demushkinQ_multiplicative_zmod_two` records `q(ℤ/2) = 2`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, p. 106
  and Remark 2.
* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (3.9.10).
-/

public section

namespace TauCeti

open CommGroup (torsion)

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

namespace IsDemushkin

variable (hG : IsDemushkin p G)
include hG

/-- **A Demushkin group with finite abelianization has rank one**: in
`G^{ab} ≅ ℤ_p^{n-1} × ℤ_p ⧸ (q)` the free factor `ℤ_p^{n-1}` is finite only for `n = 1`. -/
theorem demushkinRank_eq_one_of_finite_topologicalAbelianization
    [Finite (TopologicalAbelianization G)] : demushkinRank hG = 1 := by
  obtain ⟨e⟩ := hG.nonempty_continuousMulEquiv_topologicalAbelianization
  have : Finite (Multiplicative ((Fin (demushkinRank hG - 1) → ℤ_[p]) ×
      (ℤ_[p] ⧸ Ideal.span {(demushkinQ hG : ℤ_[p])}))) := Finite.of_equiv _ e.toEquiv
  have : Finite ((Fin (demushkinRank hG - 1) → ℤ_[p]) ×
      (ℤ_[p] ⧸ Ideal.span {(demushkinQ hG : ℤ_[p])})) := Finite.of_equiv _ Multiplicative.toAdd
  have hfin : Finite (Fin (demushkinRank hG - 1) → ℤ_[p]) :=
    Finite.prod_left (ℤ_[p] ⧸ Ideal.span {(demushkinQ hG : ℤ_[p])})
  have hpos := hG.demushkinRank_pos
  by_contra hne
  -- For `n ≥ 2` the free factor contains a copy of the infinite ring `ℤ_p`.
  have : Nonempty (Fin (demushkinRank hG - 1)) := ⟨⟨0, by omega⟩⟩
  have : Finite ℤ_[p] := Finite.of_injective (Function.const (Fin (demushkinRank hG - 1)))
    (Function.const_injective (α := Fin (demushkinRank hG - 1)) (β := ℤ_[p]))
  exact not_finite ℤ_[p]

/-- **A finite Demushkin group has rank one.** -/
theorem demushkinRank_eq_one_of_finite [Finite G] : demushkinRank hG = 1 :=
  hG.demushkinRank_eq_one_of_finite_topologicalAbelianization

/-- **A Demushkin group is finite exactly when its rank is one.** -/
theorem finite_iff_demushkinRank_eq_one : Finite G ↔ demushkinRank hG = 1 :=
  ⟨fun _ ↦ hG.demushkinRank_eq_one_of_finite, fun h ↦ by
    obtain ⟨e⟩ := hG.nonempty_continuousMulEquiv_multiplicative_zmod_two_of_demushkinRank_eq_one h
    exact Finite.of_equiv _ e.toEquiv.symm⟩

/-- **`ℤ/2` is the unique finite Demushkin group**: a Demushkin group is finite exactly when it is
topologically isomorphic to `ℤ/2`. -/
theorem finite_iff_nonempty_continuousMulEquiv_multiplicative_zmod_two :
    Finite G ↔ Nonempty (G ≃ₜ* Multiplicative (ZMod 2)) :=
  hG.finite_iff_demushkinRank_eq_one.trans hG.demushkinRank_eq_one_iff

/-- **A Demushkin group is finite exactly when its abelianization is finite.** -/
theorem finite_topologicalAbelianization_iff : Finite (TopologicalAbelianization G) ↔ Finite G :=
  ⟨fun _ ↦ hG.finite_iff_demushkinRank_eq_one.2
    hG.demushkinRank_eq_one_of_finite_topologicalAbelianization, fun _ ↦ inferInstance⟩

/-- **A Demushkin group is infinite exactly when its rank is at least two.** -/
theorem infinite_iff_two_le_demushkinRank : Infinite G ↔ 2 ≤ demushkinRank hG := by
  rw [← not_finite_iff_infinite, hG.finite_iff_demushkinRank_eq_one]
  have := hG.demushkinRank_pos
  omega

/-- A Demushkin group of rank at least two is infinite. -/
theorem infinite_of_two_le_demushkinRank (h : 2 ≤ demushkinRank hG) : Infinite G :=
  hG.infinite_iff_two_le_demushkinRank.2 h

/-- A Demushkin group whose topological generator rank exceeds one is infinite. -/
theorem infinite_of_one_lt_topologicalGeneratorRankNat {hfg : IsTopologicallyFinitelyGenerated G}
    (h : 1 < topologicalGeneratorRankNat G hfg) : Infinite G :=
  hG.infinite_of_two_le_demushkinRank (by rw [demushkinRank_def]; exact h)

/-- An infinite Demushkin group has rank at least two. -/
theorem two_le_demushkinRank_of_infinite [Infinite G] : 2 ≤ demushkinRank hG :=
  hG.infinite_iff_two_le_demushkinRank.1 ‹_›

/-- **A finite Demushkin group lives at `p = 2`.** -/
theorem eq_two_of_finite [Finite G] : p = 2 :=
  hG.eq_two_of_demushkinRank_eq_one hG.demushkinRank_eq_one_of_finite

/-- **At an odd prime every Demushkin group is infinite.** -/
theorem infinite_of_ne_two (hp : p ≠ 2) : Infinite G :=
  not_finite_iff_infinite.1 fun _ ↦ hp hG.eq_two_of_finite

/-- **A finite Demushkin group has two elements.** -/
theorem natCard_eq_two_of_finite [Finite G] : Nat.card G = 2 := by
  obtain ⟨e⟩ := hG.finite_iff_nonempty_continuousMulEquiv_multiplicative_zmod_two.1 ‹_›
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- **The abelianization of a finite Demushkin group has two elements**: it is a quotient of `G`,
which has two elements, and it maps onto `ℤ/2`. -/
theorem natCard_topologicalAbelianization_eq_two_of_finite [Finite G] :
    Nat.card (TopologicalAbelianization G) = 2 := by
  obtain ⟨e⟩ := hG.finite_iff_nonempty_continuousMulEquiv_multiplicative_zmod_two.1 ‹_›
  refine le_antisymm ((Nat.card_le_card_of_surjective _
    (QuotientGroup.mk'_surjective _)).trans_eq hG.natCard_eq_two_of_finite) ?_
  have hsurj : Function.Surjective
      (TopologicalAbelianization.lift (A := Multiplicative (ZMod 2))
        (ContinuousMonoidHom.toContinuousMonoidHom e)) := fun y ↦
    ⟨(e.symm y : G), (TopologicalAbelianization.lift_mk _ _).trans (e.apply_symm_apply y)⟩
  calc 2 = Nat.card (Multiplicative (ZMod 2)) := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    _ ≤ Nat.card (TopologicalAbelianization G) := Nat.card_le_card_of_surjective _ hsurj

/-- **A finite Demushkin group has `q`-invariant `2`**: its abelianization is the torsion group
`ℤ/2`. -/
theorem demushkinQ_eq_two_of_finite [Finite G] : demushkinQ hG = 2 := by
  have htop : torsion (TopologicalAbelianization G) = ⊤ :=
    CommGroup.torsion_eq_top_iff.2 isMulTorsion_of_finite
  have hcard := hG.natCard_topologicalAbelianization_eq_two_of_finite
  have hne : ¬ IsMulTorsionFree (TopologicalAbelianization G) := fun h ↦ by
    rw [CommGroup.isMulTorsionFree_iff_torsion_eq_bot, htop] at h
    have hone : ∀ x : TopologicalAbelianization G, x = 1 := fun x ↦
      Subgroup.mem_bot.1 (h ▸ Subgroup.mem_top x)
    have : Subsingleton (TopologicalAbelianization G) := ⟨fun x y ↦ (hone x).trans (hone y).symm⟩
    rw [Nat.card_of_subsingleton 1] at hcard
    omega
  rw [demushkinQ_of_not_isMulTorsionFree hG hne, htop, Subgroup.card_top, hcard]

end IsDemushkin

/-- **`q(ℤ/2) = 2`**: the `q`-invariant of the finite Demushkin group `ℤ/2`. -/
@[simp]
theorem demushkinQ_multiplicative_zmod_two :
    demushkinQ (p := 2) (G := Multiplicative (ZMod 2)) isDemushkin_multiplicative_zmod_two = 2 :=
  isDemushkin_multiplicative_zmod_two.demushkinQ_eq_two_of_finite

end TauCeti
