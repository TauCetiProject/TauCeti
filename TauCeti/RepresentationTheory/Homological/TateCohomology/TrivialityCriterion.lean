/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Nilpotent
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.InflationRestriction
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Sylow
public import TauCeti.RepresentationTheory.Homological.TateCohomology.DimensionShift
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Periodic

/-!
# Tate's cohomological triviality criterion

Let `G` be a finite group and `A` a representation of `G`. If the cohomology of `A` vanishes in
two consecutive degrees on every subgroup of `G` of prime-power order, then it vanishes in every
degree on every subgroup of `G` (Milne, *Class Field Theory*, II 3.10). This file proves the
criterion for ordinary cohomology in positive degrees and for Tate cohomology in all integer
degrees. It is the step of Tate's theorem that makes the splitting module of a degree-two
cohomology class cohomologically trivial.

The proof has three steps.

* For a finite cyclic group, cohomology in positive degrees is two-periodic, so vanishing in two
  consecutive positive degrees gives vanishing in all of them
  (`isZero_succ_of_isCyclic_of_isZero`).
* For a subgroup `S` of prime-power order, argue by induction on `#S`. A nontrivial such `S` has a
  normal subgroup `T` of index `p` with `S ⧸ T` cyclic. By induction the cohomology of `T`
  vanishes in every positive degree, so inflation `Hⁿ⁺¹(S ⧸ T, A^T) ⟶ Hⁿ⁺¹(S, A)` is an
  isomorphism in every degree, and the cyclic case applies to `S ⧸ T`.
* For an arbitrary subgroup, restriction to Sylow subgroups detects vanishing
  (`TauCeti.groupCohomology.isZero_of_isZero_sylow`).

Tate cohomology is reduced to the ordinary case by dimension shifting: Tate cohomology of
`dimensionShiftDown A` in degree `n + 1` is Tate cohomology of `A` in degree `n`, on every
subgroup at once, so enough downward shifts move both the hypothesis and the conclusion into
positive degrees.

## Main statements

* `TauCeti.groupCohomology.isZero_succ_of_isCyclic_of_isZero`: for a finite cyclic group,
  vanishing of `H^{q+1}` and `H^{q+2}` implies vanishing of `Hⁿ⁺¹` for every `n`.
* `TauCeti.groupCohomology.isZero_of_forall_isPGroup`: the criterion for ordinary cohomology in
  positive degrees.
* `TauCeti.TateCohomology.isZero_of_forall_isPGroup`: the criterion for Tate cohomology in all
  integer degrees.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, Theorem 3.10.
* J.-P. Serre, *Local Fields*, Chapter IX, §5 (the criterion for a finite group, via its Sylow
  subgroups) and §8 (its use in the theorem of Tate and Nakayama).
* `ClassFieldTheory/Cohomology/TrivialityCriterion.lean` in `kbuzzard/ClassFieldTheory`, commit
  `ccc3323c6750abca25b49b35106f54eb3a398509`, proves the same criterion
  (`groupCohomology.trivialCohomology_of_even_of_odd` and
  `Rep.tateCohomology_of_trivialCohomology`) by the same three steps, for hypotheses on all
  injective group homomorphisms into `G`; it is reimplemented here for subgroups of prime-power
  order, on Tau Ceti's inflation-restriction, Sylow and dimension-shifting API.
-/

public section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- **Periodicity for a finite cyclic group.** If the cohomology of a finite cyclic group vanishes
in the two consecutive positive degrees `q + 1` and `q + 2`, it vanishes in every positive
degree. -/
theorem isZero_succ_of_isCyclic_of_isZero [Finite G] [IsCyclic G] (A : Rep k G) {q : ℕ}
    (h₁ : IsZero (groupCohomology A (q + 1))) (h₂ : IsZero (groupCohomology A (q + 2)))
    (n : ℕ) : IsZero (groupCohomology A (n + 1)) := by
  have := Fintype.ofFinite G
  -- Compare with Tate cohomology, which is two-periodic.
  have e (m : ℕ) : groupCohomology A (m + 1) ≅ tateCohomology A ((m + 1 : ℕ) : ℤ) :=
    ((_root_.TateCohomology.isoGroupCohomology (m + 1)).app A).symm
  refine (e n).isZero_iff.2 ?_
  rcases Nat.even_or_odd (n + q) with h | h
  · refine (Rep.FiniteCyclicGroup.periodicIso A _ _ ?_).isZero_iff.2 ((e q).isZero_iff.1 h₁)
    obtain ⟨r, hr⟩ := h
    simp only [Int.ModEq]
    omega
  · refine (Rep.FiniteCyclicGroup.periodicIso A _ _ ?_).isZero_iff.2
      ((e (q + 1)).isZero_iff.1 h₂)
    obtain ⟨r, hr⟩ := h
    simp only [Int.ModEq]
    omega

variable [Finite G] (A : Rep k G)

/-- The criterion for a subgroup of prime-power order, by induction on its order: a nontrivial
`p`-group `S` has a normal subgroup `T` of index `p`, whose cohomology vanishes by induction, so
inflation from the cyclic quotient `S ⧸ T` is an isomorphism in every positive degree. -/
private theorem isZero_succ_of_isPGroup (p : ℕ) [Fact p.Prime] {q : ℕ}
    (h₁ : ∀ S : Subgroup G, IsPGroup p S →
      IsZero (groupCohomology (res S.subtype A) (q + 1)))
    (h₂ : ∀ S : Subgroup G, IsPGroup p S →
      IsZero (groupCohomology (res S.subtype A) (q + 2)))
    (S : Subgroup G) (hS : IsPGroup p S) (n : ℕ) :
    IsZero (groupCohomology (res S.subtype A) (n + 1)) := by
  induction hN : Nat.card S using Nat.strong_induction_on generalizing S n with
  | _ N ih =>
  subst hN
  rcases IsPGroup.card_eq_or_dvd hS with hcard | hdvd
  · have : Subsingleton S := (Nat.card_eq_one_iff_unique.1 hcard).1
    exact isZero_groupCohomology_succ_of_subsingleton _ n
  have := IsPGroup.isNilpotent hS
  obtain ⟨T, hTindex, hT⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
  -- The image of `T` in `G` is a smaller subgroup of prime-power order.
  have hlt : Nat.card (T.map S.subtype) < Nat.card S := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, ← T.card_mul_index, hTindex]
    exact lt_mul_right Nat.card_pos (Fact.out : p.Prime).one_lt
  have hTp : IsPGroup p (T.map S.subtype) := IsPGroup.to_le hS (Subgroup.map_subtype_le T)
  have hTzero (m : ℕ) : IsZero (groupCohomology (res T.subtype (res S.subtype A)) (m + 1)) :=
    (ih _ hlt (T.map S.subtype) hTp m rfl).of_iso <|
      groupCohomology.mapIso (T.equivMapOfInjective S.subtype S.subtype_injective)
        (LinearEquiv.refl k _) (fun _ => rfl) (m + 1)
  -- Inflation from `S ⧸ T` is an isomorphism in every positive degree.
  have e (m : ℕ) := @asIso _ _ _ _ (infRes (res S.subtype A) T m).f
    (isIso_infRes_f (res S.subtype A) m fun i _ => hTzero i)
  have : IsCyclic (S ⧸ T) := isCyclic_of_prime_card (p := p) (by rw [← hTindex, Subgroup.index])
  exact (e n).isZero_iff.1 <| isZero_succ_of_isCyclic_of_isZero _
    ((e q).isZero_iff.2 (h₁ S hS)) ((e (q + 1)).isZero_iff.2 (h₂ S hS)) n

/-- **Tate's cohomological triviality criterion** for ordinary cohomology (Milne II 3.10). Let `G`
be a finite group and `A` a representation of `G`. If `H^{q+1}(S, A)` and `H^{q+2}(S, A)` vanish
for every subgroup `S` of `G` of prime-power order, then `Hⁿ⁺¹(S, A)` vanishes for every
subgroup `S` of `G` and every `n`. -/
theorem isZero_of_forall_isPGroup {q : ℕ}
    (h₁ : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      IsZero (groupCohomology (res S.subtype A) (q + 1)))
    (h₂ : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      IsZero (groupCohomology (res S.subtype A) (q + 2)))
    (S : Subgroup G) (n : ℕ) : IsZero (groupCohomology (res S.subtype A) (n + 1)) := by
  refine isZero_of_isZero_sylow (res S.subtype A) n fun p _ _ => ?_
  obtain ⟨P⟩ : Nonempty (Sylow p S) := inferInstance
  -- Restriction to `P ≤ S` is restriction to the image of `P` in `G`.
  refine ⟨P, (isZero_succ_of_isPGroup A p (h₁ p) (h₂ p) ((P : Subgroup S).map S.subtype)
    (P.isPGroup'.map S.subtype) n).of_iso ?_⟩
  exact groupCohomology.mapIso ((P : Subgroup S).equivMapOfInjective S.subtype
    S.subtype_injective) (LinearEquiv.refl k _) (fun _ => rfl) (n + 1)

end TauCeti.groupCohomology

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- The criterion after `d` downward dimension shifts: for degrees `q` and `n` with
`1 ≤ q + d` and `1 ≤ n + d`, shifting `A` down `d` times moves both into positive degrees. -/
private theorem isZero_of_forall_isPGroup_aux (d : ℕ) :
    ∀ (A : Rep k G) (q n : ℤ), 1 ≤ q + d → 1 ≤ n + d →
      (∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
        IsZero (tateCohomology (res S.subtype A) q)) →
      (∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
        IsZero (tateCohomology (res S.subtype A) (q + 1))) →
      ∀ (S : Subgroup G) [Fintype S], IsZero (tateCohomology (res S.subtype A) n) := by
  induction d with
  | zero =>
    intro A q n hq hn h₁ h₂ S _
    -- In positive degrees, Tate cohomology is ordinary cohomology.
    have e {H : Type u} [Group H] [Fintype H] (B : Rep k H) (m : ℕ) :
        tateCohomology B ((m + 1 : ℕ) : ℤ) ≅ groupCohomology B (m + 1) :=
      (_root_.TateCohomology.isoGroupCohomology (m + 1)).app B
    obtain ⟨r, rfl⟩ : ∃ r : ℕ, q = (r + 1 : ℕ) := ⟨(q - 1).toNat, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m + 1 : ℕ) := ⟨(n - 1).toNat, by omega⟩
    refine (e _ m).isZero_iff.2 <| groupCohomology.isZero_of_forall_isPGroup A
      (q := r) (fun p _ T hT => ?_) (fun p _ T hT => ?_) S m
    · have := Fintype.ofFinite T
      exact (e _ r).isZero_iff.1 (h₁ p T hT)
    · have := Fintype.ofFinite T
      exact (e _ (r + 1)).isZero_iff.1 (by simpa [add_assoc] using h₂ p T hT)
  | succ d ih =>
    intro A q n hq hn h₁ h₂ S _
    -- Shift down once: degree `n` of `A` is degree `n + 1` of `dimensionShiftDown A`.
    refine (isZero_res_dimensionShiftDown_iff A S n).1 <|
      ih (dimensionShiftDown A) (q + 1) (n + 1) (by omega) (by omega)
        (fun p _ T _ hT => (isZero_res_dimensionShiftDown_iff A T q).2 (h₁ p T hT))
        (fun p _ T _ hT => (isZero_res_dimensionShiftDown_iff A T (q + 1)).2 (h₂ p T hT)) S

/-- **Tate's cohomological triviality criterion** (Milne II 3.10). Let `G` be a finite group and
`A` a representation of `G`. If its Tate cohomology vanishes in degrees `q` and `q + 1` for every
subgroup `S` of `G` of prime-power order, then it vanishes in degree `n` for every subgroup `S`
of `G` and every integer `n`. -/
theorem isZero_of_forall_isPGroup (A : Rep k G) {q : ℤ}
    (h₁ : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      IsZero (tateCohomology (res S.subtype A) q))
    (h₂ : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      IsZero (tateCohomology (res S.subtype A) (q + 1)))
    (S : Subgroup G) [Fintype S] (n : ℤ) : IsZero (tateCohomology (res S.subtype A) n) :=
  isZero_of_forall_isPGroup_aux ((1 - q).toNat + (1 - n).toNat) A q n (by omega) (by omega)
    h₁ h₂ S

end TauCeti.TateCohomology
