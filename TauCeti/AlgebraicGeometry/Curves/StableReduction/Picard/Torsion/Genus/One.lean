/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Classification
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Division
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Contraction
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Torsion.Bound
import Mathlib.RingTheory.Int.Basic

/-!
# Prime torsion of genus-one numerical types

For every numerical type of arithmetic genus one and every prime `ℓ > 6`, the numerical
Picard group has at most one dimension of `ℓ`-torsion. For a minimal type, the bound is its
topological genus: in particular a tree has no such torsion.

The genus-one classification supplies common divisors of the multiplicities and weights,
with quotients at most six and four. Dividing these common factors changes neither the
weighted Picard group nor the intersection graph. The existing graph torsion bound then
applies. This is a uniform estimate: no coprimality with the original multiplicities or
weights is assumed. Nonminimal types reduce to minimal ones by contracting `(-1)`-indices.

## References

* The Stacks Project, Lemma 55.6.2, Tag 0C8T (genus-one numerical types).
* The Stacks Project, Lemma 55.2.6, Tag 0C6X (torsion and topological genus).
-/

public section

namespace TauCeti.NumericalType

universe u

variable {T : NumericalType.{u}}

/-- A prime greater than four divides no intersection at adjacent `(-2)`-indices
when all component weights are at most four. -/
private lemma not_dvd_intersection_of_small_weights (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : 4 < ℓ) (hw : ∀ i, (T.weight i : ℕ) ≤ 4)
    (hself : ∀ i, T.intersection i i = -(2 * (T.weight i : ℤ)))
    (i j : T.Component) (hij : T.Adj i j) : ¬ (ℓ : ℤ) ∣ T.intersection i j := by
  obtain ⟨a, ha⟩ := T.weight_dvd i j
  obtain ⟨b, hb⟩ := T.weight_dvd_intersection i j
  have hpos := (T.adj_iff.mp hij).2
  have ha0 : 0 < a := by
    have : (0 : ℤ) < T.weight i := Int.natCast_pos.mpr (T.weight i).pos
    nlinarith [hpos]
  have hb0 : 0 < b := by
    have : (0 : ℤ) < T.weight j := Int.natCast_pos.mpr (T.weight j).pos
    nlinarith [hpos]
  have hab := T.intersection_ratio_mul_le_four (hself i) (hself j) hpos ha hb
  have ha4 : a ≤ 4 := by nlinarith
  intro hdvd
  rw [ha] at hdvd
  rcases (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : ℓ.Prime))).dvd_mul.mp hdvd with
    hdvd | hdvd
  · have := Int.le_of_dvd (Int.natCast_pos.mpr (T.weight i).pos) hdvd
    have := hw i
    omega
  · have := Int.le_of_dvd ha0 hdvd
    omega

/-- For a minimal numerical type of arithmetic genus one, prime torsion above six
is bounded by the first Betti number of the intersection graph. -/
theorem IsMinimal.finrank_torsion_le_topologicalGenus_of_genus_eq_one
    (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : 6 < ℓ) :
    (Module.finrank (ZMod ℓ) (T.torsion ℓ) : ℤ) ≤ T.topologicalGenus := by
  by_cases hcard : Fintype.card T.Component = 1
  · rw [T.finrank_torsion_eq_zero_of_card_eq_one hcard]
    exact T.topologicalGenus_nonneg
  have hcard' : 1 < Fintype.card T.Component := by
    have := Fintype.card_pos (α := T.Component)
    omega
  have hself := fun i ↦ ((T.isMinusTwoIndex_iff).mp
    (((T.isMinimal_and_arithmeticGenus_eq_one_iff hcard').mp ⟨hT, hg⟩) i)).2
  obtain ⟨im, hm⟩ := hT.exists_multiplicity_dvd_and_le_six_mul hg
  obtain ⟨iw, hw⟩ := hT.exists_weight_dvd_and_le_four_mul hg
  let U := T.divide (T.multiplicity im) (T.weight iw) (fun i ↦ (hm i).1) (fun i ↦ (hw i).1)
  have hmult (i : T.Component) : (U.multiplicity i : ℕ) ≤ 6 := by
    dsimp [U]
    exact (Nat.div_le_iff_le_mul_add_pred (T.multiplicity im).pos).mpr (by
      have := (hm i).2
      omega)
  have hweight (i : T.Component) : (U.weight i : ℕ) ≤ 4 := by
    dsimp [U]
    exact (Nat.div_le_iff_le_mul_add_pred (T.weight iw).pos).mpr (by
      have := (hw i).2
      omega)
  have hselfU (i : T.Component) : U.intersection i i = -(2 * (U.weight i : ℤ)) := by
    apply mul_left_cancel₀ (a := (T.weight iw : ℤ)) (Int.natCast_pos.mpr (T.weight iw).pos).ne'
    have h₁ := T.mul_divide_intersection (T.multiplicity im) (T.weight iw)
      (fun i ↦ (hm i).1) (fun i ↦ (hw i).1) i i
    have h₂ := T.mul_divide_weight (T.multiplicity im) (T.weight iw)
      (fun i ↦ (hm i).1) (fun i ↦ (hw i).1) i
    nlinarith [hself i, h₁, h₂]
  have hbound := U.finrank_torsion_le_topologicalGenus ℓ (fun i hdvd ↦ by
    have := Nat.le_of_dvd (U.multiplicity i).pos hdvd
    have := hmult i
    omega) (not_dvd_intersection_of_small_weights ℓ (by omega) hweight hselfU)
  rw [T.topologicalGenus_divide] at hbound
  rwa [T.finrank_torsion_divide (T.multiplicity im) (T.weight iw)
    (fun i ↦ (hm i).1) (fun i ↦ (hw i).1) ℓ] at hbound

/-- Every genus-one numerical type has at most one dimension of prime torsion above six.
No minimality or coprimality hypothesis on the multiplicities or weights is needed. -/
theorem finrank_torsion_le_one_of_genus_eq_one (hg : T.arithmeticGenus = 1)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 6 < ℓ) :
    Module.finrank (ZMod ℓ) (T.torsion ℓ) ≤ 1 := by
  suffices h : ∀ n, ∀ T : NumericalType.{u}, Fintype.card T.Component = n →
      T.arithmeticGenus = 1 → Module.finrank (ZMod ℓ) (T.torsion ℓ) ≤ 1 from
    h _ T rfl hg
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T hn hg
    by_cases hT : T.IsMinimal
    · by_cases hcard : Fintype.card T.Component = 1
      · rw [T.finrank_torsion_eq_zero_of_card_eq_one hcard]
        omega
      have hcard' : 1 < Fintype.card T.Component := by
        have := Fintype.card_pos (α := T.Component)
        omega
      have hself := (T.isMinimal_and_arithmeticGenus_eq_one_iff hcard').mp ⟨hT, hg⟩
      have htop := T.topologicalGenus_le_one (fun i ↦
        ((T.isMinusTwoIndex_iff.mp (hself i)).2).ge)
      have hbound := hT.finrank_torsion_le_topologicalGenus_of_genus_eq_one hg ℓ hℓ
      omega
    · obtain ⟨e, he⟩ : ∃ e, T.IsMinusOneIndex e := by
        simpa [isMinimal_iff] using hT
      have hcard : Fintype.card (T.contract he).Component < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (p := (· ≠ e)) (x := e) (by simp)
      exact (T.finrank_torsion_le_contract he ℓ).trans
        (ih _ hcard (T.contract he) rfl ((arithmeticGenus_contract he).trans hg))

end TauCeti.NumericalType
