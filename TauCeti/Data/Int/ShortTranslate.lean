/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Data.Finset.Defs
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.Linarith
import TauCeti.Data.Int.AddMulPos

/-!
# Shortening a positive integer vector along a lattice

Let `L` be a subgroup of `ℤ^ι`, `ι` finite, and let `ℓ` be a vector of positive integers. Moving
`ℓ` by `c φ`, `φ ∈ L`, for a fixed step `c > 0`, one can keep every coordinate positive while
making the coordinates of a set `R` at most `B c`, for a bound `B` depending only on `L`, in such
a way that no nonzero element of `L` vanishes on `R`: every nonzero move along `L` changes some
coordinate in `R`.

This is the reduction step of Kharlampovich–Myasnikov's Lemma 27 (implicit function theorem over
free groups, §5.4.3): there `ℓ` records the lengths of the items of a periodic structure, `c` the
length of the period, and `L` the admissible twists; one item after another is made short by
taking a remainder, until the structure becomes rigid relative to the short items.

## Main results

* `Submodule.exists_rigid_short_translate`: the bound `B`, the move `φ` and the set `R`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.4.3, Lemma 27 and its proof.
-/

public section

namespace Submodule

variable {ι : Type*}

private lemma exists_bound_of_not_rigid [Finite ι] (L : Submodule ℤ (ι → ℤ)) :
    ∃ B : ℕ, ∀ R : Finset ι, ¬(∀ ψ ∈ L, (∀ i ∈ R, ψ i = 0) → ψ = 0) →
      ∃ ψ ∈ L, (∀ i ∈ R, ψ i = 0) ∧ (∃ j, ψ j < 0) ∧ ∀ i, -(B : ℤ) ≤ ψ i := by
  have hψ (R : Finset ι) : ∃ ψ ∈ L, (∀ i ∈ R, ψ i = 0) ∧
      (¬(∀ ψ ∈ L, (∀ i ∈ R, ψ i = 0) → ψ = 0) → ∃ j, ψ j < 0) := by
    by_cases hR : ∀ ψ ∈ L, (∀ i ∈ R, ψ i = 0) → ψ = 0
    · exact ⟨0, L.zero_mem, fun _ _ => rfl, fun h => (h hR).elim⟩
    push Not at hR
    obtain ⟨ψ, hψL, hψR, hψ0⟩ := hR
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hψ0
    rcases (hj : ψ j ≠ 0).lt_or_gt with hj | hj
    · exact ⟨ψ, hψL, hψR, fun _ => ⟨j, hj⟩⟩
    · exact ⟨-ψ, L.neg_mem hψL, by simpa using hψR, fun _ => ⟨j, by simpa using hj⟩⟩
  choose ψ hψL hψR hψneg using hψ
  have := Fintype.ofFinite ι
  obtain ⟨B, hB⟩ := Finite.exists_le fun p : Finset ι × ι => (ψ p.1 p.2).natAbs
  refine ⟨B, fun R hR => ⟨ψ R, hψL R, hψR R, hψneg R hR, fun i => ?_⟩⟩
  have : (ψ R i).natAbs ≤ B := hB (R, i)
  lia

private lemma exists_rigid_short_translate_of_bound [Finite ι] {L : Submodule ℤ (ι → ℤ)} {B : ℕ}
    {ℓ : ι → ℤ} {c : ℕ} (hc : 0 < c)
    (hB : ∀ R : Finset ι, ¬(∀ ψ ∈ L, (∀ i ∈ R, ψ i = 0) → ψ = 0) →
      ∃ ψ ∈ L, (∀ i ∈ R, ψ i = 0) ∧ (∃ j, ψ j < 0) ∧ ∀ i, -(B : ℤ) ≤ ψ i)
    (R : Finset ι) (φ : ι → ℤ) (hφ : φ ∈ L) (hpos : ∀ i, 0 < ℓ i + c * φ i)
    (hR : ∀ i ∈ R, ℓ i + c * φ i ≤ B * c) :
    ∃ φ ∈ L, ∃ R : Finset ι, (∀ i, 0 < ℓ i + c * φ i) ∧ (∀ i ∈ R, ℓ i + c * φ i ≤ B * c) ∧
      ∀ ψ ∈ L, (∀ i ∈ R, ψ i = 0) → ψ = 0 := by
  classical
  have := Fintype.ofFinite ι
  revert φ
  refine Finset.strongDownwardInductionOn (n := Fintype.card ι) R ?_ R.card_le_univ
  intro R ih _ φ hφ hpos hR
  by_cases hrig : ∀ ψ ∈ L, (∀ i ∈ R, ψ i = 0) → ψ = 0
  · exact ⟨φ, hφ, R, hpos, hR, hrig⟩
  -- Move along a witness `ψ` of non-rigidity as far as positivity allows: a coordinate `i₀`
  -- outside `R` becomes short, and the coordinates in `R` do not move.
  obtain ⟨ψ, hψL, hψR, ⟨j, hj⟩, hψB⟩ := hB R hrig
  obtain ⟨t, i₀, hi₀, htpos, hti₀⟩ := Int.exists_add_mul_pos_le (v := fun i => ℓ i + c * φ i)
    (w := fun i => c * ψ i) hpos (mul_neg_of_pos_of_neg (mod_cast hc) hj)
  have hi₀R : i₀ ∉ R := fun h => by simp [hψR i₀ h] at hi₀
  -- Recurse on the larger set `insert i₀ R`.
  refine ih (Finset.card_le_univ _) (Finset.ssubset_insert hi₀R) _
    (L.add_mem hφ (L.smul_mem t hψL)) (fun i => ?_) (fun i hi => ?_) <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · linarith [htpos i]
  · rcases Finset.mem_insert.mp hi with rfl | hi
    · nlinarith [hψB i]
    · simpa [hψR i hi] using hR i hi

/-- **Shortening along a lattice.** For a subgroup `L` of `ℤ^ι`, `ι` finite, there is `B` such
that for every vector `ℓ` of positive integers and every step `c > 0` some `φ ∈ L` and some set
`R` of coordinates satisfy: `ℓ + c φ` is positive, its coordinates in `R` are at most `B c`, and
no nonzero element of `L` vanishes on `R`. -/
theorem exists_rigid_short_translate [Finite ι] (L : Submodule ℤ (ι → ℤ)) :
    ∃ B : ℕ, ∀ ℓ : ι → ℤ, (∀ i, 0 < ℓ i) → ∀ c : ℕ, 0 < c →
      ∃ φ ∈ L, ∃ R : Finset ι, (∀ i, 0 < ℓ i + c * φ i) ∧ (∀ i ∈ R, ℓ i + c * φ i ≤ B * c) ∧
        ∀ ψ ∈ L, (∀ i ∈ R, ψ i = 0) → ψ = 0 := by
  obtain ⟨B, hB⟩ := exists_bound_of_not_rigid L
  exact ⟨B, fun ℓ hℓ c hc => exists_rigid_short_translate_of_bound hc hB ∅ 0 L.zero_mem
    (by simpa using hℓ) (by simp)⟩

/-- For `L = ℤ (1, -2, 1)`, the vector `ℓ = (100, 7, 100)` and the step `c = 3`, the move
`φ = -33 (1, -2, 1)` brings `ℓ` to `(1, 205, 1)`, and `L` is rigid on the first coordinate. -/
example : ∃ φ ∈ ℤ ∙ ![1, -2, 1], ∃ R : Finset (Fin 3), (∀ i, 0 < ![100, 7, 100] i + 3 * φ i) ∧
    (∀ i ∈ R, ![100, 7, 100] i + 3 * φ i ≤ 1 * 3) ∧
    ∀ ψ ∈ ℤ ∙ ![1, -2, 1], (∀ i ∈ R, ψ i = 0) → ψ = 0 := by
  refine ⟨-33 • ![1, -2, 1], Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), {0},
    by decide, by decide, fun ψ hψ hR => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hψ
  have ha : a = 0 := by simpa using hR 0 (by simp)
  simp [ha]

end Submodule
