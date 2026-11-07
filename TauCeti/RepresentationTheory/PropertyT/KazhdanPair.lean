/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Unitary.HilbertSum
public import TauCeti.RepresentationTheory.PropertyT.Basic

/-!
# Kazhdan pairs for relative property (T)

A subgroup `Λ` of a discrete group `Γ` has relative property (T) exactly when it has a Kazhdan
pair: a finite set `F ⊆ Γ` and a `δ > 0` such that every unitary representation of `Γ` with a unit
vector moved by less than `δ` by each element of `F` has a nonzero `Λ`-invariant vector.

One direction is immediate. For the other, if no Kazhdan pair exists, choose for every finite `F`
and every `n` a unitary representation with an `(F, 1 / (n + 1))`-invariant unit vector and no
nonzero `Λ`-invariant vector. Their Hilbert direct sum has almost invariant vectors, given by the
chosen unit vectors placed in single coordinates, and still has no nonzero `Λ`-invariant vector,
since a vector of the sum is invariant exactly when each of its coordinates is.

The direct sum is indexed by a type in the universe of `Γ` and its summands live in the universe
of the representations, so the characterization is stated for representations in a universe
`max u v` containing both.

## Main statements

* `Subgroup.relativePropertyT_iff_exists_isKazhdanPair`: relative property (T) is equivalent to
  the existence of a Kazhdan pair.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Proposition 14.1.2.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Chapter 1.
-/

public section

universe u v

namespace Subgroup

open ContRepresentation

/-- **Kazhdan pairs.** A subgroup `Λ` of a discrete group `Γ` has relative property (T) exactly
when there are a finite set `F ⊆ Γ` and a `δ > 0` forming a Kazhdan pair for `Λ`. -/
theorem relativePropertyT_iff_exists_isKazhdanPair {Γ : Type v} [Group Γ] (Λ : Subgroup Γ) :
    Λ.RelativePropertyT.{max u v} ↔
      ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧ Λ.IsKazhdanPair.{max u v} F δ := by
  classical
  refine ⟨fun hΛ ↦ ?_, fun ⟨F, δ, hδ, h⟩ ↦ h.relativePropertyT hδ⟩
  by_contra hne
  -- For each finite set `F` and each `n`, choose a unitary representation with an
  -- `(F, 1 / (n + 1))`-invariant unit vector and no nonzero `Λ`-invariant vector.
  have key (i : Finset Γ × ℕ) : ¬ Λ.IsKazhdanPair.{max u v} i.1 (1 / (i.2 + 1)) :=
    fun hi ↦ hne ⟨i.1, _, Nat.one_div_pos_of_nat, hi⟩
  simp only [isKazhdanPair_iff, not_forall, not_not] at key
  choose H _ _ _ ρ hu hξ hinv using key
  -- Their Hilbert direct sum has almost invariant vectors, so it has a nonzero `Λ`-invariant
  -- vector, whose coordinates are `Λ`-invariant and hence all zero.
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp <|
    relativePropertyT_iff.mp hΛ (lp H 2) (hilbertSum ρ hu) (isUnitary_hilbertSum ρ hu) <|
      hasAlmostInvariantVectors_iff.mpr fun F ε hε ↦ by
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        obtain ⟨ξ, hξ1, hξF⟩ := hξ (F, n)
        refine ⟨lp.single 2 (F, n) ξ, by rw [lp.norm_single (by norm_num), hξ1], fun g hg ↦ ?_⟩
        rw [hilbertSum_apply_single, ← lp.single_sub, lp.norm_single (by norm_num)]
        exact (hξF g hg).trans hn
  rw [restrict_hilbertSum, mem_invariants_hilbertSum_iff] at hx
  exact hx0 (lp.ext (funext fun i ↦ by simpa [hinv i] using hx i))

end Subgroup
