/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PropertyT.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.HilbertSum

/-!
# Kazhdan pairs for relative property (T)

A pair `(F, δ)` of a finite set `F ⊆ Γ` and a real number `δ` is a *Kazhdan pair* for a subgroup
`Λ` of a discrete group `Γ` when every unitary representation of `Γ` with a unit vector moved by
less than `δ` by each element of `F` has a nonzero `Λ`-invariant vector. A Kazhdan pair with
`δ > 0` yields relative property (T), and conversely `Λ` has relative property (T) exactly when it
has a Kazhdan pair with `δ > 0`.

For the converse, if no Kazhdan pair exists, choose for every finite `F` and every `n` a unitary
representation with an `(F, 1 / (n + 1))`-invariant unit vector and no nonzero `Λ`-invariant
vector. Their Hilbert direct sum has almost invariant vectors, given by the chosen unit vectors
placed in single coordinates, and still has no nonzero `Λ`-invariant vector, since a vector of the
sum is invariant exactly when each of its coordinates is.

The direct sum is indexed by a type in the universe of `Γ` and its summands live in the universe
of the representations, so the characterization is stated for representations in a universe
`max u v` containing both.

## Main statements

* `Subgroup.IsKazhdanPair.relativePropertyT`: a Kazhdan pair gives relative property (T).
* `Subgroup.isKazhdanPair_top_univ_one`: for a finite group `Γ`, `(Γ, 1)` is a Kazhdan pair
  for `⊤`.
* `Subgroup.relativePropertyT_iff_exists_isKazhdanPair`: relative property (T) is equivalent to
  the existence of a Kazhdan pair.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Proposition 14.1.2.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Chapter 1.
-/

public section

namespace Subgroup

universe u v

open ContRepresentation

variable {Γ : Type v} [Group Γ]

/-- A pair `(F, δ)` of a finite set `F ⊆ Γ` and a real number `δ` is a Kazhdan pair for the
subgroup `Λ` when every unitary representation of `Γ` on a complex Hilbert space in universe `u`
with a unit vector moved by less than `δ` by each element of `F` has a nonzero vector fixed by
`Λ`. -/
def IsKazhdanPair (Λ : Subgroup Γ) (F : Finset Γ) (δ : ℝ) : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary →
      (∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ F, ‖ρ g ξ - ξ‖ < δ) →
        ∃ v : H, v ≠ 0 ∧ v ∈ (ρ.restrict Λ.subtype).invariants

/-- The unitary-representation criterion for Kazhdan pairs. -/
theorem isKazhdanPair_def (Λ : Subgroup Γ) (F : Finset Γ) (δ : ℝ) :
    Λ.IsKazhdanPair.{u} F δ ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary →
          (∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ F, ‖ρ g ξ - ξ‖ < δ) →
            ∃ v : H, v ≠ 0 ∧ v ∈ (ρ.restrict Λ.subtype).invariants :=
  Iff.rfl

/-- A Kazhdan pair `(F, δ)` with `δ > 0` for `Λ` gives relative property (T) of `Λ`. -/
theorem IsKazhdanPair.relativePropertyT {Λ : Subgroup Γ} {F : Finset Γ} {δ : ℝ}
    (hΛ : Λ.IsKazhdanPair.{u} F δ) (hδ : 0 < δ) : Λ.RelativePropertyT.{u} :=
  (relativePropertyT_def Λ).mpr fun H _ _ _ ρ hu hρ ↦
    hΛ H ρ hu ((hasAlmostInvariantVectors_def ρ).mp hρ F δ hδ)

/-- In a finite group `Γ`, the pair `(Γ, 1)` is a Kazhdan pair for `⊤`: averaging a unit vector
moved by less than `1` by every element gives an invariant vector within distance less than `1`
of it, which therefore cannot vanish. -/
theorem isKazhdanPair_top_univ_one [Fintype Γ] :
    (⊤ : Subgroup Γ).IsKazhdanPair.{u} Finset.univ 1 := by
  rintro H _ _ _ ρ - ⟨ξ, hξ, hF⟩
  obtain ⟨w, hw, hclose⟩ := ρ.exists_invariant_norm_sub_lt fun g ↦ hF g (Finset.mem_univ g)
  refine ⟨w, fun hw0 ↦ ?_, fun g ↦ hw g⟩
  simp [hw0, hξ] at hclose

/-- **Kazhdan pairs.** A subgroup `Λ` of a discrete group `Γ` has relative property (T) exactly
when there are a finite set `F ⊆ Γ` and a `δ > 0` forming a Kazhdan pair for `Λ`. -/
theorem relativePropertyT_iff_exists_isKazhdanPair (Λ : Subgroup Γ) :
    Λ.RelativePropertyT.{max u v} ↔
      ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧ Λ.IsKazhdanPair.{max u v} F δ := by
  classical
  refine ⟨fun hΛ ↦ ?_, fun ⟨F, δ, hδ, h⟩ ↦ h.relativePropertyT hδ⟩
  by_contra hne
  -- For each finite set `F` and each `n`, choose a unitary representation with an
  -- `(F, 1 / (n + 1))`-invariant unit vector and no nonzero `Λ`-invariant vector.
  have key (i : Finset Γ × ℕ) : ¬ Λ.IsKazhdanPair.{max u v} i.1 (1 / (i.2 + 1)) :=
    fun hi ↦ hne ⟨i.1, _, Nat.one_div_pos_of_nat, hi⟩
  simp only [isKazhdanPair_def, not_forall, not_exists, not_and] at key
  choose H _ _ _ ρ hu hξ hinv using key
  -- Their Hilbert direct sum has almost invariant vectors, so it has a nonzero `Λ`-invariant
  -- vector, whose coordinates are `Λ`-invariant and hence all zero.
  obtain ⟨x, hx0, hx⟩ :=
    (relativePropertyT_def Λ).mp hΛ (lp H 2) (hilbertSum ρ hu) (isUnitary_hilbertSum ρ hu) <|
      (hasAlmostInvariantVectors_def _).mpr fun F ε hε ↦ by
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        obtain ⟨ξ, hξ1, hξF⟩ := hξ (F, n)
        refine ⟨lp.single 2 (F, n) ξ, by rw [lp.norm_single (by norm_num), hξ1], fun g hg ↦ ?_⟩
        rw [hilbertSum_apply_single, ← lp.single_sub, lp.norm_single (by norm_num)]
        exact (hξF g hg).trans hn
  rw [restrict_hilbertSum, mem_invariants_hilbertSum_iff] at hx
  exact hx0 (lp.ext (funext fun i ↦ not_not.mp fun h ↦ hinv i (x i) h (hx i)))

end Subgroup
