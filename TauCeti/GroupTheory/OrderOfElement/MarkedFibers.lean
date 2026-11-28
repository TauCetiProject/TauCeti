/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.OrderOfElement.NegOne

/-!
# Weights on marked fibers

For a value `p`, the conjugate fiber of `w` is `{v | conj (w v) = p}`.
If `-1 ≠ 1` and the image of `g` has odd order,
`MonoidHom.map_pow_mul_ne_neg_one_of_odd_orderOf` excludes class `-1` from the
`g`-orbit of a class-`1` label. If every label in `B` has class `-1` and each marked
fiber and its conjugate fiber lie in such an orbit, `MonoidHom.notMem_of_induced_mem_marked`
shows that both fibers avoid `B`. Under the same hypotheses, if the partner `g` is a unit and
`w (g * v) = conj (w v)` for all labels `v`, `MonoidHom.sum_marked_weights_eq_sum_conjugate`
uses `Finset.sum_equiv` to equate the weighted sums over the two families of fibers.

The fiber statements follow `New.Data.IsMarked.notMem_bPlaces` and
`New.Data.IsMarked.sum_placesInducing_eq_sum_placesInducingConj` in
`grh/src/New/UpperBound/Divisibility/MarkedPrimes.lean` of
<https://github.com/lsernau/grh-lean> (commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0).
-/

public section

open Finset

namespace MonoidHom

variable {A M : Type*} [Monoid M] [HasDistribNeg M]

section Monoid

variable [Monoid A] (f : A →* M) {g : A}
  (hneg : (-1 : M) ≠ 1) (hg : Odd (orderOf (f g)))

include hneg hg

/-- Suppose `-1 ≠ 1`, the image of `g` has odd order, and every label in `B` has class `-1`.
If each marked value has a class-`1` representative whose `g`-orbit contains that fiber and
its conjugate fiber at that value, then a label with either `w σ` or `conj (w σ)` marked
lies outside `B`. -/
theorem notMem_of_induced_mem_marked
    {ι : Type*} {w : A → ι} {conj : ι → ι}
    {B : Finset A} {Λ : Finset ι} {σ : A}
    (hB : ∀ v ∈ B, f v = -1)
    (horbit : ∀ p ∈ Λ, ∃ τ, f τ = 1 ∧
      ∀ v, w v = p ∨ conj (w v) = p → ∃ i : ℕ, v = g ^ i * τ)
    (hσ : w σ ∈ Λ ∨ conj (w σ) ∈ Λ) : σ ∉ B := by
  intro hσB
  obtain ⟨p, hp, hσp⟩ : ∃ p ∈ Λ, w σ = p ∨ conj (w σ) = p := by
    rcases hσ with h | h
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩
  obtain ⟨τ, hτ, hτorbit⟩ := horbit p hp
  obtain ⟨i, hi⟩ := hτorbit σ hσp
  exact (f.map_pow_mul_ne_neg_one_of_odd_orderOf hneg hg hτ i) (hi ▸ hB σ hσB)

end Monoid

section Units

variable [Monoid A] (f : A →* M) {g : Aˣ}
  (hneg : (-1 : M) ≠ 1) (hg : Odd (orderOf (f (g : A))))

include hneg hg

/-- Assume the class and orbit hypotheses of `MonoidHom.notMem_of_induced_mem_marked` and
`w (g * v) = conj (w v)` for every label `v`, where the partner `g` is a unit. The sum of
the weighted value over marked fibers equals the sum of the weighted conjugate value over
the conjugate fibers at those same marked values. On both families of fibers, the
`B`-dependent weight is `lo`. -/
theorem sum_marked_weights_eq_sum_conjugate
    [Fintype A] [DecidableEq A] {ι α N : Type*} [DecidableEq ι] [AddCommMonoid N]
    {w : A → ι} {conj : ι → ι} {B : Finset A} {Λ : Finset ι}
    (hB : ∀ v ∈ B, f v = -1)
    (horbit : ∀ p ∈ Λ, ∃ τ, f τ = 1 ∧
      ∀ v, w v = p ∨ conj (w v) = p → ∃ i : ℕ, v = (g : A) ^ i * τ)
    (hpartner : ∀ v, w (g * v) = conj (w v)) (hi lo : α) (G : α → ι → N) :
    ∑ σ ∈ univ.filter (fun σ ↦ w σ ∈ Λ), G (if σ ∈ B then hi else lo) (w σ) =
      ∑ σ ∈ univ.filter (fun σ ↦ conj (w σ) ∈ Λ),
        G (if σ ∈ B then hi else lo) (conj (w σ)) := by
  symm
  refine sum_equiv g.mulLeft (fun σ ↦ ?_) (fun σ hσ ↦ ?_)
  · simp only [mem_filter, mem_univ, true_and, Units.mulLeft_apply, hpartner]
  · have hσc := (mem_filter.mp hσ).2
    have hlabel : w (g.mulLeft σ) = conj (w σ) := by
      simpa only [Units.mulLeft_apply] using hpartner σ
    have hσw : w (g.mulLeft σ) ∈ Λ := hlabel ▸ hσc
    have hout := f.notMem_of_induced_mem_marked hneg hg hB horbit (Or.inr hσc)
    have hpartnerOut := f.notMem_of_induced_mem_marked hneg hg hB horbit (Or.inl hσw)
    rw [ite_eq_right hout, ite_eq_right hpartnerOut, hlabel]

end Units

end MonoidHom
