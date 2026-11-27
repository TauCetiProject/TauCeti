/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import TauCeti.GroupTheory.OrderOfElement.NegOne
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Weights on marked fibers of a finite group

For a homomorphism `f` and a label `g` whose image has odd order,
`MonoidHom.map_pow_mul_ne_neg_one_of_odd_orderOf` excludes class `-1` from the orbit of a
label of class `1`, using `TauCeti.pow_ne_neg_one_of_odd_orderOf`.
`MonoidHom.notMem_of_induced_mem_marked` shows that marked fibers and their conjugate fibers
lie outside a set `B` of class-`-1` labels, so a `B`-dependent weight takes its value outside
`B`. `MonoidHom.sum_marked_weights_eq_sum_conjugate` gives equality of the weighted sums
when multiplication by the partner label induces conjugation.

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

/-- If `-1 ≠ 1` and the image of `g` under `f` has odd order, the orbit under powers of `g`
of a label of class `1` misses class `-1`. -/
theorem map_pow_mul_ne_neg_one_of_odd_orderOf {τ : A}
    (hτ : f τ = 1) (i : ℕ) : f (g ^ i * τ) ≠ -1 := by
  simpa only [map_mul, map_pow, hτ, mul_one] using
    TauCeti.pow_ne_neg_one_of_odd_orderOf hneg hg i

/-- Suppose `-1 ≠ 1`, the image of `g` has odd order, and every label in `B` has class `-1`.
If each marked value has a class-`1` representative whose `g`-orbit contains that fiber and
its conjugate fiber, then a label with either value marked lies outside `B`. -/
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

section Group

variable [Group A] (f : A →* M) {g : A}
  (hneg : (-1 : M) ≠ 1) (hg : Odd (orderOf (f g)))

include hneg hg

/-- Assume `w (g * v) = conj (w v)` for every label `v` and the class and orbit hypotheses of
`MonoidHom.notMem_of_induced_mem_marked`. The sum of the weighted value over marked fibers
equals the sum of the weighted conjugate value over conjugate fibers. On both families of fibers,
the `B`-dependent weight is `lo`. -/
theorem sum_marked_weights_eq_sum_conjugate
    [Fintype A] [DecidableEq A] {ι α N : Type*} [DecidableEq ι] [AddCommMonoid N]
    {w : A → ι} {conj : ι → ι} {B : Finset A} {Λ : Finset ι}
    (hB : ∀ v ∈ B, f v = -1)
    (horbit : ∀ p ∈ Λ, ∃ τ, f τ = 1 ∧
      ∀ v, w v = p ∨ conj (w v) = p → ∃ i : ℕ, v = g ^ i * τ)
    (hpartner : ∀ v, w (g * v) = conj (w v)) (hi lo : α) (G : α → ι → N) :
    ∑ σ ∈ univ.filter (fun σ ↦ w σ ∈ Λ), G (if σ ∈ B then hi else lo) (w σ) =
      ∑ σ ∈ univ.filter (fun σ ↦ conj (w σ) ∈ Λ),
        G (if σ ∈ B then hi else lo) (conj (w σ)) := by
  symm
  refine sum_equiv (Equiv.mulLeft g) (fun σ ↦ ?_) (fun σ hσ ↦ ?_)
  · simp only [mem_filter, mem_univ, true_and, Equiv.coe_mulLeft, hpartner]
  · have hσc := (mem_filter.mp hσ).2
    have hlabel : w (Equiv.mulLeft g σ) = conj (w σ) := by
      simpa only [Equiv.coe_mulLeft] using hpartner σ
    have hσw : w (Equiv.mulLeft g σ) ∈ Λ := hlabel ▸ hσc
    have hout := f.notMem_of_induced_mem_marked hneg hg hB horbit (Or.inr hσc)
    have hpartnerOut := f.notMem_of_induced_mem_marked hneg hg hB horbit (Or.inl hσw)
    rw [ite_eq_right hout, ite_eq_right hpartnerOut, hlabel]

end Group

end MonoidHom
