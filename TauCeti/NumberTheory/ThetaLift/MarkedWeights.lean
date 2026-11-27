/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.GroupTheory.OrderOfElement

/-!
# Weights on marked prime fibers in a cyclotomic tower

`unitsMap_pow_mul_ne_neg_one` excludes the class `-1` from the orbit of a place of
class `1` under a label of odd order modulo the base. Consequently the fibers of a
marked prime and of its conjugate carry only the shorter weight.
`sum_marked_weights_eq_sum_conjugate` reindexes weighted sums on these fibers by
multiplication by the partner label.

The argument follows `New.Data.IsMarked.notMem_bPlaces` and
`New.Data.IsMarked.sum_placesInducing_eq_sum_placesInducingConj` in
`grh/src/New/UpperBound/Divisibility/MarkedPrimes.lean` of
<https://github.com/lsernau/grh-lean> (commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0). The proof uses the order-of-element identity and `Finset.sum_equiv`.
-/

public section

open Finset

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters) {s : ℕ} {g : (ZMod (P.q₁ s))ˣ}
  (hg : Odd (orderOf (ZMod.unitsMap (P.q₀_dvd_q₁ s) g)))

include hg

/-- The orbit under multiplication by powers of `g` of a label of class `1` misses
the class `-1` if the reduction of `g` has odd order. -/
theorem unitsMap_pow_mul_ne_neg_one {τ : (ZMod (P.q₁ s))ˣ}
    (hτ : ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = 1) (i : ℕ) :
    ZMod.unitsMap (P.q₀_dvd_q₁ s) (g ^ i * τ) ≠ -1 := by
  let a := ZMod.unitsMap (P.q₀_dvd_q₁ s) g
  have : Fact (2 < P.q₀) := ⟨(by decide : 2 < 18480).trans_le P.le_q₀⟩
  simp only [map_mul, map_pow, hτ, mul_one]
  intro he
  have hp : (a ^ i) ^ orderOf a = 1 := by
    rw [pow_right_comm, pow_orderOf_eq_one, one_pow]
  rw [he] at hp
  have ha : Odd (orderOf a) := hg
  have h := congrArg (fun u : (ZMod P.q₀)ˣ ↦ (u : ZMod P.q₀)) hp
  simp only [Units.val_neg, Units.val_one, ha.neg_one_pow] at h
  exact ZMod.neg_one_ne_one h

/-- If the induced prime of a label or its conjugate is marked, that label misses
the high-weight set `B`. Each marked prime has a representative of class `1`, and the
fibers of that prime and its conjugate lie in the orbit of this representative. -/
theorem notMem_of_induced_mem_marked
    {ι : Type*} {w : (ZMod (P.q₁ s))ˣ → ι} {conj : ι → ι}
    {B : Finset (ZMod (P.q₁ s))ˣ} {Λ : Finset ι} {σ : (ZMod (P.q₁ s))ˣ}
    (hB : ∀ v ∈ B, ZMod.unitsMap (P.q₀_dvd_q₁ s) v = -1)
    (horbit : ∀ p ∈ Λ, ∃ τ, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = 1 ∧
      ∀ v, w v = p ∨ conj (w v) = p → ∃ i : ℕ, v = g ^ i * τ)
    (hσ : w σ ∈ Λ ∨ conj (w σ) ∈ Λ) : σ ∉ B := by
  intro hσB
  obtain ⟨p, hp, hσp⟩ : ∃ p ∈ Λ, w σ = p ∨ conj (w σ) = p := by
    rcases hσ with h | h
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩
  obtain ⟨τ, hτ, hτorbit⟩ := horbit p hp
  obtain ⟨i, hi⟩ := hτorbit σ hσp
  exact (P.unitsMap_pow_mul_ne_neg_one hg hτ i) (hi ▸ hB σ hσB)

/-- Summing the weight and induced prime over marked fibers gives the same result as
summing the weight and conjugate prime over conjugate fibers. The partner translation
exchanges the indexing fibers, where the two-valued weight is always the shorter one. -/
theorem sum_marked_weights_eq_sum_conjugate
    {ι α M : Type*} [DecidableEq ι] [AddCommMonoid M]
    {w : (ZMod (P.q₁ s))ˣ → ι} {conj : ι → ι}
    {B : Finset (ZMod (P.q₁ s))ˣ} {Λ : Finset ι}
    (hB : ∀ v ∈ B, ZMod.unitsMap (P.q₀_dvd_q₁ s) v = -1)
    (horbit : ∀ p ∈ Λ, ∃ τ, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = 1 ∧
      ∀ v, w v = p ∨ conj (w v) = p → ∃ i : ℕ, v = g ^ i * τ)
    (hpartner : ∀ v, w (g * v) = conj (w v)) (hi lo : α) (G : α → ι → M) :
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
    have hout := P.notMem_of_induced_mem_marked hg hB horbit (Or.inr hσc)
    have hpartnerOut := P.notMem_of_induced_mem_marked hg hB horbit (Or.inl hσw)
    rw [ite_eq_right hout, ite_eq_right hpartnerOut, hlabel]

end TauCeti.OneSidedBound.Parameters
