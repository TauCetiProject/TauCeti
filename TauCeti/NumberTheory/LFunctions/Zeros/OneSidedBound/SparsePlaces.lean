/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters

/-!
# Sparse cyclotomic places

In cyclotomic unit coordinates a set of places is sparse if, starting at one of its places,
at most one short positive exponent of a given small prime, with either sign, reaches a place
of the set after reduction modulo the part of the level coprime to that prime. The places need
not be distinct. Short, negative-sign transitions at the full level have a unique start and
exponent at any given endpoint and cannot be composed in the short range. At the ramified
prime there are no such transitions between places in the class of `-1` modulo the base level.

The sparsity condition and its application to near pairs follow `New.Parameters.IsSparse`
and `New.Data.IsNearPair` in `New/Reduction/Data/AdmissibleData.lean` and
`New/Derivatives/Sharpness/NearPairs.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit `72fead1`.
-/

public section

namespace TauCeti.OneSidedBound.Parameters

/-- Sparsity for primes at most `L`: from any place in `S`, at most one exponent in
`(0, l₀ s)` reaches another member of `S` by multiplication by a signed prime power, read
modulo the prime-to-`p` part of the cyclotomic level. The starting place itself is allowed
as an endpoint. -/
def IsSparse (P : Parameters) (s L : ℕ) (S : Set (ZMod (P.q₁ s))ˣ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ L → ∀ σ ∈ S,
    let r := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) p) (ZMod (ordCompl[p] (P.q₁ s)))
    {i : ℕ | 0 < i ∧ i < l₀ s ∧ ∃ τ ∈ S,
      r τ = (p : ZMod (ordCompl[p] (P.q₁ s))) ^ i * r σ ∨
      r τ = -((p : ZMod (ordCompl[p] (P.q₁ s))) ^ i * r σ)}.Subsingleton

/-- Characterize sparsity by uniqueness of the exponent of a signed hit in the reduced level. -/
theorem isSparse_iff {P : Parameters} {s L : ℕ} {S : Set (ZMod (P.q₁ s))ˣ} :
    P.IsSparse s L S ↔ ∀ p : ℕ, p.Prime → p ≤ L → ∀ σ ∈ S,
      let r := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) p) (ZMod (ordCompl[p] (P.q₁ s)))
      {i : ℕ | 0 < i ∧ i < l₀ s ∧ ∃ τ ∈ S,
        r τ = (p : ZMod (ordCompl[p] (P.q₁ s))) ^ i * r σ ∨
        r τ = -((p : ZMod (ordCompl[p] (P.q₁ s))) ^ i * r σ)}.Subsingleton := (Iff.rfl)

/-- In a sparse set, two short signed powers of the same prime taking one place to places of
that set at the full cyclotomic level must have the same exponent. -/
theorem IsSparse.eq_of_signed_pow_mul {P : Parameters} {s L : ℕ} {S : Set (ZMod (P.q₁ s))ˣ}
    (hS : P.IsSparse s L S) {p i j : ℕ} (hp : p.Prime) (hpL : p ≤ L)
    {σ τ ρ : (ZMod (P.q₁ s))ˣ} (hσ : σ ∈ S) (hτ : τ ∈ S) (hρ : ρ ∈ S)
    (hi : 0 < i) (hi' : i < l₀ s) (hj : 0 < j) (hj' : j < l₀ s)
    (hτi : (τ : ZMod (P.q₁ s)) = (p : ZMod (P.q₁ s)) ^ i * σ ∨
      (τ : ZMod (P.q₁ s)) = -((p : ZMod (P.q₁ s)) ^ i * σ))
    (hρj : (ρ : ZMod (P.q₁ s)) = (p : ZMod (P.q₁ s)) ^ j * σ ∨
      (ρ : ZMod (P.q₁ s)) = -((p : ZMod (P.q₁ s)) ^ j * σ)) : i = j := by
  let r := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) p) (ZMod (ordCompl[p] (P.q₁ s)))
  have reduce {x : ZMod (P.q₁ s)} {k : ℕ}
      (hx : x = (p : ZMod (P.q₁ s)) ^ k * σ ∨ x = -((p : ZMod (P.q₁ s)) ^ k * σ)) :
      r x = (p : ZMod (ordCompl[p] (P.q₁ s))) ^ k * r σ ∨
      r x = -((p : ZMod (ordCompl[p] (P.q₁ s))) ^ k * r σ) :=
    hx.imp (fun h ↦ by simpa only [map_mul, map_pow, map_natCast] using congrArg r h)
      (fun h ↦ by simpa only [map_neg, map_mul, map_pow, map_natCast] using congrArg r h)
  exact (isSparse_iff.mp hS p hp hpL σ hσ)
    ⟨hi, hi', τ, hτ, reduce hτi⟩ ⟨hj, hj', ρ, hρ, reduce hρj⟩

/-- A short negative prime-power transition in a sparse set cannot be followed by another
such transition if the sum of the exponents is still short. -/
theorem IsSparse.not_neg_pow_mul_eq_of_neg_pow_mul_eq {P : Parameters} {s L : ℕ}
    {S : Set (ZMod (P.q₁ s))ˣ} (hS : P.IsSparse s L S) {p i j : ℕ}
    (hp : p.Prime) (hpL : p ≤ L) {σ τ ρ : (ZMod (P.q₁ s))ˣ}
    (hσ : σ ∈ S) (hτ : τ ∈ S) (hρ : ρ ∈ S)
    (hi : 0 < i) (hj : 0 < j) (hij : i + j < l₀ s)
    (hτi : (τ : ZMod (P.q₁ s)) = -((p : ZMod (P.q₁ s)) ^ i * σ)) :
    (ρ : ZMod (P.q₁ s)) ≠ -((p : ZMod (P.q₁ s)) ^ j * τ) := by
  intro hρj
  have hρij : (ρ : ZMod (P.q₁ s)) = (p : ZMod (P.q₁ s)) ^ (i + j) * σ := by
    rw [hρj, hτi, mul_neg, neg_neg, pow_add]
    ac_rfl
  have := hS.eq_of_signed_pow_mul hp hpL hσ hτ hρ hi (by omega) (by omega) hij
    (.inr hτi) (.inl hρij)
  omega

/-- A negative prime-power transition into a given place of a sparse set has a unique
starting place and exponent in the short range. -/
theorem IsSparse.eq_of_neg_pow_mul_eq {P : Parameters} {s L : ℕ}
    {S : Set (ZMod (P.q₁ s))ˣ} (hS : P.IsSparse s L S) {p i j : ℕ}
    (hp : p.Prime) (hpL : p ≤ L) {σ τ ρ : (ZMod (P.q₁ s))ˣ}
    (hσ : σ ∈ S) (hτ : τ ∈ S) (hρ : ρ ∈ S)
    (hi : 0 < i) (hi' : i < l₀ s) (hj : 0 < j) (hj' : j < l₀ s)
    (hσi : (ρ : ZMod (P.q₁ s)) = -((p : ZMod (P.q₁ s)) ^ i * σ))
    (hτj : (ρ : ZMod (P.q₁ s)) = -((p : ZMod (P.q₁ s)) ^ j * τ)) :
    (σ, i) = (τ, j) := by
  have hu : IsUnit (p : ZMod (P.q₁ s)) := by
    apply (isUnit_pow_iff hi.ne').mp
    apply isUnit_of_mul_isUnit_left (y := (σ : ZMod (P.q₁ s)))
    simpa only [hσi, neg_neg] using ρ.isUnit.neg
  have aux {a b c : (ZMod (P.q₁ s))ˣ} {k l : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
      (hk : 0 < k) (hkl : k < l) (hl : l < l₀ s)
      (hak : (c : ZMod (P.q₁ s)) = -((p : ZMod (P.q₁ s)) ^ k * a))
      (hbl : (c : ZMod (P.q₁ s)) = -((p : ZMod (P.q₁ s)) ^ l * b)) : False := by
    have h : (a : ZMod (P.q₁ s)) = (p : ZMod (P.q₁ s)) ^ (l - k) * b := by
      apply (hu.pow k).mul_left_cancel
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hkl.le]
      exact neg_injective (hak.symm.trans hbl)
    have := hS.eq_of_signed_pow_mul hp hpL hb ha hc (by omega) (by omega) (by omega) hl
      (.inl h) (.inr hbl)
    omega
  have hij : i = j := le_antisymm
    (le_of_not_gt fun h ↦ aux hτ hσ hρ hj h hi' hτj hσi)
    (le_of_not_gt fun h ↦ aux hσ hτ hρ hi h hj' hσi hτj)
  subst j
  have heq := (hu.pow i).mul_left_cancel (neg_injective (hσi.symm.trans hτj))
  exact congrArg (·, i) (Units.ext heq)

/-- Multiplication by minus a power of the ramified prime cannot carry a place of class `-1`
modulo `q₀` to another place of that class. -/
theorem neg_ramified_pow_mul_ne_of_cast_eq_neg_one (P : Parameters) {s i : ℕ}
    {σ τ : (ZMod (P.q₁ s))ˣ}
    (hσ : ZMod.castHom (P.q₀_dvd_q₁ s) (ZMod P.q₀) σ = -1)
    (hτ : ZMod.castHom (P.q₀_dvd_q₁ s) (ZMod P.q₀) τ = -1) :
    (τ : ZMod (P.q₁ s)) ≠ -((P.d : ZMod (P.q₁ s)) ^ i * σ) := by
  intro h
  apply P.d_pow_ne_neg_one i
  have hr := congrArg (ZMod.castHom (P.q₀_dvd_q₁ s) (ZMod P.q₀)) h
  simpa only [map_neg, map_mul, map_pow, map_natCast, hσ, hτ, mul_neg_one, neg_neg] using hr.symm

end TauCeti.OneSidedBound.Parameters
