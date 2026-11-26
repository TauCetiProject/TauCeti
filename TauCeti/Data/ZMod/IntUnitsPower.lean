/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# The sign group as a line over `ZMod 2`

Mathlib makes the two-element group `ℤˣ = {±1}`, written additively, a module over `ZMod 2`
(`Mathlib.Data.ZMod.IntUnitsPower`). This file records that it *is* the line `ZMod 2`: the map
sending `-1` to `1` is a `ZMod 2`-linear equivalence, so in particular the dimension is `1`. This
is what lets a family of `±1`-valued characters indexed by a finite set `ι` be read as a linear
map into a `ZMod 2`-space of dimension `#ι`, and lets such a family be compared with a family of
`ZMod 2`-valued sign patterns.

## Main results

* `TauCeti.hilbertSign`: the sign dictionary `ZMod 2 → ℤˣ`, sending `0` to `1` and `1` to `-1`.
* `TauCeti.coe_hilbertSign`, `TauCeti.hilbertSign_injective`,
  `TauCeti.eq_of_neg_one_pow_val_mul_eq`: integer-power expansion and injectivity / right-factor
  cancellation for the sign character `(-1) ^ x.val`.
* `TauCeti.additiveIntUnitsLinearEquiv`: the linear equivalence `Additive ℤˣ ≃ₗ[ZMod 2] ZMod 2`.
* `TauCeti.finrank_zmod_two_additive_intUnits`: `Module.finrank (ZMod 2) (Additive ℤˣ) = 1`.
* `TauCeti.uzpow_intCast_eq_negOnePow`: the sign `(-1) ^ (n mod 2)` of a parity is the sign
  `Int.negOnePow n` of any integer lift.
* `TauCeti.uzpow_mul_eq_of_forall_uzpow_eq`: any map between Koszul-signed degree semirings
  that preserves `u ^ ·` for a unit `u : ℤˣ` automatically preserves pairwise powers
  `u ^ (p * q)`.
* `TauCeti.negOnePow_mul_uzpow`: `Int.negOnePow p * (-1) ^ τ = (-1) ^ (p + τ)`.
* `TauCeti.uzpow_mul_intCast_add_one`: the sign `(-1) ^ (τ k)` changes by `(-1) ^ τ` from `k` to
  `k + 1`.
-/

public section

namespace TauCeti

/-- **The sign group is the line `ZMod 2`.** The additive form of `ℤˣ = {±1}` is isomorphic to
`ZMod 2`, by the map sending `1` to `0` and `-1` to `1`. This is the unique isomorphism between
the two groups, so no choice is involved. -/
def additiveIntUnitsAddEquiv : Additive ℤˣ ≃+ ZMod 2 where
  toFun u := if Additive.toMul u = 1 then 0 else 1
  invFun z := Additive.ofMul (if z = 0 then 1 else -1)
  left_inv u := by
    obtain ⟨v, rfl⟩ := Additive.ofMul.surjective u
    revert v; decide
  right_inv z := by revert z; decide
  map_add' u w := by revert u w; decide

@[simp] theorem additiveIntUnitsAddEquiv_apply (u : Additive ℤˣ) :
    additiveIntUnitsAddEquiv u = if Additive.toMul u = 1 then 0 else 1 :=
  (rfl)

/-- The sign `(-1)^n`, read additively in `ZMod 2`, is the parity of `n`. -/
theorem additiveIntUnitsAddEquiv_ofMul_neg_one_pow (n : ℕ) :
    additiveIntUnitsAddEquiv (Additive.ofMul ((-1 : ℤˣ) ^ n)) = n := by
  rw [ofMul_pow, map_nsmul]
  simp

/-- Translate an additive `ZMod 2` normalization, such as that of the cohomological local symbol,
to the classical sign normalization, sending `0` to `+1` and `1` to `-1`. -/
def hilbertSign (x : ZMod 2) : ℤˣ :=
  ((AddEquiv.toMultiplicativeRight additiveIntUnitsAddEquiv).symm
    (Multiplicative.ofAdd x))

/-- The zero class has positive sign. -/
@[simp]
theorem hilbertSign_zero : hilbertSign 0 = 1 := by
  apply (AddEquiv.toMultiplicativeRight additiveIntUnitsAddEquiv).injective
  simp [hilbertSign, additiveIntUnitsAddEquiv_apply]

/-- The nonzero class in `ZMod 2` has negative sign. -/
@[simp]
theorem hilbertSign_one : hilbertSign 1 = -1 := by
  apply (AddEquiv.toMultiplicativeRight additiveIntUnitsAddEquiv).injective
  simp [hilbertSign, additiveIntUnitsAddEquiv_apply]

/-- The sign is `+1` exactly at the zero class. -/
@[simp]
theorem hilbertSign_eq_one_iff (x : ZMod 2) : hilbertSign x = 1 ↔ x = 0 := by
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl <;> simp

/-- The sign `(-1) ^ i` of the parity `i` of an integer `n` is the sign `Int.negOnePow n`. -/
theorem uzpow_intCast_eq_negOnePow (n : ℤ) : (-1 : ℤˣ) ^ (n : ZMod 2) = n.negOnePow := by
  rw [uzpow_intCast, Int.negOnePow_def]

/-- Any function between Koszul-signed degree semirings that preserves `u ^ ·` for a unit
`u : ℤˣ` automatically preserves pairwise powers `u ^ (p * q)`. -/
theorem uzpow_mul_eq_of_forall_uzpow_eq {ι κ : Type*} [CommSemiring ι] [Module ι (Additive ℤˣ)]
    [CommSemiring κ] [Module κ (Additive ℤˣ)] {u : ℤˣ} {f : ι → κ}
    (hf : ∀ p : ι, u ^ f p = u ^ p) (p q : ι) :
    u ^ (f p * f q) = u ^ (p * q) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [uzpow_mul, uzpow_mul, hf p]
    rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ p) with h | h
    · rw [h, one_uzpow, one_uzpow]
    · rw [h, hf q]

/-- The sign `Int.negOnePow p * (-1) ^ τ` is the sign `(-1) ^ (p + τ)` of the sum of the parity
of `p` and `τ`. -/
theorem negOnePow_mul_uzpow (p : ℤ) (τ : ZMod 2) :
    p.negOnePow * (-1 : ℤˣ) ^ τ = (-1 : ℤˣ) ^ ((p : ZMod 2) + τ) := by
  rw [uzpow_add, uzpow_intCast_eq_negOnePow]

/-- The sign `(-1)^(τ k)` changes by `(-1)^τ` from degree `i` to degree `i + 1`. -/
theorem uzpow_mul_intCast_add_one (τ : ZMod 2) (i : ℤ) :
    (-1 : ℤˣ) ^ (τ * ((i + 1 : ℤ) : ZMod 2)) * (-1 : ℤˣ) ^ τ = (-1 : ℤˣ) ^ (τ * i) := by
  rw [← uzpow_add]
  congr 1
  have h2 : (2 : ZMod 2) = 0 := rfl
  push_cast
  linear_combination τ * h2

/-- The sign dictionary turns addition of mod-two invariants into multiplication of signs. -/
theorem hilbertSign_add (x y : ZMod 2) : hilbertSign (x + y) = hilbertSign x * hilbertSign y :=
  ((AddEquiv.toMultiplicativeRight additiveIntUnitsAddEquiv).symm.map_mul
    (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

/-- The sign dictionary turns a finite sum of mod-two invariants into the product of their
signs. -/
theorem hilbertSign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    hilbertSign (∑ i ∈ s, f i) = ∏ i ∈ s, hilbertSign (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.sum_cons, Finset.prod_cons, hilbertSign_add, ih]

/-- **Signs are determined by their vanishing.** A sign `u ∈ {±1}` is the sign of `x : ZMod 2`
exactly when `u = 1` holds precisely when `x = 0`. -/
theorem eq_hilbertSign_iff (u : ℤˣ) (x : ZMod 2) : u = hilbertSign x ↔ (u = 1 ↔ x = 0) := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl <;> simp

/-- Coerced to `ℤ`, `TauCeti.hilbertSign x` is `(-1 : ℤ) ^ x.val`. -/
theorem coe_hilbertSign (x : ZMod 2) : (hilbertSign x : ℤ) = (-1 : ℤ) ^ x.val := by
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl
  · simp
  · simp [hilbertSign_one, ZMod.val_one]

/-- The sign dictionary `TauCeti.hilbertSign` is injective. -/
theorem hilbertSign_injective : Function.Injective hilbertSign :=
  (AddEquiv.toMultiplicativeRight additiveIntUnitsAddEquiv).symm.injective.comp
    Multiplicative.ofAdd.injective

/-- In any ring without zero divisors where `2 ≠ 0`, `(-1 : R) ^ x.val` for `x : ZMod 2` is
injective after cancelling a nonzero right factor. -/
theorem eq_of_neg_one_pow_val_mul_eq {R : Type*} [Ring R] [NoZeroDivisors R] [NeZero (2 : R)]
    {x y : ZMod 2} {c : R} (hc : c ≠ 0)
    (h : (-1 : R) ^ x.val * c = (-1 : R) ^ y.val * c) : x = y := by
  have hsign : (-1 : R) ^ x.val = (-1 : R) ^ y.val := mul_right_cancel₀ hc h
  have hne : (1 : R) ≠ -1 := fun h1 ↦
    NeZero.ne (2 : R) (by rw [← one_add_one_eq_two]; exact eq_neg_iff_add_eq_zero.mp h1)
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) x with rfl | rfl <;>
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) y with rfl | rfl
  · rfl
  · exact absurd (by simpa [ZMod.val_zero, ZMod.val_one] using hsign) hne
  · exact absurd (by simpa [ZMod.val_zero, ZMod.val_one] using hsign.symm) hne
  · rfl

/-- **The sign group is the line `ZMod 2`, linearly.** `TauCeti.additiveIntUnitsAddEquiv` is
automatically `ZMod 2`-linear, every additive map between `ZMod 2`-modules being so. -/
def additiveIntUnitsLinearEquiv : Additive ℤˣ ≃ₗ[ZMod 2] ZMod 2 :=
  additiveIntUnitsAddEquiv.toLinearEquiv fun c u =>
    _root_.ZMod.map_smul (additiveIntUnitsAddEquiv : Additive ℤˣ →+ ZMod 2) c u

@[simp] theorem additiveIntUnitsLinearEquiv_apply (u : Additive ℤˣ) :
    additiveIntUnitsLinearEquiv u = if Additive.toMul u = 1 then 0 else 1 :=
  (rfl)

/-- The sign group `Additive ℤˣ` is one-dimensional over `ZMod 2`. -/
@[simp] theorem finrank_zmod_two_additive_intUnits :
    Module.finrank (ZMod 2) (Additive ℤˣ) = 1 := by
  rw [additiveIntUnitsLinearEquiv.finrank_eq, Module.finrank_self]

/-- The sum of the coordinates of a finite family of signs, as a `ZMod 2`-linear functional. -/
noncomputable def additiveIntUnitsCoordinateSum (ι : Type*) [Fintype ι] :
    (ι → Additive ℤˣ) →ₗ[ZMod 2] Additive ℤˣ := by
  classical
  exact ∑ i : ι, LinearMap.proj i

/-- The coordinate-sum functional is the sum of the coordinates. -/
theorem additiveIntUnitsCoordinateSum_apply (ι : Type*) [Fintype ι]
    (v : ι → Additive ℤˣ) :
    additiveIntUnitsCoordinateSum ι v = ∑ i : ι, v i := by
  classical
  simp [additiveIntUnitsCoordinateSum]

/-- The space of sign vectors of coordinate sum zero has dimension `#ι - 1`, with natural-number
subtraction. For nonempty `ι` this is a hyperplane, of dimension one less than the number of
coordinates; for empty `ι` the whole space is trivial and the dimension is `0`. -/
theorem finrank_ker_additiveIntUnitsCoordinateSum (ι : Type*) [Fintype ι] :
    Module.finrank (ZMod 2) (LinearMap.ker (additiveIntUnitsCoordinateSum ι)) =
      Fintype.card ι - 1 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- no coordinates: the ambient space is trivial
    rw [Module.finrank_zero_of_subsingleton]
    simp
  let i₀ : ι := Classical.choice hι
  have hpi : Module.finrank (ZMod 2) (ι → Additive ℤˣ) = Fintype.card ι := by
    rw [Module.finrank_pi_fintype, finrank_zmod_two_additive_intUnits]
    simp
  have hsurj : Function.Surjective (additiveIntUnitsCoordinateSum ι) := fun w =>
    ⟨Pi.single i₀ w, by rw [additiveIntUnitsCoordinateSum_apply]; simp⟩
  have hrange :
      Module.finrank (ZMod 2) (LinearMap.range (additiveIntUnitsCoordinateSum ι)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_zmod_two_additive_intUnits]
  have hrn := LinearMap.finrank_range_add_finrank_ker (additiveIntUnitsCoordinateSum ι)
  rw [hpi, hrange] at hrn
  omega

end TauCeti
