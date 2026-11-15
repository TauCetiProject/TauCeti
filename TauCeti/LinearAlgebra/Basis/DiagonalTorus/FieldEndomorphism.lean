/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic

/-!
# Field endomorphisms intertwined with characters of a split torus

When a group endomorphism normalizes a split torus and maps one additive root subgroup into
another, the pinning equation intertwines the induced additive map `f` on `K` with two characters
`ξ` and `η` of `𝔾ₘ^κ` via `f (ξ(s) * u) = η(s) * f u`. This file isolates the commutative-algebraic
consequences of that equation, independent of any ambient algebraic group:

1. **Multiplicativity from divisible units** (`TauCeti.ringHomOfAddMonoidHomTorusCharacter`,
   `TauCeti.ringEquivOfAddEquivTorusCharacter`): when `ξ ≠ 0` and `[RootableBy Kˣ ℕ]`, `ξ` is
   surjective onto `Kˣ`, so `f 1 = 1` upgrades `f` to a ring endomorphism with `g (ξ(s)) = η(s)`.
2. **Proportionality from kernel inclusion**
   (`TauCeti.exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp`): over an infinite field `K`,
   `ker ξ ≤ ker η` forces `d • η = m • ξ` with `0 < d`.
3. **Positivity and sign rigidity** (`TauCeti.not_forall_map_mul_map_eq_one`,
   `TauCeti.not_forall_map_pow_mul_pow_eq_one`,
   `TauCeti.exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_eq`): over an infinite field,
   `g (ξ(s)) = η(s)` forces `d • η = m • ξ` with `0 < d` and `0 < m`; when `[RootableBy Kˣ ℕ]` and
   `ξ ≠ 0`, `g` is uniquely determined by its values on `ξ(s)`
   (`TauCeti.ringHom_eq_of_torusCharacter_eq`).

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
-/

public section

namespace TauCeti

open Polynomial

section SignObstructions

variable {R : Type*} [CommRing R] [Infinite R]

/-- Any infinite commutative ring in which every `x ≠ 0` satisfies `g x ^ d * x ^ n = 1` for some
`n > 0` has no nonzero zero divisors, hence is an integral domain. -/
private theorem isDomain_of_forall_map_pow_mul_pow_eq_one (g : R →+* R) {d n : ℕ} (hn : 0 < n)
    (h : ∀ x : R, x ≠ 0 → g x ^ d * x ^ n = 1) : IsDomain R := by
  have : Nontrivial R := Infinite.instNontrivial R
  have : NoZeroDivisors R := ⟨fun {a b} hab => or_iff_not_imp_left.mpr fun ha => by
    have h1 : (g a ^ d * a ^ (n - 1)) * a = 1 := by
      rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]; exact h a ha
    rw [← one_mul b, ← h1, mul_assoc, hab, mul_zero]⟩
  exact NoZeroDivisors.to_isDomain R

/-- No positive power sends every nonzero element of an infinite commutative ring to `1`. -/
private theorem not_forall_pow_eq_one {d : ℕ} (hd : 0 < d) :
    ¬ ∀ x : R, x ≠ 0 → x ^ d = 1 := by
  intro h
  have : IsDomain R := isDomain_of_forall_map_pow_mul_pow_eq_one (RingHom.id R) (d := 0) hd
    fun x hx => by simp [h x hx]
  refine mul_ne_zero (M₀ := R[X]) X_ne_zero (fun h1 => ?_)
    (Polynomial.zero_of_eval_zero (X * (X ^ d - 1) : R[X]) fun c => ?_)
  · simpa [hd.ne'] using congrArg (eval (0 : R)) h1
  · by_cases hc : c = 0
    · simp [hc]
    · simp [h c hc]

/-- **No two ring endomorphisms of an infinite commutative ring are pointwisely inverse on nonzero
elements.** Expanding `g (c + 1) * g' (c + 1) = 1` forces every element of `R` to be a root of
`X * (X + 1) * (X ^ 2 + X + 1)`. -/
theorem not_forall_map_mul_map_eq_one (g g' : R →+* R) :
    ¬ ∀ x : R, x ≠ 0 → g x * g' x = 1 := by
  intro h
  have : Nontrivial R := Infinite.instNontrivial R
  have : NoZeroDivisors R := ⟨fun {a b} hab => by
    by_contra hne; rw [not_or] at hne
    have h1 : (g a * g' a) * (g b * g' b) = 1 := by rw [h a hne.1, h b hne.2, mul_one]
    have h0 : (g a * g' a) * (g b * g' b) = 0 := by
      rw [mul_mul_mul_comm, ← map_mul, hab, map_zero, zero_mul]
    exact one_ne_zero (h1.symm.trans h0)⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  have hginj : Function.Injective g := (injective_iff_map_eq_zero g).mpr fun x hx => by
    by_contra hx0; simpa [hx] using (h x hx0).symm
  let P : R[X] := X * (X + 1) * (X ^ 2 + X + 1)
  have hP0 : P ≠ 0 := mul_ne_zero
    (mul_ne_zero X_ne_zero fun h1 => by simpa using congrArg (eval 0) h1)
    (fun h2 => by simpa using congrArg (eval 0) h2)
  refine hP0 (Polynomial.zero_of_eval_zero P fun c => ?_)
  simp only [P, eval_mul, eval_add, eval_pow, eval_X, eval_one]
  by_cases hc0 : c = 0; · simp [hc0]
  by_cases hc1 : c + 1 = 0; · simp [hc1]
  have hmul1 : g c * g' c = 1 := h c hc0
  have hmul2 : (g c + 1) * (g' c + 1) = 1 := by simpa only [map_add, map_one] using h (c + 1) hc1
  have hquad : g (c ^ 2 + c + 1) = g 0 := by
    rw [map_add, map_add, map_pow, map_one, map_zero]
    calc g c ^ 2 + g c + 1
      _ = g c * ((g c + 1) * (g' c + 1) - g c * g' c) + (1 - g c * g' c) := by ring
      _ = 0 := by rw [hmul2, hmul1]; ring
  rw [hginj hquad, mul_zero]

/-- On an infinite commutative ring, `g x ^ d * x ^ n = 1` cannot hold for all `x ≠ 0` when both
exponents `d` and `n` are positive. -/
private theorem not_forall_map_pow_mul_pow_eq_one_of_pos (g : R →+* R) {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) : ¬ ∀ x : R, x ≠ 0 → g x ^ d * x ^ n = 1 := by
  intro h
  have : IsDomain R := isDomain_of_forall_map_pow_mul_pow_eq_one g hn h
  let P : R[X] := X * (X ^ d + 1) * ((X ^ n + 1) ^ d * (X ^ d + 1) ^ n - X ^ (n * d))
  have hP0 : P ≠ 0 := mul_ne_zero
    (mul_ne_zero X_ne_zero fun h1 => by simpa [hd.ne'] using congrArg (eval 0) h1)
    (fun h2 => by
      simpa [hn.ne', hd.ne', Nat.mul_ne_zero hn.ne' hd.ne'] using congrArg (eval 0) h2)
  refine hP0 (Polynomial.zero_of_eval_zero P fun c => ?_)
  simp only [P, eval_mul, eval_sub, eval_pow, eval_add, eval_X, eval_one]
  by_cases hc0 : c = 0; · simp [hc0]
  by_cases hcd1 : c ^ d + 1 = 0; · rw [hcd1, mul_zero, zero_mul]
  have hcd : g (c ^ d) * c ^ n = 1 := by rw [map_pow]; exact h c hc0
  have hcd_succ : (g (c ^ d) + 1) ^ d * (c ^ d + 1) ^ n = 1 := by
    simpa only [map_add, map_one] using h (c ^ d + 1) hcd1
  have hstep : c ^ n + 1 = (g (c ^ d) + 1) * c ^ n := by
    calc c ^ n + 1 = g (c ^ d) * c ^ n + c ^ n := by rw [hcd, add_comm]
      _ = (g (c ^ d) + 1) * c ^ n := by ring
  have hpoly : (c ^ n + 1) ^ d * (c ^ d + 1) ^ n - c ^ (n * d) = 0 := by
    calc (c ^ n + 1) ^ d * (c ^ d + 1) ^ n - c ^ (n * d)
      _ = ((g (c ^ d) + 1) ^ d * (c ^ d + 1) ^ n) * (c ^ n) ^ d - (c ^ n) ^ d := by
          rw [hstep, mul_pow, pow_mul]; ring
      _ = 0 := by rw [hcd_succ, one_mul, sub_self]
  rw [hpoly, mul_zero]

/-- **No ring endomorphism of an infinite commutative ring satisfies a nontrivial negative-exponent
power law on nonzero elements.** -/
theorem not_forall_map_pow_mul_pow_eq_one (g : R →+* R) {d n : ℕ} (hdn : d ≠ 0 ∨ n ≠ 0) :
    ¬ ∀ x : R, x ≠ 0 → g x ^ d * x ^ n = 1 := by
  intro h
  have : Nontrivial R := Infinite.instNontrivial R
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact not_forall_pow_eq_one (Nat.pos_of_ne_zero (hdn.resolve_left (not_not.mpr rfl)))
      fun x hx => by simpa using h x hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hginj : Function.Injective g := (injective_iff_map_eq_zero g).mpr fun x hx => by
      by_contra hx0; simpa [hx, zero_pow hd.ne'] using (h x hx0).symm
    exact not_forall_pow_eq_one hd fun x hx => hginj (by simpa [map_pow] using h x hx)
  exact not_forall_map_pow_mul_pow_eq_one_of_pos g hd hn h

end SignObstructions

section TorusCharacterProportionality

variable {κ : Type*} [Fintype κ] {K : Type*} [Field K] [Infinite K]

/-- **Kernel inclusion between split-torus characters over an infinite field forces rational
proportionality.** If every torus point killed by `ξ` is also killed by `η`, then `d • η = m • ξ`
for some integer `m` and positive natural number `d`. -/
theorem exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp {ξ η : κ → ℤ}
    (hker : ∀ s : κ → Kˣ, torusCharacter s ξ = 1 → torusCharacter s η = 1) :
    ∃ d : ℕ, 0 < d ∧ ∃ m : ℤ, d • η = m • ξ := by
  classical
  by_cases hξ : ξ = 0
  · subst hξ
    have hη : η = 0 := by
      by_contra hη0
      obtain ⟨s, hs⟩ := exists_torusCharacter_ne (K := K) hη0
      exact hs ((hker s (torusCharacter_zero s)).trans (torusCharacter_zero s).symm)
    exact ⟨1, Nat.one_pos, 0, by simp [hη]⟩
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hξ
  have hprop : ξ i₀ • η = η i₀ • ξ := by
    by_contra hne
    obtain ⟨i₁, hi₁⟩ := Function.ne_iff.mp hne
    let δ : ℤ := ξ i₀ * η i₁ - η i₀ * ξ i₁
    have hsingle : (Pi.single i₀ δ : κ → ℤ) ≠ 0 := fun h0 =>
      sub_ne_zero.mpr hi₁ (by simpa using congrFun h0 i₀)
    obtain ⟨t, ht⟩ := exists_torusCharacter_ne (K := K) hsingle
    simp only [torusCharacter_single, torusCharacter_zero] at ht
    let s : κ → Kˣ := Pi.mulSingle i₀ (t i₀ ^ (-ξ i₁)) * Pi.mulSingle i₁ (t i₀ ^ (ξ i₀))
    have hsξ : torusCharacter s ξ = 1 := by
      rw [torusCharacter_mul, torusCharacter_mulSingle, torusCharacter_mulSingle,
        ← zpow_mul, ← zpow_mul, ← zpow_add, show -ξ i₁ * ξ i₀ + ξ i₀ * ξ i₁ = 0 by ring, zpow_zero]
    have hsη : torusCharacter s η ≠ 1 := by
      rw [torusCharacter_mul, torusCharacter_mulSingle, torusCharacter_mulSingle,
        ← zpow_mul, ← zpow_mul, ← zpow_add, show -ξ i₁ * η i₀ + ξ i₀ * η i₁ = δ by dsimp [δ]; ring]
      exact ht
    exact hsη (hker s hsξ)
  rcases lt_or_gt_of_ne hi₀ with hneg | hpos
  · refine ⟨(-ξ i₀).toNat, Int.lt_toNat.mpr (neg_pos.mpr hneg), -η i₀, ?_⟩
    rw [← natCast_zsmul, Int.toNat_of_nonneg (neg_nonneg.mpr hneg.le), neg_smul, hprop, neg_smul]
  · refine ⟨(ξ i₀).toNat, Int.lt_toNat.mpr hpos, η i₀, ?_⟩
    rw [← natCast_zsmul, Int.toNat_of_nonneg hpos.le, hprop]

/-- **Intertwining a ring endomorphism with split-torus characters forces positive rational
proportionality.** Over an infinite field, if `g (ξ(s)) = η(s)` for every torus point `s`, then
`d • η = m • ξ` with `0 < d` and `0 < m`. -/
theorem exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_eq (g : K →+* K) {ξ η : κ → ℤ}
    (hmap : ∀ s : κ → Kˣ, g (torusCharacter s ξ : K) = (torusCharacter s η : K)) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧ d • η = m • ξ := by
  classical
  obtain ⟨d, hd, z, hz⟩ := exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp (ξ := ξ) (η := η)
    fun s hs => Units.ext (by simpa [hs] using (hmap s).symm)
  by_cases hξ : ξ = 0
  · exact ⟨d, 1, hd, Nat.one_pos, by rw [hz, hξ, smul_zero, smul_zero]⟩
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hξ
  let a : ℕ := (ξ i₀).natAbs
  have had : 0 < a * d := Nat.mul_pos (Int.natAbs_pos.mpr hi₀) hd
  have hpow (u : Kˣ) : g u ^ (a * d) = ((u ^ ((a : ℤ) * z) : Kˣ) : K) := by
    let s : κ → Kˣ := Pi.mulSingle i₀ (if 0 ≤ ξ i₀ then u else u⁻¹)
    have hsξ : torusCharacter s ξ = u ^ a := by
      rw [torusCharacter_mulSingle]
      split_ifs with h0
      · rw [← zpow_natCast, Int.natAbs_of_nonneg h0]
      · rw [show ξ i₀ = -(a : ℤ) by rw [Int.ofNat_natAbs_of_nonpos (le_of_not_ge h0), neg_neg],
          inv_zpow', neg_neg, zpow_natCast]
    calc g u ^ (a * d) = (g ((u ^ a : Kˣ) : K)) ^ d := by
          rw [Units.val_pow_eq_pow_val, map_pow, pow_mul]
      _ = ((torusCharacter s η ^ d : Kˣ) : K) := by rw [← hsξ, hmap s, Units.val_pow_eq_pow_val]
      _ = ((u ^ ((a : ℤ) * z) : Kˣ) : K) := by
          rw [← torusCharacter_nsmul, hz, torusCharacter_zsmul, hsξ, ← zpow_natCast, ← zpow_mul]
  rcases lt_trichotomy z 0 with hzneg | rfl | hzpos
  · refine (not_forall_map_pow_mul_pow_eq_one g (.inl had.ne') (n := a * (-z).toNat) fun x hx =>
      ?_).elim
    have hzn : (a : ℤ) * z = -((a * (-z).toNat : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Int.toNat_of_nonneg (neg_nonneg.mpr hzneg.le), mul_neg, neg_neg]
    have h1 := hpow (Units.mk0 x hx); rw [Units.val_mk0] at h1
    rw [h1, hzn, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_mk0, inv_mul_cancel₀ (pow_ne_zero _ hx)]
  · exact (not_forall_map_pow_mul_pow_eq_one g (.inl had.ne') (n := 0) fun x hx => by
      simpa using hpow (Units.mk0 x hx)).elim
  · exact ⟨d, z.toNat, hd, Int.lt_toNat.mpr hzpos, by
      rw [hz, ← natCast_zsmul, Int.toNat_of_nonneg hzpos.le]⟩

end TorusCharacterProportionality

section ConstructRingHom

variable {κ : Type*} [Fintype κ] {K : Type*} [Field K] [RootableBy Kˣ ℕ]

/-- **Upgrading an additive map intertwined with split-torus characters to a ring endomorphism.**
When `ξ ≠ 0` and `Kˣ` is divisible, `ξ` is surjective onto `Kˣ`, so `f (ξ(s) * u) = η(s) * f u`
together with `f 1 = 1` forces `f` to preserve multiplication. -/
def ringHomOfAddMonoidHomTorusCharacter (f : K →+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0) (hf1 : f 1 = 1)
    (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) : K →+* K where
  toFun := f
  map_zero' := f.map_zero
  map_add' := f.map_add
  map_one' := hf1
  map_mul' x y := by
    by_cases hx : x = 0; · simp [hx]
    obtain ⟨s, hs⟩ := torusCharacter_surjective hξ (Units.mk0 x hx)
    have hxval : (torusCharacter s ξ : K) = x := by simpa using congrArg Units.val hs
    have hfx : f x = (torusCharacter s η : K) := by
      simpa only [hxval, mul_one, hf1] using hscale s 1
    rw [← hxval, hscale s y, hxval, hfx]

@[simp]
theorem coe_ringHomOfAddMonoidHomTorusCharacter (f : K →+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0)
    (hf1 : f 1 = 1) (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) :
    ⇑(ringHomOfAddMonoidHomTorusCharacter f hξ hf1 hscale) = f := (rfl)

@[simp]
theorem ringHomOfAddMonoidHomTorusCharacter_apply (f : K →+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0)
    (hf1 : f 1 = 1) (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) (x : K) :
    ringHomOfAddMonoidHomTorusCharacter f hξ hf1 hscale x = f x := (rfl)

/-- On torus character values of `ξ`, the upgraded ring endomorphism evaluates to the values of
`η`. -/
theorem ringHomOfAddMonoidHomTorusCharacter_torusCharacter (f : K →+ K) {ξ η : κ → ℤ}
    (hξ : ξ ≠ 0) (hf1 : f 1 = 1) (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) (s : κ → Kˣ) :
    ringHomOfAddMonoidHomTorusCharacter f hξ hf1 hscale (torusCharacter s ξ : K) =
      (torusCharacter s η : K) := by
  simpa only [ringHomOfAddMonoidHomTorusCharacter_apply, mul_one, hf1] using hscale s 1

/-- **Upgrading an additive equivalence intertwined with split-torus characters to a ring
automorphism.** -/
def ringEquivOfAddEquivTorusCharacter (f : K ≃+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0) (hf1 : f 1 = 1)
    (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) : K ≃+* K :=
  { f, ringHomOfAddMonoidHomTorusCharacter f.toAddMonoidHom hξ hf1 hscale with }

@[simp]
theorem ringEquivOfAddEquivTorusCharacter_apply (f : K ≃+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0)
    (hf1 : f 1 = 1) (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) (x : K) :
    ringEquivOfAddEquivTorusCharacter f hξ hf1 hscale x = f x := (rfl)

@[simp]
theorem coe_ringEquivOfAddEquivTorusCharacter (f : K ≃+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0)
    (hf1 : f 1 = 1) (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) :
    (ringEquivOfAddEquivTorusCharacter f hξ hf1 hscale : K →+* K) =
      ringHomOfAddMonoidHomTorusCharacter f.toAddMonoidHom hξ hf1 hscale := (rfl)

/-- **A ring endomorphism of `K` is uniquely determined by its values on a nonzero split-torus
character**, provided `Kˣ` is divisible. -/
theorem ringHom_eq_of_torusCharacter_eq {g₁ g₂ : K →+* K} {ξ : κ → ℤ} (hξ : ξ ≠ 0)
    (h : ∀ s : κ → Kˣ, g₁ (torusCharacter s ξ : K) = g₂ (torusCharacter s ξ : K)) : g₁ = g₂ := by
  ext x
  by_cases hx : x = 0; · simp [hx]
  obtain ⟨s, hs⟩ := torusCharacter_surjective hξ (Units.mk0 x hx)
  rw [← show (torusCharacter s ξ : K) = x by simpa using congrArg Units.val hs, h s]

end ConstructRingHom

end TauCeti
