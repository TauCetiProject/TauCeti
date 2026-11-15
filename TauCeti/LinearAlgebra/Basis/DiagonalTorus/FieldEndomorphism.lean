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
another, the pinning equation intertwines the induced additive map on the field `K` with two
characters `ξ` and `η` of `𝔾ₘ^κ`:

```text
f (ξ(s) * u) = η(s) * f(u).
```

This file isolates the commutative-algebraic consequences of that functional equation, independent
of any ambient algebraic group:

1. **Multiplicativity from divisible units.** When `ξ ≠ 0` and `[RootableBy Kˣ ℕ]` holds (for
   instance when `K` is algebraically closed), `ξ` is surjective onto `Kˣ`. Normalizing by
   `f 1 = 1` turns `f` into a ring endomorphism `g : K →+* K` determined on `Kˣ` by
   `g (ξ(s)) = η(s)` (`TauCeti.ringHomOfAddMonoidHomTorusCharacter`).
2. **Proportionality from kernel inclusion.** Over an infinite field `K`, if every torus point in
   the kernel of `ξ` also lies in the kernel of `η`, then a positive integer multiple of `η` is an
   integer multiple of `ξ` (`TauCeti.exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp`).
3. **Positivity and sign rigidity.** On an infinite commutative ring `R`, two ring endomorphisms `g`
   and `g'` cannot satisfy `g x * g' x = 1` for all `x ≠ 0`
   (`TauCeti.not_forall_map_mul_map_eq_one`), nor can a single ring endomorphism `g` satisfy
   `g x ^ d * x ^ n = 1` for all `x ≠ 0` when `d ≠ 0 ∨ n ≠ 0`
   (`TauCeti.not_forall_map_pow_mul_pow_eq_one`). Consequently, when `g (ξ(s)) = η(s)` holds over
   an infinite field, `η` is a *positive* rational multiple of `ξ`
   (`TauCeti.exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_eq`).

## Main definitions

* `TauCeti.ringHomOfAddMonoidHomTorusCharacter`: upgrades an additive endomorphism `f : K →+ K`
  with `f 1 = 1` and `f (ξ(s) * u) = η(s) * f u` to a ring endomorphism `K →+* K`.
* `TauCeti.ringEquivOfAddEquivTorusCharacter`: the corresponding ring automorphism `K ≃+* K` when
  `f` is an additive equivalence.

## Main results

* `TauCeti.not_forall_map_mul_map_eq_one`: no two ring endomorphisms of an infinite commutative ring
  are multiplicative inverses on nonzero elements.
* `TauCeti.not_forall_map_pow_mul_pow_eq_one`: no ring endomorphism `g` of an infinite commutative
  ring satisfies `g x ^ d * x ^ n = 1` on nonzero elements when `d ≠ 0 ∨ n ≠ 0`.
* `TauCeti.exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp`: over an infinite field, kernel
  inclusion `ker ξ ≤ ker η` forces `d • η = m • ξ` with `0 < d`.
* `TauCeti.exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_eq`: over an infinite field,
  `g (ξ(s)) = η(s)` forces `d • η = m • ξ` with `0 < d` and `0 < m`.
* `TauCeti.ringHom_eq_of_torusCharacter_eq`: when `ξ ≠ 0` and `Kˣ` is divisible, a ring
  endomorphism of `K` is uniquely determined by its values on `ξ(s)`.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  §10–11.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
-/

public section

namespace TauCeti

open Polynomial

section SignObstructions

variable {R : Type*} [CommRing R] [Infinite R]

/-- No positive power kills every nonzero element minus one on an infinite commutative ring. -/
private theorem not_forall_pow_eq_one {d : ℕ} (hd : 0 < d) :
    ¬ ∀ x : R, x ≠ 0 → x ^ d = 1 := by
  intro h
  have : Nontrivial R := Infinite.instNontrivial R
  have hnozero : NoZeroDivisors R :=
    ⟨fun {a b} hab => by
      by_contra hne
      rw [not_or] at hne
      have ha : (a ^ (d - 1)) * a = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hd]
        exact h a hne.1
      have hb : b = 0 := by
        calc b = 1 * b := (one_mul b).symm
          _ = a ^ (d - 1) * (a * b) := by rw [← ha, mul_assoc]
          _ = 0 := by rw [hab, mul_zero]
      exact hne.2 hb⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  let P : R[X] := X * (X ^ d - 1)
  have hP0 : P ≠ 0 := by
    refine mul_ne_zero X_ne_zero fun h1 => ?_
    have heval := congrArg (eval 0) h1
    simp only [eval_sub, eval_pow, eval_X, eval_one, zero_pow hd.ne', zero_sub,
      eval_zero, neg_eq_zero] at heval
    exact one_ne_zero heval
  refine hP0 (Polynomial.zero_of_eval_zero P fun c => ?_)
  simp only [P, eval_mul, eval_sub, eval_pow, eval_X, eval_one]
  by_cases hc : c = 0
  · simp [hc]
  · rw [h c hc, sub_self, mul_zero]

/-- **No two ring endomorphisms of an infinite commutative ring are pointwisely inverse on nonzero
elements.** If `g x * g' x = 1` for every `x ≠ 0`, then `R` is an integral domain, `g` has trivial
kernel, and for `c ≠ 0, -1` expanding `g (c + 1) * g' (c + 1) = 1` yields `g (c ^ 2 + c + 1) = 0`,
forcing every element of `R` to be a root of `X * (X + 1) * (X ^ 2 + X + 1)`. -/
theorem not_forall_map_mul_map_eq_one (g g' : R →+* R) :
    ¬ ∀ x : R, x ≠ 0 → g x * g' x = 1 := by
  intro h
  have : Nontrivial R := Infinite.instNontrivial R
  have hnozero : NoZeroDivisors R :=
    ⟨fun {a b} hab => by
      by_contra hne
      rw [not_or] at hne
      have h1 : (g a * g' a) * (g b * g' b) = 1 := by rw [h a hne.1, h b hne.2, mul_one]
      have h0 : (g a * g' a) * (g b * g' b) = 0 := by
        calc (g a * g' a) * (g b * g' b) = (g a * g b) * (g' a * g' b) := by ring
          _ = g (a * b) * (g' a * g' b) := by rw [map_mul]
          _ = 0 := by rw [hab, map_zero, zero_mul]
      exact one_ne_zero (h1.symm.trans h0)⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  have hginj : Function.Injective g :=
    (injective_iff_map_eq_zero g).mpr fun x hx => by
      by_contra hx0
      have h1 := h x hx0
      rw [hx, zero_mul] at h1
      exact one_ne_zero h1.symm
  let P : R[X] := X * (X + 1) * (X ^ 2 + X + 1)
  have hP0 : P ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero X_ne_zero ?_) ?_
    · intro h1
      simpa using congrArg (eval 0) h1
    · intro h2
      simpa using congrArg (eval 0) h2
  refine hP0 (Polynomial.zero_of_eval_zero P fun c => ?_)
  simp only [P, eval_mul, eval_add, eval_pow, eval_X, eval_one]
  by_cases hc0 : c = 0
  · simp [hc0]
  by_cases hc1 : c + 1 = 0
  · simp [hc1]
  have hmul1 : g c * g' c = 1 := h c hc0
  have hmul2 : (g c + 1) * (g' c + 1) = 1 := by simpa only [map_add, map_one] using h (c + 1) hc1
  have hquad : g (c ^ 2 + c + 1) = 0 := by
    rw [map_add, map_add, map_pow, map_one]
    calc g c ^ 2 + g c + 1
      _ = g c * ((g c + 1) * (g' c + 1) - g c * g' c) + (1 - g c * g' c) := by ring
      _ = g c * (1 - 1) + (1 - 1) := by rw [hmul2, hmul1]
      _ = 0 := by ring
  rw [hginj (hquad.trans g.map_zero.symm), mul_zero]

/-- Any nontrivial commutative ring in which every `x ≠ 0` satisfies `g x ^ d * x ^ n = 1` for
some `n > 0` has no nonzero zero divisors, hence is a domain. -/
private theorem isDomain_of_forall_map_pow_mul_pow_eq_one (g : R →+* R) {d n : ℕ} (hn : 0 < n)
    (h : ∀ x : R, x ≠ 0 → g x ^ d * x ^ n = 1) : IsDomain R := by
  have : Nontrivial R := Infinite.instNontrivial R
  have : NoZeroDivisors R := ⟨fun {a b} hab => by
    by_contra hne
    rw [not_or] at hne
    have ha : (g a ^ d * a ^ (n - 1)) * a = 1 := by
      rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
      exact h a hne.1
    exact hne.2 <| by
      calc b = 1 * b := (one_mul b).symm
        _ = (g a ^ d * a ^ (n - 1)) * (a * b) := by rw [← ha, mul_assoc]
        _ = 0 := by rw [hab, mul_zero]⟩
  exact NoZeroDivisors.to_isDomain R

/-- On an infinite commutative ring, `g x ^ d * x ^ n = 1` cannot hold for all `x ≠ 0` when both
exponents `d` and `n` are positive. -/
private theorem not_forall_map_pow_mul_pow_eq_one_of_pos (g : R →+* R) {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) :
    ¬ ∀ x : R, x ≠ 0 → g x ^ d * x ^ n = 1 := by
  intro h
  have : IsDomain R := isDomain_of_forall_map_pow_mul_pow_eq_one g hn h
  let P : R[X] := X * (X ^ d + 1) * ((X ^ n + 1) ^ d * (X ^ d + 1) ^ n - X ^ (n * d))
  have hP0 : P ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero X_ne_zero ?_) ?_
    · intro h1
      have heval := congrArg (eval 0) h1
      simp only [eval_add, eval_pow, eval_X, eval_one, zero_pow hd.ne', zero_add,
        eval_zero] at heval
      exact one_ne_zero heval
    · intro h2
      have heval := congrArg (eval 0) h2
      simp only [eval_sub, eval_mul, eval_pow, eval_add, eval_X, eval_one, zero_pow hn.ne',
        zero_pow hd.ne', zero_pow (Nat.mul_ne_zero hn.ne' hd.ne'), zero_add, one_pow, mul_one,
        sub_zero, eval_zero] at heval
      exact one_ne_zero heval
  refine hP0 (Polynomial.zero_of_eval_zero P fun c => ?_)
  simp only [P, eval_mul, eval_sub, eval_pow, eval_add, eval_X, eval_one]
  by_cases hc0 : c = 0
  · simp [hc0]
  by_cases hcd1 : c ^ d + 1 = 0
  · rw [hcd1, mul_zero, zero_mul]
  have hcd : g (c ^ d) * c ^ n = 1 := by rw [map_pow]; exact h c hc0
  have hcd_succ : (g (c ^ d) + 1) ^ d * (c ^ d + 1) ^ n = 1 := by
    simpa only [map_add, map_one] using h (c ^ d + 1) hcd1
  have hpoly : (c ^ n + 1) ^ d * (c ^ d + 1) ^ n - c ^ (n * d) = 0 := by
    have hstep : c ^ n + 1 = (g (c ^ d) + 1) * c ^ n := by
      calc c ^ n + 1 = g (c ^ d) * c ^ n + c ^ n := by rw [hcd, add_comm]
        _ = (g (c ^ d) + 1) * c ^ n := by ring
    calc (c ^ n + 1) ^ d * (c ^ d + 1) ^ n - c ^ (n * d)
      _ = (g (c ^ d) + 1) ^ d * (c ^ n) ^ d * (c ^ d + 1) ^ n - (c ^ n) ^ d := by
          rw [hstep, mul_pow, pow_mul]
      _ = ((g (c ^ d) + 1) ^ d * (c ^ d + 1) ^ n) * (c ^ n) ^ d - (c ^ n) ^ d := by ring
      _ = 1 * (c ^ n) ^ d - (c ^ n) ^ d := by rw [hcd_succ]
      _ = 0 := by ring
  rw [hpoly, mul_zero]

/-- **No ring endomorphism of an infinite commutative ring satisfies a nontrivial negative-exponent
power law on nonzero elements.** If `g x ^ d * x ^ n = 1` for every `x ≠ 0` with `d ≠ 0 ∨ n ≠ 0`,
then `d = 0` or `n = 0` reduces to `x ^ m = 1`, while for `0 < d` and `0 < n` evaluating at
`c ^ d + 1` forces every element of `R` to be a root of
`X * (X ^ d + 1) * ((X ^ n + 1) ^ d * (X ^ d + 1) ^ n - X ^ (n * d))`. -/
theorem not_forall_map_pow_mul_pow_eq_one (g : R →+* R) {d n : ℕ} (hdn : d ≠ 0 ∨ n ≠ 0) :
    ¬ ∀ x : R, x ≠ 0 → g x ^ d * x ^ n = 1 := by
  intro h
  have : Nontrivial R := Infinite.instNontrivial R
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hn : 0 < n := Nat.pos_of_ne_zero (hdn.resolve_left (not_not.mpr rfl))
    exact not_forall_pow_eq_one hn fun x hx => by simpa using h x hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hginj : Function.Injective g :=
      (injective_iff_map_eq_zero g).mpr fun x hx => by
        by_contra hx0
        have h1 := h x hx0
        rw [hx, zero_pow hd.ne', pow_zero, mul_one] at h1
        exact one_ne_zero h1.symm
    refine not_forall_pow_eq_one hd fun x hx => hginj ?_
    simpa [map_pow] using h x hx
  exact not_forall_map_pow_mul_pow_eq_one_of_pos g hd hn h

end SignObstructions

section TorusCharacterProportionality

variable {κ : Type*} [Fintype κ]

/-- **Kernel inclusion between split-torus characters over an infinite field forces rational
proportionality.** If every torus point killed by `ξ` is also killed by `η`, then `d • η = m • ξ`
for some integer `m` and positive natural number `d`. -/
theorem exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp {K : Type*} [Field K] [Infinite K]
    {ξ η : κ → ℤ}
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
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ξ i₀ ≠ 0 := Function.ne_iff.mp hξ
  have hprop : ξ i₀ • η = η i₀ • ξ := by
    by_contra hne
    obtain ⟨i₁, hi₁⟩ : ∃ i₁, (ξ i₀ • η) i₁ ≠ (η i₀ • ξ) i₁ := Function.ne_iff.mp hne
    let δ : ℤ := ξ i₀ * η i₁ - η i₀ * ξ i₁
    have hδ : δ ≠ 0 := sub_ne_zero.mpr hi₁
    have hsingle : (Pi.single i₀ δ : κ → ℤ) ≠ 0 := fun h0 =>
      hδ (by simpa using congrFun h0 i₀)
    obtain ⟨t, ht⟩ := exists_torusCharacter_ne (K := K) hsingle
    simp only [torusCharacter_single, torusCharacter_zero] at ht
    let u : Kˣ := t i₀
    let s : κ → Kˣ := Pi.mulSingle i₀ (u ^ (-ξ i₁)) * Pi.mulSingle i₁ (u ^ (ξ i₀))
    have hsξ : torusCharacter s ξ = 1 := by
      rw [torusCharacter_mul, torusCharacter_mulSingle, torusCharacter_mulSingle,
        ← zpow_mul, ← zpow_mul, ← zpow_add]
      have hexp : -ξ i₁ * ξ i₀ + ξ i₀ * ξ i₁ = 0 := by ring
      rw [hexp, zpow_zero]
    have hsη : torusCharacter s η ≠ 1 := by
      rw [torusCharacter_mul, torusCharacter_mulSingle, torusCharacter_mulSingle,
        ← zpow_mul, ← zpow_mul, ← zpow_add]
      have hexp : -ξ i₁ * η i₀ + ξ i₀ * η i₁ = δ := by dsimp [δ]; ring
      rwa [hexp]
    exact hsη (hker s hsξ)
  rcases lt_or_gt_of_ne hi₀ with hneg | hpos
  · refine ⟨(-ξ i₀).toNat, Int.lt_toNat.mpr (neg_pos.mpr hneg), -η i₀, ?_⟩
    rw [← natCast_zsmul, Int.toNat_of_nonneg (neg_nonneg.mpr hneg.le), neg_smul, hprop, neg_smul]
  · refine ⟨(ξ i₀).toNat, Int.lt_toNat.mpr hpos, η i₀, ?_⟩
    rw [← natCast_zsmul, Int.toNat_of_nonneg hpos.le, hprop]

/-- **Intertwining a ring endomorphism with split-torus characters forces positive rational
proportionality.** Over an infinite field, if `g (ξ(s)) = η(s)` for every torus point `s`, then
`d • η = m • ξ` with `0 < d` and `0 < m`. -/
theorem exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_eq {K : Type*} [Field K] [Infinite K]
    (g : K →+* K) {ξ η : κ → ℤ}
    (hmap : ∀ s : κ → Kˣ, g (torusCharacter s ξ : K) = (torusCharacter s η : K)) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧ d • η = m • ξ := by
  classical
  have hker : ∀ s : κ → Kˣ, torusCharacter s ξ = 1 → torusCharacter s η = 1 := fun s hs =>
    Units.ext (by simpa [hs] using (hmap s).symm)
  by_cases hξ : ξ = 0
  · subst hξ
    have hη : η = 0 := by
      by_contra hη0
      obtain ⟨s, hs⟩ := exists_torusCharacter_ne (K := K) hη0
      exact hs ((hker s (torusCharacter_zero s)).trans (torusCharacter_zero s).symm)
    exact ⟨1, 1, Nat.one_pos, Nat.one_pos, by simp [hη]⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ξ i₀ ≠ 0 := Function.ne_iff.mp hξ
  obtain ⟨d, hd, z, hz⟩ := exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp hker
  let a : ℕ := (ξ i₀).natAbs
  have had : 0 < a * d := Nat.mul_pos (Int.natAbs_pos.mpr hi₀) hd
  have hpow : ∀ u : Kˣ, g u ^ (a * d) = ((u ^ ((a : ℤ) * z) : Kˣ) : K) := fun u => by
    let s : κ → Kˣ := Pi.mulSingle i₀ (if 0 ≤ ξ i₀ then u else u⁻¹)
    have hsξ : torusCharacter s ξ = u ^ a := by
      rw [torusCharacter_mulSingle]
      split_ifs with hnonneg
      · rw [← zpow_natCast, Int.natAbs_of_nonneg hnonneg]
      · have hneg : ξ i₀ = -(a : ℤ) := by
          rw [Int.ofNat_natAbs_of_nonpos (le_of_not_ge hnonneg), neg_neg]
        rw [hneg, inv_zpow', neg_neg, zpow_natCast]
    calc g u ^ (a * d) = (g ((u ^ a : Kˣ) : K)) ^ d := by
          rw [Units.val_pow_eq_pow_val, map_pow, pow_mul]
      _ = ((torusCharacter s η ^ d : Kˣ) : K) := by
          rw [← hsξ, hmap s, Units.val_pow_eq_pow_val]
      _ = ((u ^ ((a : ℤ) * z) : Kˣ) : K) := by
          rw [← torusCharacter_nsmul, hz, torusCharacter_zsmul, hsξ, ← zpow_natCast, ← zpow_mul]
  rcases lt_trichotomy z 0 with hzneg | rfl | hzpos
  · exfalso
    let n : ℕ := (-z).toNat
    have hzn : (a : ℤ) * z = -((a * n : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Int.toNat_of_nonneg (neg_nonneg.mpr hzneg.le), mul_neg, neg_neg]
    refine not_forall_map_pow_mul_pow_eq_one g (.inl had.ne') (n := a * n) fun x hx => ?_
    have h1 := hpow (Units.mk0 x hx)
    rw [Units.val_mk0] at h1
    rw [h1, hzn, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_mk0, inv_mul_cancel₀ (pow_ne_zero _ hx)]
  · exfalso
    refine not_forall_map_pow_mul_pow_eq_one g (.inl had.ne') (n := 0) fun x hx => ?_
    simpa using hpow (Units.mk0 x hx)
  · refine ⟨d, z.toNat, hd, Int.lt_toNat.mpr hzpos, ?_⟩
    rw [hz, ← natCast_zsmul, Int.toNat_of_nonneg hzpos.le]

end TorusCharacterProportionality

section ConstructRingHom

variable {κ : Type*} [Fintype κ] {K : Type*} [Field K] [RootableBy Kˣ ℕ]

/-- **Upgrading an additive map intertwined with split-torus characters to a ring endomorphism.**
When `ξ ≠ 0` and `Kˣ` is divisible, every nonzero element of `K` has the form `ξ(s)` for some
torus point `s`, so `f (ξ(s) * u) = η(s) * f u` together with `f 1 = 1` forces `f` to preserve
multiplication. -/
def ringHomOfAddMonoidHomTorusCharacter (f : K →+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0)
    (hf1 : f 1 = 1)
    (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) :
    K →+* K where
  toFun := f
  map_zero' := f.map_zero
  map_add' := f.map_add
  map_one' := hf1
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    · obtain ⟨s, hs⟩ := torusCharacter_surjective hξ (Units.mk0 x hx)
      have hxval : (torusCharacter s ξ : K) = x := by simpa using congrArg Units.val hs
      have hfx : f x = (torusCharacter s η : K) := by
        simpa only [hxval, mul_one, hf1] using hscale s 1
      rw [← hxval, hscale s y, hxval, hfx]

@[simp]
theorem coe_ringHomOfAddMonoidHomTorusCharacter (f : K →+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0)
    (hf1 : f 1 = 1)
    (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) :
    ⇑(ringHomOfAddMonoidHomTorusCharacter f hξ hf1 hscale) = f :=
  (rfl)

@[simp]
theorem ringHomOfAddMonoidHomTorusCharacter_apply (f : K →+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0)
    (hf1 : f 1 = 1)
    (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) (x : K) :
    ringHomOfAddMonoidHomTorusCharacter f hξ hf1 hscale x = f x :=
  (rfl)

/-- On torus character values of `ξ`, the upgraded ring endomorphism evaluates to the values of
`η`. -/
theorem ringHomOfAddMonoidHomTorusCharacter_torusCharacter (f : K →+ K) {ξ η : κ → ℤ}
    (hξ : ξ ≠ 0) (hf1 : f 1 = 1)
    (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u)
    (s : κ → Kˣ) :
    ringHomOfAddMonoidHomTorusCharacter f hξ hf1 hscale (torusCharacter s ξ : K) =
      (torusCharacter s η : K) := by
  simpa only [ringHomOfAddMonoidHomTorusCharacter_apply, mul_one, hf1] using hscale s 1

/-- **Upgrading an additive equivalence intertwined with split-torus characters to a ring
automorphism.** -/
def ringEquivOfAddEquivTorusCharacter (f : K ≃+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0)
    (hf1 : f 1 = 1)
    (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) :
    K ≃+* K :=
  { f, ringHomOfAddMonoidHomTorusCharacter f.toAddMonoidHom hξ hf1 hscale with }

@[simp]
theorem ringEquivOfAddEquivTorusCharacter_apply (f : K ≃+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0)
    (hf1 : f 1 = 1)
    (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) (x : K) :
    ringEquivOfAddEquivTorusCharacter f hξ hf1 hscale x = f x :=
  (rfl)

@[simp]
theorem coe_ringEquivOfAddEquivTorusCharacter (f : K ≃+ K) {ξ η : κ → ℤ} (hξ : ξ ≠ 0)
    (hf1 : f 1 = 1)
    (hscale : ∀ (s : κ → Kˣ) (u : K),
      f ((torusCharacter s ξ : K) * u) = (torusCharacter s η : K) * f u) :
    (ringEquivOfAddEquivTorusCharacter f hξ hf1 hscale : K →+* K) =
      ringHomOfAddMonoidHomTorusCharacter f.toAddMonoidHom hξ hf1 hscale :=
  (rfl)

/-- **A ring endomorphism of `K` is uniquely determined by its values on a nonzero split-torus
character**, provided `Kˣ` is divisible. -/
theorem ringHom_eq_of_torusCharacter_eq {g₁ g₂ : K →+* K} {ξ : κ → ℤ} (hξ : ξ ≠ 0)
    (h : ∀ s : κ → Kˣ, g₁ (torusCharacter s ξ : K) = g₂ (torusCharacter s ξ : K)) :
    g₁ = g₂ := by
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨s, hs⟩ := torusCharacter_surjective hξ (Units.mk0 x hx)
    have hxval : (torusCharacter s ξ : K) = x := by simpa using congrArg Units.val hs
    rw [← hxval, h s]

end ConstructRingHom

end TauCeti
