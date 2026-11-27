/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
public import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.Data.ZMod.Count

/-!
# Gauss sums of imprimitive Dirichlet characters

Let `χ` be a Dirichlet character modulo `N` with conductor `f` and primitive character `χ^∗`
modulo `f`, and write `τ(χ) = ∑_a χ(a) e(a / N)` for the Gauss sum against the standard additive
character. Then `τ(χ) = μ(N / f) χ^∗(N / f) τ(χ^∗)`. In particular `τ(χ) = 0` unless `N / f` is
squarefree and prime to `f`, and the principal character has `τ(1_N) = μ(N)`.

With `r = N / f`, the character `χ` is `χ^∗` times the indicator of `gcd(a, r) = 1`. The Möbius
sum over the common divisors `d` of `a` and `r` removes the indicator, so
`τ(χ) = ∑_{d ∣ r} μ(d) χ^∗(d) ∑_{b mod N / d} χ^∗(b) e(b / (N / d))`. Since `χ^∗` is primitive, the
inner sum vanishes unless `N / d = f`, that is `d = r`, where it is `τ(χ^∗)`
(`DirichletCharacter.IsPrimitive.sum_inv_mul_stdAddChar`).

## Main results

* `DirichletCharacter.gaussSum_eq_moebius_mul`: `τ(χ) = μ(N / f) χ^∗(N / f) τ(χ^∗)`.
* `DirichletCharacter.gaussSum_one`: `τ(1_N) = μ(N)`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
  Theorem 9.10.
-/

public section

open Finset
open scoped ArithmeticFunction.Moebius

namespace DirichletCharacter

/-- The Möbius sum over the divisors `d` of `r` with `d ∣ k` is the indicator of `gcd(k, r) = 1`.
-/
private lemma sum_filter_dvd_moebius {r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    ∑ d ∈ r.divisors with d ∣ k, (μ d : ℂ) = if k.Coprime r then 1 else 0 := by
  have hfilter : {d ∈ r.divisors | d ∣ k} = (k.gcd r).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, ne_eq, Nat.gcd_eq_zero_iff]
    tauto
  have h := congrArg (fun g : ArithmeticFunction ℤ ↦ (g (k.gcd r) : ℂ))
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    Int.cast_sum] at h
  rw [hfilter, h]
  by_cases hk : k.gcd r = 1
  · rw [ite_eq_left hk, ite_eq_left (Nat.coprime_iff_gcd_eq_one.mpr hk), Int.cast_one]
  · rw [ite_eq_right hk, ite_eq_right (mt Nat.coprime_iff_gcd_eq_one.mp hk), Int.cast_zero]

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- A Dirichlet character is its primitive character times the indicator of
`gcd(a, N / f) = 1`, where `f` is the conductor. -/
private lemma apply_eq_primitiveCharacter_mul_ite (a : ZMod N) :
    χ a = χ.primitiveCharacter (a.val : ZMod χ.conductor) *
      if a.val.Coprime (N / χ.conductor) then 1 else 0 := by
  have hN : χ.conductor * (N / χ.conductor) = N := Nat.mul_div_cancel' χ.conductor_dvd_level
  by_cases ha : IsUnit a
  · have hcop : a.val.Coprime N := by
      rwa [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    rw [ite_eq_left (hcop.coprime_dvd_right (Nat.div_dvd_of_dvd χ.conductor_dvd_level)), mul_one]
    conv_lhs => rw [← χ.changeLevel_primitiveCharacter, ← ha.unit_spec]
    rw [changeLevel_eq_cast_of_dvd, IsUnit.unit_spec, ZMod.cast_eq_val]
  · rw [χ.map_nonunit ha]
    split_ifs with hr
    · rw [mul_one, eq_comm]
      refine MulChar.map_nonunit _ fun hu ↦ ha ?_
      have hf : a.val.Coprime χ.conductor := (ZMod.isUnit_iff_coprime _ _).mp hu
      have hcop := Nat.Coprime.mul_right hf hr
      rw [hN] at hcop
      rwa [← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime]
    · rw [mul_zero]

/-- The standard additive character modulo `N` at `d k` is the one modulo `N / d` at `k`. -/
private lemma stdAddChar_natCast_mul {d : ℕ} (hd : d ∣ N) [NeZero (N / d)] (k : ℕ) :
    ZMod.stdAddChar ((d * k : ℕ) : ZMod N) = ZMod.stdAddChar ((k : ℕ) : ZMod (N / d)) := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd
    (h ▸ hd))
  rw [← Int.cast_natCast, ← Int.cast_natCast (R := ZMod (N / d)), ZMod.stdAddChar_coe,
    ZMod.stdAddChar_coe, Nat.cast_div hd hd0]
  congr 1
  push_cast
  field_simp

/-- The terms of `τ(χ)` at the multiples of a divisor `d` of `N / f` sum to
`χ^∗(d) ∑_{b mod N / d} χ^∗(b) e(b / (N / d))`. -/
private lemma sum_ite_dvd_val_eq {d : ℕ} (hd : d ∣ N / χ.conductor) [NeZero (N / d)] :
    ∑ a : ZMod N, (if d ∣ a.val then
        χ.primitiveCharacter (a.val : ZMod χ.conductor) * ZMod.stdAddChar a else 0) =
      χ.primitiveCharacter (d : ZMod χ.conductor) *
        ∑ b : ZMod (N / d), χ.primitiveCharacter (b.val : ZMod χ.conductor) *
          ZMod.stdAddChar b := by
  have hdN : d ∣ N := hd.trans (Nat.div_dvd_of_dvd χ.conductor_dvd_level)
  have hNd : N / (N / d) = d := Nat.div_div_self hdN (NeZero.ne N)
  have h := ZMod.sum_ite_dvd_val (m := N / d) (n := N) (Nat.div_dvd_of_dvd hdN)
    (fun k ↦ χ.primitiveCharacter ((d * k : ℕ) : ZMod χ.conductor) *
      ZMod.stdAddChar ((d * k : ℕ) : ZMod N))
  rw [hNd] at h
  convert h using 1
  · refine sum_congr rfl fun a _ ↦ ?_
    split_ifs with ha
    · rw [Nat.mul_div_cancel' ha, ZMod.natCast_zmod_val]
    · rfl
  · rw [mul_sum]
    refine sum_congr rfl fun b _ ↦ ?_
    rw [stdAddChar_natCast_mul hdN, ZMod.natCast_zmod_val, Nat.cast_mul, map_mul, mul_assoc]

/-- The inner sum `∑_{b mod N / d} χ^∗(b) e(b / (N / d))` is `τ(χ^∗)` for `d = N / f` and `0` for
the other divisors `d` of `N / f`. -/
private lemma sum_primitiveCharacter_mul_stdAddChar {d : ℕ} (hd : d ∣ N / χ.conductor)
    [NeZero (N / d)] :
    ∑ b : ZMod (N / d), χ.primitiveCharacter (b.val : ZMod χ.conductor) * ZMod.stdAddChar b =
      if d = N / χ.conductor then gaussSum χ.primitiveCharacter ZMod.stdAddChar else 0 := by
  obtain ⟨s, hs⟩ := hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact NeZero.ne (N / 0) (Nat.div_zero N)
  have hN : N = χ.conductor * (d * s) := by
    rw [← hs, Nat.mul_div_cancel' χ.conductor_dvd_level]
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (by rw [hN, mul_zero, mul_zero])
  have hNd : N / d = χ.conductor * s :=
    Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hd0) (hN.trans (by ring))
  have hs' : N / d / χ.conductor = s :=
    Nat.div_eq_of_eq_mul_left (NeZero.pos _) (by rw [hNd, mul_comm])
  have h := (χ.primitiveCharacter_isPrimitive.inv).sum_inv_mul_stdAddChar
    (hNd ▸ dvd_mul_right χ.conductor s) 1
  simp only [inv_inv, one_mul] at h
  rw [h, hs', ZMod.val_one_eq_one_mod]
  by_cases hs1 : s = 1
  · subst hs1
    rw [ite_eq_left (one_dvd _), ite_eq_left (by rw [hs, mul_one]), Nat.div_one, hNd, mul_one,
      ZMod.natCast_mod]
    simp
  · have h1 : 1 % (N / d) = 1 := Nat.mod_eq_of_lt (by
      rw [hNd]
      exact lt_of_lt_of_le (by omega : 1 < s) (Nat.le_mul_of_pos_left s (NeZero.pos _)))
    rw [h1, ite_eq_right (fun h ↦ hs1 (Nat.dvd_one.mp h)), ite_eq_right fun h ↦ hs1 ?_]
    rw [hs] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) (by rw [mul_one]; exact h.symm)

/-- **The Gauss sum of an imprimitive character**: if `χ` modulo `N` has conductor `f` and
primitive character `χ^∗`, then `τ(χ) = μ(N / f) χ^∗(N / f) τ(χ^∗)`. -/
theorem gaussSum_eq_moebius_mul :
    gaussSum χ ZMod.stdAddChar = μ (N / χ.conductor) *
      χ.primitiveCharacter ((N / χ.conductor : ℕ) : ZMod χ.conductor) *
        gaussSum χ.primitiveCharacter ZMod.stdAddChar := by
  have hr : N / χ.conductor ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) χ.conductor_dvd_level) (NeZero.pos _)).ne'
  -- Remove the coprimality to `N / f` by a Möbius sum, and exchange the sums.
  calc gaussSum χ ZMod.stdAddChar
      = ∑ a : ZMod N, ∑ d ∈ (N / χ.conductor).divisors, if d ∣ a.val then (μ d : ℂ) *
          (χ.primitiveCharacter (a.val : ZMod χ.conductor) * ZMod.stdAddChar a) else 0 := by
        rw [gaussSum]
        refine sum_congr rfl fun a _ ↦ ?_
        rw [apply_eq_primitiveCharacter_mul_ite, ← sum_filter_dvd_moebius hr, sum_filter, mul_sum,
          sum_mul]
        refine sum_congr rfl fun d _ ↦ ?_
        split_ifs <;> ring
    _ = ∑ d ∈ (N / χ.conductor).divisors, (μ d : ℂ) *
          (χ.primitiveCharacter (d : ZMod χ.conductor) *
            if d = N / χ.conductor then gaussSum χ.primitiveCharacter ZMod.stdAddChar else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun d hd ↦ ?_
        have hdr : d ∣ N / χ.conductor := Nat.dvd_of_mem_divisors hd
        have : NeZero (N / d) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N)
          (hdr.trans (Nat.div_dvd_of_dvd χ.conductor_dvd_level))) (Nat.pos_of_mem_divisors hd)).ne'⟩
        rw [← sum_primitiveCharacter_mul_stdAddChar χ hdr, ← sum_ite_dvd_val_eq χ hdr, mul_sum]
        simp_rw [mul_ite, mul_zero]
    _ = _ := by
        simp_rw [mul_ite, mul_zero]
        rw [sum_ite_eq', ite_eq_left (Nat.mem_divisors_self _ hr), mul_assoc]

/-- The Gauss sum of the principal character modulo `N` is `μ(N)`. -/
theorem gaussSum_one : gaussSum (1 : DirichletCharacter ℂ N) ZMod.stdAddChar = μ N := by
  -- A character of level `1` is `1` everywhere, and its Gauss sum is `1`.
  have key {c : ℕ} [NeZero c] (hc : c = 1) (ψ : DirichletCharacter ℂ c) (x : ZMod c) :
      ψ x = 1 ∧ gaussSum ψ ZMod.stdAddChar = 1 := by
    subst hc
    refine ⟨by rw [Subsingleton.elim x 1, map_one], ?_⟩
    rw [gaussSum, Fintype.sum_subsingleton _ 0, AddChar.map_zero_eq_one, mul_one,
      Subsingleton.elim (0 : ZMod 1) 1, map_one]
  have hc : (1 : DirichletCharacter ℂ N).conductor = 1 := conductor_one
  obtain ⟨h1, h2⟩ := key hc (1 : DirichletCharacter ℂ N).primitiveCharacter
    ((N / (1 : DirichletCharacter ℂ N).conductor : ℕ) : ZMod _)
  rw [gaussSum_eq_moebius_mul, h1, h2, hc, Nat.div_one, mul_one, mul_one]

end DirichletCharacter
