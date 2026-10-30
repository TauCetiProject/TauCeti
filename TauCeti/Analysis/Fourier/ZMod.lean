/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.ZMod
import TauCeti.Data.ZMod.Count

/-!
# The discrete Fourier transform of a function of the reduction modulo a divisor

For `v ∣ N`, a function `f` on `ZMod v` pulls back to `ZMod N` along the reduction
`j ↦ (j.val : ZMod v)`. Its discrete Fourier transform modulo `N` is supported on the multiples
of `L = N / v`, where it is `L` times the transform of `f` modulo `v`:
`𝓕 (f ∘ reduction) (L m) = L • 𝓕 f m`. At the multiples of `L` the additive characters modulo `N`
are those modulo `v`, and every fibre of the reduction has `L` elements. Off the multiples of `L`,
translating by `v`, which fixes the reduction, multiplies the transform by a nontrivial root of
unity, so the transform vanishes.

This is how the Fourier coefficients of a Dirichlet character modulo `v` appear in sums over the
residues modulo a multiple `N` of `v`.

## Main results

* `ZMod.dft_comp_natCast_val`: the transform of a function of the reduction modulo `v ∣ N`.
-/

public section

namespace ZMod

variable {v N : ℕ} [NeZero v] [NeZero N] {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- **The Fourier transform of a function of the reduction modulo a divisor.** For `v ∣ N` and
`L = N / v`, the discrete Fourier transform modulo `N` of `j ↦ f (j mod v)` is `L • 𝓕 f m` at
`k = L m`, and vanishes at the `k` that are not multiples of `L`. -/
theorem dft_comp_natCast_val (hv : v ∣ N) (f : ZMod v → E) (k : ℤ) :
    𝓕 (fun j : ZMod N ↦ f (j.val : ZMod v)) (k : ZMod N) =
      if ((N / v : ℕ) : ℤ) ∣ k then (N / v) • 𝓕 f ((k / (N / v : ℕ) : ℤ) : ZMod v) else 0 := by
  set L := N / v
  have hN : N = v * L := (Nat.mul_div_cancel' hv).symm
  have hL : L ≠ 0 := fun h ↦ NeZero.ne N (by rw [hN, h, mul_zero])
  rw [dft_apply]
  split_ifs with hk
  · obtain ⟨m, rfl⟩ := hk
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hL), dft_apply,
      ← sum_comp_natCast_val hv]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    -- the character modulo `N` at `-j L m` is the character modulo `v` at `-j m`
    have h₁ : -(j * ((L * m : ℤ) : ZMod N)) = ((-((j.val : ℤ) * L * m) : ℤ) : ZMod N) := by
      push_cast
      rw [natCast_zmod_val]
      ring
    have h₂ : -(((j.val : ℕ) : ZMod v) * (m : ZMod v)) = ((-((j.val : ℤ) * m) : ℤ) : ZMod v) := by
      push_cast
      ring
    rw [h₁, h₂, stdAddChar_coe, stdAddChar_coe]
    congr 2
    have hv' : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
    have hL' : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hL
    have hN' : (N : ℂ) = v * L := by exact_mod_cast hN
    rw [hN']
    push_cast
    field_simp
  · -- translating by `v` fixes the reduction and multiplies the transform by `e(-v k / N) ≠ 1`
    set T : ZMod N → E := fun j ↦ stdAddChar (-(j * (k : ZMod N))) • f (j.val : ZMod v)
    have hred (j : ZMod N) : (((j + v).val : ℕ) : ZMod v) = (j.val : ZMod v) := by
      rw [natCast_val, natCast_val, cast_add hv, cast_natCast hv, natCast_self, add_zero]
    have hshift : ∑ j, T j = stdAddChar (-((v : ZMod N) * (k : ZMod N))) • ∑ j, T j := by
      rw [Finset.smul_sum]
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight (v : ZMod N)) T]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [T, Equiv.coe_addRight, hred, smul_smul]
      rw [← AddChar.map_add_eq_mul]
      congr 2
      ring
    have hne : stdAddChar (-((v : ZMod N) * (k : ZMod N))) ≠ 1 := by
      intro h
      rw [← AddChar.map_zero_eq_one (stdAddChar (N := N)), injective_stdAddChar.eq_iff,
        neg_eq_zero] at h
      have h' : ((v * k : ℤ) : ZMod N) = 0 := by
        push_cast
        exact h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hN, Nat.cast_mul] at h'
      exact hk ((mul_dvd_mul_iff_left (by exact_mod_cast NeZero.ne v)).mp h')
    have h0 : (1 - stdAddChar (-((v : ZMod N) * (k : ZMod N)))) • ∑ j, T j = 0 := by
      rw [sub_smul, one_smul, ← hshift, sub_self]
    exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne.symm)

end ZMod
