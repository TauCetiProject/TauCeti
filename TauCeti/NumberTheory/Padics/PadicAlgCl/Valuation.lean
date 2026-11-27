/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.LogGauge.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.RingTheory.RootsOfUnity.Ultrametric

/-!
# The normalized real additive valuation on the algebraic p-adic field

This is the logarithmic gauge of `p`, with values in `WithTop ℝ`. It is not truncated outside
the valuation ring. On integral elements it is the usual nonnegative normalized valuation.

## Provenance

`TauCeti.padicAlgClRealValuation` adapts `New.ellVal` in
`src/Lib/GaloisRep/Main/SelmerModules.lean`.
`TauCeti.padicAlgClRealValuation_sub_one` adapts
`New.Selmer.ellVal_sub_one_of_isPrimitiveRoot` in
`src/Lib/General/NumberTheory/GaussValuation.lean` and
`New.Selmer.ellVal_sub_one_eq_rootRadius` in
`src/New/Congruences/Selmer/RootsOfUnity.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The native logarithmic-gauge API supplies an untruncated
valuation, and the primitive-root formula follows from the existing norm formula.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Chapters 1–2.
-/

public section

noncomputable section
open TauCeti
namespace TauCeti

open scoped NNReal
variable (p : ℕ) [Fact p.Prime]

/-- The scalar `p` as a multiplicative pseudo-uniformizer of the algebraic p-adic field. -/
def padicAlgClPseudoUniformizer : NormedRing.PseudoUniformizer (PadicAlgCl p) :=
  .ofAlgebraMap (K := ℚ_[p]) (A := PadicAlgCl p)
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) Padic.norm_p_lt_one

/-- The underlying element of the canonical pseudo-uniformizer is `p`. -/
@[simp]
theorem coe_unit_padicAlgClPseudoUniformizer :
    ((padicAlgClPseudoUniformizer p).unit : PadicAlgCl p) = p := by
  simp [padicAlgClPseudoUniformizer]

/-- The real additive valuation on the algebraic p-adic field, normalized at `p`. -/
def padicAlgClRealValuation : AddValuation (PadicAlgCl p) (WithTop ℝ) :=
  (padicAlgClPseudoUniformizer p).addValuation

/-- The scalar defining the pseudo-uniformizer has norm `p⁻¹`. -/
theorem norm_unit_padicAlgClPseudoUniformizer :
    ‖((padicAlgClPseudoUniformizer p).unit : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [coe_unit_padicAlgClPseudoUniformizer]
  have H := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) (PadicAlgCl.valuation_p p)
  simpa only [PadicAlgCl.valuation_coe, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_natCast, NNReal.coe_inv, one_div] using H

/-- Nonnegative valuation characterizes the ring of integral elements. -/
theorem padicAlgClRealValuation_nonneg_iff (x : PadicAlgCl p) :
    0 ≤ padicAlgClRealValuation p x ↔ ‖x‖ ≤ 1 := by
  rw [padicAlgClRealValuation, NormedRing.PseudoUniformizer.addValuation_apply,
    NormedRing.PseudoUniformizer.logGauge_nonneg_iff]

/-- An upper bound on the normalized valuation is a lower bound on the norm. -/
theorem padicAlgClRealValuation_le_iff (x : PadicAlgCl p) (t : ℝ) :
    padicAlgClRealValuation p x ≤ t ↔ (p : ℝ) ^ (-t) ≤ ‖x‖ := by
  rw [padicAlgClRealValuation, NormedRing.PseudoUniformizer.addValuation_apply,
    NormedRing.PseudoUniformizer.logGauge_le_coe_iff,
    norm_unit_padicAlgClPseudoUniformizer, Real.inv_rpow (Nat.cast_nonneg p),
    ← Real.rpow_neg (Nat.cast_nonneg p)]

/-- The normalized valuation of `p` is one. -/
@[simp]
theorem padicAlgClRealValuation_p : padicAlgClRealValuation p (p : PadicAlgCl p) = 1 := by
  rw [padicAlgClRealValuation, NormedRing.PseudoUniformizer.addValuation_apply,
    ← coe_unit_padicAlgClPseudoUniformizer p]
  exact (padicAlgClPseudoUniformizer p).logGauge_unit

/-- The normalized valuation of a primitive `p ^ h`-th root of unity minus one. -/
theorem padicAlgClRealValuation_sub_one {h : ℕ} (hh : 1 ≤ h) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ h)) :
    padicAlgClRealValuation p (ζ - 1) = ((Nat.totient (p ^ h) : ℝ)⁻¹ : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hh
  have H := hζ.norm'_sub_one_pow_totient_prime_pow
  have hφ : (p ^ (k + 1)).totient ≠ 0 :=
    (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'
  have H' : ‖(ζ - 1) ^ (p ^ (k + 1)).totient‖ = ‖(p : PadicAlgCl p)‖ := by
    simpa only [norm_pow] using H
  have Hv : (p ^ (k + 1)).totient • padicAlgClRealValuation p (ζ - 1) = 1 := by
    rw [← AddValuation.map_pow, padicAlgClRealValuation,
      NormedRing.PseudoUniformizer.addValuation_apply]
    exact ((padicAlgClPseudoUniformizer p).logGauge_le_logGauge_iff.2 H'.ge).antisymm
      ((padicAlgClPseudoUniformizer p).logGauge_le_logGauge_iff.2 H'.le) |>.trans
      (by simpa only [coe_unit_padicAlgClPseudoUniformizer] using
        (padicAlgClPseudoUniformizer p).logGauge_unit)
  -- division in WithTop is avoided by extracting the finite value first
  have hfinite : padicAlgClRealValuation p (ζ - 1) ≠ ⊤ := by
    intro ht
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hφ
    rw [hm, succ_nsmul, ht, WithTop.add_top] at Hv
    exact WithTop.top_ne_coe Hv
  lift padicAlgClRealValuation p (ζ - 1) to ℝ using hfinite with a ha
  norm_cast at Hv ⊢
  rw [nsmul_eq_mul] at Hv
  apply (mul_left_cancel₀ (Nat.cast_ne_zero.2 hφ))
  rw [mul_inv_cancel₀ (Nat.cast_ne_zero.2 hφ)]
  exact Hv
end TauCeti
