/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.NormNormalization
public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.RingTheory.RootsOfUnity.Ultrametric

/-!
# Values of the normalized valuation on the algebraic p-adic field

The existing `AddValuation.ofNorm` at base `p` is normalized by `v(p) = 1`. A primitive
`p ^ h`-th root of unity has `v(ζ - 1) = 1 / φ(p ^ h)` for every positive exponent `h`.

## Provenance

`PadicAlgCl.ofNorm_sub_one` adapts `New.Selmer.ellVal_sub_one_of_isPrimitiveRoot` in
`src/Lib/General/NumberTheory/GaussValuation.lean` and
`New.Selmer.ellVal_sub_one_eq_rootRadius` in
`src/New/Congruences/Selmer/RootsOfUnity.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The primitive-root formula uses the existing norm formula
and the untruncated base-`p` valuation.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Chapters 1–2.
-/

public section

noncomputable section
namespace PadicAlgCl

variable (p : ℕ) [Fact p.Prime]

/-- The base-`p` additive valuation of `p` is one. -/
@[simp]
theorem ofNorm_p :
    AddValuation.ofNorm (p : ℝ) (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
      (p : PadicAlgCl p) = 1 := by
  rw [← WithTop.coe_one, AddValuation.ofNorm_eq_coe_iff, Real.rpow_neg_one,
    ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_extends, Padic.norm_p]

/-- The base-`p` additive valuation of a primitive `p ^ h`-th root minus one is `1 / φ(p ^ h)`
for `h ≥ 1`. -/
theorem ofNorm_sub_one {h : ℕ} (hh : 1 ≤ h) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ h)) :
    AddValuation.ofNorm (p : ℝ) (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
      (ζ - 1) = ((Nat.totient (p ^ h) : ℝ)⁻¹ : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hh
  have hφ := Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos (k + 1))
  rw [AddValuation.ofNorm_eq_coe_iff,
    ← Real.pow_rpow_inv_natCast (norm_nonneg (ζ - 1)) hφ.ne',
    hζ.norm'_sub_one_pow_totient_prime_pow,
    ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_extends, Padic.norm_p,
    Real.inv_rpow (Nat.cast_nonneg p), ← Real.rpow_neg (Nat.cast_nonneg p)]

end PadicAlgCl
