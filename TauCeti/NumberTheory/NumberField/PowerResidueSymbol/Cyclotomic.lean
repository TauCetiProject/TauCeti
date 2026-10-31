/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Ideal

/-!
# Complex conjugation and the power residue symbol of a rational integer

Let `K` be the `n`-th cyclotomic field over `ℚ`, and let `σ` be complex conjugation, the
automorphism acting on the `n`-th roots of unity by `ζ ↦ ζ⁻¹`. Since `σ` fixes every rational
integer `m`, Galois equivariance of the power residue symbol shows that, for `m` prime to an
ideal `𝔞`, the symbol of `m` at the conjugate ideal `σ 𝔞` is the inverse of its symbol at `𝔞`:
`(m / σ 𝔞)_n (m / 𝔞)_n = 1`.

This is how conjugate ideals are paired off in the reciprocity laws involving rational integers:
for instance, the symbol of an integer `m` prime to `p` at a rational prime that splits as
`p = π (σ π)` is `1`.

## Main results

* `Ideal.powerResidueSymbolIdeal_map_intCast_mul_eq_one`: `(m / σ 𝔞)_n (m / 𝔞)_n = 1` for complex
  conjugation `σ` and an integer `m` prime to `𝔞`.

## References

* N. Xu, *Reciprocity Laws*, §5, proof of Proposition 5.10.
-/

public section

open NumberField IsCyclotomicExtension.Rat

namespace Ideal

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
  [HasEnoughRootsOfUnity (𝓞 K) n]

/-- **Complex conjugation inverts the symbol of a rational integer.** In the `n`-th cyclotomic
field, let `σ` be complex conjugation, the automorphism corresponding to `-1 ∈ (ZMod n)ˣ`. For an
integer `m` prime to an ideal `𝔞` of `𝓞 K`, the symbols of `m` at `𝔞` and at its conjugate `σ 𝔞`
are inverse `n`-th roots of unity: `(m / σ 𝔞)_n (m / 𝔞)_n = 1`. -/
theorem powerResidueSymbolIdeal_map_intCast_mul_eq_one {σ : Gal(K/ℚ)}
    (hσ : galEquivZMod n K σ = -1) (𝔞 : Ideal (𝓞 K)) {m : ℤ} (hm : IsUnit (m : 𝓞 K ⧸ 𝔞)) :
    powerResidueSymbolIdeal (𝔞.map (MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ)) n m *
      powerResidueSymbolIdeal 𝔞 n m = 1 := by
  set τ := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ
  have hx : powerResidueSymbolIdeal 𝔞 n m ^ n = 1 := powerResidueSymbolIdeal_pow_eq_one hm
  -- Galois equivariance, with `σ m = m`.
  have hmap := map_powerResidueSymbolIdeal (n := n) 𝔞 τ m
  rw [map_intCast τ, map_intCast (Quotient.mk 𝔞), map_intCast (Quotient.mk (𝔞.map τ))] at hmap
  -- `σ` raises every `n`-th root of unity to the power `n - 1`.
  have hτ : τ (powerResidueSymbolIdeal 𝔞 n m) = powerResidueSymbolIdeal 𝔞 n m ^ (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    have h := galEquivZMod_smul_of_pow_eq (k + 1) K σ hx
    rw [hσ, Units.val_neg, Units.val_one, ZMod.val_neg_one] at h
    exact h
  rw [← hmap, hτ, ← pow_succ, Nat.sub_add_cancel NeZero.one_le, hx]

end Ideal
