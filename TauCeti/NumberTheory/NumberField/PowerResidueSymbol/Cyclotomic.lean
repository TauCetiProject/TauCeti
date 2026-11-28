/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootsOfUnity
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Ideal
import TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank
import TauCeti.RingTheory.Ideal.Span

/-!
# Power residue symbols in cyclotomic fields

Let `K` be the `n`-th cyclotomic field over `ℚ`. This file collects elementary properties of the
`n`-th power residue symbol specific to `𝓞 K`:

* Let `σ` be complex conjugation, the automorphism acting on the `n`-th roots of unity by
  `ζ ↦ ζ⁻¹`. Since `σ` fixes every rational integer `m`, Galois equivariance of the power residue
  symbol shows that, for `m` prime to an ideal `𝔞`, the symbol of `m` at the conjugate ideal `σ 𝔞`
  is the inverse of its symbol at `𝔞`: `(m / σ 𝔞)_n (m / 𝔞)_n = 1`. This is how conjugate ideals
  are paired off in the reciprocity laws involving rational integers: for instance, the symbol of
  an integer `m` prime to `p` at a rational prime that splits as `p = π (σ π)` is `1`.
* Since `absNorm (m 𝓞 K) = m ^ φ(n)`, evaluating `Ideal.powerResidueSymbolIdeal_mk_of_pow_eq_one`
  on a primitive `n`-th root of unity `ζ` gives `(ζ / a)_n = ζ ^ ((|a| ^ φ(n) - 1) / n)` for every
  natural number or rational integer `a` coprime to `n`.

## Main results

* `Ideal.powerResidueSymbolIdeal_pow_val_galEquivZMod`: `((α / 𝔞)_n) ^ c(σ) = (σ α / σ 𝔞)_n` for
  `n ≥ 2`, `σ ∈ Gal(K/ℚ)`, and any ideal `𝔞` and element `α ∈ 𝓞 K`.
* `Ideal.powerResidueSymbolIdeal_map_intCast_mul_eq_one`: `(m / σ 𝔞)_n (m / 𝔞)_n = 1` for complex
  conjugation `σ` and an integer `m` prime to `𝔞`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_natCast_mk_toInteger_of_coprime` and
  `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_toInteger_of_coprime`:
  `(ζ / a)_n = ζ ^ ((|a| ^ φ(n) - 1) / n)` for `a` coprime to `n`.

## References

* N. Xu, *Reciprocity Laws*, §5, proof of Proposition 5.10, and §6.
-/

public section

open NumberField IsCyclotomicExtension.Rat
open scoped Pointwise

namespace Ideal

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
  [HasEnoughRootsOfUnity (𝓞 K) n]

/-- **Galois action via the cyclotomic character.** In an `n`-th cyclotomic field over `ℚ` with
`n ≥ 2`, raising `(α / 𝔞)_n` to the representative `c(σ) ∈ [1, n)` of `σ ∈ Gal(K/ℚ)` in
`(ZMod n)ˣ` gives `(σ α / σ 𝔞)_n`, for every ideal `𝔞` of `𝓞 K` and every `α : 𝓞 K`. -/
theorem powerResidueSymbolIdeal_pow_val_galEquivZMod (𝔞 : Ideal (𝓞 K)) (hn : 2 ≤ n)
    (σ : Gal(K/ℚ)) (α : 𝓞 K) :
    powerResidueSymbolIdeal 𝔞 n (Quotient.mk 𝔞 α) ^ (galEquivZMod n K σ : ZMod n).val =
      powerResidueSymbolIdeal (σ • 𝔞) n (Quotient.mk (σ • 𝔞) (σ • α)) := by
  have : Fact (1 < n) := ⟨hn⟩
  let τ := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ
  have hτ_hom : (τ : 𝓞 K →+* 𝓞 K) = MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K) σ :=
    RingHom.ext (MulSemiringAction.toRingEquiv_apply_apply _ _ σ)
  have hτ𝔞 : 𝔞.map τ = σ • 𝔞 := by
    rw [← Ideal.map_coe, hτ_hom, Ideal.pointwise_smul_def]
  have hpow : powerResidueSymbolIdeal 𝔞 n (Quotient.mk 𝔞 α) ^ (galEquivZMod n K σ : ZMod n).val =
      τ (powerResidueSymbolIdeal 𝔞 n (Quotient.mk 𝔞 α)) := by
    rw [MulSemiringAction.toRingEquiv_apply_apply]
    rcases 𝔞.powerResidueSymbolIdeal_eq_zero_or_pow_eq_one (n := n) (Quotient.mk 𝔞 α) with h0 | h1
    · rw [h0, smul_zero, zero_pow ((ZMod.val_ne_zero _).mpr (Units.ne_zero _))]
    · exact (galEquivZMod_smul_of_pow_eq n K σ h1).symm
  rw [hpow, map_powerResidueSymbolIdeal 𝔞 τ α, MulSemiringAction.toRingEquiv_apply_apply, hτ𝔞]

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

namespace IsPrimitiveRoot

open Ideal

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {n} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ n)

/-- **The `n`-th power residue symbol of `ζ` at a natural number.** In the `n`-th cyclotomic
field `K`, for `m` coprime to `n`, the symbol of `ζ` at `m 𝓞 K` is
`ζ ^ ((m ^ φ(n) - 1) / n)`. -/
theorem powerResidueSymbolIdeal_span_natCast_mk_toInteger_of_coprime {m : ℕ} (hm : m.Coprime n) :
    powerResidueSymbolIdeal (span {(m : 𝓞 K)}) n (Ideal.Quotient.mk _ hζ.toInteger) =
      hζ.toInteger ^ ((m ^ n.totient - 1) / n) := by
  have hN : absNorm (span {(m : 𝓞 K)}) = m ^ n.totient := by
    rw [absNorm_span_natCast, finrank_ringOfIntegers n K]
  rw [powerResidueSymbolIdeal_mk_of_pow_eq_one (hN ▸ hm.pow_left _)
    hζ.toInteger_isPrimitiveRoot.pow_eq_one, hN]

/-- **The `n`-th power residue symbol of `ζ` at a rational integer.** In the `n`-th cyclotomic
field `K`, for an integer `a` with `|a|` coprime to `n`, the symbol of `ζ` at `a 𝓞 K` is
`ζ ^ ((|a| ^ φ(n) - 1) / n)`. -/
theorem powerResidueSymbolIdeal_span_intCast_mk_toInteger_of_coprime {a : ℤ}
    (ha : a.natAbs.Coprime n) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) n (Ideal.Quotient.mk _ hζ.toInteger) =
      hζ.toInteger ^ ((a.natAbs ^ n.totient - 1) / n) := by
  rw [span_singleton_intCast_eq_natAbs,
    hζ.powerResidueSymbolIdeal_span_natCast_mk_toInteger_of_coprime ha]

end IsPrimitiveRoot
