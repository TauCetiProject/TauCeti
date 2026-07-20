/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.LegendreSymbol.Frobenius

/-!
# The Frobenius of a multiquadratic field is the Legendre sign vector

Let `K = ℚ(√d₁, …, √dₙ)` be a number field generated over `ℚ` by square roots `r i` of
integers `d i`, and let `p` be an odd prime dividing none of the `d i`. The multiquadratic
roadmap's Layer 1 states the splitting law in two forms: `p` splits completely iff every `d i`
is a quadratic residue mod `p` (`TauCeti.NumberField.ncard_primesOver_multiquadratic_iff`), and
more precisely, the Frobenius at `p` is the sign vector `((d₁/p), …, (dₙ/p))` on the
generators. This file supplies the second, finer form: an arithmetic Frobenius `σ` at a prime
`Q` of `𝓞 K` above `p` (Mathlib's `IsArithFrobAt`) acts on each generator by the corresponding
Legendre symbol,

`σ (r i) = legendreSym p (d i) • r i`,

and, when the `r i` generate `K`, the Frobenius is trivial iff every symbol is `1`. Since an
automorphism of a multiquadratic field is determined by its signs on the generators (the
sign-pattern injectivity of `TauCeti.NumberTheory.Multiquadratic.Galois.Group`), this pins the
Frobenius down completely: under the identification `Gal(K/ℚ) ≅ (ℤ/2)ⁿ` it is exactly the
vector of Legendre symbols.

The local computation `φ √d = (d/p)·√d` is
`TauCeti.AlgHom.IsArithFrobAt.apply_sqrt`; this file transports it along the Galois action on
the ring of integers.

## Main results

* `TauCeti.NumberField.isArithFrobAt_apply_sqrt`: an arithmetic Frobenius at `Q ∣ p` sends
  each generator `r i` to `legendreSym p (d i) • r i`.
* `TauCeti.NumberField.isArithFrobAt_eq_one_iff`: the Frobenius is the identity iff every
  `d i` is a quadratic residue mod `p`.
-/

public section

open NumberField Ideal

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

omit [NumberField K] in
/-- A square root of an integer is an algebraic integer: it is a root of the monic `X² - d`.
Kept private; it only feeds the subtype packaging below. -/
private theorem isIntegral_of_sq_intCast {x : K} {d : ℤ}
    (hx : x ^ 2 = algebraMap ℤ K d) : IsIntegral ℤ x :=
  ⟨Polynomial.X ^ 2 - Polynomial.C d,
    Polynomial.monic_X_pow_sub_C d (by norm_num), by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hx, sub_self]⟩

/-- **The Frobenius acts on multiquadratic generators by the Legendre symbols.** Let `K` be a
number field with elements `r i` satisfying `r i ² = d i ∈ ℤ`, let `p` be an odd prime, and let
`σ ∈ Gal(K/ℚ)` be an arithmetic Frobenius at a prime `Q` of `𝓞 K` above `p`. Then for every
`i` with `p ∤ d i`,

`σ (r i) = legendreSym p (d i) • r i`.

Under the identification of the multiquadratic Galois group with `(ℤ/2)ⁿ` by sign patterns,
this says the Frobenius at `p` is the vector of Legendre symbols `((d₁/p), …, (dₙ/p))`. -/
theorem isArithFrobAt_apply_sqrt (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q)
    {i : ι} (hd : ¬ (p : ℤ) ∣ d i) :
    σ (r i) = legendreSym p (d i) • r i := by
  -- Package the generator as an algebraic integer and apply the local computation in `𝓞 K`.
  set x : 𝓞 K := ⟨r i, isIntegral_of_sq_intCast (hr i)⟩ with hxdef
  have hxsq : x ^ 2 = algebraMap ℤ (𝓞 K) (d i) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [map_pow, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
    exact hr i
  have hsmul : σ • x = legendreSym p (d i) • x :=
    TauCeti.IsArithFrobAt.smul_sqrt hσ hodd hd hxsq
  -- Push the identity from `𝓞 K` down to `K` along the coercion.
  have hcoe := congrArg (algebraMap (𝓞 K) K) hsmul
  rw [map_zsmul] at hcoe
  calc σ (r i) = algebraMap (𝓞 K) K (σ • x) := (integralClosure.coe_smul σ x).symm
    _ = legendreSym p (d i) • algebraMap (𝓞 K) K x := hcoe
    _ = legendreSym p (d i) • r i := rfl

/-- **The Frobenius is trivial iff every radicand is a residue.** Let `K = ℚ(√d₁, …, √dₙ)` be
generated over `ℚ` by the square roots `r i` of the integers `d i`, let `p` be an odd prime
with `p ∤ d i` for all `i`, and let `σ` be an arithmetic Frobenius at a prime `Q` of `𝓞 K`
above `p`. Then `σ = 1` iff every `d i` is a quadratic residue mod `p`. Combined with the
splitting law, this is the Frobenius-theoretic reading of complete splitting. -/
theorem isArithFrobAt_eq_one_iff (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ = 1 ↔ ∀ i, legendreSym p (d i) = 1 := by
  constructor
  · rintro rfl i
    -- The identity fixes `r i`, so the symbol cannot be `-1`: that would force `r i = -r i`.
    have hfix : r i = legendreSym p (d i) • r i := by
      simpa using isArithFrobAt_apply_sqrt d r hr hodd Q hσ (hcop i)
    have hne : r i ≠ 0 := by
      intro h0
      apply hcop i
      have : algebraMap ℤ K (d i) = 0 := by rw [← hr i, h0]; ring
      have hdi : d i = 0 := by
        rw [eq_intCast] at this
        exact_mod_cast this
      simp [hdi]
    rcases legendreSym.eq_one_or_neg_one p (a := d i) (by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop i) with h1 | h1
    · exact h1
    · exfalso
      rw [h1, neg_smul, one_smul] at hfix
      apply hne
      have h2 : (2 : K) * r i = 0 := by linear_combination hfix
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h two_ne_zero
      · exact h
  · intro hqr
    -- `σ` fixes each generator, and the generators generate `K` over `ℚ`.
    have hfix : ∀ i, σ (r i) = r i := fun i => by
      rw [isArithFrobAt_apply_sqrt d r hr hodd Q hσ (hcop i), hqr i, one_smul]
    refine AlgEquiv.ext fun y => ?_
    rw [AlgEquiv.one_apply]
    have hy : y ∈ (⊤ : IntermediateField ℚ K) := IntermediateField.mem_top
    rw [← htop] at hy
    induction hy using IntermediateField.adjoin_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hfix i
    | algebraMap q => exact AlgEquiv.commutes σ q
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | inv a _ ha => rw [map_inv₀, ha]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]

end TauCeti.NumberField
