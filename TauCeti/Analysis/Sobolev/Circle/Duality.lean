/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Basic

/-!
# Duality between the circle Sobolev spaces `H^s` and `H^(-s)`

All the Fourier-coefficient Sobolev spaces `H^s` of the circle are isometric to `ℓ²(ℤ)`, so any
two of them are isometric: multiplying the `n`-th coefficient by `(1 + |n|) ^ (s - t)` is a linear
isometric equivalence `H^s ≃ H^t` (`TauCeti.CircleSobolev.weightEquiv`).

For `t = -s` this isometry realizes the duality between `H^s` and `H^(-s)` through the `L²`
pairing `∑ₙ ⟪aₙ, bₙ⟫`: the inner product of `H^(-s)` between the image of `a ∈ H^s` and
`b ∈ H^(-s)` is this pairing (`TauCeti.CircleSobolev.inner_weightEquiv_neg`). In particular, for
`s ≤ 0`, `a ∈ H⁰` and `b ∈ H^(-s)`, it is the inner product of `a` and `b` in `H⁰`
(`TauCeti.CircleSobolev.inner_weightEquiv_inclusion`). This is how an operator on a Sobolev space
`H^s` of negative order is obtained from the `L²` adjoint of an operator on `H^(-s)`, for instance
the action of a circle diffeomorphism on the Sobolev spaces of negative order.

## Main definitions

* `TauCeti.CircleSobolev.weightEquiv s t`: the linear isometric equivalence `H^s ≃ H^t`
  multiplying the `n`-th coefficient by `(1 + |n|) ^ (s - t)`.

## Main statements

* `TauCeti.CircleSobolev.coeff_weightEquiv`: the coefficients of `weightEquiv s t a`.
* `TauCeti.CircleSobolev.inner_weightEquiv_neg`: for `a ∈ H^s` and `b ∈ H^(-s)`, the inner product
  of `weightEquiv s (-s) a` and `b` in `H^(-s)` is `∑ₙ ⟪aₙ, bₙ⟫`.
* `TauCeti.CircleSobolev.inner_weightEquiv_inclusion`: for `s ≤ 0`, `a ∈ H⁰` and `b ∈ H^(-s)`, the
  same inner product is the inner product of `a` and `b` in `H⁰`.

## References

* M. E. Taylor, *Partial Differential Equations I*, Chapter 4, §1 (Sobolev spaces on the torus
  and the duality of `H^s` with `H^(-s)`).
-/

public section

noncomputable section

namespace TauCeti

namespace CircleSobolev

variable {s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (s t E) in
/-- **The isometry between two circle Sobolev spaces.** Multiplying the `n`-th Fourier coefficient
by `(1 + |n|) ^ (s - t)` is a linear isometric equivalence `H^s ≃ H^t`: both spaces are isometric
to `ℓ²(ℤ, E)` by their weights (`TauCeti.CircleSobolev.toℓ2ₗᵢ`). -/
def weightEquiv : CircleSobolev s E ≃ₗᵢ[ℂ] CircleSobolev t E :=
  toℓ2ₗᵢ.trans toℓ2ₗᵢ.symm

/-- The coefficients of `weightEquiv s t a` are `(1 + |n|) ^ (s - t) • aₙ`. -/
@[simp]
theorem coeff_weightEquiv (a : CircleSobolev s E) (n : ℤ) :
    (weightEquiv s t E a).coeff n = weight (s - t) n • a.coeff n := by
  simp only [weightEquiv, LinearIsometryEquiv.trans_apply, coe_toℓ2ₗᵢ, coe_toℓ2ₗᵢ_symm,
    toℓ2_symm_apply, coeff_ofℓ2, toℓ2_apply, smul_smul, sub_eq_neg_add, weight_add]

/-- The inverse of `weightEquiv s t` is `weightEquiv t s`. -/
@[simp]
theorem weightEquiv_symm : (weightEquiv s t E).symm = weightEquiv t s E :=
  (rfl)

/-- `weightEquiv s s` is the identity. -/
@[simp]
theorem weightEquiv_self (a : CircleSobolev s E) : weightEquiv s s E a = a :=
  CircleSobolev.ext <| funext fun n ↦ by simp

/-- `weightEquiv` composes along the orders. -/
@[simp]
theorem weightEquiv_weightEquiv {u : ℝ} (a : CircleSobolev s E) :
    weightEquiv t u E (weightEquiv s t E a) = weightEquiv s u E a :=
  CircleSobolev.ext <| funext fun n ↦ by
    rw [coeff_weightEquiv, coeff_weightEquiv, coeff_weightEquiv, smul_smul, ← weight_add]
    ring_nf

section Inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **The `L²` pairing of `H^s` with `H^(-s)`.** For `a ∈ H^s` and `b ∈ H^(-s)`, the inner product
of `weightEquiv s (-s) a` and `b` in `H^(-s)` is `∑ₙ ⟪aₙ, bₙ⟫`. -/
theorem inner_weightEquiv_neg (a : CircleSobolev s F) (b : CircleSobolev (-s) F) :
    inner ℂ (weightEquiv s (-s) F a) b = ∑' n, inner ℂ (a.coeff n) (b.coeff n) := by
  rw [inner_eq_tsum]
  refine tsum_congr fun n ↦ ?_
  rw [coeff_weightEquiv, ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, ← weight_add]
  ring_nf
  simp

/-- **The `L²` pairing on `H⁰`.** For `s ≤ 0`, `a ∈ H⁰` and `b ∈ H^(-s)`, the inner product of
`weightEquiv s (-s) a` and `b` in `H^(-s)` is the inner product of `a` and `b` in `H⁰`. -/
theorem inner_weightEquiv_inclusion (hs : s ≤ 0) (a : CircleSobolev 0 F)
    (b : CircleSobolev (-s) F) :
    inner ℂ (weightEquiv s (-s) F (inclusion hs a)) b =
      inner ℂ a (inclusion (neg_nonneg.2 hs) b) := by
  rw [inner_weightEquiv_neg, inner_eq_tsum]
  simp [coeff_inclusion]

end Inner

end CircleSobolev

end TauCeti
