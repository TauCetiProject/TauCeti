/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Dual
public import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
-- Proof-only: `[m] = [n]` only if `m = n`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Comp
-- Proof-only: supersingularity and ordinarity read off the separable degree of `[p ^ k]`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular

/-!
# Supersingularity and the dual of Frobenius over a finite field

Let `W` be an elliptic curve over a finite field `F` with `q = p ^ f` elements, `π = π_q` its
Frobenius endomorphism and `π̂` the dual of `π`. This file proves that `W` is supersingular exactly
when `π̂` is purely inseparable, and ordinary exactly when `π̂` is separable (Silverman V.3.1(b),
for the `q`-power Frobenius).

Since `π̂ ∘ π = [q]` and `π` is purely inseparable, `π̂` carries the whole separable degree of
`[q] = [p ^ f]`. That separable degree is `1` on a supersingular curve and `q` on an ordinary one,
while `deg π̂ = q`.

Over a finite field this is the step between the geometric definition of supersingularity and
the trace criterion `p ∣ a_q` (Silverman V.4.1(a)), which follows once `π + π̂ = [a_q]` identifies
the pullback of the invariant differential along `π̂` with `a_q` times it.

## Main results

* `WeierstrassCurve.isSupersingular_iff_isPurelyInseparable_dualFrobeniusIsogeny`: `W` is
  supersingular exactly when `π̂` is purely inseparable.
* `WeierstrassCurve.isOrdinary_iff_isSeparable_dualFrobeniusIsogeny`: `W` is ordinary exactly
  when `π̂` is separable.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.1 and V.3.1.
-/

public section

open TauCeti.Isogeny

namespace WeierstrassCurve

variable {F : Type*} [Field F] [Finite F] (p : ℕ) [ExpChar F p] (W : WeierstrassCurve F)
  [W.IsElliptic]

/-- Over a finite field of exponential characteristic `p`, the characteristic `p` is prime,
`#F = p ^ f` with `f ≠ 0`, and the dual of Frobenius has the separable degree of `[p ^ f]`. -/
private theorem exists_separableDegree_dualFrobeniusIsogeny_eq :
    p.Prime ∧ ∃ f : ℕ, f ≠ 0 ∧ Nat.card F = p ^ f ∧
      (dualFrobeniusIsogeny W.toAffine).separableDegree = (mulByIntIsogenyOfNeZero W.toAffine
        (pow_ne_zero f (mod_cast expChar_ne_zero F p : (p : ℤ) ≠ 0))).separableDegree := by
  -- a finite field has prime characteristic, so `p` is that characteristic
  rcases expChar_is_prime_or_one F p with hp | rfl
  · have := (expChar_prime_iff (R := F) hp).1 ‹ExpChar F p›
    let _ := Fintype.ofFinite F
    obtain ⟨f, -, hq⟩ := FiniteField.card F p
    rw [← Nat.card_eq_fintype_card] at hq
    refine ⟨hp, f, f.ne_zero, hq, ?_⟩
    rw [separableDegree_dualFrobeniusIsogeny]
    congr 1
    exact (mulByIntIsogeny_inj W.toAffine _ _).2 (by rw [hq, Nat.cast_pow])
  · have := charZero_of_expChar_one' F
    have : Infinite F := .of_injective _ (Nat.cast_injective (R := F))
    exact (not_finite F).elim

/-- **Supersingularity is pure inseparability of the dual of Frobenius**: an elliptic curve over a
finite field of characteristic `p` is supersingular exactly when `π̂ = π̂_q` is purely inseparable
(Silverman V.3.1(b)). -/
theorem isSupersingular_iff_isPurelyInseparable_dualFrobeniusIsogeny :
    W.IsSupersingular p ↔ IsPurelyInseparable
      (dualFrobeniusIsogeny W.toAffine).fieldPullback.fieldRange W.toAffine.FunctionField := by
  obtain ⟨-, f, hf, -, h⟩ := exists_separableDegree_dualFrobeniusIsogeny_eq p W
  rw [← separableDegree_eq_one_iff_isPurelyInseparable, h,
    isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_pow_eq_one p W hf]

/-- **Ordinarity is separability of the dual of Frobenius**: an elliptic curve over a finite
field of characteristic `p` is ordinary exactly when `π̂ = π̂_q` is separable
(Silverman V.3.1(b)). -/
theorem isOrdinary_iff_isSeparable_dualFrobeniusIsogeny :
    W.IsOrdinary p ↔ Algebra.IsSeparable
      (dualFrobeniusIsogeny W.toAffine).fieldPullback.fieldRange W.toAffine.FunctionField := by
  obtain ⟨hp, f, hf, hq, h⟩ := exists_separableDegree_dualFrobeniusIsogeny_eq p W
  rw [← separableDegree_eq_degree_iff_isSeparable, h, degree_dualFrobeniusIsogeny, hq,
    isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_pow_eq p W hp hf]

end WeierstrassCurve

end
