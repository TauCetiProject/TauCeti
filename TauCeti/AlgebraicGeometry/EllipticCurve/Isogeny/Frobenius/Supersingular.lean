/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Dual
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
-- Proof-only: the Hasse bound `a_q² ≤ 4q`.
import TauCeti.AlgebraicGeometry.EllipticCurve.HasseBound
-- Proof-only: `π̂ = a_q - π`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Charpoly
-- Proof-only: `π` kills the differentials.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Differential
-- Proof-only: the pullback of `ω` is additive in the morphism.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential
-- Proof-only: `[m] = [n]` only if `m = n`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Comp
-- Proof-only: supersingularity and ordinarity read off the separable degree of `[p ^ k]`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular

/-!
# Supersingularity over a finite field

Let `W` be an elliptic curve over a finite field `F` with `q = p ^ f` elements, `π = π_q` its
Frobenius endomorphism, `π̂` the dual of `π` and `a_q = q + 1 - #W(F)` the trace of Frobenius. This
file proves that `W` is supersingular exactly when `π̂` is purely inseparable, and ordinary exactly
when `π̂` is separable (Silverman V.3.1(b), for the `q`-power Frobenius). It then proves the trace
criterion: `W` is supersingular exactly when `p ∣ a_q`, equivalently `#W(F) ≡ 1 (mod p)`
(Silverman V.4.1(a)). Over a prime field `𝔽_p` with `p ≥ 5`, the Hasse bound `a_p² ≤ 4p` sharpens
this to `a_p = 0`, that is `#W(𝔽_p) = p + 1` (Silverman V.4.1(b)). The sharpening fails for
`p = 2, 3` and over non-prime fields, where supersingular curves with `a_q ≠ 0` exist, so the
divisibility is the criterion in general.

Since `π̂ ∘ π = [q]` and `π` is purely inseparable, `π̂` carries the whole separable degree of
`[q] = [p ^ f]`. That separable degree is `1` on a supersingular curve and `q` on an ordinary one,
while `deg π̂ = q`. The identity `π + π̂ = [a_q]` and `π^*ω = 0` give `π̂^*ω = a_q ω` for the
invariant differential `ω`, so `π̂` is separable exactly when `a_q` is nonzero in `F`.

## Main results

* `WeierstrassCurve.isSupersingular_iff_isPurelyInseparable_dualFrobeniusIsogeny`: `W` is
  supersingular exactly when `π̂` is purely inseparable.
* `WeierstrassCurve.isOrdinary_iff_isSeparable_dualFrobeniusIsogeny`: `W` is ordinary exactly
  when `π̂` is separable.
* `TauCeti.Isogeny.pullbackDifferential_dualFrobeniusIsogeny_invariantDifferential`:
  `π̂^*ω = a_q ω`.
* `WeierstrassCurve.isSupersingular_iff_dvd_frobeniusTrace` and
  `WeierstrassCurve.isOrdinary_iff_not_dvd_frobeniusTrace`: `W` is supersingular exactly when
  `p ∣ a_q`.
* `WeierstrassCurve.isSupersingular_iff_card_point_modEq_one`: `W` is supersingular exactly when
  `#W(F) ≡ 1 (mod p)`.
* `WeierstrassCurve.isSupersingular_iff_frobeniusTrace_eq_zero` and
  `WeierstrassCurve.isSupersingular_iff_card_point_eq`: over `𝔽_p` with `p ≥ 5`, `W` is
  supersingular exactly when `a_p = 0`, that is `#W(𝔽_p) = p + 1`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5.2, III.6.1, V.3.1 and
  V.4.1.
-/

public section

open TauCeti.Isogeny

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **The dual of Frobenius pulls the invariant differential back to `a_q ω`**, where `a_q` is the
trace of Frobenius. In particular `π̂` is separable exactly when `a_q` is nonzero in `F`. -/
@[simp]
theorem pullbackDifferential_dualFrobeniusIsogeny_invariantDifferential :
    (dualFrobeniusIsogeny W).pullbackDifferential (invariantDifferential W) =
      W.frobeniusTrace • invariantDifferential W := by
  rw [← Hom.pullbackDifferential_ofIsogeny, ofIsogeny_dualFrobeniusIsogeny,
    Hom.pullbackDifferential_sub_invariantDifferential,
    Hom.pullbackDifferential_zsmul_id_invariantDifferential, Hom.pullbackDifferential_ofIsogeny,
    pullbackDifferential_frobeniusIsogeny, LinearMap.zero_apply, sub_zero]

end TauCeti.Isogeny

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

/-- **The trace criterion for ordinarity**: an elliptic curve over a finite field of
characteristic `p` is ordinary exactly when `p` does not divide its trace of Frobenius `a_q`
(Silverman V.4.1(a)). -/
theorem isOrdinary_iff_not_dvd_frobeniusTrace :
    W.IsOrdinary p ↔ ¬(p : ℤ) ∣ W.frobeniusTrace := by
  have : CharP F p :=
    (expChar_prime_iff (R := F) (exists_separableDegree_dualFrobeniusIsogeny_eq p W).1).1 ‹_›
  -- `π̂` is separable exactly when it does not kill `ω`, and `π̂^*ω = a_q ω`
  rw [isOrdinary_iff_isSeparable_dualFrobeniusIsogeny, isSeparable_iff_pullbackDifferential_ne_zero,
    pullbackDifferential_dualFrobeniusIsogeny_invariantDifferential, Ne,
    Affine.zsmul_invariantDifferential_eq_zero_iff, CharP.intCast_eq_zero_iff F p]

/-- **The trace criterion for supersingularity**: an elliptic curve over a finite field of
characteristic `p` is supersingular exactly when `p` divides its trace of Frobenius `a_q`
(Silverman V.4.1(a)). -/
theorem isSupersingular_iff_dvd_frobeniusTrace :
    W.IsSupersingular p ↔ (p : ℤ) ∣ W.frobeniusTrace := by
  rw [← not_isOrdinary, isOrdinary_iff_not_dvd_frobeniusTrace, not_not]

/-- **Supersingularity by point count**: an elliptic curve over a finite field of characteristic
`p` is supersingular exactly when its number of points, the point at infinity included, is
`1` modulo `p` (Silverman V.4.1(a)). -/
theorem isSupersingular_iff_card_point_modEq_one :
    W.IsSupersingular p ↔ Nat.card W.toAffine.Point ≡ 1 [MOD p] := by
  obtain ⟨-, f, hf, hq, -⟩ := exists_separableDegree_dualFrobeniusIsogeny_eq p W
  -- `a_q = q + (1 - #W(F))` and `p ∣ q`
  have hpq : (p : ℤ) ∣ Nat.card F := by
    rw [hq, Nat.cast_pow]
    exact dvd_pow_self _ hf
  rw [isSupersingular_iff_dvd_frobeniusTrace, frobeniusTrace_eq_card_point, add_sub_assoc,
    dvd_add_right hpq, ← Int.natCast_modEq_iff, Int.modEq_iff_dvd, Nat.cast_one]

/-- **Over `𝔽_p` with `p ≥ 5`, supersingularity is the vanishing of the trace**: an elliptic curve
over a field with `p ≥ 5` elements, `p` its characteristic, is supersingular exactly when its trace
of Frobenius `a_p` is `0` (Silverman V.4.1(b)). For `p = 2, 3`, and over fields that are not prime,
`isSupersingular_iff_dvd_frobeniusTrace` is the criterion. -/
theorem isSupersingular_iff_frobeniusTrace_eq_zero (hq : Nat.card F = p) (hp : 5 ≤ p) :
    W.IsSupersingular p ↔ W.frobeniusTrace = 0 := by
  refine (isSupersingular_iff_dvd_frobeniusTrace p W).trans
    ⟨fun ⟨k, hk⟩ ↦ ?_, fun h ↦ h ▸ dvd_zero _⟩
  have hHasse := W.frobeniusTrace_sq_le_four_mul_card
  rw [hk, hq] at hHasse
  rw [hk, mul_eq_zero, Int.natCast_eq_zero]
  right
  -- `p² k² ≤ 4 p` gives `p k² ≤ 4`, which `p ≥ 5` and `k² ≥ 1` contradict
  by_contra hk0
  have hp' : (5 : ℤ) ≤ p := mod_cast hp
  have hpk : p * k ^ 2 ≤ 4 := le_of_mul_le_mul_left (by linarith [hHasse]) (by omega : (0 : ℤ) < p)
  nlinarith [sq_abs k, Int.one_le_abs hk0]

/-- **Over `𝔽_p` with `p ≥ 5`, a curve is supersingular exactly when it has `p + 1` points**, the
point at infinity included (Silverman V.4.1(b)). -/
theorem isSupersingular_iff_card_point_eq (hq : Nat.card F = p) (hp : 5 ≤ p) :
    W.IsSupersingular p ↔ Nat.card W.toAffine.Point = p + 1 := by
  rw [isSupersingular_iff_frobeniusTrace_eq_zero p W hq hp, frobeniusTrace_eq_card_point, hq,
    sub_eq_zero, eq_comm]
  norm_cast

end WeierstrassCurve

end
