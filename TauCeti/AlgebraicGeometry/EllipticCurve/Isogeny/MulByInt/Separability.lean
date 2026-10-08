/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Proof-only: the pullback of the invariant differential along `n • id`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential
-- Proof-only: `deg [n] = n ²`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
-- Proof-only: `[m] ∘ [n] = [m n]`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Comp
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.InvariantDifferential

/-!
# Separability of multiplication by `n`

Whether `[n]` is separable is decided by its differential, and `[n] = n • id` computes that: the
pullback of the invariant differential along `[n]` is `n • ω`, which vanishes exactly when `n`
does in the base field. In characteristic zero, and in characteristic `p` for `p ∤ n`, `[n]` is
therefore separable, and then nothing is inseparable in it, so its separable degree is its whole
degree `n ²`.

## Main results

* `TauCeti.Isogeny.isSeparable_mulByIntIsogeny_iff`: `[n]` is separable exactly when `n` is
  nonzero in the base field.
* `TauCeti.Isogeny.separableDegree_mulByIntIsogeny`: in that case its separable degree is `n ²`.
* `TauCeti.Isogeny.dvd_inseparableDegree_mulByIntIsogeny`: when `n` vanishes in the base field,
  the characteristic divides the inseparable degree of `[n]`.
* `TauCeti.Isogeny.inseparableDegree_mulByIntIsogenyOfNeZero_pow`: the inseparable degree of
  `[n ^ k]` is the `k`-th power of that of `[n]`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5.4 and III.6.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- **`[n]` scales the invariant differential by `n`**: the pullback of `ω` along `[n]` is `n • ω`.
This is the differential computation the separability criterion for `[n]` rests on. -/
theorem pullbackDifferential_mulByIntIsogeny_invariantDifferential [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).pullbackDifferential (invariantDifferential W) =
      n • invariantDifferential W := by
  rw [← Hom.pullbackDifferential_ofIsogeny, ofIsogeny_mulByIntIsogeny,
    Hom.pullbackDifferential_zsmul_id_invariantDifferential]

/-- **`[n]` is separable exactly when `n` is nonzero in the base field** (Silverman III.5.4). -/
@[simp]
theorem isSeparable_mulByIntIsogeny_iff [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    Algebra.IsSeparable (mulByIntIsogeny W hn).fieldPullback.fieldRange W.FunctionField ↔
      (n : F) ≠ 0 := by
  simp [isSeparable_iff_pullbackDifferential_ne_zero,
    pullbackDifferential_mulByIntIsogeny_invariantDifferential W hn,
    zsmul_invariantDifferential_eq_zero_iff]

/-- **A separable `[n]` has separable degree `n ²`**, its degree, since nothing is inseparable. -/
theorem separableDegree_mulByIntIsogeny [W.IsElliptic] {n : ℤ}
    {hn : psiFunctionField W n ≠ 0} (hchar : (n : F) ≠ 0) :
    (mulByIntIsogeny W hn).separableDegree = n.natAbs ^ 2 := by
  have := (isSeparable_mulByIntIsogeny_iff W hn).2 hchar
  rw [separableDegree_eq_degree_of_isSeparable, degree_mulByIntIsogeny]

/-- **The inseparable degree of `[n]` is divisible by the characteristic when `n` vanishes in the
base field.** -/
theorem dvd_inseparableDegree_mulByIntIsogeny [W.IsElliptic] (p : ℕ) [ExpChar F p] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (hchar : (n : F) = 0) :
    p ∣ (mulByIntIsogeny W hn).inseparableDegree := by
  -- `[n]` is inseparable, so its inseparable degree is a power of `p` other than `1`
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (mulByIntIsogeny W hn).inseparableDegree = p ^ r :=
    (mulByIntIsogeny W hn).inseparableDegree_def ▸ finInsepDegree_eq_pow _ _ p
  have hne : (mulByIntIsogeny W hn).inseparableDegree ≠ 1 := fun h ↦
    (isSeparable_mulByIntIsogeny_iff W hn).1
      ((inseparableDegree_eq_one_iff_isSeparable _).1 h) hchar
  rw [hr] at hne ⊢
  exact dvd_pow_self p fun h ↦ hne (by rw [h, pow_zero])

/-- **The inseparable degree of `[n ^ k]` is the `k`-th power of that of `[n]`.** -/
theorem inseparableDegree_mulByIntIsogenyOfNeZero_pow [W.IsElliptic] {n : ℤ} (hn : n ≠ 0)
    (k : ℕ) :
    (mulByIntIsogenyOfNeZero W (pow_ne_zero k hn)).inseparableDegree =
      (mulByIntIsogenyOfNeZero W hn).inseparableDegree ^ k := by
  induction k with
  | zero =>
    have h₁ : psiFunctionField W 1 ≠ 0 :=
      psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero one_ne_zero
    have e : mulByIntIsogenyOfNeZero W (pow_ne_zero 0 hn) = Isogeny.id W :=
      ((mulByIntIsogeny_inj W _ h₁).2 (pow_zero n)).trans (mulByIntIsogeny_one W h₁)
    rw [e, inseparableDegree_id, pow_zero]
  | succ k ih =>
    have e : mulByIntIsogenyOfNeZero W (pow_ne_zero (k + 1) hn) =
        mulByIntIsogenyOfNeZero W (mul_ne_zero (pow_ne_zero k hn) hn) :=
      (mulByIntIsogeny_inj W _ _).2 (pow_succ n k)
    rw [e, ← mulByIntIsogenyOfNeZero_comp_mulByIntIsogenyOfNeZero W (pow_ne_zero k hn) hn,
      inseparableDegree_comp, ih, pow_succ]

end TauCeti.Isogeny

end
