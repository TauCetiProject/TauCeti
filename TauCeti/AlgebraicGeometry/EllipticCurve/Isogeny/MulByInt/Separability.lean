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
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability

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

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5.4 and III.6.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- **`[n]` is separable exactly when `n` is nonzero in the base field** (Silverman III.5.4). -/
@[simp]
theorem isSeparable_mulByIntIsogeny_iff [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    Algebra.IsSeparable (mulByIntIsogeny W hn).fieldPullback.fieldRange W.FunctionField ↔
      (n : F) ≠ 0 := by
  rw [isSeparable_iff_pullbackDifferential_ne_zero, ← Hom.pullbackDifferential_ofIsogeny,
    ofIsogeny_mulByIntIsogeny, Hom.pullbackDifferential_zsmul_id_invariantDifferential, ne_eq,
    zsmul_invariantDifferential_eq_zero_iff]

/-- **A separable `[n]` has separable degree `n ²`**, its degree, since nothing is inseparable. -/
theorem separableDegree_mulByIntIsogeny [W.IsElliptic] {n : ℤ}
    {hn : psiFunctionField W n ≠ 0} (hchar : (n : F) ≠ 0) :
    (mulByIntIsogeny W hn).separableDegree = n.natAbs ^ 2 := by
  have := (isSeparable_mulByIntIsogeny_iff W hn).2 hchar
  rw [separableDegree_eq_degree_of_isSeparable, degree_mulByIntIsogeny]

end TauCeti.Isogeny

end
