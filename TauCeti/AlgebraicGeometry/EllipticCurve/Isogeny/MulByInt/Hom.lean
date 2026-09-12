/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability

/-!
# Multiplication by `n` is `n` times the identity

`[n]` is built from the division polynomials, while the additive group of morphisms is built from
tautological points; this file says the two agree, so that results about the additive structure
apply to `[n]` and results about `[n]` are available additively.

## Main results

* `TauCeti.Isogeny.ofIsogeny_mulByIntIsogeny`: `[n] = n • id` in `Hom W W`.
* `TauCeti.Isogeny.isSeparable_mulByIntIsogeny_iff`: `[n]` is separable exactly when `n` is
  nonzero in the base field.
* `TauCeti.Isogeny.separableDegree_mulByIntIsogeny`: in that case its separable degree is `n ²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- **`[n]` is `n` times the identity** in the additive group of morphisms. The division-polynomial
construction of `[n]` and the additive structure on `Hom` therefore describe the same map. -/
@[simp]
theorem ofIsogeny_mulByIntIsogeny [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    Hom.ofIsogeny (mulByIntIsogeny W hn) = n • Hom.id W := by
  refine Hom.ext_tautologicalPoint ?_
  simp [Hom.id_def, mulByIntIsogeny_pullback, tautologicalPoint_mulByIntPullback]

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
    (hn : psiFunctionField W n ≠ 0) (hchar : (n : F) ≠ 0) :
    (mulByIntIsogeny W hn).separableDegree = n.natAbs ^ 2 := by
  have := (isSeparable_mulByIntIsogeny_iff W hn).2 hchar
  rw [separableDegree_eq_degree_of_isSeparable, degree_mulByIntIsogeny]

end TauCeti.Isogeny

end
