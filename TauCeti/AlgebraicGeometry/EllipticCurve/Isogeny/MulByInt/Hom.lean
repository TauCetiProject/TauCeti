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

/-!
# Multiplication by `n` is `n` times the identity

`[n]` is built from the division polynomials, while the additive group of morphisms is built from
tautological points; this file says the two agree, so that results about the additive structure
apply to `[n]` and results about `[n]` are available additively.

Read additively, the degree of `[n]` says that the degree **scales quadratically**,
`deg (n • f) = n² · deg f`, for every morphism and not just for a multiplication: that is the
homogeneity half of the statement that the degree is a quadratic form on `Hom W₁ W₂`, the form
whose non-negativity gives the Hasse bound. The other half, that the associated pairing is
additive, is not proved here.

## Main results

* `TauCeti.Isogeny.ofIsogeny_mulByIntIsogeny`: `[n] = n • id` in `Hom W W`.
* `TauCeti.Isogeny.isSeparable_mulByIntIsogeny_iff`: `[n]` is separable exactly when `n` is
  nonzero in the base field.
* `TauCeti.Isogeny.Hom.degree_zsmul` and `TauCeti.Isogeny.Hom.degree_nsmul`:
  `deg (n • f) = n² · deg f`, the degree's homogeneity, for an integer and a natural scalar.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 for the identification
  of `[n]` with `n • id`, III.6 for the degree as a quadratic form, of which `Hom.degree_zsmul` is
  the homogeneity.
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
variable {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The degree scales quadratically**: `deg (n • f) = n² · deg f`.

This is the homogeneity half of the degree being a quadratic form on `Hom W₁ W₂`. It holds with no
hypothesis on `n` or `f`: at `n = 0` and at `f = 0` both sides are `0`, which is what the value
`Hom.degree 0 = 0` is stipulated for. -/
@[simp]
theorem Hom.degree_zsmul [W₂.IsElliptic] (n : ℤ) (f : Hom W₁ W₂) :
    (n • f).degree = n.natAbs ^ 2 * f.degree := by
  have hcomp : n • f = (n • Hom.id W₂).comp f := by rw [Hom.zsmul_comp, Hom.id_comp]
  have hid : (n • Hom.id W₂).degree = n.natAbs ^ 2 := by
    rcases eq_or_ne n 0 with rfl | hn
    · rw [zero_smul, Hom.degree_zero, Int.natAbs_zero, Nat.zero_pow two_pos]
    · rw [← ofIsogeny_mulByIntIsogeny W₂
        (psiFunctionField_ne_zero_of_Δ_ne_zero W₂ W₂.isUnit_Δ.ne_zero hn),
        Hom.degree_ofIsogeny, degree_mulByIntIsogeny]
  rw [hcomp, Hom.degree_comp, hid]

/-- **The degree scales quadratically for a natural multiple**: `deg (n • f) = n² · deg f`. -/
@[simp]
theorem Hom.degree_nsmul [W₂.IsElliptic] (n : ℕ) (f : Hom W₁ W₂) :
    (n • f).degree = n ^ 2 * f.degree := by
  rw [← natCast_zsmul f n, Hom.degree_zsmul, Int.natAbs_natCast]

end TauCeti.Isogeny

end
