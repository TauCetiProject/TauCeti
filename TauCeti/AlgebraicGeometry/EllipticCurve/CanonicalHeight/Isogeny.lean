/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Limit
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.XRatFunc
import Mathlib.Algebra.Polynomial.Homogenize

/-!
# The canonical height along an isogeny

For a morphism `f : W₁ → W₂` of elliptic curves over a field with a theory of heights, the
canonical height scales by the degree:

  `canonicalHeight (f P) = deg f · canonicalHeight P`.

The proof has two halves. First, a nonzero `f` is an isogeny `φ`, which acts on the `x`-line
through the rational function `φ.xRatFunc` of degree `deg f`
(`TauCeti.Isogeny.degree_eq_max_natDegree_xRatFunc`), so homogenising its numerator and
denominator in degree `deg f` gives a pair of binary forms computing `x(f P)` from `x(P)`.
Mathlib's upper bound for heights of values of homogeneous polynomial maps then gives
`h(f P) ≤ deg f · h(P) + C`, and averaging along multiples gives
`canonicalHeight (f P) ≤ deg f · canonicalHeight P`. Second, the same inequality for the dual
`f̂`, whose composite with `f` is multiplication by `deg f`, gives
`(deg f)² canonicalHeight P = canonicalHeight (f̂ (f P)) ≤ deg f · canonicalHeight (f P)`, the
reverse inequality.

## Main results

* `TauCeti.Isogeny.Hom.exists_naiveHeight_pointMap_le`: `h(f P) ≤ deg f · h(P) + C`.
* `TauCeti.Isogeny.Hom.canonicalHeight_pointMap`:
  `canonicalHeight (f P) = deg f · canonicalHeight P`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.5.6 (heights along a
  morphism of projective spaces, whose upper bound is Mathlib's `Height.logHeight_eval_le'`) and
  VIII.9 (the canonical height).
-/

public section

open Filter Height Polynomial Topology WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F : Type*} [Field F] [AdmissibleAbsValues F] [DecidableEq F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The naïve height grows at most by the degree** along a morphism `f`:
`h(f P) ≤ deg f · h(P) + C` for a constant `C` depending only on `f`. -/
theorem exists_naiveHeight_pointMap_le (f : Hom W₁ W₂) :
    ∃ C, ∀ P : W₁.Point, (f.pointMap P).naiveHeight ≤ f.degree * P.naiveHeight + C := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · exact ⟨0, fun P ↦ by simp⟩
  have hnum : φ.xRatFunc.num.natDegree ≤ φ.degree :=
    φ.degree_eq_max_natDegree_xRatFunc ▸ le_max_left _ _
  have hden : φ.xRatFunc.denom.natDegree ≤ φ.degree :=
    φ.degree_eq_max_natDegree_xRatFunc ▸ le_max_right _ _
  -- the binary forms of degree `deg φ` computing `x(φ P)` from `x(P)`
  let p : Fin 2 → MvPolynomial (Fin 2) F :=
    ![φ.xRatFunc.num.homogenize φ.degree, φ.xRatFunc.denom.homogenize φ.degree]
  have hp (i : Fin 2) : (p i).IsHomogeneous φ.degree := by
    fin_cases i <;> exact isHomogeneous_homogenize _
  obtain ⟨C, hC⟩ := logHeight_eval_le' hp
  refine ⟨max C 0, fun P ↦ ?_⟩
  rw [degree_ofIsogeny]
  have hP := P.naiveHeight_nonneg
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, pointMap_zero, Point.naiveHeight_zero]
    positivity
  by_cases hd : φ.xRatFunc.denom.eval x = 0
  · rw [(pointMap_ofIsogeny_some_eq_zero_iff h).mpr hd, Point.naiveHeight_zero]
    positivity
  have hne := (pointMap_ofIsogeny_some_eq_zero_iff h).not.mpr hd
  have heval :
      (fun j ↦ (p j).eval ![x, 1]) = ![φ.xRatFunc.num.eval x, φ.xRatFunc.denom.eval x] := by
    ext j
    fin_cases j <;> simp [p, eval_homogenize hnum, eval_homogenize hden]
  have hrep : ((ofIsogeny φ).pointMap (.some x y h)).xRep =
      (φ.xRatFunc.denom.eval x)⁻¹ • ![φ.xRatFunc.num.eval x, φ.xRatFunc.denom.eval x] := by
    rw [← Point.some_coords hne, Point.xRep_some, xCoord_pointMap_ofIsogeny_some h hd]
    ext j
    fin_cases j <;> simp [div_eq_inv_mul, hd]
  have hx := hC ![x, 1]
  rw [heval] at hx
  rw [Point.naiveHeight_eq_logHeight, hrep, logHeight_smul_eq_logHeight _ (inv_ne_zero hd),
    Point.naiveHeight_eq_logHeight, Point.xRep_some]
  linarith [le_max_left C 0]

/-- **The canonical height grows at most by the degree**:
`canonicalHeight (f P) ≤ deg f · canonicalHeight P`, the naïve bound divided by `n²` along the
multiples `n • P`. -/
private theorem canonicalHeight_pointMap_le (f : Hom W₁ W₂) (P : W₁.Point) :
    (f.pointMap P).canonicalHeight ≤ f.degree * P.canonicalHeight := by
  obtain ⟨C, hC⟩ := f.exists_naiveHeight_pointMap_le
  have hlim : Tendsto (fun n : ℕ ↦ f.degree * ((n • P).naiveHeight / (n : ℝ) ^ 2) + C / (n : ℝ) ^ 2)
      atTop (𝓝 (f.degree * P.canonicalHeight + 0)) :=
    (P.tendsto_naiveHeight_nsmul_div_sq.const_mul _).add (tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop))
  rw [add_zero] at hlim
  refine le_of_tendsto_of_tendsto' (f.pointMap P).tendsto_naiveHeight_nsmul_div_sq hlim fun n ↦ ?_
  rw [← pointMap_nsmul, mul_div_assoc', ← add_div]
  exact div_le_div_of_nonneg_right (hC (n • P)) (sq_nonneg _)

/-- **The canonical height scales by the degree along a morphism**:
`canonicalHeight (f P) = deg f · canonicalHeight P`. This includes the zero morphism, which has
degree `0` and sends every point to `O`. -/
theorem canonicalHeight_pointMap (f : Hom W₁ W₂) (P : W₁.Point) :
    (f.pointMap P).canonicalHeight = f.degree * P.canonicalHeight := by
  have h₁ := canonicalHeight_pointMap_le f P
  have h₂ := canonicalHeight_pointMap_le f.dual (f.pointMap P)
  rw [degree_dual, ← comp_pointMap, dual_comp_self, nsmul_pointMap, id_pointMap,
    Point.canonicalHeight_nsmul] at h₂
  rcases Nat.eq_zero_or_pos f.degree with hd | hd
  · rw [degree_eq_zero_iff] at hd
    subst hd
    simp
  have hd' : (0 : ℝ) < f.degree := Nat.cast_pos.mpr hd
  refine le_antisymm h₁ (le_of_mul_le_mul_left ?_ hd')
  linarith

end TauCeti.Isogeny.Hom
