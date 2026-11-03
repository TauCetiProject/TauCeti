/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Equation
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# The point-valued Tate uniformisation map

For a unit `q` of norm below one in a complete non-archimedean normed field, the Tate
coordinates define `tateUniformization : Kˣ / q^ℤ → E_q(K)`. The identity coset maps to the
point at infinity; all other cosets give affine points with the established Tate coordinates.
In particular, the inverse image of infinity is exactly the identity coset, or `q^ℤ` when
expressed on unit representatives.

For a complete normed extension `L` of `K`, the Tate coordinates over `L` give
`tateUniformizationBaseChange L q hq : Lˣ / q^ℤ → E_q(L)`, valued in the points of the base change
of `E_q` to `L`. On classes coming from `Kˣ / q^ℤ`, it is the base change of
`tateUniformization`, and it commutes with every continuous `K`-algebra map `L → M`, which acts on
parameters through `tateParameterMap`.

The map respects inversion and isometric coefficient embeddings. These statements do not
assert additivity, injectivity away from infinity, or surjectivity, and the map is not yet
bundled as a group homomorphism. The norm need not be discrete, and the characteristic is
unrestricted.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

namespace TauCeti

open WeierstrassCurve.Affine

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The Tate uniformisation map as a function on multiplicative parameters. The identity
coset is sent to infinity, rather than to the totalised coordinate-series values at a pole. -/
noncomputable def tateUniformization (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Kˣ ⧸ Subgroup.zpowers q) : (tateCurveAt q hq).toAffine.Point := by
  classical
  exact if hx : x = 1 then 0 else Point.mk (equation_tateQuotientCoordinates q hq hx)

/-- The identity parameter maps to the point at infinity. -/
@[simp]
theorem tateUniformization_one (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    tateUniformization q hq 1 = 0 := by
  simp [tateUniformization]

/-- At a nonidentity parameter the map is the affine point with the Tate coordinates. -/
theorem tateUniformization_of_ne_one (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {x : Kˣ ⧸ Subgroup.zpowers q} (hx : x ≠ 1) :
    tateUniformization q hq x = Point.mk (equation_tateQuotientCoordinates q hq hx) := by
  simp [tateUniformization, hx]

/-- Exactly the identity parameter maps to infinity. -/
@[simp]
theorem tateUniformization_eq_zero_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Kˣ ⧸ Subgroup.zpowers q) :
    tateUniformization q hq x = 0 ↔ x = 1 := by
  classical
  by_cases hx : x = 1
  · simp [hx]
  · simp [tateUniformization_of_ne_one q hq hx, Point.mk, hx]

/-- The formula on a unit representative away from the poles. -/
theorem tateUniformization_mk_of_notMem_zpowers (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : u ∉ Subgroup.zpowers q) :
    tateUniformization q hq (u : Kˣ ⧸ Subgroup.zpowers q) =
      Point.mk (equation_tateUniformizationX_tateUniformizationY_of_notMem_zpowers q u hq hu) := by
  rw [tateUniformization_of_ne_one q hq
    (x := (u : Kˣ ⧸ Subgroup.zpowers q)) (fun h ↦ hu ((QuotientGroup.eq_one_iff u).mp h))]
  simp only [Point.mk, tateQuotientCoordinates_mk]

/-- An affine point is the image of a parameter exactly when both its coordinates are the
Tate coordinates and the parameter is not the identity. -/
@[simp]
theorem tateUniformization_eq_some_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Kˣ ⧸ Subgroup.zpowers q) {a b : K}
    (h : (tateCurveAt q hq).toAffine.Nonsingular a b) :
    tateUniformization q hq x = .some a b h ↔
      x ≠ 1 ∧ (tateQuotientCoordinates q x).1 = a ∧
        (tateQuotientCoordinates q x).2 = b := by
  classical
  by_cases hx : x = 1
  · simp [hx]
  · simp [tateUniformization_of_ne_one q hq hx, Point.mk, hx]

/-- Inverting the multiplicative parameter negates its image on the Tate curve. -/
@[simp]
theorem tateUniformization_inv (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Kˣ ⧸ Subgroup.zpowers q) :
    tateUniformization q hq x⁻¹ = -tateUniformization q hq x := by
  classical
  by_cases hx : x = 1
  · simp [hx]
  · rw [tateUniformization_of_ne_one q hq (inv_ne_one.mpr hx),
      tateUniformization_of_ne_one q hq hx]
    simp only [Point.mk, Point.neg_some, Point.some.injEq,
      negY, tateCurveAt_a₁, tateCurveAt_a₃, one_mul, sub_zero]
    rw [tateQuotientCoordinates_inv q hq x]
    exact ⟨rfl, rfl⟩

section BaseChange

variable {L : Type*} [NormedField L] [CompleteSpace L] [IsUltrametricDist L]
  (f : K →+* L) [RingHomIsometric f]

/-- Tate uniformisation commutes with an isometric field embedding, after identifying the
mapped Tate equation with the Tate equation of the mapped parameter. -/
theorem mapAlong_tateUniformization (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Kˣ ⧸ Subgroup.zpowers q) :
    cast (congrArg (fun W : WeierstrassCurve L ↦ W.toAffine.Point)
      (map_tateCurveAt f q hq))
      (Point.mapAlong (W := tateCurveAt q hq) f f.injective (tateUniformization q hq x)) =
        tateUniformization (Units.map (f : K →* L) q)
          (by simpa using hq)
          (tateParameterBaseChange f q x) := by
  classical
  by_cases hx : x = 1
  · subst x
    simp only [tateUniformization_one, map_one, Point.mapAlong_zero]
    exact Point.cast_zero (map_tateCurveAt f q hq)
  · have hx' : tateParameterBaseChange f q x ≠ 1 := by
      intro h
      exact hx (tateParameterBaseChange_injective f f.injective q (by simpa using h))
    rw [tateUniformization_of_ne_one q hq hx,
      tateUniformization_of_ne_one _ _ hx']
    simp only [Point.mk, Point.mapAlong_some]
    rw [Point.cast_some (map_tateCurveAt f q hq)]
    simp only [tateQuotientCoordinates_tateParameterBaseChange f
      (RingHom.isometry f).continuous q hq x]

end BaseChange

/-! ### The uniformisation over an extension -/

section Extension

open WeierstrassCurve

variable (L : Type*) [NormedField L] [NormedAlgebra K L] [CompleteSpace L] [IsUltrametricDist L]

/-- The **Tate uniformisation over an extension** `L` of `K`, the map `Lˣ / q^ℤ → E_q(L)` into the
points of the base change of `E_q` to `L`. It is `tateUniformization` for the image of `q` in `L`,
transported along `baseChange_tateCurveAt`. -/
noncomputable def tateUniformizationBaseChange (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    ((tateCurveAt q hq)⁄L).toAffine.Point :=
  cast (congrArg (fun W : WeierstrassCurve L ↦ W.toAffine.Point)
    (baseChange_tateCurveAt L q hq).symm)
    (tateUniformization _ ((by simpa using hq)) x)

/-- Exactly the identity parameter maps to infinity. -/
@[simp]
theorem tateUniformizationBaseChange_eq_zero_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    tateUniformizationBaseChange L q hq x = 0 ↔ x = 1 := by
  rw [← tateUniformization_eq_zero_iff _ ((by simpa using hq)) x,
    ← Point.cast_zero (baseChange_tateCurveAt L q hq).symm, tateUniformizationBaseChange]
  exact cast_inj _

/-- The identity parameter maps to the point at infinity. -/
@[simp]
theorem tateUniformizationBaseChange_one (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    tateUniformizationBaseChange L q hq 1 = 0 :=
  (tateUniformizationBaseChange_eq_zero_iff L q hq 1).mpr rfl

/-- An affine point is the image of a parameter exactly when both its coordinates are the
Tate coordinates and the parameter is not the identity. -/
@[simp]
theorem tateUniformizationBaseChange_eq_some_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) {a b : L}
    (h : ((tateCurveAt q hq)⁄L).toAffine.Nonsingular a b) :
    tateUniformizationBaseChange L q hq x = .some a b h ↔
      x ≠ 1 ∧ (tateQuotientCoordinates _ x).1 = a ∧ (tateQuotientCoordinates _ x).2 = b := by
  have e := baseChange_tateCurveAt L q hq
  rw [← tateUniformization_eq_some_iff _ ((by simpa using hq)) x (by exact e ▸ h),
    tateUniformizationBaseChange, ← cast_inj (congrArg (fun W : WeierstrassCurve L ↦
      W.toAffine.Point) e), cast_cast, cast_eq, Point.cast_some e]

/-- Inverting the multiplicative parameter negates its image on the base-changed Tate curve. -/
@[simp]
theorem tateUniformizationBaseChange_inv (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    tateUniformizationBaseChange L q hq x⁻¹ = -tateUniformizationBaseChange L q hq x := by
  -- transport along an equality of curves commutes with negation
  have cast_neg : ∀ {V V' : WeierstrassCurve L} (h : V = V') (P : V.toAffine.Point),
      cast (congrArg (fun W : WeierstrassCurve L ↦ W.toAffine.Point) h) (-P) =
        -cast (congrArg (fun W : WeierstrassCurve L ↦ W.toAffine.Point) h) P := by
    rintro _ _ rfl P
    rfl
  rw [tateUniformizationBaseChange, tateUniformization_inv,
    cast_neg (baseChange_tateCurveAt L q hq).symm]
  rfl

/-- **The Tate uniformisation is compatible with base change from `K`**: moving the image of a
class of `Kˣ / q^ℤ` to `L` gives the image of the class it defines in `Lˣ / q^ℤ`. -/
theorem tateUniformizationBaseChange_tateParameterBaseChange (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Kˣ ⧸ Subgroup.zpowers q) :
    tateUniformizationBaseChange L q hq (tateParameterBaseChange (algebraMap K L) q x) =
      Point.mapAlong (algebraMap K L) (algebraMap K L).injective (tateUniformization q hq x) := by
  have : RingHomIsometric (algebraMap K L) := ⟨norm_algebraMap' L _⟩
  rw [tateUniformizationBaseChange, ← mapAlong_tateUniformization (algebraMap K L) q hq x,
    cast_cast]
  -- `(tateCurveAt q hq)⁄L` is `(tateCurveAt q hq).map (algebraMap K L)` by definition, so the
  -- remaining transport is along a definitional equality of point types
  rfl

variable {L} {M : Type*} [NormedField M] [NormedAlgebra K M] [CompleteSpace M]
  [IsUltrametricDist M] [DecidableEq L] [DecidableEq M]

/-- **The Tate uniformisation is compatible with continuous maps of extensions**: for a continuous
`K`-algebra map `ι : L → M`, applying `ι` to the image of a parameter `x` gives the image of
`ι x`. -/
theorem map_tateUniformizationBaseChange (q : Kˣ) (hq : ‖(q : K)‖ < 1) (ι : L →ₐ[K] M)
    (hι : Continuous ι)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    Point.map ι (tateUniformizationBaseChange L q hq x) =
      tateUniformizationBaseChange M q hq (tateParameterMap q ι x) := by
  by_cases hx : x = 1
  · simp [hx]
  obtain ⟨a, b, h, hP⟩ := Point.exists_eq_some_of_ne_zero
    ((tateUniformizationBaseChange_eq_zero_iff L q hq x).not.mpr hx)
  obtain ⟨-, ha, hb⟩ := (tateUniformizationBaseChange_eq_some_iff L q hq x h).mp hP
  rw [hP, Point.map_some, eq_comm, tateUniformizationBaseChange_eq_some_iff,
    tateQuotientCoordinates_tateParameterMap q hq ι hι, ha, hb]
  exact ⟨(map_ne_one_iff _ (tateParameterMap_injective q ι.injective)).mpr hx, rfl, rfl⟩

end Extension

end TauCeti

end
