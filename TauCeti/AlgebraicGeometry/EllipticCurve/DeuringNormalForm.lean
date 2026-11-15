/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.DivisionPolynomialSeparable

/-!
# The Deuring normal form of an elliptic curve

For `a : R`, the Weierstrass curve in **Deuring normal form** is

`Y² + aXY + Y = X³`,

that is, `a₁ = a`, `a₃ = 1` and `a₂ = a₄ = a₆ = 0` (`WeierstrassCurve.deuringNormalForm`). Its
invariants are

  `c₄ = a (a³ - 24)`, `c₆ = -a⁶ + 36a³ - 216`, `Δ = a³ - 27`, `j = a³ (a³ - 24)³ / (a³ - 27)`,

so it is elliptic exactly when `a³ - 27` is a unit. The point `(0, 0)` lies on it, with horizontal
tangent `Y = 0` meeting the curve there to order three: `(0, 0)` is a flex, a point of order `3`,
and the `3`-division polynomial `Ψ₃` vanishes at `0`.

Conversely, a point at which `Ψ₃` vanishes can be moved to the origin in this shape (Silverman,
*AEC*, Appendix A, Proposition 1.3). Let `(x, y)` be a point of `W` with `Ψ₃(x) = 0`, and suppose
that `ψ₂(x, y) = 2y + a₁x + a₃` is a cube `u³` of a unit. The translation `(r, t) = (x, y)` moves
the point to the origin (`a₆ = 0`), the shear `s` with `s ψ₂(x, y) = a₄ + 2a₂x - a₁y + 3x²` makes
the tangent line there horizontal (`a₄ = 0`), and the scaling by `u` makes `a₃ = 1`. The coefficient
`a₂` then vanishes because `a₂ ψ₂(x, y)² = Ψ₃(x)` after the translation and shear
(`WeierstrassCurve.a₂_mul_ψ₂_sq_eq_eval_Ψ₃`).

Away from characteristic `3` every elliptic curve takes this form after a finite separable
extension of the base field: adjoin a root `x` of the separable polynomial `Ψ₃`, a matching `y`,
and a cube root of `ψ₂(x, y)`, which is nonzero because `Ψ₃` and `Ψ₂Sq` have no common root. This
holds in characteristic `2` too, where the Legendre form `y² = x (x - 1) (x - λ)` of
`TauCeti/AlgebraicGeometry/EllipticCurve/Legendre.lean` is not available. Since `j` is an explicit
rational function of `a`, the Deuring form ties the reduction of an elliptic curve to its
`j`-invariant in residue characteristic `2`, as the Legendre form does away from it: this is how
the criterion `WeierstrassCurve.hasPotentialGoodReduction_of_isInteger_j` for potential good
reduction is proved in residue characteristic `2`.

## Main definitions

* `WeierstrassCurve.deuringNormalForm a`: the curve `Y² + aXY + Y = X³`.

## Main results

* `WeierstrassCurve.deuringNormalForm_Δ` and `WeierstrassCurve.deuringNormalForm_j`: its
  discriminant and `j`-invariant.
* `WeierstrassCurve.exists_variableChange_smul_eq_deuringNormalForm`: a curve with a point at
  which `Ψ₃` vanishes and `ψ₂` is a cube of a unit is a change of variables away from Deuring
  normal form.
* `WeierstrassCurve.exists_variableChange_smul_baseChange_eq_deuringNormalForm`: away from
  characteristic `3`, an elliptic curve takes Deuring normal form over a finite separable
  extension.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Appendix A, Proposition 1.3,
  and VII.5.5.
-/

public section

universe u

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-! ### The Deuring normal form -/

/-- The Weierstrass curve `Y² + aXY + Y = X³` in **Deuring normal form**: `a₁ = a`, `a₃ = 1` and
`a₂ = a₄ = a₆ = 0`. -/
def deuringNormalForm (a : R) : WeierstrassCurve R where
  a₁ := a
  a₂ := 0
  a₃ := 1
  a₄ := 0
  a₆ := 0

variable (a : R)

@[simp] theorem deuringNormalForm_a₁ : (deuringNormalForm a).a₁ = a := (rfl)
@[simp] theorem deuringNormalForm_a₂ : (deuringNormalForm a).a₂ = 0 := (rfl)
@[simp] theorem deuringNormalForm_a₃ : (deuringNormalForm a).a₃ = 1 := (rfl)
@[simp] theorem deuringNormalForm_a₄ : (deuringNormalForm a).a₄ = 0 := (rfl)
@[simp] theorem deuringNormalForm_a₆ : (deuringNormalForm a).a₆ = 0 := (rfl)

@[simp]
theorem deuringNormalForm_b₂ : (deuringNormalForm a).b₂ = a ^ 2 := by
  simp [b₂, sq]

@[simp]
theorem deuringNormalForm_b₄ : (deuringNormalForm a).b₄ = a := by
  simp [b₄]

@[simp]
theorem deuringNormalForm_b₆ : (deuringNormalForm a).b₆ = 1 := by
  simp [b₆]

@[simp]
theorem deuringNormalForm_b₈ : (deuringNormalForm a).b₈ = 0 := by
  simp [b₈]

@[simp]
theorem deuringNormalForm_c₄ : (deuringNormalForm a).c₄ = a * (a ^ 3 - 24) := by
  rw [c₄, deuringNormalForm_b₂, deuringNormalForm_b₄]
  ring

/-- The `c₆` of the Deuring normal form `Y² + aXY + Y = X³` is `-a⁶ + 36a³ - 216`. -/
@[simp]
theorem deuringNormalForm_c₆ : (deuringNormalForm a).c₆ = -a ^ 6 + 36 * a ^ 3 - 216 := by
  rw [c₆, deuringNormalForm_b₂, deuringNormalForm_b₄, deuringNormalForm_b₆]
  ring

/-- The discriminant of the Deuring normal form `Y² + aXY + Y = X³` is `a³ - 27`. -/
@[simp]
theorem deuringNormalForm_Δ : (deuringNormalForm a).Δ = a ^ 3 - 27 := by
  rw [Δ, deuringNormalForm_b₂, deuringNormalForm_b₄, deuringNormalForm_b₆, deuringNormalForm_b₈]
  ring

/-- The Deuring normal form `Y² + aXY + Y = X³` is elliptic exactly when `a³ - 27` is a unit. -/
theorem isElliptic_deuringNormalForm_iff :
    (deuringNormalForm a).IsElliptic ↔ IsUnit (a ^ 3 - 27) := by
  rw [isElliptic_iff, deuringNormalForm_Δ]

/-- The `j`-invariant of the Deuring normal form `Y² + aXY + Y = X³` is
`a³ (a³ - 24)³ / (a³ - 27)`. -/
@[simp]
theorem deuringNormalForm_j {F : Type*} [Field F] (a : F) [(deuringNormalForm a).IsElliptic] :
    (deuringNormalForm a).j = a ^ 3 * (a ^ 3 - 24) ^ 3 / (a ^ 3 - 27) := by
  rw [j_eq, deuringNormalForm_c₄, deuringNormalForm_Δ, div_eq_inv_mul, mul_pow]

/-- The point `(0, 0)` lies on the Deuring normal form. -/
theorem equation_deuringNormalForm_zero : (deuringNormalForm a).toAffine.Equation 0 0 :=
  Affine.equation_zero.mpr (deuringNormalForm_a₆ a)

/-- On the Deuring normal form, the `3`-division polynomial `Ψ₃` vanishes at `0`: the origin is a
point of order `3`. -/
@[simp]
theorem eval_Ψ₃_deuringNormalForm_zero : (deuringNormalForm a).Ψ₃.eval 0 = 0 := by
  simp [eval_Ψ₃]

/-- The Deuring normal form commutes with base change. -/
@[simp]
theorem map_deuringNormalForm {A : Type*} [CommRing A] (φ : R →+* A) :
    (deuringNormalForm a).map φ = deuringNormalForm (φ a) := by
  ext <;> simp

/-! ### Changes of variables to Deuring normal form -/

variable {W : WeierstrassCurve R}

/-- **Deuring normal form at a point of order `3`.** Let `(x, y)` be a point of `W` at which the
`3`-division polynomial `Ψ₃` vanishes, and `u` a unit with `u³ = ψ₂(x, y) = 2y + a₁x + a₃`. Then a
change of variables carries `W` to a curve `Y² + aXY + Y = X³` in Deuring normal form. -/
theorem exists_variableChange_smul_eq_deuringNormalForm {x y : R} (h : W.toAffine.Equation x y)
    (hΨ₃ : W.Ψ₃.eval x = 0) (u : Rˣ) (hu : (u : R) ^ 3 = 2 * y + W.a₁ * x + W.a₃) :
    ∃ (C : VariableChange R) (a : R), C • W = deuringNormalForm a := by
  set v : R := ↑u⁻¹
  have hv : v * u = 1 := u.inv_mul
  set s := (W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2) * v ^ 3
  have hs : s * (2 * y + W.a₁ * x + W.a₃) = W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2 := by
    rw [← hu]
    linear_combination (W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2) *
      (v ^ 2 * u ^ 2 + v * u + 1) * hv
  -- the coefficient `a₂` after the translation and the shear vanishes with `Ψ₃(x)`
  have ha₂ : W.a₂ - s * W.a₁ + 3 * x - s ^ 2 = 0 := by
    have h₂ := a₂_mul_ψ₂_sq_eq_eval_Ψ₃ h hs
    rw [hΨ₃, ← hu] at h₂
    have hu6 : IsUnit (((u : R) ^ 3) ^ 2) := (u.isUnit.pow 3).pow 2
    exact hu6.mul_left_eq_zero.mp h₂
  rw [Affine.equation_iff] at h
  refine ⟨⟨u, x, s, y⟩, v * (W.a₁ + 2 * s), ?_⟩
  ext
  · rw [variableChange_a₁, deuringNormalForm_a₁]
  · rw [variableChange_a₂, deuringNormalForm_a₂, ha₂, mul_zero]
  · rw [variableChange_a₃, deuringNormalForm_a₃]
    linear_combination (-v ^ 3) * hu + (v ^ 2 * u ^ 2 + v * u + 1) * hv
  · rw [variableChange_a₄, deuringNormalForm_a₄]
    linear_combination (-v ^ 4) * hs
  · rw [variableChange_a₆, deuringNormalForm_a₆]
    linear_combination (-v ^ 6) * h

/-- Away from characteristic `3`, an elliptic curve over `K` has a point `(x, y)` with `Ψ₃(x) = 0`
and `ψ₂(x, y) = 2y + a₁x + a₃ ≠ 0` over a finite separable extension `L` of `K`: adjoin a root `x`
of the separable polynomial `Ψ₃`, then a root `y` of the quadratic in `Y` cutting out the points
above `x`, whose discriminant `Ψ₂Sq(x)` is nonzero because `Ψ₃` and `Ψ₂Sq` have no common root. -/
private theorem exists_equation_eval_Ψ₃_eq_zero_baseChange {K : Type u} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic] (h3 : (3 : K) ≠ 0) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L) (x y : L), (W.baseChange L).toAffine.Equation x y ∧
      (W.baseChange L).Ψ₃.eval x = 0 ∧
      2 * y + (W.baseChange L).a₁ * x + (W.baseChange L).a₃ ≠ 0 := by
  -- a root `x₀` of the separable polynomial `Ψ₃`, in its splitting field `L₁`
  have hsep₁ : W.Ψ₃.Separable := by
    rw [← preΨ_three]
    exact W.separable_preΨ (by exact_mod_cast h3)
  let L₁ := SplittingField W.Ψ₃
  have : IsGalois K L₁ := IsGalois.of_separable_splitting_field hsep₁
  obtain ⟨x₀, hx₀⟩ := (SplittingField.splits W.Ψ₃).exists_eval_eq_zero (by
    rw [degree_map, degree_eq_natDegree (W.Ψ₃_ne_zero h3), W.natDegree_Ψ₃ h3]
    norm_num)
  set W₁ := W.baseChange L₁ with hW₁
  have hΨ₁ : W₁.Ψ₃.eval x₀ = 0 := by rw [hW₁, baseChange, map_Ψ₃]; exact hx₀
  have hD : W₁.Ψ₂Sq.eval x₀ ≠ 0 := by
    refine W₁.eval_Ψ₂Sq_ne_zero_of_eval_Ψ₃_eq_zero ?_ hΨ₁
    rw [hW₁, baseChange, map_Δ]
    exact (_root_.map_ne_zero _).mpr W.isUnit_Δ.ne_zero
  -- the points of `W₁` above `x₀` are the roots of the quadratic `q`, of discriminant `Ψ₂Sq(x₀)`
  obtain ⟨b, hb⟩ : ∃ b, b = W₁.a₁ * x₀ + W₁.a₃ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = x₀ ^ 3 + W₁.a₂ * x₀ ^ 2 + W₁.a₄ * x₀ + W₁.a₆ := ⟨_, rfl⟩
  set q : L₁[X] := C 1 * X ^ 2 + C b * X + C (-c)
  have hDq : W₁.Ψ₂Sq.eval x₀ = discrim 1 b (-c) := by
    simp only [Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X, hb, hc, discrim]
    ring
  have hsep₂ : q.Separable :=
    separable_quadratic_of_isUnit_discrim (hDq ▸ isUnit_iff_ne_zero.mpr hD)
  -- a root `y₀` of `q`, in its splitting field `L₂`; then `(2y₀ + b)² = Ψ₂Sq(x₀)`
  let L₂ := SplittingField q
  have : IsGalois L₁ L₂ := IsGalois.of_separable_splitting_field hsep₂
  obtain ⟨y₀, hy₀⟩ := (SplittingField.splits q).exists_eval_eq_zero (by
    rw [degree_map, degree_quadratic one_ne_zero]
    norm_num)
  set ι := algebraMap L₁ L₂
  have hy : y₀ ^ 2 + ι b * y₀ - ι c = 0 := by
    simp only [q, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X,
      Polynomial.map_neg, eval_add, eval_mul, eval_pow, eval_neg, eval_C, eval_X, map_one, one_mul,
      map_neg] at hy₀
    linear_combination hy₀
  have hw : (2 * y₀ + ι b) ^ 2 = ι (discrim 1 b (-c)) := by
    rw [discrim, map_sub, map_pow, map_mul, map_mul, map_neg, map_one, map_ofNat]
    linear_combination 4 * hy
  have hw0 : 2 * y₀ + ι b ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero, eq_comm, map_eq_zero_iff ι ι.injective, ← hDq] at hw
    exact hD hw
  have : Algebra.IsSeparable K L₂ := Algebra.IsSeparable.trans K L₁ L₂
  have : FiniteDimensional K L₂ := Module.Finite.trans L₁ L₂
  -- the point `(x₀, y₀)` of the base change `W₁.map ι` of `W` to `L₂`
  have hW₂ : W₁.map ι = W.baseChange L₂ := map_baseChange W (IsScalarTower.toAlgHom K L₁ L₂)
  refine ⟨L₂, _, _, ‹_›, ‹_›, ι x₀, y₀, ?_, ?_, ?_⟩ <;> rw [← hW₂]
  · rw [Affine.equation_iff]
    simp only [hb, hc, map_add, map_mul, map_pow] at hy
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
    linear_combination hy
  · rw [map_Ψ₃, eval_map, eval₂_at_apply, hΨ₁, map_zero]
  · rwa [map_a₁, map_a₃, add_assoc, ← map_mul, ← map_add, ← hb]

/-- **Deuring normal form over a finite separable extension.** Away from characteristic `3`, an
elliptic curve over `K` becomes isomorphic to a curve `Y² + aXY + Y = X³` over a finite separable
extension `L` of `K`: one obtained by adjoining a root `x` of the `3`-division polynomial `Ψ₃`, a
point `(x, y)` of the curve above it, and a cube root of `2y + a₁x + a₃`. -/
theorem exists_variableChange_smul_baseChange_eq_deuringNormalForm {K : Type u} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic] (h3 : (3 : K) ≠ 0) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L) (C : VariableChange L) (a : L),
      C • W.baseChange L = deuringNormalForm a := by
  obtain ⟨L₁, _, _, _, _, x, y, hE, hΨ₃, hψ₂⟩ := exists_equation_eval_Ψ₃_eq_zero_baseChange W h3
  set W₁ := W.baseChange L₁
  -- a cube root `u` of `ψ₂(x, y)`, in the splitting field `L` of `X³ - ψ₂(x, y)`
  have h3₁ : ((3 : ℕ) : L₁) ≠ 0 := by
    rw [Nat.cast_ofNat, ← map_ofNat (algebraMap K L₁)]
    exact (_root_.map_ne_zero _).mpr h3
  let L := SplittingField (X ^ 3 - C (2 * y + W₁.a₁ * x + W₁.a₃) : L₁[X])
  have : IsGalois L₁ L := IsGalois.of_separable_splitting_field (separable_X_pow_sub_C _ h3₁ hψ₂)
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.trans K L₁ L
  have : FiniteDimensional K L := Module.Finite.trans L₁ L
  obtain ⟨u, hu⟩ := (SplittingField.splits
    (X ^ 3 - C (2 * y + W₁.a₁ * x + W₁.a₃) : L₁[X])).exists_eval_eq_zero
    (by rw [degree_map, degree_X_pow_sub_C (by norm_num)]; norm_num)
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X,
    eval_C, sub_eq_zero] at hu
  set f := algebraMap L₁ L
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow three_ne_zero, eq_comm, map_eq_zero_iff f f.injective] at hu
    exact hψ₂ hu
  -- the point `(x, y)` of the base change `W₁.map f` of `W` to `L`, with `ψ₂(x, y) = u³`
  have hW : W₁.map f = W.baseChange L := map_baseChange W (IsScalarTower.toAlgHom K L₁ L)
  have hu₃ : ((Units.mk0 u hu0 : Lˣ) : L) ^ 3 = 2 * f y + (W₁.map f).a₁ * f x + (W₁.map f).a₃ := by
    rw [Units.val_mk0, hu, map_a₁, map_a₃]
    simp only [map_add, map_mul, map_ofNat]
  obtain ⟨C, a, hC⟩ := exists_variableChange_smul_eq_deuringNormalForm (hE.map f)
    (by rw [map_Ψ₃, eval_map, eval₂_at_apply, hΨ₃, map_zero]) _ hu₃
  exact ⟨L, _, _, ‹_›, ‹_›, C, a, hW ▸ hC⟩

end WeierstrassCurve

end
