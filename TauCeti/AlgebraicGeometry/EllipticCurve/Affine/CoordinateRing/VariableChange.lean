/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
-- Proof-only: the monomial basis of the coordinate ring.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.Basis
-- Proof-only: `equation_X_root`, the equation satisfied by the coordinate functions.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval
-- Proof-only: the Weierstrass equation under a change of variables.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.VariableChange

/-!
# Changes of variables and the coordinate functions of a Weierstrass curve

Let `W` be a Weierstrass curve over a commutative ring `R`, and let `x` and `y` be the coordinate
functions of its affine coordinate ring `R[W] = R[X, Y] ⧸ (W(X, Y))`. The pair `(x, y)` satisfies
the Weierstrass equation of `W`, and of no other Weierstrass curve over `R`. This file is about
the pairs of the shape `(αx + β, γy + δx + ε)`, with coefficients in `R`, that satisfy the
Weierstrass equation of a second curve `W'` over `R`. For a change of variables `C = (u, r, s, t)`
the pair `(u²x + r, u³y + u²sx + t)` does so exactly when `C • W' = W`, by the transformation law
`WeierstrassCurve.Affine.baseChange_variableChange_equation`. Conversely, if
`(αx + β, γy + δx + ε)` satisfies the equation of `W'` then `γ² = α³`, and if moreover `α` is a
unit then the pair is `(u²x + r, u³y + u²sx + t)` for a change of variables `C` with `C • W' = W`.
No hypothesis on `W`, on `W'` or on `R` is needed.

The coordinate ring is free over `R` on the monomials `xⁱ` and `xⁱy`
(`WeierstrassCurve.Affine.CoordinateRing.basisMonomials`). Once `y²` is eliminated by the equation
of `W`, the equation of `W'` at such a pair is an `R`-linear relation among the six monomials `1`,
`x`, `x²`, `x³`, `y` and `xy`, so its six coefficients vanish. For the pair `(x, y)` the coefficient
of `x³` is zero and the other five are, up to sign, the differences of the coefficients of the two
curves. For the pair `(αx + β, γy + δx + ε)` the coefficient of `x³` is `γ² - α³`. When `α` is a
unit, `u = γ / α` is then a unit with `u² = α` and `u³ = γ`, which puts the pair in the shape
`(u²x + r, u³y + u²sx + t)`, and that case is reduced to the pair `(x, y)` by the transformation
law `WeierstrassCurve.Affine.baseChange_variableChange_equation`.

The first statement makes the substitution `(x', y') ↦ (u²x + r, u³y + u²sx + t)` a homomorphism
`R[W'] → R[W]` whenever `C • W' = W`, and the substitution of `C⁻¹` inverts it: a change of
variables identifies the coordinate rings, and changes of variables compose as these isomorphisms
do. The second statement is the converse: a homomorphism `R[W'] → R[W]` of this shape, with `α` a
unit, comes from a change of variables.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.variableChangeEquiv`: the isomorphism
  `R[W'] ≃ₐ[R] R[W]` of a change of variables `C` with `C • W' = W`.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.equation_X_root_iff`: the pair `(x, y)` satisfies
  the equation of `V` over `R[W]` exactly when `V = W`.
* `WeierstrassCurve.Affine.CoordinateRing.sq_eq_pow_three_of_equation`: if the pair
  `(αx + β, γy + δx + ε)` satisfies the equation of `W'` over `R[W]`, then `γ² = α³`.
* `WeierstrassCurve.Affine.CoordinateRing.exists_variableChange_of_equation`: if moreover `α` is
  a unit, there is a change of variables `C` with `C • W' = W`, `u² = α`, `u³ = γ`, `r = β`,
  `u²s = δ` and `t = ε`.
* `WeierstrassCurve.Affine.CoordinateRing.variableChangeEquiv_trans` and
  `WeierstrassCurve.Affine.CoordinateRing.variableChangeEquiv_one`: the isomorphisms compose
  as the changes of variables multiply.
* `WeierstrassCurve.Affine.CoordinateRing.variableChangeEquiv_inj`: a change of variables is
  determined by its isomorphism of coordinate rings.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 (the change of
  variables) and the proof of III.3.1(b).
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, directory
`projects/ModularCurves/ModularCurves/EllipticCurve`. The results come from
`exists_variableChange_of_filtration` in `ComparisonCoefficients.lean` and its private helpers
`six_ext` and `exists_unit_sq_cube`. That theorem takes an isomorphism `R[W'] ≃ₐ[R] R[W]` preserving
a filtration of the coordinate rings by spans of monomials, extracts `α`, `β`, `γ`, `δ`, `ε` from it
with `α` and `γ` units, and treats the zero ring separately. Here no isomorphism and no filtration
appear: the hypothesis is the equation satisfied by the pair `(αx + β, γy + δx + ε)`, only `α` is
assumed to be a unit, and there is no case distinction on `R`. What is kept is the comparison of the
coefficients of `1`, `x`, `x²`, `x³`, `y` and `xy` after eliminating `y²` (the source's `six_ext`,
which is proved there for a nontrivial ring from Mathlib's basis `{1, y}` over `R[X]` and is deduced
here from the monomial basis), and the unit `u = γ / α` (`exists_unit_sq_cube`). The source then
solves the five other coefficient equations for the coefficients of `C • W'`; here only the
coefficient of `x³` of that relation is used, and `C • W' = W` follows from the transformation law
`WeierstrassCurve.Affine.baseChange_variableChange_equation` and from `equation_X_root_iff`, in
which the other five coefficients are compared for the pair `(x, y)` only. The equation satisfied
by the pair `(x, y)`, `equation_X_root`, is used in the source as `coordY_mul_coordY`
(`PoleFiltration.lean`), a formula for `y²`. `equation_X_root_iff` is not in the source, and
neither is `variableChangeEquiv` with its lemmas.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine.CoordinateRing

variable {R : Type*} [CommRing R]

-- An `R`-linear relation among the monomials `1`, `x`, `x²`, `x³`, `y` and `xy` of `R[W]` has
-- zero coefficients: these monomials are members of the monomial basis.
private theorem coeff_eq_zero_of_relation (W : Affine R) {c₀ c₁ c₂ c₃ d₀ d₁ : R}
    (h : algebraMap R W.CoordinateRing c₀ + algebraMap R _ c₁ * AdjoinRoot.of W.polynomial X
      + algebraMap R _ c₂ * AdjoinRoot.of W.polynomial X ^ 2
      + algebraMap R _ c₃ * AdjoinRoot.of W.polynomial X ^ 3
      + algebraMap R _ d₀ * AdjoinRoot.root W.polynomial
      + algebraMap R _ d₁ * (AdjoinRoot.of W.polynomial X * AdjoinRoot.root W.polynomial) = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ d₀ = 0 ∧ d₁ = 0 := by
  have hli := (CoordinateRing.basisMonomials W).linearIndependent.comp
    ![(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (1, 1)] (by decide)
  -- evaluating the two families at the six indices turns the relation into `h`
  have key := Fintype.linearIndependent_iff.mp hli ![c₀, c₁, c₂, c₃, d₀, d₁]
    (by simpa only [Fin.sum_univ_six, Function.comp_apply, Matrix.cons_val, basisMonomials_apply,
      Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one, one_mul, Algebra.smul_def] using h)
  exact ⟨key 0, key 1, key 2, key 3, key 4, key 5⟩

variable {W W' V : WeierstrassCurve R}

/-- **A Weierstrass curve is determined by the coordinate functions of its coordinate ring.** For
Weierstrass curves `W` and `V` over `R`, the pair `(x, y)` of coordinate functions of `R[W]`
satisfies the Weierstrass equation of the base change of `V` to `R[W]` if and only if `V = W`. -/
@[simp]
theorem equation_X_root_iff :
    (V⁄W.toAffine.CoordinateRing).toAffine.Equation (AdjoinRoot.of W.toAffine.polynomial X)
      (AdjoinRoot.root W.toAffine.polynomial) ↔ V = W := by
  have hW := equation_X_root W
  refine ⟨fun h ↦ ?_, fun h ↦ by rwa [h]⟩
  rw [equation_iff'] at h hW
  simp only [baseChange_a₁, baseChange_a₂, baseChange_a₃, baseChange_a₄, baseChange_a₆] at h hW
  -- the difference of the two equations is a linear relation among `1`, `x`, `x²`, `y` and `xy`;
  -- `algebra` normalises in the `R`-algebra `R[W]`, keeping the coefficients in `R`
  obtain ⟨h₆, h₄, h₂, -, h₃, h₁⟩ := coeff_eq_zero_of_relation W.toAffine (c₀ := W.a₆ - V.a₆)
    (c₁ := W.a₄ - V.a₄) (c₂ := W.a₂ - V.a₂) (c₃ := 0) (d₀ := V.a₃ - W.a₃) (d₁ := V.a₁ - W.a₁)
    (by linear_combination (norm := algebra) h - hW)
  exact WeierstrassCurve.ext (sub_eq_zero.mp h₁) (sub_eq_zero.mp h₂).symm (sub_eq_zero.mp h₃)
    (sub_eq_zero.mp h₄).symm (sub_eq_zero.mp h₆).symm

/-- If a pair `(αx + β, γy + δx + ε)` of elements of the coordinate ring `R[W]`, with `α`, `β`,
`γ`, `δ` and `ε` in `R`, satisfies the Weierstrass equation of the base change of `W'` to `R[W]`,
then `γ² = α³`. -/
theorem sq_eq_pow_three_of_equation {α β γ δ ε : R}
    (h : (W'⁄W.toAffine.CoordinateRing).toAffine.Equation
      (algebraMap R W.toAffine.CoordinateRing α * AdjoinRoot.of W.toAffine.polynomial X
        + algebraMap R _ β)
      (algebraMap R W.toAffine.CoordinateRing γ * AdjoinRoot.root W.toAffine.polynomial
        + algebraMap R _ δ * AdjoinRoot.of W.toAffine.polynomial X + algebraMap R _ ε)) :
    γ ^ 2 = α ^ 3 := by
  have hW := equation_X_root W
  rw [equation_iff'] at h hW
  simp only [baseChange_a₁, baseChange_a₂, baseChange_a₃, baseChange_a₄, baseChange_a₆] at h hW
  -- eliminating `y²` leaves a linear relation among `1`, `x`, `x²`, `x³`, `y` and `xy`
  obtain ⟨-, -, -, h₃, -, -⟩ := coeff_eq_zero_of_relation W.toAffine
    (c₀ := ε ^ 2 + W'.a₁ * β * ε + W'.a₃ * ε - (β ^ 3 + W'.a₂ * β ^ 2 + W'.a₄ * β + W'.a₆)
      + γ ^ 2 * W.a₆)
    (c₁ := 2 * δ * ε + W'.a₁ * (α * ε + β * δ) + W'.a₃ * δ
      - (3 * α * β ^ 2 + 2 * W'.a₂ * α * β + W'.a₄ * α) + γ ^ 2 * W.a₄)
    (c₂ := δ ^ 2 + W'.a₁ * α * δ - (3 * α ^ 2 * β + W'.a₂ * α ^ 2) + γ ^ 2 * W.a₂)
    (c₃ := γ ^ 2 - α ^ 3)
    (d₀ := 2 * γ * ε + W'.a₁ * β * γ + W'.a₃ * γ - γ ^ 2 * W.a₃)
    (d₁ := 2 * γ * δ + W'.a₁ * α * γ - γ ^ 2 * W.a₁)
    (by linear_combination (norm := algebra) h - algebraMap R _ γ ^ 2 * hW)
  exact sub_eq_zero.mp h₃

/-- **A solution of Weierstrass shape over the coordinate ring comes from a change of variables.**
If a pair `(αx + β, γy + δx + ε)` of elements of the coordinate ring `R[W]`, with `α`, `β`, `γ`,
`δ` and `ε` in `R` and `α` a unit, satisfies the Weierstrass equation of the base change of `W'`
to `R[W]`, then there is a change of variables `C = (u, r, s, t)` over `R` with `C • W' = W`,
`u² = α`, `u³ = γ`, `r = β`, `u²s = δ` and `t = ε`; that is, the pair is
`(u²x + r, u³y + u²sx + t)`. -/
theorem exists_variableChange_of_equation {α β γ δ ε : R} (hα : IsUnit α)
    (h : (W'⁄W.toAffine.CoordinateRing).toAffine.Equation
      (algebraMap R W.toAffine.CoordinateRing α * AdjoinRoot.of W.toAffine.polynomial X
        + algebraMap R _ β)
      (algebraMap R W.toAffine.CoordinateRing γ * AdjoinRoot.root W.toAffine.polynomial
        + algebraMap R _ δ * AdjoinRoot.of W.toAffine.polynomial X + algebraMap R _ ε)) :
    ∃ C : VariableChange R, C • W' = W ∧ (C.u : R) ^ 2 = α ∧ (C.u : R) ^ 3 = γ ∧ C.r = β ∧
      (C.u : R) ^ 2 * C.s = δ ∧ C.t = ε := by
  have hγα := sq_eq_pow_three_of_equation h
  -- `u = γ / α` is a unit, with inverse `γ / α²`, and `u² = α`, `u³ = γ`
  obtain ⟨v, hv⟩ := hα.exists_right_inv
  obtain ⟨u, rfl, rfl⟩ : ∃ u : Rˣ, (u : R) ^ 2 = α ∧ (u : R) ^ 3 = γ := by
    refine ⟨Units.mkOfMulEqOne (γ * v) (γ * v ^ 2) ?_, ?_, ?_⟩
    · linear_combination v ^ 3 * hγα + (α ^ 2 * v ^ 2 + α * v + 1) * hv
    · rw [Units.val_mkOfMulEqOne]
      linear_combination v ^ 2 * hγα + α * (α * v + 1) * hv
    · rw [Units.val_mkOfMulEqOne]
      linear_combination γ * v ^ 3 * hγα + γ * (α ^ 2 * v ^ 2 + α * v + 1) * hv
  obtain ⟨s, rfl⟩ : (u : R) ^ 2 ∣ δ := (u.isUnit.pow 2).dvd
  -- the pair is now `(u²x + β, u³y + u²sx + ε)`: by the transformation law, `(x, y)` satisfies
  -- the equation of `C • W'` for `C = (u, β, s, ε)`
  simp only [map_mul, map_pow] at h
  exact ⟨⟨u, β, s, ε⟩,
    equation_X_root_iff.mp ((baseChange_variableChange_equation W' ⟨u, β, s, ε⟩ _ _).mp h),
    rfl, rfl, rfl, rfl, rfl⟩

/-! ### The isomorphism of coordinate rings induced by a change of variables -/

section VariableChangeEquiv

variable {W'' : WeierstrassCurve R} (C C' : VariableChange R)

/-- The pair `(u²x + r, u³y + u²sx + t)` of `R[W]` satisfies the Weierstrass equation of `W'` when
`C • W' = W`: this is the transformation law, read at the coordinate functions of `W`. -/
private theorem equation_variableChange (h : C • W' = W) :
    (W'⁄W.toAffine.CoordinateRing).toAffine.Equation
      (algebraMap R W.toAffine.CoordinateRing C.u ^ 2 * AdjoinRoot.of W.toAffine.polynomial X
        + algebraMap R _ C.r)
      (algebraMap R W.toAffine.CoordinateRing C.u ^ 3 * AdjoinRoot.root W.toAffine.polynomial
        + algebraMap R _ C.u ^ 2 * algebraMap R _ C.s * AdjoinRoot.of W.toAffine.polynomial X
        + algebraMap R _ C.t) :=
  (baseChange_variableChange_equation W' C _ _).mpr (by rw [h]; exact equation_X_root W)

/-- The homomorphism `R[W'] → R[W]` substituting `(u²x + r, u³y + u²sx + t)` for the coordinate
functions of `W'`, for `C • W' = W`. -/
private noncomputable def variableChangeAlgHom (h : C • W' = W) :
    W'.toAffine.CoordinateRing →ₐ[R] W.toAffine.CoordinateRing :=
  evalAlgHom (equation_variableChange C h)

private theorem variableChangeAlgHom_comp (h : C • W' = W) (h' : C' • W'' = W') :
    (variableChangeAlgHom C h).comp (variableChangeAlgHom C' h') =
      variableChangeAlgHom (C * C') (by rw [mul_smul, h', h]) := by
  -- both sides are substitutions; compare them on the two coordinate functions of `W''`
  refine algHom_ext ?_ ?_ <;>
  · simp only [variableChangeAlgHom, AlgHom.comp_apply, evalAlgHom_of_X, evalAlgHom_root, map_add,
      map_mul, map_pow, AlgHom.commutes, VariableChange.mul_def, Units.val_mul]
    ring

private theorem variableChangeAlgHom_eq_id (h : C • W = W) (hC : C = 1) :
    variableChangeAlgHom C h = AlgHom.id R W.toAffine.CoordinateRing := by
  subst hC
  refine algHom_ext ?_ ?_ <;>
  · simp [variableChangeAlgHom, VariableChange.one_def]

/-- **The isomorphism of coordinate rings induced by a change of variables.** If `C • W' = W`,
the coordinate functions `x'` and `y'` of `W'` are sent to `u²x + r` and `u³y + u²sx + t`, where
`x` and `y` are those of `W`; on points, this is the substitution
`(x, y) ↦ (u²x + r, u³y + u²sx + t)` carrying the points of `W` to those of `W'`. The inverse is
the isomorphism of `C⁻¹`. -/
noncomputable def variableChangeEquiv (h : C • W' = W) :
    W'.toAffine.CoordinateRing ≃ₐ[R] W.toAffine.CoordinateRing :=
  AlgEquiv.ofAlgHom (variableChangeAlgHom C h)
    (variableChangeAlgHom C⁻¹ (by rw [← h, inv_smul_smul]))
    (by rw [variableChangeAlgHom_comp]; exact variableChangeAlgHom_eq_id _ _ (mul_inv_cancel C))
    (by rw [variableChangeAlgHom_comp]; exact variableChangeAlgHom_eq_id _ _ (inv_mul_cancel C))

/-- The isomorphism of a change of variables sends `x'` to `u²x + r`. -/
@[simp]
theorem variableChangeEquiv_of_X (h : C • W' = W) :
    variableChangeEquiv C h (AdjoinRoot.of W'.toAffine.polynomial X) =
      algebraMap R W.toAffine.CoordinateRing C.u ^ 2 * AdjoinRoot.of W.toAffine.polynomial X
        + algebraMap R _ C.r :=
  evalAlgHom_of_X _

/-- The isomorphism of a change of variables sends `y'` to `u³y + u²sx + t`. -/
@[simp]
theorem variableChangeEquiv_root (h : C • W' = W) :
    variableChangeEquiv C h (AdjoinRoot.root W'.toAffine.polynomial) =
      algebraMap R W.toAffine.CoordinateRing C.u ^ 3 * AdjoinRoot.root W.toAffine.polynomial
        + algebraMap R _ C.u ^ 2 * algebraMap R _ C.s * AdjoinRoot.of W.toAffine.polynomial X
        + algebraMap R _ C.t :=
  evalAlgHom_root _

/-- The inverse of the isomorphism of `C` is the isomorphism of `C⁻¹`. -/
theorem variableChangeEquiv_symm (h : C • W' = W) (h' : C⁻¹ • W = W') :
    (variableChangeEquiv C h).symm = variableChangeEquiv C⁻¹ h' := by
  -- both inverses are, by construction, the substitution `variableChangeAlgHom C⁻¹`
  ext
  rfl

/-- The inverse of the isomorphism of a change of variables sends `x` to `u⁻²(x' - r)`, written
through the components of `C⁻¹`. -/
@[simp]
theorem variableChangeEquiv_symm_of_X (h : C • W' = W) :
    (variableChangeEquiv C h).symm (AdjoinRoot.of W.toAffine.polynomial X) =
      algebraMap R W'.toAffine.CoordinateRing C⁻¹.u ^ 2 * AdjoinRoot.of W'.toAffine.polynomial X
        + algebraMap R _ C⁻¹.r := by
  rw [variableChangeEquiv_symm C h (by rw [← h, inv_smul_smul]), variableChangeEquiv_of_X]

/-- The inverse of the isomorphism of a change of variables sends `y` to
`u⁻³(y' - s(x' - r) - t)`, written through the components of `C⁻¹`. -/
@[simp]
theorem variableChangeEquiv_symm_root (h : C • W' = W) :
    (variableChangeEquiv C h).symm (AdjoinRoot.root W.toAffine.polynomial) =
      algebraMap R W'.toAffine.CoordinateRing C⁻¹.u ^ 3 * AdjoinRoot.root W'.toAffine.polynomial
        + algebraMap R _ C⁻¹.u ^ 2 * algebraMap R _ C⁻¹.s * AdjoinRoot.of W'.toAffine.polynomial X
        + algebraMap R _ C⁻¹.t := by
  rw [variableChangeEquiv_symm C h (by rw [← h, inv_smul_smul]), variableChangeEquiv_root]

/-- The isomorphisms of changes of variables compose as the changes of variables multiply. -/
@[simp]
theorem variableChangeEquiv_trans (h : C • W' = W) (h' : C' • W'' = W') :
    (variableChangeEquiv C' h').trans (variableChangeEquiv C h) =
      variableChangeEquiv (C * C') (by rw [mul_smul, h', h]) :=
  AlgEquiv.coe_toAlgHom_injective (variableChangeAlgHom_comp C C' h h')

/-- The isomorphism of the identity change of variables is the identity. -/
@[simp]
theorem variableChangeEquiv_one (h : (1 : VariableChange R) • W = W) :
    variableChangeEquiv 1 h = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective (variableChangeAlgHom_eq_id 1 h rfl)

/-- **A change of variables is determined by its isomorphism of coordinate rings**: the images of
`x'` and `y'` determine `u²`, `u³`, `r`, `u²s` and `t`, because `x`, `y` and `1` are linearly
independent over `R` in `R[W]`. -/
theorem variableChangeEquiv_inj (h : C • W' = W) (h' : C' • W' = W) :
    variableChangeEquiv C h = variableChangeEquiv C' h' ↔ C = C' := by
  refine ⟨fun he ↦ ?_, fun hC ↦ by subst hC; rfl⟩
  have hX := congr($he (AdjoinRoot.of W'.toAffine.polynomial X))
  have hY := congr($he (AdjoinRoot.root W'.toAffine.polynomial))
  rw [variableChangeEquiv_of_X, variableChangeEquiv_of_X] at hX
  rw [variableChangeEquiv_root, variableChangeEquiv_root] at hY
  -- read off the coefficients of `x`, `y` and `1` from the two coordinate identities
  have hli := Fintype.linearIndependent_iff.mp (linearIndependent_X_root_one (W := W.toAffine))
  have hX' := hli ![(C.u : R) ^ 2 - (C'.u : R) ^ 2, 0, C.r - C'.r] (by
    simp only [Fin.sum_univ_three, Matrix.cons_val, Algebra.smul_def, map_sub, map_pow, map_zero]
    linear_combination hX)
  have hY' := hli ![(C.u : R) ^ 2 * C.s - (C'.u : R) ^ 2 * C'.s, (C.u : R) ^ 3 - (C'.u : R) ^ 3,
    C.t - C'.t] (by
    simp only [Fin.sum_univ_three, Matrix.cons_val, Algebra.smul_def, map_sub, map_pow, map_mul]
    linear_combination hY)
  have hu2 : (C.u : R) ^ 2 = (C'.u : R) ^ 2 := sub_eq_zero.mp (hX' 0)
  have hu3 : (C.u : R) ^ 3 = (C'.u : R) ^ 3 := sub_eq_zero.mp (hY' 1)
  -- `u = u³ / u²`, so `u` is determined, and then so is `s`
  have hu : C.u = C'.u := by
    have hu2' : C.u ^ 2 = C'.u ^ 2 := Units.ext (by simpa using hu2)
    have hu3' : C.u ^ 3 = C'.u ^ 3 := Units.ext (by simpa using hu3)
    calc C.u = C.u ^ 3 * (C.u ^ 2)⁻¹ := by group
      _ = C'.u ^ 3 * (C'.u ^ 2)⁻¹ := by rw [hu2', hu3']
      _ = C'.u := by group
  have hus : (C.u : R) ^ 2 * C.s = (C'.u : R) ^ 2 * C'.s := sub_eq_zero.mp (hY' 0)
  have hs : C.s = C'.s :=
    (C.u.isUnit.pow 2).mul_left_cancel (by linear_combination hus - C'.s * hu2)
  exact VariableChange.ext hu (sub_eq_zero.mp (hX' 2)) hs (sub_eq_zero.mp (hY' 2))

end VariableChangeEquiv

end WeierstrassCurve.Affine.CoordinateRing

end
