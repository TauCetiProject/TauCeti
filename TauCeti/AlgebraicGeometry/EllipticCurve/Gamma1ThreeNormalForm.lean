/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The `Γ₁(3)` normal form `Y² + a₁XY + a₃Y = X³`

For `a₁, a₃ : R`, the Weierstrass curve in **`Γ₁(3)` normal form** (the Hessian or Tate normal form
at an inflection point) is

`Y² + a₁XY + a₃Y = X³`,

that is, `a₂ = a₄ = a₆ = 0` (`WeierstrassCurve.gamma1ThreeNormalForm`). The origin `(0, 0)` lies on
it with horizontal tangent `Y = 0` meeting the curve to order three; both the Deuring normal form
(`a₃ = 1`) and the full level-three normal form (`a₁ = 3μ`, `a₃ = μ³ - 1`) specialize it. Its
invariants are

`c₄ = a₁⁴ - 24a₁a₃`,  `c₆ = -a₁⁶ + 36a₁³a₃ - 216a₃²`,  `Δ = a₁³a₃³ - 27a₃⁴`.

Under an admissible change of variables `C = (u, r, s, t)` acting on
`W = gamma1ThreeNormalForm a₁ a₃`, the vanishing of the quadratic, linear and constant coefficients
`a₂`, `a₄`, `a₆` of `C • W` cuts out the arrows to another `Γ₁(3)` normal form. For a strict change
`C = (1, r, s, t)` these three coefficients are `3r - s² - a₁s`,
`3r² - a₁rs - a₃s - a₁t - 2st` and `r³ - a₁rt - a₃t - t²`; in particular, when `3` is invertible
in `R`, the vanishing of `(C • W).a₂` expresses `r` as `(s² + a₁s) / 3`.

## Main definitions

* `WeierstrassCurve.gamma1ThreeNormalForm a₁ a₃`: the curve `Y² + a₁XY + a₃Y = X³`, over any `Zero`.

## Main results

* `WeierstrassCurve.gamma1ThreeNormalForm_c₄`, `gamma1ThreeNormalForm_c₆`,
  `gamma1ThreeNormalForm_Δ`: its `c`-invariants and discriminant.
* `WeierstrassCurve.map_gamma1ThreeNormalForm`, `WeierstrassCurve.baseChange_gamma1ThreeNormalForm`:
  compatibility with ring homomorphisms and base change.
* `WeierstrassCurve.eq_gamma1ThreeNormalForm_iff`: a Weierstrass curve is `gamma1ThreeNormalForm` of
  its own `a₁` and `a₃` if and only if `a₂ = a₄ = a₆ = 0`.
* `WeierstrassCurve.strictVariableChange_gamma1ThreeNormalForm_a₁` through `_a₆`: explicit
  coefficients of `⟨1, r, s, t⟩ • gamma1ThreeNormalForm a₁ a₃`.
* `WeierstrassCurve.r_eq_of_variableChange_gamma1ThreeNormalForm_a₂_eq_zero`: when `3` is
  invertible, `(C • gamma1ThreeNormalForm a₁ a₃).a₂ = 0` forces `C.r = ⅟3 * (C.s² + a₁ * C.s)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Appendix A,
  Proposition 1.3.
* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §7.
* K. Carrick, J. Davies and S. van Nigtevecht, *Topological modular forms with level structure:
  deformations, transfers, and differentials*, §4.2.
-/

public section

namespace WeierstrassCurve

section Zero

variable {R : Type*} [Zero R] (a₁ a₃ : R)

/-- The Weierstrass curve `Y² + a₁XY + a₃Y = X³` in **`Γ₁(3)` normal form**: `a₂ = a₄ = a₆ = 0`.
Only `Zero R` is required to state its five coefficients. -/
def gamma1ThreeNormalForm : WeierstrassCurve R where
  a₁ := a₁
  a₂ := 0
  a₃ := a₃
  a₄ := 0
  a₆ := 0

@[simp] theorem gamma1ThreeNormalForm_a₁ : (gamma1ThreeNormalForm a₁ a₃).a₁ = a₁ := (rfl)

@[simp] theorem gamma1ThreeNormalForm_a₂ : (gamma1ThreeNormalForm a₁ a₃).a₂ = 0 := (rfl)

@[simp] theorem gamma1ThreeNormalForm_a₃ : (gamma1ThreeNormalForm a₁ a₃).a₃ = a₃ := (rfl)

@[simp] theorem gamma1ThreeNormalForm_a₄ : (gamma1ThreeNormalForm a₁ a₃).a₄ = 0 := (rfl)

@[simp] theorem gamma1ThreeNormalForm_a₆ : (gamma1ThreeNormalForm a₁ a₃).a₆ = 0 := (rfl)

/-- A Weierstrass curve is `gamma1ThreeNormalForm` of its own `a₁` and `a₃` if and only if
`a₂ = a₄ = a₆ = 0`. -/
theorem eq_gamma1ThreeNormalForm_iff (W : WeierstrassCurve R) :
    W = gamma1ThreeNormalForm W.a₁ W.a₃ ↔ W.a₂ = 0 ∧ W.a₄ = 0 ∧ W.a₆ = 0 :=
  ⟨fun h ↦ by rw [h]; exact ⟨rfl, rfl, rfl⟩,
    fun ⟨h₂, h₄, h₆⟩ ↦ WeierstrassCurve.ext rfl h₂ rfl h₄ h₆⟩

end Zero

variable {R S : Type*} [CommRing R] [CommRing S] (a₁ a₃ : R)

/-- A ring homomorphism carries `gamma1ThreeNormalForm` to `gamma1ThreeNormalForm` on the images
of the coefficients. -/
@[simp]
theorem map_gamma1ThreeNormalForm (f : R →+* S) :
    (gamma1ThreeNormalForm a₁ a₃).map f = gamma1ThreeNormalForm (f a₁) (f a₃) := by
  ext <;> simp [WeierstrassCurve.map]

/-- Base change carries `gamma1ThreeNormalForm` to `gamma1ThreeNormalForm` on the algebra images
of the coefficients. Stated separately from `map_gamma1ThreeNormalForm` because `simp` does not
unfold `baseChange`. -/
@[simp]
theorem baseChange_gamma1ThreeNormalForm [Algebra R S] :
    (gamma1ThreeNormalForm a₁ a₃).baseChange S =
      gamma1ThreeNormalForm (algebraMap R S a₁) (algebraMap R S a₃) :=
  map_gamma1ThreeNormalForm a₁ a₃ _

@[simp]
theorem gamma1ThreeNormalForm_b₂ : (gamma1ThreeNormalForm a₁ a₃).b₂ = a₁ ^ 2 := by
  simp [b₂, sq]

@[simp]
theorem gamma1ThreeNormalForm_b₄ : (gamma1ThreeNormalForm a₁ a₃).b₄ = a₁ * a₃ := by
  simp [b₄]

@[simp]
theorem gamma1ThreeNormalForm_b₆ : (gamma1ThreeNormalForm a₁ a₃).b₆ = a₃ ^ 2 := by
  simp [b₆, sq]

@[simp]
theorem gamma1ThreeNormalForm_b₈ : (gamma1ThreeNormalForm a₁ a₃).b₈ = 0 := by
  simp [b₈]

/-- The invariant `c₄` of `Y² + a₁XY + a₃Y = X³` is `a₁⁴ - 24a₁a₃`. -/
@[simp]
theorem gamma1ThreeNormalForm_c₄ :
    (gamma1ThreeNormalForm a₁ a₃).c₄ = a₁ ^ 4 - 24 * a₁ * a₃ := by
  rw [c₄, gamma1ThreeNormalForm_b₂, gamma1ThreeNormalForm_b₄]
  ring

/-- The invariant `c₆` of `Y² + a₁XY + a₃Y = X³` is `-a₁⁶ + 36a₁³a₃ - 216a₃²`. -/
@[simp]
theorem gamma1ThreeNormalForm_c₆ :
    (gamma1ThreeNormalForm a₁ a₃).c₆ = -a₁ ^ 6 + 36 * a₁ ^ 3 * a₃ - 216 * a₃ ^ 2 := by
  rw [c₆, gamma1ThreeNormalForm_b₂, gamma1ThreeNormalForm_b₄, gamma1ThreeNormalForm_b₆]
  ring

/-- The discriminant `Δ` of `Y² + a₁XY + a₃Y = X³` is `a₁³a₃³ - 27a₃⁴`. -/
@[simp]
theorem gamma1ThreeNormalForm_Δ :
    (gamma1ThreeNormalForm a₁ a₃).Δ = a₁ ^ 3 * a₃ ^ 3 - 27 * a₃ ^ 4 := by
  rw [Δ, gamma1ThreeNormalForm_b₂, gamma1ThreeNormalForm_b₄, gamma1ThreeNormalForm_b₆,
    gamma1ThreeNormalForm_b₈]
  ring

/-- A point `(x, y)` lies on `gamma1ThreeNormalForm a₁ a₃` if and only if
`y² + a₁xy + a₃y = x³`. -/
@[simp]
theorem gamma1ThreeNormalForm_equation_iff (x y : R) :
    (gamma1ThreeNormalForm a₁ a₃).toAffine.Equation x y ↔
      y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 := by
  rw [Affine.equation_iff]
  simp [gamma1ThreeNormalForm]

/-- The origin `(0, 0)` lies on `gamma1ThreeNormalForm a₁ a₃`. -/
theorem gamma1ThreeNormalForm_equation_zero :
    (gamma1ThreeNormalForm a₁ a₃).toAffine.Equation 0 0 := by
  simp

/-- A pure scaling `⟨u, 0, 0, 0⟩` carries `gamma1ThreeNormalForm a₁ a₃` to
`gamma1ThreeNormalForm (u⁻¹ * a₁) (u⁻¹³ * a₃)`. -/
@[simp]
theorem smul_gamma1ThreeNormalForm (u : Rˣ) :
    (⟨u, 0, 0, 0⟩ : VariableChange R) • gamma1ThreeNormalForm a₁ a₃ =
      gamma1ThreeNormalForm (↑u⁻¹ * a₁) (↑u⁻¹ ^ 3 * a₃) := by
  ext <;> simp [variableChange_def]

/-! ### Action of strict changes of variables `⟨1, r, s, t⟩` -/

section StrictVariableChange

variable (r s t : R)

@[simp]
theorem strictVariableChange_gamma1ThreeNormalForm_a₁ :
    ((⟨1, r, s, t⟩ : VariableChange R) • gamma1ThreeNormalForm a₁ a₃).a₁ = a₁ + 2 * s := by
  simp [variableChange_a₁]

@[simp]
theorem strictVariableChange_gamma1ThreeNormalForm_a₂ :
    ((⟨1, r, s, t⟩ : VariableChange R) • gamma1ThreeNormalForm a₁ a₃).a₂ =
      3 * r - s ^ 2 - a₁ * s := by
  simp [variableChange_a₂]
  ring

@[simp]
theorem strictVariableChange_gamma1ThreeNormalForm_a₃ :
    ((⟨1, r, s, t⟩ : VariableChange R) • gamma1ThreeNormalForm a₁ a₃).a₃ =
      a₃ + a₁ * r + 2 * t := by
  simp [variableChange_a₃]
  ring

@[simp]
theorem strictVariableChange_gamma1ThreeNormalForm_a₄ :
    ((⟨1, r, s, t⟩ : VariableChange R) • gamma1ThreeNormalForm a₁ a₃).a₄ =
      3 * r ^ 2 - a₁ * r * s - a₃ * s - a₁ * t - 2 * s * t := by
  simp [variableChange_a₄]
  ring

@[simp]
theorem strictVariableChange_gamma1ThreeNormalForm_a₆ :
    ((⟨1, r, s, t⟩ : VariableChange R) • gamma1ThreeNormalForm a₁ a₃).a₆ =
      r ^ 3 - a₁ * r * t - a₃ * t - t ^ 2 := by
  simp [variableChange_a₆]
  ring

end StrictVariableChange

/-- When `3` is invertible in `R`, any change of variables `C` annihilating `a₂` on
`gamma1ThreeNormalForm a₁ a₃` has `C.r = ⅟3 * (C.s² + a₁ * C.s)`. -/
theorem r_eq_of_variableChange_gamma1ThreeNormalForm_a₂_eq_zero [Invertible (3 : R)]
    {a₁ a₃ : R} {C : VariableChange R}
    (h₂ : (C • gamma1ThreeNormalForm a₁ a₃).a₂ = 0) :
    C.r = ⅟(3 : R) * (C.s ^ 2 + a₁ * C.s) := by
  rw [variableChange_a₂, gamma1ThreeNormalForm_a₁, gamma1ThreeNormalForm_a₂,
    (C.u⁻¹.isUnit.pow 2).mul_right_eq_zero] at h₂
  linear_combination ⅟(3 : R) * h₂ - C.r * invOf_mul_self (3 : R)

end WeierstrassCurve

end
