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

For `a₁, a₃ : R`, the Weierstrass curve in **`Γ₁(3)` normal form** is

`Y² + a₁XY + a₃Y = X³`,

that is, `a₂ = a₄ = a₆ = 0` (`WeierstrassCurve.gamma1ThreeNormalForm`, requiring only `[Zero R]`).
Over a commutative ring `R`, the origin `(0, 0)` always lies on it
(`equation_gamma1ThreeNormalForm_zero`). When `a₃` is a unit (in particular, `a₃ ≠ 0` over a
field), the defining polynomial `Y² + a₁XY + a₃Y - X³` has partial derivatives `(0, a₃)` at
`(0, 0)`, so `(0, 0)` is a smooth inflection point with horizontal tangent `Y = 0` meeting the
curve to order three (when `Δ` is a unit, the curve is elliptic and `(0, 0)` is a `3`-torsion
point); without assuming `a₃` is a unit, `(0, 0)` may be singular (for example when `a₃ = 0`). Both
the Deuring normal form (`a₃ = 1`) and the full level-three normal form
(`a₁ = 3μ`, `a₃ = μ³ - 1`) specialize it. Its invariants are

`c₄ = a₁⁴ - 24a₁a₃`,  `c₆ = -a₁⁶ + 36a₁³a₃ - 216a₃²`,  `Δ = a₁³a₃³ - 27a₃⁴`.

Under an admissible change of variables `C = (u, r, s, t)` acting on
`W = gamma1ThreeNormalForm a₁ a₃`, the vanishing of the quadratic, linear and constant coefficients
`a₂`, `a₄`, `a₆` of `C • W` cuts out the arrows to another `Γ₁(3)` normal form. For a strict change
`C = (1, r, s, t)` these three coefficients are `3r - s² - a₁s`, `3r² - a₁rs - a₃s - a₁t - 2st` and
`r³ - a₁rt - a₃t - t²` (`WeierstrassCurve.IsStrictGamma1ThreeChange`); in particular, when `3` is
invertible in `R`, the vanishing of `(C • W).a₂` expresses `r` as `(s² + a₁s) / 3`.

## Main definitions

* `WeierstrassCurve.gamma1ThreeNormalForm a₁ a₃`: the curve `Y² + a₁XY + a₃Y = X³`, over any `Zero`.
* `WeierstrassCurve.IsStrictGamma1ThreeChange a₁ a₃ C`: `C` has `u = 1` and carries
  `gamma1ThreeNormalForm a₁ a₃` to another `Γ₁(3)` normal form.

## Main results

* `WeierstrassCurve.gamma1ThreeNormalForm_c₄`, `gamma1ThreeNormalForm_c₆`,
  `gamma1ThreeNormalForm_Δ`: its `c`-invariants and discriminant.
* `WeierstrassCurve.map_gamma1ThreeNormalForm`, `WeierstrassCurve.baseChange_gamma1ThreeNormalForm`:
  compatibility with ring homomorphisms and base change.
* `WeierstrassCurve.eq_gamma1ThreeNormalForm_iff`: a Weierstrass curve is `gamma1ThreeNormalForm` of
  its own `a₁` and `a₃` if and only if `a₂ = a₄ = a₆ = 0`.
* `WeierstrassCurve.strictVariableChange_gamma1ThreeNormalForm_a₁` through `_a₆`: explicit
  coefficients of `⟨1, r, s, t⟩ • gamma1ThreeNormalForm a₁ a₃`.
* `WeierstrassCurve.IsStrictGamma1ThreeChange.one`, `.mul`, `.inv`, `.map`: groupoid and
  base-change closure of strict `Γ₁(3)` variable changes.
* `WeierstrassCurve.r_eq_of_variableChange_gamma1ThreeNormalForm_a₂_eq_zero`: when `3` is
  invertible, `(C • gamma1ThreeNormalForm a₁ a₃).a₂ = 0` forces `C.r = ⅟3 * (C.s² + a₁ * C.s)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Appendix A,
  Proposition 1.3.
* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §7.
* K. Carrick, J. Davies and S. van Nigtevecht, *The descent spectral sequence for topological
  modular forms*, arXiv:2412.01640v2, §4.2.
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

section Invariants

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
theorem equation_gamma1ThreeNormalForm_iff (x y : R) :
    (gamma1ThreeNormalForm a₁ a₃).toAffine.Equation x y ↔
      y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 := by
  rw [Affine.equation_iff]
  simp [gamma1ThreeNormalForm]

/-- The origin `(0, 0)` lies on `gamma1ThreeNormalForm a₁ a₃`. -/
theorem equation_gamma1ThreeNormalForm_zero :
    (gamma1ThreeNormalForm a₁ a₃).toAffine.Equation 0 0 := by
  simp

/-- A pure scaling `⟨u, 0, 0, 0⟩` carries `gamma1ThreeNormalForm a₁ a₃` to
`gamma1ThreeNormalForm (u⁻¹ * a₁) ((u⁻¹) ^ 3 * a₃)`. -/
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

end Invariants

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A change of variables `C` is a **strict `Γ₁(3)` arrow** out of `gamma1ThreeNormalForm a₁ a₃`
when `C.u = 1` and `C • gamma1ThreeNormalForm a₁ a₃` again has `a₂ = a₄ = a₆ = 0`. -/
def IsStrictGamma1ThreeChange (a₁ a₃ : R) (C : VariableChange R) : Prop :=
  C.u = 1 ∧ (C • gamma1ThreeNormalForm a₁ a₃).a₂ = 0 ∧
    (C • gamma1ThreeNormalForm a₁ a₃).a₄ = 0 ∧ (C • gamma1ThreeNormalForm a₁ a₃).a₆ = 0

/-- Explicit unfolding of `IsStrictGamma1ThreeChange`. -/
theorem isStrictGamma1ThreeChange_iff {a₁ a₃ : R} {C : VariableChange R} :
    IsStrictGamma1ThreeChange a₁ a₃ C ↔
      C.u = 1 ∧ (C • gamma1ThreeNormalForm a₁ a₃).a₂ = 0 ∧
        (C • gamma1ThreeNormalForm a₁ a₃).a₄ = 0 ∧ (C • gamma1ThreeNormalForm a₁ a₃).a₆ = 0 :=
  Iff.rfl

/-- Characterization of `IsStrictGamma1ThreeChange a₁ a₃ ⟨1, r, s, t⟩` by the three defining
polynomial equations in `(r, s, t)`. -/
theorem isStrictGamma1ThreeChange_mk_iff {a₁ a₃ r s t : R} :
    IsStrictGamma1ThreeChange a₁ a₃ ⟨1, r, s, t⟩ ↔
      3 * r - s ^ 2 - a₁ * s = 0 ∧
        3 * r ^ 2 - a₁ * r * s - a₃ * s - a₁ * t - 2 * s * t = 0 ∧
        r ^ 3 - a₁ * r * t - a₃ * t - t ^ 2 = 0 := by
  simp [IsStrictGamma1ThreeChange]

namespace IsStrictGamma1ThreeChange

/-- A strict `Γ₁(3)` arrow has `u = 1`. -/
theorem u_eq_one {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C) :
    C.u = 1 :=
  h.1

/-- Acting by a strict `Γ₁(3)` arrow annihilates `a₂`. -/
theorem a₂_eq_zero {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C) :
    (C • gamma1ThreeNormalForm a₁ a₃).a₂ = 0 :=
  h.2.1

/-- Acting by a strict `Γ₁(3)` arrow annihilates `a₄`. -/
theorem a₄_eq_zero {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C) :
    (C • gamma1ThreeNormalForm a₁ a₃).a₄ = 0 :=
  h.2.2.1

/-- Acting by a strict `Γ₁(3)` arrow annihilates `a₆`. -/
theorem a₆_eq_zero {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C) :
    (C • gamma1ThreeNormalForm a₁ a₃).a₆ = 0 :=
  h.2.2.2

/-- A strict `Γ₁(3)` arrow `C` equals `⟨1, C.r, C.s, C.t⟩`. -/
theorem eq_mk {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C) :
    C = ⟨1, C.r, C.s, C.t⟩ :=
  VariableChange.ext h.1 rfl rfl rfl

/-- Acting by a strict `Γ₁(3)` arrow produces `gamma1ThreeNormalForm (a₁ + 2s) (a₃ + a₁r + 2t)`. -/
theorem smul_eq {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C) :
    C • gamma1ThreeNormalForm a₁ a₃ =
      gamma1ThreeNormalForm (a₁ + 2 * C.s) (a₃ + a₁ * C.r + 2 * C.t) := by
  have hW := (eq_gamma1ThreeNormalForm_iff (C • gamma1ThreeNormalForm a₁ a₃)).mpr ⟨h.2.1, h.2.2⟩
  conv_lhs => rw [hW]
  conv_lhs => rw [h.eq_mk]
  simp

/-- The identity change of variables is a strict `Γ₁(3)` arrow. -/
theorem one (a₁ a₃ : R) : IsStrictGamma1ThreeChange a₁ a₃ 1 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp

/-- Strict `Γ₁(3)` arrows are closed under composition. -/
theorem mul {a₁ a₃ : R} {C₁ C₂ : VariableChange R}
    (h₁ : IsStrictGamma1ThreeChange a₁ a₃ C₁)
    (h₂ : IsStrictGamma1ThreeChange (a₁ + 2 * C₁.s) (a₃ + a₁ * C₁.r + 2 * C₁.t) C₂) :
    IsStrictGamma1ThreeChange a₁ a₃ (C₂ * C₁) := by
  refine ⟨by rw [VariableChange.mul_def, h₂.1, h₁.1, mul_one], ?_⟩
  rw [mul_smul, h₁.smul_eq]
  exact h₂.2

/-- The inverse of a strict `Γ₁(3)` arrow is a strict `Γ₁(3)` arrow from its target back to its
source. -/
theorem inv {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C) :
    IsStrictGamma1ThreeChange (a₁ + 2 * C.s) (a₃ + a₁ * C.r + 2 * C.t) C⁻¹ := by
  refine ⟨by simp [VariableChange.inv_def, h.1], ?_⟩
  rw [← h.smul_eq, inv_smul_smul]
  exact ⟨gamma1ThreeNormalForm_a₂ a₁ a₃, gamma1ThreeNormalForm_a₄ a₁ a₃,
    gamma1ThreeNormalForm_a₆ a₁ a₃⟩

/-- Strict `Γ₁(3)` arrows are preserved along ring homomorphisms. -/
theorem map {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGamma1ThreeChange a₁ a₃ C)
    (f : R →+* S) : IsStrictGamma1ThreeChange (f a₁) (f a₃) (C.map f) := by
  refine ⟨by simp [h.1], ?_⟩
  have hsmul : C.map f • gamma1ThreeNormalForm (f a₁) (f a₃) =
      (C • gamma1ThreeNormalForm a₁ a₃).map f := by
    rw [← map_gamma1ThreeNormalForm, map_variableChange]
  rw [hsmul]
  simp [h.2.1, h.2.2.1, h.2.2.2]

end IsStrictGamma1ThreeChange

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
