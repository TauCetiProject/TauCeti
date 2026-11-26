/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Section
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic

/-!
# The Floer section on `W^{1,p}` of the cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space. The Floer operator
(`TauCeti.SymplecticForm.floerOperator`)

`F(u) = ∂s u - X_{K_s}(u) + J(u) (∂t u - X_{K_t}(u))`

is a quasilinear first-order operator `∂s u + A(z, u) ∂t u + G(z, u)` with `A = J` and the
zeroth-order term `G = -X_{K_s} - J X_{K_t}` (`TauCeti.SymplecticForm.floerZerothOrder`;
`TauCeti.SymplecticForm.floerOperator_eq_add_floerZerothOrder`). The **Floer section** around a
reference map `w`, `TauCeti.SymplecticForm.floerSection`, is therefore the quasilinear section
`TauCeti.CylinderSobolev.quasilinearSection` of these coefficients, with `b = ∂t w`: a map from
`W^{1,p}(ℝ × S¹, V)` to `Lᵖ`, for `p > 2`, whose value at a test section `ξ` is
`F(w + ξ) - F(w)` almost everywhere on the strip (`TauCeti.SymplecticForm.floerSection_toW1p_ae`).
Its strict differentiability, with derivative the linearization
`TauCeti.CylinderSobolev.quasilinearLinearization` of these coefficients, is
`TauCeti.CylinderSobolev.hasStrictFDerivAt_quasilinearSection`, applied with `A = J` and
`G = floerZerothOrder`. This is the map to which the implicit function theorem and the
Sard–Smale theorem are applied in the transversality theory of Floer cylinders.

## Main definitions

* `TauCeti.SymplecticForm.floerZerothOrder`: the zeroth-order term `-X_{K_s} - J X_{K_t}` of the
  Floer operator.
* `TauCeti.SymplecticForm.floerSection`: the Floer section `ξ ↦ F(w + ξ) - F(w)` on `W^{1,p}`.

## Main results

* `TauCeti.SymplecticForm.floerOperator_eq_add_floerZerothOrder`: the Floer operator is
  `∂s u + J(u) ∂t u + G(u)`.
* `TauCeti.SymplecticForm.floerSection_toW1p_ae`: on the jet of a test section `ξ`, the Floer
  section is `F(w + ξ) - F(w)`.

## References

* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292, Section 3.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (stripMeasure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The zeroth-order term `G(z, y) = -X_{K_s(z)}(y) - J(z, y) X_{K_t(z)}(y)` of the Floer operator,
which is `∂s u + J(u) ∂t u + G(u)`
(`TauCeti.SymplecticForm.floerOperator_eq_add_floerZerothOrder`). -/
def floerZerothOrder (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (z : ℝ × ℝ) (y : V) : V :=
  -ω.hamiltonianVectorField (Ks z) y - J z y (ω.hamiltonianVectorField (Kt z) y)

/-- The defining formula of the zeroth-order term of the Floer operator. -/
theorem floerZerothOrder_def (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (z : ℝ × ℝ) (y : V) :
    ω.floerZerothOrder J Ks Kt z y =
      -ω.hamiltonianVectorField (Ks z) y - J z y (ω.hamiltonianVectorField (Kt z) y) :=
  (rfl)

/-- **The Floer operator is quasilinear.** It is `∂s u + J(u) ∂t u + G(u)` for the zeroth-order
term `G = -X_{K_s} - J X_{K_t}`. -/
theorem floerOperator_eq_add_floerZerothOrder (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerOperator J Ks Kt u z =
      fderiv ℝ u z (1, 0) + J z (u z) (fderiv ℝ u z (0, 1)) +
        ω.floerZerothOrder J Ks Kt z (u z) := by
  rw [floerOperator_def, floerZerothOrder_def, stdComplexLineReal_eq, stdComplexLineImag_eq,
    map_sub]
  abel

/-- **The Floer section** around a reference map `w`: the quasilinear section
`TauCeti.CylinderSobolev.quasilinearSection` from `W^{1,p}(ℝ × S¹, V)` to `Lᵖ` of the Floer
operator, with coefficients `A = J` and `G = -X_{K_s} - J X_{K_t}` and with `b = ∂t w`. On the jet
of a test section `ξ` it is `F(w + ξ) - F(w)` (`TauCeti.SymplecticForm.floerSection_toW1p_ae`). -/
def floerSection (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (w : ℝ × ℝ → V) (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : W1p V p) : Lp V p stripMeasure :=
  quasilinearSection J (ω.floerZerothOrder J Ks Kt) w (fun z ↦ fderiv ℝ w z (0, 1)) p x

/-- The Floer section is the quasilinear section of the Floer coefficients. -/
theorem floerSection_def (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (w : ℝ × ℝ → V) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ω.floerSection J Ks Kt w p =
      quasilinearSection J (ω.floerZerothOrder J Ks Kt) w (fun z ↦ fderiv ℝ w z (0, 1)) p :=
  (rfl)

/-- **The Floer section on test sections is the change of the Floer operator.** Let `2 < p < ∞`,
let `w` be differentiable with `∂t w` bounded, and let `J` and the zeroth-order term
`G = -X_{K_s} - J X_{K_t}` be continuous in `(z, y)` and Lipschitz in `y` uniformly in `z`, with
`J` bounded. Then on the jet of a test section `ξ` the Floer section is almost everywhere
`F(w + ξ) - F(w)`. -/
theorem floerSection_toW1p_ae {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 < p) (hpt : p ≠ ∞)
    {ω : SymplecticForm V} {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {w : ℝ × ℝ → V} (hJc : Continuous (Function.uncurry J))
    (hGc : Continuous (Function.uncurry (ω.floerZerothOrder J Ks Kt)))
    (hw : Differentiable ℝ w)
    (hwt : AEStronglyMeasurable (fun z ↦ fderiv ℝ w z (0, 1)) stripMeasure) {B C : ℝ}
    {K L : ℝ≥0} (hwB : ∀ z, ‖fderiv ℝ w z (0, 1)‖ ≤ B) (hJC : ∀ z y, ‖J z y‖ ≤ C)
    (hJL : ∀ z, LipschitzWith K (J z)) (hGL : ∀ z, LipschitzWith L (ω.floerZerothOrder J Ks Kt z))
    (ξ : testSection V) :
    ω.floerSection J Ks Kt w p (toW1p p ξ) =ᵐ[stripMeasure] fun z ↦
      ω.floerOperator J Ks Kt (w + ξ) z - ω.floerOperator J Ks Kt w z := by
  have hξ : Differentiable ℝ (ξ : ℝ × ℝ → V) :=
    (mem_testSection_iff.1 ξ.property).1.differentiable (by norm_num)
  filter_upwards [quasilinearSection_toW1p_ae hp hpt hJc hGc hw.continuous.aestronglyMeasurable
    hwt hwB hJC hJL hGL ξ] with z hz
  rw [floerSection_def, hz, floerOperator_eq_add_floerZerothOrder,
    floerOperator_eq_add_floerZerothOrder, fderiv_add (hw z) (hξ z), Pi.add_apply]
  simp only [add_apply, map_add]
  abel

end TauCeti.SymplecticForm
