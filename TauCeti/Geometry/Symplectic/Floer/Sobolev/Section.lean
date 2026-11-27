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
`W^{1,p}(ℝ × S¹, V)` to `Lᵖ`, for `p > 2`. When `2 < p < ∞`, `J` and `G` are continuous in
`(z, y)`, `w` is differentiable, `∂t w` and `J` are bounded, and `J` and `G` are Lipschitz in `y`
uniformly in `z`, its value at a test section `ξ` is `F(w + ξ) - F(w)` almost everywhere on the
strip (`TauCeti.SymplecticForm.floerSection_toW1p_ae`).
If moreover `J` and `G` are differentiable in `y`, with bounded, jointly continuous derivatives
`J'`, `G'` that are uniformly equicontinuous, it is strictly differentiable, with derivative the
linearization
`TauCeti.CylinderSobolev.quasilinearLinearization` of these coefficients
(`TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection`).

Under the hypotheses of `TauCeti.SymplecticForm.floerSection_apply_ae` (`∂t w` and `J` bounded,
`J` and `G` Lipschitz in `y` uniformly in `z`), the Floer section is everywhere given by its
pointwise formula; outside them it may take the junk value `0`. Under these hypotheses, with `w`
differentiable, the zeros of the Floer section are the `ξ` in `W^{1,p}` for which `u = w + ξ` is a
weak solution of `F(u) = F(w)`: the equation holds almost everywhere with the weak derivatives
`ξ_s`, `ξ_t` of `ξ` in place of its classical derivatives. Agreement with
`TauCeti.SymplecticForm.floerOperator` is proved only on test sections
(`TauCeti.SymplecticForm.floerSection_toW1p_ae`). When the reference map is itself a Floer
cylinder, `F(w) = 0`, these zeros are the weak solutions of the Floer equation near `w`. By the
pointwise formula `TauCeti.SymplecticForm.floerSection_apply_ae`, such a zero satisfies the Floer
equation for `u = w + ξ` almost everywhere, so for periodic `w`, `J` of class `C^ℓ` and `Ks`, `Kt`
of class `C^(ℓ+1)`, with `J(z, u z)² = -1`, elliptic regularity makes `u` of class `C^ℓ`
(`TauCeti.SymplecticForm.contDiff_add_continuousValue_of_ae_floer`). The Floer section is the
map to which the implicit function theorem and the Sard–Smale theorem are applied in the
transversality theory of Floer cylinders. For a reference map with `F(w)` in `Lᵖ`, such as a
pre-glued map, the Floer section plus the constant `F(w)` agrees with `ξ ↦ F(w + ξ)` on test
sections, and has the same derivative.

## Main definitions

* `TauCeti.SymplecticForm.floerSection`: the quasilinear section with `A = J`,
  `G = floerZerothOrder` and `b = ∂t w`; under the hypotheses of
  `TauCeti.SymplecticForm.floerSection_toW1p_ae`, on test sections it equals `F(w + ξ) - F(w)`
  almost everywhere.

## Main results

* `TauCeti.SymplecticForm.floerSection_apply_ae`: the pointwise formula of the Floer section.
* `TauCeti.SymplecticForm.floerSection_zero`: it vanishes at the reference map.
* `TauCeti.SymplecticForm.floerSection_toW1p_ae`: under bounds on the coefficients, on the jet of
  a test section `ξ` the Floer section is `F(w + ξ) - F(w)` almost everywhere.
* `TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection`: for coefficients differentiable in `y`
  with bounded, continuous, uniformly equicontinuous derivatives, the Floer section is strictly
  differentiable, with derivative the linearization of the Floer coefficients.

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

/-- **The Floer section** around a reference map `w`: the quasilinear section
`TauCeti.CylinderSobolev.quasilinearSection` from `W^{1,p}(ℝ × S¹, V)` to `Lᵖ` of the Floer
operator, with coefficients `A = J` and `G = -X_{K_s} - J X_{K_t}` and with `b = ∂t w`. Under the
hypotheses of `TauCeti.SymplecticForm.floerSection_toW1p_ae` (`2 < p < ∞`, `J` and `G` continuous
in `(z, y)`, `w` differentiable, `∂t w` and `J` bounded, `J` and `G` Lipschitz in `y`), on the jet
of a test section `ξ` it is almost everywhere
`F(w + ξ) - F(w)`. When the pointwise expression of the section does not lie in `Lᵖ`, its value is
`0`. -/
def floerSection (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (w : ℝ × ℝ → V) (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : W1p V p) : Lp V p stripMeasure :=
  quasilinearSection J (ω.floerZerothOrder J Ks Kt) w (fun z ↦ fderiv ℝ w z (0, 1)) p x

/-- The Floer section is the quasilinear section of the Floer coefficients. -/
theorem floerSection_def (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (w : ℝ × ℝ → V) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ω.floerSection J Ks Kt w p =
      quasilinearSection J (ω.floerZerothOrder J Ks Kt) w (fun z ↦ fderiv ℝ w z (0, 1)) p :=
  (rfl)

/-- The Floer section vanishes at the reference map. -/
@[simp]
theorem floerSection_zero (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (w : ℝ × ℝ → V) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ω.floerSection J Ks Kt w p 0 = 0 :=
  quasilinearSection_zero

/-- The `t`-derivative `∂t w` of any map `w` is measurable on the strip, which supplies the
measurability of the coefficient `b = ∂t w` of the Floer section. -/
private theorem aestronglyMeasurable_fderiv_apply (w : ℝ × ℝ → V) :
    AEStronglyMeasurable (fun z ↦ fderiv ℝ w z (0, 1)) stripMeasure := by
  borelize V
  exact (measurable_fderiv_apply_const ℝ w (0, 1)).aestronglyMeasurable

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {ω : SymplecticForm V} {J : ℝ × ℝ → V → V →L[ℝ] V}
  {Ks Kt : ℝ × ℝ → V → ℝ} {w : ℝ × ℝ → V}

/-- **The pointwise formula of the Floer section.** Let `2 < p < ∞`, let `∂t w` be bounded, and
let `J` and the zeroth-order term `G = -X_{K_s} - J X_{K_t}` be continuous in `(z, y)` and
Lipschitz in `y` uniformly in `z`, with `J` bounded. Then the Floer section at
`x = (ξ, ξ_s, ξ_t)` is almost everywhere
`ξ_s + J(w + ξ) (∂t w + ξ_t) - J(w) ∂t w + G(w + ξ) - G(w)`. -/
theorem floerSection_apply_ae (hp : 2 < p) (hpt : p ≠ ∞)
    (hJc : Continuous (Function.uncurry J))
    (hGc : Continuous (Function.uncurry (ω.floerZerothOrder J Ks Kt)))
    (hw : AEStronglyMeasurable w stripMeasure) {B C : ℝ} {K L : ℝ≥0}
    (hwB : ∀ z, ‖fderiv ℝ w z (0, 1)‖ ≤ B) (hJC : ∀ z y, ‖J z y‖ ≤ C)
    (hJL : ∀ z, LipschitzWith K (J z)) (hGL : ∀ z, LipschitzWith L (ω.floerZerothOrder J Ks Kt z))
    (x : W1p V p) :
    ω.floerSection J Ks Kt w p x =ᵐ[stripMeasure] fun z ↦
      ((x : Lp (V × V × V) p stripMeasure) z).2.1 +
        (J z (w z + continuousValue p x z)
            (fderiv ℝ w z (0, 1) + ((x : Lp (V × V × V) p stripMeasure) z).2.2) -
          J z (w z) (fderiv ℝ w z (0, 1))) +
        (ω.floerZerothOrder J Ks Kt z (w z + continuousValue p x z) -
          ω.floerZerothOrder J Ks Kt z (w z)) :=
  quasilinearSection_apply_ae hp hpt hJc hGc hw (aestronglyMeasurable_fderiv_apply w) hwB hJC hJL
    hGL x

/-- **The Floer section on test sections is the change of the Floer operator.** Let `2 < p < ∞`,
let `w` be differentiable with `∂t w` bounded, and let `J` and the zeroth-order term
`G = -X_{K_s} - J X_{K_t}` be continuous in `(z, y)` and Lipschitz in `y` uniformly in `z`, with
`J` bounded. Then on the jet of a test section `ξ` the Floer section is almost everywhere
`F(w + ξ) - F(w)`. -/
theorem floerSection_toW1p_ae (hp : 2 < p) (hpt : p ≠ ∞) (hJc : Continuous (Function.uncurry J))
    (hGc : Continuous (Function.uncurry (ω.floerZerothOrder J Ks Kt)))
    (hw : Differentiable ℝ w) {B C : ℝ} {K L : ℝ≥0} (hwB : ∀ z, ‖fderiv ℝ w z (0, 1)‖ ≤ B)
    (hJC : ∀ z y, ‖J z y‖ ≤ C) (hJL : ∀ z, LipschitzWith K (J z))
    (hGL : ∀ z, LipschitzWith L (ω.floerZerothOrder J Ks Kt z)) (ξ : testSection V) :
    ω.floerSection J Ks Kt w p (toW1p p ξ) =ᵐ[stripMeasure] fun z ↦
      ω.floerOperator J Ks Kt (w + ξ) z - ω.floerOperator J Ks Kt w z := by
  have hξ : Differentiable ℝ (ξ : ℝ × ℝ → V) :=
    (mem_testSection_iff.1 ξ.property).1.differentiable (by norm_num)
  filter_upwards [quasilinearSection_toW1p_ae hp hpt hJc hGc hw.continuous.aestronglyMeasurable
    (aestronglyMeasurable_fderiv_apply w) hwB hJC hJL hGL ξ] with z hz
  rw [floerSection_def, hz, floerOperator_eq_add_floerZerothOrder,
    floerOperator_eq_add_floerZerothOrder, fderiv_add (hw z) (hξ z), Pi.add_apply]
  simp only [add_apply, map_add]
  abel

/-- **The Floer section is strictly differentiable.** Let `2 < p < ∞` and let `∂t w` be bounded.
Let `J` and the zeroth-order term `G = -X_{K_s} - J X_{K_t}` be differentiable in `y`, with
derivatives `J'` and `G'` that are bounded and uniformly continuous in `y` uniformly in `z`, and
let `J`, `J'`, `G`, `G'` be continuous in `(z, y)`, with `J` bounded. Then the Floer section is
strictly differentiable at every `x₀ ∈ W^{1,p}(ℝ × S¹, V)`, with derivative the linearization
`TauCeti.CylinderSobolev.quasilinearLinearization` of the Floer coefficients at `x₀`. -/
theorem hasStrictFDerivAt_floerSection (hp : 2 < p) (hpt : p ≠ ∞)
    {J' : ℝ × ℝ → V → V →L[ℝ] V →L[ℝ] V} {G' : ℝ × ℝ → V → V →L[ℝ] V}
    (hJc : Continuous (Function.uncurry J))
    (hGc : Continuous (Function.uncurry (ω.floerZerothOrder J Ks Kt)))
    (hJ'c : Continuous (Function.uncurry J')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w stripMeasure) {B C : ℝ} {K L : ℝ≥0}
    (hwB : ∀ z, ‖fderiv ℝ w z (0, 1)‖ ≤ B) (hJC : ∀ z y, ‖J z y‖ ≤ C)
    (hJ : ∀ z y, HasFDerivAt (J z) (J' z y) y) (hJ'K : ∀ z y, ‖J' z y‖ ≤ K)
    (hJ'u : UniformEquicontinuous J')
    (hG : ∀ z y, HasFDerivAt (ω.floerZerothOrder J Ks Kt z) (G' z y) y)
    (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (hG'u : UniformEquicontinuous G') (x₀ : W1p V p) :
    HasStrictFDerivAt (ω.floerSection J Ks Kt w p)
      (quasilinearLinearization J J' G' w (fun z ↦ fderiv ℝ w z (0, 1)) p x₀) x₀ := by
  rw [floerSection_def]
  exact hasStrictFDerivAt_quasilinearSection hp hpt hJc hGc hJ'c hG'c hw
    (aestronglyMeasurable_fderiv_apply w) hwB hJC hJ hJ'K hJ'u hG hG'K hG'u x₀

end TauCeti.SymplecticForm
