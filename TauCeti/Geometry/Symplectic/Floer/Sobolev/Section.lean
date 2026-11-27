/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.QuasilinearSection
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic

/-!
# The Floer section on spaces of `W^{1,p}` jets

Let `(V, ω)` be a finite-dimensional symplectic vector space. The Floer operator
(`TauCeti.SymplecticForm.floerOperator`)

`F(u) = ∂s u - X_{K_s}(u) + J(u) (∂t u - X_{K_t}(u))`

is a quasilinear first-order operator `∂s u + A(z, u) ∂t u + G(z, u)` with `A = J` and the
zeroth-order term `G = -X_{K_s} - J X_{K_t}` (`TauCeti.SymplecticForm.floerZerothOrder`;
`TauCeti.SymplecticForm.floerOperator_eq_add_floerZerothOrder`). The **Floer section** around a
reference map `w`, `TauCeti.SymplecticForm.floerSection`, is therefore the quasilinear section
`TauCeti.quasilinearSection` of these coefficients, with `b = ∂t w`. It is defined on any space `X`
of `Lᵖ(μ)` jets `(ξ, ξ_s, ξ_t)` whose values have continuous representatives
`e : X →L[ℝ] (ℝ × ℝ →ᵇ V)`. For `2 < p < ∞` the Sobolev embedding supplies them on
`W^{1,p}(ℝ × S¹, V)` of the cylinder (`TauCeti.CylinderSobolev.continuousValue`) and on
`W^{1,p}_F(ℝ × [0, 1], V)` of the strip with boundary values in subspaces `F₀`, `F₁`
(`TauCeti.StripSobolev.continuousValueIccExtend`). For a reference map with `F(w) = 0`, the zeros of
the section are the weak solutions of the Floer equation near `w`: cylinders, respectively strips
with boundary on `w + F₀` and `w + F₁`, which with `K_s = 0` and `K_t = H` solve
`∂s u + J(u) (∂t u - X_H(u)) = 0` weakly, the linear model of the strips of Lagrangian Floer
homology.

When `J` and `G` are continuous in `(z, y)`, `w` is differentiable, `∂t w` and `J` are bounded,
and `J` and `G` are Lipschitz in `y` uniformly in `z`, its value at the jet of a differentiable
section `ξ` is `F(w + ξ) - F(w)` almost everywhere
(`TauCeti.SymplecticForm.floerSection_ae_eq_of_ae_eq_jet`).
If moreover `J` and `G` are differentiable in `y`, with bounded, jointly continuous derivatives
`J'`, `G'` that are uniformly equicontinuous, it is strictly differentiable, with derivative the
linearization `TauCeti.quasilinearLinearization` of these coefficients
(`TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection`).

Under the hypotheses of `TauCeti.SymplecticForm.floerSection_apply_ae` (`∂t w` and `J` bounded,
`J` and `G` Lipschitz in `y` uniformly in `z`), the Floer section is everywhere given by its
pointwise formula; outside them it may take the junk value `0`. Under these hypotheses, with `w`
differentiable, the zeros of the Floer section are the `x = (ξ, ξ_s, ξ_t)` in `X` for which
`u = w + ξ` is a weak solution of `F(u) = F(w)`: the equation holds almost everywhere with the weak
derivatives `ξ_s`, `ξ_t` of `ξ` in place of its classical derivatives. Agreement with
`TauCeti.SymplecticForm.floerOperator` is proved only on jets of differentiable sections
(`TauCeti.SymplecticForm.floerSection_ae_eq_of_ae_eq_jet`). When the reference map is itself a
Floer cylinder or strip, `F(w) = 0`, these zeros are the weak solutions of the Floer equation near
`w`; that they are classical solutions is elliptic regularity, which is not proved here. The Floer
section is the map to which the implicit function theorem and the Sard–Smale theorem are applied in
the transversality theory of Floer cylinders and strips. For a reference map with `F(w)` in `Lᵖ`,
such as a pre-glued map, the Floer section plus the constant `F(w)` agrees with `ξ ↦ F(w + ξ)` on
jets of differentiable sections, and has the same derivative.

## Main definitions

* `TauCeti.SymplecticForm.floerSection`: the quasilinear section with `A = J`,
  `G = floerZerothOrder` and `b = ∂t w`; under the hypotheses of
  `TauCeti.SymplecticForm.floerSection_ae_eq_of_ae_eq_jet`, on jets of differentiable sections it
  equals `F(w + ξ) - F(w)` almost everywhere.

## Main results

* `TauCeti.SymplecticForm.floerSection_apply_ae`: the pointwise formula of the Floer section.
* `TauCeti.SymplecticForm.floerSection_zero`: it vanishes at the reference map.
* `TauCeti.SymplecticForm.floerSection_ae_eq_of_ae_eq_jet`: under bounds on the coefficients, on
  the jet of a differentiable section `ξ` the Floer section is `F(w + ξ) - F(w)` almost everywhere.
* `TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection`: for coefficients differentiable in `y`
  with bounded, continuous, uniformly equicontinuous derivatives, the Floer section is strictly
  differentiable, with derivative the linearization of the Floer coefficients.

## References

* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292, Section 3.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1.
* D. Auroux, *A beginner's introduction to Fukaya categories*, in *Contact and Symplectic
  Topology*, Bolyai Soc. Math. Stud. 26 (2014), §1.2, on Floer strips with Lagrangian boundary.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti.SymplecticForm

open StripSobolev (jet)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure (ℝ × ℝ)} {X : Submodule ℝ (Lp (V × V × V) p μ)}

/-- **The Floer section** around a reference map `w`, on a space `X` of `Lᵖ(μ)` jets whose values
have the continuous representatives `e`: the quasilinear section `TauCeti.quasilinearSection` from
`X` to `Lᵖ(μ)` of the Floer operator, with coefficients `A = J` and `G = -X_{K_s} - J X_{K_t}` and
with `b = ∂t w`. Under the hypotheses of `TauCeti.SymplecticForm.floerSection_ae_eq_of_ae_eq_jet`
(`J` and `G` continuous in `(z, y)`, `w` differentiable, `∂t w` and `J` bounded, `J` and `G`
Lipschitz in `y`), on the jet of a differentiable section `ξ` it is almost everywhere
`F(w + ξ) - F(w)`. When the pointwise expression of the section does not lie in `Lᵖ`, its value is
`0`. -/
def floerSection (ω : SymplecticForm V) (e : X →L[ℝ] (ℝ × ℝ →ᵇ V))
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (w : ℝ × ℝ → V) (x : X) : Lp V p μ :=
  quasilinearSection e J (ω.floerZerothOrder J Ks Kt) w (fun z ↦ fderiv ℝ w z (0, 1)) x

/-- The Floer section is the quasilinear section of the Floer coefficients. -/
theorem floerSection_def (ω : SymplecticForm V) (e : X →L[ℝ] (ℝ × ℝ →ᵇ V))
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (w : ℝ × ℝ → V) :
    ω.floerSection e J Ks Kt w =
      quasilinearSection e J (ω.floerZerothOrder J Ks Kt) w (fun z ↦ fderiv ℝ w z (0, 1)) :=
  (rfl)

/-- The Floer section vanishes at the reference map. -/
@[simp]
theorem floerSection_zero (ω : SymplecticForm V) (e : X →L[ℝ] (ℝ × ℝ →ᵇ V))
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (w : ℝ × ℝ → V) :
    ω.floerSection e J Ks Kt w 0 = 0 :=
  quasilinearSection_zero

/-- The `t`-derivative `∂t w` of any map `w` is measurable, which supplies the measurability of
the coefficient `b = ∂t w` of the Floer section. -/
private theorem aestronglyMeasurable_fderiv_apply (w : ℝ × ℝ → V) :
    AEStronglyMeasurable (fun z ↦ fderiv ℝ w z (0, 1)) μ := by
  borelize V
  exact (measurable_fderiv_apply_const ℝ w (0, 1)).aestronglyMeasurable

variable {ω : SymplecticForm V} {e : X →L[ℝ] (ℝ × ℝ →ᵇ V)} {J : ℝ × ℝ → V → V →L[ℝ] V}
  {Ks Kt : ℝ × ℝ → V → ℝ} {w : ℝ × ℝ → V}

/-- **The pointwise formula of the Floer section.** Let `e` give continuous representatives of the
values of the elements of `X`, let `∂t w` be bounded, and let `J` and the zeroth-order term
`G = -X_{K_s} - J X_{K_t}` be continuous in `(z, y)` and Lipschitz in `y` uniformly in `z`, with
`J` bounded. Then the Floer section at `x = (ξ, ξ_s, ξ_t)` is almost everywhere
`ξ_s + J(w + ξ) (∂t w + ξ_t) - J(w) ∂t w + G(w + ξ) - G(w)`, with `ξ` read through `e x`. -/
theorem floerSection_apply_ae
    (he : ∀ x : X, ∀ᵐ z ∂μ, ((x : Lp (V × V × V) p μ) z).1 = e x z)
    (hJc : Continuous (Function.uncurry J))
    (hGc : Continuous (Function.uncurry (ω.floerZerothOrder J Ks Kt)))
    (hw : AEStronglyMeasurable w μ) {B C : ℝ} {K L : ℝ≥0}
    (hwB : ∀ z, ‖fderiv ℝ w z (0, 1)‖ ≤ B) (hJC : ∀ z y, ‖J z y‖ ≤ C)
    (hJL : ∀ z, LipschitzWith K (J z)) (hGL : ∀ z, LipschitzWith L (ω.floerZerothOrder J Ks Kt z))
    (x : X) :
    ω.floerSection e J Ks Kt w x =ᵐ[μ] fun z ↦
      ((x : Lp (V × V × V) p μ) z).2.1 +
        (J z (w z + e x z) (fderiv ℝ w z (0, 1) + ((x : Lp (V × V × V) p μ) z).2.2) -
          J z (w z) (fderiv ℝ w z (0, 1))) +
        (ω.floerZerothOrder J Ks Kt z (w z + e x z) - ω.floerZerothOrder J Ks Kt z (w z)) :=
  quasilinearSection_apply_ae he hJc hGc hw (aestronglyMeasurable_fderiv_apply w) hwB hJC hJL
    hGL x

/-- **The Floer section on jets of sections is the change of the Floer operator.** Let `e` give
continuous representatives of the values of the elements of `X`, let `w` be differentiable with
`∂t w` bounded, and let `J` and the zeroth-order term `G = -X_{K_s} - J X_{K_t}` be continuous in
`(z, y)` and Lipschitz in `y` uniformly in `z`, with `J` bounded. If `x ∈ X` is almost everywhere
the jet of a differentiable section `ξ`, the Floer section at `x` is almost everywhere
`F(w + ξ) - F(w)`. -/
theorem floerSection_ae_eq_of_ae_eq_jet
    (he : ∀ x : X, ∀ᵐ z ∂μ, ((x : Lp (V × V × V) p μ) z).1 = e x z)
    (hJc : Continuous (Function.uncurry J))
    (hGc : Continuous (Function.uncurry (ω.floerZerothOrder J Ks Kt)))
    (hw : Differentiable ℝ w) {B C : ℝ} {K L : ℝ≥0} (hwB : ∀ z, ‖fderiv ℝ w z (0, 1)‖ ≤ B)
    (hJC : ∀ z y, ‖J z y‖ ≤ C) (hJL : ∀ z, LipschitzWith K (J z))
    (hGL : ∀ z, LipschitzWith L (ω.floerZerothOrder J Ks Kt z)) {x : X} {ξ : ℝ × ℝ → V}
    (hξ : Differentiable ℝ ξ) (hx : (x : Lp (V × V × V) p μ) =ᵐ[μ] jet ξ) :
    ω.floerSection e J Ks Kt w x =ᵐ[μ] fun z ↦
      ω.floerOperator J Ks Kt (w + ξ) z - ω.floerOperator J Ks Kt w z := by
  filter_upwards [quasilinearSection_ae_eq_of_ae_eq_jet he hJc hGc
    hw.continuous.aestronglyMeasurable (aestronglyMeasurable_fderiv_apply w) hwB hJC hJL hGL hx]
    with z hz
  rw [floerSection_def, hz, floerOperator_eq_add_floerZerothOrder,
    floerOperator_eq_add_floerZerothOrder, fderiv_add (hw z) (hξ z), Pi.add_apply]
  simp only [add_apply, map_add]
  abel

/-- **The Floer section is strictly differentiable.** Let `e` give continuous representatives of
the values of the elements of `X`, and let `∂t w` be bounded. Let `J` and the zeroth-order term
`G = -X_{K_s} - J X_{K_t}` be differentiable in `y`, with derivatives `J'` and `G'` that are
bounded and uniformly continuous in `y` uniformly in `z`, and let `J`, `J'`, `G`, `G'` be
continuous in `(z, y)`, with `J` bounded. Then the Floer section is strictly differentiable at
every `x₀ ∈ X`, with derivative the linearization `TauCeti.quasilinearLinearization` of the Floer
coefficients at `x₀`. -/
theorem hasStrictFDerivAt_floerSection
    (he : ∀ x : X, ∀ᵐ z ∂μ, ((x : Lp (V × V × V) p μ) z).1 = e x z)
    {J' : ℝ × ℝ → V → V →L[ℝ] V →L[ℝ] V} {G' : ℝ × ℝ → V → V →L[ℝ] V}
    (hJc : Continuous (Function.uncurry J))
    (hGc : Continuous (Function.uncurry (ω.floerZerothOrder J Ks Kt)))
    (hJ'c : Continuous (Function.uncurry J')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w μ) {B C : ℝ} {K L : ℝ≥0}
    (hwB : ∀ z, ‖fderiv ℝ w z (0, 1)‖ ≤ B) (hJC : ∀ z y, ‖J z y‖ ≤ C)
    (hJ : ∀ z y, HasFDerivAt (J z) (J' z y) y) (hJ'K : ∀ z y, ‖J' z y‖ ≤ K)
    (hJ'u : UniformEquicontinuous J')
    (hG : ∀ z y, HasFDerivAt (ω.floerZerothOrder J Ks Kt z) (G' z y) y)
    (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (hG'u : UniformEquicontinuous G') (x₀ : X) :
    HasStrictFDerivAt (ω.floerSection e J Ks Kt w)
      (quasilinearLinearization e J J' G' w (fun z ↦ fderiv ℝ w z (0, 1)) x₀) x₀ := by
  rw [floerSection_def]
  exact hasStrictFDerivAt_quasilinearSection he hJc hGc hJ'c hG'c hw
    (aestronglyMeasurable_fderiv_apply w) hwB hJC hJ hJ'K hJ'u hG hG'K hG'u x₀

end TauCeti.SymplecticForm
