/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Section
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization
import TauCeti.Analysis.Calculus.ContDiff.Differentiable

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
(`TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection`), and hence continuously differentiable
(`TauCeti.SymplecticForm.contDiff_floerSection`).

**The derivative is the linearized Floer operator.** The zeroth-order part of the linearized Floer
operator along a map `u` is `η ↦ (dJ(z, u) η) ∂t u + dG(z, u) η`
(`TauCeti.SymplecticForm.floerLinearizationCoeff_eq_flip_add_fderiv_floerZerothOrder`), and the
linearization of the Floer coefficients at `x₀ = (ξ₀, ξ₀_s, ξ₀_t)` is
`h ↦ h_s + J(u₀) h_t + (J'(u₀) h) (∂t w + ξ₀_t) + G'(u₀) h` with `u₀ = w + ξ₀`. When the
Hamiltonian vector fields are differentiable and `u₀` has the classical derivative
`∂t u₀ = ∂t w + ξ₀_t` almost everywhere, essentially bounded, the two agree: the linearization is
the Sobolev realization `D_{u₀}` of the linearized Floer operator
(`TauCeti.SymplecticForm.floerSobolevOperator`;
`TauCeti.SymplecticForm.quasilinearLinearization_eq_floerSobolevOperator`), which is therefore the
strict derivative of the Floer section at `x₀`
(`TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection_floerSobolevOperator`). At the reference
map, `x₀ = 0`, the conditions on `x₀` hold automatically, and the derivative of the Floer section
around `w` at `0` is `D_w` (`TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection_zero`). Through
these identifications, properties of `D_w` such as being Fredholm or onto become properties of the
derivative of the Floer section, as the implicit function and Sard–Smale theorems require.

Under the hypotheses of `TauCeti.SymplecticForm.floerSection_apply_ae` (`∂t w` and `J` bounded,
`J` and `G` Lipschitz in `y` uniformly in `z`), the Floer section is everywhere given by its
pointwise formula; outside them it may take the junk value `0`. Under these hypotheses, with `w`
differentiable, the zeros of the Floer section are the `ξ` in `W^{1,p}` for which `u = w + ξ` is a
weak solution of `F(u) = F(w)`: the equation holds almost everywhere with the weak derivatives
`ξ_s`, `ξ_t` of `ξ` in place of its classical derivatives. Agreement with
`TauCeti.SymplecticForm.floerOperator` is proved only on test sections
(`TauCeti.SymplecticForm.floerSection_toW1p_ae`). When the reference map is itself a Floer
cylinder, `F(w) = 0`, these zeros are the weak solutions of the Floer equation near `w`; that they
are classical Floer cylinders is elliptic regularity, which is not proved here. The Floer section is
the map to which the implicit function theorem and the Sard–Smale theorem are applied in the
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
* `TauCeti.SymplecticForm.contDiff_floerSection`: under the same hypotheses, the Floer section is
  `C¹`.
* `TauCeti.SymplecticForm.quasilinearLinearization_eq_floerSobolevOperator`: at a point whose
  value has bounded classical `t`-derivative equal to its weak one, the linearization of the Floer
  coefficients is the Sobolev realization of the linearized Floer operator.
* `TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection_floerSobolevOperator`: the strict
  derivative of the Floer section at such a point `x₀` is `D_{w + ξ₀}`.
* `TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection_zero`: the strict derivative of the Floer
  section at the reference map is `D_w`.

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

/-- **The Floer section is `C¹`.** Under the hypotheses of
`TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection`, the Floer section is strictly
differentiable at every point, hence continuously differentiable. -/
theorem contDiff_floerSection (hp : 2 < p) (hpt : p ≠ ∞)
    {J' : ℝ × ℝ → V → V →L[ℝ] V →L[ℝ] V} {G' : ℝ × ℝ → V → V →L[ℝ] V}
    (hJc : Continuous (Function.uncurry J))
    (hGc : Continuous (Function.uncurry (ω.floerZerothOrder J Ks Kt)))
    (hJ'c : Continuous (Function.uncurry J')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w stripMeasure) {B C : ℝ} {K L : ℝ≥0}
    (hwB : ∀ z, ‖fderiv ℝ w z (0, 1)‖ ≤ B) (hJC : ∀ z y, ‖J z y‖ ≤ C)
    (hJ : ∀ z y, HasFDerivAt (J z) (J' z y) y) (hJ'K : ∀ z y, ‖J' z y‖ ≤ K)
    (hJ'u : UniformEquicontinuous J')
    (hG : ∀ z y, HasFDerivAt (ω.floerZerothOrder J Ks Kt z) (G' z y) y)
    (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (hG'u : UniformEquicontinuous G') :
    ContDiff ℝ 1 (ω.floerSection J Ks Kt w p) :=
  contDiff_one_of_forall_hasStrictFDerivAt fun x₀ ↦ hasStrictFDerivAt_floerSection hp hpt hJc hGc
    hJ'c hG'c hw hwB hJC hJ hJ'K hJ'u hG hG'K hG'u x₀

/-! ### The derivative is the linearized Floer operator -/

section Linearization

variable {J' : ℝ × ℝ → V → V →L[ℝ] V →L[ℝ] V} {G' : ℝ × ℝ → V → V →L[ℝ] V}

/-- **The linearization of the Floer coefficients is the linearized Floer operator.** Let
`2 < p < ∞`, let `∂t w` be bounded, let `J` be bounded and continuous, and let `J'`, `G'` be
bounded, continuous derivatives in `y` of `J` and of the zeroth-order term
`G = -X_{K_s} - J X_{K_t}`, the Hamiltonian vector fields being differentiable. At a point
`x₀ = (ξ₀, ξ₀_s, ξ₀_t)` of `W^{1,p}` whose continuous value `ξ₀` makes `u₀ = w + ξ₀` a map with
`∂t u₀ = ∂t w + ξ₀_t` almost everywhere and `∂t u₀` essentially bounded, the linearization
`TauCeti.CylinderSobolev.quasilinearLinearization` of the Floer coefficients at `x₀` is the
Sobolev realization `D_{u₀}` of the linearized Floer operator along `u₀`
(`TauCeti.SymplecticForm.floerSobolevOperator`). -/
theorem quasilinearLinearization_eq_floerSobolevOperator (hp : 2 < p) (hpt : p ≠ ∞)
    (hJc : Continuous (Function.uncurry J)) (hJ'c : Continuous (Function.uncurry J'))
    (hG'c : Continuous (Function.uncurry G')) (hw : AEStronglyMeasurable w stripMeasure)
    {B B' C : ℝ} {K L : ℝ≥0} (hwB : ∀ z, ‖fderiv ℝ w z (0, 1)‖ ≤ B) (hJC : ∀ z y, ‖J z y‖ ≤ C)
    (hJ'K : ∀ z y, ‖J' z y‖ ≤ K) (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (x₀ : W1p V p)
    (hJ : ∀ z, HasFDerivAt (J z) (J' z (w z + continuousValue p x₀ z))
      (w z + continuousValue p x₀ z))
    (hG : ∀ z, HasFDerivAt (ω.floerZerothOrder J Ks Kt z) (G' z (w z + continuousValue p x₀ z))
      (w z + continuousValue p x₀ z))
    (hKs : ∀ z, DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks z))
      (w z + continuousValue p x₀ z))
    (hKt : ∀ z, DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt z))
      (w z + continuousValue p x₀ z))
    (hx₀ : ∀ᵐ z ∂stripMeasure, fderiv ℝ (w + ⇑(continuousValue p x₀)) z (0, 1) =
      fderiv ℝ w z (0, 1) + ((x₀ : Lp (V × V × V) p stripMeasure) z).2.2)
    (hx₀B : ∀ᵐ z ∂stripMeasure, ‖fderiv ℝ (w + ⇑(continuousValue p x₀)) z (0, 1)‖ ≤ B') :
    quasilinearLinearization J J' G' w (fun z ↦ fderiv ℝ w z (0, 1)) p x₀ =
      ω.floerSobolevOperator p J Ks Kt (w + ⇑(continuousValue p x₀)) := by
  set u₀ := w + ⇑(continuousValue p x₀)
  -- the coefficient field of `D_{u₀}` in terms of `J'` and `G'`; `u₀ z` unfolds to the point
  -- `w z + continuousValue p x₀ z` of the hypotheses
  have hcoeff (z : ℝ × ℝ) : ω.floerJetCoeff J Ks Kt u₀ z = firstOrderJetCoeff (J z (u₀ z))
      ((J' z (u₀ z)).flip (fderiv ℝ u₀ z (0, 1)) + G' z (u₀ z)) := by
    have hJz : HasFDerivAt (J z) (J' z (u₀ z)) (u₀ z) := hJ z
    have hGz : HasFDerivAt (ω.floerZerothOrder J Ks Kt z) (G' z (u₀ z)) (u₀ z) := hG z
    rw [floerJetCoeff_def, floerLinearizationCoeff_eq_flip_add_fderiv_floerZerothOrder ω
      hJz.differentiableAt (hKs z) (hKt z), hJz.fderiv, hGz.fderiv]
  have hu₀ : AEStronglyMeasurable u₀ stripMeasure :=
    hw.add (continuousValue p x₀).continuous.aestronglyMeasurable
  have hM : MemLp (ω.floerJetCoeff J Ks Kt u₀) ∞ stripMeasure := by
    refine memLp_top_of_bound ?_ (1 + C + (K * B' + L)) ?_
    · rw [funext hcoeff]
      have hΦ : Continuous fun q : (V →L[ℝ] V) × ((V →L[ℝ] V →L[ℝ] V) × V) × (V →L[ℝ] V) ↦
          firstOrderJetCoeff q.1 (q.2.1.1.flip q.2.1.2 + q.2.2) :=
        continuous_iff_continuousAt.2 fun q ↦ continuousAt_firstOrderJetCoeff
          continuous_fst.continuousAt
          ((((ContinuousLinearMap.flipₗᵢ ℝ V V V).continuous.comp continuous_snd.fst.fst).clm_apply
            continuous_snd.fst.snd).add continuous_snd.snd).continuousAt
      have hy (Φ : ℝ × ℝ → V → V →L[ℝ] V) (hΦc : Continuous (Function.uncurry Φ)) :
          AEStronglyMeasurable (fun z ↦ Φ z (u₀ z)) stripMeasure :=
        hΦc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hu₀)
      exact hΦ.comp_aestronglyMeasurable ((hy J hJc).prodMk
        ((hJ'c.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hu₀)).prodMk
          (aestronglyMeasurable_fderiv_apply u₀) |>.prodMk (hy G' hG'c)))
    · filter_upwards [hx₀B] with z hz
      rw [hcoeff]
      refine (norm_firstOrderJetCoeff_le _ _).trans (add_le_add (add_le_add_right (hJC _ _) _) ?_)
      refine (norm_add_le _ _).trans (add_le_add ?_ (hG'K _ _))
      refine ((J' z (u₀ z)).flip.le_opNorm _).trans ?_
      rw [ContinuousLinearMap.opNorm_flip]
      exact mul_le_mul (hJ'K _ _) hz (norm_nonneg _) K.coe_nonneg
  refine ContinuousLinearMap.ext fun h ↦ Lp.ext ?_
  filter_upwards [quasilinearLinearization_apply_ae hJc hJ'c hG'c hw
      (aestronglyMeasurable_fderiv_apply w) hwB hJC hJ'K hG'K x₀ h,
    coeFn_floerSobolevOperator ω hM h, hx₀, fst_ae_eq_continuousValue hp hpt h]
    with z e₁ e₂ e₃ e₄
  rw [e₁, e₂, hcoeff, firstOrderJetCoeff_apply, e₃, ← e₄]
  simp only [u₀, Pi.add_apply, add_apply, ContinuousLinearMap.flip_apply, map_add]
  abel

/-- **The derivative of the Floer section is the linearized Floer operator.** Under the hypotheses
of `TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection`, with differentiable Hamiltonian
vector fields, at a point `x₀ = (ξ₀, ξ₀_s, ξ₀_t)` of `W^{1,p}` for which `u₀ = w + ξ₀` has
`∂t u₀ = ∂t w + ξ₀_t` almost everywhere and `∂t u₀` essentially bounded, the strict derivative of
the Floer section is the Sobolev realization `D_{u₀}` of the linearized Floer operator along
`u₀`. -/
theorem hasStrictFDerivAt_floerSection_floerSobolevOperator (hp : 2 < p) (hpt : p ≠ ∞)
    (hJc : Continuous (Function.uncurry J))
    (hGc : Continuous (Function.uncurry (ω.floerZerothOrder J Ks Kt)))
    (hJ'c : Continuous (Function.uncurry J')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w stripMeasure) {B B' C : ℝ} {K L : ℝ≥0}
    (hwB : ∀ z, ‖fderiv ℝ w z (0, 1)‖ ≤ B) (hJC : ∀ z y, ‖J z y‖ ≤ C)
    (hJ : ∀ z y, HasFDerivAt (J z) (J' z y) y) (hJ'K : ∀ z y, ‖J' z y‖ ≤ K)
    (hJ'u : UniformEquicontinuous J')
    (hG : ∀ z y, HasFDerivAt (ω.floerZerothOrder J Ks Kt z) (G' z y) y)
    (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (hG'u : UniformEquicontinuous G')
    (x₀ : W1p V p)
    (hKs : ∀ z, DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks z))
      (w z + continuousValue p x₀ z))
    (hKt : ∀ z, DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt z))
      (w z + continuousValue p x₀ z))
    (hx₀ : ∀ᵐ z ∂stripMeasure, fderiv ℝ (w + ⇑(continuousValue p x₀)) z (0, 1) =
      fderiv ℝ w z (0, 1) + ((x₀ : Lp (V × V × V) p stripMeasure) z).2.2)
    (hx₀B : ∀ᵐ z ∂stripMeasure, ‖fderiv ℝ (w + ⇑(continuousValue p x₀)) z (0, 1)‖ ≤ B') :
    HasStrictFDerivAt (ω.floerSection J Ks Kt w p)
      (ω.floerSobolevOperator p J Ks Kt (w + ⇑(continuousValue p x₀))) x₀ := by
  rw [← quasilinearLinearization_eq_floerSobolevOperator hp hpt hJc hJ'c hG'c hw hwB hJC hJ'K hG'K
    x₀ (fun z ↦ hJ z _) (fun z ↦ hG z _) hKs hKt hx₀ hx₀B]
  exact hasStrictFDerivAt_floerSection hp hpt hJc hGc hJ'c hG'c hw hwB hJC hJ hJ'K hJ'u hG hG'K
    hG'u x₀

/-- **The derivative of the Floer section at the reference map is `D_w`.** Under the hypotheses of
`TauCeti.SymplecticForm.hasStrictFDerivAt_floerSection`, with differentiable Hamiltonian vector
fields, the strict derivative of the Floer section around `w` at `0` is the Sobolev realization
`D_w` of the linearized Floer operator along `w`. -/
theorem hasStrictFDerivAt_floerSection_zero (hp : 2 < p) (hpt : p ≠ ∞)
    (hJc : Continuous (Function.uncurry J))
    (hGc : Continuous (Function.uncurry (ω.floerZerothOrder J Ks Kt)))
    (hJ'c : Continuous (Function.uncurry J')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w stripMeasure) {B C : ℝ} {K L : ℝ≥0}
    (hwB : ∀ z, ‖fderiv ℝ w z (0, 1)‖ ≤ B) (hJC : ∀ z y, ‖J z y‖ ≤ C)
    (hJ : ∀ z y, HasFDerivAt (J z) (J' z y) y) (hJ'K : ∀ z y, ‖J' z y‖ ≤ K)
    (hJ'u : UniformEquicontinuous J')
    (hG : ∀ z y, HasFDerivAt (ω.floerZerothOrder J Ks Kt z) (G' z y) y)
    (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (hG'u : UniformEquicontinuous G')
    (hKs : ∀ z, DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks z)) (w z))
    (hKt : ∀ z, DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt z)) (w z)) :
    HasStrictFDerivAt (ω.floerSection J Ks Kt w p) (ω.floerSobolevOperator p J Ks Kt w) 0 := by
  have hv : w + ⇑(continuousValue p (0 : W1p V p)) = w := by simp
  have h := hasStrictFDerivAt_floerSection_floerSobolevOperator hp hpt hJc hGc hJ'c hG'c hw hwB
    hJC hJ hJ'K hJ'u hG hG'K hG'u (B' := B) 0 (by simpa using hKs) (by simpa using hKt) ?_ ?_
  · rwa [hv] at h
  · filter_upwards [Lp.coeFn_zero (V × V × V) p stripMeasure] with z hz
    simp only [hv, Submodule.coe_zero, hz, Pi.zero_apply, Prod.snd_zero, add_zero]
  · simpa [hv] using Filter.Eventually.of_forall hwB

end Linearization

end TauCeti.SymplecticForm
