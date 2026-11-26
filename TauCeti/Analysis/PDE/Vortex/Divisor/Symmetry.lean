/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor.Normalized
public import TauCeti.Analysis.PDE.Vortex.Equivariance
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Regularity
public import TauCeti.Analysis.PDE.Vortex.Isometry
public import TauCeti.Analysis.PDE.Vortex.RigidMotion
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Translation, rotation and line-frame laws of the plane vortex family and its splitting

Taubes's plane vortex with zero divisor the roots of a polynomial `P` is the field
`x_P = TauCeti.Vortex.polynomialVortex P`, reconstructed from the amplitude `u₀ + w_P` and the
section `P`, where `u₀ = -log (1 + ‖P‖²) / 2` is the background amplitude and `w_P` the smooth
reduced solution. For `c ∈ ℂᵐ` the normalized vortex `y_c = TauCeti.Vortex.normalizedVortex c`
is `x_(P_c)` for the monic polynomial `P_c` with lower coefficients `c`, followed by the polynomial
gauge `g_c` that turns the phase of its section into the winding phase `(z / |z|)ᵐ` outside a disc.
This file shows that these explicit families transform under the symmetries of the plane and of
the line at infinity as their divisors do, up to explicit framed gauges. These are the laws that
let the kernel projections, right inverses and decay estimates of a vortex be moved by a rigid
motion of the plane, as gluing a vortex along a curve requires.

**The reduced solution.** Taubes's functional depends on `P` only through `‖P‖` and `‖P'‖`, so its
minimizer moves with affine isometries of the plane
(`TauCeti.Vortex.reducedMinimizer_compAffineIsometryEquivL`). Since `w_P` is the unique continuous
representative of the minimizer, the same holds pointwise for `w_P`
(`TauCeti.Vortex.reducedSolution_compAffineIsometryEquivL`): `w_(P ∘ (· + a)) = w_P ∘ (· + a)`,
`w_(P ∘ (u ·)) = w_P ∘ (u ·)` for `|u| = 1`, and `w_(c P) = w_P` for `|c| = 1`.

**The vortex of a polynomial.** Consequently
(`TauCeti.Vortex.translateField_polynomialVortex`, `TauCeti.Vortex.rotateField_polynomialVortex`,
`TauCeti.Vortex.polynomialVortex_C_mul`):

* translating the plane by `a` translates the vortex: `T_a x_P = x_(P ∘ (· + a))`, whose zeros
  are those of `P` moved by `-a`;
* rotating the plane by `u` rotates the vortex: `R_u x_P = x_(P ∘ (u ·))`;
* a unit constant `c` in front of `P` is the constant gauge `c`: `x_(c P) = c · x_P`.

In particular the vortex with a single zero at `z₀` is the translate of the vortex centred at `0`
(`TauCeti.Vortex.polynomialVortex_X_sub_C`), and the vortex `x_(Xᵐ)` with an `m`-fold zero at `0`
is rotation-equivariant up to the constant line-frame gauge `u⁻ᵐ`, like the reference field
(`TauCeti.Vortex.gaugeTransform_rotateField_polynomialVortex_X_pow`).

**The normalized vortices.** On the symmetric coordinates `c` of the divisor, a rotation acts by
`TauCeti.Vortex.rotateCoeff` (the coefficients of `u⁻ᵐ P_c(u ·)`) and a translation by
`TauCeti.Polynomial.translateCoeff` (the coefficients of `P_c(· + a)`). Then:

* `y_(c^u) = u⁻ᵐ · R_u y_c` (`TauCeti.Vortex.normalizedVortex_rotateCoeff`): the normalized
  family is equivariant for the action `x ↦ u⁻ᵐ · R_u x` of rotations on the framed fields, which
  preserves every `A_m^s` (`TauCeti.Vortex.gaugeTransform_rotateField_mem_framedFieldSpace`);
* `y_(c + a) = h · T_a y_c` for the framed gauge `h(z) = g_(c + a)(z) g_c(z + a)⁻¹`
  (`TauCeti.Vortex.normalizedVortex_translateCoeff`,
  `TauCeti.Vortex.normalizingTranslationGauge_mem_framedGaugeGroup`), where `c + a` stands for
  `translateCoeff a c`. Translations do not preserve the winding phase, so the normalized family
  is equivariant only up to this gauge. Outside a disc `h` is the translation gauge `τ`
  (`TauCeti.Vortex.exists_forall_normalizingTranslationGauge_eq_translationGauge`), which carries
  `T_a` back to framed fields, and `h τ⁻¹` lies in the Sobolev gauge group `G_(k+1)`, `k ≥ 2`
  (`TauCeti.Vortex.normalizingTranslationGauge_mul_inv_translationGauge_mem_sobolevGaugeGroup`):
  in `A_m^k`, `y_(c + a)` lies in the `G_(k+1)`-orbit of `τ · T_a y_c`.

**The kernel projections and right inverses.** The realization
`L_P : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` of the gauge-fixed operator at the `L∞` class of the vortex of `P`
(`TauCeti.Vortex.polynomialVortexLp`) splits along the `L²` pairing into the projection `π_P`
onto its kernel and the right inverse `Q_P` with values orthogonal to the kernel. The class of the
vortex moves with `P`: moving it by `z ↦ u z + a` gives the class for `P(u · + a)`
(`TauCeti.Vortex.polynomialVortexLp_comp_C_mul_X_add_C`), and changing its line frame by a unit
constant `c` gives the class for `c P` (`TauCeti.Vortex.polynomialVortexLp_C_mul`). In the
symmetric coordinates `c ∈ ℂᵐ` of the divisor, where `P_c = monicOfCoeff c`, the class for the
translated coefficients is the translated class, and the class for the rotated coefficients is
the rotated class in the line frame changed by `u⁻ᵐ`
(`TauCeti.Vortex.polynomialVortexLp_monicOfCoeff_translateCoeff`,
`TauCeti.Vortex.polynomialVortexLp_monicOfCoeff_rotateCoeff`). With the rigid-motion and
line-frame laws of the realization (`TauCeti.Analysis.PDE.Vortex.RigidMotion`), these give the
translation and rotation laws of the splitting along the vortex family:

* `π_(P_(c + a)) = T_a ∘ π_(P_c) ∘ T_a⁻¹` and `Q_(P_(c + a)) = T_a ∘ Q_(P_c) ∘ T_a⁻¹`, with the
  translation acting on variations and on targets;
* `π_(P_(c^u)) = (u⁻ᵐ R_u) ∘ π_(P_c) ∘ (u⁻ᵐ R_u)⁻¹` and likewise for `Q`, with the rotation
  `R_u` followed by the change of line frame by `u⁻ᵐ`.

Permutations of the zeros act trivially, since `c` consists of symmetric functions of the zeros.
These conjugations carry the kernel projections and right inverses at a divisor, and their
estimates, to every translate and rotation of that divisor.

## Main definitions

* `TauCeti.Vortex.normalizingTranslationGauge`: the framed gauge relating `T_a y_c` to
  `y_(translateCoeff a c)`.

## Main results

* `TauCeti.Vortex.reducedSolution_compAffineIsometryEquivL`: the reduced solution moves with
  affine isometries of the plane.
* `TauCeti.Vortex.translateField_polynomialVortex`, `TauCeti.Vortex.rotateField_polynomialVortex`,
  `TauCeti.Vortex.polynomialVortex_C_mul`: the translation, rotation and line-frame laws of the
  vortex of a polynomial.
* `TauCeti.Vortex.normalizedVortex_rotateCoeff`, `TauCeti.Vortex.normalizedVortex_translateCoeff`:
  the rotation and translation laws of the normalized vortices.
* `TauCeti.Vortex.normalizingTranslationGauge_mul_inv_translationGauge_mem_sobolevGaugeGroup`:
  the translation law is compatible with the Sobolev gauge orbits of `A_m^k`.
* the translation and rotation laws of the kernel projections and right inverses along the vortex
  family, in the namespace `TauCeti.Vortex`:
  `orthogonalKerProjection_sobolevGaugeFixedOperator_polynomialVortexLp_translateCoeff`,
  `orthogonalRightInverse_sobolevGaugeFixedOperator_polynomialVortexLp_translateCoeff`,
  `orthogonalKerProjection_sobolevGaugeFixedOperator_polynomialVortexLp_rotateCoeff` and
  `orthogonalRightInverse_sobolevGaugeFixedOperator_polynomialVortexLp_rotateCoeff`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

open Complex MeasureTheory Polynomial
open TauCeti.Polynomial

namespace TauCeti.Vortex

/-! ### The reduced solution -/

section ReducedSolution

variable {P Q : Polynomial ℂ}

/-- **Isometry equivariance of the reduced solution.** If an affine isometry `g` of the plane
carries the norms of `P` and `P'` to those of `Q` and `Q'`, then the reduced solution of `Q` is
the reduced solution of `P` composed with `g`. -/
theorem reducedSolution_compAffineIsometryEquivL (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (hQ : ∀ z, ‖Q.eval z‖ = ‖P.eval (g z)‖)
    (hQ' : ∀ z, ‖Q.derivative.eval z‖ = ‖P.derivative.eval (g z)‖) :
    reducedSolution Q = fun z ↦ reducedSolution P (g z) := by
  rcases Nat.eq_zero_or_pos P.natDegree with hm | hm
  · -- A constant `P` has `P' = 0`, so `Q' = 0` and `Q` is constant too.
    have hQ0 : Q.natDegree = 0 := derivative_eq_zero.1 <| Polynomial.funext fun z ↦ by
      simpa [derivative_of_natDegree_zero hm] using hQ' z
    rw [reducedSolution_eq_zero_of_natDegree_eq_zero hm,
      reducedSolution_eq_zero_of_natDegree_eq_zero hQ0]
    rfl
  · have hmQ : 0 < Q.natDegree := Nat.pos_of_ne_zero fun h ↦
      hm.ne' <| derivative_eq_zero.1 <| Polynomial.funext fun z ↦ by
        simpa [derivative_of_natDegree_zero h] using (hQ' (g.symm z)).symm
    refine (eq_reducedSolution_of_ae_eq hmQ
      ((contDiff_reducedSolution P).continuous.comp g.continuous) ?_).symm
    rw [reducedMinimizer_compAffineIsometryEquivL hm g hQ hQ']
    have hv := W1p.value_compAffineIsometryEquivL_ae (U := ⊤) (V := ⊤) g (by simp)
      (reducedMinimizer P)
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hv
    exact hv.trans (g.measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (value_reducedMinimizer_ae_eq_reducedSolution hm))

variable (P)

/-- **The translation law of the reduced solution**: the reduced solution of `P.comp (X + C a)`,
whose zeros are those of `P` translated by `-a`, is that of `P` at `z + a`. -/
@[simp]
theorem reducedSolution_comp_X_add_C (a z : ℂ) :
    reducedSolution (P.comp (X + C a)) z = reducedSolution P (z + a) :=
  congrFun (reducedSolution_compAffineIsometryEquivL (AffineIsometryEquiv.vaddConst ℝ a)
    (fun z ↦ by simp) (fun z ↦ by simp [derivative_comp])) z

/-- **The rotation law of the reduced solution**: for `u` on the unit circle, the reduced
solution of `P.comp (C u * X)` is that of `P` at `u z`. -/
@[simp]
theorem reducedSolution_comp_C_mul_X (u : Circle) (z : ℂ) :
    reducedSolution (P.comp (C (u : ℂ) * X)) z = reducedSolution P (u * z) :=
  congrFun (reducedSolution_compAffineIsometryEquivL (rotation u).toAffineIsometryEquiv
    (fun z ↦ by simp) (fun z ↦ by simp [derivative_comp])) z

/-- **The line-frame law of the reduced solution**: multiplying `P` by a unit constant does not
change its reduced solution. -/
@[simp]
theorem reducedSolution_C_mul {c : ℂ} (hc : ‖c‖ = 1) :
    reducedSolution (C c * P) = reducedSolution P :=
  reducedSolution_compAffineIsometryEquivL (AffineIsometryEquiv.refl ℝ ℂ)
    (fun z ↦ by simp [hc]) (fun z ↦ by simp [hc])

end ReducedSolution

/-! ### The vortex of a polynomial -/

section PolynomialVortex

variable (P : Polynomial ℂ)

/-- **The translation law of the plane vortices**: translating the vortex of `P` by `a` gives the
vortex of `P.comp (X + C a)`, whose zeros are those of `P` translated by `-a`. -/
@[simp]
theorem translateField_polynomialVortex (a : ℂ) :
    translateField a (polynomialVortex P) = polynomialVortex (P.comp (X + C a)) := by
  simp only [polynomialVortex_def, translateField_amplitudeField, reducedSolution_comp_X_add_C]
  congr 1
  · funext z
    simp [backgroundAmplitude_apply]
  · funext z
    simp

/-- **The rotation law of the plane vortices**: rotating the vortex of `P` by `u` gives the vortex
of `P.comp (C u * X)`. -/
@[simp]
theorem rotateField_polynomialVortex (u : Circle) :
    rotateField u (polynomialVortex P) = polynomialVortex (P.comp (C (u : ℂ) * X)) := by
  simp only [polynomialVortex_def, rotateField_amplitudeField, reducedSolution_comp_C_mul_X]
  congr 1
  · funext z
    simp [backgroundAmplitude_apply]
  · funext z
    simp

/-- **The line-frame law of the plane vortices**: the vortex of `c P`, for `c` on the unit
circle, is the vortex of `P` transformed by the constant gauge `c`. -/
@[simp]
theorem polynomialVortex_C_mul (c : Circle) :
    polynomialVortex (C (c : ℂ) * P) = gaugeTransform (fun _ ↦ c) (polynomialVortex P) := by
  rw [polynomialVortex_def, polynomialVortex_def, ← amplitudeField_const_mul,
    reducedSolution_C_mul P (Circle.norm_coe c)]
  congr 1
  · funext z
    simp [backgroundAmplitude_apply]
  · funext z
    simp

/-- **The vortex of a single zero** at `z₀` is the vortex centred at `0`, translated by `-z₀`. -/
theorem polynomialVortex_X_sub_C (z₀ : ℂ) :
    polynomialVortex (X - C z₀) = translateField (-z₀) (polynomialVortex X) := by
  rw [translateField_polynomialVortex, X_comp, map_neg, ← sub_eq_add_neg]

/-- **Rotation symmetry of the centred vortex.** The vortex of `Xᵐ`, with an `m`-fold zero at
`0`, is rotation-equivariant up to the line frame: rotating it by `u` and applying the constant
gauge `u⁻ᵐ` returns it. -/
theorem gaugeTransform_rotateField_polynomialVortex_X_pow (m : ℕ) (u : Circle) :
    gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u (polynomialVortex (X ^ m))) =
      polynomialVortex (X ^ m) := by
  have h : (X ^ m : Polynomial ℂ).comp (C (u : ℂ) * X) = C ((u ^ m : Circle) : ℂ) * X ^ m := by
    simp [mul_pow]
  rw [rotateField_polynomialVortex, h, polynomialVortex_C_mul,
    ← gaugeTransform_mul (differentiable_const _) (differentiable_const _)]
  convert gaugeTransform_one _
  funext z
  simp

end PolynomialVortex

/-! ### The normalized vortices -/

section Normalized

variable {m : ℕ}

/-- **The rotation law of the normalized vortices.** The normalized vortex with rotated
coefficients is the rotated normalized vortex followed by the constant line-frame gauge `u⁻ᵐ`:
`y_(c^u) = u⁻ᵐ · R_u y_c`. -/
theorem normalizedVortex_rotateCoeff (u : Circle) (c : Fin m → ℂ) :
    normalizedVortex (rotateCoeff u c) =
      gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u (normalizedVortex c)) := by
  rw [normalizedVortex_def, normalizedVortex_def, monicOfCoeff_rotateCoeff_eq_C_mul_comp,
    polynomialVortex_C_mul, ← rotateField_polynomialVortex,
    rotateField_gaugeTransform_polynomialGauge,
    ← gaugeTransform_mul (differentiable_polynomialGauge _) (differentiable_const _),
    ← gaugeTransform_mul (differentiable_const _) (differentiable_polynomialGauge _), mul_comm]

/-- **The normalizing translation gauge** `h(z) = g_(c + a)(z) g_c(z + a)⁻¹`, where `g_c` is the
polynomial gauge and `c + a` stands for `translateCoeff a c`: it carries the translate `T_a y_c`
of the normalized vortex to the normalized vortex with translated coefficients
(`TauCeti.Vortex.normalizedVortex_translateCoeff`). -/
def normalizingTranslationGauge (a : ℂ) (c : Fin m → ℂ) (z : ℂ) : Circle :=
  polynomialGauge (translateCoeff a c) z * (polynomialGauge c (z + a))⁻¹

/-- The normalizing translation gauge at `z` is `g_(c + a)(z) g_c(z + a)⁻¹`. -/
theorem normalizingTranslationGauge_apply (a : ℂ) (c : Fin m → ℂ) (z : ℂ) :
    normalizingTranslationGauge a c z =
      polynomialGauge (translateCoeff a c) z * (polynomialGauge c (z + a))⁻¹ :=
  (rfl)

/-- The normalizing translation gauge is a smooth framed gauge. -/
theorem normalizingTranslationGauge_mem_framedGaugeGroup (a : ℂ) (c : Fin m → ℂ) :
    normalizingTranslationGauge a c ∈ framedGaugeGroup :=
  mul_mem (polynomialGauge_mem_framedGaugeGroup _)
    (inv_mem (comp_add_mem_framedGaugeGroup (polynomialGauge_mem_framedGaugeGroup c) a))

/-- **The translation law of the normalized vortices.** The normalized vortex with translated
coefficients is the translated normalized vortex transformed by the normalizing translation gauge:
`y_(c + a) = h · T_a y_c`. -/
theorem normalizedVortex_translateCoeff (a : ℂ) (c : Fin m → ℂ) :
    normalizedVortex (translateCoeff a c) =
      gaugeTransform (normalizingTranslationGauge a c) (translateField a (normalizedVortex c)) := by
  have hh := differentiable_of_mem_framedGaugeGroup
    (normalizingTranslationGauge_mem_framedGaugeGroup a c)
  have hg : Differentiable ℝ fun z ↦ (polynomialGauge c (z + a) : ℂ) :=
    (differentiable_polynomialGauge c).comp (differentiable_id.add_const a)
  have hprod : normalizingTranslationGauge a c * (fun z ↦ polynomialGauge c (z + a)) =
      polynomialGauge (translateCoeff a c) := by
    funext z
    simp [normalizingTranslationGauge_apply]
  rw [normalizedVortex_def, normalizedVortex_def, translateField_gaugeTransform,
    translateField_polynomialVortex, ← taylor_apply, ← monicOfCoeff_translateCoeff,
    ← gaugeTransform_mul hh hg, hprod]

/-- **The normalizing translation gauge outside a disc** is the translation gauge: far out, both
carry the translated winding phase `((z + a) / |z + a|)ᵐ` to the winding phase `(z / |z|)ᵐ`. -/
theorem exists_forall_normalizingTranslationGauge_eq_translationGauge (a : ℂ)
    (c : Fin m → ℂ) : ∃ R, ∀ z : ℂ, R ≤ ‖z‖ →
      normalizingTranslationGauge a c z = translationGauge m a z := by
  set S := m * ∑ i, ‖c i‖ ^ 2 + 2
  set S' := m * ∑ i, ‖translateCoeff a c i‖ ^ 2 + 2
  refine ⟨‖a‖ + ‖c‖ + 1 + S + S' + 2, fun z hz ↦ ?_⟩
  have hS : 0 ≤ S := by positivity
  have hS' : 0 ≤ S' := by positivity
  -- Far out, `z + a` is not a root of `P_c` and all three cutoffs are inactive.
  have hza : ‖c‖ + 1 + S + S' + 2 ≤ ‖z + a‖ := by
    have := norm_sub_norm_le z (-a)
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  have h1 : 1 ≤ ‖z‖ := by linarith [norm_nonneg a, norm_nonneg c]
  have h1a : 1 ≤ ‖z + a‖ := by linarith [norm_nonneg c]
  have hsq {t T : ℝ} (h1 : 1 ≤ t) (h : T ≤ t) : T ≤ t ^ 2 := by nlinarith
  have hzS' : S' ≤ ‖z‖ ^ 2 := hsq h1 (by linarith [norm_nonneg a, norm_nonneg c])
  have hzaS : S ≤ ‖z + a‖ ^ 2 := hsq h1a (by linarith [norm_nonneg c])
  have hza2 : ‖a‖ ^ 2 + 2 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg a, norm_nonneg c]
  have hP : (monicOfCoeff c).eval (z + a) ≠ 0 := fun h ↦
    (norm_lt_of_isRoot_monicOfCoeff c h).not_ge (by linarith)
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hza0 : z + a ≠ 0 := norm_pos_iff.1 (by linarith)
  have hgc := polynomialGauge_mul_eval (c := c) hzaS
  have hgca := polynomialGauge_mul_eval (c := translateCoeff a c) (z := z) hzS'
  rw [eval_monicOfCoeff_translateCoeff, coe_windingPhase m hz0] at hgca
  rw [coe_windingPhase m hza0] at hgc
  have htr := coe_translationGauge_mul_pow (m := m) hza2
  -- Cancel the common nonzero value `P_c(z + a)` from the two normalizations.
  have key : (translationGauge m a z : ℂ) * (polynomialGauge c (z + a) : ℂ) =
      (polynomialGauge (translateCoeff a c) z : ℂ) := by
    refine mul_right_cancel₀ hP ?_
    rw [hgca, mul_assoc, hgc, ← htr]
    ring
  apply Circle.ext
  rw [normalizingTranslationGauge_apply, Circle.coe_mul, Circle.coe_inv, ← key,
    mul_inv_cancel_right₀ (Circle.coe_ne_zero _)]

/-- **The translated normalized vortex up to the translation gauge.** The normalized vortex with
translated coefficients is the translated normalized vortex followed by the translation gauge
`τ`, which keeps framed fields framed
(`TauCeti.Vortex.gaugeTransform_translationGauge_translateField_mem_framedFieldSpace`), and then
by the gauge `h τ⁻¹`, where `h` is the normalizing translation gauge. -/
theorem normalizedVortex_translateCoeff_eq_gaugeTransform_mul_inv (a : ℂ) (c : Fin m → ℂ) :
    normalizedVortex (translateCoeff a c) =
      gaugeTransform (normalizingTranslationGauge a c * (translationGauge m a)⁻¹)
        (gaugeTransform (translationGauge m a) (translateField a (normalizedVortex c))) := by
  have hτ := translationGauge_mem_framedGaugeGroup m a
  have hu := mul_mem (normalizingTranslationGauge_mem_framedGaugeGroup a c) (inv_mem hτ)
  rw [← gaugeTransform_mul (differentiable_of_mem_framedGaugeGroup hu)
    (differentiable_of_mem_framedGaugeGroup hτ), inv_mul_cancel_right,
    normalizedVortex_translateCoeff]

/-- **The translated normalized vortex lies in the same Sobolev gauge orbit.** For `k ≥ 2`, the
gauge `h τ⁻¹` relating the normalized vortex with translated coefficients to the translated
normalized vortex followed by the translation gauge `τ`
(`TauCeti.Vortex.normalizedVortex_translateCoeff_eq_gaugeTransform_mul_inv`), where `h` is the
normalizing translation gauge, lies in the Sobolev gauge group `G_(k+1)`. Both fields lie in
`A_m^k`, so they lie in the same `G_(k+1)`-orbit there. -/
theorem normalizingTranslationGauge_mul_inv_translationGauge_mem_sobolevGaugeGroup {k : ℕ}
    (hk : 1 < k) (a : ℂ) (c : Fin m → ℂ) :
    normalizingTranslationGauge a c * (translationGauge m a)⁻¹ ∈
      sobolevGaugeGroup (s := k + 1) (by norm_cast; omega) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- In degree zero every gauge involved is trivial.
    have hc (d : Fin 0 → ℂ) : d = 0 := Subsingleton.elim _ _
    have h1 : normalizingTranslationGauge a c = 1 := by
      funext z
      rw [normalizingTranslationGauge_apply, hc (translateCoeff a c), hc c, polynomialGauge_zero]
      simp
    rw [h1, translationGauge_zero_left, inv_one, mul_one]
    exact one_mem _
  have hu := (mem_framedGaugeGroup _).1 (mul_mem (normalizingTranslationGauge_mem_framedGaugeGroup
    a c) (inv_mem (translationGauge_mem_framedGaugeGroup m a)))
  let f : ContDiffBump (0 : ℝ) := default
  refine mem_sobolevGaugeGroup_of_mem_framedFieldSpace (f := f) hk
    (gaugeTransform_translationGauge_translateField_mem_framedFieldSpace a
      (normalizedVortex_mem_framedFieldSpace hm f c k)) (hu.1.of_le (by simp)) ?_
  rw [← normalizedVortex_translateCoeff_eq_gaugeTransform_mul_inv]
  exact normalizedVortex_mem_framedFieldSpace hm f _ k

end Normalized

/-! ### The kernel projections and right inverses along the vortex family -/

section Splitting

open TopologicalSpace
open scoped ENNReal

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-- **The rigid-motion law of the `L∞` classes of the plane vortices.** Moving the class of the
vortex of `P` by `z ↦ u z + a` gives the class of the vortex of `P(u · + a)`. -/
theorem polynomialVortexLp_comp_C_mul_X_add_C (P : Polynomial ℂ) (u : Circle) (a : ℂ) :
    polynomialVortexLp (P.comp (C (u : ℂ) * X + C a)) =
      coefficientMotion u a (polynomialVortexLp P) := by
  refine Lp.ext ?_
  filter_upwards [polynomialVortexLp_ae_eq (P.comp (C (u : ℂ) * X + C a)),
    coeFn_coefficientMotion_of_ae_eq (polynomialVortexLp_ae_eq P) u a] with z h₁ h₂
  rw [h₁, h₂, translateField_polynomialVortex, rotateField_polynomialVortex, comp_assoc]
  simp

/-- **The line-frame law of the `L∞` classes of the plane vortices.** For `c` on the unit circle,
the class of the vortex of `c P` is the class of the vortex of `P` in the line frame changed by
`c`. -/
theorem polynomialVortexLp_C_mul (P : Polynomial ℂ) (c : Circle) :
    polynomialVortexLp (C (c : ℂ) * P) =
      (gaugeFrame c).compLpₗᵢ ∞ μ⊤ (polynomialVortexLp P) := by
  refine Lp.ext ?_
  filter_upwards [polynomialVortexLp_ae_eq (C (c : ℂ) * P),
    (gaugeFrame c).coeFn_compLpₗᵢ (polynomialVortexLp P), polynomialVortexLp_ae_eq P]
    with z h₁ h₂ h₃
  rw [h₁, h₂, h₃, polynomialVortex_C_mul, gaugeTransform_const_apply]

variable {m : ℕ}

/-- **The translation law of the vortex family in symmetric coordinates.** The class of the vortex
with translated coefficients is the class of the vortex of `P_c` translated by `a`. -/
theorem polynomialVortexLp_monicOfCoeff_translateCoeff (a : ℂ) (c : Fin m → ℂ) :
    polynomialVortexLp (monicOfCoeff (translateCoeff a c)) =
      coefficientMotion 1 a (polynomialVortexLp (monicOfCoeff c)) := by
  rw [← polynomialVortexLp_comp_C_mul_X_add_C, monicOfCoeff_translateCoeff, taylor_apply]
  simp

/-- **The rotation law of the vortex family in symmetric coordinates.** The class of the vortex
with rotated coefficients is the class of the vortex of `P_c` rotated by `u`, in the line frame
changed by `u⁻ᵐ`. -/
theorem polynomialVortexLp_monicOfCoeff_rotateCoeff (u : Circle) (c : Fin m → ℂ) :
    polynomialVortexLp (monicOfCoeff (rotateCoeff u c)) =
      (gaugeFrame (u⁻¹ ^ m)).compLpₗᵢ ∞ μ⊤
        (coefficientMotion u 0 (polynomialVortexLp (monicOfCoeff c))) := by
  rw [monicOfCoeff_rotateCoeff_eq_C_mul_comp, polynomialVortexLp_C_mul,
    ← polynomialVortexLp_comp_C_mul_X_add_C, map_zero, add_zero]

/-- **The translation law of the kernel projections along the vortex family.** The projection of
`H¹(ℂ)⁴` onto the kernel of the realization at the vortex with translated coefficients, along the
`L²`-orthogonal complement of the kernel, is the projection at the vortex of `P_c` conjugated by
the translation of variations. -/
theorem orthogonalKerProjection_sobolevGaugeFixedOperator_polynomialVortexLp_translateCoeff
    (a : ℂ) (c : Fin m → ℂ) :
    ContinuousLinearMap.orthogonalKerProjection sobolevFieldValues
        (sobolevGaugeFixedOperator (polynomialVortexLp (monicOfCoeff (translateCoeff a c)))) =
      (variationMotion 1 a : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] _) ∘L
        ContinuousLinearMap.orthogonalKerProjection sobolevFieldValues
          (sobolevGaugeFixedOperator (polynomialVortexLp (monicOfCoeff c))) ∘L
        ((variationMotion 1 a).symm : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] _) := by
  rw [polynomialVortexLp_monicOfCoeff_translateCoeff,
    orthogonalKerProjection_sobolevGaugeFixedOperator_coefficientMotion]

/-- **The translation law of the right inverses along the vortex family.** The right inverse of
the realization at the vortex with translated coefficients, with values `L²`-orthogonal to its
kernel, is the right inverse at the vortex of `P_c` conjugated by the translations of targets and
variations. -/
theorem orthogonalRightInverse_sobolevGaugeFixedOperator_polynomialVortexLp_translateCoeff
    (a : ℂ) (c : Fin m → ℂ) :
    ContinuousLinearMap.orthogonalRightInverse sobolevFieldValues
        (sobolevGaugeFixedOperator (polynomialVortexLp (monicOfCoeff (translateCoeff a c)))) =
      (variationMotion 1 a : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] _) ∘L
        ContinuousLinearMap.orthogonalRightInverse sobolevFieldValues
          (sobolevGaugeFixedOperator (polynomialVortexLp (monicOfCoeff c))) ∘L
        ((targetMotion 1 a).symm.toContinuousLinearEquiv :
          Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] _) := by
  rw [polynomialVortexLp_monicOfCoeff_translateCoeff,
    orthogonalRightInverse_sobolevGaugeFixedOperator_coefficientMotion]

/-- **The rotation law of the kernel projections along the vortex family.** The projection of
`H¹(ℂ)⁴` onto the kernel of the realization at the vortex with rotated coefficients, along the
`L²`-orthogonal complement of the kernel, is the projection at the vortex of `P_c` conjugated by
the rotation of variations followed by the change of line frame by `u⁻ᵐ`. -/
theorem orthogonalKerProjection_sobolevGaugeFixedOperator_polynomialVortexLp_rotateCoeff
    (u : Circle) (c : Fin m → ℂ) :
    ContinuousLinearMap.orthogonalKerProjection sobolevFieldValues
        (sobolevGaugeFixedOperator (polynomialVortexLp (monicOfCoeff (rotateCoeff u c)))) =
      (variationFrame (u⁻¹ ^ m) : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] _) ∘L
        ((variationMotion u 0 : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] _) ∘L
          ContinuousLinearMap.orthogonalKerProjection sobolevFieldValues
            (sobolevGaugeFixedOperator (polynomialVortexLp (monicOfCoeff c))) ∘L
          ((variationMotion u 0).symm : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] _)) ∘L
        ((variationFrame (u⁻¹ ^ m)).symm : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] _) := by
  rw [polynomialVortexLp_monicOfCoeff_rotateCoeff,
    orthogonalKerProjection_sobolevGaugeFixedOperator_compLpₗᵢ_gaugeFrame,
    orthogonalKerProjection_sobolevGaugeFixedOperator_coefficientMotion]

/-- **The rotation law of the right inverses along the vortex family.** The right inverse of the
realization at the vortex with rotated coefficients, with values `L²`-orthogonal to its kernel, is
the right inverse at the vortex of `P_c` conjugated by the rotations of targets and variations
followed by the changes of line frame by `u⁻ᵐ`. -/
theorem orthogonalRightInverse_sobolevGaugeFixedOperator_polynomialVortexLp_rotateCoeff
    (u : Circle) (c : Fin m → ℂ) :
    ContinuousLinearMap.orthogonalRightInverse sobolevFieldValues
        (sobolevGaugeFixedOperator (polynomialVortexLp (monicOfCoeff (rotateCoeff u c)))) =
      (variationFrame (u⁻¹ ^ m) : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] _) ∘L
        ((variationMotion u 0 : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] _) ∘L
          ContinuousLinearMap.orthogonalRightInverse sobolevFieldValues
            (sobolevGaugeFixedOperator (polynomialVortexLp (monicOfCoeff c))) ∘L
          ((targetMotion u 0).symm.toContinuousLinearEquiv :
            Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] _)) ∘L
        (((gaugeFrame (u⁻¹ ^ m)⁻¹).compLpₗᵢ 2 μ⊤).toContinuousLinearEquiv :
          Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] _) := by
  rw [polynomialVortexLp_monicOfCoeff_rotateCoeff,
    orthogonalRightInverse_sobolevGaugeFixedOperator_compLpₗᵢ_gaugeFrame,
    orthogonalRightInverse_sobolevGaugeFixedOperator_coefficientMotion]

end Splitting

end TauCeti.Vortex
