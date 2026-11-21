/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Euclidean.Volume.Sphere
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# The coordinate ADM flux

Let `g : ℝⁿ → (Fin n → Fin n → ℝ)` be the coefficients `g_ij` of a Riemannian metric in a
coordinate system on the exterior of a ball, as for an asymptotically Euclidean end. The ADM
mass of the end is the limit, as `r → ∞`, of

`[2 (n - 1) |Sⁿ⁻¹|]⁻¹ ∫_{|x| = r} Σ_j (Σ_i (∂_i g_ij - ∂_j g_ii)) x_j / r dS`,

where `dS` is the Euclidean area of the coordinate sphere and `|Sⁿ⁻¹|` is the area of the unit
sphere. This file defines the integrand, `TauCeti.coordinateFluxIntegrand`, and the normalized
flux at radius `r`, `TauCeti.normalizedCoordinateFlux`. The area measure is the normalized
`(n - 1)`-dimensional Hausdorff measure `μHE[n - 1]`, and `|Sⁿ⁻¹|` is
`TauCeti.roundSphereVolume (n - 1)`.

The flux at radius `r` only sees the coefficients near the sphere of radius `r`
(`TauCeti.normalizedCoordinateFlux_congr_of_eqOn`), so the mass of an end only depends on its
coefficients outside a ball. The flux density is measurable whatever the coefficients
(`TauCeti.measurable_coordinateFluxIntegrand`), it is `o(|x|⁻¹)` at infinity when the derivatives
of the coefficients are (`TauCeti.isLittleO_coordinateFluxIntegrand`), and it obeys a product
rule for coefficients `w g_ij` with a scalar factor `w` (`TauCeti.coordinateFluxIntegrand_mul`).
The flux is homogeneous in `g`, additive for coefficients differentiable on the sphere with
integrable flux densities, and unchanged by adding constant coefficients such as `δ_ij`.
Replacing `g` by `g(s ·)` for `s > 0` turns the flux at radius `r` into `s ^ (2 - n)` times the
flux at radius `s r` (`TauCeti.normalizedCoordinateFlux_comp_smul`): for the metric `λ g` in the
coordinates `√λ x`, whose coefficients are `g(x / √λ)`, this is the scaling law
`m(λ g) = λ ^ ((n - 2) / 2) m(g)` of the mass.

The remaining results evaluate the flux on the model metrics against which the normalization is
checked. For conformally flat coefficients `w(|x|) δ_ij` the flux density is
`(1 - n) w'(|x|)` (`TauCeti.coordinateFluxIntegrand_conformal_radial`), so the normalized flux is
`-r ^ (n - 1) w'(r) / 2` (`TauCeti.normalizedCoordinateFlux_conformal_radial`). In particular
the metric `(1 + c |x| ^ (2 - n)) ^ (4 / (n - 2)) δ` has mass `2 c`
(`TauCeti.tendsto_normalizedCoordinateFlux_conformal_one_add_mul_rpow`), and the spatial
Schwarzschild metric `(1 + m |x| ^ (2 - n) / 2) ^ (4 / (n - 2)) δ` has mass `m`. The coefficients
`x_i x_j |x| ^ (-n)` have normalized flux `1 / 2` at every radius
(`TauCeti.normalizedCoordinateFlux_mul_mul_rpow`), so the metric `δ_ij + ε x_i x_j |x| ^ (-n)`,
whose coefficients are not of the conformal form `f δ_ij`, has mass `ε / 2`.

## References

* S. Cecchini, R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, arXiv:2108.11972, equation (2.1) and Example 2.2.
* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Definition 8.2
  and §9.
-/

public section

noncomputable section

open MeasureTheory Measure Metric Set Filter
open scoped Topology

namespace TauCeti

variable {n : ℕ}

/-- The integrand of the coordinate ADM flux: for metric coefficients `g i j` on `ℝⁿ` it is
`Σ_j (Σ_i (∂_i g_ij - ∂_j g_ii)) x_j / |x|`, the flux density through the sphere of radius `|x|`
for its outward Euclidean unit normal `x / |x|`. -/
def coordinateFluxIntegrand (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j, (∑ i, (fderiv ℝ (fun y ↦ g y i j) x (EuclideanSpace.single i 1) -
    fderiv ℝ (fun y ↦ g y i i) x (EuclideanSpace.single j 1))) * (x j / ‖x‖)

/-- Unfolding lemma for `TauCeti.coordinateFluxIntegrand`. -/
theorem coordinateFluxIntegrand_def (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand g x =
      ∑ j, (∑ i, (fderiv ℝ (fun y ↦ g y i j) x (EuclideanSpace.single i 1) -
        fderiv ℝ (fun y ↦ g y i i) x (EuclideanSpace.single j 1))) * (x j / ‖x‖) :=
  (rfl)

/-- The normalized coordinate ADM flux at radius `r`: the integral of
`TauCeti.coordinateFluxIntegrand g` over the sphere of radius `r`, for normalized
`(n - 1)`-dimensional Hausdorff measure, divided by `2 (n - 1) |Sⁿ⁻¹|`, where
`|Sⁿ⁻¹| = TauCeti.roundSphereVolume (n - 1)` is the area of the unit sphere of `ℝⁿ`. On the
sphere, the factor `x_j / |x|` of the integrand is the `x_j / r` of the classical formula. The
ADM mass of an asymptotically Euclidean end is the limit of this quantity as `r → ∞`
(Cecchini–Zeidler, equation (2.1)). -/
def normalizedCoordinateFlux (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) : ℝ :=
  (∫ x in sphere (0 : EuclideanSpace ℝ (Fin n)) r, coordinateFluxIntegrand g x ∂μHE[n - 1]) /
    (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1))

/-- Unfolding lemma for `TauCeti.normalizedCoordinateFlux`. -/
theorem normalizedCoordinateFlux_def (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux g r =
      (∫ x in sphere (0 : EuclideanSpace ℝ (Fin n)) r, coordinateFluxIntegrand g x ∂μHE[n - 1]) /
        (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)) :=
  (rfl)

/-- The flux density is measurable, whatever the regularity of the coefficients. -/
theorem measurable_coordinateFluxIntegrand (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) :
    Measurable (coordinateFluxIntegrand g) := by
  rw [funext (coordinateFluxIntegrand_def g)]
  fun_prop

/-- Coefficients with derivatives `o(|x|⁻¹)` at infinity have flux density `o(|x|⁻¹)`. -/
theorem isLittleO_coordinateFluxIntegrand {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    (hg : ∀ i j, (fun x ↦ fderiv ℝ (fun y ↦ g y i j) x) =o[Bornology.cobounded _]
      fun x ↦ ‖x‖⁻¹) :
    coordinateFluxIntegrand g =o[Bornology.cobounded _] fun x ↦ ‖x‖⁻¹ := by
  have hD (i j k : Fin n) : (fun x ↦ fderiv ℝ (fun y ↦ g y i j) x (EuclideanSpace.single k 1))
      =o[Bornology.cobounded _] fun x ↦ ‖x‖⁻¹ :=
    ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k 1)).isBigO_comp _ _).trans_isLittleO
      (hg i j)
  -- The factor `x_j / |x|` is bounded.
  have hx (j : Fin n) : (fun x : EuclideanSpace ℝ (Fin n) ↦ x j / ‖x‖) =O[Bornology.cobounded _]
      fun _ ↦ (1 : ℝ) :=
    ((Asymptotics.isBigO_inv_norm_smul_apply _ (fun _ ↦ EuclideanSpace.proj j) id).trans
      (Asymptotics.isBigO_const_const _ one_ne_zero _)).congr_left fun x ↦ by simp [div_eq_inv_mul]
  rw [funext (coordinateFluxIntegrand_def g)]
  refine Asymptotics.IsLittleO.fun_sum fun j _ ↦ ?_
  simpa using ((Asymptotics.IsLittleO.fun_sum fun i _ ↦ (hD i j i).sub (hD i i j))).mul_isBigO
    (hx j)

/-- The flux density vanishes at the origin, where `x_j / |x|` is `0`. -/
@[simp]
theorem coordinateFluxIntegrand_zero_right (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) :
    coordinateFluxIntegrand g 0 = 0 := by
  simp [coordinateFluxIntegrand_def]

/-- Constant coefficients, such as those of the Euclidean metric, have zero flux density. -/
@[simp]
theorem coordinateFluxIntegrand_const (a : Fin n → Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand (fun _ ↦ a) x = 0 := by
  simp [coordinateFluxIntegrand_def]

/-- Constant coefficients, such as those of the Euclidean metric, have zero flux. -/
@[simp]
theorem normalizedCoordinateFlux_const (a : Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux (fun _ ↦ a) r = 0 := by
  simp [normalizedCoordinateFlux_def]

/-- The flux density at `x` only depends on the coefficients near `x`. -/
theorem coordinateFluxIntegrand_congr_of_eventuallyEq
    {g g' : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (h : g =ᶠ[𝓝 x] g') :
    coordinateFluxIntegrand g x = coordinateFluxIntegrand g' x := by
  have hd (i j : Fin n) : fderiv ℝ (fun y ↦ g y i j) x = fderiv ℝ (fun y ↦ g' y i j) x :=
    (h.fun_comp fun a ↦ a i j).fderiv_eq
  simp only [coordinateFluxIntegrand_def, hd]

/-- The flux at radius `r` only depends on the coefficients outside any smaller ball. -/
theorem normalizedCoordinateFlux_congr_of_eqOn
    {g g' : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {R r : ℝ}
    (h : EqOn g g' {x | R < ‖x‖}) (hR : R < r) :
    normalizedCoordinateFlux g r = normalizedCoordinateFlux g' r := by
  rw [normalizedCoordinateFlux_def, normalizedCoordinateFlux_def,
    setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx ↦ ?_]
  refine coordinateFluxIntegrand_congr_of_eventuallyEq <| Filter.eventuallyEq_of_mem
    ((isOpen_lt continuous_const continuous_norm).mem_nhds ?_) h
  simpa [mem_sphere_zero_iff_norm.1 hx] using hR

/-- The flux at large radii only depends on the coefficients outside a ball: coefficients that
agree outside a ball have the same mass. -/
theorem normalizedCoordinateFlux_eventuallyEq_of_eqOn
    {g g' : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {R : ℝ} (h : EqOn g g' {x | R < ‖x‖}) :
    normalizedCoordinateFlux g =ᶠ[atTop] normalizedCoordinateFlux g' :=
  (eventually_gt_atTop R).mono fun _ hr ↦ normalizedCoordinateFlux_congr_of_eqOn h hr

/-- If the flux density is constant, equal to `c`, on the sphere of radius `r > 0`, then the
normalized flux at radius `r` is `r ^ (n - 1) c / (2 (n - 1))`. -/
theorem normalizedCoordinateFlux_eq_of_eqOn_sphere
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} (hn : n ≠ 0) {r c : ℝ} (hr : 0 < r)
    (h : EqOn (coordinateFluxIntegrand g) (fun _ ↦ c) (sphere 0 r)) :
    normalizedCoordinateFlux g r = r ^ (n - 1) * c / (2 * (n - 1)) := by
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n - 1 + 1 := by
    rw [finrank_euclideanSpace_fin]
    omega
  have hS := (roundSphereVolume_pos (n - 1)).ne'
  rw [normalizedCoordinateFlux_def, setIntegral_congr_fun isClosed_sphere.measurableSet h,
    setIntegral_const, measureReal_def,
    euclideanHausdorffMeasure_sphere_eq_ofReal_pow_mul_roundSphereVolume hE 0 hr,
    ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hr.le _) (roundSphereVolume_pos _).le),
    smul_eq_mul]
  field_simp

/-- If the flux density equals `c |x| ^ (1 - n)` on the sphere of radius `r > 0`, then the
normalized flux at radius `r` is `c / (2 (n - 1))`, independently of `r`. -/
theorem normalizedCoordinateFlux_eq_of_eqOn_sphere_mul_rpow
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} (hn : n ≠ 0) {r c : ℝ} (hr : 0 < r)
    (h : EqOn (coordinateFluxIntegrand g) (fun x ↦ c * ‖x‖ ^ (1 - n : ℝ)) (sphere 0 r)) :
    normalizedCoordinateFlux g r = c / (2 * (n - 1)) := by
  rw [normalizedCoordinateFlux_eq_of_eqOn_sphere (c := c * r ^ (1 - n : ℝ)) hn hr
      fun x hx ↦ (h hx).trans (by dsimp only; rw [mem_sphere_zero_iff_norm.1 hx]),
    mul_left_comm, ← Real.rpow_natCast, ← Real.rpow_add hr, Nat.cast_sub (by omega), Nat.cast_one,
    sub_add_sub_cancel', sub_self, Real.rpow_zero, mul_one]

/-! ### Linearity -/

/-- The flux density is homogeneous in the coefficients. -/
@[simp]
theorem coordinateFluxIntegrand_smul (c : ℝ) (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand (c • g) x = c * coordinateFluxIntegrand g x := by
  have hd (i j : Fin n) :
      fderiv ℝ (fun y ↦ c * g y i j) x = c • fderiv ℝ (fun y ↦ g y i j) x := by
    have : (fun y ↦ c * g y i j) = c • fun y ↦ g y i j := by ext; simp
    rw [this, fderiv_const_smul_field, Pi.smul_apply]
  simp only [coordinateFluxIntegrand_def, Pi.smul_apply, smul_eq_mul, hd, FunLike.coe_smul,
    ← mul_sub, ← Finset.mul_sum, mul_assoc]

/-- The flux is homogeneous in the coefficients. -/
@[simp]
theorem normalizedCoordinateFlux_smul (c : ℝ) (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (r : ℝ) :
    normalizedCoordinateFlux (c • g) r = c * normalizedCoordinateFlux g r := by
  simp only [normalizedCoordinateFlux_def, coordinateFluxIntegrand_smul, integral_const_mul,
    mul_div_assoc]

/-- Adding constant coefficients, such as those of the Euclidean metric, does not change the
flux density. -/
@[simp]
theorem coordinateFluxIntegrand_const_add (a : Fin n → Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand (fun y i j ↦ a i j + g y i j) x = coordinateFluxIntegrand g x := by
  simp [coordinateFluxIntegrand_def]

/-- Adding constant coefficients, such as those of the Euclidean metric, does not change the
flux: the mass of `δ + h` is the mass of `h`. -/
@[simp]
theorem normalizedCoordinateFlux_const_add (a : Fin n → Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux (fun y i j ↦ a i j + g y i j) r = normalizedCoordinateFlux g r := by
  simp [normalizedCoordinateFlux_def]

/-- The flux density is additive in coefficients differentiable at the point. -/
theorem coordinateFluxIntegrand_add {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hg : ∀ i j, DifferentiableAt ℝ (fun y ↦ g y i j) x)
    (hh : ∀ i j, DifferentiableAt ℝ (fun y ↦ h y i j) x) :
    coordinateFluxIntegrand (g + h) x =
      coordinateFluxIntegrand g x + coordinateFluxIntegrand h x := by
  have hd (i j : Fin n) : fderiv ℝ (fun y ↦ (g + h) y i j) x =
      fderiv ℝ (fun y ↦ g y i j) x + fderiv ℝ (fun y ↦ h y i j) x := by
    simpa using fderiv_fun_add (hg i j) (hh i j)
  simp only [coordinateFluxIntegrand_def, hd, add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← add_mul, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Product rule for the flux density.** For a function `w` and coefficients `g` differentiable
at `x`, the flux density of `w g_ij` at `x` is `w(x)` times that of `g`, plus
`Σ_j (Σ_i (∂_i w g_ij - ∂_j w g_ii)) x_j / |x|`. -/
theorem coordinateFluxIntegrand_mul {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hw : DifferentiableAt ℝ w x) (hg : ∀ i j, DifferentiableAt ℝ (fun y ↦ g y i j) x) :
    coordinateFluxIntegrand (fun y i j ↦ w y * g y i j) x =
      w x * coordinateFluxIntegrand g x +
        ∑ j, (∑ i, (fderiv ℝ w x (EuclideanSpace.single i 1) * g x i j -
          fderiv ℝ w x (EuclideanSpace.single j 1) * g x i i)) * (x j / ‖x‖) := by
  have hd (i j : Fin n) : fderiv ℝ (fun y ↦ w y * g y i j) x =
      w x • fderiv ℝ (fun y ↦ g y i j) x + g x i j • fderiv ℝ w x :=
    fderiv_fun_mul hw (hg i j)
  simp only [coordinateFluxIntegrand_def, hd, add_apply, smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The flux is additive in coefficients differentiable on the sphere with integrable flux
densities. -/
theorem normalizedCoordinateFlux_add {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    (hg : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r, ∀ i j,
      DifferentiableAt ℝ (fun y ↦ g y i j) x)
    (hh : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r, ∀ i j,
      DifferentiableAt ℝ (fun y ↦ h y i j) x)
    (hgi : IntegrableOn (coordinateFluxIntegrand g) (sphere 0 r) μHE[n - 1])
    (hhi : IntegrableOn (coordinateFluxIntegrand h) (sphere 0 r) μHE[n - 1]) :
    normalizedCoordinateFlux (g + h) r =
      normalizedCoordinateFlux g r + normalizedCoordinateFlux h r := by
  rw [normalizedCoordinateFlux_def, normalizedCoordinateFlux_def, normalizedCoordinateFlux_def,
    ← add_div, ← integral_add hgi hhi,
    setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx ↦
      coordinateFluxIntegrand_add (hg x hx) (hh x hx)]

/-! ### Rescaling the coordinates -/

/-- Rescaling the coordinates by `s > 0` turns the flux density at `x` into `s` times the flux
density of `g` at `s • x`. -/
theorem coordinateFluxIntegrand_comp_smul (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand (fun y ↦ g (s • y)) x = s * coordinateFluxIntegrand g (s • x) := by
  have hd (i j : Fin n) :
      fderiv ℝ (fun y ↦ g (s • y) i j) x = s • fderiv ℝ (fun y ↦ g y i j) (s • x) :=
    fderiv_comp_smul (f := fun y ↦ g y i j) s
  have hx (j : Fin n) : (s • x) j / ‖s • x‖ = x j / ‖x‖ := by
    rw [PiLp.smul_apply, norm_smul, Real.norm_of_nonneg hs.le, smul_eq_mul,
      mul_div_mul_left _ _ hs.ne']
  simp only [coordinateFluxIntegrand_def, hd, hx, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    ← mul_sub, ← Finset.mul_sum, mul_assoc]

/-- **Scaling of the flux.** Rescaling the coordinates by `s > 0` turns the normalized flux at
radius `r` into `s ^ (2 - n)` times the normalized flux of `g` at radius `s r`. For the metric
`λ g` in the coordinates `√λ x`, whose coefficients are `g (x / √λ)`, this is the scaling law
`m(λ g) = λ ^ ((n - 2) / 2) m(g)` of the mass. -/
theorem normalizedCoordinateFlux_comp_smul (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    {s : ℝ} (hs : 0 < s) (r : ℝ) :
    normalizedCoordinateFlux (fun y ↦ g (s • y)) r =
      s ^ (2 - (n : ℤ)) * normalizedCoordinateFlux g (s * r) := by
  simp only [normalizedCoordinateFlux_def, coordinateFluxIntegrand_comp_smul g hs]
  rcases le_or_gt r 0 with hr | hr
  · rw [setIntegral_sphere_eq_zero_of_nonpos _ _ hr (by simp),
      setIntegral_sphere_eq_zero_of_nonpos _ _ (mul_nonpos_of_nonneg_of_nonpos hs.le hr) (by simp)]
    simp
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [coordinateFluxIntegrand_def]
  -- Both sphere integrals are pulled back to the unit sphere.
  rw [setIntegral_sphere_eq_smul_setIntegral_sphere_zero_one _ _ hr,
    setIntegral_sphere_eq_smul_setIntegral_sphere_zero_one _ _ (mul_pos hs hr)]
  simp only [zero_add, smul_smul, smul_eq_mul, integral_const_mul]
  have hpow : s ^ (2 - (n : ℤ)) * s ^ (n - 1) = s := by
    rw [← zpow_natCast, ← zpow_add₀ hs.ne', Nat.cast_sub hn, Nat.cast_one]
    simp
  generalize (∫ u in sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    coordinateFluxIntegrand g ((s * r) • u) ∂μHE[n - 1]) = I
  rw [mul_pow]
  linear_combination (-(r ^ (n - 1) * I / (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)))) * hpow

/-- **Scaling of the mass.** If the normalized flux of `g` tends to `m`, then the normalized flux
of the coefficients rescaled by `s > 0` tends to `s ^ (2 - n) m`. -/
theorem tendsto_normalizedCoordinateFlux_comp_smul
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {m : ℝ}
    (h : Tendsto (normalizedCoordinateFlux g) atTop (𝓝 m)) {s : ℝ} (hs : 0 < s) :
    Tendsto (normalizedCoordinateFlux fun y ↦ g (s • y)) atTop (𝓝 (s ^ (2 - (n : ℤ)) * m)) := by
  simp only [funext (normalizedCoordinateFlux_comp_smul g hs)]
  exact (h.comp (tendsto_id.const_mul_atTop hs)).const_mul _

/-! ### Conformally flat coefficients -/

/-- The flux density of the conformally flat coefficients `f(x) δ_ij` is `(1 - n)` times the
radial derivative of `f`. -/
theorem coordinateFluxIntegrand_conformal (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand (fun y i j ↦ if i = j then f y else 0) x =
      (1 - n) * (fderiv ℝ f x x / ‖x‖) := by
  have hsum₁ (j : Fin n) : ∑ i, fderiv ℝ (fun y ↦ if i = j then f y else 0) x
      (EuclideanSpace.single i 1) = fderiv ℝ f x (EuclideanSpace.single j 1) := by
    rw [Fintype.sum_eq_single j fun i hij ↦ by simp [hij]]
    simp
  have hx : fderiv ℝ f x x = ∑ j, x j * fderiv ℝ f x (EuclideanSpace.single j 1) := by
    nth_rw 2 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x]
    simp
  simp only [coordinateFluxIntegrand_def, Finset.sum_sub_distrib, hsum₁, ↓reduceIte,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hx, Finset.mul_sum,
    Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The flux density of the radial conformally flat coefficients `w(|x|) δ_ij` at `x ≠ 0` is
`(1 - n) w'(|x|)`. -/
theorem coordinateFluxIntegrand_conformal_radial (w : ℝ → ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) :
    coordinateFluxIntegrand (fun y i j ↦ if i = j then w ‖y‖ else 0) x = (1 - n) * deriv w ‖x‖ := by
  rw [coordinateFluxIntegrand_conformal]
  have hnorm : DifferentiableAt ℝ (‖·‖) x := (contDiffAt_norm ℝ hx (n := 1)).differentiableAt
    one_ne_zero
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  by_cases hw : DifferentiableAt ℝ w ‖x‖
  · have h : HasFDerivAt (fun y ↦ w ‖y‖) (deriv w ‖x‖ • fderiv ℝ (‖·‖) x) x :=
      hw.hasDerivAt.comp_hasFDerivAt x hnorm.hasFDerivAt
    simp [h.fderiv, hnorm.fderiv_norm_self, hx']
  rw [fderiv_zero_of_not_differentiableAt ((differentiableAt_comp_norm_iff hx).not.2 hw),
    deriv_zero_of_not_differentiableAt hw]
  simp

/-- **The flux of a radial conformally flat metric.** For `n ≥ 2` and `r > 0`, the normalized
flux of the coefficients `w(|x|) δ_ij` at radius `r` is `-r ^ (n - 1) w'(r) / 2`. -/
theorem normalizedCoordinateFlux_conformal_radial (hn : 2 ≤ n) (w : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    normalizedCoordinateFlux (fun y : EuclideanSpace ℝ (Fin n) ↦ fun i j ↦
      if i = j then w ‖y‖ else 0) r = -(r ^ (n - 1) * deriv w r) / 2 := by
  have hn' : (n : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (Nat.one_lt_cast.2 hn).ne'
  rw [normalizedCoordinateFlux_eq_of_eqOn_sphere (c := (1 - n) * deriv w r) (by omega) hr
    fun x hx ↦ ?_]
  · field_simp
    ring
  · have hx' : ‖x‖ = r := mem_sphere_zero_iff_norm.1 hx
    exact (coordinateFluxIntegrand_conformal_radial w (norm_pos_iff.1 (hx' ▸ hr))).trans
      (by rw [hx'])

/-- **The mass of a conformally flat end.** For `n ≥ 3`, the normalized flux of the coefficients
`(1 + c |x| ^ (2 - n)) ^ (4 / (n - 2)) δ_ij` tends to `2 c`. For `c = m / 2` these are the
coefficients of the spatial Schwarzschild metric of mass `m` (Cecchini–Zeidler, Example 2.2). -/
theorem tendsto_normalizedCoordinateFlux_conformal_one_add_mul_rpow (hn : 3 ≤ n) (c : ℝ) :
    Tendsto (normalizedCoordinateFlux fun y : EuclideanSpace ℝ (Fin n) ↦ fun i j ↦
      if i = j then (1 + c * ‖y‖ ^ (2 - n : ℝ)) ^ (4 / (n - 2 : ℝ)) else 0) atTop (𝓝 (2 * c)) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set p : ℝ := 4 / (n - 2)
  set B : ℝ → ℝ := fun r ↦ 1 + c * r ^ (2 - n : ℝ)
  have hB : Tendsto B atTop (𝓝 1) := by
    have h := tendsto_rpow_neg_atTop (y := n - 2) (by linarith)
    simpa [B] using (h.const_mul c).const_add 1
  -- Eventually `r > 0` and `B r > 0`, and then the flux is `2 c B(r) ^ (p - 1)`.
  have heq : (fun r ↦ 2 * c * B r ^ (p - 1)) =ᶠ[atTop] normalizedCoordinateFlux
      fun y : EuclideanSpace ℝ (Fin n) ↦ fun i j ↦ if i = j then B ‖y‖ ^ p else 0 := by
    filter_upwards [eventually_gt_atTop 0, hB.eventually (lt_mem_nhds one_pos)] with r hr hBr
    have hd : HasDerivAt (fun t ↦ B t ^ p)
        (c * ((2 - n) * r ^ ((2 - n : ℝ) - 1)) * p * B r ^ (p - 1)) r :=
      (((Real.hasDerivAt_rpow_const (Or.inl hr.ne')).const_mul c).const_add 1).rpow_const
        (Or.inl hBr.ne')
    have hp : (2 - n) * p = -4 := by
      simp only [p]
      field_simp [show (n : ℝ) - 2 ≠ 0 by linarith]
      ring
    rw [normalizedCoordinateFlux_eq_of_eqOn_sphere_mul_rpow
      (c := (1 - n) * (c * (2 - n) * p * B r ^ (p - 1))) (by omega) hr fun x hx ↦ ?_]
    · rw [eq_div_iff (by linarith)]
      linear_combination (n - 1) * c * B r ^ (p - 1) * hp
    · have hx' : ‖x‖ = r := mem_sphere_zero_iff_norm.1 hx
      refine (coordinateFluxIntegrand_conformal_radial (fun t ↦ B t ^ p)
        (norm_pos_iff.1 (hx' ▸ hr))).trans ?_
      dsimp only
      rw [hx', hd.deriv, show (2 - n : ℝ) - 1 = 1 - n by ring]
      ring
  refine Tendsto.congr' heq ?_
  simpa using (hB.rpow_const (Or.inl one_ne_zero)).const_mul (2 * c)

/-! ### A non-conformal perturbation -/

/-- The coefficients `x_i x_j |x| ^ (-n)` have flux density `(n - 1) |x| ^ (1 - n)` away from the
origin. -/
theorem coordinateFluxIntegrand_mul_mul_rpow {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    coordinateFluxIntegrand (fun y i j ↦ y i * y j * ‖y‖ ^ (-(n : ℝ))) x =
      (n - 1) * ‖x‖ ^ (1 - n : ℝ) := by
  set a := -(n : ℝ) * ‖x‖ ^ (-(n : ℝ) - 2)
  set ψ := ‖x‖ ^ (-(n : ℝ))
  have hψ := hasFDerivAt_norm_rpow_of_ne (-(n : ℝ)) hx
  -- The derivative of `x_i x_j |x| ^ (-n)` in the direction of the basis vector `e_k`.
  have hD (i j k : Fin n) : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ y i * y j *
      ‖y‖ ^ (-(n : ℝ))) x (EuclideanSpace.single k 1) =
        a * x i * x j * x k + ψ * (x i * (if j = k then 1 else 0) +
          x j * (if i = k then 1 else 0)) := by
    have h := (((EuclideanSpace.proj i).hasFDerivAt (x := x)).fun_mul
      ((EuclideanSpace.proj j).hasFDerivAt (x := x))).fun_mul hψ
    simp only [EuclideanSpace.coe_proj] at h
    rw [h.fderiv]
    simp only [add_apply, smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
      EuclideanSpace.coe_proj, PiLp.single_apply, smul_eq_mul, conj_trivial, one_mul, a, ψ]
    ring
  -- The inner sum `Σ_i (∂_i g_ij - ∂_j g_ii)` is `(n - 1) |x| ^ (-n) x_j`.
  have hinner (j : Fin n) :
      ∑ i, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ y i * y j * ‖y‖ ^ (-(n : ℝ))) x
        (EuclideanSpace.single i 1) - fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦
          y i * y i * ‖y‖ ^ (-(n : ℝ))) x (EuclideanSpace.single j 1)) = (n - 1) * ψ * x j := by
    calc _ = ∑ i, (ψ * x j + ψ * (if j = i then x i else 0) - 2 * (ψ * if i = j then x i else 0)) :=
          Finset.sum_congr rfl fun i _ ↦ by
            rw [hD, hD]
            by_cases h : i = j
            · subst h
              simp only [ite_true]
              ring
            · simp only [h, Ne.symm h, ite_false, ite_true]
              ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hN : ∑ j, x j * x j = ‖x‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq x, sq]
  have hpow : ‖x‖ ^ (1 - n : ℝ) = ψ * ‖x‖ := by
    rw [sub_eq_neg_add, Real.rpow_add (norm_pos_iff.2 hx), Real.rpow_one]
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  simp only [coordinateFluxIntegrand_def, hinner]
  calc _ = (n - 1) * ψ / ‖x‖ * ∑ j, x j * x j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = _ := by
        rw [hN, hpow]
        field_simp

/-- **The mass sees non-conformal terms.** For `n ≥ 2` and `r > 0`, the normalized flux of the
coefficients `x_i x_j |x| ^ (-n)` at radius `r` is `1 / 2`. So the metric
`δ_ij + ε x_i x_j |x| ^ (-n)`, whose coefficients are not a multiple of `δ_ij` for `ε ≠ 0`, has
mass `ε / 2`
(`TauCeti.normalizedCoordinateFlux_const_add`, `TauCeti.normalizedCoordinateFlux_smul`). -/
theorem normalizedCoordinateFlux_mul_mul_rpow (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    normalizedCoordinateFlux (fun y : EuclideanSpace ℝ (Fin n) ↦ fun i j ↦
      y i * y j * ‖y‖ ^ (-(n : ℝ))) r = 1 / 2 := by
  have hn' : (n : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (Nat.one_lt_cast.2 hn).ne'
  rw [normalizedCoordinateFlux_eq_of_eqOn_sphere_mul_rpow (c := n - 1) (by omega) hr
    fun x hx ↦ coordinateFluxIntegrand_mul_mul_rpow
      (norm_pos_iff.1 ((mem_sphere_zero_iff_norm.1 hx).symm ▸ hr))]
  field_simp

end TauCeti
