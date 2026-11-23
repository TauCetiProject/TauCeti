/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent.Clutching
import TauCeti.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.MeasureTheory.Integral.PolarCoord

/-!
# The Fubini–Study area of the standard sphere of the Riemann sphere

The standard sphere `TauCeti.riemannSphereSquare` of the Riemann sphere `OnePoint ℂ` is the based
sphere `I² / ∂I² → OnePoint ℂ`, based at `∞`, that maps the open square onto `ℂ` along rays from its
centre. On it the clutching number of the complex tangent bundle, its first Chern number, is `2`
(`TauCeti.clutchingNumber_tangentSpace_riemannSphereSquare`). This file computes its symplectic
area: the integral of the Fubini–Study form `ω_FS` (`OnePoint.fubiniStudyForm`) over its class in
`π₂(OnePoint ℂ, ∞)` is `1` (`OnePoint.sphereIntegral_fubiniStudyForm_riemannSphereSquare`), the
total area of the sphere. For the form `a • ω_FS` of the sphere of area `a` the area of the class is
`a` (by `TauCeti.sphereIntegral_smul`). The area and the first Chern number of a sphere class are
the two periods with which capped Hamiltonian Floer theory on the two-sphere filters and grades its
Novikov coefficients.

The integral of a closed form over a class of `π₂` is computed on a smooth representative
(`TauCeti.sphereIntegral_mk_of_contMDiff`). The standard sphere itself is not smooth: its radial
rescaling `2 c / √(1 - r²)` uses the sup radius `r` of the offset `c = (s - 1/2) + (t - 1/2) i`
from the centre of the square. Instead, with `q = |c|²` and the smooth profile
`ψ(q) = expNegInvGlue (1/4 - q)`, which is positive for `q < 1/4` and vanishes for `q ≥ 1/4`,
consider the map `w = c / ψ(q)` of the plane, equal to `∞` where `ψ(q) = 0`. It is smooth: near a
point with `ψ(q) ≠ 0` it is the smooth `ℂ`-valued map `c / ψ(q)`, and near a point with
`ψ(q) = 0`, where `c ≠ 0`, it is the inverted chart's preimage of the smooth map `ψ(q) / c`. Both
maps rescale each ray from the centre of the square by a positive factor, so in the inverted
coordinate the straight line `c / ((1 - τ) √(1 - r²) / 2 + τ ψ(q))` joins them through spheres
based at `∞` (the denominator only vanishes on the boundary of the square, and for `τ = 1` outside
the disc `q < 1/4`). Hence `w` represents the class of the standard sphere.

On the disc `q < 1/4` the derivatives of `w = c / ψ(q)` give the integrand
`ω_FS(∂s w, ∂t w) = ρ(w) Im (conj (∂s w) ∂t w) = G'(q) / π` for the primitive
`G(q) = q / (ψ(q)² + q)`, which is `0` at `q = 0` and `1` for `q ≥ 1/4`; at the remaining points
`ψ` attains its minimum `0`, so the derivative of `w`, read in the inverted chart, vanishes, and so
does `G'(q)`. Integrating in polar coordinates, the integral is
`2π ∫₀^∞ r G'(r²) / π dr = G(1/4) - G(0) = 1`.

## Main results

* `OnePoint.sphereIntegral_fubiniStudyForm_riemannSphereSquare`: the Fubini–Study form integrates
  to `1` over the class of the standard sphere in `π₂(OnePoint ℂ, ∞)`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Section 2 (the Fubini–Study metric, normalized so that a line has area one).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Section 11.1 (the symplectic area and first Chern number of spherical classes).
-/

public section

noncomputable section

open Set Filter Function MeasureTheory TauCeti ComplexConjugate
open scoped Manifold Topology TauCeti.ComplexManifold Topology.Homotopy

namespace OnePoint

/-! ### The point `c / d` of the Riemann sphere -/

/-- The point `c / d` of the Riemann sphere for `c : ℂ` and real `d`, read as `∞` when `d = 0`. -/
private def divPoint (c : ℂ) (d : ℝ) : OnePoint ℂ :=
  if d = 0 then ∞ else ((c / d : ℂ) : OnePoint ℂ)

private theorem divPoint_of_ne_zero (c : ℂ) {d : ℝ} (hd : d ≠ 0) :
    divPoint c d = ((c / d : ℂ) : OnePoint ℂ) := by
  simp [divPoint, hd]

private theorem divPoint_zero (c : ℂ) : divPoint c 0 = ∞ := by
  simp [divPoint]

/-- Away from `c = 0` the point `c / d` is read in the inverted chart as `d / c`, including
`d = 0`. -/
private theorem divPoint_eq_invChart_symm {c : ℂ} (hc : c ≠ 0) (d : ℝ) :
    divPoint c d = invChart.symm (d • c⁻¹) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [divPoint_zero]
  · have h : d • c⁻¹ ≠ 0 := smul_ne_zero hd (inv_ne_zero hc)
    rw [divPoint_of_ne_zero c hd, invChart_symm_of_ne_zero h, Complex.real_smul, mul_inv, inv_inv,
      div_eq_mul_inv, mul_comm]

/-- Near a point where `d ≠ 0`, the map `x ↦ c x / d x` into the Riemann sphere is the inclusion
of the `ℂ`-valued map `c / d`. -/
private theorem divPoint_eventuallyEq_coe {X : Type*} [TopologicalSpace X] {c : X → ℂ}
    {d : X → ℝ} (hd : Continuous d) {x : X} (hx : d x ≠ 0) :
    (fun y ↦ divPoint (c y) (d y)) =ᶠ[𝓝 x] fun y ↦ ((c y / d y : ℂ) : OnePoint ℂ) := by
  filter_upwards [hd.continuousAt.eventually_ne hx] with y hy
  exact divPoint_of_ne_zero _ hy

/-- Near a point where `c ≠ 0`, the map `x ↦ c x / d x` into the Riemann sphere is read in the
inverted chart as `d / c`. -/
private theorem divPoint_eventuallyEq_invChart_symm {X : Type*} [TopologicalSpace X] {c : X → ℂ}
    {d : X → ℝ} (hc : Continuous c) {x : X} (hx : c x ≠ 0) :
    (fun y ↦ divPoint (c y) (d y)) =ᶠ[𝓝 x] fun y ↦ invChart.symm (d y • (c y)⁻¹) := by
  filter_upwards [hc.continuousAt.eventually_ne hx] with y hy
  exact divPoint_eq_invChart_symm hy _

/-- The map `x ↦ c x / d x` into the Riemann sphere is continuous when `c` and `d` are, provided
`c` does not vanish where `d` does. -/
private theorem continuous_divPoint {X : Type*} [TopologicalSpace X] {c : X → ℂ} {d : X → ℝ}
    (hc : Continuous c) (hd : Continuous d) (h : ∀ x, d x = 0 → c x ≠ 0) :
    Continuous fun x ↦ divPoint (c x) (d x) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : d x = 0
  · have hcx := h x hx
    refine ContinuousAt.congr ?_ (divPoint_eventuallyEq_invChart_symm hc hcx).symm
    exact (invChart.continuousOn_symm.continuousAt (by simp)).comp
      ((hd.continuousAt.smul (hc.continuousAt.inv₀ hcx)))
  · refine ContinuousAt.congr ?_ (divPoint_eventuallyEq_coe hd hx).symm
    exact continuous_coe.continuousAt.comp
      (hc.continuousAt.div (Complex.continuous_ofReal.comp hd).continuousAt
        (by exact_mod_cast hx))

/-- The map `p ↦ c p / d p` from the plane into the Riemann sphere is smooth when `c` and `d` are,
provided `c` does not vanish where `d` does. -/
private theorem contMDiff_divPoint {c : ℝ × ℝ → ℂ} {d : ℝ × ℝ → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (h : ∀ x, d x = 0 → c x ≠ 0) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) fun x ↦ divPoint (c x) (d x) := by
  intro x
  by_cases hx : d x = 0
  · have hcx := h x hx
    refine ContMDiffAt.congr_of_eventuallyEq ?_
      (divPoint_eventuallyEq_invChart_symm hc.continuous hcx)
    exact contMDiff_invChart_symm_real.contMDiffAt.comp x
      ((hd.contDiffAt.smul (hc.contDiffAt.inv hcx)).contMDiffAt)
  · refine ContMDiffAt.congr_of_eventuallyEq ?_ (divPoint_eventuallyEq_coe hd.continuous hx)
    have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun y ↦ c y / (d y : ℂ)) x := by
      have h := hc.contDiffAt.mul (ContDiffAt.inv (f := fun y ↦ (d y : ℂ))
        (Complex.ofRealCLM.contDiff.comp hd).contDiffAt (Complex.ofReal_ne_zero.2 hx))
      simp only [div_eq_mul_inv]
      exact h
    exact contMDiff_coe_real.contMDiffAt.comp x hg.contMDiffAt

/-- Where `d ≠ 0`, the derivative of `p ↦ c p / d p`, read in the affine chart, is that of the
`ℂ`-valued map `p ↦ (d p)⁻¹ • c p`. -/
private theorem mfderiv_divPoint_of_ne_zero {c : ℝ × ℝ → ℂ} {d : ℝ × ℝ → ℝ} (hd : Continuous d)
    {x : ℝ × ℝ} (hx : d x ≠ 0) {D : ℝ × ℝ →L[ℝ] ℂ}
    (hD : HasFDerivAt (fun y ↦ (d y)⁻¹ • c y) D x) (v : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (fun y ↦ divPoint (c y) (d y)) x v = D v := by
  have hD' : HasFDerivAt (fun y ↦ c y / (d y : ℂ)) D x := by
    convert hD using 2 with y
    rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
  have h : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (fun y ↦ ((c y / d y : ℂ) : OnePoint ℂ)) x
      ((ContinuousLinearMap.id ℝ ℂ).comp D) :=
    (hasMFDerivAt_coe _).comp x hD'.hasMFDerivAt
  rw [(divPoint_eventuallyEq_coe hd hx).mfderiv_eq, h.mfderiv]
  -- The goal is `(tangentSpaceCast _ _ ∘L id ∘L D) v = D v`: `mfderiv_eq` inserts Mathlib's
  -- definitional cast between tangent spaces, which has no rewriting API.
  rfl

/-- Where `d` attains the value `0` as its minimum and `c ≠ 0`, the map `p ↦ c p / d p` has zero
derivative: read in the inverted chart it is `d / c`, whose derivative vanishes there with that
of `d`. -/
private theorem mfderiv_divPoint_of_isLocalMin {c : ℝ × ℝ → ℂ} {d : ℝ × ℝ → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d) {x : ℝ × ℝ} (hcx : c x ≠ 0)
    (hx : d x = 0) (hmin : IsLocalMin d x) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (fun y ↦ divPoint (c y) (d y)) x = 0 := by
  have hd' : HasFDerivAt d (0 : ℝ × ℝ →L[ℝ] ℝ) x := by
    have h : HasFDerivAt d (fderiv ℝ d x) x := (hd.differentiable (by simp) x).hasFDerivAt
    rwa [hmin.hasFDerivAt_eq_zero h] at h
  have hinv : HasFDerivAt (fun y ↦ (c y)⁻¹) (fderiv ℝ (fun y ↦ (c y)⁻¹) x) x :=
    ((hc.contDiffAt.inv hcx).differentiableAt (by simp)).hasFDerivAt
  have hk : HasFDerivAt (fun y ↦ d y • (c y)⁻¹) (0 : ℝ × ℝ →L[ℝ] ℂ) x := by
    convert hd'.smul hinv using 1
    simp [hx]
  have hinvChart := (contMDiff_invChart_symm_real (n := 1) (d x • (c x)⁻¹)).mdifferentiableAt
    one_ne_zero
  have h : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (fun y ↦ invChart.symm (d y • (c y)⁻¹)) x
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) invChart.symm (d x • (c x)⁻¹)).comp 0) :=
    hinvChart.hasMFDerivAt.comp x hk.hasMFDerivAt
  rw [(divPoint_eventuallyEq_invChart_symm hc.continuous hcx).mfderiv_eq, h.mfderiv]
  ext v
  simp

/-! ### A smooth representative of the standard sphere -/

/-- The offset `(s - 1/2) + (t - 1/2) i` of a point of the plane from the centre of the unit
square. -/
private def offset (p : ℝ × ℝ) : ℂ :=
  ((p.1 - 1 / 2 : ℝ) : ℂ) + ((p.2 - 1 / 2 : ℝ) : ℂ) * Complex.I

/-- The squared distance `(s - 1/2)² + (t - 1/2)²` from the centre of the unit square. -/
private def radiusSq (p : ℝ × ℝ) : ℝ :=
  (p.1 - 1 / 2) ^ 2 + (p.2 - 1 / 2) ^ 2

/-- The profile `ψ(q) = expNegInvGlue (1/4 - q)`, positive for `q < 1/4` and zero for
`q ≥ 1/4`. -/
private def profile (q : ℝ) : ℝ :=
  expNegInvGlue (1 / 4 - q)

/-- The smooth representative `w = c / ψ(|c|²)` of the standard sphere, `∞` outside the disc
`|c|² < 1/4`. -/
private def smoothSphere (p : ℝ × ℝ) : OnePoint ℂ :=
  divPoint (offset p) (profile (radiusSq p))

private theorem offset_re (p : ℝ × ℝ) : (offset p).re = p.1 - 1 / 2 := by
  simp [offset]

private theorem offset_im (p : ℝ × ℝ) : (offset p).im = p.2 - 1 / 2 := by
  simp [offset]

private theorem norm_offset_sq (p : ℝ × ℝ) : ‖offset p‖ ^ 2 = radiusSq p := by
  rw [Complex.sq_norm, offset, Complex.normSq_add_mul_I, radiusSq]

private theorem norm_offset_div_sq (p : ℝ × ℝ) {ψ : ℝ} (hψ : 0 ≤ ψ) :
    ‖offset p / (ψ : ℂ)‖ ^ 2 = radiusSq p / ψ ^ 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hψ, div_pow, norm_offset_sq]

private theorem contDiff_offset : ContDiff ℝ (⊤ : ℕ∞) offset :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_fst.sub contDiff_const)).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_snd.sub contDiff_const)).mul contDiff_const)

private theorem contDiff_profile : ContDiff ℝ (⊤ : ℕ∞) profile :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)

private theorem contDiff_profile_radiusSq : ContDiff ℝ (⊤ : ℕ∞) fun p ↦ profile (radiusSq p) :=
  contDiff_profile.comp (by unfold radiusSq; fun_prop)

private theorem profile_nonneg (q : ℝ) : 0 ≤ profile q :=
  expNegInvGlue.nonneg _

private theorem profile_pos {q : ℝ} (hq : q < 1 / 4) : 0 < profile q :=
  expNegInvGlue.pos_of_pos (by linarith)

private theorem profile_eq_zero_iff {q : ℝ} : profile q = 0 ↔ 1 / 4 ≤ q := by
  rw [profile, expNegInvGlue.zero_iff_nonpos, sub_nonpos]

/-- The offset does not vanish where the profile does. -/
private theorem offset_ne_zero_of_profile_eq_zero {p : ℝ × ℝ} (hp : profile (radiusSq p) = 0) :
    offset p ≠ 0 := by
  intro h
  have h' := norm_offset_sq p
  rw [h, norm_zero] at h'
  linarith [profile_eq_zero_iff.1 hp]

private theorem contMDiff_smoothSphere : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) smoothSphere :=
  contMDiff_divPoint contDiff_offset contDiff_profile_radiusSq
    fun _ ↦ offset_ne_zero_of_profile_eq_zero

/-- The derivative of `expNegInvGlue` at `1/4 - q`, which is minus the derivative of the
profile at `q`. -/
private theorem hasDerivAt_profile (q : ℝ) :
    HasDerivAt profile (-deriv expNegInvGlue (1 / 4 - q)) q := by
  have h := ((expNegInvGlue.contDiff (n := 1)).differentiable (by simp)
    (1 / 4 - q)).hasDerivAt.comp q ((hasDerivAt_id q).const_sub (1 / 4))
  rw [show -deriv expNegInvGlue (1 / 4 - q) = deriv expNegInvGlue (1 / 4 - q) * -1 by ring]
  exact h

/-! ### The integrand -/

/-- The derivative `G'(q) = ψ(q) (ψ(q) - 2 q ψ'(q)) / (ψ(q)² + q)²` of the primitive
`G(q) = q / (ψ(q)² + q)`; the integrand of the Fubini–Study form along the smooth sphere at a
point with `|c|² = q` is `G'(q) / π`. -/
private def areaDensity (q : ℝ) : ℝ :=
  profile q * (profile q + 2 * q * deriv expNegInvGlue (1 / 4 - q)) / (profile q ^ 2 + q) ^ 2

/-- The primitive `G(q) = q / (ψ(q)² + q)` of `areaDensity`. -/
private def areaPrimitive (q : ℝ) : ℝ :=
  q / (profile q ^ 2 + q)

private theorem areaDensity_of_le {q : ℝ} (hq : 1 / 4 ≤ q) : areaDensity q = 0 := by
  simp [areaDensity, profile_eq_zero_iff.2 hq]

/-- The derivative of `ψ(|c|²)⁻¹ c` along a curve `γ` in the plane, at a time where
`ψ = ψ(|c|²) ≠ 0`: if `c ∘ γ` has derivative `v` and `|c|² ∘ γ` has derivative `r'`, it is
`ψ⁻¹ v + r' e ψ⁻² c`, for `e = expNegInvGlue' (1/4 - |c|²)`, which is minus the derivative of the
profile. -/
private theorem hasDerivAt_profile_inv_smul_offset {γ : ℝ → ℝ × ℝ} {τ : ℝ} {v : ℂ} {r' : ℝ}
    (ho : HasDerivAt (fun τ ↦ offset (γ τ)) v τ) (hr : HasDerivAt (fun τ ↦ radiusSq (γ τ)) r' τ)
    (h : profile (radiusSq (γ τ)) ≠ 0) :
    HasDerivAt (fun τ ↦ (profile (radiusSq (γ τ)))⁻¹ • offset (γ τ))
      ((profile (radiusSq (γ τ)))⁻¹ • v +
        (r' * deriv expNegInvGlue (1 / 4 - radiusSq (γ τ)) /
          profile (radiusSq (γ τ)) ^ 2) • offset (γ τ)) τ := by
  have hψ : HasDerivAt (fun τ ↦ profile (radiusSq (γ τ)))
      (-deriv expNegInvGlue (1 / 4 - radiusSq (γ τ)) * r') τ :=
    (hasDerivAt_profile _).comp τ hr
  have hp := hψ.inv h
  convert hp.smul ho using 3
  ring

/-- The partial derivative `∂s (ψ⁻¹ c)` of the smooth sphere in the affine chart, at a point where
`ψ = ψ(|c|²) ≠ 0`: it is `ψ⁻¹ + 2 (s - 1/2) e ψ⁻² c`, for `e = expNegInvGlue' (1/4 - |c|²)`. -/
private theorem hasDerivAt_fst {s t : ℝ} (h : profile (radiusSq (s, t)) ≠ 0) :
    HasDerivAt (fun s' ↦ (profile (radiusSq (s', t)))⁻¹ • offset (s', t))
      ((profile (radiusSq (s, t)))⁻¹ • (1 : ℂ) +
        (2 * (s - 1 / 2) * deriv expNegInvGlue (1 / 4 - radiusSq (s, t)) /
          profile (radiusSq (s, t)) ^ 2) • offset (s, t)) s := by
  have ho : HasDerivAt (fun s' ↦ offset (s', t)) 1 s := by
    simpa [offset] using (((hasDerivAt_id s).sub_const (1 / 2 : ℝ)).ofReal_comp).add_const
      (((t - 1 / 2 : ℝ) : ℂ) * Complex.I)
  have hr : HasDerivAt (fun s' ↦ radiusSq (s', t)) (2 * (s - 1 / 2)) s := by
    simpa [radiusSq] using
      (((hasDerivAt_id s).sub_const (1 / 2 : ℝ)).pow 2).add_const ((t - 1 / 2) ^ 2)
  exact hasDerivAt_profile_inv_smul_offset (γ := fun s' ↦ (s', t)) ho hr h

/-- The partial derivative `∂t (ψ⁻¹ c)` of the smooth sphere in the affine chart, at a point where
`ψ = ψ(|c|²) ≠ 0`: it is `ψ⁻¹ i + 2 (t - 1/2) e ψ⁻² c`, for `e = expNegInvGlue' (1/4 - |c|²)`. -/
private theorem hasDerivAt_snd {s t : ℝ} (h : profile (radiusSq (s, t)) ≠ 0) :
    HasDerivAt (fun t' ↦ (profile (radiusSq (s, t')))⁻¹ • offset (s, t'))
      ((profile (radiusSq (s, t)))⁻¹ • Complex.I +
        (2 * (t - 1 / 2) * deriv expNegInvGlue (1 / 4 - radiusSq (s, t)) /
          profile (radiusSq (s, t)) ^ 2) • offset (s, t)) t := by
  have ho : HasDerivAt (fun t' ↦ offset (s, t')) Complex.I t := by
    simpa [offset] using ((((hasDerivAt_id t).sub_const (1 / 2 : ℝ)).ofReal_comp).mul_const
      Complex.I).const_add (((s - 1 / 2 : ℝ) : ℂ))
  have hr : HasDerivAt (fun t' ↦ radiusSq (s, t')) (2 * (t - 1 / 2)) t := by
    simpa [radiusSq] using
      (((hasDerivAt_id t).sub_const (1 / 2 : ℝ)).pow 2).const_add ((s - 1 / 2) ^ 2)
  exact hasDerivAt_profile_inv_smul_offset (γ := fun t' ↦ (s, t')) ho hr h

/-- The smooth sphere has derivative `0` where the profile vanishes: there the profile attains its
minimum `0`. -/
private theorem mfderiv_smoothSphere_of_profile_eq_zero {p : ℝ × ℝ}
    (h : profile (radiusSq p) = 0) : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) smoothSphere p = 0 := by
  have hmin : IsLocalMin (fun p ↦ profile (radiusSq p)) p :=
    Filter.Eventually.of_forall fun p' ↦ by simpa [h] using profile_nonneg (radiusSq p')
  exact mfderiv_divPoint_of_isLocalMin contDiff_offset contDiff_profile_radiusSq
    (offset_ne_zero_of_profile_eq_zero h) h hmin

/-- **The integrand of the Fubini–Study form along the smooth sphere** is `G'(|c|²) / π`. -/
private theorem fubiniStudyForm_smoothSphere (p : ℝ × ℝ) :
    fubiniStudyForm.val (smoothSphere p) ![mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) smoothSphere p (1, 0),
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) smoothSphere p (0, 1)] =
      Real.pi⁻¹ * areaDensity (radiusSq p) := by
  by_cases h : profile (radiusSq p) = 0
  · rw [mfderiv_smoothSphere_of_profile_eq_zero h, areaDensity_of_le (profile_eq_zero_iff.1 h),
      mul_zero]
    exact (fubiniStudyForm.val _).map_coord_zero (0 : Fin 2) rfl
  obtain ⟨s, t⟩ := p
  have hψ : 0 < profile (radiusSq (s, t)) := (profile_nonneg _).lt_of_ne' h
  have hdiff : DifferentiableAt ℝ (fun p ↦ (profile (radiusSq p))⁻¹ • offset p) (s, t) :=
    ((contDiff_profile_radiusSq.contDiffAt.inv h).smul
      contDiff_offset.contDiffAt).differentiableAt (by simp)
  have hD := hdiff.hasFDerivAt
  have hmf (v : ℝ × ℝ) := mfderiv_divPoint_of_ne_zero contDiff_profile_radiusSq.continuous
    (c := offset) h hD v
  have h1 : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) smoothSphere (s, t) (1, 0) = _ :=
    (hmf (1, 0)).trans ((hasDerivAt_slice_left hdiff).unique (hasDerivAt_fst h))
  have h2 : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) smoothSphere (s, t) (0, 1) = _ :=
    (hmf (0, 1)).trans ((hasDerivAt_slice_right hdiff).unique (hasDerivAt_snd h))
  have hpt : smoothSphere (s, t) = ((offset (s, t) / profile (radiusSq (s, t)) : ℂ) : OnePoint ℂ) :=
    divPoint_of_ne_zero _ h
  rw [h1, h2]
  refine (SmoothBundleForm.eval₂_apply fubiniStudyForm (smoothSphere (s, t)) _ _).symm.trans ?_
  rw [hpt, eval₂_fubiniStudyForm_coe, fubiniStudyDensity_def, norm_offset_div_sq _ hψ.le]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
    Complex.smul_re, Complex.smul_im, offset_re, offset_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, smul_eq_mul, areaDensity]
  have hq : radiusSq (s, t) = (s - 1 / 2) ^ 2 + (t - 1 / 2) ^ 2 := rfl
  generalize deriv expNegInvGlue (1 / 4 - radiusSq (s, t)) = e
  generalize profile (radiusSq (s, t)) = ψ at hψ ⊢
  rw [hq]
  field_simp
  ring

/-! ### The integral over the plane -/

private theorem profile_sq_add_pos {q : ℝ} (hq : 0 ≤ q) : 0 < profile q ^ 2 + q := by
  rcases hq.eq_or_lt with rfl | hq
  · simpa using pow_pos (profile_pos (by norm_num : (0 : ℝ) < 1 / 4)) 2
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) hq

private theorem areaPrimitive_zero : areaPrimitive 0 = 0 := by
  simp [areaPrimitive]

private theorem areaPrimitive_of_le {q : ℝ} (hq : 1 / 4 ≤ q) : areaPrimitive q = 1 := by
  have hq' : q ≠ 0 := by positivity
  simp [areaPrimitive, profile_eq_zero_iff.2 hq, hq']

private theorem hasDerivAt_areaPrimitive {q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt areaPrimitive (areaDensity q) q := by
  unfold areaPrimitive
  convert (hasDerivAt_id' q).div (((hasDerivAt_profile q).pow 2).add (hasDerivAt_id' q))
    (profile_sq_add_pos hq).ne' using 1
  simp only [areaDensity, Pi.add_apply, Pi.pow_apply]
  field_simp
  ring

private theorem continuousAt_areaDensity {q : ℝ} (hq : 0 ≤ q) : ContinuousAt areaDensity q := by
  have hψ : Continuous profile := contDiff_profile.continuous
  have he : Continuous fun q : ℝ ↦ deriv expNegInvGlue (1 / 4 - q) :=
    ((expNegInvGlue.contDiff (n := 1)).continuous_deriv le_rfl).comp (by fun_prop)
  exact ((hψ.mul (hψ.add ((continuous_const.mul continuous_id).mul he))).continuousAt).div
    ((((hψ.pow 2).add continuous_id).pow 2).continuousAt)
    (pow_ne_zero 2 (profile_sq_add_pos hq).ne')

/-- The radial profile of the integrand integrates against `r dr` to `1 / (2π)`, through the
primitive `r ↦ G(r²) / (2π)`. -/
private theorem integral_Ioi_mul_areaDensity :
    ∫ r in Ioi (0 : ℝ), r * (Real.pi⁻¹ * areaDensity (r ^ 2)) = (2 * Real.pi)⁻¹ := by
  have hderiv (r : ℝ) : HasDerivAt (fun r : ℝ ↦ Real.pi⁻¹ * areaPrimitive (r ^ 2) / 2)
      (r * (Real.pi⁻¹ * areaDensity (r ^ 2))) r := by
    have hsq : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
    have h := ((HasDerivAt.comp (h := fun x : ℝ ↦ x ^ 2) r
      (hasDerivAt_areaPrimitive (q := r ^ 2) (sq_nonneg r)) hsq).const_mul
      Real.pi⁻¹).div_const 2
    exact h.congr_deriv (by ring)
  have hzero {r : ℝ} (hr : 1 / 2 ≤ |r|) : r * (Real.pi⁻¹ * areaDensity (r ^ 2)) = 0 := by
    rw [areaDensity_of_le (by nlinarith [sq_abs r, abs_nonneg r]), mul_zero, mul_zero]
  have hint : Integrable fun r : ℝ ↦ r * (Real.pi⁻¹ * areaDensity (r ^ 2)) := by
    refine Continuous.integrable_of_hasCompactSupport
      (continuous_iff_continuousAt.2 fun r ↦ continuousAt_id.mul (continuousAt_const.mul
        (ContinuousAt.comp (g := areaDensity) (f := fun r : ℝ ↦ r ^ 2)
          (continuousAt_areaDensity (sq_nonneg r)) (continuous_pow 2).continuousAt)))
      (HasCompactSupport.intro (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)) fun r hr ↦ ?_)
    refine hzero ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hr
    rcases hr with hr | hr
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have hlim : Tendsto (fun r : ℝ ↦ Real.pi⁻¹ * areaPrimitive (r ^ 2) / 2) atTop
      (𝓝 (Real.pi⁻¹ * 1 / 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with r hr
    rw [areaPrimitive_of_le (by nlinarith)]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _ ↦ hderiv r) hint.integrableOn hlim]
  simp only [zero_pow two_ne_zero, areaPrimitive_zero]
  ring

/-- The integrand integrates to `1` over `ℂ`, in polar coordinates. -/
private theorem integral_areaDensity_norm_sq :
    ∫ z : ℂ, Real.pi⁻¹ * areaDensity (‖z‖ ^ 2) = 1 := by
  rw [integral_fun_norm_complex fun r ↦ Real.pi⁻¹ * areaDensity (r ^ 2)]
  simp only [smul_eq_mul, integral_Ioi_mul_areaDensity]
  field_simp

/-- The integrand integrates to `1` over the plane `ℝ × ℝ`. -/
private theorem integral_areaDensity_radiusSq :
    ∫ p : ℝ × ℝ, Real.pi⁻¹ * areaDensity (radiusSq p) = 1 := by
  rw [← Complex.volume_preserving_equiv_real_prod.integral_comp']
  have h : (fun z : ℂ ↦ Real.pi⁻¹ * areaDensity (radiusSq (Complex.measurableEquivRealProd z))) =
      fun z ↦ (fun w : ℂ ↦ Real.pi⁻¹ * areaDensity (‖w‖ ^ 2))
        (z - (1 / 2 + 1 / 2 * Complex.I)) := by
    funext z
    simp only [Complex.sq_norm, Complex.normSq_apply, radiusSq]
    simp [sq]
  rw [h, integral_sub_right_eq_self (fun w : ℂ ↦ Real.pi⁻¹ * areaDensity (‖w‖ ^ 2)),
    integral_areaDensity_norm_sq]

/-- Outside the unit square the point is outside the disc `|c|² < 1/4`. -/
private theorem one_fourth_le_radiusSq_of_notMem {p : ℝ × ℝ}
    (hp : p ∉ Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) : 1 / 4 ≤ radiusSq p := by
  obtain ⟨a, b⟩ := p
  by_contra h
  simp only [radiusSq, not_le] at h
  refine hp ⟨Prod.mk_le_mk.2 ⟨?_, ?_⟩, Prod.mk_le_mk.2 ⟨?_, ?_⟩⟩ <;>
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2)]

/-- **The Fubini–Study integral of the smooth sphere over the unit square is `1`.** -/
private theorem rectangleIntegral_smoothSphere :
    rectangleIntegral fubiniStudyForm.val smoothSphere (0, 0) (1, 1) = 1 := by
  rw [← IsSmoothForm.setIntegral_eq_rectangleIntegral (fubiniStudyForm.isSmoothForm.of_le (by simp))
    (contMDiff_smoothSphere.of_le (by simp)) (by simp [Prod.mk_le_mk])]
  simp_rw [fubiniStudyForm_smoothSphere]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ by
    rw [areaDensity_of_le (one_fourth_le_radiusSq_of_notMem hp), mul_zero],
    integral_areaDensity_radiusSq]

/-! ### The class of the smooth sphere -/

private theorem offset_eq_squareCenterOffset (y : Fin 2 → unitInterval) :
    offset ((y 0 : ℝ), (y 1 : ℝ)) = squareCenterOffset y :=
  Complex.ext (by simp [offset_re]) (by simp [offset_im])

private theorem radiusSq_eq_norm_sq (y : Fin 2 → unitInterval) :
    radiusSq ((y 0 : ℝ), (y 1 : ℝ)) = ‖squareCenterOffset y‖ ^ 2 := by
  rw [← offset_eq_squareCenterOffset, norm_offset_sq]

/-- On the boundary of the unit square the point is outside the disc `|c|² < 1/4`. -/
private theorem profile_eq_zero_of_mem_boundary {y : Fin 2 → unitInterval}
    (hy : y ∈ Cube.boundary (Fin 2)) : profile (radiusSq ((y 0 : ℝ), (y 1 : ℝ))) = 0 := by
  refine profile_eq_zero_iff.2 ?_
  obtain ⟨i, hi | hi⟩ := hy <;> fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at hi <;>
    simp only [radiusSq, hi, Set.Icc.coe_zero, Set.Icc.coe_one] <;>
    nlinarith [sq_nonneg ((y 0 : ℝ) - 1 / 2), sq_nonneg ((y 1 : ℝ) - 1 / 2)]

/-- The smooth sphere on the unit square, a sphere based at `∞`. -/
private def smoothSphereGenLoop : Ω^ (Fin 2) (OnePoint ℂ) ∞ :=
  ⟨⟨fun y ↦ smoothSphere ((y 0 : ℝ), (y 1 : ℝ)),
    contMDiff_smoothSphere.continuous.comp (by fun_prop)⟩, fun y hy ↦ by
      simp [smoothSphere, profile_eq_zero_of_mem_boundary hy, divPoint_zero]⟩

/-- The denominator `√(1 - r²) / 2` of the standard sphere `c / (√(1 - r²) / 2)`. -/
private def squareScale (y : Fin 2 → unitInterval) : ℝ :=
  √(1 - cubeRadius y ^ 2) / 2

private theorem squareScale_pos {y : Fin 2 → unitInterval} (hy : y ∉ Cube.boundary (Fin 2)) :
    0 < squareScale y :=
  half_pos (Real.sqrt_pos.2 (one_sub_cubeRadius_sq_pos hy))

private theorem squareScale_of_mem {y : Fin 2 → unitInterval} (hy : y ∈ Cube.boundary (Fin 2)) :
    squareScale y = 0 := by
  simp [squareScale, (cubeRadius_eq_one_iff y).2 hy]

/-- The denominator of the straight-line homotopy, in the inverted coordinate, from the standard
sphere to the smooth sphere. -/
private def homotopyScale (x : unitInterval × (Fin 2 → unitInterval)) : ℝ :=
  (1 - (x.1 : ℝ)) * squareScale x.2 + x.1 * profile (radiusSq ((x.2 0 : ℝ), (x.2 1 : ℝ)))

private theorem continuous_homotopyScale : Continuous homotopyScale := by
  unfold homotopyScale squareScale radiusSq
  have := contDiff_profile.continuous
  have := continuous_cubeRadius (N := Fin 2)
  fun_prop

/-- The offset from the centre does not vanish where the denominator of the homotopy does. -/
private theorem squareCenterOffset_ne_zero_of_homotopyScale_eq_zero
    {x : unitInterval × (Fin 2 → unitInterval)} (hx : homotopyScale x = 0) :
    squareCenterOffset x.2 ≠ 0 := by
  intro hc
  have hy : x.2 ∉ Cube.boundary (Fin 2) := fun hb ↦ squareCenterOffset_ne_zero_of_mem hb hc
  have ha := squareScale_pos hy
  have hb : 0 < profile (radiusSq ((x.2 0 : ℝ), (x.2 1 : ℝ))) :=
    profile_pos (by rw [radiusSq_eq_norm_sq, hc]; norm_num)
  have ht := x.1.property.1
  have ht' := x.1.property.2
  rcases ht'.lt_or_eq with ht' | ht'
  · have : 0 < (1 - (x.1 : ℝ)) * squareScale x.2 := mul_pos (by linarith) ha
    have : 0 ≤ (x.1 : ℝ) * profile (radiusSq ((x.2 0 : ℝ), (x.2 1 : ℝ))) :=
      mul_nonneg ht hb.le
    simp only [homotopyScale] at hx
    linarith
  · simp [homotopyScale, ht', hb.ne'] at hx

/-- **The smooth sphere represents the standard sphere.** In the inverted coordinate the
straight line `c / ((1 - τ) √(1 - r²) / 2 + τ ψ(|c|²))` joins the standard sphere to the smooth
sphere relative to the boundary of the square. -/
private def smoothSphereHomotopy :
    (riemannSphereSquare : C(Fin 2 → unitInterval, OnePoint ℂ)).HomotopyRel
      smoothSphereGenLoop (Cube.boundary (Fin 2)) where
  toFun x := divPoint (squareCenterOffset x.2) (homotopyScale x)
  continuous_toFun := continuous_divPoint (by fun_prop) continuous_homotopyScale
    fun _ ↦ squareCenterOffset_ne_zero_of_homotopyScale_eq_zero
  map_zero_left y := by
    by_cases hy : y ∈ Cube.boundary (Fin 2)
    · simp [homotopyScale, squareScale_of_mem hy, divPoint_zero,
        riemannSphereSquare_apply_of_mem hy]
    · have ha := squareScale_pos hy
      simp only [homotopyScale, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
      rw [divPoint_of_ne_zero _ ha.ne', GenLoop.coe_coe, riemannSphereSquare_apply_of_notMem hy]
      congr 1
      simp only [squareScale, Complex.ofReal_div, Complex.ofReal_ofNat]
      field_simp
  map_one_left y := by
    simp [homotopyScale, smoothSphereGenLoop, smoothSphere, offset_eq_squareCenterOffset]
  prop' τ y hy := by
    simp [homotopyScale, squareScale_of_mem hy, profile_eq_zero_of_mem_boundary hy,
      divPoint_zero, riemannSphereSquare_apply_of_mem hy]

/-! ### The Fubini–Study area of the standard sphere -/

/-- **The Fubini–Study area of the standard sphere is `1`.** The integral of the Fubini–Study form
`ω_FS` over the class of the standard sphere `TauCeti.riemannSphereSquare` in
`π₂(OnePoint ℂ, ∞)` is `1`, the total area of the Riemann sphere. On the same class the first Chern
number of the tangent bundle is `2` (`TauCeti.clutchingNumber_tangentSpace_riemannSphereSquare`). -/
theorem sphereIntegral_fubiniStudyForm_riemannSphereSquare :
    sphereIntegral fubiniStudyForm.val ∞ ⟦riemannSphereSquare⟧ = 1 := by
  rw [show (⟦riemannSphereSquare⟧ : HomotopyGroup (Fin 2) (OnePoint ℂ) ∞) =
      ⟦smoothSphereGenLoop⟧ from Quotient.sound ⟨smoothSphereHomotopy⟩,
    sphereIntegral_mk_of_contMDiff (fubiniStudyForm.isSmoothForm.of_le (by simp))
      ((SmoothForm.isClosed_def _).1 isSymplectic_fubiniStudyForm.isClosed) contMDiff_smoothSphere
      fun _ ↦ rfl,
    rectangleIntegral_smoothSphere]

end OnePoint
