/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor.Normalized
public import TauCeti.Analysis.PDE.Vortex.Gauge.Cohomology
public import TauCeti.Analysis.PDE.Vortex.Kernel.Tangent
import TauCeti.Analysis.Calculus.FDeriv.Pi.Lp
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Sobolev.BesselPotential.ZeroAtInfty
import TauCeti.RingTheory.Polynomial.SymmetricPower

/-!
# The velocity of the family of plane vortices over the divisor space

For `c ∈ ℂᵐ`, `m ≥ 1`, the normalized vortex `y_c` (`TauCeti.Vortex.normalizedVortex`) is the
framed degree-`m` plane vortex whose zero divisor has the symmetric coordinates `c`, put in the
gauge whose section has the fixed winding phase at infinity. It depends smoothly on `c`, jointly in
the point (`TauCeti.Vortex.contDiff_normalizedVortex_uncurry`) and in every Sobolev space
(`TauCeti.Vortex.SobolevFieldSpace.contDiff_subRef_normalizedVortex`). This file computes its
velocity `∂_v y_c = w ↦ ∂_v (c ↦ y_c (w))` in a direction `v ∈ ℂᵐ`, in terms of the kernel of the
gauge-fixed operator `L_{y_c} = d₀* ⊕ d₁` and its divisor coordinates
`E : ker L_{y_c} ≃ ℂᵐ` (`TauCeti.Vortex.gaugeFixedKernelEquivCoeff`), which identify the kernel
with the tangent space of `Sym^m ℂ` through the divisor variation
(`TauCeti.Vortex.IsDivisorVariation`):

`∂_v y_c = E⁻¹ v + d₀ u`

for a phase `u` in `H^(k+2)`
(`TauCeti.Vortex.exists_fderiv_normalizedVortex_eq_add_gaugeDirection`).
So the abstract identification of `ker L_{y_c}` with the tangent space of the divisor space is the
derivative of the family of vortices, up to an infinitesimal gauge transformation, collisions of
zeros included. In particular the velocity is an infinitesimal gauge transformation only when
`v = 0` (`TauCeti.Vortex.exists_fderiv_normalizedVortex_eq_gaugeDirection_iff`): the normalized
family is transverse to the gauge orbits. When the divisor of the inserted vortex moves with the
point of a curve, this is the identification of the moving vortex's velocity with the kernel
direction of the moving divisor.

The proof assembles three facts about the velocity.

* **It solves the linearized equation.** For any jointly `C²` family of plane fields `F_q` that
  solve the vortex equation near a parameter `p`, the velocity `∂_v F_p` satisfies
  `d₁ ∂_v F_p = 0` at `F_p` (`TauCeti.Vortex.linearizedEquation_fderiv_eq_zero`): differentiate the
  equation in the parameter, swapping the parameter and spatial derivatives
  (`TauCeti.fderiv_fderiv_slice_apply_comm`).
* **It lies in every Sobolev space.** The coordinates of `y_c - x_m` form a smooth family in
  `H^s(ℂ)⁴`, whose parameter derivative is the continuous representative of the velocity
  (`BesselPotentialSpace.fderiv_apply_mem_realSobolevFunctions`), so the velocity lies in
  `H^s(ℂ)⁴` for every `s` (`TauCeti.Vortex.fderiv_normalizedVortex_mem_sobolevFields`). With the
  first point, it is a cocycle of the deformation complex at `y_c`, so it differs from an element
  of `ker L_{y_c}` by a coboundary `d₀ u`
  (`TauCeti.Vortex.exists_sub_gaugeDirection_mem_gaugeFixedKernel`).
* **Its divisor variation is `v`.** The section of `y_c` is `H_c P_c`, with `P_c` the monic
  polynomial with lower coefficients `c` and `H_c` jointly smooth and nowhere zero. Its velocity is
  `∂_v H_c P_c + H_c R_v`, where `R_v = ∂_v P_c` is the polynomial with coefficients `v`
  (`TauCeti.Polynomial.fderiv_eval_monicOfCoeff_apply`), so its divisor variation is `R_v`
  (`TauCeti.Vortex.isDivisorVariation_fderiv_of_sectionValue_eq_mul`,
  `TauCeti.Vortex.isDivisorVariation_fderiv_normalizedVortex`). Coboundaries have divisor
  variation zero (`TauCeti.Vortex.isDivisorVariation_gaugeDirection`), and `E` is characterized by
  the divisor variation (`TauCeti.Vortex.gaugeFixedKernelEquivDegreeLT_eq_iff`).

## Main results

* `TauCeti.Vortex.linearizedEquation_fderiv_eq_zero`: the velocity of a family of vortices solves
  the linearized vortex equation.
* `TauCeti.Vortex.isDivisorVariation_fderiv_normalizedVortex`: the velocity of `y_c` in the
  direction `v` has divisor variation the polynomial with coefficients `v`.
* `TauCeti.Vortex.fderiv_normalizedVortex_mem_sobolevFields`: the velocity of `y_c` lies in
  `H^s(ℂ)⁴` for every `s`.
* `TauCeti.Vortex.exists_fderiv_normalizedVortex_eq_add_gaugeDirection`: `∂_v y_c = E⁻¹ v + d₀ u`.
* `TauCeti.Vortex.exists_fderiv_normalizedVortex_eq_gaugeDirection_iff`: `∂_v y_c` is an
  infinitesimal gauge transformation exactly when `v = 0`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
-/

public section

noncomputable section

open Complex Filter Topology Polynomial MeasureTheory Module TemperedDistribution
open scoped ContDiff BesselPotentialSpace

namespace TauCeti.Vortex

/-! ### The velocity of a family of vortices solves the linearized equation -/

section Linearization

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {F : P → ℂ → EuclideanSpace ℝ (Fin 4)} {p : P} {z : ℂ}

/-- A coordinate of a jointly `C²` family of fields, as a function of the parameter and the
point. -/
private theorem contDiffAt_coord (hF : ContDiffAt ℝ 2 (Function.uncurry F) (p, z)) (i : Fin 4) :
    ContDiffAt ℝ (minSmoothness ℝ 2) (fun pq : P × ℂ ↦ F pq.1 pq.2 i) (p, z) := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ).contDiff.contDiffAt.comp _ hF

/-- A spatial derivative of a coordinate of a jointly `C²` family is differentiable in the
parameter. -/
private theorem differentiableAt_fderiv_coord (hF : ContDiffAt ℝ 2 (Function.uncurry F) (p, z))
    (i : Fin 4) (e : ℂ) : DifferentiableAt ℝ (fun q ↦ fderiv ℝ (fun w ↦ F q w i) z e) p := by
  have hG := contDiffAt_coord hF i
  exact ((TauCeti.hasFDerivAt_spatialFDeriv hG).clm_apply (hasFDerivAt_const e p)).differentiableAt

/-- A coordinate of a jointly `C²` family is differentiable in the parameter. -/
private theorem differentiableAt_coord (hF : ContDiffAt ℝ 2 (Function.uncurry F) (p, z))
    (i : Fin 4) : DifferentiableAt ℝ (fun q ↦ F q z i) p :=
  ((contDiffAt_coord hF i).differentiableAt (by simp)).comp (f := fun q ↦ (q, z)) p
    (differentiableAt_id.prodMk (differentiableAt_const z))

/-- A jointly `C²` family is differentiable in the parameter. -/
private theorem differentiableAt_slice (hF : ContDiffAt ℝ 2 (Function.uncurry F) (p, z)) :
    DifferentiableAt ℝ (fun q ↦ F q z) p :=
  (hF.differentiableAt two_ne_zero).comp (f := fun q ↦ (q, z)) p
    (differentiableAt_id.prodMk (differentiableAt_const z))

/-- The parameter derivative of a spatial derivative of a coordinate is the spatial derivative of
that coordinate of the velocity. -/
private theorem fderiv_fderiv_coord (hF : ContDiffAt ℝ 2 (Function.uncurry F) (p, z))
    (i : Fin 4) (e : ℂ) (v : P) :
    fderiv ℝ (fun q ↦ fderiv ℝ (fun w ↦ F q w i) z e) p v =
      fderiv ℝ (fun w ↦ fderiv ℝ (fun q ↦ F q w) p v i) z e := by
  have hG := contDiffAt_coord hF i
  rw [TauCeti.fderiv_fderiv_slice_apply_comm hG v e]
  have hev : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 (Function.uncurry F) (p, w) :=
    (continuous_const.prodMk continuous_id : Continuous fun w : ℂ ↦ (p, w)).continuousAt.eventually
      (hF.eventually (by simp))
  have heq : (fun w ↦ fderiv ℝ (fun q ↦ F q w i) p v) =ᶠ[𝓝 z]
      fun w ↦ fderiv ℝ (fun q ↦ F q w) p v i := by
    filter_upwards [hev] with w hw
    exact (differentiableAt_slice hw).fderiv_piLp_apply i v
  rw [heq.fderiv_eq]

/-- **The velocity of a family of vortices solves the linearized equation.** Let `F` be a family of
plane fields, jointly `C²` in the parameter and the point near `(p, z)`, solving the vortex
equation at `z` for all parameters near `p`. Then for every direction `v` the velocity
`w ↦ ∂_v F_p (w)` satisfies the linearized vortex equation `d₁ ∂_v F_p = 0` of `F_p` at `z`. -/
theorem linearizedEquation_fderiv_eq_zero (hF : ContDiffAt ℝ 2 (Function.uncurry F) (p, z))
    (hsol : ∀ᶠ q in 𝓝 p, equation (F q) z = 0) (v : P) :
    linearizedEquation (F p) (fun w ↦ fderiv ℝ (fun q ↦ F q w) p v) z = 0 := by
  -- Each component of `q ↦ equation (F q) z` vanishes near `p`, so its derivative vanishes.
  have hzero (k : Fin 3) {g : P → ℝ} {L : P →L[ℝ] ℝ} (hL : HasFDerivAt g L p)
      (hg : ∀ q, g q = equation (F q) z k) : L v = 0 := by
    have h : g =ᶠ[𝓝 p] fun _ ↦ 0 := hsol.mono fun q hq ↦ by simp [hg, hq]
    rw [← hL.fderiv, h.fderiv_eq, fderiv_const_apply, zero_apply]
  have hc (i : Fin 4) := (differentiableAt_coord hF i).hasFDerivAt
  have hd (i : Fin 4) (e : ℂ) := (differentiableAt_fderiv_coord hF i e).hasFDerivAt
  have hdd (i : Fin 4) (e : ℂ) := fderiv_fderiv_coord hF i e v
  have hcc (i : Fin 4) := (differentiableAt_slice hF).fderiv_piLp_apply i v
  ext k
  fin_cases k
  · have h := hzero 0 (((hd 0 I).sub (hd 1 1)).add
      ((((hc 2).pow 2).add ((hc 3).pow 2)).const_mul (1 / 2) |>.sub_const (1 / 8)))
      fun q ↦ by rw [equation_apply_zero]; simp only [Pi.add_apply, Pi.sub_apply]; ring
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, nsmul_eq_mul, hdd, hcc] at h
    simp only [Fin.zero_eta, Fin.isValue, linearizedEquation_apply_zero, PiLp.zero_apply]
    norm_num at h
    linear_combination h
  · have h := hzero 1 ((((hd 2 1).sub (hd 3 I)).sub ((hc 0).mul (hc 3))).sub ((hc 1).mul (hc 2)))
      fun q ↦ by rw [equation_apply_one]; rfl
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, hdd, hcc] at h
    simp only [Fin.mk_one, Fin.isValue, linearizedEquation_apply_one, PiLp.zero_apply]
    linear_combination h
  · have h := hzero 2 ((((hd 3 1).add (hd 2 I)).add ((hc 0).mul (hc 2))).sub ((hc 1).mul (hc 3)))
      fun q ↦ by rw [equation_apply_two]; rfl
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, hdd, hcc] at h
    simp only [Fin.reduceFinMk, Fin.isValue, linearizedEquation_apply_two, PiLp.zero_apply]
    linear_combination h

end Linearization

/-! ### The divisor variation of the velocity -/

section DivisorVariation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {F : P → ℂ → EuclideanSpace ℝ (Fin 4)} {p : P} {z : ℂ}

/-- The section, as a real-linear map of the field value. -/
private noncomputable def sectionCLM : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℂ :=
  (2 : ℝ) • ((EuclideanSpace.proj 2 : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ).smulRight (1 : ℂ) +
    (EuclideanSpace.proj 3 : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ).smulRight I)

private theorem sectionCLM_apply (x : ℂ → EuclideanSpace ℝ (Fin 4)) (w : ℂ) :
    sectionCLM (x w) = sectionValue x w := by
  simp [sectionCLM, sectionValue_apply, Complex.real_smul]
  ring

/-- The section of the velocity of a family of fields is the velocity of its sections. -/
private theorem sectionValue_fderiv (hF : DifferentiableAt ℝ (fun q ↦ F q z) p) (v : P) :
    sectionValue (fun w ↦ fderiv ℝ (fun q ↦ F q w) p v) z =
      fderiv ℝ (fun q ↦ sectionValue (F q) z) p v := by
  have h := (sectionCLM.hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  rw [show (fun q ↦ sectionValue (F q) z) = ⇑sectionCLM ∘ fun q ↦ F q z from
    funext fun q ↦ (sectionCLM_apply (F q) z).symm, h, ← sectionCLM_apply,
    ContinuousLinearMap.comp_apply]

/-- **The divisor variation of the velocity of a family of fields.** Let `F` be a family of fields
whose sections factor as `α_q = H_q Q_q` through polynomials `Q_q` and functions `H` jointly `C¹`
in the parameter and the point, with `H_p` nowhere zero. If the zero divisor `D` has polynomial
`Q_p` and the velocity of the polynomials in the direction `v` is `R`, then `R` is a divisor
variation of the velocity `w ↦ ∂_v F_p (w)` of the fields. -/
theorem isDivisorVariation_fderiv_of_sectionValue_eq_mul {H : P → ℂ → ℂ} {Q : P → ℂ[X]}
    {D : Multiset ℂ} {R : ℂ[X]} {v : P} (hF : ∀ w, DifferentiableAt ℝ (fun q ↦ F q w) p)
    (hH : ContDiff ℝ 1 (Function.uncurry H)) (hH₀ : ∀ w, H p w ≠ 0)
    (hsec : ∀ q w, sectionValue (F q) w = H q w * (Q q).eval w)
    (hQ : ∀ w, DifferentiableAt ℝ (fun q ↦ (Q q).eval w) p)
    (hR : ∀ w, fderiv ℝ (fun q ↦ (Q q).eval w) p v = R.eval w)
    (hD : (D.map fun a ↦ X - C a).prod = Q p) :
    IsDivisorVariation (F p) (fun w ↦ fderiv ℝ (fun q ↦ F q w) p v) D R := by
  -- The derivative of `H` along the parameter, as a function of the point.
  have hHd (w : ℂ) : HasFDerivAt (fun q ↦ H q w)
      ((fderiv ℝ (Function.uncurry H) (p, w)).comp (ContinuousLinearMap.inl ℝ P ℂ)) p :=
    ((hH.differentiable one_ne_zero (p, w)).hasFDerivAt).comp (f := fun q ↦ (q, w)) p
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) p w)
  refine isDivisorVariation_iff.2 ⟨fun w ↦ fderiv ℝ (fun q ↦ H q w) p v / H p w, ?_, fun w ↦ ?_⟩
  · have hc : Continuous fun w ↦ fderiv ℝ (Function.uncurry H) (p, w) (v, 0) :=
      ((hH.continuous_fderiv one_ne_zero).comp (continuous_const.prodMk continuous_id)).clm_apply
        continuous_const
    refine Continuous.div ?_ ((hH.continuous).comp (continuous_const.prodMk continuous_id)) hH₀
    convert hc using 2 with w
    simp [(hHd w).fderiv]
  · rw [sectionValue_fderiv (hF w) v,
      show (fun q ↦ sectionValue (F q) w) = fun q ↦ H q w * (Q q).eval w from
        funext fun q ↦ hsec q w,
      fderiv_fun_mul (hHd w).differentiableAt (hQ w), hsec p w, hD]
    simp only [add_apply, smul_apply, smul_eq_mul, hR]
    field_simp [hH₀ w]
    ring

variable {m : ℕ}

open TauCeti.Polynomial in
/-- The section of the normalized vortex `y_c` is `g_c exp (u_c) P_c`. -/
private theorem sectionValue_normalizedVortex (c : Fin m → ℂ) (w : ℂ) :
    sectionValue (normalizedVortex c) w =
      ((polynomialGauge c w : ℂ) * (Real.exp (backgroundAmplitude (monicOfCoeff c).eval w +
        reducedSolution (monicOfCoeff c) w) : ℂ)) * (monicOfCoeff c).eval w := by
  rw [normalizedVortex_def, sectionValue_gaugeTransform, sectionValue_polynomialVortex, mul_assoc]

open TauCeti.Polynomial in
/-- **The velocity of the normalized vortices moves the divisor by its coordinates.** The
velocity `∂_v y_c` of the normalized vortices in the direction `v ∈ ℂᵐ` has divisor variation the
polynomial with coefficients `v`, the velocity of the monic polynomial `P_c` with lower
coefficients `c`. -/
theorem isDivisorVariation_fderiv_normalizedVortex (c v : Fin m → ℂ) :
    IsDivisorVariation (normalizedVortex c) (fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v)
      ((Sym.coeffEquiv ℂ m).symm c : Multiset ℂ) ((degreeLTEquiv ℂ m).symm v) := by
  have hP : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ (monicOfCoeff p.1).eval p.2 :=
    (contDiff_eval_monicOfCoeff contDiff_fst contDiff_snd).restrict_scalars ℝ
  refine isDivisorVariation_fderiv_of_sectionValue_eq_mul
    (H := fun c' w ↦ (polynomialGauge c' w : ℂ) * (Real.exp (backgroundAmplitude
      (monicOfCoeff c').eval w + reducedSolution (monicOfCoeff c') w) : ℂ))
    (fun w ↦ (contDiff_normalizedVortex_uncurry.differentiable (by simp) (c, w)).comp
      (f := fun c' ↦ (c', w)) c (differentiableAt_id.prodMk (differentiableAt_const w)))
    ?_ (fun w ↦ mul_ne_zero (Circle.coe_ne_zero _) (by exact_mod_cast (Real.exp_pos _).ne'))
    sectionValue_normalizedVortex
    (fun w ↦ ((hasFDerivAt_eval_monicOfCoeff c w).restrictScalars ℝ).differentiableAt)
    (fun w ↦ ?_) ?_
  · exact (contDiff_polynomialGauge.mul (ofRealCLM.contDiff.comp (Real.contDiff_exp.comp
      ((contDiff_parametric_backgroundAmplitude (f := fun c' ↦ (monicOfCoeff c').eval) hP).add
        contDiff_reducedSolution_monicOfCoeff)))).of_le (by simp)
  · rw [((hasFDerivAt_eval_monicOfCoeff c w).restrictScalars ℝ).fderiv,
      ContinuousLinearMap.coe_restrictScalars', ← (hasFDerivAt_eval_monicOfCoeff c w).fderiv,
      fderiv_eval_monicOfCoeff_apply]
  · rw [← Sym.toMonic_coeffEquiv_symm, Sym.coe_toMonic, ofMultiset_apply]

end DivisorVariation

/-! ### The velocity in the kernel of the gauge-fixed operator -/

section NormalizedVortex

open BesselPotentialSpace TauCeti.Polynomial

variable {m : ℕ}

/-- The Sobolev embedding of the coordinate `subRef x j` of a continuous field of `A_m^s` is the
complexification of `z ↦ x(z)ⱼ - x_m(z)ⱼ`, at every point. -/
private theorem toZeroAtInfty_subRef_apply {f : ContDiffBump (0 : ℝ)} {s : ℝ}
    (hs : finrank ℝ ℂ < 2 * s) (x : SobolevFieldSpace f m s) (j : Fin 4) (w : ℂ) :
    toZeroAtInfty hs (x.subRef j) w = ((x w j - referenceField f m w j : ℝ) : ℂ) := by
  have h0 : 0 ≤ s := TauCeti.nonneg_of_finrank_lt_two_mul hs
  have hae := (coeFn_inclusionLp_ae_eq_toZeroAtInfty (hs := hs) h0 (x.subRef j)).symm.trans
    (toLp_inclusion h0 (x.subRef j) ▸ SobolevFieldSpace.coeFn_toLp_inclusion_subRef h0 x j)
  have hc : Continuous fun z ↦ ((x z j - referenceField f m z j : ℝ) : ℂ) :=
    continuous_ofReal.comp
      (((EuclideanSpace.proj j).continuous.comp x.continuous).sub
        ((EuclideanSpace.proj j).continuous.comp (contDiff_referenceField f m).continuous))
  exact congrFun ((Continuous.ae_eq_iff_eq volume (toZeroAtInfty hs _).continuous hc).1 hae) w

/-- **The velocity of the normalized vortices lies in every Sobolev space.** The derivative
`w ↦ ∂_v y_c (w)` of the normalized vortices `y_c` in the divisor coordinates `c`, in the direction
`v`, lies in `H^s(ℂ)⁴` for every `s`. -/
theorem fderiv_normalizedVortex_mem_sobolevFields (hm : 0 < m) (c v : Fin m → ℂ) (s : ℝ) :
    (fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v) ∈ sobolevFields s := by
  refine sobolevFields_mono (le_max_left s 2) (mem_sobolevFields.2 fun j ↦ ?_)
  have hs : finrank ℝ ℂ < 2 * max s 2 := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith [le_max_right s 2]
  have hU : ContDiff ℝ ∞ fun c' ↦
      (SobolevFieldSpace.normalizedVortex hm default (max s 2) c').subRef j :=
    contDiff_pi.1 (SobolevFieldSpace.contDiff_subRef_normalizedVortex hm default
      (by positivity)) j
  have h := fderiv_apply_mem_realSobolevFunctions hs (hU.differentiable (by simp) c)
    (g := fun c' w ↦ normalizedVortex c' w j - referenceField default m w j)
    (fun c' w ↦ by rw [toZeroAtInfty_subRef_apply hs, SobolevFieldSpace.coe_normalizedVortex]) v
  convert h using 2 with w
  have hd : DifferentiableAt ℝ (fun c' ↦ normalizedVortex c' w) c :=
    (contDiff_normalizedVortex_uncurry.differentiable (by simp) (c, w)).comp
      (f := fun c' ↦ (c', w)) c (differentiableAt_id.prodMk (differentiableAt_const w))
  rw [fderiv_sub_const, hd.fderiv_piLp_apply]

/-- The velocity of the normalized vortices is smooth in the point. -/
private theorem contDiff_fderiv_normalizedVortex (c v : Fin m → ℂ) :
    ContDiff ℝ ∞ fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v := by
  have h : ContDiff ℝ ∞ (Function.uncurry fun (w : ℂ) (c' : Fin m → ℂ) ↦ normalizedVortex c' w) :=
    contDiff_normalizedVortex_uncurry.comp (contDiff_snd.prodMk contDiff_fst)
  exact (h.fderiv contDiff_const le_rfl).clm_apply contDiff_const

/-- **The velocity of the normalized vortices is the kernel field of its divisor coordinates, up
to gauge.** Let `y_c` be the normalized vortex with divisor coefficients `c ∈ ℂᵐ`, `m ≥ 1`, and let
`E : ker L_{y_c} ≃ ℂᵐ` be the divisor coordinates of the kernel of its gauge-fixed operator
(`TauCeti.Vortex.gaugeFixedKernelEquivCoeff`). For every direction `v ∈ ℂᵐ` and every `k ≥ 3`, the
velocity `∂_v y_c` of the family is the kernel field `E⁻¹ v` plus an infinitesimal gauge
transformation `d₀ u` with `u ∈ H^(k+2)` of class `C³`. -/
theorem exists_fderiv_normalizedVortex_eq_add_gaugeDirection (hm : 0 < m) {k : ℕ} (hk : 3 ≤ k)
    (c v : Fin m → ℂ) :
    ∃ u ∈ realSobolevFunctions ℂ (k + 2) 2, ContDiff ℝ 3 u ∧
      (fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v) =
        ((gaugeFixedKernelEquivCoeff (contDiff_normalizedVortex c)
            (fun w ↦ by simp [equation_normalizedVortex hm c w])
            (tendsto_normSq_normalizedVortex hm c)
            (isZeroMultiplicity_sectionValue_normalizedVortex c)).symm v :
          ℂ → EuclideanSpace ℝ (Fin 4)) + gaugeDirection (normalizedVortex c) u := by
  set δ := fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v
  have hsol := equation_normalizedVortex hm c
  -- The velocity is a cocycle of the deformation complex.
  have hcoc : δ ∈ deformationCocycles (normalizedVortex c) k := mem_deformationCocycles.2
    ⟨fderiv_normalizedVortex_mem_sobolevFields hm c v _,
      (contDiff_fderiv_normalizedVortex c v).of_le (by simp), fun w ↦
        linearizedEquation_fderiv_eq_zero
          (contDiff_normalizedVortex_uncurry.contDiffAt.of_le (by simp))
          (.of_forall fun c' ↦ equation_normalizedVortex hm c' w) v⟩
  obtain ⟨u, hu, hu3, hK⟩ := exists_sub_gaugeDirection_mem_gaugeFixedKernel hk
    (normalizedVortex_mem_framedFieldSpace hm default c _) (contDiff_normalizedVortex c).continuous
    hsol hcoc
  refine ⟨u, hu, hu3, ?_⟩
  -- Its harmonic representative has divisor variation `v`.
  have hdiv : IsDivisorVariation (normalizedVortex c) (δ - gaugeDirection (normalizedVortex c) u)
      ((Sym.coeffEquiv ℂ m).symm c : Multiset ℂ) ((degreeLTEquiv ℂ m).symm v) := by
    have h := (isDivisorVariation_fderiv_normalizedVortex c v).add
      ((isDivisorVariation_gaugeDirection _ hu3.continuous _).smul (-1))
    simpa [sub_eq_add_neg] using h
  set E := gaugeFixedKernelEquivCoeff (contDiff_normalizedVortex c)
    (fun w ↦ by simp [equation_normalizedVortex hm c w]) (tendsto_normSq_normalizedVortex hm c)
    (isZeroMultiplicity_sectionValue_normalizedVortex c)
  have hE : E.symm v = ⟨_, (Submodule.mem_inf.1 hK).left⟩ := by
    rw [LinearEquiv.symm_apply_eq, gaugeFixedKernelEquivCoeff_apply,
      (gaugeFixedKernelEquivDegreeLT_eq_iff _ _ _ _).2 hdiv, LinearEquiv.apply_symm_apply]
  rw [hE]
  simp

/-- **The normalized family is transverse to the gauge orbits.** For `m ≥ 1` and `k ≥ 3`, the
velocity `∂_v y_c` of the normalized vortices is an infinitesimal gauge transformation `d₀ u`, with
`u ∈ H^(k+2)` of class `C³`, only for `v = 0`. -/
theorem exists_fderiv_normalizedVortex_eq_gaugeDirection_iff (hm : 0 < m) {k : ℕ} (hk : 3 ≤ k)
    (c v : Fin m → ℂ) :
    (∃ u ∈ realSobolevFunctions ℂ (k + 2) 2, ContDiff ℝ 3 u ∧
      (fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v) =
        gaugeDirection (normalizedVortex c) u) ↔ v = 0 := by
  refine ⟨fun ⟨u', hu', hu'3, hδ'⟩ ↦ ?_, fun hv ↦ ⟨0, zero_mem _, contDiff_const, ?_⟩⟩
  · obtain ⟨u, hu, hu3, hδ⟩ := exists_fderiv_normalizedVortex_eq_add_gaugeDirection hm hk c v
    set E := gaugeFixedKernelEquivCoeff (contDiff_normalizedVortex c)
      (fun w ↦ by simp [equation_normalizedVortex hm c w]) (tendsto_normSq_normalizedVortex hm c)
      (isZeroMultiplicity_sectionValue_normalizedVortex c)
    -- `E⁻¹ v = d₀ (u' - u)` is a coboundary in the kernel of `L_{y_c}`, hence zero.
    have hB : (E.symm v : ℂ → EuclideanSpace ℝ (Fin 4)) ∈
        deformationCoboundaries (normalizedVortex c) k := by
      refine mem_deformationCoboundaries.2 ⟨u' - u, sub_mem hu' hu, hu'3.sub hu3, funext fun w ↦ ?_⟩
      rw [sub_eq_add_neg, ← neg_one_smul ℝ u,
        gaugeDirection_add _ (f := u') (g := (-1 : ℝ) • u) (hu'3.differentiable (by simp) w)
          ((hu3.const_smul (-1 : ℝ)).differentiable (by simp) w), gaugeDirection_smul,
        neg_one_smul, ← sub_eq_add_neg, ← congrFun hδ' w, congrFun hδ w]
      simp
    have h0 := eq_zero_of_mem_gaugeFixedKernel_of_mem_deformationCoboundaries (E.symm v).property hB
    simpa using congrArg E (Subtype.ext h0 : E.symm v = 0)
  · subst hv
    rw [gaugeDirection_zero]
    ext w : 1
    simp

end NormalizedVortex

end TauCeti.Vortex
