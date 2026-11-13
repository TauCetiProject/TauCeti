/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic
public import TauCeti.Geometry.Symplectic.Floer.Plane.Action

/-!
# The asymptotic orbit at the end of a finite-energy PSS plane

Let `𝔎` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from
a period-one `C¹` Hamiltonian `H` on a symplectic vector space `(V, ω)`, and let `ε = ±1` be the
sign of the end of `p` at `∞`. Let `u` be a solution of the Floer equation
`(du - X_𝔎)^{0,1} = 0` on a part `‖w‖ > r` of the end, for uniformly tame almost complex
structures `J(z)`, with image in a compact set and with finite energy there. Far out on the end
`𝔎` is `H(t) dt` in end coordinates.
For `R ∈ ℝ` write `ℓ_R(t) = u(φ(ε R + i t))` for the loop of `u` along the circle
`‖w‖ = exp (2πR)`, where `φ(z) = exp (2π ε z)` is the end lift. This file shows that `u` breaks
off a one-periodic orbit at its end:

* if `u` is `C¹`, there are a one-periodic orbit `x` of the Hamiltonian vector field,
  `x' = X_{H_t}(x)`, and radii `R_n → ∞` such that the loops `ℓ_{R_n}` converge uniformly to `x`
  (`SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation`);
* if `u` is `C²`, the orbit can moreover be chosen so that the actions `A_H(ℓ_R)` tend to `A_H(x)`
  as `R → ∞`
  (`SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation`);
* hence, for a `C²` solution on the whole plane with finite energy, the energy is
  `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`
  (`exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq` in
  `TauCeti.SymplecticForm`).

So `x` is the generator at which a PSS plane meets the Floer complex: an input for the positive
plane, an output for the negative plane. The energy identity of
`TauCeti.Geometry.Symplectic.Floer.Plane.Action` assumed convergence of the end actions; here it
follows from finite energy and compactness.

On the positive plane `ε = 1`, the end in the coordinates `(s, t)` of the end lift is a Floer
half-cylinder `s > a`, for any `a ≥ 2`, for the cylindrical datum `H(t) dt`, with the structures
`J ∘ φ`. Since `φ` is holomorphic, the Floer equation and the energy pull back along it
(`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_realChart_positive`), and `φ` is
injective on the half-strip `s > a`, `0 ≤ t < 1`, so the energy of the half-cylinder is at most
that of `u` on `‖w‖ > exp (2πa)`
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_realChart_positive_le`). The
results on finite-energy half-cylinders of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` then apply. The negative plane is the
positive plane for the reversed Hamiltonian `-H(-t)`
(`TauCeti.Floer.PSSPlane.perturbation_negative`), and its loops are the loops of the positive plane
traversed backwards. Reversing time turns an orbit `y` of `-H(-t)` into the orbit `t ↦ y(-t)` of
`H`, since both the time and the derivative change sign
(`TauCeti.SymplecticForm.hamiltonianVectorField_neg`). It also negates the action of a loop
relative to `-H(-t)` (`TauCeti.SymplecticForm.hamiltonianAction_comp_neg`), which transfers the
convergence of the end actions.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  asymptotics of the perturbed planes of the PSS maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
-/

public section

open Set Real Function MeasureTheory Filter
open TauCeti.Complex (realChart realChart_apply contDiff_realChart)
open scoped Topology

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V}
  {c M : ℝ} {K : Set V}

/-- The end lift of the positive plane in real coordinates, at a point `(s, t)`, is the image of
`s + i t`. -/
private theorem realChart_positive_mk (s t : ℝ) :
    realChart positive.cylindricalEndLift (s, t) =
      Complex.equivRealProdCLM
        (positive.cylindricalEndLift (↑(positive.endSign * s) + ↑t * Complex.I)) := by
  rw [realChart_apply, Complex.equivRealProdCLM_symm_apply, endSign_positive, one_mul]

/-- The half-cylinder `s > a` of the positive plane lies in the part `‖w‖ > exp (2πa)` of the
plane. -/
private theorem exp_lt_norm_realChart_positive {a : ℝ} {z : ℝ × ℝ} (hz : a < z.1) :
    Real.exp (2 * π * a) <
      ‖Complex.equivRealProdCLM.symm (realChart positive.cylindricalEndLift z)‖ := by
  rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, norm_cylindricalEndLift,
    endSign_positive, one_mul, Complex.equivRealProdCLM_symm_apply_re, Real.exp_lt_exp]
  nlinarith [Real.pi_pos]

/-- The part `‖w‖ > r` of the plane, in real coordinates, is open. -/
private theorem isOpen_lt_norm (r : ℝ) :
    IsOpen {z : ℝ × ℝ | r < ‖Complex.equivRealProdCLM.symm z‖} :=
  isOpen_lt continuous_const (continuous_norm.comp Complex.equivRealProdCLM.symm.continuous)

/-- Every part `‖w‖ > r` of the plane contains a part `‖w‖ > exp (2πa)` with `a ≥ 2`. -/
private theorem exists_two_le_exp_lt_norm_subset (r : ℝ) :
    ∃ a : ℝ, 2 ≤ a ∧ {z : ℝ × ℝ | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖} ⊆
      {z | r < ‖Complex.equivRealProdCLM.symm z‖} := by
  refine ⟨max 2 r, le_max_left _ _, fun z (hz : Real.exp _ < _) ↦ show r < _ from
    lt_of_le_of_lt ?_ hz⟩
  have h₁ := Real.add_one_le_exp (2 * π * max 2 r)
  have h₂ : 0 ≤ (2 * π - 1) * max 2 r :=
    mul_nonneg (by linarith [Real.two_le_pi]) (by linarith [le_max_left 2 r])
  linarith [le_max_right 2 r]

/-- The end lift of the positive plane is injective on the half-strip `s > a`, `0 ≤ t < 1`. -/
private theorem injOn_realChart_positive (a : ℝ) :
    InjOn (realChart positive.cylindricalEndLift) (Ioi a ×ˢ Ico 0 1) := by
  intro a ha b hb hab
  rw [realChart_apply, realChart_apply] at hab
  have ha' : Complex.equivRealProdCLM.symm a ∈ {z : ℂ | z.im ∈ Ico 0 (0 + 1)} := by
    simpa using ha.2
  have hb' : Complex.equivRealProdCLM.symm b ∈ {z : ℂ | z.im ∈ Ico 0 (0 + 1)} := by
    simpa using hb.2
  have h := positive.injOn_cylindricalEndLift 0 ha' hb' (Complex.equivRealProdCLM.injective hab)
  exact Complex.equivRealProdCLM.symm.injective h

/-- From `s = 2` on, the pullback of the datum of the positive plane along its end lift is the
cylindrical datum `H(t) dt`, so the Floer operators of the two data agree there. -/
private theorem perturbedFDeriv_comp_realChart_positive (ω : SymplecticForm V)
    (hH : Periodic H 1) (u : ℝ × ℝ → V) {z : ℝ × ℝ} (hz : 2 ≤ z.1) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      ω.perturbedFDeriv
        (perturbationPullback (realChart positive.cylindricalEndLift)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (realChart positive.cylindricalEndLift)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag) u z := by
  rw [positive.perturbationPullback_realChart_cylindricalEndLift_stdComplexLineReal H,
    positive.perturbationPullback_realChart_cylindricalEndLift_stdComplexLineImag hH]
  refine ContinuousLinearMap.ext fun a ↦ ?_
  simp only [perturbedFDeriv_apply, endSign_positive, one_mul,
    smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ z.1 - 1)]

/-- **The Floer equation on the end of the positive plane.** From `s = 2` on, if `u` solves the
Floer equation for the datum of the positive plane and the structures `J` at the image of `(s, t)`
under the end lift `φ`, then `u ∘ φ` solves the Floer equation at `(s, t)` for the cylindrical
datum `H(t) dt` and the structures `J ∘ φ`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_realChart_positive (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {z : ℝ × ℝ} (hz : 2 ≤ z.1)
    (hu : DifferentiableAt ℝ u (realChart positive.cylindricalEndLift z))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart positive.cylindricalEndLift z))
      (ω.perturbedFDeriv
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (realChart positive.cylindricalEndLift z) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart positive.cylindricalEndLift z))
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (u ∘ realChart positive.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [perturbedFDeriv_comp_realChart_positive ω hH _ hz]
  exact ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback
    ((contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable one_ne_zero z) hu
    (differentiableAt_perturbation_target hH hHs _ _ 1)
    (differentiableAt_perturbation_target hH hHs _ _ Complex.I)
    (Floer.isComplexLinearMap_fderiv_realChart (positive.hasDerivAt_cylindricalEndLift _)) hfloer

/-- From `s = 2` on, where `u` is differentiable at the image of `(s, t)` under the end lift `φ`
of the positive plane, the energy density of `u ∘ φ` at `(s, t)` for the cylindrical datum
`H(t) dt` is the Jacobian of `φ` times the energy density of `u` for the datum of the plane. -/
private theorem floerEnergyDensity_comp_realChart_positive (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {z : ℝ × ℝ} (hz : 2 ≤ z.1)
    (hu : DifferentiableAt ℝ u (realChart positive.cylindricalEndLift z)) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (u ∘ realChart positive.cylindricalEndLift) z =
      (fderiv ℝ (realChart positive.cylindricalEndLift) z).det *
        ω.floerEnergyDensity
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          (realChart positive.cylindricalEndLift z) := by
  rw [floerEnergyDensity_def, perturbedFDeriv_comp_realChart_positive ω hH _ hz,
    ← floerEnergyDensity_def]
  exact ω.floerEnergyDensity_perturbationPullback
    ((contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable one_ne_zero z) hu
    (differentiableAt_perturbation_target hH hHs _ _ 1)
    (differentiableAt_perturbation_target hH hHs _ _ Complex.I)

/-- **The energy on the end of the positive plane.** For `a ≥ 2`, if `u` is differentiable on the
part `‖w‖ > exp (2πa)` of the positive plane, then the energy of `u ∘ φ` on the half-cylinder
`s > a`, `0 ≤ t ≤ 1`, for the cylindrical datum `H(t) dt`, is at most the energy of `u` on that
part of the plane: the end lift `φ` is injective on the half-strip `0 ≤ t < 1` and preserves
orientation. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_positive_le (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {a : ℝ} (ha : 2 ≤ a)
    (hu : DifferentiableOn ℝ u
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖}) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≤
      ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) := by
  have hS : MeasurableSet (Ioi a ×ˢ Ico (0 : ℝ) 1) :=
    measurableSet_Ioi.prod measurableSet_Ico
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] Ioi a ×ˢ Ico 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ico_ae_eq_Icc.symm
  have hud {z : ℝ × ℝ} (hz : a < z.1) :
      DifferentiableAt ℝ u (realChart positive.cylindricalEndLift z) :=
    hu.differentiableAt ((isOpen_lt_norm _).mem_nhds (exp_lt_norm_realChart_positive hz))
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hS
    (injOn_realChart_positive a)
    (fun z _ ↦ (contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable
      one_ne_zero z) fun z hz ↦ by
      rw [floerEnergyDensity_comp_realChart_positive ω hH hHs (ha.trans hz.1.le) (hud hz.1),
        abs_of_pos (positive.det_fderiv_realChart_cylindricalEndLift_pos z)]]
  refine lintegral_mono_set ?_
  rintro _ ⟨z, hz, rfl⟩
  exact exp_lt_norm_realChart_positive hz.1

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The loops of the positive plane along its end are periodic. -/
private theorem periodic_comp_cylindricalEndLift_positive (u : ℝ × ℝ → V) (R : ℝ) :
    Periodic (fun t : ℝ ↦ u (Complex.equivRealProdCLM
      (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I)))) 1 := fun t ↦
  congrArg (fun w ↦ u (Complex.equivRealProdCLM w))
    (positive.periodic_cylindricalEndLift (positive.endSign * R) t)

/-- **The asymptotic orbit at the end of the positive plane.** This is the case `p = positive` of
`exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation`, on the part `‖w‖ > exp (2πa)`
with `a ≥ 2` and for an arbitrary Hamiltonian; the negative plane is reduced to it. -/
private theorem exists_periodic_hasDerivAt_tendstoUniformly_positive
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {a : ℝ} (ha : 2 ≤ a)
    (hu : ContDiffOn ℝ 1 u {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    (hK : IsCompact K)
    (huK : ∀ z, Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖ →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖ →
      ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I)))) x atTop := by
  set ψ := realChart positive.cylindricalEndLift
  have hψ : ContDiff ℝ 1 ψ := contDiff_realChart positive.contDiff_cylindricalEndLift
  have hud := hu.differentiableOn one_ne_zero
  obtain ⟨x, hxper, hx, φ, -, hφ, hux⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_floer (a := a) (J := J ∘ ψ) hHs hH
      (hu.comp hψ.contDiffOn fun z hz ↦ exp_lt_norm_realChart_positive hz.1)
      (fun s _ ↦ by
        simpa only [comp_apply, ψ, realChart_positive_mk] using
          periodic_comp_cylindricalEndLift_positive u s)
      hK (fun s hs t ↦ huK _ (exp_lt_norm_realChart_positive hs)) hc
      (fun z hz ↦ hJc _ (exp_lt_norm_realChart_positive hz.1))
      (fun z hz ↦ hJM _ (exp_lt_norm_realChart_positive hz.1))
      (fun z hz ↦ ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_positive hH hHs
        (ha.trans hz.1.le)
        (hud.differentiableAt ((isOpen_lt_norm _).mem_nhds (exp_lt_norm_realChart_positive hz.1)))
        (hfloer _ (exp_lt_norm_realChart_positive hz.1)))
      ((ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_le hH hHs ha hud).trans_lt
        hE.lt_top).ne
  simp only [comp_apply, ψ, realChart_positive_mk] at hux
  exact ⟨x, hxper, hx, φ, hφ, hux⟩

/-- **The asymptotic action at the end of the positive plane.** This is the case `p = positive` of
`exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation`, on the part
`‖w‖ > exp (2πa)` with `a ≥ 2` and for an arbitrary Hamiltonian; the negative plane is reduced to
it. -/
private theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {a : ℝ} (ha : 2 ≤ a)
    (hu : ContDiffOn ℝ 2 u {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    (hK : IsCompact K)
    (huK : ∀ z, Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖ →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖ →
      ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
  set ψ := realChart positive.cylindricalEndLift
  have hψ : ContDiff ℝ 2 ψ := contDiff_realChart positive.contDiff_cylindricalEndLift
  have hud := hu.differentiableOn two_ne_zero
  obtain ⟨x, hxper, hx, ⟨φ, -, hφ, hux⟩, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer (a := a) (J := J ∘ ψ) hHs hH
      (hu.comp hψ.contDiffOn fun z hz ↦ exp_lt_norm_realChart_positive hz.1)
      (fun s _ ↦ by
        simpa only [comp_apply, ψ, realChart_positive_mk] using
          periodic_comp_cylindricalEndLift_positive u s)
      hK (fun s hs t ↦ huK _ (exp_lt_norm_realChart_positive hs)) hc
      (fun z hz ↦ hJc _ (exp_lt_norm_realChart_positive hz.1))
      (fun z hz ↦ hJM _ (exp_lt_norm_realChart_positive hz.1))
      (fun z hz ↦ ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_positive hH hHs
        (ha.trans hz.1.le)
        (hud.differentiableAt ((isOpen_lt_norm _).mem_nhds (exp_lt_norm_realChart_positive hz.1)))
        (hfloer _ (exp_lt_norm_realChart_positive hz.1)))
      ((ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_le hH hHs ha hud).trans_lt
        hE.lt_top).ne
  simp only [comp_apply, ψ, realChart_positive_mk] at hux hA
  exact ⟨x, hxper, hx, ⟨φ, hφ, hux⟩, hA⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The reversed Hamiltonian `-H(-t)` of a period-one Hamiltonian has period one. -/
private theorem periodic_neg_comp_neg (hH : Periodic H 1) :
    Periodic (fun t y ↦ -H (-t) y) 1 := fun t ↦ by
  simp only [show -(t + 1) = -t - 1 by ring, hH.sub_eq]

omit [FiniteDimensional ℝ V] in
/-- The reversed Hamiltonian `-H(-t)` of a `C¹` Hamiltonian is `C¹`. -/
private theorem contDiff_uncurry_neg_comp_neg (hHs : ContDiff ℝ 1 (uncurry H)) :
    ContDiff ℝ 1 (uncurry fun t y ↦ -H (-t) y) :=
  (hHs.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg

/-- Reversing time turns a one-periodic orbit `y` of the reversed Hamiltonian `-H(-t)` into the
one-periodic orbit `t ↦ y(-t)` of `H`. -/
private theorem periodic_hasDerivAt_comp_neg {y : ℝ → V} (hyper : Periodic y 1)
    (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (fun x ↦ -H (-t) x) (y t)) t) :
    Periodic (fun t ↦ y (-t)) 1 ∧
      ∀ t, HasDerivAt (fun t ↦ y (-t)) (ω.hamiltonianVectorField (H t) (y (-t))) t := by
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · simp only [show -(t + 1) = -t - 1 by ring, hyper.sub_eq]
  · have h := (hy (-t)).scomp t (hasDerivAt_neg t)
    have hX : ω.hamiltonianVectorField (fun y ↦ -H (-(-t)) y) (y (-t)) =
        -ω.hamiltonianVectorField (H t) (y (-t)) := by
      rw [← hamiltonianVectorField_neg]
      simp only [neg_neg]
      rfl
    rw [hX, neg_one_smul, neg_neg] at h
    exact h

/-- The loops of the negative plane are those of the positive plane traversed backwards. -/
private theorem cylindricalEndLift_negative_endSign_mul (R t : ℝ) :
    negative.cylindricalEndLift (↑(negative.endSign * R) + ↑t * Complex.I) =
      positive.cylindricalEndLift (↑(positive.endSign * R) + ↑(-t) * Complex.I) := by
  rw [cylindricalEndLift_negative]
  congr 1
  simp only [endSign_negative, endSign_positive]
  push_cast
  ring

/-- **The asymptotic orbit at the end of a finite-energy PSS plane.** Let `𝔎` be the perturbation of
a PSS plane `p` given by a period-one `C¹` Hamiltonian `H`. Let `u` be `C¹` on a part `‖w‖ > r` of
the end, with image in a compact set `K`, solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there
for almost complex structures `J(z)` with `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖`, `c > 0`,
and with finite energy there. Then there is a one-periodic orbit `x` of the Hamiltonian vector
field such that the loops `ℓ_R(t) = u(φ(ε R + i t))`, where `φ` is the end lift
`p.cylindricalEndLift` and `ε = p.endSign`, converge uniformly to `x` along some `R_n → ∞`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop := by
  -- Shrink the end to a part `‖w‖ > exp (2πa)` with `a ≥ 2`, where the datum is cylindrical.
  obtain ⟨a, ha, hsub⟩ := exists_two_le_exp_lt_norm_subset r
  have hE' := ne_top_of_le_ne_top hE (lintegral_mono_set hsub)
  cases p
  · exact exists_periodic_hasDerivAt_tendstoUniformly_positive hH hHs ha (hu.mono hsub) hK
      (fun z hz ↦ huK z (hsub hz)) hc (fun z hz ↦ hJc z (hsub hz)) (fun z hz ↦ hJM z (hsub hz))
      (fun z hz ↦ hfloer z (hsub hz)) hE'
  -- The negative plane is the positive plane for the reversed Hamiltonian `-H(-t)`.
  rw [perturbation_negative] at hfloer hE'
  obtain ⟨y, hyper, hy, R, hR, huy⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_positive (periodic_neg_comp_neg hH)
      (contDiff_uncurry_neg_comp_neg hHs) ha (hu.mono hsub) hK (fun z hz ↦ huK z (hsub hz)) hc
      (fun z hz ↦ hJc z (hsub hz)) (fun z hz ↦ hJM z (hsub hz)) (fun z hz ↦ hfloer z (hsub hz))
      hE'
  obtain ⟨hxper, hx⟩ := periodic_hasDerivAt_comp_neg hyper hy
  refine ⟨fun t ↦ y (-t), hxper, hx, R, hR, ?_⟩
  simp only [cylindricalEndLift_negative_endSign_mul]
  exact huy.comp fun t ↦ -t

/-- **The asymptotic action at the end of a finite-energy PSS plane.** Let `𝔎` be the perturbation
of a PSS plane `p` given by a period-one `C¹` Hamiltonian `H`. Let `u` be `C²` on a part `‖w‖ > r`
of the end, with image in a compact set `K`, solving the Floer equation `(du - X_𝔎)^{0,1} = 0`
there for almost complex structures `J(z)` with `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖`,
`c > 0`, and with finite energy there. Then there is a one-periodic orbit `x` of the Hamiltonian
vector field such that the loops `ℓ_R(t) = u(φ(ε R + i t))`, where `φ` is the end lift
`p.cylindricalEndLift` and `ε = p.endSign`, converge uniformly to `x` along some `R_n → ∞`, and
their actions `A_H(ℓ_R)` tend to the action `A_H(x)` as `R → ∞`. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
  -- Shrink the end to a part `‖w‖ > exp (2πa)` with `a ≥ 2`, where the datum is cylindrical.
  obtain ⟨a, ha, hsub⟩ := exists_two_le_exp_lt_norm_subset r
  have hE' := ne_top_of_le_ne_top hE (lintegral_mono_set hsub)
  cases p
  · exact exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive hH hHs ha (hu.mono hsub)
      hK (fun z hz ↦ huK z (hsub hz)) hc (fun z hz ↦ hJc z (hsub hz))
      (fun z hz ↦ hJM z (hsub hz)) (fun z hz ↦ hfloer z (hsub hz)) hE'
  -- The negative plane is the positive plane for the reversed Hamiltonian `-H(-t)`.
  rw [perturbation_negative] at hfloer hE'
  have hH' := periodic_neg_comp_neg hH
  obtain ⟨y, hyper, hy, ⟨R, hR, huy⟩, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive hH'
      (contDiff_uncurry_neg_comp_neg hHs) ha (hu.mono hsub) hK (fun z hz ↦ huK z (hsub hz)) hc
      (fun z hz ↦ hJc z (hsub hz)) (fun z hz ↦ hJM z (hsub hz)) (fun z hz ↦ hfloer z (hsub hz))
      hE'
  obtain ⟨hxper, hx⟩ := periodic_hasDerivAt_comp_neg hyper hy
  refine ⟨fun t ↦ y (-t), hxper, hx, ⟨R, hR, ?_⟩, ?_⟩
  · simp only [cylindricalEndLift_negative_endSign_mul]
    exact huy.comp fun t ↦ -t
  -- Reversing a loop negates its action relative to the reversed Hamiltonian.
  have hrev {x : ℝ → V} (hx : Periodic x 1) : ω.hamiltonianAction H (fun t ↦ x (-t)) =
      -ω.hamiltonianAction (fun t y ↦ -H (-t) y) x := by
    simpa only [neg_neg] using ω.hamiltonianAction_comp_neg hH' hx
  rw [hrev hyper]
  refine hA.neg.congr fun R ↦ ?_
  simp only [cylindricalEndLift_negative_endSign_mul]
  exact (hrev (periodic_comp_cylindricalEndLift_positive u R)).symm

/-- **The energy of a finite-energy PSS plane.** Let `𝔎` be the perturbation of a PSS plane `p`
given by a period-one `C¹` Hamiltonian `H`, and let `u` be a `C²` solution of the Floer equation
`(du - X_𝔎)^{0,1} = 0` on the whole plane, for almost complex structures `J(z)` tamed by `ω`, with
finite energy. Suppose that on a part `‖w‖ > r` of the end the image of `u` lies in a compact set
`K` and `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖` with `c > 0`. Then there is a one-periodic
orbit `x` of the Hamiltonian vector field, the uniform limit of the loops `ℓ_R(t) = u(φ(ε R + i t))`
along some `R_n → ∞`, where `φ` is the end lift `p.cylindricalEndLift` and `ε = p.endSign`, such
that the actions `A_H(ℓ_R)` tend to `A_H(x)` as `R → ∞` and

`E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`. -/
theorem exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hK : IsCompact K) {r : ℝ}
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  obtain ⟨x, hxper, hx, hux, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation p hH hHs
      hu.contDiffOn hK huK hc hJc hJM (fun z _ ↦ hfloer z)
      ((setLIntegral_le_lintegral _ _).trans_lt hE.lt_top).ne
  exact ⟨x, hxper, hx, hux, hA, lintegral_floerEnergyDensity_pssPlanePerturbation_eq ω hH hHs hu hJ
    hfloer hA⟩

end TauCeti.SymplecticForm
