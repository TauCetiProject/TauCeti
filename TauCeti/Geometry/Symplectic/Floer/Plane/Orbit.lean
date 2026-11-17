/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic
public import TauCeti.Geometry.Symplectic.Floer.Plane.Action
import TauCeti.Algebra.Ring.Periodic

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
traversed backwards (`TauCeti.Floer.PSSPlane.cylindricalEndLift_negative_endSign_mul`). Reversing
time turns an orbit `y` of `-H(-t)` into the orbit `t ↦ y(-t)` of `H`, since both the time and the
derivative change sign
(`TauCeti.SymplecticForm.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_neg`). It also
negates the action of a loop
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

omit [FiniteDimensional ℝ V] in
/-- A map differentiable on the part `‖w‖ > exp (2πa)` of the plane is differentiable at the image
under the end lift of the positive plane of every point of the half-cylinder `s > a`. -/
private theorem differentiableAt_realChart_positive {a : ℝ}
    (hu : DifferentiableOn ℝ u {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    {z : ℝ × ℝ} (hz : a < z.1) :
    DifferentiableAt ℝ u (realChart positive.cylindricalEndLift z) :=
  hu.differentiableAt <| (isOpen_lt continuous_const (by fun_prop)).mem_nhds
    (exp_lt_norm_realChart_positive hz)

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
Floer equation for the datum of the positive plane and an almost complex structure `J` at the image
of `(s, t)` under the end lift `φ`, then `u ∘ φ` solves the Floer equation at `(s, t)` for the
cylindrical datum `H(t) dt` and the same structure `J`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_realChart_positive (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {J : AlmostComplexStructure V}
    {z : ℝ × ℝ} (hz : 2 ≤ z.1) (hu : DifferentiableAt ℝ u (realChart positive.cylindricalEndLift z))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (realChart positive.cylindricalEndLift z) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
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
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hS
    (injOn_realChart_positive a)
    (fun z _ ↦ (contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable
      one_ne_zero z) fun z hz ↦ by
      rw [floerEnergyDensity_comp_realChart_positive ω hH hHs (ha.trans hz.1.le)
        (differentiableAt_realChart_positive hu hz.1),
        abs_of_pos (positive.det_fderiv_realChart_cylindricalEndLift_pos z)]]
  refine lintegral_mono_set ?_
  rintro _ ⟨z, hz, rfl⟩
  exact exp_lt_norm_realChart_positive hz.1

/-- **The half-cylinder at the end of the positive plane.** If `u` is `Cⁿ`, `n ≠ 0`, on a part
`‖w‖ > r` of the positive plane, with image in `K`, solving the Floer equation there for structures
`J(z)` bounded by `c` and `M`, and with finite energy there, then on some half-cylinder `s > a` the
map `u ∘ φ` and the structures `J ∘ φ` satisfy the hypotheses of the finite-energy half-cylinder
theorems of `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` for the cylindrical datum
`H(t) dt`. -/
private theorem exists_halfCylinder_comp_realChart_positive (ω : SymplecticForm V)
    {n : WithTop ℕ∞} (hn : n ≠ 0) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ n u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ a : ℝ, ContDiffOn ℝ n (u ∘ realChart positive.cylindricalEndLift) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ (u ∘ realChart positive.cylindricalEndLift) (s, t)) 1) ∧
      (∀ s, a < s → ∀ t, (u ∘ realChart positive.cylindricalEndLift) (s, t) ∈ K) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
        c * ‖v‖ ^ 2 ≤ ω v ((J ∘ realChart positive.cylindricalEndLift) z v)) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
        ‖(J ∘ realChart positive.cylindricalEndLift) z v‖ ≤ M * ‖v‖) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((J ∘ realChart positive.cylindricalEndLift) z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (u ∘ realChart positive.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≠ ⊤ := by
  -- Shrink the end to a part `‖w‖ > exp (2πa)` with `a ≥ 2`, where the datum is cylindrical.
  obtain ⟨a, ha, hsub⟩ := exists_two_le_exp_lt_norm_subset r
  have hmem {z : ℝ × ℝ} (hz : a < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (realChart positive.cylindricalEndLift z)‖ :=
    hsub (exp_lt_norm_realChart_positive hz)
  have hud := (hu.mono hsub).differentiableOn hn
  refine ⟨a, (hu.mono hsub).comp
      (contDiff_realChart positive.contDiff_cylindricalEndLift).contDiffOn
      fun z hz ↦ exp_lt_norm_realChart_positive hz.1,
    fun s _ ↦ ?_, fun s hs t ↦ huK _ (hmem hs), fun z hz ↦ hJc _ (hmem hz.1),
    fun z hz ↦ hJM _ (hmem hz.1),
    fun z hz ↦ ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_positive hH hHs
      (ha.trans hz.1.le) (differentiableAt_realChart_positive hud hz.1) (hfloer _ (hmem hz.1)),
    ((ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_le hH hHs ha hud).trans_lt
      ((lintegral_mono_set hsub).trans_lt hE.lt_top)).ne⟩
  simpa only [comp_apply, realChart_positive_mk] using
    positive.periodic_comp_cylindricalEndLift u s

/-- **The asymptotic orbit at the end of the positive plane.** This is the case `p = positive` of
`exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation`, for an arbitrary Hamiltonian;
the negative plane is reduced to it. -/
private theorem exists_periodic_hasDerivAt_tendstoUniformly_positive
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I)))) x atTop := by
  obtain ⟨a, hu', hper, huK', hJc', hJM', hfloer', hE'⟩ :=
    ω.exists_halfCylinder_comp_realChart_positive one_ne_zero hH hHs hu huK hJc hJM hfloer hE
  obtain ⟨x, hxper, hx, φ, -, hφ, hux⟩ := exists_periodic_hasDerivAt_tendstoUniformly_of_floer
    hHs hH hu' hper hK huK' hc hJc' hJM' hfloer' hE'
  simp only [comp_apply, realChart_positive_mk] at hux
  exact ⟨x, hxper, hx, φ, hφ, hux⟩

/-- **The asymptotic action at the end of the positive plane.** This is the case `p = positive` of
`exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation`, for an arbitrary
Hamiltonian; the negative plane is reduced to it. -/
private theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
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
  obtain ⟨a, hu', hper, huK', hJc', hJM', hfloer', hE'⟩ :=
    ω.exists_halfCylinder_comp_realChart_positive two_ne_zero hH hHs hu huK hJc hJM hfloer hE
  obtain ⟨x, hxper, hx, ⟨φ, -, hφ, hux⟩, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer
      hHs hH hu' hper hK huK' hc hJc' hJM' hfloer' hE'
  simp only [comp_apply, realChart_positive_mk] at hux hA
  exact ⟨x, hxper, hx, ⟨φ, hφ, hux⟩, hA⟩

omit [FiniteDimensional ℝ V] in
/-- The negative plane given by `H` is the positive plane given by the reversed Hamiltonian
`-H(-t)` (`TauCeti.Floer.PSSPlane.perturbation_negative`), which is again period-one and `C¹`. -/
private theorem periodic_contDiff_reverse (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) :
    Periodic (fun t y ↦ -H (-t) y) 1 ∧ ContDiff ℝ 1 (uncurry fun t y ↦ -H (-t) y) :=
  ⟨hH.comp_neg.comp Neg.neg, (hHs.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg⟩

/-- **The orbit at the end of the negative plane.** Reversing time turns a one-periodic orbit `y` of
the reversed Hamiltonian `-H(-t)` into the one-periodic orbit `t ↦ y(-t)` of `H`; if the loops of
`u` along the end of the positive plane converge uniformly to `y` along `R_n`, then the loops of `u`
along the end of the negative plane converge uniformly to `t ↦ y(-t)` along `R_n`. -/
private theorem periodic_hasDerivAt_tendstoUniformly_negative (ω : SymplecticForm V)
    {y : ℝ → V} (hyper : Periodic y 1)
    (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (fun x ↦ -H (-t) x) (y t)) t)
    {R : ℕ → ℝ} (huy : TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
      (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I)))) y atTop) :
    Periodic (fun t ↦ y (-t)) 1 ∧
      (∀ t, HasDerivAt (fun t ↦ y (-t)) (ω.hamiltonianVectorField (H t) (y (-t))) t) ∧
      TendstoUniformly (fun n (t : ℝ) ↦ u (Complex.equivRealProdCLM
        (negative.cylindricalEndLift (↑(negative.endSign * R n) + ↑t * Complex.I))))
        (fun t ↦ y (-t)) atTop := by
  refine ⟨hyper.comp_neg, fun t ↦ ?_, ?_⟩
  · exact ω.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_neg
      (by simpa only [neg_neg, Pi.neg_def] using hy (-t))
  simp only [cylindricalEndLift_negative_endSign_mul]
  exact huy.comp fun t ↦ -t

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
  cases p
  · exact exists_periodic_hasDerivAt_tendstoUniformly_positive hH hHs hu hK huK hc hJc hJM hfloer hE
  -- The negative plane is the positive plane for the reversed Hamiltonian `-H(-t)`.
  rw [perturbation_negative] at hfloer hE
  obtain ⟨hH', hHs'⟩ := periodic_contDiff_reverse hH hHs
  obtain ⟨y, hyper, hy, R, hR, huy⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_positive hH' hHs' hu hK huK hc hJc hJM hfloer hE
  obtain ⟨hxper, hx, hux⟩ := ω.periodic_hasDerivAt_tendstoUniformly_negative hyper hy huy
  exact ⟨_, hxper, hx, R, hR, hux⟩

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
  cases p
  · exact exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive hH hHs hu hK huK hc hJc
      hJM hfloer hE
  -- The negative plane is the positive plane for the reversed Hamiltonian `-H(-t)`.
  rw [perturbation_negative] at hfloer hE
  obtain ⟨hH', hHs'⟩ := periodic_contDiff_reverse hH hHs
  obtain ⟨y, hyper, hy, ⟨R, hR, huy⟩, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive hH' hHs' hu hK huK hc hJc hJM
      hfloer hE
  obtain ⟨hxper, hx, hux⟩ := ω.periodic_hasDerivAt_tendstoUniformly_negative hyper hy huy
  refine ⟨_, hxper, hx, ⟨R, hR, hux⟩, ?_⟩
  -- Reversing a loop negates its action relative to the reversed Hamiltonian.
  have hrev {x : ℝ → V} (hx : Periodic x 1) : ω.hamiltonianAction H (fun t ↦ x (-t)) =
      -ω.hamiltonianAction (fun t y ↦ -H (-t) y) x := by
    simpa only [neg_neg] using ω.hamiltonianAction_comp_neg hH' hx
  rw [hrev hyper]
  refine hA.neg.congr fun R ↦ ?_
  simp only [cylindricalEndLift_negative_endSign_mul]
  exact (hrev (positive.periodic_comp_cylindricalEndLift u R)).symm

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
