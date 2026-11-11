/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder
public import TauCeti.Geometry.Symplectic.Floer.Plane.Action

/-!
# The asymptotic orbit at the end of a finite-energy PSS plane

Let `K` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from
a period-one `C¹` Hamiltonian `H` on a symplectic vector space `(V, ω)`, and let `ε = ±1` be the
sign of the end of `p` at `∞`. Let `u` be a solution of the Floer equation `(du - X_K)^{0,1} = 0`
on the part `‖w‖ > exp (4π)` of the end, where `K` is `H(t) dt` in end coordinates, for uniformly
tame almost complex structures `J(z)`, with image in a compact set and with finite energy there.
For `R ∈ ℝ` write `ℓ_R(t) = u(φ(ε R + i t))` for the loop of `u` along the circle
`‖w‖ = exp (2πR)`, where `φ(z) = exp (2π ε z)` is the end lift. This file shows that `u` breaks
off a one-periodic orbit at its end:

* there are a one-periodic orbit `x` of the Hamiltonian vector field, `x' = X_{H_t}(x)`, and
  radii `R_n → ∞` such that the loops `ℓ_{R_n}` converge uniformly to `x`, and if `u` is `C²`
  the actions `A_H(ℓ_R)` tend to `A_H(x)` as `R → ∞`
  (`SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation`);
* hence, for a `C²` solution on the whole plane with finite energy, the energy is
  `E(u) = ε A_H(x) - ∫_ℂ R_K(u)`
  (`exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq` in
  `TauCeti.SymplecticForm`).

So `x` is the generator at which a PSS plane meets the Floer complex: an input for the positive
plane, an output for the negative plane. The energy identity of
`TauCeti.Geometry.Symplectic.Floer.Plane.Action` assumed convergence of the end actions; here it
follows from finite energy and compactness.

On the positive plane `ε = 1`, the end in the coordinates `(s, t)` of the end lift is a Floer
half-cylinder `s > 2` for the cylindrical datum `H(t) dt`, with the structures `J ∘ φ`. Since `φ` is
holomorphic, the Floer equation and the energy pull back along it
(`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_perturbationPullback`,
`TauCeti.SymplecticForm.floerEnergyDensity_perturbationPullback`), and `φ` is injective on the
half-strip `s > 2`, `0 ≤ t < 1`, so the energy of the half-cylinder is at most that of `u`. The
results on finite-energy half-cylinders of `TauCeti.Geometry.Symplectic.Floer.HalfCylinder` then
apply. The negative plane is the positive plane for the reversed Hamiltonian `-H(-t)`
(`TauCeti.Floer.PSSPlane.perturbation_negative`), and its loops are the loops of the positive plane
traversed backwards. Reversal negates the action and the time of the Hamiltonian
(`TauCeti.SymplecticForm.hamiltonianAction_comp_neg`), which turns the orbit of the reversed
Hamiltonian into an orbit of `H`.

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

/-- The half-cylinder `s > 2` of the positive plane lies in the part `‖w‖ > exp (4π)` of the
plane. -/
private theorem exp_lt_norm_realChart_positive {z : ℝ × ℝ} (hz : 2 < z.1) :
    Real.exp (4 * π) <
      ‖Complex.equivRealProdCLM.symm (realChart positive.cylindricalEndLift z)‖ := by
  rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, norm_cylindricalEndLift,
    endSign_positive, one_mul, Complex.equivRealProdCLM_symm_apply_re, Real.exp_lt_exp]
  nlinarith [Real.pi_pos]

/-- The part `‖w‖ > exp (4π)` of the plane, in real coordinates, is open. -/
private theorem isOpen_exp_lt_norm :
    IsOpen {z : ℝ × ℝ | Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖} :=
  isOpen_lt continuous_const (continuous_norm.comp Complex.equivRealProdCLM.symm.continuous)

/-- The end lift of the positive plane is injective on the half-strip `s > 2`, `0 ≤ t < 1`. -/
private theorem injOn_realChart_positive :
    InjOn (realChart positive.cylindricalEndLift) (Ioi 2 ×ˢ Ico 0 1) := by
  intro a ha b hb hab
  rw [realChart_apply, realChart_apply] at hab
  have ha' : Complex.equivRealProdCLM.symm a ∈ {z : ℂ | z.im ∈ Ico 0 (0 + 1)} := by
    simpa using ha.2
  have hb' : Complex.equivRealProdCLM.symm b ∈ {z : ℂ | z.im ∈ Ico 0 (0 + 1)} := by
    simpa using hb.2
  have h := positive.injOn_cylindricalEndLift 0 ha' hb' (Complex.equivRealProdCLM.injective hab)
  exact Complex.equivRealProdCLM.symm.injective h

omit [FiniteDimensional ℝ V] in
/-- The datum of a PSS plane, on a fixed tangent vector `v`, is differentiable in the target point
for a period-one `C¹` Hamiltonian. -/
private theorem differentiableAt_perturbation (p : PSSPlane) (hH : Periodic H 1)
    (hHs : ContDiff ℝ 1 (uncurry H)) (v : ℂ) (z : ℝ × ℝ) (x : V) :
    DifferentiableAt ℝ (fun y ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) y v) x :=
  ((contDiff_uncurry_perturbation hH hHs v).comp
    (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero x

/-- Beyond `s = 2` the pullback of the datum of the positive plane along its end lift is the
cylindrical datum `H(t) dt`, so the Floer operators of the two data agree there. -/
private theorem perturbedFDeriv_comp_realChart_positive (ω : SymplecticForm V)
    (hH : Periodic H 1) (u : ℝ × ℝ → V) {z : ℝ × ℝ} (hz : 2 < z.1) :
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

/-- In the part `‖w‖ > exp (4π)` of the positive plane, where its datum is `C¹` and `u` is
differentiable, the energy density of `u` read on the half-cylinder `s > 2` of the end, for the
cylindrical datum `H(t) dt`, is the Jacobian of the end lift times the energy density of `u`. -/
private theorem floerEnergyDensity_comp_realChart_positive (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {z : ℝ × ℝ} (hz : 2 < z.1)
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
    (differentiableAt_perturbation positive hH hHs 1 _ _)
    (differentiableAt_perturbation positive hH hHs Complex.I _ _)

/-- If `u` has finite energy on the part `‖w‖ > exp (4π)` of the positive plane, then `u` read on
the half-cylinder `s > 2` of the end has finite energy for the cylindrical datum `H(t) dt`: the end
lift is injective on the half-strip `0 ≤ t < 1` and preserves orientation. -/
private theorem lintegral_floerEnergyDensity_comp_realChart_positive_ne_top
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H))
    (hu : ∀ z : ℝ × ℝ, 2 < z.1 → DifferentiableAt ℝ u (realChart positive.cylindricalEndLift z))
    (hE : ∫⁻ z in {z | Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∫⁻ z in Ioi 2 ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≠ ⊤ := by
  have hS : MeasurableSet (Ioi (2 : ℝ) ×ˢ Ico (0 : ℝ) 1) :=
    measurableSet_Ioi.prod measurableSet_Ico
  have hae : (Ioi (2 : ℝ) ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] Ioi 2 ×ˢ Ico 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq EventuallyEq.rfl Ico_ae_eq_Icc.symm
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hS
    injOn_realChart_positive
    (fun z _ ↦ (contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable
      one_ne_zero z) fun z hz ↦ by
      rw [floerEnergyDensity_comp_realChart_positive ω hH hHs hz.1 (hu z hz.1),
        abs_of_pos (positive.det_fderiv_realChart_pos z)]]
  refine ((lintegral_mono_set ?_).trans_lt hE.lt_top).ne
  rintro _ ⟨z, hz, rfl⟩
  exact exp_lt_norm_realChart_positive hz.1

/-- **The asymptotic orbit at the end of the positive plane.** This is the case `p = positive` of
`exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation`, for an arbitrary
Hamiltonian; the negative plane is reduced to it. -/
private theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H))
    (hu : ContDiffOn ℝ 2 u {z | Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖})
    (hK : IsCompact K)
    (huK : ∀ z, Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖ →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖ →
      ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ φ : ℕ → ℝ, Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * φ n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
  set ψ := realChart positive.cylindricalEndLift
  have hψ : ContDiff ℝ 2 ψ := contDiff_realChart positive.contDiff_cylindricalEndLift
  have hud {z : ℝ × ℝ} (hz : 2 < z.1) : DifferentiableAt ℝ u (ψ z) :=
    (hu.contDiffAt (isOpen_exp_lt_norm.mem_nhds (exp_lt_norm_realChart_positive hz))
      ).differentiableAt two_ne_zero
  -- On the half-cylinder `s > 2`, `u ∘ ψ` solves the Floer equation for `H(t) dt` and `J ∘ ψ`.
  have hfloer' : ∀ z ∈ Ioi 2 ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) ((J ∘ ψ) z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u ∘ ψ) z : ℝ × ℝ →ₗ[ℝ] V) := by
    intro z hz
    rw [perturbedFDeriv_comp_realChart_positive ω hH _ hz.1]
    exact ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback
      (hψ.differentiable two_ne_zero z) (hud hz.1)
      (differentiableAt_perturbation positive hH hHs 1 _ _)
      (differentiableAt_perturbation positive hH hHs Complex.I _ _)
      (Floer.isComplexLinearMap_fderiv_realChart (positive.hasDerivAt_cylindricalEndLift _))
      (hfloer _ (exp_lt_norm_realChart_positive hz.1))
  -- The finite-energy half-cylinder breaks off an orbit.
  obtain ⟨x, hxper, hx, ⟨φ, -, hφ, hux⟩, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer (a := 2) (J := J ∘ ψ) hHs hH
      (hu.comp hψ.contDiffOn fun z hz ↦ exp_lt_norm_realChart_positive hz.1)
      (fun s _ t ↦ by
        simp only [comp_apply, ψ, realChart_positive_mk]
        exact congrArg (fun w ↦ u (Complex.equivRealProdCLM w))
          (positive.periodic_cylindricalEndLift (positive.endSign * s) t))
      hK (fun s hs t ↦ huK _ (exp_lt_norm_realChart_positive hs)) hc
      (fun z hz ↦ hJc _ (exp_lt_norm_realChart_positive hz.1))
      (fun z hz ↦ hJM _ (exp_lt_norm_realChart_positive hz.1)) hfloer'
      (lintegral_floerEnergyDensity_comp_realChart_positive_ne_top ω hH hHs (fun _ hz ↦ hud hz) hE)
  simp only [comp_apply, ψ, realChart_positive_mk] at hux hA
  exact ⟨x, hxper, hx, ⟨φ, hφ, hux⟩, hA⟩

/-- **The asymptotic orbit at the end of a finite-energy PSS plane.** Let `K` be the perturbation of
a PSS plane `p` given by a period-one `C¹` Hamiltonian `H`, equal to `H(t) dt` in end coordinates
on the part `‖w‖ > exp (4π)` of the end. Let `u` be `C²` there, with image in a compact set `K`,
solving the Floer equation `(du - X_K)^{0,1} = 0` for almost complex structures `J(z)` with
`c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖`, `c > 0`, and with finite energy there. Then there
is a one-periodic orbit `x` of the Hamiltonian vector field such that the loops
`ℓ_R(t) = u(φ(ε R + i t))` converge uniformly to `x` along some `R_n → ∞`, and their actions
`A_H(ℓ_R)` tend to the action `A_H(x)` as `R → ∞`. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H))
    (hu : ContDiffOn ℝ 2 u {z | Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖})
    (hK : IsCompact K)
    (huK : ∀ z, Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖ →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖ →
      ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ φ : ℕ → ℝ, Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * φ n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
  cases p
  · exact exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive hH hHs hu hK huK hc hJc
      hJM hfloer hE
  -- The negative plane is the positive plane for the reversed Hamiltonian `-H(-t)`.
  rw [perturbation_negative] at hfloer hE
  have hH' : Periodic (fun t y ↦ -H (-t) y) 1 := fun t ↦ by
    simp only [show -(t + 1) = -t - 1 by ring, hH.sub_eq]
  have hHs' : ContDiff ℝ 1 (uncurry fun t y ↦ -H (-t) y) :=
    (hHs.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg
  obtain ⟨y, hyper, hy, ⟨φ, hφ, huy⟩, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive hH' hHs' hu hK huK hc hJc hJM
      hfloer hE
  -- The loops of the negative plane are those of the positive plane traversed backwards.
  have hloop (R t : ℝ) :
      negative.cylindricalEndLift (↑(negative.endSign * R) + ↑t * Complex.I) =
        positive.cylindricalEndLift (↑(positive.endSign * R) + ↑(-t) * Complex.I) := by
    rw [cylindricalEndLift_negative]
    congr 1
    simp only [endSign_negative, endSign_positive]
    push_cast
    ring
  have hper (R : ℝ) : Periodic (fun t : ℝ ↦ u (Complex.equivRealProdCLM
      (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I)))) 1 := fun t ↦
    congrArg (fun w ↦ u (Complex.equivRealProdCLM w))
      (positive.periodic_cylindricalEndLift (positive.endSign * R) t)
  refine ⟨fun t ↦ y (-t), fun t ↦ ?_, fun t ↦ ?_, ⟨φ, hφ, ?_⟩, ?_⟩
  · simp only [show -(t + 1) = -t - 1 by ring, hyper.sub_eq]
  · have h := (hy (-t)).scomp t (hasDerivAt_neg t)
    have hX : ω.hamiltonianVectorField (fun y ↦ -H (-(-t)) y) (y (-t)) =
        -ω.hamiltonianVectorField (H t) (y (-t)) := by
      rw [← hamiltonianVectorField_neg]
      simp only [neg_neg]
      rfl
    rw [hX, neg_one_smul, neg_neg] at h
    exact h
  · simp only [hloop]
    exact huy.comp fun t ↦ -t
  · have hrev {x : ℝ → V} (hx : Periodic x 1) : ω.hamiltonianAction H (fun t ↦ x (-t)) =
        -ω.hamiltonianAction (fun t y ↦ -H (-t) y) x := by
      simpa only [neg_neg] using ω.hamiltonianAction_comp_neg hH' hx
    rw [hrev hyper]
    refine hA.neg.congr fun R ↦ ?_
    simp only [hloop]
    exact (hrev (hper R)).symm

/-- **The energy of a finite-energy PSS plane.** Let `K` be the perturbation of a PSS plane `p`
given by a period-one `C¹` Hamiltonian `H`, and let `u` be a `C²` solution of the Floer equation
`(du - X_K)^{0,1} = 0` on the whole plane, for almost complex structures `J(z)` tamed by `ω`, with
finite energy. Suppose that on the part `‖w‖ > exp (4π)` of the end the image of `u` lies in a
compact set `K` and `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖` with `c > 0`. Then there is a
one-periodic orbit `x` of the Hamiltonian vector field, the uniform limit of the loops
`ℓ_R(t) = u(φ(ε R + i t))` along some `R_n → ∞`, such that

`E(u) = ε A_H(x) - ∫_ℂ R_K(u)`. -/
theorem exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hK : IsCompact K)
    (huK : ∀ z, Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖ →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, Real.exp (4 * π) < ‖Complex.equivRealProdCLM.symm z‖ →
      ∀ v, ‖J z v‖ ≤ M * ‖v‖)
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
      (∃ φ : ℕ → ℝ, Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * φ n) + ↑t * Complex.I)))) x atTop) ∧
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
  exact ⟨x, hxper, hx, hux, lintegral_floerEnergyDensity_pssPlanePerturbation_eq ω hH hHs hu hJ
    hfloer hA⟩

end TauCeti.SymplecticForm
