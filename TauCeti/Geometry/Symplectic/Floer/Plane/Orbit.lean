/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic
public import TauCeti.Geometry.Symplectic.Floer.Plane.Action
public import TauCeti.Geometry.Symplectic.Floer.SignedEnd.Orbit

/-!
# Exterior Floer pullback, energy, and asymptotic orbits on a PSS plane

Let `p` be a PSS plane (`TauCeti.Floer.PSSPlane`) with end sign `ε = p.endSign = ±1` at `∞`, and
let `K : ℂ → V → ℂ →L[ℝ] ℝ` be a Hamiltonian perturbation on `ℂ` with values in a symplectic
vector space `(V, ω)` that equals `H(t) dt` beyond some longitudinal height `T₀` on the end of `p`,
for a period-one Hamiltonian `H : ℝ → V → ℝ` (for instance `K = p.perturbation H` with `T₀ = 2`).
Adapting `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` to the PSS planes, this file
develops the positive-end-chart pullback, exact exterior energy change of variables, half-cylinder
reduction, and subsequential asymptotic orbit and action convergence at `∞`.

**Positive end chart and exterior energy.** In the positive end chart `φ_+ = positive.endChart`
(`TauCeti.Floer.PSSPlane.endChart`), `K` pulls back on `{s ≥ T₀}` to `H'_p(t) dt` for the
positive-end Hamiltonian `H'_p(t, x) = ε H(ε t, x)`
(`TauCeti.Floer.PSSPlane.positiveEndHamiltonian`). Since `φ_+` is holomorphic,
orientation-preserving, and maps `(a, ∞) × [0, 1)` and `[a, ∞) × [0, 1)` bijectively onto
`{‖w‖ > exp (2πa)}` and `{‖w‖ ≥ exp (2πa)}`:

* `u ∘ φ_+` solves the half-cylinder Floer equation for `H'_p` at every point with `s ≥ T₀`
  (`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_pssPlane_endChart_positive`);
* for `a ≥ T₀`, the half-cylinder energy of `u ∘ φ_+` over `(a, ∞) × [0, 1]` (resp.
  `[a, ∞) × [0, 1]`) equals the Floer energy of `u` over `{‖w‖ > exp (2πa)}` (resp.
  `{‖w‖ ≥ exp (2πa)}`)
  (`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_Ioi_eq`,
  `TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_Ici_eq`);
* `TauCeti.SymplecticForm.floer_comp_pssPlane_endChart_positive` and
  `TauCeti.SymplecticForm.floer_comp_pssPlane_endChart_positive_of_cylindrical` package the
  resulting finite-energy Floer half-cylinder hypotheses (including cylindrical almost complex
  structures `J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`) for downstream convergence and decay
  arguments.

**Asymptotic orbits and whole-plane energy.** Applying
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` to `u ∘ φ_+` and transferring orbits and
actions from `H'_p` back to `H` via `TauCeti.Geometry.Symplectic.Floer.SignedEnd.Orbit` shows that
any finite-energy solution on an exterior `{‖w‖ > r}` with precompact image and uniformly tame
almost complex structures breaks off a `1`-periodic orbit `x` of `H` along some `R_n → ∞`
(`exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_of_floer`, and
`exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation` for `p.perturbation H`), with
`A_H(ℓ_R) → A_H(x)` as `R → ∞` when `u` is `C²`
(`exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlane_endChart_of_floer`,
`exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation`), yielding the
whole-plane energy identity `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`
(`exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq`).

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  asymptotics of the perturbed planes of the PSS maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
-/

public section

open Set Real Function MeasureTheory Filter
open scoped ENNReal Topology

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

section OrbitsAndPullback

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ω : SymplecticForm V}
  {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : ℝ → V → ℝ} {T₀ : ℝ} {p : PSSPlane}

/-- Beyond `T₀` in `positive.endChart`, the components of `K` are differentiable in the target
point whenever each `H t` is differentiable. -/
private theorem differentiableAt_perturbation_endChart_positive
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hHd : ∀ t, Differentiable ℝ (H t)) {z : ℝ × ℝ} (hz : T₀ ≤ z.1) (v : ℂ) (y : V) :
    DifferentiableAt ℝ (fun x ↦ K (Complex.equivRealProdCLM.symm (positive.endChart z)) x v) y := by
  set w := Complex.equivRealProdCLM.symm (positive.endChart z)
  have hw : w ≠ 0 := positive.equivRealProdCLM_symm_endChart_ne_zero z
  have hre : T₀ ≤ p.endSign * (p.endCoord w).re := by
    rw [endSign_mul_re_endCoord, ← positive.endSign_mul_re_endCoord, endSign_positive, one_mul,
      re_endCoord_endChart]
    exact hz
  have h : (fun x ↦ K w x v) = fun x ↦ H (p.endCoord w).im x * p.endAngularForm w v := by
    funext x
    rw [hKH w x hw hre, smul_apply, smul_eq_mul]
  rw [h]
  exact ((hHd _) y).mul_const _

/-- The action of a `1`-periodic loop for `p.positiveEndHamiltonian H` is `ε` times the action for
`H` of the loop read at `t ↦ ε t`. -/
theorem hamiltonianAction_pssPlane_positiveEndHamiltonian (p : PSSPlane) (hH : Periodic H 1)
    {x : ℝ → V} (hx : Periodic x 1) :
    ω.hamiltonianAction (p.positiveEndHamiltonian H) x =
      p.endSign * ω.hamiltonianAction H (fun t ↦ x (p.endSign * t)) := by
  rw [p.positiveEndHamiltonian_eq_signedHamiltonian]
  exact ω.hamiltonianAction_signedHamiltonian p.endSign_mul_endSign hH hx

variable [FiniteDimensional ℝ V]

/-! ### Orbits in the positive end chart -/

/-- At the signed time `ε t`, the Hamiltonian vector field of `p.positiveEndHamiltonian H` is `ε`
times that of `H` at `t`. -/
theorem hamiltonianVectorField_pssPlane_positiveEndHamiltonian_endSign_mul (p : PSSPlane)
    (t : ℝ) :
    ω.hamiltonianVectorField (p.positiveEndHamiltonian H (p.endSign * t)) =
      p.endSign • ω.hamiltonianVectorField (H t) := by
  rw [p.positiveEndHamiltonian_eq_signedHamiltonian]
  exact ω.hamiltonianVectorField_signedHamiltonian_mul p.endSign_mul_endSign H t

/-- Reading an orbit of `p.positiveEndHamiltonian H` with the signed time `t ↦ ε t` gives an orbit
of `H`. -/
theorem hasDerivAt_comp_pssPlane_endSign_mul (p : PSSPlane) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (p.positiveEndHamiltonian H t) (x t)) t)
    (t : ℝ) :
    HasDerivAt (fun t ↦ x (p.endSign * t)) (ω.hamiltonianVectorField (H t) (x (p.endSign * t))) t :=
  by
  rw [p.positiveEndHamiltonian_eq_signedHamiltonian] at hx
  exact ω.hasDerivAt_comp_mul_of_signedHamiltonian p.endSign_mul_endSign hx t

/-- Reading an orbit of `H` with the signed time `t ↦ ε t` gives an orbit of
`p.positiveEndHamiltonian H`. -/
theorem hasDerivAt_comp_pssPlane_endSign_mul_positiveEndHamiltonian (p : PSSPlane) {y : ℝ → V}
    (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) (t : ℝ) :
    HasDerivAt (fun t ↦ y (p.endSign * t))
      (ω.hamiltonianVectorField (p.positiveEndHamiltonian H t) (y (p.endSign * t))) t := by
  rw [p.positiveEndHamiltonian_eq_signedHamiltonian]
  exact ω.hasDerivAt_comp_mul_signedHamiltonian p.endSign_mul_endSign hy t

/-! ### Floer pullback and exterior energy in `positive.endChart` -/

/-- On `{s ≥ T₀}`, the perturbed derivative of `u ∘ positive.endChart` for
`p.positiveEndHamiltonian H` agrees with the perturbed derivative for the pulled-back perturbation
`K`. -/
private theorem perturbedFDeriv_comp_pssPlane_endChart_positive_eq
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) {u : ℝ × ℝ → V} {z : ℝ × ℝ} (hz : T₀ ≤ z.1) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ p.positiveEndHamiltonian H w.2)
        (u ∘ positive.endChart) z =
      ω.perturbedFDeriv
        (perturbationPullback positive.endChart
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal)
        (perturbationPullback positive.endChart
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag)
        (u ∘ positive.endChart) z :=
  ω.perturbedFDeriv_congr _
    (funext fun x ↦
      (perturbationPullback_endChart_positive_stdComplexLineReal_of_le hKH hz x).symm)
    (funext fun x ↦
      (perturbationPullback_endChart_positive_stdComplexLineImag_of_le hKH hH hz x).symm)

/-- **The Floer equation on the end of a PSS plane in `positive.endChart`.** Where `K = H(t) dt`
beyond `T₀` on the end of `p`, if `u` solves `(du - X_K)^{0,1} = 0` at `positive.endChart z` for
`z.1 ≥ T₀`, then `u ∘ positive.endChart` solves the half-cylinder Floer equation at `z` for
`p.positiveEndHamiltonian H`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_pssPlane_endChart_positive
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {u : ℝ × ℝ → V}
    {J : AlmostComplexStructure V} {z : ℝ × ℝ} (hz : T₀ ≤ z.1)
    (hu : DifferentiableAt ℝ u (positive.endChart z))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (positive.endChart z) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ p.positiveEndHamiltonian H w.2)
        (u ∘ positive.endChart) z : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [perturbedFDeriv_comp_pssPlane_endChart_positive_eq hKH hH hz]
  exact ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    (positive.contDiff_endChart.differentiable one_ne_zero z) hu
    (differentiableAt_perturbation_endChart_positive hKH hHd hz 1 _)
    (differentiableAt_perturbation_endChart_positive hKH hHd hz Complex.I _)
    (positive.isComplexLinearMap_fderiv_endChart z) hfloer

/-- Where `K = H(t) dt` beyond `T₀` on the end of `p`, for `z.1 ≥ T₀` the half-cylinder energy
density of `u ∘ positive.endChart` for `p.positiveEndHamiltonian H` is the Jacobian determinant of
`positive.endChart` times the Floer energy density of `u` for `K` at `positive.endChart z`. -/
theorem floerEnergyDensity_comp_pssPlane_endChart_positive
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {u : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hz : T₀ ≤ z.1) (hu : DifferentiableAt ℝ u (positive.endChart z)) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ p.positiveEndHamiltonian H w.2)
        (u ∘ positive.endChart) z =
      (fderiv ℝ positive.endChart z).det *
        ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u (positive.endChart z) := by
  rw [floerEnergyDensity_def, perturbedFDeriv_comp_pssPlane_endChart_positive_eq hKH hH hz,
    ← floerEnergyDensity_def]
  exact ω.floerEnergyDensity_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    (positive.contDiff_endChart.differentiable one_ne_zero z) hu
    (differentiableAt_perturbation_endChart_positive hKH hHd hz 1 _)
    (differentiableAt_perturbation_endChart_positive hKH hHd hz Complex.I _)

/-- For any measurable set `P ⊆ [T₀, ∞)` of longitudinal coordinates, the half-cylinder energy of
`u ∘ positive.endChart` over `P × [0, 1]` equals the Floer energy of `u` over
`positive.endChart '' (P × [0, 1))`. -/
theorem setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_prod_Icc_eq
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {P : Set ℝ} (hP : MeasurableSet P)
    (hPT : ∀ s ∈ P, T₀ ≤ s) {u : ℝ × ℝ → V}
    (hu : ∀ z ∈ P ×ˢ Ico (0 : ℝ) 1, DifferentiableAt ℝ u (positive.endChart z)) :
    ∫⁻ z in P ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ p.positiveEndHamiltonian H w.2) (u ∘ positive.endChart) z) =
      ∫⁻ z in positive.endChart '' (P ×ˢ Ico 0 1),
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  have hae : (P ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] P ×ˢ Ico 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ico_ae_eq_Icc.symm
  rw [setLIntegral_congr hae]
  refine (lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul
    (hP.prod measurableSet_Ico)
    ((positive.injOn_endChart_univ_prod_Ico 0).mono
      (prod_mono (subset_univ _) (by simp only [zero_add, subset_rfl])))
    (fun z _ ↦ positive.contDiff_endChart.differentiable one_ne_zero z) fun z hz ↦ ?_).symm
  rw [floerEnergyDensity_comp_pssPlane_endChart_positive hKH hH hHd (hPT z.1 hz.1) (hu z hz),
    abs_of_pos (positive.det_fderiv_endChart_pos z)]

/-- **Exact exterior energy on `(a, ∞)`.** Where `K = H(t) dt` beyond `T₀` on the end of `p`, for
`a ≥ T₀` the half-cylinder energy of `u ∘ positive.endChart` over `(a, ∞) × [0, 1]` equals the
Floer energy of `u` over `{‖w‖ > exp (2πa)}`. -/
theorem setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_Ioi_eq
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {a : ℝ} (ha : T₀ ≤ a) {u : ℝ × ℝ → V}
    (hu : DifferentiableOn ℝ u {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖}) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ p.positiveEndHamiltonian H w.2) (u ∘ positive.endChart) z) =
      ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  rw [← image_endChart_positive_Ioi_prod_Ico]
  exact setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_prod_Icc_eq hKH hH hHd
    measurableSet_Ioi (fun _ hs ↦ ha.trans hs.le) fun z hz ↦
    differentiableAt_endChart_positive hu le_rfl hz.1

/-- **Exact exterior energy on `[a, ∞)`.** Where `K = H(t) dt` beyond `T₀` on the end of `p`, for
`a ≥ T₀` the half-cylinder energy of `u ∘ positive.endChart` over `[a, ∞) × [0, 1]` equals the
Floer energy of `u` over `{‖w‖ ≥ exp (2πa)}`. -/
theorem setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_Ici_eq
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {a : ℝ} (ha : T₀ ≤ a) {u : ℝ × ℝ → V}
    (hu : ∀ z, Real.exp (2 * π * a) ≤ ‖Complex.equivRealProdCLM.symm z‖ →
      DifferentiableAt ℝ u z) :
    ∫⁻ z in Ici a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ p.positiveEndHamiltonian H w.2) (u ∘ positive.endChart) z) =
      ∫⁻ z in {z | Real.exp (2 * π * a) ≤ ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  rw [← image_endChart_positive_Ici_prod_Ico]
  refine setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_prod_Icc_eq hKH hH hHd
    measurableSet_Ici (fun _ hs ↦ ha.trans hs) fun z hz ↦ hu _ ?_
  rw [norm_equivRealProdCLM_symm_endChart, endSign_positive, one_mul]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz.1 Real.two_pi_pos.le)

/-- When `u` has finite Floer energy on `{‖w‖ > r}` and `a ≥ T₀` satisfies `r ≤ exp (2π a)`,
`u ∘ positive.endChart` has finite half-cylinder energy on `(a, ∞) × [0, 1]`. -/
theorem setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_Ioi_ne_top
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {r a : ℝ} (ha : T₀ ≤ a)
    (hr : r ≤ Real.exp (2 * π * a)) {u : ℝ × ℝ → V}
    (hu : DifferentiableOn ℝ u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ p.positiveEndHamiltonian H w.2) (u ∘ positive.endChart) z) ≠ ⊤ := by
  have hsub : {z : ℝ × ℝ | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖} ⊆
      {z | r < ‖Complex.equivRealProdCLM.symm z‖} := fun _ hz ↦ hr.trans_lt hz
  rw [setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_Ioi_eq hKH hH hHd ha
    (hu.mono hsub)]
  exact ne_top_of_le_ne_top hE (lintegral_mono_set hsub)

/-! ### Half-cylinder reduction on the exterior of a PSS plane -/

/-- **Half-cylinder reduction on the end of a PSS plane.** If `K = H(t) dt` beyond `T₀` on the end
of `p` and `u` is `C^n` (`n ≠ 0`) with image in `B` and finite Floer energy on `{‖w‖ > r}`, solving
`(du - X_K)^{0,1} = 0` there, then for any `a ≥ T₀` with `r ≤ exp (2π a)` the map
`u ∘ positive.endChart` is `C^n` on `(a, ∞) × ℝ`, `1`-periodic in `t`, takes values in `B`, solves
the half-cylinder Floer equation for `p.positiveEndHamiltonian H` and `J ∘ positive.endChart`, and
has finite half-cylinder energy over `(a, ∞) × [0, 1]`. -/
theorem floer_comp_pssPlane_endChart_positive
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    {r a : ℝ} (ha : T₀ ≤ a) (hr : r ≤ Real.exp (2 * π * a)) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ n u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) {B : Set V}
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ContDiffOn ℝ n (u ∘ positive.endChart) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ (u ∘ positive.endChart) (s, t)) 1) ∧
      (∀ s, a < s → ∀ t, (u ∘ positive.endChart) (s, t) ∈ B) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((J ∘ positive.endChart) z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ p.positiveEndHamiltonian H w.2)
          (u ∘ positive.endChart) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ p.positiveEndHamiltonian H w.2) (u ∘ positive.endChart) z) ≠ ⊤ := by
  have hmem {z : ℝ × ℝ} (hz : a < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (positive.endChart z)‖ :=
    lt_norm_equivRealProdCLM_symm_endChart_positive hr hz
  have hud := hu.differentiableOn hn
  exact ⟨hu.comp positive.contDiff_endChart.contDiffOn fun _ hz ↦ hmem hz.1,
    fun s _ t ↦ by simp only [comp_apply, positive.endChart_add_one],
    fun s hs t ↦ huB _ (hmem hs),
    fun z hz ↦ isComplexLinearMap_perturbedFDeriv_comp_pssPlane_endChart_positive hKH hH hHd
      (ha.trans hz.1.le) (differentiableAt_endChart_positive hud hr hz.1) (hfloer _ (hmem hz.1)),
    setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_Ioi_ne_top hKH hH hHd ha hr
      hud hE⟩

/-- **Cylindrical-end half-cylinder reduction on a PSS plane.** Under the hypotheses of
`floer_comp_pssPlane_endChart_positive`, if moreover `J` is cylindrical beyond `T₀` on the end of
`p`, `J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a `1`-periodic `C^m` family `J₀` tamed by `ω`
on `ℝ × B`, then `u ∘ positive.endChart` and the time-reflected family `(t, x) ↦ J₀(ε t, x)`
satisfy all hypotheses of a finite-energy cylindrical Floer half-cylinder on `(a, ∞)`. -/
theorem floer_comp_pssPlane_endChart_positive_of_cylindrical
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    {r a : ℝ} (ha : T₀ ≤ a) (hr : r ≤ Real.exp (2 * π * a)) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ n u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) {B : Set V}
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {W : Set (ℝ × V)} (hW : IsOpen W) {J₀ : ℝ → V → AlmostComplexStructure V} {m : WithTop ℕ∞}
    (hJ₀ : ContDiffOn ℝ m (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hBW : univ ×ˢ B ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ B, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t)))) :
    IsOpen ((fun q : ℝ × V ↦ (p.endSign * q.1, q.2)) ⁻¹' W) ∧
      ContDiffOn ℝ m
        (fun q : ℝ × V ↦ (J₀ (p.endSign * q.1) q.2).toLinearMap.toContinuousLinearMap)
        ((fun q : ℝ × V ↦ (p.endSign * q.1, q.2)) ⁻¹' W) ∧
      Periodic (fun t ↦ J₀ (p.endSign * t)) 1 ∧
      univ ×ˢ B ⊆ (fun q : ℝ × V ↦ (p.endSign * q.1, q.2)) ⁻¹' W ∧
      (∀ t, ∀ x ∈ B, ω.Tames (J₀ (p.endSign * t) x)) ∧
      ContDiffOn ℝ n (u ∘ positive.endChart) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ (u ∘ positive.endChart) (s, t)) 1) ∧
      (∀ s, a < s → ∀ t, (u ∘ positive.endChart) (s, t) ∈ B) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J₀ (p.endSign * z.2) ((u ∘ positive.endChart) z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ p.positiveEndHamiltonian H w.2)
          (u ∘ positive.endChart) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ p.positiveEndHamiltonian H w.2) (u ∘ positive.endChart) z) ≠ ⊤ := by
  obtain ⟨hu', hper', huB', hfloer', hE'⟩ :=
    floer_comp_pssPlane_endChart_positive hKH hH hHd hn ha hr hu huB hfloer hE
  set g : ℝ × V → ℝ × V := fun q ↦ (p.endSign * q.1, q.2)
  have hg : ContDiff ℝ m g := (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
  exact ⟨hW.preimage hg.continuous, hJ₀.comp hg.contDiffOn (mapsTo_preimage g W),
    p.periodic_comp_endSign_mul hJ₀per, fun q hq ↦ hBW ⟨mem_univ _, hq.2⟩, fun t ↦ hJ₀t _,
    hu', hper', huB', fun z hz ↦ eq_comp_endChart_positive hJ (ha.trans hz.1.le) ▸ hfloer' z hz,
    hE'⟩

end OrbitsAndPullback

/-! ### Asymptotic orbits, actions, and whole-plane energy -/

section AsymptoticOrbits

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ} {B : Set V}

/-- **Subsequential orbit convergence at the end of a finite-energy PSS plane (general tail).**
Let `K = H(t) dt` beyond `T₀` on the end of `p` for a `1`-periodic `C¹` Hamiltonian `H`, and let
`u` be a `C¹` finite-energy solution of `(du - X_K)^{0,1} = 0` on `{‖w‖ > r}` with image in a
compact set `B` and uniformly tame structures `J(z)`. Then there exist a `1`-periodic orbit `x` of
`H` and `R_n → ∞` along which `t ↦ u(p.endChart (ε R_n, t))` converges uniformly to `x`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_of_floer (p : PSSPlane)
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hB : IsCompact B)
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (p.endChart (p.endSign * R n, t))) x atTop := by
  obtain ⟨a, ha, hr⟩ := exists_le_and_le_exp r T₀
  have hHd : ∀ t, Differentiable ℝ (H t) := fun t ↦
    (hHs.differentiable one_ne_zero).comp ((differentiable_const t).prodMk differentiable_id)
  obtain ⟨hu', hper', huB', hfloer', hE'⟩ :=
    floer_comp_pssPlane_endChart_positive hKH hH hHd one_ne_zero ha hr hu huB hfloer hE
  obtain ⟨y, hyper, hy, R, -, hR, huy⟩ := exists_periodic_hasDerivAt_tendstoUniformly_of_floer
    (p.contDiff_uncurry_positiveEndHamiltonian hHs) (p.periodic_positiveEndHamiltonian hH)
    hu' hper' hB huB' hc
    (fun z hz ↦ hJc _ (lt_norm_equivRealProdCLM_symm_endChart_positive hr hz.1))
    (fun z hz ↦ hJM _ (lt_norm_equivRealProdCLM_symm_endChart_positive hr hz.1))
    hfloer' hE'
  refine ⟨fun t ↦ y (p.endSign * t), p.periodic_comp_endSign_mul hyper,
    hasDerivAt_comp_pssPlane_endSign_mul p hy, R, hR, ?_⟩
  rw [funext fun n ↦ p.comp_endChart_eq_comp_endChart_positive u (R n)]
  exact huy.comp _

/-- **Asymptotic action convergence at the end of a finite-energy PSS plane (general tail).**
Under the hypotheses of `exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_of_floer`,
if moreover `u` is `C²` on `{‖w‖ > r}`, then the orbit `x` can be chosen so that
`A_H(t ↦ u(p.endChart (ε R, t))) → A_H(x)` as `R → ∞`. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlane_endChart_of_floer
    (p : PSSPlane)
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hB : IsCompact B)
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (p.endChart (p.endSign * R n, t))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (p.endChart (p.endSign * R, t)))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
  obtain ⟨a, ha, hr⟩ := exists_le_and_le_exp r T₀
  have hHd : ∀ t, Differentiable ℝ (H t) := fun t ↦
    (hHs.differentiable one_ne_zero).comp ((differentiable_const t).prodMk differentiable_id)
  obtain ⟨hu', _, huB', hfloer', hE'⟩ :=
    floer_comp_pssPlane_endChart_positive hKH hH hHd two_ne_zero ha hr hu huB hfloer hE
  have hper (s : ℝ) : Periodic (fun t ↦ (u ∘ positive.endChart) (s, t)) 1 := fun t ↦ by
    simp only [comp_apply, positive.endChart_add_one]
  obtain ⟨y, hyper, hy, ⟨R, -, hR, huy⟩, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer
      (p.contDiff_uncurry_positiveEndHamiltonian hHs) (p.periodic_positiveEndHamiltonian hH)
      hu' (fun s _ ↦ hper s) hB huB' hc
      (fun z hz ↦ hJc _ (lt_norm_equivRealProdCLM_symm_endChart_positive hr hz.1))
      (fun z hz ↦ hJM _ (lt_norm_equivRealProdCLM_symm_endChart_positive hr hz.1))
      hfloer' hE'
  refine ⟨fun t ↦ y (p.endSign * t), p.periodic_comp_endSign_mul hyper,
    hasDerivAt_comp_pssPlane_endSign_mul p hy, ⟨R, hR, ?_⟩, ?_⟩
  · rw [funext fun n ↦ p.comp_endChart_eq_comp_endChart_positive u (R n)]
    exact huy.comp _
  · have hAp (z : ℝ → V) (hz : Periodic z 1) :
        ω.hamiltonianAction H (fun t ↦ z (p.endSign * t)) =
          p.endSign * ω.hamiltonianAction (p.positiveEndHamiltonian H) z := by
      rw [ω.hamiltonianAction_pssPlane_positiveEndHamiltonian p hH hz, ← mul_assoc,
        endSign_mul_endSign, one_mul]
    have hAs : (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (p.endChart (p.endSign * R, t)))) =
        fun R ↦ p.endSign * ω.hamiltonianAction (p.positiveEndHamiltonian H)
          (fun t ↦ (u ∘ positive.endChart) (R, t)) :=
      funext fun R ↦ by
        rw [p.comp_endChart_eq_comp_endChart_positive u R]
        exact hAp _ (hper R)
    rw [hAs, hAp _ hyper]
    exact hA.const_mul _

/-- **The asymptotic orbit at the end of a finite-energy PSS plane.** Let `𝔎` be the perturbation of
a PSS plane `p` given by a period-one `C¹` Hamiltonian `H`. Let `u` be `C¹` on a part `‖w‖ > r` of
the end, with image in a compact set `K`, solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there
for almost complex structures `J(z)` with `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖`, `c > 0`,
and with finite energy there. Then there is a one-periodic orbit `x` of the Hamiltonian vector
field such that the loops `ℓ_R(t) = u(φ(ε R + i t))`, where `φ` is the end lift
`p.cylindricalEndLift` and `ε = p.endSign`, converge uniformly to `x` along some `R_n → ∞`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) {K : Set V}
    (hK : IsCompact K) (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
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
  simpa only [endChart_mk] using
    exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_of_floer p
      (K := p.perturbation H) (T₀ := 2) (fun _ x _ hw ↦ perturbation_eq_smul_endAngularForm hw x)
      hH hHs hu hK huK hc hJc hJM hfloer hE

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
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) {K : Set V}
    (hK : IsCompact K) (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
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
  simpa only [endChart_mk] using
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlane_endChart_of_floer p
      (K := p.perturbation H) (T₀ := 2) (fun _ x _ hw ↦ perturbation_eq_smul_endAngularForm hw x)
      hH hHs hu hK huK hc hJc hJM hfloer hE

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
    {K : Set V} (hK : IsCompact K) {r : ℝ}
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

end AsymptoticOrbits

end TauCeti.SymplecticForm
