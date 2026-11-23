/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic
public import TauCeti.Geometry.Symplectic.Floer.Plane.Action
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Geometry.Symplectic.Floer.Manifold.Translation
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart

/-!
# The asymptotic orbit at the end of a finite-energy PSS plane

Let `p` be a PSS plane (`TauCeti.Floer.PSSPlane`) with end sign `ε = p.endSign = ±1` at `∞`, and let
`𝔎` be a Hamiltonian perturbation on `ℂ` with values in a symplectic vector space `(V, ω)` that
equals `H(t) dt` beyond signed longitudinal height `T₀` on the end of `p`, for a period-one `C¹`
Hamiltonian `H` (for instance `𝔎 = p.perturbation H` with `T₀ = 2`, or
`TauCeti.Floer.negativePlanePerturbation H` on the negative plane). Let `u` be a solution of the
Floer equation `(du - X_𝔎)^{0,1} = 0` on a part `‖w‖ > r` of the end, for uniformly tame almost
complex structures `J(z)`, with image in a compact set and with finite energy there.
For `R ∈ ℝ` write `ℓ_R(t) = u(φ(ε R + i t))` for the loop of `u` along the circle
`‖w‖ = exp (2πR)`, where `φ(z) = exp (2π ε z)` is the end lift. This file shows that `u` breaks
off a one-periodic orbit at its end:

* if `u` is `C¹`, there are a one-periodic orbit `x` of the Hamiltonian vector field,
  `x' = X_{H_t}(x)`, and radii `R_n → ∞` such that the loops `ℓ_{R_n}` converge uniformly to `x`
  (`SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_of_eq_smul_endAngularForm` and
  `SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation`);
* if `u` is `C²`, the orbit can moreover be chosen so that the actions `A_H(ℓ_R)` tend to `A_H(x)`
  as `R → ∞`
  (`SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_eq_smul_endAngularForm`
  and `SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation`);
* hence, for a `C²` solution on the whole plane with `𝔎 = p.perturbation H` and finite energy, the
  energy is `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`
  (`exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq` in
  `TauCeti.SymplecticForm`).

So `x` is the generator at which a PSS plane meets the Floer complex: an input for the positive
plane, an output for the negative plane. The energy identity of
`TauCeti.Geometry.Symplectic.Floer.Plane.Action` assumed convergence of the end actions; here it
follows from finite energy and compactness.

On the positive plane `ε = 1`, the end in the coordinates `(s, t)` of the end lift is a Floer
half-cylinder `s > a`, for any `a ≥ T₀` with `r ≤ exp (2πa)`, for the cylindrical datum `H(t) dt`,
with the structures `J ∘ φ`. Since `φ` is holomorphic, injective on every strip of angular width
one, and maps `(a, ∞) × [0, 1)` and `[a, ∞) × [0, 1)` onto `{‖w‖ > exp (2πa)}` and
`{‖w‖ ≥ exp (2πa)}`, the Floer equation pulls back along `φ` (`SymplecticForm.`
`isComplexLinearMap_perturbedFDeriv_comp_realChart_positive_of_eq_smul_endAngularForm`)
and the half-cylinder energy over `(a, ∞) × [0, 1]` and `[a, ∞) × [0, 1]` equals the plane energy
over `{‖w‖ > exp (2πa)}` and `{‖w‖ ≥ exp (2πa)}`
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_realChart_positive_Ioi_eq`,
`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_realChart_positive_Ici_eq`). The
results on finite-energy half-cylinders of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` then apply. On the negative plane, any
perturbation matching `H(t) dt` beyond `T₀` matches `(-H(-t)) dt` beyond `T₀` on the positive plane
(`TauCeti.Floer.PSSPlane.eq_smul_endAngularForm_positive_of_negative`), and its loops are the loops
of the positive plane traversed backwards
(`TauCeti.Floer.PSSPlane.cylindricalEndLift_negative_endSign_mul`). Reversing time turns an orbit
`y` of `-H(-t)` into the orbit `t ↦ y(-t)` of `H`
(`TauCeti.SymplecticForm.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse`) and
negates the action relative to `-H(-t)` (`TauCeti.SymplecticForm.hamiltonianAction_comp_neg`).

The case of a manifold target is treated in
`TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Manifold`.

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
  {ω : SymplecticForm V} {𝔎 : ℂ → V → ℂ →L[ℝ] ℝ} {H : ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ} {K : Set V}

omit [FiniteDimensional ℝ V] in
/-- A map differentiable on the part `‖w‖ > exp (2πa)` of the plane is differentiable at the image
under the end lift of the positive plane of every point of the half-cylinder `s > a`. -/
private theorem differentiableAt_realChart_positive {a : ℝ}
    (hu : DifferentiableOn ℝ u {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    {z : ℝ × ℝ} (hz : a < z.1) :
    DifferentiableAt ℝ u (realChart positive.cylindricalEndLift z) :=
  hu.differentiableAt <| (isOpen_lt continuous_const (by fun_prop)).mem_nhds
    (exp_lt_norm_realChart_positive hz)

omit [FiniteDimensional ℝ V] in
/-- Where `𝔎 = H(t) dt` beyond `T₀` on the positive plane and each `H t` is differentiable,
`y ↦ 𝔎(φ(z), y, v)` is differentiable at every target point `x` whenever `z.1 ≥ T₀`. -/
private theorem differentiableAt_perturbation_realChart_positive
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hHd : ∀ t, Differentiable ℝ (H t)) {z : ℝ × ℝ} (hz : T₀ ≤ z.1) (v : ℂ) (x : V) :
    DifferentiableAt ℝ
      (fun y ↦ 𝔎 (Complex.equivRealProdCLM.symm (realChart positive.cylindricalEndLift z)) y v)
      x := by
  set w₀ := Complex.equivRealProdCLM.symm (realChart positive.cylindricalEndLift z) with hw₀def
  have hw₀ : w₀ ≠ 0 := by
    rw [hw₀def, TauCeti.Complex.equivRealProdCLM_symm_realChart]
    exact positive.cylindricalEndLift_ne_zero _
  have hre : (positive.endCoord w₀).re = z.1 := by
    rw [hw₀def, TauCeti.Complex.equivRealProdCLM_symm_realChart, re_endCoord_cylindricalEndLift,
      Complex.equivRealProdCLM_symm_apply_re]
  have heq : (fun y ↦ 𝔎 w₀ y v) =
      fun y ↦ H (positive.endCoord w₀).im y * positive.endAngularForm w₀ v := by
    funext y
    rw [h𝔎 w₀ y hw₀ (hre ▸ hz), smul_apply, smul_eq_mul]
  rw [heq]
  exact ((hHd (positive.endCoord w₀).im) x).mul_const _

/-- Where `𝔎 = H(t) dt` beyond `T₀` on the positive plane, the pullback of `𝔎` along the end lift
is `H(t) dt` on `{s ≥ T₀}`, so the perturbed derivatives of the two data agree there. -/
private theorem perturbedFDeriv_comp_realChart_positive_of_eq_smul_endAngularForm
    (ω : SymplecticForm V)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (u : ℝ × ℝ → V) {z : ℝ × ℝ} (hz : T₀ ≤ z.1) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      ω.perturbedFDeriv
        (perturbationPullback (realChart positive.cylindricalEndLift)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal)
        (perturbationPullback (realChart positive.cylindricalEndLift)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag)
        u z := by
  refine ω.perturbedFDeriv_congr _ (funext fun x ↦ ?_) (funext fun x ↦ ?_)
  · rw [perturbationPullback_realChart_positive_of_eq_smul_endAngularForm h𝔎 hH _ hz,
      equivRealProdCLM_symm_stdComplexLineReal]
    simp
  · rw [perturbationPullback_realChart_positive_of_eq_smul_endAngularForm h𝔎 hH _ hz,
      equivRealProdCLM_symm_stdComplexLineImag]
    simp

/-- **The Floer equation on the end of the positive plane (general perturbation).** Where
`𝔎 = H(t) dt` beyond `T₀` on the positive plane, if `u` solves `(du - X_𝔎)^{0,1} = 0` at the image
of `(s, t)` under `φ` with `s ≥ T₀`, then `u ∘ φ` solves the cylindrical Floer equation at `(s, t)`
for `H(t) dt` and the same structure `J`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_realChart_positive_of_eq_smul_endAngularForm
    (ω : SymplecticForm V)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {J : AlmostComplexStructure V}
    {z : ℝ × ℝ} (hz : T₀ ≤ z.1)
    (hu : DifferentiableAt ℝ u (realChart positive.cylindricalEndLift z))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (realChart positive.cylindricalEndLift z) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (u ∘ realChart positive.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [perturbedFDeriv_comp_realChart_positive_of_eq_smul_endAngularForm ω h𝔎 hH _ hz]
  exact ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback
    ((contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable one_ne_zero z) hu
    (differentiableAt_perturbation_realChart_positive h𝔎 hHd hz 1 _)
    (differentiableAt_perturbation_realChart_positive h𝔎 hHd hz Complex.I _)
    (isComplexLinearMap_fderiv_realChart (positive.hasDerivAt_cylindricalEndLift _)) hfloer

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
        (u ∘ realChart positive.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V) :=
  ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_positive_of_eq_smul_endAngularForm
    (fun _ x _ hw ↦ positive.perturbation_eq_smul_endAngularForm (by simpa using hw) x) hH
    (fun t ↦ (hHs.differentiable one_ne_zero).comp
      ((differentiable_const t).prodMk differentiable_id))
    hz hu hfloer

/-- Where `𝔎 = H(t) dt` beyond `T₀` on the positive plane, for `z.1 ≥ T₀` the cylindrical energy
density of `u ∘ φ` is the Jacobian determinant of `φ` times the energy density of `u` for `𝔎`. -/
theorem floerEnergyDensity_comp_realChart_positive_of_eq_smul_endAngularForm
    (ω : SymplecticForm V)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {z : ℝ × ℝ} (hz : T₀ ≤ z.1)
    (hu : DifferentiableAt ℝ u (realChart positive.cylindricalEndLift z)) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (u ∘ realChart positive.cylindricalEndLift) z =
      (fderiv ℝ (realChart positive.cylindricalEndLift) z).det *
        ω.floerEnergyDensity
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u
          (realChart positive.cylindricalEndLift z) := by
  rw [floerEnergyDensity_def,
    perturbedFDeriv_comp_realChart_positive_of_eq_smul_endAngularForm ω h𝔎 hH _ hz,
    ← floerEnergyDensity_def]
  exact ω.floerEnergyDensity_perturbationPullback
    ((contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable one_ne_zero z) hu
    (differentiableAt_perturbation_realChart_positive h𝔎 hHd hz 1 _)
    (differentiableAt_perturbation_realChart_positive h𝔎 hHd hz Complex.I _)

/-- **Exact exterior energy on `(a, ∞)`.** Where `𝔎 = H(t) dt` beyond `T₀` on the positive plane,
for `a ≥ T₀` the half-cylinder energy of `u ∘ φ` over `(a, ∞) × [0, 1]` equals the Floer energy of
`u` over `{‖w‖ > exp (2πa)}`. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_positive_Ioi_eq
    (ω : SymplecticForm V)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {a : ℝ} (ha : T₀ ≤ a)
    (hu : DifferentiableOn ℝ u
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖}) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) =
      ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) :=
  setLIntegral_ofReal_comp_realChart_positive_Ioi_eq fun _ hz ↦
    ω.floerEnergyDensity_comp_realChart_positive_of_eq_smul_endAngularForm h𝔎 hH hHd
      (ha.trans hz.1.le) (differentiableAt_realChart_positive hu hz.1)

/-- **Exact exterior energy on `[a, ∞)`.** Where `𝔎 = H(t) dt` beyond `T₀` on the positive plane,
for `a ≥ T₀` the half-cylinder energy of `u ∘ φ` over `[a, ∞) × [0, 1]` equals the Floer energy of
`u` over `{‖w‖ ≥ exp (2πa)}`. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_positive_Ici_eq
    (ω : SymplecticForm V)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {a : ℝ} (ha : T₀ ≤ a)
    (hu : ∀ z, Real.exp (2 * π * a) ≤ ‖Complex.equivRealProdCLM.symm z‖ →
      DifferentiableAt ℝ u z) :
    ∫⁻ z in Ici a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) =
      ∫⁻ z in {z | Real.exp (2 * π * a) ≤ ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) :=
  setLIntegral_ofReal_comp_realChart_positive_Ici_eq fun z hz ↦
    ω.floerEnergyDensity_comp_realChart_positive_of_eq_smul_endAngularForm h𝔎 hH hHd
      (ha.trans hz.1) (hu _ <| by
        rw [positive.norm_symm_realChart_cylindricalEndLift, endSign_positive, one_mul]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz.1 Real.two_pi_pos.le))

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
          u z) :=
  (ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_Ioi_eq
    (fun _ x _ hw ↦ positive.perturbation_eq_smul_endAngularForm (by simpa using hw) x) hH
    (fun t ↦ (hHs.differentiable one_ne_zero).comp
      ((differentiable_const t).prodMk differentiable_id)) ha hu).le

/-- **The energy on part of the end of the positive plane.** For `a ≥ 2`, if `u` is differentiable
on the part `‖w‖ > exp (2πa)` of the positive plane, then the energy of `u ∘ φ` for the cylindrical
datum `H(t) dt` over a measurable subset `s` of a half-strip `s > a`, `t₀ ≤ t < t₀ + 1` of angular
width one is at most the energy of `u` on that part of the plane. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_positive_le_of_subset
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {a t₀ : ℝ}
    (ha : 2 ≤ a)
    (hu : DifferentiableOn ℝ u
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hst : s ⊆ Ioi a ×ˢ Ico t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≤
      ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) :=
  setLIntegral_ofReal_comp_realChart_positive_le_of_subset hs hst fun _ hz ↦
    ω.floerEnergyDensity_comp_realChart_positive_of_eq_smul_endAngularForm
      (fun _ x _ hw ↦ positive.perturbation_eq_smul_endAngularForm (by simpa using hw) x) hH
      (fun t ↦ (hHs.differentiable one_ne_zero).comp
        ((differentiable_const t).prodMk differentiable_id))
      (ha.trans (hst hz).1.le) (differentiableAt_realChart_positive hu (hst hz).1)

/-- **The energy of a translated end of the positive plane.** For `a ≥ 2`, if `u` is
differentiable on the part `‖w‖ > exp (2πa)` of the positive plane, and the translate `s + (R, 0)`
of a measurable set `s` lies in a half-strip `s > a`, `t₀ ≤ t < t₀ + 1` of angular width one, then
the energy of the translated end `z ↦ u(φ(z + (R, 0)))` for the cylindrical datum `H(t) dt` over
`s` is at most the energy of `u` on that part of the plane. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_positive_add_le
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {a t₀ : ℝ}
    (ha : 2 ≤ a)
    (hu : DifferentiableOn ℝ u
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    (R : ℝ) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hst : ∀ z ∈ s, z + (R, 0) ∈ Ioi a ×ˢ Ico t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0)))) z) ≤
      ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) := by
  -- The energy of the translated end over `s` is that of `u ∘ φ` over `s + (R, 0)`.
  have h := ω.constSmooth.lintegral_floerEnergyDensity_comp_add_right (fun _ _ ↦ 0)
    (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) (R, 0)
    ((· + ((R, 0) : ℝ × ℝ)) '' s)
  rw [preimage_image_eq _ (add_left_injective _)] at h
  simp only [floerEnergyDensity_constSmooth, Prod.snd_add, add_zero, comp_apply] at h
  rw [h]
  exact ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_le_of_subset hH hHs ha hu
    ((measurableEmbedding_addRight _).measurableSet_image' hs)
    (by rintro _ ⟨z, hz, rfl⟩; exact hst z hz)

/-- **Half-cylinder reduction on `(a, ∞)` of the positive plane.** Where `𝔎 = H(t) dt` beyond `T₀`
on the positive plane, for any `a ≥ T₀` with `r ≤ exp (2πa)`, a `Cⁿ` (`n ≠ 0`) finite-energy Floer
solution `u` on `{‖w‖ > r}` with values in `K` pulls back along `φ` to a `Cⁿ`, `1`-periodic,
finite-energy Floer half-cylinder on `(a, ∞) × ℝ` with values in `K`. -/
theorem floer_comp_realChart_positive_of_eq_smul_endAngularForm (ω : SymplecticForm V)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    {r a : ℝ} (ha : T₀ ≤ a) (hr : r ≤ Real.exp (2 * π * a))
    (hu : ContDiffOn ℝ n u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ContDiffOn ℝ n (u ∘ realChart positive.cylindricalEndLift) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ (u ∘ realChart positive.cylindricalEndLift) (s, t)) 1) ∧
      (∀ s, a < s → ∀ t, (u ∘ realChart positive.cylindricalEndLift) (s, t) ∈ K) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((J ∘ realChart positive.cylindricalEndLift) z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (u ∘ realChart positive.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≠ ⊤ := by
  have hsub : {z : ℝ × ℝ | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖} ⊆
      {z | r < ‖Complex.equivRealProdCLM.symm z‖} := fun _ hz ↦ hr.trans_lt hz
  have hmem {z : ℝ × ℝ} (hz : a < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (realChart positive.cylindricalEndLift z)‖ :=
    hsub (exp_lt_norm_realChart_positive hz)
  have hud := (hu.mono hsub).differentiableOn hn
  refine ⟨(hu.mono hsub).comp
      (contDiff_realChart positive.contDiff_cylindricalEndLift).contDiffOn
      fun z hz ↦ exp_lt_norm_realChart_positive hz.1,
    fun s _ ↦ ?_, fun s hs t ↦ huK _ (hmem hs),
    fun z hz ↦
      ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_positive_of_eq_smul_endAngularForm
        h𝔎 hH hHd (ha.trans hz.1.le) (differentiableAt_realChart_positive hud hz.1)
        (hfloer _ (hmem hz.1)),
    ((ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_Ioi_eq h𝔎 hH hHd ha hud).le.trans_lt
      ((lintegral_mono_set hsub).trans_lt hE.lt_top)).ne⟩
  simpa only [comp_apply, comp_def, realChart_positive_mk] using
    (positive.periodic_cylindricalEndLift (positive.endSign * s)).comp
      fun w ↦ u (Complex.equivRealProdCLM w)

/-- **The half-cylinder at the end of the positive plane.** If `u` is `Cⁿ`, `n ≠ 0`, on a part
`‖w‖ > r` of the positive plane, with image in `K`, solving the Floer equation there for structures
`J(z)` bounded by `c` and `M`, and with finite energy there, then on some half-cylinder `s > a` the
map `u ∘ φ` and the structures `J ∘ φ` satisfy the hypotheses of the finite-energy half-cylinder
theorems of `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` for the cylindrical datum
`H(t) dt`. -/
theorem exists_halfCylinder_comp_realChart_positive (ω : SymplecticForm V)
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
  obtain ⟨a, ha, hr⟩ := exists_le_and_le_exp r 2
  obtain ⟨hu', hper, huK', hfloer', hE'⟩ :=
    ω.floer_comp_realChart_positive_of_eq_smul_endAngularForm
      (fun _ x _ hw ↦ positive.perturbation_eq_smul_endAngularForm (by simpa using hw) x) hH
      (fun t ↦ (hHs.differentiable one_ne_zero).comp
        ((differentiable_const t).prodMk differentiable_id)) hn ha hr hu huK hfloer hE
  refine ⟨a, hu', hper, huK',
    fun z hz ↦ hJc _ (hr.trans_lt (exp_lt_norm_realChart_positive hz.1)),
    fun z hz ↦ hJM _ (hr.trans_lt (exp_lt_norm_realChart_positive hz.1)), hfloer', hE'⟩

/-- **The asymptotic orbit at the end of the positive plane.** -/
private theorem exists_periodic_hasDerivAt_tendstoUniformly_positive_of_eq_smul_endAngularForm
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I)))) x atTop := by
  obtain ⟨a, ha, hr⟩ := exists_le_and_le_exp r T₀
  obtain ⟨hu', hper, huK', hfloer', hE'⟩ :=
    ω.floer_comp_realChart_positive_of_eq_smul_endAngularForm h𝔎 hH
      (fun t ↦ (hHs.differentiable one_ne_zero).comp
        ((differentiable_const t).prodMk differentiable_id)) one_ne_zero ha hr hu huK hfloer hE
  obtain ⟨x, hxper, hx, φ, -, hφ, hux⟩ := exists_periodic_hasDerivAt_tendstoUniformly_of_floer
    hHs hH hu' hper hK huK' hc
    (fun z hz ↦ hJc _ (hr.trans_lt (exp_lt_norm_realChart_positive hz.1)))
    (fun z hz ↦ hJM _ (hr.trans_lt (exp_lt_norm_realChart_positive hz.1))) hfloer' hE'
  simp only [comp_apply, realChart_positive_mk] at hux
  exact ⟨x, hxper, hx, φ, hφ, hux⟩

/-- **The asymptotic action at the end of the positive plane.** -/
private theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive_of_eq_smul
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
  obtain ⟨a, ha, hr⟩ := exists_le_and_le_exp r T₀
  obtain ⟨hu', hper, huK', hfloer', hE'⟩ :=
    ω.floer_comp_realChart_positive_of_eq_smul_endAngularForm h𝔎 hH
      (fun t ↦ (hHs.differentiable one_ne_zero).comp
        ((differentiable_const t).prodMk differentiable_id)) two_ne_zero ha hr hu huK hfloer hE
  obtain ⟨x, hxper, hx, ⟨φ, -, hφ, hux⟩, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer hHs hH hu' hper hK huK' hc
      (fun z hz ↦ hJc _ (hr.trans_lt (exp_lt_norm_realChart_positive hz.1)))
      (fun z hz ↦ hJM _ (hr.trans_lt (exp_lt_norm_realChart_positive hz.1))) hfloer' hE'
  simp only [comp_apply, realChart_positive_mk] at hux hA
  exact ⟨x, hxper, hx, ⟨φ, hφ, hux⟩, hA⟩

omit [FiniteDimensional ℝ V] in
/-- The reversed Hamiltonian `-H(-t)` of a period-one `Cⁿ` Hamiltonian is again period-one and
`Cⁿ`. -/
theorem periodic_contDiff_reverse {n : WithTop ℕ∞} (hH : Periodic H 1)
    (hHs : ContDiff ℝ n (uncurry H)) :
    Periodic (fun t y ↦ -H (-t) y) 1 ∧ ContDiff ℝ n (uncurry fun t y ↦ -H (-t) y) :=
  ⟨hH.comp_neg.comp Neg.neg, (hHs.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg⟩

/-- **The orbit at the end of the negative plane.** Reversing time turns a one-periodic orbit `y` of
the reversed Hamiltonian `-H(-t)` into the one-periodic orbit `t ↦ y(-t)` of `H`; if the loops of
`u` along the end of the positive plane converge uniformly to `y` along a filter `l`, then the loops
of `u` along the end of the negative plane converge uniformly to `t ↦ y(-t)` along `l`. -/
theorem periodic_hasDerivAt_tendstoUniformly_negative {ι : Type*} {l : Filter ι}
    (ω : SymplecticForm V) {y : ℝ → V} (hyper : Periodic y 1)
    (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (fun x ↦ -H (-t) x) (y t)) t)
    {R : ι → ℝ} (huy : TendstoUniformly (fun i t ↦ u (Complex.equivRealProdCLM
      (positive.cylindricalEndLift (↑(positive.endSign * R i) + ↑t * Complex.I)))) y l) :
    Periodic (fun t ↦ y (-t)) 1 ∧
      (∀ t, HasDerivAt (fun t ↦ y (-t)) (ω.hamiltonianVectorField (H t) (y (-t))) t) ∧
      TendstoUniformly (fun i (t : ℝ) ↦ u (Complex.equivRealProdCLM
        (negative.cylindricalEndLift (↑(negative.endSign * R i) + ↑t * Complex.I))))
        (fun t ↦ y (-t)) l := by
  refine ⟨hyper.comp_neg, ω.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse hy, ?_⟩
  simp only [cylindricalEndLift_negative_endSign_mul]
  exact huy.comp fun t ↦ -t

/-- **Subsequential orbit breaking at the end of a PSS plane (general perturbation).** Let `𝔎`
agree with `H(t) dt` beyond signed height `T₀` on the end of `p`, for a period-one `C¹` Hamiltonian
`H`. Let `u` be `C¹` on `{‖w‖ > r}`, with image in a compact set `K`, solving `(du - X_𝔎)^{0,1} = 0`
there for uniformly tame structures `J(z)` with finite energy there. Then there are a one-periodic
orbit `x` of `H` and radii `R_n → ∞` along which the end loops `ℓ_{R_n}(t) = u(φ(ε R_n + i t))`
converge uniformly to `x`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_of_eq_smul_endAngularForm (p : PSSPlane)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop := by
  cases p
  · exact exists_periodic_hasDerivAt_tendstoUniformly_positive_of_eq_smul_endAngularForm
      (fun w x hw hz ↦ h𝔎 w x hw (by simpa [endSign_positive] using hz)) hH hHs hu hK huK hc hJc
      hJM hfloer hE
  obtain ⟨hH', hHs'⟩ := periodic_contDiff_reverse hH hHs
  obtain ⟨y, hyper, hy, R, hR, huy⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_positive_of_eq_smul_endAngularForm
      (fun w x hw hz ↦ eq_smul_endAngularForm_positive_of_negative h𝔎 x hw hz)
      hH' hHs' hu hK huK hc hJc hJM hfloer hE
  obtain ⟨hxper, hx, hux⟩ := ω.periodic_hasDerivAt_tendstoUniformly_negative hyper hy huy
  exact ⟨_, hxper, hx, R, hR, hux⟩

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
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop :=
  exists_periodic_hasDerivAt_tendstoUniformly_of_eq_smul_endAngularForm p
    (fun _ x _ hw ↦ p.perturbation_eq_smul_endAngularForm hw x) hH hHs hu hK huK hc hJc hJM
    hfloer hE

/-- **The asymptotic action at the end of a PSS plane (general perturbation).** Under the hypotheses
of `exists_periodic_hasDerivAt_tendstoUniformly_of_eq_smul_endAngularForm`, if `u` is `C²` on
`{‖w‖ > r}`, the broken-off orbit `x` can be chosen so that `A_H(ℓ_R) → A_H(x)` as `R → ∞`. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_eq_smul_endAngularForm
    (p : PSSPlane)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
  cases p
  · exact exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive_of_eq_smul
      (fun w x hw hz ↦ h𝔎 w x hw (by simpa [endSign_positive] using hz)) hH hHs hu hK huK hc hJc
      hJM hfloer hE
  obtain ⟨hH', hHs'⟩ := periodic_contDiff_reverse hH hHs
  obtain ⟨y, hyper, hy, ⟨R, hR, huy⟩, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_positive_of_eq_smul
      (fun w x hw hz ↦ eq_smul_endAngularForm_positive_of_negative h𝔎 x hw hz)
      hH' hHs' hu hK huK hc hJc hJM hfloer hE
  obtain ⟨hxper, hx, hux⟩ := ω.periodic_hasDerivAt_tendstoUniformly_negative hyper hy huy
  refine ⟨_, hxper, hx, ⟨R, hR, hux⟩, ?_⟩
  have hrev {x : ℝ → V} (hx : Periodic x 1) : ω.hamiltonianAction H (fun t ↦ x (-t)) =
      -ω.hamiltonianAction (fun t y ↦ -H (-t) y) x := by
    simpa only [neg_neg] using ω.hamiltonianAction_comp_neg hH' hx
  rw [hrev hyper]
  refine hA.neg.congr fun R ↦ ?_
  simp only [cylindricalEndLift_negative_endSign_mul]
  exact (hrev ((positive.periodic_cylindricalEndLift (positive.endSign * R)).comp
    fun w ↦ u (Complex.equivRealProdCLM w))).symm

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
        (𝓝 (ω.hamiltonianAction H x)) :=
  exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_eq_smul_endAngularForm p
    (fun _ x _ hw ↦ p.perturbation_eq_smul_endAngularForm hw x) hH hHs hu hK huK hc hJc hJM
    hfloer hE

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
