/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Basic
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Analysis.SpecialFunctions.Log.DivLeIff

/-!
# Capping the output of the pair of pants with a positive PSS plane

The Piunikhin–Salamon–Schwarz map from Floer to Morse theory counts *positive planes*: maps from
the plane with a positive (input) cylindrical end, solving the perturbed Cauchy–Riemann equation
for a perturbation one-form that equals `H(t) dt` far out on the end and vanishes on a disc about
the pole, where the map meets a stable manifold of a Morse function. The comparison between the
pair-of-pants product and the quantum product closes up a pair of pants by gluing negative PSS
planes into its two inputs and a positive PSS plane onto its output; the negative planes and the
input capping families are in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping`. This file
constructs the perturbation data of the positive plane and of the output capping family.

The positive plane is modelled on the Riemann sphere minus `0`, with the input end at `0` of the
thrice-punctured sphere `ℂ ∖ {0, 1}`, with end lift `z ↦ exp (-2πz) / 2` on the half-plane
`Re z > 0`, and with its pole at `∞`. Its perturbation `TauCeti.Floer.positivePlanePerturbation H`
is `β(s - 1) H(t) dt` in the end coordinates `(s, t)`, and it vanishes wherever `s ≤ 1`, that is
on `‖w‖ ≥ exp (-2π) / 2`. This region is a neighbourhood of the pole `∞` and contains the point
`1`, which is an ordinary point of the plane. The datum is the pair-of-pants perturbation whose
second input and output Hamiltonians vanish (`TauCeti.Floer.pairOfPantsPerturbation_single_zero`),
and this identification transfers the smoothness, the curvature estimates and the energy identity
of the pair of pants to the plane.

The output capping family is the plumbed perturbation
`TauCeti.Floer.plumbedPerturbation Ha (Pi.single 0 (Ha ∞)) 0 L`, which glues the output end of the
pair of pants with Hamiltonians `Ha` into the input end of the positive plane with Hamiltonian
`Ha ∞`, along a neck of length `L`. The plumbing map `ψ` sends the inputs `0` and `1` of the pair
of pants to `0` and `ψ(1)`, so the capped datum lives on the sphere with the two input punctures
`0` and `ψ(1)` and the pole `∞`. Like the plane datum, it vanishes on `‖w‖ ≥ exp (-2π) / 2`, so it
is smooth across `1` and near the pole, and its integrated curvature is bounded uniformly in `L`.

## Main definitions

* `TauCeti.Floer.positivePlanePerturbation H`: the perturbation of the positive plane with input
  Hamiltonian `H`.

## Main results

* `TauCeti.Floer.positivePlanePerturbation_eq_zero_of_le_norm`: the plane datum vanishes on
  `‖w‖ ≥ exp (-2π) / 2`, a neighbourhood of the pole `∞` containing `1`.
* `TauCeti.Floer.positivePlanePerturbation_cylindricalEndLift`: far out on the end it is
  `H(t) dt`.
* `TauCeti.Floer.contMDiffAt_positivePlanePerturbation`: for a period-one Hamiltonian of class
  `C^n`, the plane datum is of class `C^n` on `(ℂ ∖ {0}) × M`.
* `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_positivePlanePerturbation_le`: its
  integrated curvature along any map is at most a bound for `|H|`.
* `TauCeti.SymplecticForm.integral_floerEnergyDensity_positivePlanePerturbation_annulus`: the
  energy identity over the closed annulus between the circle `s = R` of the end and the circle
  `‖w‖ = 2 exp (2πR)`.
* `SymplecticForm.abs_integral_floerEnergyDensity_positivePlanePerturbation_annulus_sub_le`: the
  resulting energy bound, uniform in `R`.
* `TauCeti.Floer.plumbedPerturbation_single_zero_eq_zero_of_le_norm`: the output-capped datum
  vanishes on `‖w‖ ≥ exp (-2π) / 2`.
* `TauCeti.Floer.contMDiffAt_plumbedPerturbation_single_zero`: for `L > 4` the output-capped datum
  is of class `C^n` on `ℂ ∖ {0, ψ(1)}`.
* `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_single_zero_le`:
  the integrated curvature of the output capping family is bounded uniformly in the neck length.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  perturbed planes of the PSS maps and the comparison of the pair-of-pants and quantum products.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*} {H : ℝ → M → ℝ}

/-- The Hamiltonian perturbation one-form on the positive PSS plane with input Hamiltonian `H`.
At `w ∈ ℂ` and `x ∈ M` it is the covector `β(s(w) - 1) H(t(w), x) dt`, where `(s, t)` are the
coordinates of the end at `0` of the thrice-punctured sphere, with end lift `z ↦ exp (-2πz) / 2`
on `Re z > 0`, and `β = smoothTransition` is the smooth transition from `0` on `(-∞, 0]` to `1` on
`[1, ∞)`. The pole of the plane is `∞`. -/
def positivePlanePerturbation (H : ℝ → M → ℝ) (w : ℂ) (x : M) : ℂ →L[ℝ] ℝ :=
  (smoothTransition ((zero.endCoord w).re - 1) * H (zero.endCoord w).im x) •
    zero.endAngularForm w

/-- The defining equation of the positive plane perturbation: the cutoff-weighted covector
`β(s - 1) H(t, x) dt` of the end at `0`. -/
theorem positivePlanePerturbation_def (H : ℝ → M → ℝ) (w : ℂ) (x : M) :
    positivePlanePerturbation H w x =
      (smoothTransition ((zero.endCoord w).re - 1) * H (zero.endCoord w).im x) •
        zero.endAngularForm w :=
  (rfl)

/-- **The plane is a pair of pants with one input.** The pair-of-pants perturbation whose input
Hamiltonian at `0` is `H` and whose other two Hamiltonians vanish is the positive plane
perturbation of `H`. -/
@[simp]
theorem pairOfPantsPerturbation_single_zero (H : ℝ → M → ℝ) :
    pairOfPantsPerturbation (Pi.single zero H) = positivePlanePerturbation H := by
  funext w x
  rw [pairOfPantsPerturbation_def, Fintype.sum_eq_single zero fun q hq => by
    simp [Pi.single_eq_of_ne hq]]
  simp [positivePlanePerturbation_def]

/-- Families indexed by the ends that are `H` at `0` and zero elsewhere inherit any property
shared by `H` and `0`. -/
private theorem forall_single_zero {P : (ℝ → M → ℝ) → Prop} (h₀ : P 0) (hH : P H)
    (q : Puncture) : P ((Pi.single zero H : Puncture → ℝ → M → ℝ) q) := by
  rw [Pi.single_apply]
  split_ifs
  exacts [hH, h₀]

/-- A bound `|H| ≤ B` gives the bounds `Pi.single 0 B` for the family that is `H` at `0` and
zero elsewhere. -/
private theorem abs_single_zero_le {B : ℝ} (hB : ∀ t x, |H t x| ≤ B) (r : Puncture) (t : ℝ)
    (x : M) :
    |(Pi.single zero H : Puncture → ℝ → M → ℝ) r t x| ≤ (Pi.single zero B : Puncture → ℝ) r := by
  rcases eq_or_ne r zero with rfl | hr
  · simpa using hB t x
  · simp [Pi.single_eq_of_ne hr]

/-- On `‖w‖ ≥ exp (-2π) / 2` the longitudinal coordinate `s` of the end at `0` is at most `1`. -/
private theorem re_endCoord_zero_le_one {w : ℂ} (hw : Real.exp (-(2 * π)) / 2 ≤ ‖w‖) :
    (zero.endCoord w).re ≤ 1 := by
  have hw₀ : w ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hw
    linarith [Real.exp_pos (-(2 * π))]
  rw [re_endCoord, endCenter_zero, endScale_zero, sub_zero,
    Real.neg_log_div_le_iff (by simpa using hw₀) (by positivity), norm_div, norm_div, norm_one,
    Complex.norm_ofNat, mul_one]
  rw [div_div_eq_mul_div, div_one]
  linarith

/-- The radius `exp (-2π) / 2` is less than `1 / 2`, so points within `1 / 2` of `1`, such as
`1` itself, lie in the region `‖w‖ > exp (-2π) / 2` where the plane datum vanishes. -/
private theorem exp_neg_two_pi_div_two_lt_half : Real.exp (-(2 * π)) / 2 < 1 / 2 := by
  have : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  linarith

/-- **The pole region.** The positive plane perturbation vanishes on `‖w‖ ≥ exp (-2π) / 2`, where
the longitudinal coordinate `s` of the end is at most `1`. This region is a neighbourhood of the
pole `∞` and contains the point `1`. -/
theorem positivePlanePerturbation_eq_zero_of_le_norm {w : ℂ}
    (hw : Real.exp (-(2 * π)) / 2 ≤ ‖w‖) (x : M) : positivePlanePerturbation H w x = 0 := by
  rw [positivePlanePerturbation_def,
    smoothTransition.zero_of_nonpos (by linarith [re_endCoord_zero_le_one hw]), zero_mul,
    zero_smul]

/-- Near a point of the open region `‖w‖ > exp (-2π) / 2`, the positive plane perturbation
vanishes. -/
private theorem eventually_positivePlanePerturbation_eq_zero {z : ℝ × ℝ}
    (hz : Real.exp (-(2 * π)) / 2 < ‖Complex.equivRealProdCLM.symm z‖) :
    ∀ᶠ z' in 𝓝 z, positivePlanePerturbation H (Complex.equivRealProdCLM.symm z') = fun _ ↦ 0 := by
  filter_upwards [(Complex.equivRealProdCLM.symm.continuous.norm.continuousAt (x := z)).eventually
    (lt_mem_nhds hz)] with z' hz'
  exact funext (positivePlanePerturbation_eq_zero_of_le_norm hz'.le)

/-- **The perturbation on the end.** On the half-plane `Re z > 0`, the pullback of the positive
plane perturbation along the end lift `φ` is the continuation datum `β(s - 1) H(t) dt`: it sends
a tangent vector `v` of the cylinder to `Im v · β(Re z - 1) H(Im z)`. -/
theorem positivePlanePerturbation_cylindricalEndLift_of_pos (hH : Periodic H 1) {z : ℂ}
    (hz : 0 < z.re) (x : M) (v : ℂ) :
    positivePlanePerturbation H (zero.cylindricalEndLift z) x
        (deriv zero.cylindricalEndLift z * v) =
      v.im * (smoothTransition (z.re - 1) * H z.im x) := by
  have h := pairOfPantsPerturbation_cylindricalEndLift_of_pos (H := Pi.single zero H) (q := zero)
    (by simpa using hH) (z := z) (by simpa using hz) x v
  simpa using h

/-- **The perturbation is `H(t) dt` far out on the end.** On the half-plane `Re z ≥ 2`, the
pullback of the positive plane perturbation along the end lift sends a tangent vector `v` of the
cylinder to `Im v · H(Im z)`. -/
theorem positivePlanePerturbation_cylindricalEndLift (hH : Periodic H 1) {z : ℂ}
    (hz : 2 ≤ z.re) (x : M) (v : ℂ) :
    positivePlanePerturbation H (zero.cylindricalEndLift z) x
        (deriv zero.cylindricalEndLift z * v) =
      v.im * H z.im x := by
  rw [positivePlanePerturbation_cylindricalEndLift_of_pos hH (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The plane perturbation is smooth.** For a Hamiltonian of period one which is `C^n` on
`ℝ × M`, the positive plane perturbation is `C^n` on `(ℂ ∖ {0}) × M`. Near points with
`‖w‖ > exp (-2π) / 2` it vanishes, and elsewhere off the input puncture it is the pair-of-pants
perturbation with one input. -/
theorem contMDiffAt_positivePlanePerturbation {n : ℕ∞} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry H)) {w : ℂ} (hw : w ≠ 0) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => positivePlanePerturbation H p.1 p.2) (w, x) := by
  rcases lt_or_ge (Real.exp (-(2 * π)) / 2) ‖w‖ with hlt | hge
  · -- Near the pole region, the perturbation vanishes.
    refine (contMDiffAt_const (c := (0 : ℂ →L[ℝ] ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [continuous_fst.norm.continuousAt.eventually (lt_mem_nhds hlt)] with p hp
    exact positivePlanePerturbation_eq_zero_of_le_norm hp.le p.2
  · -- Off it, the point lies in the pair of pants with one input.
    have hw₁ : w ≠ 1 := by
      rintro rfl
      rw [norm_one] at hge
      linarith [exp_neg_two_pi_div_two_lt_half]
    rw [← pairOfPantsPerturbation_single_zero]
    exact contMDiffAt_pairOfPantsPerturbation
      (forall_single_zero (P := fun f => Periodic f 1) (fun _ => rfl) hH)
      (forall_single_zero (P := fun f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f))
        contMDiff_const hHs) ⟨w, hw, hw₁⟩ x

/-! ### Capping the output of the pair of pants -/

variable {Ha : Puncture → ℝ → M → ℝ} {L : ℝ}

omit [TopologicalSpace M] [ChartedSpace G M] in
/-- **The capped pole region.** Plumb the output end of a pair of pants with Hamiltonians `Ha`
into the input end of the positive plane with Hamiltonian `Ha ∞`, along a neck of length `L > 2`.
The capped datum vanishes on `‖w‖ ≥ exp (-2π) / 2`, where it is the plane datum. -/
theorem plumbedPerturbation_single_zero_eq_zero_of_le_norm (hL : 2 < L) {w : ℂ}
    (hw : Real.exp (-(2 * π)) / 2 ≤ ‖w‖) (x : M) :
    plumbedPerturbation Ha (Pi.single zero (Ha inf)) zero L w x = 0 := by
  rw [plumbedPerturbation_def, ite_eq_right (by linarith [re_endCoord_zero_le_one hw]),
    pairOfPantsPerturbation_single_zero, positivePlanePerturbation_eq_zero_of_le_norm hw]

/-- **The output-capped datum is smooth.** For period-one Hamiltonians `Ha` of class `C^n` on
`ℝ × M` and neck length `L > 4`, the perturbation obtained by plumbing the output end of the pair
of pants with Hamiltonians `Ha` into the input end of the positive plane with Hamiltonian `Ha ∞`
is `C^n` at every point of `ℂ × M` whose domain point is neither of the two input punctures `0`
and `ψ(1)` of the capped sphere, where `ψ` is the plumbing map. -/
theorem contMDiffAt_plumbedPerturbation_single_zero {n : ℕ∞} (hHa : ∀ r, Periodic (Ha r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Ha r))) (hL : 4 < L) {w : ℂ}
    (hw : w ≠ 0 ∧ w ≠ zero.plumbingMap L 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => plumbedPerturbation Ha (Pi.single zero (Ha inf)) zero L p.1 p.2)
      (w, x) := by
  rcases lt_or_ge (Real.exp (-(2 * π)) / 2) ‖w‖ with hlt | hge
  · -- Near the pole region, the datum vanishes.
    refine (contMDiffAt_const (c := (0 : ℂ →L[ℝ] ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [continuous_fst.norm.continuousAt.eventually (lt_mem_nhds hlt)] with p hp
    exact plumbedPerturbation_single_zero_eq_zero_of_le_norm (by linarith) hp.le p.2
  · -- Off it, the point lies in the plumbed four-punctured sphere.
    have hw₁ : w ≠ 1 := by
      rintro rfl
      rw [norm_one] at hge
      linarith [exp_neg_two_pi_div_two_lt_half]
    exact contMDiffAt_plumbedPerturbation (q := zero) (by decide) hHa
      (forall_single_zero (P := fun f => Periodic f 1) (fun _ => rfl) (hHa inf))
      hHas (forall_single_zero (P := fun f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f))
        contMDiff_const (hHas inf)) (by simp) hL ⟨⟨hw.1, hw₁⟩, hw.2⟩ x

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : ℝ → V → ℝ} {Ha : Puncture → ℝ → V → ℝ} {L : ℝ}

/-- **The integrated curvature of the positive plane.** Let `K` be the positive plane perturbation
of a period-one `C¹` Hamiltonian `H` with `|H| ≤ B`, with components `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`. Then for every map `u` into the
target, the integral of `|R_K(z, u(z))|` over the plane is at most `B`. -/
theorem lintegral_enorm_hamiltonianCurvature_positivePlanePerturbation_le (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal B := by
  have h := ω.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le
    (forall_single_zero (P := fun f => Periodic f 1) (fun _ => rfl) hH)
    (forall_single_zero (P := fun f => ContDiff ℝ 1 (uncurry f)) contDiff_const hHs)
    (abs_single_zero_le hB) u
  rwa [pairOfPantsPerturbation_single_zero, Fintype.sum_eq_single zero fun r hr => by
    simp [Pi.single_eq_of_ne hr], Pi.single_eq_same] at h

omit [FiniteDimensional ℝ V] in
/-- The components of the positive plane perturbation in real coordinates are `C¹` jointly in the
domain point and the target point, off the input puncture. -/
private theorem contDiffOn_positivePlanePerturbation_apply (hH : Periodic H 1)
    (hHs : ContDiff ℝ 1 (uncurry H)) (v : ℂ) :
    ContDiffOn ℝ 1
      (uncurry fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x v)
      ({z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0} ×ˢ univ) := by
  have hHs' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry H) := by
    have h := hHs.contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  rintro ⟨z, x⟩ ⟨hz, -⟩
  have h : ContMDiffAt 𝓘(ℝ, ℂ × V) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × V => positivePlanePerturbation H p.1 p.2)
      (Complex.equivRealProdCLM.symm z, x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffAt_positivePlanePerturbation hH hHs' hz x
  exact ((h.contDiffAt.comp (z, x) ((Complex.equivRealProdCLM.symm.contDiff.comp
    contDiff_fst).prodMk contDiff_snd).contDiffAt).clm_apply contDiffAt_const).contDiffWithinAt

/-- **The energy identity on annuli of the positive plane.** Let `K` be the positive plane
perturbation of a period-one `C¹` Hamiltonian `H`, with components `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let `u` be a map which is
`C¹` off the input puncture `0`. For `R ≥ 1`, over the closed annulus
`A_R = {exp (-2πR) / 2 ≤ ‖w‖ ≤ 2 exp (2πR)}`, whose inner boundary is the circle `s = R` of the
end, the Floer energy of `u` is its symplectic area, plus `β(R - 1)` times the integral of `H(t)`
along the inner boundary circle, minus the integrated curvature:

`∫_{A_R} E = ∫_{A_R} u^*ω + β(R - 1) ∫₀¹ H(t, u(φ(R + i t))) dt - ∫_{A_R} R_K(u)`.

Here `φ` is the end lift `z ↦ exp (-2πz) / 2` and `β = smoothTransition`, so `β(R - 1) = 1` for
`R ≥ 2`. The perturbation vanishes near the outer boundary circle. -/
theorem integral_floerEnergyDensity_positivePlanePerturbation_annulus (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0}) {R : ℝ}
    (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
          Metric.ball 0 (Real.exp (-(2 * π * R)) / 2)),
        ω.floerEnergyDensity
          (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
            Metric.ball 0 (Real.exp (-(2 * π * R)) / 2)),
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1,
          H t (u (Complex.equivRealProdCLM (zero.cylindricalEndLift (R + t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
            Metric.ball 0 (Real.exp (-(2 * π * R)) / 2)),
          ω.hamiltonianCurvature
            (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  set U := {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0}
  set A := Complex.equivRealProdCLM.symm ⁻¹' (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
    Metric.ball 0 (Real.exp (-(2 * π * R)) / 2))
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  -- On the truncation, this is the energy identity of the pair of pants with one input.
  have hT := ω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
    (forall_single_zero (P := fun f => Periodic f 1) (fun _ => rfl) hH)
    (forall_single_zero (P := fun f => ContDiff ℝ 1 (uncurry f)) contDiff_const hHs)
    (hu.mono fun z hz => hz.1) hR
  rw [pairOfPantsPerturbation_single_zero, Fintype.sum_eq_single zero fun r hr => by
    simp [Pi.single_eq_of_ne hr]] at hT
  simp only [Pi.single_eq_same, endSign_zero, one_mul] at hT
  -- The annulus is the truncation together with a small disc about `1`, which lies in the region
  -- `‖w‖ > exp (-2π) / 2` where the perturbation vanishes.
  have hTA : T ⊆ A := fun z hz => by
    rw [mem_preimage, truncation_eq] at hz
    exact ⟨hz.2, fun h => (not_lt.2 hz.1.1) (mem_ball_zero_iff.1 h)⟩
  have hAT {z : ℝ × ℝ} (hz : z ∈ A \ T) :
      Real.exp (-(2 * π)) / 2 < ‖Complex.equivRealProdCLM.symm z‖ := by
    obtain ⟨⟨hzD, hzB⟩, hzT⟩ := hz
    have h₀ : Real.exp (-(2 * π * R)) / 2 ≤ ‖Complex.equivRealProdCLM.symm z‖ :=
      not_lt.1 fun h => hzB (mem_ball_zero_iff.2 h)
    have h₁ : ‖Complex.equivRealProdCLM.symm z - 1‖ < Real.exp (-(2 * π * R)) / 2 := by
      by_contra! h
      exact hzT (by rw [mem_preimage, truncation_eq]; exact ⟨⟨h₀, h⟩, hzD⟩)
    have he : Real.exp (-(2 * π * R)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have hnorm := norm_sub_norm_le (1 : ℂ) (Complex.equivRealProdCLM.symm z)
    rw [norm_one, norm_sub_rev] at hnorm
    linarith [exp_neg_two_pi_div_two_lt_half]
  have hAU : A ⊆ U := fun z hz h =>
    hz.2 (by rw [h]; exact Metric.mem_ball_self (by positivity))
  -- The three integrands are continuous off the input puncture, hence integrable on the compact
  -- annulus.
  have hU : IsOpen U := isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const
  have hKs := contDiffOn_positivePlanePerturbation_apply hH hHs 1
  have hKt := contDiffOn_positivePlanePerturbation_apply hH hHs Complex.I
  have hA : IsCompact A :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      ((isCompact_closedBall _ _).diff Metric.isOpen_ball)
  have hATm : MeasurableSet (A \ T) :=
    hA.isClosed.measurableSet.diff (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_truncation R)).isClosed.measurableSet
  have hint (f : ℝ × ℝ → ℝ) (hf : ContinuousOn f U) : IntegrableOn f A :=
    (hf.mono hAU).integrableOn_compact hA
  have hdu := hu.continuousOn_fderiv_of_isOpen hU le_rfl
  have hE := hint _ (ω.continuousOn_floerEnergyDensity hU hu hKs hKt)
  have harea := hint (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal)
    (fderiv ℝ u z stdComplexLineImag)) (ω.continuousOn_apply_comp (hdu.clm_apply continuousOn_const)
      (hdu.clm_apply continuousOn_const))
  have hcurv := hint _ (ω.continuousOn_hamiltonianCurvature_comp hU hu.continuousOn hKs hKt)
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f A) :
      ∫ z in A, f z = (∫ z in T, f z) + ∫ z in A \ T, f z := by
    conv_lhs => rw [← union_sdiff_cancel hTA]
    exact setIntegral_union disjoint_sdiff_right hATm (hf.mono_set hTA) (hf.mono_set sdiff_subset)
  -- Off the truncation the energy is the area and the curvature vanishes.
  have hEA : ∫ z in A \ T, ω.floerEnergyDensity
      (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in A \ T, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) := by
    refine setIntegral_congr_fun hATm fun z hz => ?_
    have hK := (eventually_positivePlanePerturbation_eq_zero (H := H) (hAT hz)).self_of_nhds
    simp [floerEnergyDensity_def, perturbedFDeriv_apply_stdComplexLineReal,
      perturbedFDeriv_apply_stdComplexLineImag, hK]
  have hRA : ∫ z in A \ T, ω.hamiltonianCurvature
      (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
    have hK := eventually_positivePlanePerturbation_eq_zero (H := H) (hAT hz)
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0)
      (hK.mono fun z' hz' ↦ funext fun y ↦ by simp [hz'])
      (hK.mono fun z' hz' ↦ funext fun y ↦ by simp [hz']), hamiltonianCurvature_zero_left]
    simp
  rw [hsplit _ hE, hsplit _ harea, hsplit _ hcurv, hEA, hRA, hT]
  ring

/-- **The energy bound on annuli of the positive plane.** If `|H| ≤ B`, then for every `R ≥ 1` the
Floer energy over the closed annulus `exp (-2πR) / 2 ≤ ‖w‖ ≤ 2 exp (2πR)` differs from the
symplectic area plus the Hamiltonian boundary term by at most `B`, uniformly in `R`. -/
theorem abs_integral_floerEnergyDensity_positivePlanePerturbation_annulus_sub_le
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0}) {R : ℝ}
    (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
          Metric.ball 0 (Real.exp (-(2 * π * R)) / 2)),
        ω.floerEnergyDensity
          (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
            Metric.ball 0 (Real.exp (-(2 * π * R)) / 2)),
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1,
          H t (u (Complex.equivRealProdCLM (zero.cylindricalEndLift (R + t * Complex.I)))))| ≤
      B := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [integral_floerEnergyDensity_positivePlanePerturbation_annulus ω hH hHs hu hR, hsub,
    abs_neg]
  have hB₀ : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  rw [← ENNReal.ofReal_le_ofReal_iff hB₀, ← Real.enorm_eq_ofReal_abs]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_positivePlanePerturbation_le ω hH hHs hB u))

/-- **The integrated curvature of the output capping family is bounded uniformly in the neck
length.** Plumb the output end of the pair of pants with period-one `C¹` Hamiltonians `Ha` into
the input end of the positive plane with Hamiltonian `Ha ∞`, along a neck of length `L > 4`. If
`|Ha r| ≤ Ba r`, then for every map `u` into the target the integral of `|R_K(z, u(z))|` over the
plane is at most `∑ r, Ba r + Ba ∞`, which does not depend on `L`. -/
theorem lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_single_zero_le
    (ω : SymplecticForm V) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hL : 4 < L) {Ba : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha (Pi.single zero (Ha inf)) zero L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha (Pi.single zero (Ha inf)) zero L
          (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ r, ENNReal.ofReal (Ba r) + ENNReal.ofReal (Ba inf) := by
  have h := ω.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le (q := zero) (by decide)
    hHa (forall_single_zero (P := fun f => Periodic f 1) (fun _ => rfl) (hHa inf))
    hHas (forall_single_zero (P := fun f => ContDiff ℝ 1 (uncurry f)) contDiff_const (hHas inf))
    (by simp) hL hBa (abs_single_zero_le (hBa inf)) u
  have hs : ∑ r, ENNReal.ofReal ((Pi.single zero (Ba inf) : Puncture → ℝ) r) =
      ENNReal.ofReal (Ba inf) := by
    rw [Fintype.sum_eq_single zero fun r hr => by simp [Pi.single_eq_of_ne hr],
      Pi.single_eq_same]
  rwa [hs] at h

end TauCeti.SymplecticForm
