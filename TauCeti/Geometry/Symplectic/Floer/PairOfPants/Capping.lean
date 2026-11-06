/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Basic
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature

/-!
# Capping an input of the pair of pants with a negative PSS plane

The Piunikhin–Salamon–Schwarz map from Morse to Floer theory counts *negative planes*: maps from
the plane `ℂ` with a Morse incidence at the pole `0` and a negative (output) cylindrical end at
`∞`, solving the perturbed Cauchy–Riemann equation for a perturbation one-form that vanishes on a
disc about the pole and equals `H(t) dt` far out on the end. Its value on the fundamental cycle is
the unit of the pair-of-pants product, and the unit property is proved with *capping families*: a
negative plane is glued into an input `q ∈ {0, 1}` of the pair of pants along a neck of length
`L`, and the result is a cylinder with the remaining input and the output as its two ends.

This file constructs the perturbation data of these domains. The negative plane uses the
cylindrical end at `∞` of the thrice-punctured sphere `ℂ ∖ {0, 1}`, with end lift
`z ↦ 2 exp (-2πz)` on the half-plane `Re z < 0`, so that the plumbing maps
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap` glue it into the input ends of the pair of
pants. Its perturbation is `TauCeti.Floer.negativePlanePerturbation H`, which is
`β(-s - 1) H(t) dt` in the end coordinates `(s, t)` and vanishes off the part `-s > 1` of the end.
It is the pair-of-pants perturbation whose two input Hamiltonians are zero
(`TauCeti.Floer.pairOfPantsPerturbation_single_inf`), and this identification transfers the
curvature estimates and the energy identity of the pair of pants to the plane.

The capping family at the input `q` is the plumbed perturbation
`TauCeti.Floer.plumbedPerturbation (Pi.single inf (Hb q)) Hb q L`, which inserts the negative plane
with Hamiltonian `Hb q` into the end `q` of the pair of pants with Hamiltonians `Hb`. Since the
plane datum vanishes on its pole disc, the capped datum vanishes on the image of that disc, the
disc of radius `exp (-2π(L - 1)) / 2` about the capped puncture `c_q`. It is therefore smooth
across `c_q` and across the image of the point `1` of the plane, on the cylinder `ℂ ∖ {c_q'}`,
where `q'` is the other input.

## Main definitions

* `TauCeti.Floer.negativePlanePerturbation H`: the perturbation of the negative plane with
  output Hamiltonian `H`.

## Main results

* `TauCeti.Floer.negativePlanePerturbation_eq_zero_of_norm_le`: the plane datum vanishes on the
  pole disc `‖w‖ ≤ 2 exp (2π)`.
* `TauCeti.Floer.negativePlanePerturbation_cylindricalEndLift`: far out on the end it is
  `H(t) dt`.
* `TauCeti.Floer.contMDiff_negativePlanePerturbation`: for a period-one Hamiltonian of class
  `C^n`, the plane datum is of class `C^n` on all of `ℂ × M`, including the pole.
* `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_negativePlanePerturbation_le`: its
  integrated curvature along any map is at most a bound for `|H|`.
* `TauCeti.SymplecticForm.integral_floerEnergyDensity_negativePlanePerturbation_closedBall`: the
  energy identity over the disc bounded by the circle `s = -R` of the end.
* `SymplecticForm.abs_integral_floerEnergyDensity_negativePlanePerturbation_closedBall_sub_le`: the
  resulting energy bound, uniform in `R`.
* `TauCeti.Floer.plumbedPerturbation_single_inf_eq_zero`: the capped datum vanishes on the disc of
  radius `exp (-2π(L - 1)) / 2` about the capped puncture.
* `TauCeti.Floer.contMDiffAt_plumbedPerturbation_single_inf`: for `L > 4` the capped datum is of
  class `C^n` on the cylinder obtained by capping.
* `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_single_inf_le`:
  the integrated curvature of the capping family is bounded uniformly in the neck length.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  perturbed planes of the PSS maps and the unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants and gluing perturbation data.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*} {H : ℝ → M → ℝ}

/-- The Hamiltonian perturbation one-form on the negative PSS plane with output Hamiltonian `H`.
At `w ∈ ℂ` and `x ∈ M` it is the covector `β(-s(w) - 1) H(t(w), x) dt`, where `(s, t)` are the
coordinates of the end at `∞` of the thrice-punctured sphere, with end lift `z ↦ 2 exp (-2πz)`
on `Re z < 0`, and `β = smoothTransition` is the smooth transition from `0` on `(-∞, 0]` to `1` on
`[1, ∞)`. -/
def negativePlanePerturbation (H : ℝ → M → ℝ) (w : ℂ) (x : M) : ℂ →L[ℝ] ℝ :=
  (smoothTransition (-(inf.endCoord w).re - 1) * H (inf.endCoord w).im x) • inf.endAngularForm w

theorem negativePlanePerturbation_def (H : ℝ → M → ℝ) (w : ℂ) (x : M) :
    negativePlanePerturbation H w x =
      (smoothTransition (-(inf.endCoord w).re - 1) * H (inf.endCoord w).im x) •
        inf.endAngularForm w :=
  (rfl)

/-- **The plane is a pair of pants with zero inputs.** The pair-of-pants perturbation whose input
Hamiltonians vanish and whose output Hamiltonian is `H` is the negative plane perturbation of
`H`. -/
@[simp]
theorem pairOfPantsPerturbation_single_inf (H : ℝ → M → ℝ) :
    pairOfPantsPerturbation (Pi.single inf H) = negativePlanePerturbation H := by
  funext w x
  rw [pairOfPantsPerturbation_def, Fintype.sum_eq_single inf fun q hq => by
    simp [Pi.single_eq_of_ne hq]]
  simp [negativePlanePerturbation_def]

/-- **The pole disc.** The negative plane perturbation vanishes on the disc `‖w‖ ≤ 2 exp (2π)`
about the pole, where the signed longitudinal coordinate `-s` of the end is at most `1`. -/
theorem negativePlanePerturbation_eq_zero_of_norm_le {w : ℂ} (hw : ‖w‖ ≤ 2 * Real.exp (2 * π))
    (x : M) : negativePlanePerturbation H w x = 0 := by
  have h : -(inf.endCoord w).re ≤ 1 := by
    rw [re_endCoord, endCenter_inf, endScale_inf, sub_zero, neg_div, neg_neg,
      div_le_one (by positivity)]
    rcases eq_or_ne w 0 with rfl | hw₀
    · simpa using Real.pi_pos.le
    · rw [Real.log_le_iff_le_exp (by simpa using hw₀), norm_div, Complex.norm_ofNat]
      linarith
  rw [negativePlanePerturbation_def, smoothTransition.zero_of_nonpos (by linarith), zero_mul,
    zero_smul]

/-- Near a point of the open pole disc `‖w‖ < 2 exp (2π)`, the negative plane perturbation
vanishes. -/
private theorem eventually_negativePlanePerturbation_eq_zero {z : ℝ × ℝ}
    (hz : ‖Complex.equivRealProdCLM.symm z‖ < 2 * Real.exp (2 * π)) :
    ∀ᶠ z' in 𝓝 z, negativePlanePerturbation H (Complex.equivRealProdCLM.symm z') = fun _ ↦ 0 := by
  filter_upwards [(Complex.equivRealProdCLM.symm.continuous.norm.continuousAt (x := z)).eventually
    (gt_mem_nhds hz)] with z' hz'
  exact funext (negativePlanePerturbation_eq_zero_of_norm_le hz'.le)

/-- **The perturbation on the end.** On the half-plane `Re z < 0`, the pullback of the negative
plane perturbation along the end lift `φ` is the continuation datum `β(-s - 1) H(t) dt`: it sends
a tangent vector `v` of the cylinder to `Im v · β(-Re z - 1) H(Im z)`. -/
theorem negativePlanePerturbation_cylindricalEndLift_of_neg (hH : Periodic H 1) {z : ℂ}
    (hz : z.re < 0) (x : M) (v : ℂ) :
    negativePlanePerturbation H (inf.cylindricalEndLift z) x (deriv inf.cylindricalEndLift z * v) =
      v.im * (smoothTransition (-z.re - 1) * H z.im x) := by
  have h := pairOfPantsPerturbation_cylindricalEndLift_of_pos (H := Pi.single inf H) (q := inf)
    (by simpa using hH) (z := z) (by simpa using hz) x v
  simpa [pairOfPantsPerturbation_single_inf] using h

/-- **The perturbation is `H(t) dt` far out on the end.** On the half-plane `Re z ≤ -2`, the
pullback of the negative plane perturbation along the end lift sends a tangent vector `v` of the
cylinder to `Im v · H(Im z)`. -/
theorem negativePlanePerturbation_cylindricalEndLift (hH : Periodic H 1) {z : ℂ}
    (hz : z.re ≤ -2) (x : M) (v : ℂ) :
    negativePlanePerturbation H (inf.cylindricalEndLift z) x (deriv inf.cylindricalEndLift z * v) =
      v.im * H z.im x := by
  rw [negativePlanePerturbation_cylindricalEndLift_of_neg hH (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The plane perturbation is smooth.** For a Hamiltonian of period one which is `C^n` on
`ℝ × M`, the negative plane perturbation is `C^n` on `ℂ × M`. Off the open pole disc it is the
pair-of-pants perturbation with zero inputs, and on that disc it vanishes. -/
theorem contMDiff_negativePlanePerturbation {n : ℕ∞} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry H)) :
    ContMDiff (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => negativePlanePerturbation H p.1 p.2) := by
  rintro ⟨w, x⟩
  rcases lt_or_ge ‖w‖ (2 * Real.exp (2 * π)) with hlt | hge
  · -- On the open pole disc, the perturbation vanishes.
    refine (contMDiffAt_const (c := (0 : ℂ →L[ℝ] ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [continuous_fst.norm.continuousAt.eventually (gt_mem_nhds hlt)] with p hp
    exact negativePlanePerturbation_eq_zero_of_norm_le hp.le p.2
  · -- Off it, the point lies in the pair of pants with zero inputs.
    have h1 : 1 ≤ Real.exp (2 * π) := Real.one_le_exp (by positivity)
    have hw₀ : w ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hge
      linarith
    have hw₁ : w ≠ 1 := by
      rintro rfl
      rw [norm_one] at hge
      linarith
    rw [← pairOfPantsPerturbation_single_inf]
    exact contMDiffAt_pairOfPantsPerturbation
      (forall_single inf (P := fun f => Periodic f 1) (fun _ => rfl) hH)
      (forall_single inf (P := fun f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f))
        contMDiff_const hHs) ⟨w, hw₀, hw₁⟩ x

/-! ### Capping an input of the pair of pants -/

variable {Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

omit [TopologicalSpace M] [ChartedSpace G M] in
/-- **The capped disc.** Plumb a negative plane into the input end `q` of a pair of pants with
Hamiltonians `Hb`, along a neck of length `L > 2`. The capped datum vanishes on the disc of radius
`exp (-2π(L - 1)) / 2` about the capped puncture `c_q`, the image under the plumbing map of the
pole disc of the plane. -/
theorem plumbedPerturbation_single_inf_eq_zero (hq : q ≠ inf) (hL : 2 < L) {w : ℂ}
    (hw : ‖w - q.endCenter‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2) (x : M) :
    plumbedPerturbation (Pi.single inf H) Hb q L w x = 0 := by
  rcases eq_or_ne w q.endCenter with rfl | hc
  · -- At the capped puncture itself the datum is that of the receiving pair of pants.
    rw [plumbedPerturbation_def, re_endCoord_endCenter, ite_eq_right (by linarith),
      pairOfPantsPerturbation_endCenter]
  · have hd : 0 < ‖w - q.endCenter‖ := norm_pos_iff.2 (sub_ne_zero.2 hc)
    have hlog : Real.log (‖w - q.endCenter‖ / (1 / 2)) ≤ -(2 * π * (L - 1)) := by
      rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ (by norm_num)]
      linarith
    have hre : L - 1 ≤ (q.endCoord w).re := by
      rw [re_endCoord, norm_div, norm_endScale hq, le_div_iff₀ (by positivity)]
      linarith
    -- The point corresponds to a point of the pole disc of the plane.
    have hexp : Real.exp (-(2 * π * (L - 1))) = Real.exp (2 * π) * Real.exp (-(2 * π * L)) := by
      rw [← Real.exp_add]
      ring_nf
    have hw' : ‖(w - q.endCenter) / q.plumbingFactor L‖ ≤ 2 * Real.exp (2 * π) := by
      rw [norm_div, norm_plumbingFactor, norm_endScale hq, div_le_iff₀ (by positivity)]
      rw [hexp] at hw
      linarith
    rw [plumbedPerturbation_def, ite_eq_left (by linarith), pairOfPantsPerturbation_single_inf,
      negativePlanePerturbation_eq_zero_of_norm_le hw', ContinuousLinearMap.zero_comp]

/-- **The capped datum is smooth.** For period-one Hamiltonians `Hb` of class `C^n` on `ℝ × M` and
neck length `L > 4`, the perturbation obtained by plumbing the negative plane with Hamiltonian
`Hb q` into the input end `q` of the pair of pants with Hamiltonians `Hb` is `C^n` at every point
of `ℂ × M` whose domain point is the capped puncture `c_q` or a point of `ℂ ∖ {0, 1}`: it is
smooth on the capped cylinder `ℂ ∖ {c_q'}`, where `q'` is the other input. -/
theorem contMDiffAt_plumbedPerturbation_single_inf {n : ℕ∞} (hq : q ≠ inf)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Hb r))) (hL : 4 < L) {w : ℂ}
    (hw : w = q.endCenter ∨ w ≠ 0 ∧ w ≠ 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => plumbedPerturbation (Pi.single inf (Hb q)) Hb q L p.1 p.2) (w, x) := by
  set ρ := Real.exp (-(2 * π * (L - 1))) / 2 with hρdef
  rcases lt_or_ge ‖w - q.endCenter‖ ρ with hlt | hge
  · -- On the open capped disc the datum vanishes.
    refine (contMDiffAt_const (c := (0 : ℂ →L[ℝ] ℝ))).congr_of_eventuallyEq ?_
    have h : ∀ᶠ p : ℂ × M in 𝓝 (w, x), ‖p.1 - q.endCenter‖ < ρ :=
      (continuous_fst.sub continuous_const).norm.continuousAt.eventually (gt_mem_nhds hlt)
    filter_upwards [h] with p hp
    exact plumbedPerturbation_single_inf_eq_zero hq (by linarith) hp.le p.2
  · -- Off it, the point lies in the plumbed four-punctured sphere.
    have hρ : 0 < ρ := by positivity
    have hc : w ≠ q.endCenter := fun h => by
      rw [h, sub_self, norm_zero] at hge
      linarith
    have h₁ : w ≠ q.plumbingMap L 1 := by
      rintro rfl
      rw [plumbingMap_apply, add_sub_cancel_left, mul_one, norm_plumbingFactor, norm_endScale hq,
        hρdef] at hge
      have := Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos] : -(2 * π * L) < -(2 * π * (L - 1)))
      linarith [Real.exp_pos (-(2 * π * L))]
    exact contMDiffAt_plumbedPerturbation hq
      (forall_single inf (P := fun f => Periodic f 1) (fun _ => rfl) (hHb q)) hHb
      (forall_single inf (P := fun f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f))
        contMDiff_const (hHbs q)) hHbs (by simp) hL ⟨hw.resolve_left hc, h₁⟩ x

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : ℝ → V → ℝ} {Hb : Puncture → ℝ → V → ℝ} {q : Puncture} {L : ℝ}

/-- **The integrated curvature of the negative plane.** Let `K` be the negative plane
perturbation of a period-one `C¹` Hamiltonian `H` with `|H| ≤ B`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`. Then for
every map `u` into the target, the integral of `|R_K(z, u(z))|` over the plane is at most `B`. -/
theorem lintegral_enorm_hamiltonianCurvature_negativePlanePerturbation_le (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal B := by
  have h := ω.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le
    (forall_single inf (P := fun f => Periodic f 1) (fun _ => rfl) hH)
    (forall_single inf (P := fun f => ContDiff ℝ 1 (uncurry f)) contDiff_const hHs)
    (abs_single_le inf hB) u
  rwa [pairOfPantsPerturbation_single_inf, Fintype.sum_eq_single inf fun r hr => by
    simp [Pi.single_eq_of_ne hr], Pi.single_eq_same] at h

omit [FiniteDimensional ℝ V] in
/-- The components of the negative plane perturbation in real coordinates are `C¹` jointly in the
domain point and the target point, on the whole plane. -/
private theorem contDiff_negativePlanePerturbation_apply (hH : Periodic H 1)
    (hHs : ContDiff ℝ 1 (uncurry H)) (v : ℂ) :
    ContDiff ℝ 1
      (uncurry fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x v) := by
  have hHs' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry H) := by
    have h := hHs.contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have h : ContMDiff 𝓘(ℝ, ℂ × V) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × V => negativePlanePerturbation H p.1 p.2) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiff_negativePlanePerturbation hH hHs'
  exact (h.contDiff.comp ((Complex.equivRealProdCLM.symm.contDiff.comp contDiff_fst).prodMk
    contDiff_snd)).clm_apply contDiff_const

/-- **The energy identity on discs of the negative plane.** Let `K` be the negative plane
perturbation of a period-one `C¹` Hamiltonian `H`, with components `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let `u` be a `C¹` map. For
`R ≥ 1`, over the disc `‖w‖ ≤ 2 exp (2πR)`, bounded by the circle `s = -R` of the end, the Floer
energy of `u` is its symplectic area, minus `β(R - 1)` times the integral of `H(t)` along the
boundary circle, minus the integrated curvature:

`∫_{D_R} E = ∫_{D_R} u^*ω - β(R - 1) ∫₀¹ H(t, u(φ(-R + i t))) dt - ∫_{D_R} R_K(u)`.

Here `φ` is the end lift `z ↦ 2 exp (-2πz)` and `β = smoothTransition`, so `β(R - 1) = 1` for
`R ≥ 2`. -/
theorem integral_floerEnergyDensity_negativePlanePerturbation_closedBall (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u)
    {R : ℝ} (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * R)),
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1,
          H t (u (Complex.equivRealProdCLM (inf.cylindricalEndLift (-R + t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * R)),
          ω.hamiltonianCurvature
            (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  -- On the truncation, this is the energy identity of the pair of pants with zero inputs.
  have hT := ω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
    (forall_single inf (P := fun f => Periodic f 1) (fun _ => rfl) hH)
    (forall_single inf (P := fun f => ContDiff ℝ 1 (uncurry f)) contDiff_const hHs)
    hu.contDiffOn hR
  rw [pairOfPantsPerturbation_single_inf, Fintype.sum_eq_single inf fun r hr => by
    simp [Pi.single_eq_of_ne hr]] at hT
  simp only [Pi.single_eq_same, endSign_inf, neg_one_mul, Complex.ofReal_neg] at hT
  set D := Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall (0 : ℂ) (2 * Real.exp (2 * π * R))
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  -- The disc is the truncation of the pair of pants together with small discs about `0` and
  -- `1`, which lie in the pole disc where the perturbation vanishes.
  have hTD : T ⊆ D := fun z hz => by
    rw [mem_preimage, truncation_eq] at hz
    exact hz.2
  have hDT {z : ℝ × ℝ} (hz : z ∈ D \ T) :
      ‖Complex.equivRealProdCLM.symm z‖ < 2 * Real.exp (2 * π) :=
    mem_ball_zero_iff.1 (closedBall_sdiff_truncation_subset_ball (by linarith) hz)
  -- The three integrands are continuous, hence integrable on the compact disc.
  have hKs := contDiff_negativePlanePerturbation_apply hH hHs 1
  have hKt := contDiff_negativePlanePerturbation_apply hH hHs Complex.I
  have hD : IsCompact D :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _)
  have hDTm : MeasurableSet (D \ T) :=
    hD.isClosed.measurableSet.diff (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_truncation R)).isClosed.measurableSet
  have hint (f : ℝ × ℝ → ℝ) (hf : Continuous f) : IntegrableOn f D :=
    hf.continuousOn.integrableOn_compact hD
  have hdu := hu.continuous_fderiv one_ne_zero
  have hE := hint _ (continuousOn_univ.1 (ω.continuousOn_floerEnergyDensity isOpen_univ
    hu.contDiffOn (by simpa using hKs.contDiffOn) (by simpa using hKt.contDiffOn)))
  have harea := hint (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal)
    (fderiv ℝ u z stdComplexLineImag)) (ω.continuous_apply_comp (hdu.clm_apply continuous_const)
      (hdu.clm_apply continuous_const))
  have hcurv := hint _ (continuousOn_univ.1 (ω.continuousOn_hamiltonianCurvature_comp isOpen_univ
    hu.continuous.continuousOn (by simpa using hKs.contDiffOn) (by simpa using hKt.contDiffOn)))
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f D) :
      ∫ z in D, f z = (∫ z in T, f z) + ∫ z in D \ T, f z := by
    conv_lhs => rw [← union_sdiff_cancel hTD]
    exact setIntegral_union disjoint_sdiff_right hDTm (hf.mono_set hTD) (hf.mono_set sdiff_subset)
  -- Off the truncation the energy is the area and the curvature vanishes.
  have hED : ∫ z in D \ T, ω.floerEnergyDensity
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in D \ T, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) := by
    refine setIntegral_congr_fun hDTm fun z hz => ?_
    have hK := (eventually_negativePlanePerturbation_eq_zero (H := H) (hDT hz)).self_of_nhds
    simp [floerEnergyDensity_def, perturbedFDeriv_apply_stdComplexLineReal,
      perturbedFDeriv_apply_stdComplexLineImag, hK]
  have hRD : ∫ z in D \ T, ω.hamiltonianCurvature
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
    have hK := eventually_negativePlanePerturbation_eq_zero (H := H) (hDT hz)
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0)
      (hK.mono fun z' hz' ↦ funext fun y ↦ by simp [hz'])
      (hK.mono fun z' hz' ↦ funext fun y ↦ by simp [hz']), hamiltonianCurvature_zero_left]
    simp
  rw [hsplit _ hE, hsplit _ harea, hsplit _ hcurv, hED, hRD, hT]
  ring

/-- **The energy bound on discs of the negative plane.** If `|H| ≤ B`, then for every `R ≥ 1` the
Floer energy over the disc `‖w‖ ≤ 2 exp (2πR)` differs from the symplectic area minus the
Hamiltonian boundary term by at most `B`, uniformly in `R`. -/
theorem abs_integral_floerEnergyDensity_negativePlanePerturbation_closedBall_sub_le
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) {R : ℝ} (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * R)),
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1,
          H t (u (Complex.equivRealProdCLM (inf.cylindricalEndLift (-R + t * Complex.I)))))| ≤
      B := by
  have hsub (a b c : ℝ) : a - b - c - a + b = -c := by ring
  rw [integral_floerEnergyDensity_negativePlanePerturbation_closedBall ω hH hHs hu hR, hsub,
    abs_neg]
  have hB₀ : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  rw [← ENNReal.ofReal_le_ofReal_iff hB₀, ← Real.enorm_eq_ofReal_abs]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_negativePlanePerturbation_le ω hH hHs hB u))

/-- **The integrated curvature of the capping family is bounded uniformly in the neck length.**
Plumb the negative plane with Hamiltonian `Hb q` into the input end `q` of the pair of pants with
period-one `C¹` Hamiltonians `Hb`, along a neck of length `L > 4`. If `|Hb r| ≤ Bb r`, then for
every map `u` into the target the integral of `|R_K(z, u(z))|` over the plane is at most
`Bb q + ∑ r, Bb r`, which does not depend on `L`. -/
theorem lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_single_inf_le
    (ω : SymplecticForm V) (hq : q ≠ inf) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L) {Bb : Puncture → ℝ}
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb q)) Hb q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb q)) Hb q L
          (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal (Bb q) + ∑ r, ENNReal.ofReal (Bb r) := by
  have h := ω.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le hq
    (forall_single inf (P := fun f => Periodic f 1) (fun _ => rfl) (hHb q)) hHb
    (forall_single inf (P := fun f => ContDiff ℝ 1 (uncurry f)) contDiff_const (hHbs q)) hHbs
    (by simp) hL (abs_single_le inf (hBb q)) hBb u
  rwa [Fintype.sum_eq_single inf fun r hr => by simp [Pi.single_eq_of_ne hr],
    Pi.single_eq_same] at h

end TauCeti.SymplecticForm
