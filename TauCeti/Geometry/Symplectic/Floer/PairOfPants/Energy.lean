/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Curvature and energy of the pair-of-pants perturbation on its ends

The energy of a solution of the perturbed Cauchy–Riemann equation `(du - X_K)^{0,1} = 0` is its
symplectic area, plus the boundary integral of `K(u)`, minus the integral of the curvature
`R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}` (`TauCeti.SymplecticForm.integral_floerEnergyDensity`).
An energy bound for the pair-of-pants product therefore needs a bound on `∫ sup_x |R_K|` which
does not depend on how far out the ends are cut off.

This file computes the curvature of the perturbation `TauCeti.Floer.pairOfPantsPerturbation` in
the end coordinates `z = (s, t)` of each end `q`, for Hamiltonians on a symplectic vector space.
There the perturbation is the continuation datum `β(±s - 1) H_q(t) dt`, where `β` is the smooth
transition function, so its curvature is `±β'(±s - 1) H_q(t)`. It is supported in the collar
`1 ≤ ±s ≤ 2`, and since `β' ≥ 0` has total integral `1`, the integrated curvature over any part of
the end is bounded by `∫ h`, for any bound `|H_q(t, x)| ≤ h(t)`, whatever the length of that part.
The perturbation vanishes off the three ends
(`TauCeti.Floer.exists_cylindricalEndLift_of_pairOfPantsPerturbation_ne_zero`), so the collars of
the three ends carry all of its curvature.

The components `K_s` and `K_t` of the perturbation in end coordinates are
`TauCeti.Floer.pairOfPantsEndComponent H q 1` and `TauCeti.Floer.pairOfPantsEndComponent H q I`.

## Main results

* `TauCeti.SymplecticForm.hamiltonianCurvature_pairOfPantsEndComponent`: the curvature on the end
  is `±β'(±s - 1) H_q(t)`.
* `TauCeti.SymplecticForm.hamiltonianCurvature_pairOfPantsEndComponent_eq_zero`: it vanishes
  outside the collar `1 ≤ ±s ≤ 2`.
* `TauCeti.SymplecticForm.integral_abs_hamiltonianCurvature_pairOfPantsEndComponent_le`: the
  integrated curvature along any map over a rectangle `[a₁, b₁] × [a₂, b₂]` in the end is at most
  `∫_{a₂}^{b₂} h`, uniformly in `a₁` and `b₁`.
* `TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_pairOfPantsEndComponent_sub_le`:
  consequently the Floer energy over such a rectangle differs from the symplectic area plus the
  Hamiltonian boundary terms `∫ β(±s - 1) H_q(t, u(s, t)) dt` at its two ends by at most `∫ h`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on perturbation data for the pair-of-pants product and its energy estimate.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
-/

public noncomputable section

open Filter Function MeasureTheory Set Topology Real Complex
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {q : Puncture}

/-- **The curvature on an end.** On the part `±s > 0` of the end `q`, the curvature of the
pair-of-pants perturbation in end coordinates is `±β'(±s - 1) H_q(t)`. -/
theorem hamiltonianCurvature_pairOfPantsEndComponent (ω : SymplecticForm V)
    (hH : Periodic (H q) 1) {z : ℝ × ℝ} (hz : 0 < q.endSign * z.1) {x : V}
    (hHx : DifferentiableAt ℝ (fun t ↦ H q t x) z.2) :
    ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1) (pairOfPantsEndComponent H q I) z x =
      q.endSign * deriv smoothTransition (q.endSign * z.1 - 1) * H q z.2 x := by
  obtain ⟨hs, ht⟩ := eventuallyEq_pairOfPantsEndComponent hH hz
  have hβ : HasDerivAt (fun s ↦ smoothTransition (q.endSign * s - 1))
      (deriv smoothTransition (q.endSign * z.1 - 1) * q.endSign) z.1 :=
    (((hasDerivAt_id z.1).const_mul q.endSign).sub_const 1).smoothTransition.congr_deriv
      (by simp)
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq hs ht,
    ω.hamiltonianCurvature_continuation hβ.differentiableAt hHx, hβ.deriv]
  ring

/-- **The curvature is supported in the collar.** On the parts `0 < ±s < 1` and `±s > 2` of the
end `q`, the curvature of the pair-of-pants perturbation in end coordinates vanishes. -/
theorem hamiltonianCurvature_pairOfPantsEndComponent_eq_zero (ω : SymplecticForm V)
    (hH : Periodic (H q) 1) {z : ℝ × ℝ} (hz : 0 < q.endSign * z.1)
    (hz' : q.endSign * z.1 < 1 ∨ 2 < q.endSign * z.1) (x : V) :
    ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1) (pairOfPantsEndComponent H q I) z x =
      0 := by
  obtain ⟨hs, ht⟩ := eventuallyEq_pairOfPantsEndComponent hH hz
  -- Near `z`, the cutoff `β(±s - 1)` is constant, equal to `0` or to `1`.
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ᶠ w in 𝓝 z, smoothTransition (q.endSign * w.1 - 1) = c := by
    have hcont : Continuous fun w : ℝ × ℝ ↦ q.endSign * w.1 :=
      continuous_const.mul continuous_fst
    rcases hz' with h | h
    · exact ⟨0, eventually_of_mem (hcont.isOpen_preimage _ isOpen_Iio |>.mem_nhds h) fun w hw ↦
        smoothTransition.zero_of_nonpos (by simp only [mem_preimage, mem_Iio] at hw; linarith)⟩
    · exact ⟨1, eventually_of_mem (hcont.isOpen_preimage _ isOpen_Ioi |>.mem_nhds h) fun w hw ↦
        smoothTransition.one_of_one_le (by simp only [mem_preimage, mem_Ioi] at hw; linarith)⟩
  have ht' : pairOfPantsEndComponent H q I =ᶠ[𝓝 z] fun w ↦ (fun t x ↦ c * H q t x) w.2 := by
    filter_upwards [ht, hc] with w hw hcw
    rw [hw, hcw]
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq hs ht']
  exact ω.hamiltonianCurvature_cylindrical (fun t x ↦ c * H q t x) z x

/-- The derivative `s ↦ β'(±s - 1)` of the cutoff of an end has total integral one. -/
private theorem integral_deriv_smoothTransition_endSign_mul_sub_one (q : Puncture) :
    ∫ s, deriv smoothTransition (q.endSign * s - 1) = 1 := by
  rw [Measure.integral_comp_mul_left (fun y ↦ deriv smoothTransition (y - 1)),
    integral_sub_right_eq_self (deriv smoothTransition), smoothTransition.integral_deriv,
    abs_inv, abs_endSign, inv_one, one_smul]

/-- **Uniform curvature bound on an end.** Let `h` bound the Hamiltonian `H_q` of the end `q` on
`[a₂, b₂]`, uniformly on the target. Over any rectangle `[a₁, b₁] × [a₂, b₂]` in the part
`±s > 0` of the end, the integrated curvature of the pair-of-pants perturbation along any map `u`
is at most `∫_{a₂}^{b₂} h`, independently of `a₁` and `b₁`. -/
theorem integral_abs_hamiltonianCurvature_pairOfPantsEndComponent_le (ω : SymplecticForm V)
    (hH : Periodic (H q) 1) {a b : ℝ × ℝ}
    (hHd : ∀ t ∈ Icc a.2 b.2, ∀ x, DifferentiableAt ℝ (fun t ↦ H q t x) t) (u : ℝ × ℝ → V)
    {h : ℝ → ℝ} (ha : 0 < q.endSign * a.1) (hb : 0 < q.endSign * b.1)
    (hh : ∀ t ∈ Icc a.2 b.2, ∀ x, |H q t x| ≤ h t)
    (hhi : IntegrableOn h (Icc a.2 b.2)) :
    ∫ z in Icc a b, |ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
        (pairOfPantsEndComponent H q I) z (u z)| ≤
      ∫ t in Icc a.2 b.2, h t := by
  set f : ℝ × ℝ → ℝ := fun z ↦ |ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
    (pairOfPantsEndComponent H q I) z (u z)|
  set β' : ℝ → ℝ := fun s ↦ deriv smoothTransition (q.endSign * s - 1)
  have hβ'0 (s : ℝ) : 0 ≤ β' s := smoothTransition.monotone.deriv_nonneg
  have hh0 : 0 ≤ ∫ t in Icc a.2 b.2, h t :=
    setIntegral_nonneg measurableSet_Icc fun t ht ↦ (abs_nonneg _).trans (hh t ht 0)
  by_cases hfi : IntegrableOn f (Icc a b)
  swap
  · rw [integral_undef hfi]
    exact hh0
  -- The pointwise bound `|R_K(z, u z)| ≤ β'(±s - 1) h(t)`.
  have hpos {z : ℝ × ℝ} (hz : z ∈ Icc a b) : 0 < q.endSign * z.1 := by
    rcases le_total 0 q.endSign with hq | hq
    · nlinarith [hz.1.1, mul_le_mul_of_nonneg_left hz.1.1 hq]
    · nlinarith [hz.2.1, mul_le_mul_of_nonpos_left hz.2.1 hq]
  have hfg (z : ℝ × ℝ) (hz : z ∈ Icc a b) : f z ≤ β' z.1 * h z.2 := by
    simp only [f, β', ω.hamiltonianCurvature_pairOfPantsEndComponent hH (hpos hz)
        (hHd z.2 ⟨hz.1.2, hz.2.2⟩ _),
      abs_mul, abs_endSign, one_mul, abs_of_nonneg (hβ'0 z.1)]
    exact mul_le_mul_of_nonneg_left (hh z.2 ⟨hz.1.2, hz.2.2⟩ (u z)) (hβ'0 z.1)
  -- The bound integrates to `(∫ β') (∫ h) ≤ ∫ h` over the rectangle.
  have hβ'i : Integrable β' :=
    (smoothTransition.integrable_deriv.comp_sub_right 1).comp_mul_left'
      (show q.endSign ≠ 0 by cases q <;> norm_num)
  have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume := Measure.volume_eq_prod ℝ ℝ
  have hgi : IntegrableOn (fun z : ℝ × ℝ ↦ β' z.1 * h z.2) (Icc a b) := by
    rw [IntegrableOn, Icc_prod_eq, hvol, ← Measure.prod_restrict]
    exact (hβ'i.integrableOn (s := Icc a.1 b.1)).mul_prod hhi
  calc ∫ z in Icc a b, f z ≤ ∫ z in Icc a b, β' z.1 * h z.2 :=
        setIntegral_mono_on hfi hgi measurableSet_Icc hfg
    _ = (∫ s in Icc a.1 b.1, β' s) * ∫ t in Icc a.2 b.2, h t := by
        rw [Icc_prod_eq, hvol]
        exact setIntegral_prod_mul β' h _ _
    _ ≤ 1 * ∫ t in Icc a.2 b.2, h t := by
        refine mul_le_mul_of_nonneg_right ?_ hh0
        rw [← integral_deriv_smoothTransition_endSign_mul_sub_one q]
        exact setIntegral_le_integral hβ'i (.of_forall hβ'0)
    _ = ∫ t in Icc a.2 b.2, h t := one_mul _

/-- **Uniform energy estimate on an end.** Let `H_q` be `C¹` and let `h` bound it on `[a₂, b₂]`,
uniformly on the target. For a map `u` which is `C¹` near a rectangle `[a₁, b₁] × [a₂, b₂]` in the
part `±s > 0` of the end `q`, the Floer energy of `u` over the rectangle for the pair-of-pants
perturbation differs from its symplectic area plus the Hamiltonian boundary terms
`∫ β(±s - 1) H_q(t, u(s, t)) dt` at `s = b₁` and `s = a₁` by at most `∫_{a₂}^{b₂} h`,
independently of `a₁` and `b₁`. -/
theorem abs_integral_floerEnergyDensity_pairOfPantsEndComponent_sub_le (ω : SymplecticForm V)
    (hH : Periodic (H q) 1) (hHs : ContDiff ℝ 1 (uncurry (H q))) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hUq : U ⊆ {z | 0 < q.endSign * z.1}) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u U) {a b : ℝ × ℝ} (hab : a ≤ b) (habU : Icc a b ⊆ U) {h : ℝ → ℝ}
    (hh : ∀ t ∈ Icc a.2 b.2, ∀ x, |H q t x| ≤ h t) (hhi : IntegrableOn h (Icc a.2 b.2)) :
    |(∫ z in Icc a b,
        ω.floerEnergyDensity (pairOfPantsEndComponent H q 1) (pairOfPantsEndComponent H q I) u z) -
      ((∫ z in Icc a b, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        ((∫ t in a.2..b.2, smoothTransition (q.endSign * b.1 - 1) * H q t (u (b.1, t))) -
          ∫ t in a.2..b.2, smoothTransition (q.endSign * a.1 - 1) * H q t (u (a.1, t))))| ≤
      ∫ t in Icc a.2 b.2, h t := by
  have hmem {z : ℝ × ℝ} (hz : z ∈ Icc a b) : 0 < q.endSign * z.1 := hUq (habU hz)
  have ha : 0 < q.endSign * a.1 := hmem ⟨le_rfl, hab⟩
  have hb : 0 < q.endSign * b.1 := hmem ⟨hab, le_rfl⟩
  -- On `U`, the components are those of the smooth continuation datum `β(±s - 1) H_q(t) dt`.
  have hKs : ContDiffOn ℝ 1 (uncurry (pairOfPantsEndComponent H q 1)) (U ×ˢ univ) :=
    contDiffOn_const.congr fun p hp ↦ pairOfPantsEndComponent_one_of_pos hH (hUq hp.1) p.2
  have hKt : ContDiffOn ℝ 1 (uncurry (pairOfPantsEndComponent H q I)) (U ×ˢ univ) := by
    refine ContDiffOn.congr ?_ fun p hp ↦ pairOfPantsEndComponent_I_of_pos hH (hUq hp.1) p.2
    exact ((smoothTransition.contDiff.comp ((contDiff_const.mul (contDiff_fst.comp
      contDiff_fst)).sub contDiff_const)).mul (hHs.comp ((contDiff_snd.comp contDiff_fst).prodMk
        contDiff_snd))).contDiffOn
  rw [ω.integral_floerEnergyDensity hU hu hKs hKt hab habU]
  -- The `ds` boundary terms vanish and the `dt` boundary terms are the Hamiltonian terms.
  have hs₁ : ∫ s in a.1..b.1, pairOfPantsEndComponent H q 1 (s, a.2) (u (s, a.2)) = 0 :=
    intervalIntegral.integral_zero_ae (.of_forall fun s hs ↦ by
      rw [uIoc_of_le hab.1] at hs
      exact pairOfPantsEndComponent_one_of_pos hH (hmem (z := (s, a.2))
        ⟨⟨hs.1.le, le_rfl⟩, ⟨hs.2, hab.2⟩⟩) _)
  have hs₂ : ∫ s in a.1..b.1, pairOfPantsEndComponent H q 1 (s, b.2) (u (s, b.2)) = 0 :=
    intervalIntegral.integral_zero_ae (.of_forall fun s hs ↦ by
      rw [uIoc_of_le hab.1] at hs
      exact pairOfPantsEndComponent_one_of_pos hH (hmem (z := (s, b.2))
        ⟨⟨hs.1.le, hab.2⟩, ⟨hs.2, le_rfl⟩⟩) _)
  have ht₁ : ∫ t in a.2..b.2, pairOfPantsEndComponent H q I (b.1, t) (u (b.1, t)) =
      ∫ t in a.2..b.2, smoothTransition (q.endSign * b.1 - 1) * H q t (u (b.1, t)) :=
    intervalIntegral.integral_congr fun t _ ↦
      pairOfPantsEndComponent_I_of_pos (z := (b.1, t)) hH hb _
  have ht₂ : ∫ t in a.2..b.2, pairOfPantsEndComponent H q I (a.1, t) (u (a.1, t)) =
      ∫ t in a.2..b.2, smoothTransition (q.endSign * a.1 - 1) * H q t (u (a.1, t)) :=
    intervalIntegral.integral_congr fun t _ ↦
      pairOfPantsEndComponent_I_of_pos (z := (a.1, t)) hH ha _
  rw [hs₁, hs₂, ht₁, ht₂, zero_add, sub_zero, sub_sub_cancel_left, abs_neg]
  have hHd (t : ℝ) (_ : t ∈ Icc a.2 b.2) (x : V) : DifferentiableAt ℝ (fun t ↦ H q t x) t :=
    (hHs.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero t
  exact abs_integral_le_integral_abs.trans
    (ω.integral_abs_hamiltonianCurvature_pairOfPantsEndComponent_le hH hHd u ha hb hh hhi)

end SymplecticForm

end TauCeti
