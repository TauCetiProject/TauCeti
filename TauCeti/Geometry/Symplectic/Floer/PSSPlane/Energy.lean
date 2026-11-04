/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.PSSPlane.Basic
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Curvature and energy of the PSS plane perturbations

The planes of the Piunikhin–Salamon–Schwarz maps carry the perturbation
`TauCeti.Floer.pssPlanePerturbation`, which in the end coordinates `z = (s, t)` of the plane is
the continuation datum `K = β(σ s - 1) H(t) dt` on the whole cylinder
(`TauCeti.Floer.pssPlaneEndComponent_one`, `TauCeti.Floer.pssPlaneEndComponent_I`). Here `σ = ±1`
is the sign of the plane and `β` is the smooth transition function. This file records the
energy estimates for these data, for Hamiltonians on a symplectic vector space `(V, ω)`.

The curvature of `K` is `σ β'(σ s - 1) H(t)`. Since `β' ≥ 0` has total integral `1`, if
`|H(t, x)| ≤ h(t)` then for every map `u`, measurable or not, the integrated curvature over the
whole cylinder satisfies

`∫_{ℝ × [a, b]} |R_K(z, u(z))| dz ≤ ∫_a^b h`.

In particular it is bounded independently of the map, as compactness for the PSS moduli spaces
requires. For a map `u` which is `C²` and one-periodic in `t`, the energy identity
`TauCeti.SymplecticForm.integral_floerEnergyDensity_continuation_eq_hamiltonianAction_sub` gives
the Floer energy over `[a, b] × [0, 1]` as a difference of actions minus the integrated curvature.
Near the pole the perturbation vanishes and the action reduces to the symplectic area of the loop,
while far out on the end it is the Hamiltonian action for `H`. Hence on the positive plane

`E(u; [a, b] × [0, 1]) = A_H(u(b, ·)) - a(u(a, ·)) - ∫ R_K(u)` for `a ≤ 1` and `b ≥ 2`,

and on the negative plane

`E(u; [a, b] × [0, 1]) = a(u(b, ·)) - A_H(u(a, ·)) - ∫ R_K(u)` for `a ≤ -2` and `b ≥ -1`,

where `a(x)` is the symplectic area of the loop `x` (`TauCeti.SymplecticForm.loopArea`) and `A_H`
the Hamiltonian action (`TauCeti.SymplecticForm.hamiltonianAction`). For a map defined across
the pole the loop at the pole side shrinks to a point, so its area tends to zero; passing to that
limit, and to the asymptotic orbit `x` at the end, would give the identities
`E = A_H(x) - ∫ R_K` and `E = -A_H(x) - ∫ R_K` for the two planes. These limits are not taken
here.

## Main results

* `TauCeti.SymplecticForm.hamiltonianCurvature_pssPlaneEndComponent`: the curvature in end
  coordinates is `σ β'(σ s - 1) H(t)`.
* `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_pssPlaneEndComponent_le`: the
  integrated curvature over the whole cylinder `ℝ × [a, b]` is at most `∫_a^b h`.
* `TauCeti.SymplecticForm.integral_floerEnergyDensity_pssPlaneEndComponent`: the energy identity
  on `[a, b] × [0, 1]`, in terms of actions.
* `TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_pssPlaneEndComponent_sub_le`: the
  energy differs from the change of action by at most `∫_0^1 h`, uniformly in `a` and `b`.
* `TauCeti.SymplecticForm.integral_floerEnergyDensity_pssPlaneEndComponent_pos` and
  `TauCeti.SymplecticForm.integral_floerEnergyDensity_pssPlaneEndComponent_neg`: the identities
  between the pole disc and the end of the positive and negative planes.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
-/

public noncomputable section

open Function MeasureTheory Set Topology Real

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {P : PSSPlane} {H : ℝ → V → ℝ}

/-- **The curvature of the plane perturbation.** In end coordinates, the curvature of the
perturbation of the plane `P` is `σ β'(σ s - 1) H(t)`, where `σ` is the sign of the plane. -/
theorem hamiltonianCurvature_pssPlaneEndComponent (ω : SymplecticForm V) (hH : Periodic H 1)
    {z : ℝ × ℝ} {x : V} (hHx : DifferentiableAt ℝ (fun t ↦ H t x) z.2) :
    ω.hamiltonianCurvature (pssPlaneEndComponent P H 1) (pssPlaneEndComponent P H Complex.I) z x =
      P.sign * deriv smoothTransition (P.sign * z.1 - 1) * H z.2 x := by
  have hβ : HasDerivAt (fun s ↦ smoothTransition (P.sign * s - 1))
      (deriv smoothTransition (P.sign * z.1 - 1) * P.sign) z.1 :=
    (((hasDerivAt_id z.1).const_mul P.sign).sub_const 1).smoothTransition.congr_deriv
      (by simp)
  rw [pssPlaneEndComponent_one, pssPlaneEndComponent_I hH,
    ω.hamiltonianCurvature_continuation (β := fun s ↦ smoothTransition (P.sign * s - 1))
      hβ.differentiableAt hHx, hβ.deriv]
  ring

/-- **Uniform curvature bound on the plane.** Let `h` bound the Hamiltonian `H` on `[a, b]`,
uniformly on the target. For every map `u` from the cylinder to the target, measurable or not, the
integrated curvature of the plane perturbation along `u` over the whole cylinder `ℝ × [a, b]` is
at most `∫_a^b h`. -/
theorem lintegral_enorm_hamiltonianCurvature_pssPlaneEndComponent_le (ω : SymplecticForm V)
    (hH : Periodic H 1) {a b : ℝ} (hHd : ∀ t ∈ Icc a b, ∀ x, DifferentiableAt ℝ (fun t ↦ H t x) t)
    (u : ℝ × ℝ → V) {h : ℝ → ℝ} (hh : ∀ t ∈ Icc a b, ∀ x, |H t x| ≤ h t)
    (hhi : IntegrableOn h (Icc a b)) :
    ∫⁻ z in univ ×ˢ Icc a b, ‖ω.hamiltonianCurvature (pssPlaneEndComponent P H 1)
        (pssPlaneEndComponent P H Complex.I) z (u z)‖ₑ ≤ ENNReal.ofReal (∫ t in Icc a b, h t) := by
  set β' : ℝ → ℝ := fun s ↦ deriv smoothTransition (P.sign * s - 1)
  have hβ'0 (s : ℝ) : 0 ≤ β' s := smoothTransition.monotone.deriv_nonneg
  have hβ'm : Measurable β' :=
    ((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).measurable.comp
      (by fun_prop)
  calc _ ≤ ∫⁻ z in univ ×ˢ Icc a b, ENNReal.ofReal (β' z.1) * ENNReal.ofReal (h z.2) := by
        refine setLIntegral_mono' (MeasurableSet.univ.prod measurableSet_Icc) fun z hz ↦ ?_
        -- Pointwise, `|R_K(z, u z)| = β'(σ s - 1) |H(t, u z)| ≤ β'(σ s - 1) h(t)`.
        rw [ω.hamiltonianCurvature_pssPlaneEndComponent hH (hHd z.2 hz.2 _),
          Real.enorm_eq_ofReal_abs, abs_mul, abs_mul, PSSPlane.abs_sign, one_mul,
          abs_of_nonneg (hβ'0 _), ← ENNReal.ofReal_mul (hβ'0 _)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hh _ hz.2 _) (hβ'0 _))
    _ = (∫⁻ s, ENNReal.ofReal (β' s)) * ∫⁻ t in Icc a b, ENNReal.ofReal (h t) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
        exact lintegral_prod_mul hβ'm.ennreal_ofReal.aemeasurable
          hhi.aemeasurable.ennreal_ofReal
    _ = ENNReal.ofReal (∫ t in Icc a b, h t) := by
        rw [smoothTransition.lintegral_ofReal_deriv_mul_sub P.sign_ne_zero, P.abs_sign, inv_one,
          ENNReal.ofReal_one, one_mul,
          ofReal_integral_eq_lintegral_ofReal hhi (ae_restrict_of_forall_mem measurableSet_Icc
            fun t ht ↦ (abs_nonneg _).trans (hh t ht 0))]

variable {u : ℝ × ℝ → V} {U : Set (ℝ × ℝ)} {a b : ℝ}

/-- **The energy identity on the plane.** Let `H` be `C¹` of period one, and let `u` be `C²` on an
open neighbourhood `U` of `[a, b] × [0, 1]` in end coordinates, with `u(s, 1) = u(s, 0)` for
`s ∈ [a, b]`. Then the Floer energy of `u` over the rectangle for the plane perturbation is the
action of the loop at `s = b` for the Hamiltonian `β(σ b - 1) H`, minus that of the loop at `s = a`
for `β(σ a - 1) H`, minus the integrated curvature. -/
theorem integral_floerEnergyDensity_pssPlaneEndComponent (ω : SymplecticForm V) (hH : Periodic H 1)
    (hHs : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (pssPlaneEndComponent P H 1)
        (pssPlaneEndComponent P H Complex.I) u z =
      ω.hamiltonianAction (fun t x ↦ smoothTransition (P.sign * b - 1) * H t x)
          (fun t ↦ u (b, t)) -
        ω.hamiltonianAction (fun t x ↦ smoothTransition (P.sign * a - 1) * H t x)
          (fun t ↦ u (a, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature (pssPlaneEndComponent P H 1)
          (pssPlaneEndComponent P H Complex.I) z (u z) := by
  rw [pssPlaneEndComponent_one, pssPlaneEndComponent_I hH]
  exact ω.integral_floerEnergyDensity_continuation_eq_hamiltonianAction_sub
    (β := fun s ↦ smoothTransition (P.sign * s - 1))
    (smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
    hHs hU hu hab hRU hper

/-- **Uniform energy estimate on the plane.** Under the hypotheses of
`TauCeti.SymplecticForm.integral_floerEnergyDensity_pssPlaneEndComponent`, if `h` bounds `H` on
`[0, 1]` uniformly on the target, then the Floer energy of `u` over `[a, b] × [0, 1]` differs from
the change of action by at most `∫_0^1 h`, independently of `a` and `b`. -/
theorem abs_integral_floerEnergyDensity_pssPlaneEndComponent_sub_le (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    {h : ℝ → ℝ} (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, |H t x| ≤ h t)
    (hhi : IntegrableOn h (Icc 0 1)) :
    |(∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (pssPlaneEndComponent P H 1)
        (pssPlaneEndComponent P H Complex.I) u z) -
      (ω.hamiltonianAction (fun t x ↦ smoothTransition (P.sign * b - 1) * H t x)
          (fun t ↦ u (b, t)) -
        ω.hamiltonianAction (fun t x ↦ smoothTransition (P.sign * a - 1) * H t x)
          (fun t ↦ u (a, t)))| ≤
      ∫ t in Icc 0 1, h t := by
  rw [ω.integral_floerEnergyDensity_pssPlaneEndComponent hH hHs hU hu hab hRU hper,
    sub_sub_cancel_left, abs_neg]
  have hHd (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) (x : V) : DifferentiableAt ℝ (fun t ↦ H t x) t :=
    (hHs.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero t
  have hh0 : 0 ≤ ∫ t in Icc (0 : ℝ) 1, h t :=
    setIntegral_nonneg measurableSet_Icc fun t ht ↦ (abs_nonneg _).trans (hh t ht 0)
  -- The rectangle lies in the cylinder `ℝ × [0, 1]`, over which the curvature is bounded.
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal hh0 ?_)
  refine (lintegral_mono_set (prod_mono (subset_univ _) le_rfl)).trans ?_
  simp_rw [ofReal_norm]
  exact ω.lintegral_enorm_hamiltonianCurvature_pssPlaneEndComponent_le hH hHd u hh hhi

/-- **The energy identity on the positive plane.** Between the pole disc `s ≤ 1`, where the
perturbation vanishes, and the end `s ≥ 2`, where it is `H(t) dt`, the Floer energy of `u` over
`[a, b] × [0, 1]` is the Hamiltonian action of the loop at `s = b`, minus the symplectic area of
the loop at `s = a`, minus the integrated curvature. -/
theorem integral_floerEnergyDensity_pssPlaneEndComponent_pos (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (ha : a ≤ 1) (hb : 2 ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (pssPlaneEndComponent .pos H 1)
        (pssPlaneEndComponent .pos H Complex.I) u z =
      ω.hamiltonianAction H (fun t ↦ u (b, t)) - ω.loopArea (fun t ↦ u (a, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature (pssPlaneEndComponent .pos H 1)
          (pssPlaneEndComponent .pos H Complex.I) z (u z) := by
  rw [ω.integral_floerEnergyDensity_pssPlaneEndComponent hH hHs hU hu (by linarith) hRU hper,
    PSSPlane.sign_pos, one_mul, one_mul, smoothTransition.one_of_one_le (by linarith),
    smoothTransition.zero_of_nonpos (by linarith)]
  simp [hamiltonianAction_def]

/-- **The energy identity on the negative plane.** Between the end `s ≤ -2`, where the
perturbation is `H(t) dt`, and the pole disc `s ≥ -1`, where it vanishes, the Floer energy of `u`
over `[a, b] × [0, 1]` is the symplectic area of the loop at `s = b`, minus the Hamiltonian action
of the loop at `s = a`, minus the integrated curvature. -/
theorem integral_floerEnergyDensity_pssPlaneEndComponent_neg (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (ha : a ≤ -2) (hb : -1 ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (pssPlaneEndComponent .neg H 1)
        (pssPlaneEndComponent .neg H Complex.I) u z =
      ω.loopArea (fun t ↦ u (b, t)) - ω.hamiltonianAction H (fun t ↦ u (a, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature (pssPlaneEndComponent .neg H 1)
          (pssPlaneEndComponent .neg H Complex.I) z (u z) := by
  rw [ω.integral_floerEnergyDensity_pssPlaneEndComponent hH hHs hU hu (by linarith) hRU hper,
    PSSPlane.sign_neg, smoothTransition.zero_of_nonpos (by linarith),
    smoothTransition.one_of_one_le (by linarith)]
  simp [hamiltonianAction_def]

end SymplecticForm

end TauCeti
