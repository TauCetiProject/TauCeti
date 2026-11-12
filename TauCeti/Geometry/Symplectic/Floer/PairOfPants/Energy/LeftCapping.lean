/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping
import TauCeti.Geometry.Symplectic.Area.ThricePuncturedSphere

/-!
# The energy of the input-exchange family capped at `0`

The left unit property of the pair-of-pants product is proved with the family
`K_c = TauCeti.Floer.cappedExchangePerturbation H L c`, `0 ≤ c ≤ 1`, of perturbation data on the
sphere `ℂ ∖ {1}` obtained by capping the input at `0` of the input-exchange family with a negative
plane along a neck of length `L`. Its member `c = 0` is the capping family at `0`, and its member
`c = 1` is a continuation datum on the standard cylinder. The chain homotopy given by the
one-parameter family of moduli spaces must be supported in the sense of
`TauCeti.NovikovModule.kernelMap`, and this support comes from an action bound that is uniform in
`c` and in the neck length. This file proves the energy identity of every member of the family and
the resulting energy and action bounds, for a symplectic vector space target.

Write `ℓ_1(R)(t) = u(φ_1(R + i t))` for the loop of a map `u` along the circle `s = R` of the
remaining input end, and `ℓ^c_∞(R)(t) = u(c + φ_∞(-R + i t))` for its loop along the circle
`s = -R` of the output end recentred at `c`. These circles bound the capped truncation
`TauCeti.ThricePuncturedSphere.cappedExchangeTruncation c R`, a compact subset of `ℂ ∖ {1}`
which contains the capped puncture `0`. For a map `u` which is `C²` on `ℂ ∖ {1}`, period-one `C¹`
Hamiltonians `H_q`, a neck length `L > 4` and `R ≥ L - 1`, the Floer energy of `u` for `K_c` over
this truncation is

`∫ E = A_{H_1}(ℓ_1(R)) - A_{H_∞}(ℓ^c_∞(R)) - ∫_S R_{K_c}(u)`

(`SymplecticForm.integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation`),
where `A_H` is the Hamiltonian action `TauCeti.SymplecticForm.hamiltonianAction` and
`S = ℂ ∖ {0, 1}`. The Hamiltonian `H_0` of the capped input contributes to the curvature but to no
boundary term. If `|H_q| ≤ B_q`, the curvature bound
`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_cappedExchangePerturbation_le` shows
that the energy differs from the change of action by at most `B_0 + B_0 + B_1 + B_∞`, uniformly in
`c`, `L` and `R` (in `SymplecticForm`,
`abs_integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation_sub_le`).
For a solution of the Floer equation with tame almost complex structures the energy is
nonnegative, which gives the action bound
`A_{H_∞}(ℓ^c_∞(R)) ≤ A_{H_1}(ℓ_1(R)) + B_0 + B_0 + B_1 + B_∞`
(`SymplecticForm.hamiltonianAction_le_add_add_sum_of_cappedExchangePerturbation`) and its limit
`a_∞ ≤ a_1 + B_0 + B_0 + B_1 + B_∞` for the limiting actions of the two ends
(`SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction_cappedExchangePerturbation`).

The identity is reduced to the energy identity of the input-exchange family
(`SymplecticForm.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation`) for the
Hamiltonians with `H_0` replaced by `0`. Away from the annulus where the negative plane is plumbed
into the end at `0`, the two data agree: near the capped puncture both vanish, and elsewhere the
capped datum is the input-exchange datum, whose component on the end at `0` is switched off where
the signed longitudinal coordinate of that end is at most `1`. The annulus lies inside the
truncation with recentred output end once `R ≥ L - 1`, so the energy plus the integrated curvature
over that truncation is the same for both data
(`SymplecticForm.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn`). The capped
truncation adds to it the disc about `0` cut out by the circle `s = R` of the end at `0`, where the
capped datum vanishes and the energy is the symplectic area. By Stokes' formula
(`SymplecticForm.integral_preimage_ball_eq_neg_loopArea`) this area cancels the loop area of the
boundary loop of the disc, which is the action of that loop for the zero Hamiltonian.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants and on their energy estimates.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {L c : ℝ}

/-- **The energy identity along the input-exchange family capped at `0`.** Let `K_c` be the member
`c ∈ [0, 1]` of the input-exchange family capped at `0` along a neck of length `L > 4`, for
period-one `C¹` Hamiltonians `H_q`, with components `K_s(z) = K_c(z)(1)` and `K_t(z) = K_c(z)(i)` in
the global coordinate `z = s + i t` of `ℂ`, and let `u` be a map which is `C²` on the capped domain
`ℂ ∖ {1}`. For `R ≥ L - 1`, the Floer energy of `u` over the capped truncation with recentred output
end is the change of action between the loop `ℓ_1(t) = u(φ_1(R + i t))` along the boundary circle
of the remaining input end and the loop `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` along the boundary circle
of the recentred output end, minus the integrated curvature over `S = ℂ ∖ {0, 1}`:

`∫ E = A_{H_1}(ℓ_1) - A_{H_∞}(ℓ^c_∞) - ∫_S R_{K_c}(u)`. -/
theorem integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1}) {R : ℝ}
    (hR : L - 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' cappedExchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) -
        ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
          (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) -
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set e := Complex.equivRealProdCLM
  set S : Set (ℝ × ℝ) := {z | e.symm z ≠ 0 ∧ e.symm z ≠ 1}
  set U : Set (ℝ × ℝ) := {z | e.symm z ≠ 1}
  set T := e.symm ⁻¹' exchangeTruncation c R
  set B := e.symm ⁻¹' Metric.ball (0 : ℂ) (Real.exp (-(2 * π * R)) / 2)
  have hR₂ : 2 ≤ R := by linarith
  have hS : S = thricePuncturedSphereReal := Set.ext fun _ ↦ mem_thricePuncturedSphereReal_iff.symm
  have hSo : IsOpen S := hS ▸ isOpen_thricePuncturedSphereReal
  have hUo : IsOpen U := isOpen_ne_fun e.symm.continuous continuous_const
  have hSU : S ⊆ U := fun _ hz ↦ hz.2
  have hTS : T ⊆ S := fun _ hz ↦ exchangeTruncation_subset c R hz
  have hTc : IsCompact T := e.symm.toHomeomorph.isCompact_preimage.2
    (isCompact_exchangeTruncation c R)
  have hBm : MeasurableSet B := (Metric.isOpen_ball.preimage e.symm.continuous).measurableSet
  -- The capped datum and the input-exchange datum with `H_0` switched off are `C¹`.
  have hK (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x v) (U ×ˢ univ) :=
    fun p hp ↦ (contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hp.1 p.2
      v).contDiffWithinAt
  have hK' (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ exchangePerturbation (update H zero 0) c (e.symm z) x v) (S ×ˢ univ) :=
    fun p hp ↦ (contDiffAt_uncurry_exchangePerturbation (periodic_update_zero hH zero)
      (contDiff_update_zero hHs zero) c (mem_thricePuncturedSphereReal_iff.2 hp.1) p.2
        v).contDiffWithinAt
  -- The two data agree on `S` outside the truncation `T`.
  have hagree (v : ℂ) : EqOn (fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x v)
      (fun z x ↦ exchangePerturbation (update H zero 0) c (e.symm z) x v) (S \ T) :=
    fun z hz ↦ funext fun x ↦ by
      beta_reduce
      rw [cappedExchangePerturbation_eq_of_notMem hL hc₀ hc₁ hR hz.2 x]
  -- So the energy plus the curvature over `T` is the same for both data.
  have h₁ := ω.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn hSo
    ((hu.mono hSU).of_le one_le_two) ((hK 1).mono (prod_mono hSU subset_rfl))
    ((hK Complex.I).mono (prod_mono hSU subset_rfl)) (hK' 1) (hK' Complex.I) hTc hTS (hagree 1)
    (hagree Complex.I)
  -- The energy identity of the input-exchange family with `H_0` switched off.
  have h₂ := ω.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation
    (periodic_update_zero hH zero) (contDiff_update_zero hHs zero) hc₀ hc₁ (hu.mono hSU) hR₂
  -- Both curvatures vanish on `S` outside `T`, so their integrals over `S` are those over `T`.
  have hR' (z : ℝ × ℝ) (hz : z ∈ S \ T) :=
    hamiltonianCurvature_exchangePerturbation_update_zero_eq_zero ω hH hHs hc₀ hc₁ hR₂ hz.1 hz.2
      (u z)
  have hRcap (z : ℝ × ℝ) (hz : z ∈ S \ T) :
      ω.hamiltonianCurvature
        (fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x Complex.I) z (u z) = 0 := by
    have hn : S \ T ∈ 𝓝 z := (hSo.sdiff hTc.isClosed).mem_nhds hz
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq ((hagree 1).eventuallyEq_of_mem hn)
      ((hagree Complex.I).eventuallyEq_of_mem hn)]
    exact hR' z hz
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSo.measurableSet hTS hR'] at h₂
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSo.measurableSet hTS hRcap]
  -- The capped truncation is `T` together with the disc `B` about the capped puncture.
  have hcap : e.symm ⁻¹' cappedExchangeTruncation c R = T ∪ B := by
    rw [cappedExchangeTruncation_eq_union (abs_le.2 ⟨by linarith, hc₁⟩) (by linarith),
      preimage_union]
  have hcapc : IsCompact (e.symm ⁻¹' cappedExchangeTruncation c R) :=
    e.symm.toHomeomorph.isCompact_preimage.2 (isCompact_cappedExchangeTruncation c R)
  have hEint : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x Complex.I) u)
      (e.symm ⁻¹' cappedExchangeTruncation c R) :=
    ((ω.continuousOn_floerEnergyDensity hUo (hu.of_le one_le_two) (hK 1) (hK Complex.I)).mono
      fun _ hz ↦ cappedExchangeTruncation_subset c R hz).integrableOn_compact hcapc
  rw [hcap] at hEint ⊢
  rw [setIntegral_union ((disjoint_exchangeTruncation_ball c R).preimage _) hBm
    (hEint.mono_set subset_union_left) (hEint.mono_set subset_union_right)]
  -- On `B` the capped datum vanishes, so the energy density is the area density.
  have hB (z : ℝ × ℝ) (hz : z ∈ B) (v : ℂ) (x : V) :
      cappedExchangePerturbation H L c (e.symm z) x v = 0 := by
    have hρ : Real.exp (-(2 * π * R)) ≤ Real.exp (-(2 * π * (L - 1))) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    have hz' : ‖e.symm z‖ < Real.exp (-(2 * π * R)) / 2 := by
      simpa [B] using hz
    have hzL : ‖e.symm z‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2 := by linarith
    simp [cappedExchangePerturbation_eq_zero (H := H) (by linarith) hc₀ hc₁ hzL x]
  rw [setIntegral_congr_fun hBm fun z hz ↦ by
    rw [ω.floerEnergyDensity_congr_perturbation u (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0)
      (funext fun x ↦ hB z hz 1 x) (funext fun x ↦ hB z hz Complex.I x), floerEnergyDensity_zero]]
  -- By Stokes' formula the area over `B` cancels the action of its boundary loop for `H_0 = 0`.
  rw [integral_preimage_ball_eq_neg_loopArea ω R fun z hz ↦
    hu.contDiffAt (hUo.mem_nhds fun h ↦ by
      have h' : ‖e.symm z‖ ≤ Real.exp (-(2 * π * R)) / 2 := by simpa using hz
      rw [h, norm_one] at h'
      linarith [Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos] : -(2 * π * R) ≤ 0)])]
  have hone : one ≠ zero := by decide
  have hinf : inf ≠ zero := by decide
  simp only [update_self, update_of_ne hone, update_of_ne hinf, hamiltonianAction_def,
    Pi.zero_apply, intervalIntegral.integral_zero, add_zero] at h₂ ⊢
  linarith

/-- **The energy and the actions along the input-exchange family capped at `0`.** If the end
Hamiltonians are bounded, `|H_q| ≤ B_q`, then for every `c ∈ [0, 1]`, `L > 4` and `R ≥ L - 1` the
Floer energy of `u` for the member `c` of the family over the capped truncation differs from the
change of action `A_{H_1}(ℓ_1) - A_{H_∞}(ℓ^c_∞)` of its two boundary loops by at most
`B_0 + (B_0 + B_1 + B_∞)`, uniformly in `c`, `L` and `R`. -/
theorem abs_integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation_sub_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : L - 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' cappedExchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) -
        ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
          (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))))| ≤ B zero + ∑ q, B q := by
  rw [integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation ω hH hHs hL
    hc₀ hc₁ hu hR, sub_sub_cancel_left, abs_neg]
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 0)
  have hsum₀ : 0 ≤ B zero + ∑ q, B q := add_nonneg (hB₀ _) (Finset.sum_nonneg fun q _ ↦ hB₀ q)
  have hsum : ENNReal.ofReal (B zero) + ∑ q, ENNReal.ofReal (B q) =
      ENNReal.ofReal (B zero + ∑ q, B q) := by
    rw [ENNReal.ofReal_add (hB₀ _) (Finset.sum_nonneg fun q _ ↦ hB₀ q),
      ENNReal.ofReal_sum_of_nonneg fun q _ ↦ hB₀ q]
  rw [← ENNReal.ofReal_le_ofReal_iff hsum₀, ← Real.enorm_eq_ofReal_abs, ← hsum]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_cappedExchangePerturbation_le ω hH hHs hL hB hc₀ hc₁ u))

/-- **The action bound along the input-exchange family capped at `0`.** Let `K_c` be the member
`c ∈ [0, 1]` of the input-exchange family capped at `0` along a neck of length `L > 4`, for
period-one `C¹` Hamiltonians `H_q` with `|H_q| ≤ B_q`, and let `u` be a map which is `C²` on the
capped domain `ℂ ∖ {1}` and solves the Floer equation `(du - X_K)^{0,1} = 0` for `K_c` on the capped
truncation, `R ≥ L - 1`, for almost complex structures `J(z)` tamed by `ω`. Then the action of the
output loop `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` is at most the action of the input loop
`ℓ_1(t) = u(φ_1(R + i t))` plus `B_0 + (B_0 + B_1 + B_∞)`:

`A_{H_∞}(ℓ^c_∞) ≤ A_{H_1}(ℓ_1) + B_0 + (B_0 + B_1 + B_∞)`,

uniformly in `c` and `L`. -/
theorem hamiltonianAction_le_add_add_sum_of_cappedExchangePerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1}) {R : ℝ}
    (hR : L - 1 ≤ R) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' cappedExchangeTruncation c R, ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' cappedExchangeTruncation c R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
        (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) ≤
      ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
        (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) + B zero + ∑ q, B q := by
  -- The energy over the capped truncation is nonnegative.
  have hE := setIntegral_nonneg (μ := volume)
    ((isCompact_cappedExchangeTruncation c R).isClosed.preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet fun z hz ↦
        ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (abs_integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation_sub_le
      ω hH hHs hB hL hc₀ hc₁ hu hR)).2
  linarith

/-- **The action bound for the limiting actions along the input-exchange family capped at `0`.**
Let `u` be a map which is `C²` on the capped domain `ℂ ∖ {1}` and solves the Floer equation there
for the member `c ∈ [0, 1]` of the input-exchange family capped at `0` along a neck of length
`L > 4`, for bounded period-one `C¹` Hamiltonians `|H_q| ≤ B_q` and almost complex structures
`J(z)` tamed by `ω`. If the actions of the input loop `ℓ_1(t) = u(φ_1(R + i t))` and of the output
loop `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` converge to `a_1` and `a_∞` as `R → ∞`, then

`a_∞ ≤ a_1 + B_0 + (B_0 + B_1 + B_∞)`,

uniformly in `c` and `L`. -/
theorem le_add_add_sum_of_tendsto_hamiltonianAction_cappedExchangePerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a₁ a : ℝ}
    (ha₁ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 a₁))
    (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 a)) :
    a ≤ a₁ + B zero + ∑ q, B q :=
  le_of_tendsto_of_tendsto ha ((ha₁.add_const _).add_const _) <| eventually_atTop.2
    ⟨L - 1, fun R hR ↦ hamiltonianAction_le_add_add_sum_of_cappedExchangePerturbation ω hH hHs hB
      hL hc₀ hc₁ hu hR (fun z hz ↦ hJ z (cappedExchangeTruncation_subset c R hz))
      fun z hz ↦ hfloer z (cappedExchangeTruncation_subset c R hz)⟩

end SymplecticForm

end TauCeti
