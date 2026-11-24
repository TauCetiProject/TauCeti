/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Curvature.CompactSupport
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Recentring
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping
import TauCeti.Geometry.Symplectic.Area.ThricePuncturedSphere

/-!
# The energy of the input-exchange family capped at `0`

The pair-of-pants product is unital on the left because gluing the negative PSS plane of `H_0`
into the input at `0` of the pair of pants `S = ℂ ∖ {0, 1}` gives a cylinder whose counts compare
with continuation maps. The comparison runs along the input-exchange family capped at `0`,
`K_c = TauCeti.Floer.cappedExchangePerturbation H L c` for `0 ≤ c ≤ 1`: the capping datum at `0`
along a neck of length `L`, with the output end recentred at `c`. Its domain is the capped surface
`ℂ ∖ {1}`, with one input end at `1`, carrying `H_1`, and the output end recentred at `c`, carrying
`H_∞`. The one-parameter family of moduli spaces gives the left unit homotopy, whose kernel must be
supported; that support comes from an energy bound uniform in `c`. This file proves the energy
identity of every member of the family and that uniform bound, for a target which is a
finite-dimensional manifold `M` with a nondegenerate two-form `ω`, such as a closed symplectic
manifold.

For a map `u` which is `C¹` on `S`, whose loops `t ↦ u(φ_1(R + i t))` along the input end and
`t ↦ u(c + φ_∞(-R + i t))` along the recentred output end converge pointwise to loops `x_1` and
`x_∞` as `R → ∞`, and whose energy and area densities are integrable,

`∫_S E = ∫_S u^*ω + ∫₀¹ H_1(t, x_1(t)) dt - ∫₀¹ H_∞(t, x_∞(t)) dt - ∫_S R_{K_c}(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedExchangePerturbation`). The
puncture `0` of `S` is a null set, so the integrals over `S` are those over the capped domain; the
capped puncture contributes no boundary term, since the datum vanishes on the pole disc of the
plane. Along every map the integrated curvature is at most `B_0 + (B_0 + B_1 + B_∞)` for
`|H_q| ≤ B_q`
(`SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_cappedExchangePerturbation_le`),
so the energy differs from the area plus the Hamiltonian terms by at most that constant, uniformly
in `c` and `L`
(`SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_cappedExchangePerturbation_sub_le`).
For a solution of the Floer equation with tamed almost complex structures the energy is
nonnegative, which bounds the area plus the Hamiltonian terms below by
`-(B_0 + (B_0 + B_1 + B_∞))` (`SmoothTwoForm`'s
`IsNondegenerate.neg_add_sum_le_integral_add_sub_of_isComplexLinearMap_cappedExchangePerturbation`).

The proof reduces to the start `c = 0` of the family, the capping datum at `0`. Pulling back along
the diffeomorphism `Φ_c` of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Recentring`
carries `K_c` to `K_0`
(`TauCeti.Floer.perturbationPullback_exchangeMap_cappedExchangePerturbation`), and transports
the energy, area and curvature integrals. The datum `K_0` is `C¹` on `S × M` and
cylindrical on all three ends of `S`: it is `H_1(t) dt` and `H_∞(t) dt` far out on the ends at `1`
and `∞`, and it vanishes beyond the height `L` of the end at `0`, which lies in the pole disc of the
plane (`TauCeti.Floer.cappedExchangePerturbation_zero_eq_smul_endAngularForm`). So the energy
identity for data cylindrical on the ends
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm`) applies to
it, with the Hamiltonian `0` on the end at `0`. Its curvature along `u` is integrable: it is
continuous on `S` (`SmoothTwoForm.IsNondegenerate.continuousOn_hamiltonianCurvature_comp`) and has
finite integral by the curvature bound.

For a symplectic vector space target, the energy over the truncations is the change of action of
their boundary loops. Write `ℓ_1(R)(t) = u(φ_1(R + i t))` for the loop of a map `u` along the
circle `s = R` of the remaining input end, and `ℓ^c_∞(R)(t) = u(c + φ_∞(-R + i t))` for its loop
along the circle `s = -R` of the output end recentred at `c`. These circles bound the capped
truncation `TauCeti.ThricePuncturedSphere.cappedExchangeTruncation c R`, a compact subset of
`ℂ ∖ {1}` which contains the capped puncture `0`. For a map `u` which is `C²` on `ℂ ∖ {1}`,
period-one `C¹` Hamiltonians `H_q`, a neck length `L > 4` and `R ≥ L - 1`, the Floer energy of `u`
for `K_c` over this truncation is

`∫ E = A_{H_1}(ℓ_1(R)) - A_{H_∞}(ℓ^c_∞(R)) - ∫_{ℂ ∖ {1}} R_{K_c}(u)`

(`SymplecticForm.integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation`),
where `A_H` is the Hamiltonian action `TauCeti.SymplecticForm.hamiltonianAction`. The
Hamiltonian `H_0` of the capped input contributes to the curvature but to no boundary term. If
`|H_q| ≤ B_q`, the energy differs from the change of action by at most `B_0 + B_0 + B_1 + B_∞`,
uniformly in `c`, `L` and `R` (in `SymplecticForm`,
`abs_integral_floerEnergyDensity_cappedExchangePerturbation_cappedExchangeTruncation_sub_le`).
For a solution of the Floer equation with tame almost complex structures the energy is
nonnegative, which gives the action bound
`A_{H_∞}(ℓ^c_∞(R)) ≤ A_{H_1}(ℓ_1(R)) + B_0 + B_0 + B_1 + B_∞`
(`SymplecticForm.hamiltonianAction_le_add_add_sum_of_cappedExchangePerturbation`) and its limit
`a_∞ ≤ a_1 + B_0 + B_0 + B_1 + B_∞` for the limiting actions of the two ends
(`SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction_cappedExchangePerturbation`).

This truncated identity is reduced to the energy identity of the input-exchange family
(`SymplecticForm.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation`) for the
Hamiltonians with `H_0` replaced by `0`. Away from the annulus where the negative plane is plumbed
into the end at `0`, the two data agree: near the capped puncture both vanish, and elsewhere the
capped datum is the input-exchange datum, whose component on the end at `0` is switched off where
the signed longitudinal coordinate of that end is at most `1`. The annulus lies inside the
truncation with recentred output end once `R ≥ L - 1`, so the energy plus the integrated curvature
over that truncation is the same for both data
(`SymplecticForm.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn`), while
outside that truncation the curvature of `K_c` vanishes on `ℂ ∖ {1}`
(`SymplecticForm.hamiltonianCurvature_cappedExchangePerturbation_eq_zero`) and that of the
input-exchange datum vanishes on `S = ℂ ∖ {0, 1}`
(`SymplecticForm.hamiltonianCurvature_exchangePerturbation_eq_zero`). The capped truncation adds
to it the disc about `0` cut out by the circle `s = R` of the end at `0`, where the capped datum
vanishes and the energy is the symplectic area. By Stokes' formula
(`SymplecticForm.integral_fderiv_apply_preimage_ball_eq_neg_loopArea_cylindricalEndLift`) this area
cancels the loop area of the boundary loop of the disc, which is the action of that loop for the
zero Hamiltonian.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants and its energy estimates.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology Manifold

namespace TauCeti

namespace Floer

variable {M : Type*} {H : Puncture → ℝ → M → ℝ} {L c : ℝ}

/-- **The capped family is a pullback of its start.** For `L ≥ 2` and `0 ≤ c ≤ 1`, the pullback
along the diffeomorphism `Φ_c` (`TauCeti.Floer.exchangeMap`) of the member `c` of the
input-exchange family capped at `0` is its member `0`, the capping datum at `0`. -/
theorem perturbationPullback_exchangeMap_cappedExchangePerturbation (hL : 2 ≤ L) (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) (v y : ℝ × ℝ) (x : M) :
    perturbationPullback (exchangeMap c)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I) v y x =
      cappedExchangePerturbation H L 0 (Complex.equivRealProdCLM.symm y) x
        (Complex.equivRealProdCLM.symm v) := by
  have h10 : (10 : ℝ) ≤ 2 * Real.exp (2 * π) := by
    linarith [Real.add_one_le_exp (2 * π), Real.two_le_pi]
  refine perturbationPullback_exchangeMap_of_eq hc₀ hc₁ (fun w hw ↦ funext fun x ↦ ?_)
    (fun w h₁ h₂ ↦ funext fun x ↦ ?_) (fun w h₁ h₂ ↦ funext fun x ↦ ?_)
    (fun w hw ↦ funext fun x ↦ ?_) v y x
  · -- Near the inputs both members are the capped part.
    have hwc : ‖w - c‖ ≤ 4 := by
      have := norm_sub_le w (c : ℂ)
      rw [Complex.norm_real, Real.norm_of_nonneg hc₀] at this
      linarith
    rw [cappedExchangePerturbation_of_norm_sub_le (by linarith),
      cappedExchangePerturbation_of_norm_sub_le (c := 0) (by simpa using (by linarith :
        ‖w‖ ≤ 2 * Real.exp (2 * π)))]
  · -- Between the ends the member `c` vanishes ...
    rw [cappedExchangePerturbation_of_le_norm_sub hL hc₀ hc₁ (by linarith)]
    exact negativePlanePerturbation_eq_zero_of_norm_le (by linarith) x
  · -- ... and so does the member `0`.
    rw [cappedExchangePerturbation_of_le_norm_sub hL le_rfl zero_le_one
      (by simpa using (by linarith : 3 / 2 ≤ ‖w‖))]
    exact negativePlanePerturbation_eq_zero_of_norm_le (by simpa using (by linarith :
      ‖w‖ ≤ 2 * Real.exp (2 * π))) x
  · -- Near the output end both members are translates of the plane datum.
    rw [cappedExchangePerturbation_of_le_norm_sub hL hc₀ hc₁ (by simpa using hw),
      cappedExchangePerturbation_of_le_norm_sub hL le_rfl zero_le_one (by simpa using hw)]
    simp

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {H : Puncture → ℝ → M → ℝ} {L c : ℝ}

/-- The members of the capped family are `C¹` jointly in the domain point of `S` and the target
point. -/
private theorem contMDiffAt_cappedExchangePerturbation_apply (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (hL : 4 < L) (c : ℝ) :
    ∀ z ∈ thricePuncturedSphereReal, ∀ x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ cappedExchangePerturbation H L c p.1 p.2)
      (Complex.equivRealProdCLM.symm z, x) :=
  fun _ hz x ↦ (contMDiffAt_cappedExchangePerturbation hH hHs hL c
    (mem_thricePuncturedSphereReal_iff.1 hz).2 x).comp
      (f := fun p : ℂ × M ↦ (c, p)) _ (contMDiffAt_const.prodMk contMDiffAt_id)

variable [IsManifold I ⊤ M] {ω : SmoothTwoForm I M} [FiniteDimensional ℝ E]

/-- **The curvature of the input-exchange family capped at `0` is integrable.** For bounded
period-one `C¹` Hamiltonians, `L > 4` and `0 ≤ c ≤ 1`, the curvature of the member `c` of the
family along a map continuous on `S` is integrable over the plane. -/
theorem IsNondegenerate.integrable_hamiltonianCurvature_cappedExchangePerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) :
    Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) := by
  have hK := contMDiffAt_cappedExchangePerturbation_apply hH hHs hL c
  have hcomp (v : ℂ) (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
        (uncurry fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x v)
        (z, x) := by
    have h : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
        (fun p : (ℝ × ℝ) × M ↦
          cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm p.1) p.2) (z, x) :=
      (hK z hz x).comp (z, x)
        ((Complex.equivRealProdCLM.symm.contDiff.contMDiff.comp contMDiff_fst).contMDiffAt.prodMk
          contMDiffAt_snd)
    exact h.clm_apply contMDiffAt_const
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hm := (hω.continuousOn_hamiltonianCurvature_comp isOpen_thricePuncturedSphereReal
    (hcomp 1) (hcomp Complex.I) hu).aestronglyMeasurable (μ := volume)
      isOpen_thricePuncturedSphereReal.measurableSet
  rw [hS] at hm
  refine ⟨hm, (ω.lintegral_enorm_hamiltonianCurvature_cappedExchangePerturbation_le hH hHs hL hB
    hc₀ hc₁ u).trans_lt ?_⟩
  exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
    ENNReal.sum_lt_top.2 fun _ _ ↦ ENNReal.ofReal_lt_top⟩

/-- The energy identity of the capping datum at `0`, the start of the family, for a map `v`
whose loops along the circles of the input end at `1` and of the output end at `∞` converge to
`x₁` and `x_∞`. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_cappedExchangePerturbation_zero
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L) {v : ℝ × ℝ → M}
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v thricePuncturedSphereReal) {x₁ xinf : ℝ → M}
    (hx₁ : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ v (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x₁ t)))
    (hxinf : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ v (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xinf t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ cappedExchangePerturbation H L 0 (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L 0 (Complex.equivRealProdCLM.symm z) x Complex.I)
      v) thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (v z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L 0 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L 0 (Complex.equivRealProdCLM.symm z) x
          Complex.I) v z =
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (v z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineImag) : ℝ)) +
        (∫ t in (0 : ℝ)..1, H one t (x₁ t)) - (∫ t in (0 : ℝ)..1, H inf t (xinf t)) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ cappedExchangePerturbation H L 0 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L 0 (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (v z) := by
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  rw [IntegrableOn, hS] at hE hA
  -- The datum is cylindrical on all three ends, with the Hamiltonian `0` on the capped end.
  have hH' : ∀ q, Periodic (update H zero 0 q) 1 :=
    forall_update_zero (P := fun f ↦ Periodic f 1) (fun _ ↦ rfl) hH zero
  have hK (w : ThricePuncturedSphere) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
        (fun p : ℂ × M ↦ cappedExchangePerturbation H L 0 p.1 p.2) ((w : ℂ), x) := by
    exact (contMDiffAt_cappedExchangePerturbation hH hHs hL 0 w.property.2 x).comp
      (f := fun p : ℂ × M ↦ ((0 : ℝ), p)) _ (contMDiffAt_const.prodMk contMDiffAt_id)
  -- The Hamiltonian terms of the loops along the three ends converge.
  have hloop (q : Puncture) (hq : q ≠ zero) {xq : ℝ → M}
      (hxq : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ v (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (xq t))) :
      Tendsto (fun σ ↦ ∫ t in (0 : ℝ)..1, update H zero 0 q t (v (endChart q (q.endSign * σ, t))))
        atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (xq t))) := by
    simpa only [endChart_apply, Complex.equivRealProdCLM_symm_apply, update_of_ne hq] using
      tendsto_intervalIntegral_endLoop (fun q ↦ (hHs q).continuous) hB hv.continuousOn hxq
  have hh : ∀ q, Tendsto
      (fun σ ↦ ∫ t in (0 : ℝ)..1, update H zero 0 q t (v (endChart q (q.endSign * σ, t))))
      atTop (𝓝 (Puncture.rec 0 (∫ t in (0 : ℝ)..1, H one t (x₁ t))
        (∫ t in (0 : ℝ)..1, H inf t (xinf t)) q)) := by
    intro q
    cases q with
    | zero => simp
    | one => exact hloop one (by decide) fun t ↦ by simpa using hx₁ t
    | inf => exact hloop inf (by decide) fun t ↦ by simpa using hxinf t
  have h := hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK
    (fun q w x hw ↦ cappedExchangePerturbation_zero_eq_smul_endAngularForm (by linarith) q w x hw)
    hH' hv hE hA (hω.integrable_hamiltonianCurvature_cappedExchangePerturbation hH hHs hB hL le_rfl
      zero_le_one hv.continuousOn) hh
  simp only [hS, Puncture.sum_univ, endSign_zero, endSign_one, endSign_inf] at h ⊢
  rw [h]
  ring

/-- **The energy identity of the input-exchange family capped at `0`, for a manifold target.** Let
`K_c` be the member `c ∈ [0, 1]` of the family capped at `0` along a neck of length `L > 4`, for
bounded period-one `C¹` Hamiltonians `H_q` on a finite-dimensional manifold with a nondegenerate
two-form, with components `K_s(z) = K_c(z)(1)` and `K_t(z) = K_c(z)(i)` in the global coordinate
`z = s + i t` of `ℂ`. Let `u` be a map which is `C¹` on `S`, whose loops `t ↦ u(φ_1(R + i t))`
along the circles of the input end at `1` and `t ↦ u(c + φ_∞(-R + i t))` along the circles of the
recentred output end converge pointwise to loops `x₁` and `x_∞` as `R → ∞`, and whose Floer energy
density for `K_c` and symplectic area density are integrable over `S`. Then

`∫_S E = ∫_S u^*ω + ∫₀¹ H_1(t, x₁(t)) dt - ∫₀¹ H_∞(t, x_∞(t)) dt - ∫_S R_{K_c}(u)`.

The capped puncture `0` contributes no Hamiltonian term. -/
theorem IsNondegenerate.integral_floerEnergyDensity_cappedExchangePerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x₁ xinf : ℝ → M}
    (hx₁ : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x₁ t)))
    (hxinf : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xinf t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
      u) thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∫ t in (0 : ℝ)..1, H one t (x₁ t)) - (∫ t in (0 : ℝ)..1, H inf t (xinf t)) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (u z) := by
  -- Transport everything along `Φ_c`, which maps `S` onto itself, to the map `u ∘ Φ_c` and the
  -- capping datum at `0`.
  have hK := contMDiffAt_cappedExchangePerturbation_apply hH hHs hL c
  have hp := perturbationPullback_exchangeMap_cappedExchangePerturbation (H := H) (L := L)
    (by linarith) hc₀ hc₁
  have hv := contMDiffOn_comp_exchangeMap hc₀ hc₁ hu
  have hs := isOpen_thricePuncturedSphereReal.measurableSet
  have himage := image_exchangeMap_thricePuncturedSphereReal hc₀ hc₁
  rw [← himage] at hE hA
  have hEv := integrableOn_of_integrableOn_image_exchangeMap hc₀ hc₁ hs hE
    fun w hw ↦ ω.floerEnergyDensity_comp_exchangeMap hK hp hc₀ hc₁ hu hw
  have hAv := integrableOn_of_integrableOn_image_exchangeMap hc₀ hc₁ hs hA
    fun w hw ↦ ω.eval₂_mfderiv_comp_stdComplexLine
      ((contDiff_exchangeMap c).differentiable two_ne_zero w)
      (mdifferentiableAt_exchangeMap hc₀ hc₁ hu hw)
  -- The end loops of `u ∘ Φ_c` are eventually those of `u` on the input end and on the recentred
  -- output end.
  have hx₁v (t : ℝ) : Tendsto (fun R : ℝ ↦ (u ∘ exchangeMap c) (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x₁ t)) := by
    refine (hx₁ t).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [comp_apply, exchangeMap_cylindricalEndLift c (by decide) hR]
  have hxinfv (t : ℝ) : Tendsto (fun R : ℝ ↦ (u ∘ exchangeMap c) (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xinf t)) := by
    refine (hxinf t).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with R hR
    rw [comp_apply, exchangeMap_cylindricalEndLift_inf c hR]
  rw [← himage, ω.integral_floerEnergyDensity_image_exchangeMap hK hp hc₀ hc₁ hu hs subset_rfl,
    integral_area_image_exchangeMap ω hc₀ hc₁ hu hs subset_rfl,
    ω.integral_hamiltonianCurvature_image_exchangeMap hK hp hc₀ hc₁ u hs subset_rfl]
  exact hω.integral_floerEnergyDensity_cappedExchangePerturbation_zero hH hHs hB hL hv hx₁v
    hxinfv hEv hAv

/-- **The energy bound along the input-exchange family capped at `0`, for a manifold target.**
Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedExchangePerturbation`, the Floer
energy over `S` differs from its topological part, the symplectic area plus the Hamiltonian terms
at the asymptotic orbits, by at most `B_0 + (B_0 + B_1 + B_∞)`, uniformly in `c` and in the neck
length `L`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_cappedExchangePerturbation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x₁ xinf : ℝ → M}
    (hx₁ : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x₁ t)))
    (hxinf : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xinf t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
      u) thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    |(∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z) -
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ((∫ t in (0 : ℝ)..1, H one t (x₁ t)) - ∫ t in (0 : ℝ)..1, H inf t (xinf t))| ≤
      B zero + ∑ q, B q := by
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 (u 0))
  have hsub (a b d e : ℝ) : a + b - d - e - a - (b - d) = -e := by ring
  rw [hω.integral_floerEnergyDensity_cappedExchangePerturbation hH hHs hB hL hc₀ hc₁ hu hx₁ hxinf
    hE hA, hsub, abs_neg,
    ← ENNReal.ofReal_le_ofReal_iff (add_nonneg (hB₀ zero) (Finset.sum_nonneg fun q _ ↦ hB₀ q)),
    ← Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_add (hB₀ zero) (Finset.sum_nonneg fun q _ ↦ hB₀ q),
    ENNReal.ofReal_sum_of_nonneg fun q _ ↦ hB₀ q]
  exact (eNorm_integral_le_lintegral_eNorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (ω.lintegral_enorm_hamiltonianCurvature_cappedExchangePerturbation_le hH hHs hL hB hc₀ hc₁ u))

/-- **The topological energy along the input-exchange family capped at `0` is bounded below, for
a manifold target.** Let `u` solve the Floer equation `(du - X_{K_c})^{0,1} = 0` on `S` for the
member `c ∈ [0, 1]` of the family capped at `0`, for almost complex structures `J z` on the
tangent spaces `T_{u(z)} M` tamed by the two-form, under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedExchangePerturbation`. Since its
energy is nonnegative, its symplectic area plus the Hamiltonian terms at the asymptotic orbits is
at least `-(B_0 + (B_0 + B_1 + B_∞))`, uniformly in `c` and in the neck length `L`. -/
theorem
    IsNondegenerate.neg_add_sum_le_integral_add_sub_of_isComplexLinearMap_cappedExchangePerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x₁ xinf : ℝ → M}
    (hx₁ : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x₁ t)))
    (hxinf : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xinf t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
      u) thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z).toLinearMap) :
    -(B zero + ∑ q, B q) ≤
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∫ t in (0 : ℝ)..1, H one t (x₁ t)) - ∫ t in (0 : ℝ)..1, H inf t (xinf t) := by
  have hpos := setIntegral_nonneg (μ := volume) isOpen_thricePuncturedSphereReal.measurableSet
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := abs_le.1 (hω.abs_integral_floerEnergyDensity_cappedExchangePerturbation_sub_le hH hHs
    hB hL hc₀ hc₁ hu hx₁ hxinf hE hA)
  linarith [h.2]

end SmoothTwoForm

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {L c : ℝ}

/-- For `L > 2`, `0 ≤ c ≤ 1` and `R ≥ L - 1`, the member `c` of the capped family vanishes on the
disc of radius `exp (-2πR) / 2` about the capped puncture `0`, so the Floer energy there of a map
`u` which is `C²` on `ℂ ∖ {1}` is its symplectic area. By Stokes' formula this is minus the loop
area of the boundary loop `t ↦ u(φ_0(R + i t))` of the disc. -/
private theorem integral_floerEnergyDensity_cappedExchangePerturbation_ball (ω : SymplecticForm V)
    (hL : 2 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1}) {R : ℝ}
    (hR : L - 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.ball 0 (Real.exp (-(2 * π * R)) / 2),
        ω.floerEnergyDensity
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      -ω.loopArea
        (fun t ↦ u (Complex.equivRealProdCLM (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) := by
  set e := Complex.equivRealProdCLM
  set B := e.symm ⁻¹' Metric.ball (0 : ℂ) (Real.exp (-(2 * π * R)) / 2)
  have hBm : MeasurableSet B := (Metric.isOpen_ball.preimage e.symm.continuous).measurableSet
  -- On `B` the capped datum vanishes, so the energy density is the area density.
  have hB (z : ℝ × ℝ) (hz : z ∈ B) (v : ℂ) (x : V) :
      cappedExchangePerturbation H L c (e.symm z) x v = 0 := by
    have hρ : Real.exp (-(2 * π * R)) ≤ Real.exp (-(2 * π * (L - 1))) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    have hz' : ‖e.symm z‖ < Real.exp (-(2 * π * R)) / 2 := by
      simpa [B] using hz
    have hzL : ‖e.symm z‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2 := by linarith
    simp [cappedExchangePerturbation_eq_zero (H := H) hL hc₀ hc₁ hzL x]
  rw [setIntegral_congr_fun hBm fun z hz ↦ by
    rw [ω.floerEnergyDensity_congr_perturbation u (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0)
      (funext fun x ↦ hB z hz 1 x) (funext fun x ↦ hB z hz Complex.I x), floerEnergyDensity_zero]]
  -- By Stokes' formula the area over `B` is minus the loop area of its boundary loop.
  have hUo : IsOpen {z : ℝ × ℝ | e.symm z ≠ 1} := isOpen_ne_fun e.symm.continuous continuous_const
  have hρ : ‖zero.endScale‖ * Real.exp (-(2 * π * R)) = Real.exp (-(2 * π * R)) / 2 := by
    rw [norm_endScale (by decide)]
    ring
  have h := integral_fderiv_apply_preimage_ball_eq_neg_loopArea_cylindricalEndLift ω (u := u) zero R
  rw [endCenter_zero, hρ] at h
  exact h fun z hz ↦
    hu.contDiffAt (hUo.mem_nhds fun h ↦ by
      have h' : ‖e.symm z‖ ≤ Real.exp (-(2 * π * R)) / 2 := by simpa using hz
      rw [h, norm_one] at h'
      linarith [Real.exp_le_one_iff.2
        (by nlinarith [Real.pi_pos, (by linarith : (0 : ℝ) ≤ R)] : -(2 * π * R) ≤ 0)])

/-- **The energy identity along the input-exchange family capped at `0`.** Let `K_c` be the member
`c ∈ [0, 1]` of the input-exchange family capped at `0` along a neck of length `L > 4`, for
period-one `C¹` Hamiltonians `H_q`, with components `K_s(z) = K_c(z)(1)` and `K_t(z) = K_c(z)(i)` in
the global coordinate `z = s + i t` of `ℂ`, and let `u` be a map which is `C²` on the capped domain
`ℂ ∖ {1}`. For `R ≥ L - 1`, the Floer energy of `u` over the capped truncation with recentred output
end is the change of action between the loop `ℓ_1(t) = u(φ_1(R + i t))` along the boundary circle
of the remaining input end and the loop `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` along the boundary circle
of the recentred output end, minus the integrated curvature over the capped domain `ℂ ∖ {1}`:

`∫ E = A_{H_1}(ℓ_1) - A_{H_∞}(ℓ^c_∞) - ∫_{ℂ ∖ {1}} R_{K_c}(u)`. -/
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
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
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
  -- With `H_0` switched off, the Hamiltonians are still periodic and `C¹`.
  have hH' : ∀ q, Periodic (update H zero 0 q) 1 :=
    forall_update_zero (P := fun f ↦ Periodic f 1) (fun _ ↦ rfl) hH zero
  have hHs' : ∀ q, ContDiff ℝ 1 (uncurry (update H zero 0 q)) :=
    forall_update_zero (P := fun f ↦ ContDiff ℝ 1 (uncurry f)) contDiff_const hHs zero
  -- The capped datum and the input-exchange datum with `H_0` switched off are `C¹`.
  have hK (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x v) (U ×ˢ univ) :=
    fun p hp ↦ (contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hp.1 p.2
      v).contDiffWithinAt
  have hK' (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ exchangePerturbation (update H zero 0) c (e.symm z) x v) (S ×ˢ univ) :=
    fun p hp ↦ (contDiffAt_uncurry_exchangePerturbation hH' hHs' c
      (mem_thricePuncturedSphereReal_iff.2 hp.1) p.2 v).contDiffWithinAt
  -- The two data agree on `S` outside the truncation `T`.
  have hagree (v : ℂ) : EqOn (fun z x ↦ cappedExchangePerturbation H L c (e.symm z) x v)
      (fun z x ↦ exchangePerturbation (update H zero 0) c (e.symm z) x v) (S \ T) :=
    fun z hz ↦ funext fun x ↦ by
      beta_reduce
      rw [cappedExchangePerturbation_of_notMem_exchangeTruncation (by linarith) hc₀ hc₁ hR hz.2 x]
  -- So the energy plus the curvature over `T` is the same for both data.
  have h₁ := ω.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn hSo
    ((hu.mono hSU).of_le one_le_two) ((hK 1).mono (prod_mono hSU subset_rfl))
    ((hK Complex.I).mono (prod_mono hSU subset_rfl)) (hK' 1) (hK' Complex.I) hTc hTS (hagree 1)
    (hagree Complex.I)
  -- The energy identity of the input-exchange family with `H_0` switched off.
  have h₂ := ω.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation
    hH' hHs' hc₀ hc₁ (hu.mono hSU) hR₂
  -- The curvatures vanish on `S`, respectively `U`, outside `T`, so their integrals over these
  -- sets are those over `T`.
  have hR' (z : ℝ × ℝ) (hz : z ∈ S \ T) :=
    hamiltonianCurvature_exchangePerturbation_eq_zero ω hH' hHs' hc₀ hc₁ hR₂ hz.1 hz.2 (u z)
  have hRcap (z : ℝ × ℝ) (hz : z ∈ U \ T) :=
    hamiltonianCurvature_cappedExchangePerturbation_eq_zero ω hH hHs (by linarith) hc₀ hc₁ hR hR₂
      hz.1 hz.2 (u z)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSo.measurableSet hTS hR'] at h₂
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUo.measurableSet (hTS.trans hSU) hRcap]
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
  -- On the disc `B` the capped datum vanishes, and by Stokes' formula the area over `B` cancels
  -- the action of its boundary loop for `H_0 = 0`.
  rw [integral_floerEnergyDensity_cappedExchangePerturbation_ball ω (by linarith) hc₀ hc₁ hu hR]
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
  rw [← ENNReal.ofReal_le_ofReal_iff hsum₀, ← Real.eNorm_eq_ofReal_abs, ← hsum]
  exact (eNorm_integral_le_lintegral_eNorm _).trans ((setLIntegral_le_lintegral _ _).trans
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
    ((isClosed_cappedExchangeTruncation c R).preimage
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
