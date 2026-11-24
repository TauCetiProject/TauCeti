/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Curvature.CompactSupport
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Recentring
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping

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
    (forall_update_iff H fun _ f ↦ Periodic f 1).2 ⟨fun _ ↦ rfl, fun q _ ↦ hH q⟩
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

end TauCeti
