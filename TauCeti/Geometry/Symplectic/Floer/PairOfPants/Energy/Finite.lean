/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action

/-!
# Finite-energy pairs of pants have limiting end actions

Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of period-one
Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with values in a symplectic vector space
`(V, ω)`, and let `u` be a `C²` solution of the Floer equation `(du - X_K)^{0,1} = 0` on `S` for
almost complex structures `J(z)` tamed by `ω`. Write `A_q(R)` for the Hamiltonian action
`A_{H_q}` (`TauCeti.SymplecticForm.hamiltonianAction`) of the end loop
`ℓ_q(R)(t) = u(φ_q(±R + i t))` on the circle `±s = R` of the end `q`, where `φ_q` is the end lift
`Puncture.cylindricalEndLift`, the sign is `+` on the input ends `0` and `1`, and `-` on the
output end `∞`.

The energy identities of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action` express the
energy of `u` through the limits of the actions `A_q(R)` as `R → ∞`, and take the existence of
these limits as a hypothesis. This file shows that the limits exist as soon as the energy is
finite, so that the energy identity `E(u) = a_0 + a_1 - a_∞ - ∫_S R_K(u)` holds for every
finite-energy solution.

On the part `±s ≥ 2` of the end `q` the perturbation is the cylindrical datum `H_q(t) dt`, so in
the end coordinates the energy over a rectangle `[c, d] × [0, 1]` is the change of action
(`TauCeti.SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`), and the energy
density is nonnegative. Hence the action of the end loops increases with the end coordinate `s`,
and `±A_q(R)` increases with `R`. The truncated energy identity bounds the signed sum
`∑ q, ±A_q(R)` by the total energy plus the integrated curvature, so each `A_q(R)` is monotone
and bounded, and converges. Conversely, convergent end actions give finite energy by the energy
identity. Thus a Floer solution on the pair of pants has finite energy exactly when its end
actions converge, and then each end action approaches its limit monotonically: from below on the
input ends and from above on the output end.

## Main results

* `SymplecticForm.monotoneOn_hamiltonianAction_endChart`: on the part `±s ≥ 2` of an end, the
  action of the end loops of a Floer solution increases with the end coordinate `s`.
* `SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_ne_top_iff`: a Floer
  solution has finite energy exactly when the actions of its end loops converge.
* `SymplecticForm.sum_endSign_mul_hamiltonianAction_le`: for `R ≥ 2`, the signed sum of the end
  actions of a finite-energy Floer solution is at most its energy plus the integrated curvature.
* `SymplecticForm.endSign_mul_hamiltonianAction_le_of_tendsto`: for `R ≥ 2`, the action of an end
  loop is at most its limit on the input ends and at least its limit on the output end.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1 and the
  chapter on Floer homology, on the action functional and the energy identity.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- On the part `±s ≥ 2` of the end `q`, the energy density of a Floer solution, read in the end
coordinates, is the energy density of the cylindrical datum `H_q(t) dt`, and it is nonnegative. -/
private theorem floerEnergyDensity_endChart_nonneg (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {J : AlmostComplexStructure V}
    {q : Puncture} {ζ : ℝ × ℝ} (hζ : 2 ≤ q.endSign * ζ.1) (hJ : ω.Tames J)
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u (endChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    0 ≤ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H q w.2) (u ∘ endChart q) ζ := by
  have hpos : 0 < q.endSign * ζ.1 := by linarith
  have hS := endChart_mem_thricePuncturedSphereReal hpos
  -- The components of the perturbation are differentiable in the target point.
  have hK (v : ℂ) : DifferentiableAt ℝ
      (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm (endChart q ζ)) x v)
      (u (endChart q ζ)) :=
    ((contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hS _ v).differentiableAt
      one_ne_zero).comp _ ((differentiableAt_const _).prodMk differentiableAt_id)
  have hpb := ω.floerEnergyDensity_perturbationPullback
    (Ks := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hasFDerivAt_endChart q ζ).differentiableAt
    ((hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).differentiableAt two_ne_zero)
    (hK 1) (hK Complex.I)
  -- In the end coordinates, the pulled-back datum is `H_q(t) dt` at `ζ`.
  have hKs : perturbationPullback (endChart q)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      stdComplexLineReal ζ = fun _ ↦ 0 := by
    funext x
    rw [perturbationPullback_endChart, equivRealProdCLM_symm_stdComplexLineReal,
      pairOfPantsEndComponent_one_of_pos (hH q) hpos]
  have hKt : perturbationPullback (endChart q)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      stdComplexLineImag ζ = H q ζ.2 := by
    funext x
    rw [perturbationPullback_endChart, equivRealProdCLM_symm_stdComplexLineImag,
      pairOfPantsEndComponent_I_of_pos (hH q) hpos,
      smoothTransition.one_of_one_le (by linarith), one_mul]
  have heq : ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H q w.2) (u ∘ endChart q) ζ =
      ω.floerEnergyDensity
        (perturbationPullback (endChart q)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (endChart q)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag)
        (u ∘ endChart q) ζ := by
    simp only [floerEnergyDensity_def, perturbedFDeriv_apply_stdComplexLineReal,
      perturbedFDeriv_apply_stdComplexLineImag, hKs, hKt]
  rw [heq, hpb]
  exact mul_nonneg (det_fderiv_endChart_nonneg q ζ) (ω.floerEnergyDensity_nonneg hJ hfloer)

/-- **The end actions increase along the ends.** Let `u` be `C²` on `S = ℂ ∖ {0, 1}` and solve
the Floer equation `(du - X_K)^{0,1} = 0` for the pair-of-pants perturbation `K` and almost complex
structures `J(z)` tamed by `ω`, at the points of the part `±s ≥ 2` of the end `q`. Then on that
part the action of the end loop `t ↦ u(φ_q(s + i t))` is a monotone function of `s`. -/
theorem monotoneOn_hamiltonianAction_endChart (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {J : ℝ × ℝ → AlmostComplexStructure V}
    {q : Puncture}
    (hJ : ∀ ζ : ℝ × ℝ, 2 ≤ q.endSign * ζ.1 → ω.Tames (J (endChart q ζ)))
    (hfloer : ∀ ζ : ℝ × ℝ, 2 ≤ q.endSign * ζ.1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (endChart q ζ)) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (endChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    MonotoneOn (fun s ↦ ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (s, t))))
      {s | 2 ≤ q.endSign * s} := by
  intro c hc d hd hcd
  set U : Set (ℝ × ℝ) := {ζ | 1 < q.endSign * ζ.1}
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_const.mul continuous_fst)
  -- Every point of the rectangle `[c, d] × [0, 1]` lies in the part `±s ≥ 2` of the end.
  have hmem {s : ℝ} (hs : s ∈ Icc c d) : 2 ≤ q.endSign * s := by
    rw [mem_ofPred_eq] at hc hd
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h] at hc hd ⊢ <;> linarith [hs.1, hs.2]
  have hRU : Icc c d ×ˢ Icc 0 1 ⊆ U := fun ζ hζ ↦ by
    simp only [U, mem_ofPred_eq]
    linarith [hmem hζ.1]
  have hv : ContDiffOn ℝ 2 (u ∘ endChart q) U :=
    hu.comp (contDiff_endChart q 2).contDiffOn fun ζ hζ ↦
      endChart_mem_thricePuncturedSphereReal (by
        simp only [U, mem_ofPred_eq] at hζ
        linarith)
  have hper (s : ℝ) : (u ∘ endChart q) (s, 1) = (u ∘ endChart q) (s, 0) := by
    simp only [comp_apply, endChart_mk]
    simpa using congrArg (fun w ↦ u (Complex.equivRealProdCLM w))
      (q.periodic_cylindricalEndLift s 0)
  -- The energy over the rectangle is the change of action, and it is nonnegative.
  have h := ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub (hHs q) hUo hv hcd hRU
    fun s _ ↦ hper s
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun ζ (hζ : ζ ∈ Icc c d ×ˢ Icc 0 1) ↦ floerEnergyDensity_endChart_nonneg ω hH hHs hu (hmem hζ.1)
      (hJ ζ (hmem hζ.1)) (hfloer ζ (hmem hζ.1))
  simp only [comp_apply] at h
  linarith

/-- In the parametrization `R ↦ ±R` of the ends by their signed longitudinal coordinate, the
signed end action `±A_q(R)` increases with `R ≥ 2`. -/
private theorem monotoneOn_endSign_mul_hamiltonianAction (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {J : ℝ × ℝ → AlmostComplexStructure V}
    {q : Puncture}
    (hJ : ∀ ζ : ℝ × ℝ, 2 ≤ q.endSign * ζ.1 → ω.Tames (J (endChart q ζ)))
    (hfloer : ∀ ζ : ℝ × ℝ, 2 ≤ q.endSign * ζ.1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (endChart q ζ)) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (endChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    MonotoneOn (fun R ↦ q.endSign * ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) (Ici 2) := by
  intro R₁ hR₁ R₂ hR₂ hR
  have hR₁' : (2 : ℝ) ≤ R₁ := hR₁
  have hR₂' : (2 : ℝ) ≤ R₂ := hR₂
  have hle := ω.monotoneOn_hamiltonianAction_endChart hH hHs hu hJ hfloer
  simp only [← endChart_mk]
  rcases endSign_eq_one_or_eq_neg_one q with h | h
  · simp only [h, one_mul]
    exact hle (by rw [mem_ofPred_eq, h]; linarith) (by rw [mem_ofPred_eq, h]; linarith) hR
  · simp only [h, neg_one_mul, neg_le_neg_iff]
    exact hle (by rw [mem_ofPred_eq, h]; linarith) (by rw [mem_ofPred_eq, h]; linarith)
      (neg_le_neg hR)

/-- **The end actions are bounded by the energy.** Let `u` be `C²` on `S = ℂ ∖ {0, 1}` and solve
the Floer equation `(du - X_K)^{0,1} = 0` for the pair-of-pants perturbation `K` and almost complex
structures `J(z)` tamed by `ω`. If the energy of `u` is finite, then for every `R ≥ 2` the signed
sum `∑ q, ±A_q(R)` of the actions of the end loops `ℓ_q(t) = u(φ_q(±R + i t))` is at most the
energy of `u` plus the integrated curvature `∫_S R_K(u)`. -/
theorem sum_endSign_mul_hamiltonianAction_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    {R : ℝ} (hR : 2 ≤ R) :
    ∑ q, q.endSign * ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) ≤
      (∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z)).toReal +
      ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) := by
  have hTS := preimage_truncation_subset_thricePuncturedSphereReal R
  have hTm := (isCompact_preimage_truncation R).isClosed.measurableSet
  -- The signed sum of the end actions is the energy over the truncation `S_R` plus the
  -- integrated curvature.
  have hid : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∑ q, q.endSign * ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) :=
    ω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction
      hH hHs hu hR
  -- The energy over `S_R` is at most the total energy, since the energy density is nonnegative.
  have hint : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z ≤
      (∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hTm fun z hz ↦
        ω.floerEnergyDensity_nonneg (hJ z (hTS hz)) (hfloer z (hTS hz)))
      ((integrableOn_truncation_pairOfPantsPerturbation ω hH hHs (hu.of_le one_le_two)
        R).1.aestronglyMeasurable)]
    exact ENNReal.toReal_mono hE (lintegral_mono_set hTS)
  linarith

/-- **Finite energy is equivalent to convergence of the end actions.** Let `K` be the
pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of
`S = ℂ ∖ {0, 1}`, and let `u` be a map which is `C²` on `S` and solves the Floer equation
`(du - X_K)^{0,1} = 0` there for almost complex structures `J(z)` tamed by `ω`. Then the energy
of `u` is finite if and only if, on every end `q`, the actions of the loops
`ℓ_q(t) = u(φ_q(±R + i t))` along the circles `±s = R` converge as `R → ∞`. In that case the
energy is given by `SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq`. -/
theorem lintegral_floerEnergyDensity_pairOfPantsPerturbation_ne_top_iff (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤ ↔
      ∃ a : Puncture → ℝ, ∀ q, Tendsto (fun R ↦ ω.hamiltonianAction (H q)
        (fun t ↦ u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 (a q)) := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set A : Puncture → ℝ → ℝ := fun q R ↦ ω.hamiltonianAction (H q)
    (fun t ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))
  refine ⟨fun hE ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  swap
  · exact (ω.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq hH hHs hu hJ hfloer
      ha).trans_ne ENNReal.ofReal_ne_top
  set C : ℝ := (∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (e z)).toReal +
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)
  -- Every end loop with `±s ≥ 2` lies in `S`, where the hypotheses hold.
  have hS {q : Puncture} {ζ : ℝ × ℝ} (hζ : 2 ≤ q.endSign * ζ.1) :
      endChart q ζ ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (by linarith)
  have hmono (q : Puncture) := monotoneOn_endSign_mul_hamiltonianAction ω hH hHs hu (q := q)
    (fun _ hζ ↦ hJ _ (hS hζ)) (fun _ hζ ↦ hfloer _ (hS hζ))
  have hsum {R : ℝ} (hR : 2 ≤ R) : ∑ q, q.endSign * A q R ≤ C :=
    ω.sum_endSign_mul_hamiltonianAction_le hH hHs hu hJ hfloer hE hR
  -- Each signed end action is increasing and bounded above, so it converges.
  have hconv (q : Puncture) : ∃ b, Tendsto (fun R ↦ q.endSign * A q R) atTop (𝓝 b) := by
    set g : ℝ → ℝ := fun R ↦ q.endSign * A q (max R 2)
    have hg : Monotone g := fun R₁ R₂ hR ↦ hmono q (le_max_right R₁ 2) (le_max_right R₂ 2)
      (max_le_max_right 2 hR)
    have hbdd : BddAbove (range g) := by
      refine ⟨C - ∑ r ∈ Finset.univ.erase q, r.endSign * A r 2, ?_⟩
      rintro _ ⟨R, rfl⟩
      have hR : 2 ≤ max R 2 := le_max_right R 2
      have hrest : ∑ r ∈ Finset.univ.erase q, r.endSign * A r 2 ≤
          ∑ r ∈ Finset.univ.erase q, r.endSign * A r (max R 2) :=
        Finset.sum_le_sum fun r _ ↦ hmono r (mem_Ici.2 le_rfl) hR hR
      have h := hsum hR
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q)] at h
      simp only [g]
      linarith
    refine ⟨⨆ R, g R, (tendsto_atTop_ciSup hg hbdd).congr' ?_⟩
    filter_upwards [eventually_ge_atTop 2] with R hR
    simp only [g, max_eq_left hR]
  choose b hb using hconv
  refine ⟨fun q ↦ q.endSign * b q, fun q ↦ ((hb q).const_mul q.endSign).congr fun R ↦ ?_⟩
  rw [← mul_assoc, endSign_mul_self, one_mul]

/-- **The end actions approach their limits monotonically.** Let `u` be `C²` on `S = ℂ ∖ {0, 1}`
and solve the Floer equation `(du - X_K)^{0,1} = 0` for the pair-of-pants perturbation `K` and
almost complex structures `J(z)` tamed by `ω`, at the points of the part `±s ≥ 2` of the end `q`.
If the actions of the loops `ℓ_q(t) = u(φ_q(±R + i t))` of the end `q` tend to `a` as `R → ∞`, then
`±A_{H_q}(ℓ_q) ≤ ±a` for every `R ≥ 2`: the actions of the input loops are at most their limits,
and the action of the output loop is at least its limit. -/
theorem endSign_mul_hamiltonianAction_le_of_tendsto (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {J : ℝ × ℝ → AlmostComplexStructure V}
    {q : Puncture}
    (hJ : ∀ ζ : ℝ × ℝ, 2 ≤ q.endSign * ζ.1 → ω.Tames (J (endChart q ζ)))
    (hfloer : ∀ ζ : ℝ × ℝ, 2 ≤ q.endSign * ζ.1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (endChart q ζ)) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (endChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    {a : ℝ}
    (ha : Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 a))
    {R : ℝ} (hR : 2 ≤ R) :
    q.endSign * ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) ≤ q.endSign * a := by
  have hmono := monotoneOn_endSign_mul_hamiltonianAction ω hH hHs hu hJ hfloer
  refine ge_of_tendsto (ha.const_mul q.endSign) ?_
  filter_upwards [eventually_ge_atTop R] with R' hR'
  exact hmono (mem_Ici.2 hR) (mem_Ici.2 (hR.trans hR')) hR'

end SymplecticForm

end TauCeti
