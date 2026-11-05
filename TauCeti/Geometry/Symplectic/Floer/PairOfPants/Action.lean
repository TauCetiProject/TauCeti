/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Geometry.Symplectic.Area.ThricePuncturedSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The energy of a pair of pants in terms of the actions of its ends

Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of period-one
Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with values in a symplectic vector space
`(V, ω)`, and let `u` be a map which is `C²` on `S`. For a truncation `S_R` of `S`
(`TauCeti.ThricePuncturedSphere.truncation`), write `ℓ_q(R)` for the loop
`t ↦ u(φ_q(±R + i t))` along the boundary circle `±s = R` of the end `q`, where `φ_q` is the end
lift `Puncture.cylindricalEndLift`. This file rewrites the energy identity of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature` with Hamiltonian actions
`A_H(x) = a(x) + ∫₀¹ H(t, x(t)) dt` (`TauCeti.SymplecticForm.hamiltonianAction`):

`∫_{S_R} E = A_{H_0}(ℓ_0(R)) + A_{H_1}(ℓ_1(R)) - A_{H_∞}(ℓ_∞(R)) - ∫_S R_K(u)`

for `R ≥ 2`
(`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction`).
The symplectic area over `S_R` becomes the signed sum of the loop areas of the boundary circles by
Stokes' formula `TauCeti.SymplecticForm.integral_fderiv_apply_truncation`, and the curvature
integral over `S_R` is the curvature integral over all of `S`, because the curvature vanishes on
the cylindrical parts `±s > 2` of the ends
(`SymplecticForm.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt`); no bound on
the Hamiltonians is needed for this.

For a solution of the Floer equation `(du - X_K)^{0,1} = 0` with tame almost complex structures
the energy density is nonnegative. If the actions of the three end loops converge to limits `a_q`
as `R → ∞`, then the energy of the solution over all of `S` is

`E(u) = a_0 + a_1 - a_∞ - ∫_S R_K(u)`

(`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq`). This is the energy
identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` of the pair-of-pants product for a vector space
target, on which every sphere has zero area. If `|H_q| ≤ B_q`, then `|∫_S R_K| ≤ B_0 + B_1 + B_∞`,
which gives the energy bound `E(u) ≤ a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞`
(`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_le`) and the action bound
`a_∞ ≤ a_0 + a_1 + B_0 + B_1 + B_∞` for the output
(`SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction`): the potential bound under which
the counts of such solutions form a supported product kernel
(`TauCeti.NovikovModule.kernelProduct`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations.
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
  {H : Puncture → ℝ → V → ℝ}

/-- The truncations, in real coordinates, are measurable. -/
private theorem measurableSet_truncation (R : ℝ) :
    MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
  ((isCompact_truncation R).isClosed.preimage
    Complex.equivRealProdCLM.symm.continuous).measurableSet

/-- Stokes' formula `TauCeti.SymplecticForm.integral_fderiv_apply_truncation` in the real
coordinates `ℝ × ℝ ≃ ℂ` of the energy identity. -/
private theorem integral_symplecticForm_fderiv_truncation (ω : SymplecticForm V) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}) {R : ℝ} (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
      ∑ q : Puncture, q.endSign * ω.loopArea (fun t ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) := by
  have hv : ContDiffOn ℝ 2 (u ∘ Complex.equivRealProdCLM) {w : ℂ | w ≠ 0 ∧ w ≠ 1} :=
    hu.comp Complex.equivRealProdCLM.contDiff.contDiffOn fun w hw ↦ by
      rw [mem_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply]
      exact hw
  have h := ω.integral_fderiv_apply_truncation hv hR
  simp only [Function.comp_apply] at h
  rw [← h]
  have h₁ : Complex.equivRealProdCLM 1 = stdComplexLineReal := by
    rw [← equivRealProdCLM_symm_stdComplexLineReal, ContinuousLinearEquiv.apply_symm_apply]
  have hI : Complex.equivRealProdCLM Complex.I = stdComplexLineImag := by
    rw [← equivRealProdCLM_symm_stdComplexLineImag, ContinuousLinearEquiv.apply_symm_apply]
  simp only [ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, h₁, hI]
  have hpre : Complex.measurableEquivRealProd ⁻¹'
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R) = truncation R := by
    ext w
    simp [Complex.measurableEquivRealProd]
  rw [← Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding _ _, hpre]
  rfl

/-- **The energy identity on the truncated pair of pants, in terms of actions.** Let `K` be the
pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of
`S = ℂ ∖ {0, 1}`, with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate
`z = s + i t` of `ℂ`, and let `u` be a map which is `C²` on `S`. For `R ≥ 2`, the Floer energy of
`u` over the truncation `S_R` is the signed sum of the Hamiltonian actions of the loops
`ℓ_q(t) = u(φ_q(±R + i t))` along its three boundary circles, minus the integrated curvature over
`S`:

`∫_{S_R} E = ∑ q, ±A_{H_q}(ℓ_q) - ∫_S R_K(u)`,

with the sign `+` on the input ends `0` and `1` and `-` on the output end `∞`. -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∑ q, q.endSign * ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  -- The curvature vanishes on `S` outside `S_R`, which contains the collars of the ends.
  have hcurv : ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) =
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      ((isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).inter
        (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const)).measurableSet
      (fun z hz ↦ ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩) fun z hz ↦ ?_
    obtain ⟨q, hq⟩ : ∃ q : Puncture,
        R < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re := by
      by_contra! h
      exact hz.2 (mem_truncation.2 ⟨hz.1.1, hz.1.2, h⟩)
    exact ω.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hH hHs hz.1
      (by linarith) _
  rw [hcurv, integral_floerEnergyDensity_pairOfPantsPerturbation_truncation ω hH hHs
      (hu.of_le one_le_two) (by linarith : (1 : ℝ) ≤ R),
    integral_symplecticForm_fderiv_truncation ω hu (by linarith),
    smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ R - 1), one_mul]
  simp only [hamiltonianAction_def, mul_add, Finset.sum_add_distrib]

/-- Under convergence of the actions of the end loops, the energy over the truncations `S_(n+2)`
converges to the signed sum of the limiting actions minus the integrated curvature. -/
private theorem tendsto_integral_floerEnergyDensity_truncation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 (a q))) :
    Tendsto (fun n : ℕ ↦ ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (n + 2),
        ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) atTop
      (𝓝 ((∑ q, q.endSign * a q) -
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z))) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun n : ℕ ↦ ∑ q, q.endSign * ω.hamiltonianAction (H q)
      (fun t ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * ((n : ℝ) + 2)) + ↑t * Complex.I))))) atTop
      (𝓝 (∑ q, q.endSign * a q)) := by
    refine tendsto_finsetSum _ fun q _ ↦ ?_
    exact ((ha q).comp hn).const_mul _
  refine (hsum.sub_const _).congr fun n ↦ ?_
  rw [integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction
    ω hH hHs hu (by linarith [n.cast_nonneg (α := ℝ)])]

/-- **The energy of a pair of pants.** Let `K` be the pair-of-pants perturbation of period-one
`C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, and let `u` be a map which is `C²`
on `S` and solves the Floer equation `(du - X_K)^{0,1} = 0` there for almost complex structures
`J(z)` tamed by `ω`. If the actions of the loops `ℓ_q(t) = u(φ_q(±R + i t))` along the circles
`±s = R` of the ends converge to `a_q` as `R → ∞`, then the energy of `u` is

`E(u) = a_0 + a_1 - a_∞ - ∫_S R_K(u)`. -/
theorem lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z) (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 (a q))) :
    ∫⁻ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) =
      ENNReal.ofReal ((∑ q, q.endSign * a q) -
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) := by
  -- Exhaust `S` by the truncations `S_(n+2)`.
  set T : ℕ → Set (ℝ × ℝ) := fun n ↦ Complex.equivRealProdCLM.symm ⁻¹' truncation (n + 2)
  have hTS (n : ℕ) : T n ⊆ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} :=
    fun z hz ↦ ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩
  have hmono : Monotone T := fun m n hmn z hz ↦ by
    obtain ⟨h₀, h₁, h⟩ := mem_truncation.1 hz
    exact mem_truncation.2 ⟨h₀, h₁, fun q ↦ (h q).trans (by gcongr)⟩
  have hunion : ⋃ n, T n = {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} := by
    refine (iUnion_subset hTS).antisymm fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge
      (∑ q : Puncture, |q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re|)
    refine mem_iUnion.2 ⟨n, mem_truncation.2 ⟨hz.1, hz.2, fun q ↦ ?_⟩⟩
    have := Finset.single_le_sum (f := fun q : Puncture ↦
      |q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re|)
      (fun q _ ↦ abs_nonneg _) (Finset.mem_univ q)
    linarith [le_abs_self (q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re)]
  -- On each truncation the energy is the integral of a nonnegative integrable function.
  have hE (n : ℕ) : ∫⁻ z in T n, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) = ENNReal.ofReal (∫ z in T n, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) :=
    (ofReal_integral_eq_lintegral_ofReal
      (integrableOn_truncation_pairOfPantsPerturbation ω hH hHs (hu.of_le one_le_two) _).1
      (ae_restrict_of_forall_mem (measurableSet_truncation _) fun z hz ↦
        ω.floerEnergyDensity_nonneg (hJ z (hTS n hz)) (hfloer z (hTS n hz)))).symm
  have hlim : Tendsto (fun n ↦ ∫⁻ z in T n, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z)) atTop (𝓝 (∫⁻ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z))) := by
    rw [← hunion, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    exact tendsto_atTop_iSup fun m n hmn ↦
      lintegral_mono' (Measure.restrict_mono (hmono hmn) le_rfl) le_rfl
  refine tendsto_nhds_unique hlim ?_
  simp only [hE]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    (tendsto_integral_floerEnergyDensity_truncation ω hH hHs hu ha)

/-- The integrated curvature of the pair-of-pants perturbation over `S` is at most
`B_0 + B_1 + B_∞` in absolute value, if `|H_q| ≤ B_q`. -/
private theorem abs_integral_hamiltonianCurvature_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → V) :
    |∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)| ≤ ∑ q, B q := by
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 0)
  rw [← ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun q _ => hB₀ q),
    ← Real.enorm_eq_ofReal_abs, ENNReal.ofReal_sum_of_nonneg fun q _ => hB₀ q]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u))

/-- **The energy bound for a pair of pants.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq`, if moreover
`|H_q| ≤ B_q`, then the energy of `u` is at most `a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞`. -/
theorem lintegral_floerEnergyDensity_pairOfPantsPerturbation_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z) (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 (a q))) :
    ∫⁻ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) ≤
      ENNReal.ofReal ((∑ q, q.endSign * a q) + ∑ q, B q) := by
  rw [lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq ω hH hHs hu hJ hfloer ha]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [neg_abs_le (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)), abs_integral_hamiltonianCurvature_le ω hH hHs hB u]

/-- **The action bound for a pair of pants.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq`, if moreover
`|H_q| ≤ B_q`, then the limiting action of the output end is at most the sum of the limiting
actions of the input ends plus `B_0 + B_1 + B_∞`:

`a_∞ ≤ a_0 + a_1 + B_0 + B_1 + B_∞`. -/
theorem le_add_add_sum_of_tendsto_hamiltonianAction (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z) (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 (a q))) :
    a inf ≤ a zero + a one + ∑ q, B q := by
  -- The energy over each truncation is nonnegative, hence so is its limit.
  have hnonneg := ge_of_tendsto' (tendsto_integral_floerEnergyDensity_truncation ω hH hHs hu ha)
    fun n ↦ setIntegral_nonneg (measurableSet_truncation _) fun z hz ↦
      ω.floerEnergyDensity_nonneg (hJ z ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩)
        (hfloer z ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩)
  have hcurv := abs_integral_hamiltonianCurvature_le ω hH hHs hB u
  rw [sum_univ, endSign_zero, endSign_one, endSign_inf] at hnonneg
  linarith [neg_abs_le (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z))]

end SymplecticForm

end TauCeti
