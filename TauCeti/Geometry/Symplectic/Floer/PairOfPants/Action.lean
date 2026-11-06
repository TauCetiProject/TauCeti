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
the Hamiltonians is needed for this. If `|H_q| ≤ B_q`, then `|∫_S R_K| ≤ B_0 + B_1 + B_∞`, so
the energy over `S_R` differs from the signed sum of the actions by at most `B_0 + B_1 + B_∞`,
uniformly in `R`
(`SymplecticForm.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_sum_le`).
For a solution of the Floer equation on `S_R` with tame almost complex structures the energy over
`S_R` is nonnegative, which gives the action bound
`A_{H_∞}(ℓ_∞(R)) ≤ A_{H_0}(ℓ_0(R)) + A_{H_1}(ℓ_1(R)) + B_0 + B_1 + B_∞` for every `R ≥ 2`
(`SymplecticForm.hamiltonianAction_le_add_add_sum`).

For a solution of the Floer equation `(du - X_K)^{0,1} = 0` with tame almost complex structures
the energy density is nonnegative. If the actions of the three end loops converge to limits `a_q`
as `R → ∞`, then the energy of the solution over all of `S` is

`E(u) = a_0 + a_1 - a_∞ - ∫_S R_K(u)`

(`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq`). This is the energy
identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` of the pair-of-pants product for a vector space
target, on which every sphere has zero area. If `|H_q| ≤ B_q`, the curvature bound gives the
energy bound `E(u) ≤ a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞`
(`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_le`) and the action bound
`a_∞ ≤ a_0 + a_1 + B_0 + B_1 + B_∞` for the output, the limit of the action bounds on the
truncations (`SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction`): the potential bound
under which the counts of such solutions form a supported product kernel
(`TauCeti.NovikovModule.kernelProduct`).

When the pair of pants is a piece of a larger domain, glued along the end `q`, the map is only
defined on part of that end. Cutting `S_R` along the circle `±s = c` of the end `q`, `2 ≤ c ≤ R`,
the energy over the part `±s ≤ c` of `S_R` of a map which is `C²` only on the part `±s < c + 1` of
`S` is

`∑_{r ≠ q} ±A_{H_r}(ℓ_r(R)) + ±A_{H_q}(ℓ_q(c)) - ∫ R_K(u)`,

with the curvature integrated over the same part, by
`SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_inter_eq_sum_hamiltonianAction`.
It follows from the identity on `S_R` for `u` cut off beyond the circle `±s = c + 3/4`: on the
outer part `c < ±s ≤ R` of the end `q`, where the perturbation is `H_q(t) dt`, the energy of the
cut-off map is the change of action from the circle `±s = c` to the circle `±s = R`, whatever
the cut-off map is there.

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

/-- **The energy and the actions on a truncated pair of pants.** If the end Hamiltonians are
bounded, `|H_q| ≤ B_q`, then for every `R ≥ 2` the Floer energy of `u` over the truncation `S_R`
differs from the signed sum `A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) - A_{H_∞}(ℓ_∞)` of the actions of its
boundary loops by at most `B_0 + B_1 + B_∞`, uniformly in `R`. -/
theorem abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_sum_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      ∑ q, q.endSign * ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))| ≤ ∑ q, B q := by
  rw [integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction
    ω hH hHs hu hR, sub_sub_cancel_left, abs_neg]
  exact abs_integral_hamiltonianCurvature_le ω hH hHs hB u

/-- **The action bound on a truncated pair of pants.** Let `K` be the pair-of-pants perturbation
of period-one `C¹` Hamiltonians `H_q` with `|H_q| ≤ B_q`, and let `u` be a map which is `C²` on
`S = ℂ ∖ {0, 1}` and solves the Floer equation `(du - X_K)^{0,1} = 0` on the truncation `S_R`,
`R ≥ 2`, for almost complex structures `J(z)` tamed by `ω`. Then the action of the output loop
`ℓ_∞(t) = u(φ_∞(-R + i t))` is at most the sum of the actions of the input loops
`ℓ_q(t) = u(φ_q(R + i t))` plus `B_0 + B_1 + B_∞`:

`A_{H_∞}(ℓ_∞) ≤ A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) + B_0 + B_1 + B_∞`.

No convergence of the actions as `R → ∞` is assumed. -/
theorem hamiltonianAction_le_add_add_sum (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) ≤
      ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) + ∑ q, B q := by
  -- The energy over `S_R` is nonnegative.
  have hE := setIntegral_nonneg (μ := volume) (measurableSet_truncation R) fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_sum_le
      ω hH hHs hB hu hR)).2
  simp only [sum_univ, endSign_zero, endSign_one, endSign_inf, one_mul, neg_one_mul] at h ⊢
  linarith

/-- **The action bound for a pair of pants.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq`, if moreover
`|H_q| ≤ B_q`, then the limiting action of the output end is at most the sum of the limiting
actions of the input ends plus `B_0 + B_1 + B_∞`:

`a_∞ ≤ a_0 + a_1 + B_0 + B_1 + B_∞`.

This is the limit `R → ∞` of `SymplecticForm.hamiltonianAction_le_add_add_sum`. -/
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
  have h₀ := ha zero
  have h₁ := ha one
  have hinf := ha inf
  simp only [endSign_zero, endSign_one, endSign_inf, one_mul, neg_one_mul] at h₀ h₁ hinf
  exact le_of_tendsto_of_tendsto hinf ((h₀.add h₁).add_const _) <| eventually_atTop.2
    ⟨2, fun R hR ↦ hamiltonianAction_le_add_add_sum ω hH hHs hB hu hR
      (fun z hz ↦ hJ z ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩)
      fun z hz ↦ hfloer z ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩⟩

/-! ### Truncations with one end cut short -/

/-- **The energy identity on a cylindrical part of an end.** On the part `c < ±s ≤ R` of the end
`q`, with `c ≥ 2`, where the pair-of-pants perturbation is `H_q(t) dt`, the energy of a map `u`
which is `C²` on `S` is the signed change `±(A_{H_q}(ℓ_q(R)) - A_{H_q}(ℓ_q(c)))` of the actions of
the loops `ℓ_q(r)(t) = u(φ_q(±r + i t))`. -/
private theorem integral_floerEnergyDensity_image_endChart_eq (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) (q : Puncture) {c R : ℝ} (hc : 2 ≤ c)
    (hcR : c ≤ R) :
    ∫ z in endChart q '' ({s : ℝ | c < q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Ico 0 1),
        ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      q.endSign * (ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) -
        ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * c) + ↑t * Complex.I))))) := by
  set P : Set ℝ := {s : ℝ | c < q.endSign * s ∧ q.endSign * s ≤ R}
  set U : Set (ℝ × ℝ) := {z | 1 / 2 < q.endSign * z.1}
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_const.mul continuous_fst)
  have hS {z : ℝ × ℝ} (hz : z ∈ U) : endChart q z ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (by have h : 1 / 2 < q.endSign * z.1 := hz; linarith)
  have hmemU {z : ℝ × ℝ} (h : 1 / 2 < q.endSign * z.1) : z ∈ U := h
  have hPU {z : ℝ × ℝ} (hz : z.1 ∈ P) : z ∈ U := hmemU (by linarith [hz.1])
  have hm : MeasurableSet (P ×ˢ Ico (0 : ℝ) 1) :=
    ((measurableSet_lt measurable_const (measurable_const.mul measurable_id)).inter
      (measurableSet_le (measurable_const.mul measurable_id) measurable_const)).prod
      measurableSet_Ico
  have hud {w : ℝ × ℝ} (hw : w ∈ U) : DifferentiableAt ℝ u (endChart q w) :=
    (hu.differentiableOn two_ne_zero _ (hS hw)).differentiableAt
      (isOpen_thricePuncturedSphereReal.mem_nhds (hS hw))
  have hK {w : ℝ × ℝ} (hw : w ∈ U) (v : ℂ) : DifferentiableAt ℝ
      (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm (endChart q w)) x v)
      (u (endChart q w)) :=
    ((contDiffAt_uncurry_pairOfPantsPerturbation hH hHs (hS hw) _ v).differentiableAt
      one_ne_zero).comp _ ((differentiableAt_const _).prodMk differentiableAt_id)
  rw [ω.integral_floerEnergyDensity_image hm (injOn_endChart_prod_Ico q P)
      (fun w _ ↦ (hasFDerivAt_endChart q w).differentiableAt)
      (fun w _ ↦ det_fderiv_endChart_nonneg q w) (fun w hw ↦ hud (hPU hw.1))
      (fun w hw ↦ hK (hPU hw.1) 1) (fun w hw ↦ hK (hPU hw.1) _),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]
  -- Where `±s ≥ 2` the datum in the cylinder coordinates of the end is `H_q(t) dt`, so the energy
  -- over a rectangle `[a, b] × [0, 1]` there is the change of action.
  have key {a b : ℝ} (hab : a ≤ b) (h2 : ∀ s ∈ Icc a b, 2 ≤ q.endSign * s) :
      ∫ w in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (pairOfPantsEndComponent H q 1)
          (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q) w =
        ω.hamiltonianAction (H q) (fun t ↦ (u ∘ endChart q) (b, t)) -
          ω.hamiltonianAction (H q) (fun t ↦ (u ∘ endChart q) (a, t)) := by
    have hcong {w : ℝ × ℝ} (hw : 2 ≤ q.endSign * w.1) :
        ω.floerEnergyDensity (pairOfPantsEndComponent H q 1)
            (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q) w =
          ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H q w.2) (u ∘ endChart q) w := by
      have hw₀ : 0 < q.endSign * w.1 := by linarith
      refine ω.floerEnergyDensity_congr_perturbation _
        (funext (pairOfPantsEndComponent_one_of_pos (hH q) hw₀)) (funext fun x ↦ ?_)
      rw [pairOfPantsEndComponent_I_of_pos (hH q) hw₀,
        smoothTransition.one_of_one_le (by linarith), one_mul]
    rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      fun w hw ↦ hcong (h2 w.1 hw.1)]
    exact ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub (hHs q) hUo
      (hu.comp (contDiff_endChart q 2).contDiffOn fun w hw ↦ hS hw) hab
      (fun w hw ↦ hmemU (by linarith [h2 w.1 hw.1]))
      fun s _ ↦ by
        have h := q.periodic_cylindricalEndLift s 0
        simp only [zero_add, Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul,
          add_zero] at h
        simp only [comp_apply, endChart_apply, Complex.equivRealProdCLM_symm_apply,
          Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero, h]
  simp only [equivRealProdCLM_cylindricalEndLift]
  rcases endSign_eq_one_or_eq_neg_one q with h | h
  · have hP : P = Ioc c R := by ext s; simp [P, h]
    have hae : P ×ˢ Ico (0 : ℝ) 1 =ᵐ[volume] Icc c R ×ˢ Icc 0 1 := by
      rw [hP, Measure.volume_eq_prod]
      exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc Ico_ae_eq_Icc
    rw [setIntegral_congr_set hae, key hcR fun s hs ↦ by rw [h, one_mul]; exact hc.trans hs.1, h]
    simp
  · have hP : P = Ico (-R) (-c) := by
      ext s
      simp only [P, h, mem_ofPred_eq, mem_Ico, neg_one_mul]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    have hae : P ×ˢ Ico (0 : ℝ) 1 =ᵐ[volume] Icc (-R) (-c) ×ˢ Icc 0 1 := by
      rw [hP, Measure.volume_eq_prod]
      exact Measure.set_prod_ae_eq Ico_ae_eq_Icc Ico_ae_eq_Icc
    rw [setIntegral_congr_set hae, key (neg_le_neg hcR) fun s hs ↦ by
      rw [h]; linarith [hs.2], h]
    simp only [comp_apply, neg_one_mul]
    ring

omit [FiniteDimensional ℝ V] in
/-- A map which is `C²` on the part `±s < c + 1` of `S`, with `±s` the signed longitudinal
coordinate of the end `q`, agrees near the part `±s < c + 1/4` with a map which is `C²` on all of
`S`: cut it off beyond the circle `±s = c + 3/4`. -/
private theorem exists_contDiffOn_eventuallyEq (q : Puncture) {c : ℝ} {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1 ∧
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < c + 1}) :
    ∃ v : ℝ × ℝ → V, ContDiffOn ℝ 2 v thricePuncturedSphereReal ∧
      (∀ z, q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ c + 1 / 4 →
        v z = u z) ∧
      ∀ z ∈ thricePuncturedSphereReal,
        q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < c + 1 / 4 →
        v =ᶠ[𝓝 z] u := by
  set σ : ℝ × ℝ → ℝ := fun z ↦ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re
  have hσ {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) : ContDiffAt ℝ 2 σ z :=
    contDiffAt_const.mul ((q.contDiffAt_re_endCoord
      (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)).comp z
        Complex.equivRealProdCLM.symm.contDiff.contDiffAt)
  set v : ℝ × ℝ → V := fun z ↦ (1 - smoothTransition (2 * (σ z - c) - 1 / 2)) • u z
  have hv_eq {z : ℝ × ℝ} (hz : σ z ≤ c + 1 / 4) : v z = u z := by
    simp only [v, smoothTransition.zero_of_nonpos (by linarith : 2 * (σ z - c) - 1 / 2 ≤ 0),
      sub_zero, one_smul]
  refine ⟨v, fun z hz ↦ ContDiffAt.contDiffWithinAt ?_, fun z ↦ hv_eq,
    fun z hz hσz ↦ ((hσ hz).continuousAt.eventually (gt_mem_nhds hσz)).mono fun _ h ↦
      hv_eq h.le⟩
  by_cases hσz : σ z < c + 1
  · -- Inside the circle `±s = c + 1` both factors are `C²`.
    have hn : {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1 ∧ σ z < c + 1} ∈ 𝓝 z := by
      filter_upwards [isOpen_thricePuncturedSphereReal.mem_nhds hz,
        (hσ hz).continuousAt.eventually (gt_mem_nhds hσz)] with w hw hw'
      exact ⟨hw.1, hw.2, hw'⟩
    exact (contDiffAt_const.sub (smoothTransition.contDiff.contDiffAt.comp z
      ((contDiffAt_const.mul ((hσ hz).sub contDiffAt_const)).sub contDiffAt_const))).smul
        (hu.contDiffAt hn)
  · -- Beyond the circle `±s = c + 3/4` the cut-off map vanishes.
    refine (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
    filter_upwards [(hσ hz).continuousAt.eventually (lt_mem_nhds
      (by linarith : c + 3 / 4 < σ z))] with w hw
    simp only [v, smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * (σ w - c) - 1 / 2),
      sub_self, zero_smul]

/-- For `0 ≤ c`, the part `±s > c` of the end `q` in the truncation `S_R` is the image under the
end chart of `c < ±s ≤ R`, `t ∈ [0, 1)`. -/
private theorem preimage_truncation_inter_eq_image_endChart (q : Puncture) {c : ℝ} (hc : 0 ≤ c)
    (R : ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | c < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re} =
      endChart q '' ({s : ℝ | c < q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Ico 0 1) := by
  rw [image_endChart_prod_Ico fun s hs ↦ by linarith [hs.1]]
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_truncation, mem_ofPred_eq,
    mem_thricePuncturedSphereReal_iff]
  constructor
  · rintro ⟨⟨h₀, h₁, hR⟩, h⟩
    exact ⟨⟨h₀, h₁⟩, h, hR q⟩
  · rintro ⟨⟨h₀, h₁⟩, h, hR⟩
    refine ⟨⟨h₀, h₁, fun r ↦ ?_⟩, h⟩
    by_cases hr : q = r
    · exact hr ▸ hR
    · linarith [endSign_mul_re_endCoord_nonpos hr (by linarith : 0 < q.endSign *
        (q.endCoord (Complex.equivRealProdCLM.symm z)).re),
        (endSign_mul_re_endCoord_nonpos hr (by linarith : 0 < q.endSign *
          (q.endCoord (Complex.equivRealProdCLM.symm z)).re)).trans (by linarith : (0 : ℝ) ≤ R)]

/-- The curvature of the pair-of-pants perturbation along any map vanishes on `S` outside the
part `±s ≤ c` of the end `q` of the truncation `S_R`, for `2 ≤ c` and `2 ≤ R`. -/
private theorem setIntegral_hamiltonianCurvature_eq_inter (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (q : Puncture)
    {c R : ℝ} (hc : 2 ≤ c) (hR : 2 ≤ R) (v : ℝ × ℝ → V) :
    ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (v z) =
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
          {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ c},
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (v z) := by
  have hsub : Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
      {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ c} ⊆
        {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1} :=
    fun z hz ↦ ⟨(mem_truncation.1 hz.1).1, (mem_truncation.1 hz.1).2.1⟩
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    isOpen_thricePuncturedSphereReal.measurableSet hsub fun z hz ↦ ?_
  obtain ⟨r, hr⟩ : ∃ r : Puncture,
      2 < r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re := by
    by_contra! h
    exact hz.2 ⟨mem_truncation.2 ⟨hz.1.1, hz.1.2, fun r ↦ (h r).trans hR⟩, (h q).trans hc⟩
  exact ω.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hH hHs hz.1 hr _

/-- **The energy identity on a truncated pair of pants with one end cut short.** Let `K` be the
pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_r`, and let `2 ≤ c ≤ R`. Cut the
truncation `S_R` along the circle `±s = c` of the end `q`, keeping the part `±s ≤ c`. For a map `u`
which is `C²` on the part `±s < c + 1` of `S`, the energy over this region is

`∑_{r ≠ q} ±A_{H_r}(ℓ_r(R)) + ±A_{H_q}(ℓ_q(c)) - ∫ R_K(u)`,

where `ℓ_r(R)(t) = u(φ_r(±R + i t))` are the loops along the circles `±s = R` of the other two
ends, `ℓ_q(c)(t) = u(φ_q(±c + i t))` is the loop along the cut, and the curvature is integrated
over the same region. Nothing is assumed about `u` beyond the circle `±s = c + 1` of the end `q`,
which is how this applies to a pair of pants glued into a larger domain along that end. -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation_inter_eq_sum_hamiltonianAction
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (q : Puncture) {c R : ℝ} (hc : 2 ≤ c) (hcR : c ≤ R) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1 ∧
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < c + 1}) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ c},
        ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      (∑ r ∈ Finset.univ.erase q, r.endSign * ω.hamiltonianAction (H r)
          (fun t ↦ u (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) +
        q.endSign * ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * c) + ↑t * Complex.I)))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
            {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ c},
          ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R with hT
  set σ : ℝ × ℝ → ℝ := fun z ↦ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re
  set A := T ∩ {z | σ z ≤ c} with hA
  obtain ⟨v, hv, hv_eq, hv_eventually⟩ := exists_contDiffOn_eventuallyEq q hu
  -- The energy identity on `S_R` for the cut-off map `v`.
  have hid :=
    integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction
      ω hH hHs hv (hc.trans hcR)
  rw [← hT, setIntegral_hamiltonianCurvature_eq_inter ω hH hHs q hc (hc.trans hcR), ← hT,
    ← hA] at hid
  -- Split `S_R` along the circle `±s = c`; the outer part is a cylindrical part of the end `q`,
  -- where the energy of `v` is the change of action.
  have hTm : MeasurableSet T :=
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_truncation R)).isClosed.measurableSet
  have hAm : MeasurableSet A :=
    hTm.inter (measurableSet_le ((measurable_re_endCoord q).const_mul _) measurable_const)
  have hTAB : T = A ∪ (T ∩ {z | c < σ z}) := by
    rw [← inter_union_distrib_left, ← ofPred_or]
    simp only [le_or_gt, ofPred_true, inter_univ]
  have hdisj : Disjoint A (T ∩ {z | c < σ z}) :=
    Set.disjoint_left.2 fun z hA hB ↦ by
      have h₁ : σ z ≤ c := hA.2
      have h₂ : c < σ z := hB.2
      linarith
  obtain ⟨hE, -, -⟩ := integrableOn_truncation_pairOfPantsPerturbation ω hH hHs
    (hv.of_le one_le_two) R
  rw [hTAB, setIntegral_union hdisj
      (hTm.inter (measurableSet_lt measurable_const ((measurable_re_endCoord q).const_mul _)))
      (hE.mono_set inter_subset_left) (hE.mono_set inter_subset_left),
    preimage_truncation_inter_eq_image_endChart q (by linarith) R,
    integral_floerEnergyDensity_image_endChart_eq ω hH hHs hv q hc hcR] at hid
  -- On the inner part, and on its boundary loops, the cut-off map is `u`.
  have hSA {z : ℝ × ℝ} (hz : z ∈ A) : z ∈ thricePuncturedSphereReal :=
    ⟨(mem_truncation.1 hz.1).1, (mem_truncation.1 hz.1).2.1⟩
  have hAσ {z : ℝ × ℝ} (hz : z ∈ A) : σ z ≤ c := hz.2
  have hEA : ∫ z in A, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v z =
      ∫ z in A, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
    setIntegral_congr_fun hAm fun z hz ↦ ω.floerEnergyDensity_congr_of_eventuallyEq _ _
      (hv_eventually z (hSA hz) ((hAσ hz).trans_lt (by linarith)))
  have hRA : ∫ z in A, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (v z) = ∫ z in A, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) :=
    setIntegral_congr_fun hAm fun z hz ↦ by
      rw [hv_eq z ((hAσ hz).trans (by linarith))]
  have hloop_q : (fun t : ℝ ↦ v (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * c) + ↑t * Complex.I)))) =
      fun t : ℝ ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * c) + ↑t * Complex.I))) := by
    funext t
    refine hv_eq _ ?_
    rw [equivRealProdCLM_cylindricalEndLift, re_endCoord_endChart, ← mul_assoc, endSign_mul_self,
      one_mul]
    linarith
  have hloop {r : Puncture} (hr : r ∈ Finset.univ.erase q) :
      (fun t : ℝ ↦ v (Complex.equivRealProdCLM
        (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) =
      fun t : ℝ ↦ u (Complex.equivRealProdCLM
        (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))) := by
    funext t
    refine hv_eq _ ?_
    rw [equivRealProdCLM_cylindricalEndLift]
    linarith [endSign_mul_re_endCoord_nonpos (Finset.ne_of_mem_erase hr) (q := r) (r := q)
      (w := Complex.equivRealProdCLM.symm (endChart r (r.endSign * R, t)))
      (by rw [re_endCoord_endChart, ← mul_assoc, endSign_mul_self, one_mul]; linarith)]
  rw [hEA, hRA, ← Finset.add_sum_erase _ _ (Finset.mem_univ q), hloop_q,
    Finset.sum_congr rfl fun r hr ↦ by rw [hloop hr]] at hid
  linarith

end SymplecticForm

end TauCeti
