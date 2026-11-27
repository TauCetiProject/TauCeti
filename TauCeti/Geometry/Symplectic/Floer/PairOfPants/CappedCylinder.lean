/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Capped
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.CylinderAction
import TauCeti.MeasureTheory.Integral.Lebesgue.ReProdIm
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip

/-!
# The pair of pants capped at `1` as a Floer cylinder

Plumbing the negative PSS plane with Hamiltonian `H_1` into the input end at `1` of the pair of
pants `ℂ ∖ {0, 1}` with Hamiltonians `H_0`, `H_1`, `H_∞`, along a neck of length `L`, gives the
perturbation one-form `K = TauCeti.Floer.plumbedPerturbation (Pi.single ∞ H_1) H 1 L` of the
capping family (`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping`). It is smooth on the
capped domain `ℂ ∖ {0}`, a cylinder whose two ends are the remaining input at `0` and the output
at `∞`. This file puts it on the standard cylinder `ℝ × ℝ/ℤ`, where, like a continuation datum
from `H_0` to `H_∞`, it is `H_0(t) dt` and `H_∞(t) dt` on the two ends; the unit property of the
pair-of-pants product compares the capping family with continuation maps in these coordinates.

The end lift `φ_0(z) = exp (-2πz) / 2` of the end at `0` maps the cylinder `ℂ / iℤ` onto
`ℂ ∖ {0}`. The end lift at `∞` is centred at `0` too, so in the cylinder coordinate `z = s + i t`
of `φ_0` the end at `∞` is the translate `z ↦ z + log 4 / (2π)` of its own end coordinate
(`TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift_zero_eq_inf_add`). The pullback of `K`
along `φ_0` has components `TauCeti.Floer.cappedCylinderComponent H L v` along a tangent vector `v`
of the cylinder, and:

* it is `H_0(t) dt` for `s ≥ 2` (`TauCeti.Floer.cappedCylinderComponent_of_two_le`) and `H_∞(t) dt`
  for `s ≤ -3` (`TauCeti.Floer.cappedCylinderComponent_of_le_neg_three`), whatever the neck length
  `L ≥ 2`; the capping Hamiltonian `H_1` only enters on the preimage of the end at `1`, a disc in
  the cylinder about the point that `φ_0` sends to the capped puncture `1`;
* it has period one in `t` (`TauCeti.Floer.periodic_cappedCylinderComponent`);
* for `L > 4` and period-one `C^n` Hamiltonians it is `C^n` jointly in the cylinder point and the
  target point (`TauCeti.Floer.contMDiff_cappedCylinderComponent`, for a manifold target, and
  `TauCeti.Floer.contDiff_uncurry_cappedCylinderComponent`, for a vector space target), and
  jointly in the neck length as well
  (`TauCeti.Floer.contMDiffAt_cappedCylinderComponent_family`,
  `TauCeti.Floer.contDiffOn_cappedCylinderComponent_family`).

For a symplectic vector space target `(V, ω)` and bounds `|H_r| ≤ B_r`, the integrated curvature
`∫ |R_K(u)|` over one period `ℝ × [t₀, t₀ + 1)` of the cylinder is at most
`B_1 + (B_0 + B_1 + B_∞)` along every map `u`, uniformly in `L`
(`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le`), since
the curvature allowance does not depend on the chart. For a `C²` map `u` with
`u(s, 1) = u(s, 0)`, and `a ≤ -3`, `2 ≤ b`, the Floer energy over `[a, b] × [0, 1]` is

`∫ E = A_{H_0}(u(b, ·)) - A_{H_∞}(u(a, ·)) - ∫ R_K(u)`

(`TauCeti.SymplecticForm.integral_floerEnergyDensity_cappedCylinderComponent`), within
`B_1 + (B_0 + B_1 + B_∞)` of the change of action
(`TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le`). For a
Floer solution with tame almost complex structures the energy is nonnegative, so the action of the
output loop is at most the action of the input loop plus this constant
(`TauCeti.SymplecticForm.hamiltonianAction_le_add_add_sum_of_cappedCylinderComponent`), and the
same holds for the limiting actions at the two ends
(`TauCeti.SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction_cappedCylinderComponent`).
This is the action filtration shift of the capping family, the same at every neck length.
Letting the rectangle grow, the energy over every rectangle is at most `a₀ - a_∞ + B_1 + (B_0 +
B_1 + B_∞)` for the limiting actions `a₀` and `a_∞` of the loops at the two ends
(`TauCeti.SymplecticForm.setIntegral_floerEnergyDensity_cappedCylinderComponent_le`), hence so is
the energy over one period `ℝ × [0, 1]` of the cylinder
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_cappedCylinderComponent_le`); for `u` of
period one in `t` the energy over `N` periods is at most `N` times this bound
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_cappedCylinderComponent_le`). This is the
energy bound for compactness of the family on the cylinder.

On the capped plane `ℂ ∖ {0}` itself the end chart `φ_0` is holomorphic, so a solution `u` on the
capped plane gives the solution `u ∘ φ_0` on the cylinder
(`SymplecticForm.isComplexLinearMap_perturbedFDeriv_cappedCylinderComponent_comp_endChart`) with
the same energy over corresponding regions
(`SymplecticForm.integral_floerEnergyDensity_image_endChart_zero_plumbedPerturbation`). A compact
subset `D` of the capped plane lies in the image of a finite band of the cylinder, so the energy of
`u` over `D` is at most `a₀ - a_∞ + B_1 + (B_0 + B_1 + B_∞)`, whatever the neck length
(`TauCeti.SymplecticForm.setIntegral_floerEnergyDensity_plumbedPerturbation_single_inf_le`). This
is the energy bound for compactness of the capping family. There the energy density is continuous
(`TauCeti.SymplecticForm.continuousOn_floerEnergyDensity_plumbedPerturbation_single_inf`).

For a manifold target `M` with a nondegenerate two-form `ω`, such as a closed symplectic
manifold, the curvature bound, the energy identity and the action bound hold both between loops
at finite ends, with actions depending on discs bounding the loops, and between the asymptotic
loops at the two ends. The curvature bound
holds along every map into `M`
(`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le`; the
vector space bound is its case `TauCeti.SymplecticForm.constSmooth`). For a `C¹` map `u` with
`u(s, 1) = u(s, 0)`, the energy over `[a, b] × [0, 1]` is
`∫ u^*ω + ∫₀¹ H_0(t, u(b, t)) dt - ∫₀¹ H_∞(t, u(a, t)) dt - ∫ R_K(u)`
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent`). For a `C²`
map, `1`-periodic in `t`, and a disc `D` bounding the output loop `γ_a = u(a, ·)`, the disc `D ⋆ u`
transported along the cylinder bounds the input loop `γ_b = u(b, ·)`, and

`∫ E = A_{H_0}(γ_b, D ⋆ u) - A_{H_∞}(γ_a, D) - ∫ R_K(u)`

for the capped action `A_H(γ, D) = ∫ D^*ω + ∫₀¹ H(t, γ(t)) dt` (`TauCeti.cappedLoopAction`)
(`IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_eq_cappedLoopAction_sub`).
Hence for a Floer solution with tamed almost complex structures,
`A_{H_∞}(γ_a, D) ≤ A_{H_0}(γ_b, D ⋆ u) + B_1 + (B_0 + B_1 + B_∞)`
(`IsNondegenerate.cappedLoopAction_le_add_add_sum_of_cappedCylinderComponent`). These
identities assume that the energy density and the curvature along `u` are integrable over the
rectangle.

Over the whole cylinder, for a `C¹` map `u`, `1`-periodic in `t`, whose loops `u(a i, ·)` and
`u(b i, ·)` converge pointwise to loops `x_inf` and `x₀` along some `a i → -∞` and `b i → ∞`, and
whose energy, area and curvature densities are integrable over `ℝ × [0, 1]`,

`∫ E = ∫ u^*ω + ∫₀¹ H_0(t, x₀(t)) dt - ∫₀¹ H_∞(t, x_inf(t)) dt - ∫ R_K(u)`

(`IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_univ_prod`), and for a Floer
solution with tamed almost complex structures
`∫₀¹ H_∞(t, x_inf(t)) dt ≤ ∫ u^*ω + ∫₀¹ H_0(t, x₀(t)) dt + B_1 + (B_0 + B_1 + B_∞)`
(`IsNondegenerate.intervalIntegral_le_add_add_sum_of_cappedCylinderComponent`).
This is the manifold counterpart of the bound on limiting actions for a vector space target.
Conversely the energy over the strip is at most
`∫ u^*ω + ∫₀¹ H_0(t, x₀(t)) dt - ∫₀¹ H_∞(t, x_inf(t)) dt + B_1 + (B_0 + B_1 + B_∞)`
(`IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_univ_prod_le`).

On the capped plane of a manifold target, as for a vector space target, a solution `u` gives the
solution `u ∘ φ_0` on the cylinder
(`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_cappedCylinderComponent_comp_endChart`) with
the same energy over corresponding regions
(`SmoothTwoForm.integral_floerEnergyDensity_image_endChart_zero_plumbedPerturbation`): the energy
density of `u ∘ φ_0` for the capped datum on the cylinder is the Jacobian determinant of `φ_0`
times that of `u` for the capping datum
(`TauCeti.SmoothTwoForm.floerEnergyDensity_cappedCylinderComponent_comp_endChart`). So if the
energy density of `u ∘ φ_0` is integrable over the strip, that of `u` is integrable on every
measurable subset `Ω` of the capped plane
(`TauCeti.SmoothTwoForm.integrableOn_floerEnergyDensity_plumbedPerturbation_single_inf`), and for
a Floer solution the energy of `u` over `Ω` is at most the bound above for `u ∘ φ_0`, whatever the
neck length
(`IsNondegenerate.setIntegral_floerEnergyDensity_plumbedPerturbation_single_inf_le`). This is the
energy bound for compactness of the capping family on a manifold target.

Capping the input at `0` instead leaves the cylinder `ℂ ∖ {1}`, whose remaining end at `1` is
centred at `1` while the output end is centred at `0`; the two end coordinates then differ by more
than a translation, and that family is not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity of Hamiltonian perturbations.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the energy of Floer cylinders between capped
  orbits.
-/

public noncomputable section

open Set Real Manifold Topology Function MeasureTheory Filter
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*} {Hb : Puncture → ℝ → M → ℝ} {L : ℝ}

/-- **The pair of pants capped at `1`, on the cylinder.** The component along a tangent vector
`v` of the cylinder, at the point `z = (s, t)` and the target point `x`, of the pullback along the
end lift `φ_0` of the end at `0` of the perturbation obtained by plumbing the negative plane with
Hamiltonian `Hb 1` into the input end at `1` of the pair of pants with Hamiltonians `Hb`, along a
neck of length `L`. Its `ds` and `dt` components are `cappedCylinderComponent Hb L 1` and
`cappedCylinderComponent Hb L Complex.I`. -/
def cappedCylinderComponent (Hb : Puncture → ℝ → M → ℝ) (L : ℝ) (v : ℂ) (z : ℝ × ℝ) (x : M) :
    ℝ :=
  plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
    (zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) x
    (deriv zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z) * v)

theorem cappedCylinderComponent_def (Hb : Puncture → ℝ → M → ℝ) (L : ℝ) (v : ℂ) (z : ℝ × ℝ)
    (x : M) :
    cappedCylinderComponent Hb L v z x =
      plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) x
        (deriv zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z) * v) :=
  (rfl)

/-- Where the signed longitudinal coordinate of the end at `1` is not positive, the capped datum is
the datum of the receiving pair of pants. -/
private theorem plumbedPerturbation_single_inf_one_of_re_endCoord_nonpos (hL : 2 ≤ L) {w : ℂ}
    (hw : (one.endCoord w).re ≤ 0) (x : M) :
    plumbedPerturbation (Pi.single inf (Hb one)) Hb one L w x = pairOfPantsPerturbation Hb w x :=
  plumbedPerturbation_of_re_endCoord_le (by simp) (by simp) (by linarith) x

/-- On the part `±s ≥ 1` of an end other than `1`, the longitudinal coordinate of the end at `1` is
not positive. -/
private theorem re_endCoord_one_cylindricalEndLift_nonpos {q : Puncture} (hq : q ≠ one) {w : ℂ}
    (hw : 1 ≤ q.endSign * w.re) : (one.endCoord (q.cylindricalEndLift w)).re ≤ 0 := by
  simpa using endSign_mul_re_endCoord_nonpos hq (w := q.cylindricalEndLift w)
    (by rw [re_endCoord_cylindricalEndLift]; linarith)

/-- The end lift of the end at `0` maps the cylinder into `ℂ ∖ {0}`: every image point is the
capped puncture `1` or a point of the pair of pants. -/
private theorem cylindricalEndLift_zero_eq_endCenter_one_or (w : ℂ) :
    zero.cylindricalEndLift w = one.endCenter ∨
      zero.cylindricalEndLift w ≠ 0 ∧ zero.cylindricalEndLift w ≠ 1 := by
  have h₀ := zero.cylindricalEndLift_sub_endCenter_ne_zero w
  rw [endCenter_zero, sub_zero] at h₀
  exact eq_endCenter_one_or_of_ne_zero h₀

/-- **The input end.** For `s ≥ 2`, the capped datum on the cylinder is `Hb 0 (t) dt`. -/
theorem cappedCylinderComponent_of_two_le (hHb : Periodic (Hb zero) 1) (hL : 2 ≤ L)
    {z : ℝ × ℝ} (hz : 2 ≤ z.1) (v : ℂ) (x : M) :
    cappedCylinderComponent Hb L v z x = v.im * Hb zero z.2 x := by
  set w := Complex.equivRealProdCLM.symm z
  have hw : w.re = z.1 := by simp [w, Complex.equivRealProdCLM_symm_apply]
  have hone : (one.endCoord (zero.cylindricalEndLift w)).re ≤ 0 :=
    re_endCoord_one_cylindricalEndLift_nonpos (by simp)
      (by rw [endSign_zero, one_mul, hw]; linarith)
  rw [cappedCylinderComponent_def, plumbedPerturbation_single_inf_one_of_re_endCoord_nonpos hL hone,
    pairOfPantsPerturbation_cylindricalEndLift hHb (by simpa [hw] using hz)]
  simp [w, Complex.equivRealProdCLM_symm_apply]

/-- **The output end.** For `s ≤ -3`, the capped datum on the cylinder is `Hb ∞ (t) dt`. -/
theorem cappedCylinderComponent_of_le_neg_three (hHb : Periodic (Hb inf) 1) (hL : 2 ≤ L)
    {z : ℝ × ℝ} (hz : z.1 ≤ -3) (v : ℂ) (x : M) :
    cappedCylinderComponent Hb L v z x = v.im * Hb inf z.2 x := by
  -- In the end coordinate of `∞`, the point `z` of the cylinder is `z + c`, and `c < 1`.
  set c : ℝ := Real.log 4 / (2 * π)
  set w := Complex.equivRealProdCLM.symm z + (c : ℂ)
  have hc : c < 1 := by
    rw [div_lt_one (by positivity)]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith [Real.two_le_pi]
  have hw : w.re = z.1 + c := by simp [w, Complex.equivRealProdCLM_symm_apply]
  have hlift : zero.cylindricalEndLift = fun z ↦ inf.cylindricalEndLift (z + (c : ℂ)) :=
    funext cylindricalEndLift_zero_eq_inf_add
  have hderiv : deriv zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z) =
      deriv inf.cylindricalEndLift w := by
    rw [hlift, deriv_comp_add_const]
  have hone : (one.endCoord (inf.cylindricalEndLift w)).re ≤ 0 :=
    re_endCoord_one_cylindricalEndLift_nonpos (by simp) (by rw [endSign_inf, hw]; linarith)
  rw [cappedCylinderComponent_def, hderiv, congrFun hlift,
    plumbedPerturbation_single_inf_one_of_re_endCoord_nonpos hL hone,
    pairOfPantsPerturbation_cylindricalEndLift hHb (by rw [endSign_inf, hw]; linarith)]
  simp [w, Complex.equivRealProdCLM_symm_apply]

/-- **Periodicity.** The capped datum on the cylinder has period one in the angular coordinate
`t`. -/
theorem periodic_cappedCylinderComponent (Hb : Puncture → ℝ → M → ℝ) (L : ℝ) (v : ℂ) (s : ℝ) :
    Periodic (fun t ↦ cappedCylinderComponent Hb L v (s, t)) 1 := by
  intro t
  have h : zero.cylindricalEndLift (Complex.equivRealProdCLM.symm (s, t + 1)) =
      zero.cylindricalEndLift (Complex.equivRealProdCLM.symm (s, t)) := by
    simpa [Complex.equivRealProdCLM_symm_apply] using zero.periodic_cylindricalEndLift s t
  funext x
  beta_reduce
  rw [cappedCylinderComponent_def, cappedCylinderComponent_def, deriv_cylindricalEndLift,
    deriv_cylindricalEndLift, h]

/-- The capped datum on the cylinder is the pullback along the end chart of `0` of the capped
datum on `ℂ ∖ {0}`, in real coordinates. -/
theorem perturbationPullback_endChart_zero_plumbedPerturbation (Hb : Puncture → ℝ → M → ℝ)
    (L : ℝ) (v : ℝ × ℝ) :
    perturbationPullback (endChart zero)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      cappedCylinderComponent Hb L (Complex.equivRealProdCLM.symm v) := by
  rw [perturbationPullback_endChart_eq_cylindricalEndLift]
  funext z x
  rw [cappedCylinderComponent_def]

/-- The `ds` component of the pullback along the end chart of `0` of the capped datum on
`ℂ ∖ {0}` is the `ds` component of the capped datum on the cylinder. -/
@[simp]
theorem perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineReal
    (Hb : Puncture → ℝ → M → ℝ) (L : ℝ) :
    perturbationPullback (endChart zero)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal =
      cappedCylinderComponent Hb L 1 := by
  rw [perturbationPullback_endChart_zero_plumbedPerturbation]
  simp [stdComplexLineReal_eq, Complex.equivRealProdCLM_symm_apply]

/-- The `dt` component of the pullback along the end chart of `0` of the capped datum on
`ℂ ∖ {0}` is the `dt` component of the capped datum on the cylinder. -/
@[simp]
theorem perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineImag
    (Hb : Puncture → ℝ → M → ℝ) (L : ℝ) :
    perturbationPullback (endChart zero)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag =
      cappedCylinderComponent Hb L Complex.I := by
  rw [perturbationPullback_endChart_zero_plumbedPerturbation]
  simp [stdComplexLineImag_eq, Complex.equivRealProdCLM_symm_apply]

section Smooth

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The capped datum on the cylinder is smooth in the neck length.** For period-one Hamiltonians
`Hb` of class `C^n` on `ℝ × M`, every component of the capped datum on the cylinder is `C^n` jointly
in the neck length, the cylinder point and the target point, at every neck length `L > 4`. -/
theorem contMDiffAt_cappedCylinderComponent_family {n : ℕ∞} (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Hb r))) (hL : 4 < L) (v : ℂ)
    (z : ℝ × ℝ) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℝ) n
      (fun p : ℝ × ((ℝ × ℝ) × M) ↦ cappedCylinderComponent Hb p.1 v p.2.1 p.2.2) (L, (z, x)) := by
  have hlift : ContDiff ℝ n
      (fun z : ℝ × ℝ ↦ zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) :=
    ((zero.contDiff_cylindricalEndLift n).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff
  have hderiv : ContDiff ℝ n
      (fun z : ℝ × ℝ ↦ deriv zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z) * v) := by
    simp only [deriv_cylindricalEndLift]
    exact ((contDiff_const.mul (hlift.sub contDiff_const)).neg).mul contDiff_const
  -- The end lift maps the cylinder into `ℂ ∖ {0}`, where the capped datum is smooth.
  have hK := contMDiffAt_plumbedPerturbation_single_inf_family (q := one) (by simp) hHb hHbs hL
    (cylindricalEndLift_zero_eq_endCenter_one_or (Complex.equivRealProdCLM.symm z)) x
  have hg : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) n
      (fun p : ℝ × ((ℝ × ℝ) × M) ↦
        (p.1, (zero.cylindricalEndLift (Complex.equivRealProdCLM.symm p.2.1), p.2.2)))
      (L, (z, x)) :=
    (contMDiff_fst.prodMk ((hlift.contMDiff.comp (contMDiff_fst.comp contMDiff_snd)).prodMk
      (contMDiff_snd.comp contMDiff_snd))).contMDiffAt
  exact (hK.comp (L, (z, x)) hg).clm_apply
    (hderiv.contMDiff.comp (contMDiff_fst.comp contMDiff_snd)).contMDiffAt

/-- **The capped datum on the cylinder is smooth.** For period-one Hamiltonians `Hb` of class
`C^n` on `ℝ × M` and neck length `L > 4`, every component of the capped datum on the cylinder is
`C^n` jointly in the cylinder point and the target point. -/
theorem contMDiff_cappedCylinderComponent {n : ℕ∞} (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Hb r))) (hL : 4 < L) (v : ℂ) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (cappedCylinderComponent Hb L v)) :=
  fun ⟨z, x⟩ ↦ (contMDiffAt_cappedCylinderComponent_family hHb hHbs hL v z x).comp
    (z, x) (contMDiffAt_const.prodMk contMDiffAt_id)

end Smooth

section VectorSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Hb : Puncture → ℝ → V → ℝ}

/-- **The capped datum on the cylinder is smooth**, for a vector space target. For period-one
Hamiltonians `Hb` of class `C^n` on `ℝ × V` and neck length `L > 4`, every component of the capped
datum on the cylinder is `C^n` jointly in the cylinder point and the target point. -/
theorem contDiff_uncurry_cappedCylinderComponent {n : ℕ∞} (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ n (uncurry (Hb r))) (hL : 4 < L) (v : ℂ) :
    ContDiff ℝ n (uncurry (cappedCylinderComponent Hb L v)) :=
  (contMDiff_prod_modelWithCornersSelf_iff.1 (contMDiff_cappedCylinderComponent hHb
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hL v)).contDiff

/-- **The capped datum on the cylinder is smooth in the neck length**, for a vector space target.
For period-one Hamiltonians `Hb` of class `C^n` on `ℝ × V`, every component of the capped datum on
the cylinder is `C^n` jointly in the neck length, the cylinder point and the target point, on the
neck lengths `L > 4`. -/
theorem contDiffOn_cappedCylinderComponent_family {n : ℕ∞} (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ n (uncurry (Hb r))) (v : ℂ) :
    ContDiffOn ℝ n (fun p : ℝ × ((ℝ × ℝ) × V) ↦ cappedCylinderComponent Hb p.1 v p.2.1 p.2.2)
      (Ioi 4 ×ˢ univ) := by
  rintro ⟨L, z, x⟩ ⟨hL, -⟩
  have h := contMDiffAt_cappedCylinderComponent_family hHb
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hL v z x
  -- Read the product of the self-models through the self-model of the product.
  have hg : ContMDiff 𝓘(ℝ, ℝ × ((ℝ × ℝ) × V)) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, V))) n
      fun p : ℝ × ((ℝ × ℝ) × V) ↦ (p.1, (p.2.1, p.2.2)) :=
    contDiff_fst.contMDiff.prodMk
      ((contDiff_fst.comp contDiff_snd).contMDiff.prodMk (contDiff_snd.comp contDiff_snd).contMDiff)
  exact (h.comp (L, (z, x)) hg.contMDiffAt).contDiffAt.contDiffWithinAt

/-- The capped datum at `1` is differentiable in the target point at every point of the image of
the end chart of `0`. -/
private theorem differentiableAt_plumbedPerturbation_endChart_zero
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    (v : ℂ) (ζ : ℝ × ℝ) (x : V) :
    DifferentiableAt ℝ (fun x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
      (Complex.equivRealProdCLM.symm (endChart zero ζ)) x v) x :=
  ((contDiffAt_uncurry_plumbedPerturbation_single_inf (by simp) hHb hHbs hL
    (eq_endCenter_one_or_of_ne_zero (equivRealProdCLM_symm_endChart_zero_ne_zero ζ)) x
    v).differentiableAt one_ne_zero).comp x
    (differentiableAt_const _ |>.prodMk differentiableAt_id)

end VectorSpace

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I ⊤ M] {Hb : Puncture → ℝ → M → ℝ} {L : ℝ} {Bb : Puncture → ℝ}
  {ω : SmoothTwoForm I M} {u : ℝ × ℝ → M} {a b : ℝ}

/-- **The integrated curvature of the capped cylinder is bounded uniformly in the neck length**,
for a manifold target. For period-one `C¹` Hamiltonians on a manifold `M` with a two-form `ω`,
with `|Hb r| ≤ Bb r`, and neck length `L > 4`, along every map `u` into `M` the integral of
`|R_K(z, u(z))|` over one period `ℝ × [t₀, t₀ + 1)` of the cylinder is at most
`Bb 1 + ∑ r, Bb r`. -/
theorem lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le (ω : SmoothTwoForm I M)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (t₀ : ℝ) (u : ℝ × ℝ → M) :
    ∫⁻ z in univ ×ˢ Ico t₀ (t₀ + 1), ‖ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) z (u z)‖ₑ ≤
      ENNReal.ofReal (Bb one) + ∑ r, ENNReal.ofReal (Bb r) := by
  set s : Set (ℝ × ℝ) := univ ×ˢ Ico t₀ (t₀ + 1)
  have hinj := injOn_endChart_univ_prod_Ico zero t₀
  -- A map on the capped domain which restricts to `u` along the end chart.
  set u' : ℝ × ℝ → M := u ∘ invFunOn (endChart zero) s
  have hu' {w : ℝ × ℝ} (hw : w ∈ s) : u' (endChart zero w) = u w := by
    simp only [u', comp_apply]
    rw [hinj.leftInvOn_invFunOn hw]
  -- The end chart lands in `ℂ ∖ {0}`, where the capped datum is `C¹`.
  have hK (w : ℝ × ℝ) (x : M) := contMDiffAt_plumbedPerturbation_single_inf (n := 1)
    (q := one) (w := Complex.equivRealProdCLM.symm (endChart zero w)) (by simp) hHb hHbs hL
    (by rw [equivRealProdCLM_symm_endChart]; exact cylindricalEndLift_zero_eq_endCenter_one_or _)
    x
  -- Differentiability in the domain point.
  have hdom (v : ℂ) (w : ℝ × ℝ) (x : M) : DifferentiableAt ℝ
      (fun z ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (Complex.equivRealProdCLM.symm z) x v) (endChart zero w) := by
    have hg : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℂ).prod I) 1
        (fun z : ℝ × ℝ ↦ (Complex.equivRealProdCLM.symm z, x)) (endChart zero w) :=
      (Complex.equivRealProdCLM.symm.contDiff.contMDiff.prodMk contMDiff_const).contMDiffAt
    exact (contMDiffAt_iff_contDiffAt.1 (((hK w x).comp (endChart zero w) hg).clm_apply
      contMDiffAt_const)).differentiableAt one_ne_zero
  -- Differentiability in the target point.
  have htgt (v : ℂ) (w : ℝ × ℝ) (x : M) : MDifferentiableAt I 𝓘(ℝ)
      (fun x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (Complex.equivRealProdCLM.symm (endChart zero w)) x v) x := by
    have hg : ContMDiffAt I (𝓘(ℝ, ℂ).prod I) 1
        (fun x : M ↦ (Complex.equivRealProdCLM.symm (endChart zero w), x)) x :=
      contMDiffAt_const.prodMk contMDiffAt_id
    exact (((hK w x).comp x hg).clm_apply contMDiffAt_const).mdifferentiableAt one_ne_zero
  have h := ω.lintegral_enorm_hamiltonianCurvature_image (u := u')
    (Ks := fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
      (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
      (Complex.equivRealProdCLM.symm z) x Complex.I)
    (MeasurableSet.univ.prod measurableSet_Ico) hinj
    (fun w _ ↦ (contDiff_endChart zero 2).contDiffAt) (fun w _ ↦ hdom 1 w _)
    (fun w _ ↦ hdom Complex.I w _) (fun w _ ↦ htgt 1 w _) (fun w _ ↦ htgt Complex.I w _)
  rw [perturbationPullback_endChart_zero_plumbedPerturbation,
    perturbationPullback_endChart_zero_plumbedPerturbation] at h
  have h₁ : Complex.equivRealProdCLM.symm stdComplexLineReal = 1 := by
    simp [stdComplexLineReal_eq, Complex.equivRealProdCLM_symm_apply]
  have hI : Complex.equivRealProdCLM.symm stdComplexLineImag = Complex.I := by
    simp [stdComplexLineImag_eq, Complex.equivRealProdCLM_symm_apply]
  rw [h₁, hI] at h
  calc ∫⁻ z in s, ‖ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u z)‖ₑ
      = ∫⁻ z in s, ‖ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u' (endChart zero z))‖ₑ :=
        setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ico) fun w hw ↦ by
          rw [hu' hw]
    _ = _ := h.symm
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ ≤ _ := ω.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_single_inf_le
        (q := one) (by simp) hHb hHbs hL hBb u'

/-- The integrated curvature of the capped cylinder over any subset `s` of the strip
`ℝ × [0, 1]`, such as a rectangle `[a, b] × [0, 1]` or the whole strip, is at most
`Bb 1 + ∑ r, Bb r` in absolute value, whatever the neck length `L > 4`. -/
theorem abs_setIntegral_hamiltonianCurvature_cappedCylinderComponent_le (ω : SmoothTwoForm I M)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → M) {s : Set (ℝ × ℝ)}
    (hs : s ⊆ univ ×ˢ Icc 0 1) :
    |∫ z in s, ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) z (u z)| ≤ Bb one + ∑ r, Bb r := by
  have hB0 (r : Puncture) : 0 ≤ Bb r := (abs_nonneg _).trans (hBb r 0 (u 0))
  have hsum : 0 ≤ ∑ r, Bb r := Finset.sum_nonneg fun r _ ↦ hB0 r
  rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg (hB0 one) hsum), ← Real.eNorm_eq_ofReal_abs,
    ENNReal.ofReal_add (hB0 one) hsum, ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hB0 r]
  have hcurv := ω.lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le hHb hHbs hL hBb
    0 u
  -- The strip `ℝ × [0, 1]` is `ℝ × [0, 1)` up to a null set.
  have hsets : ((univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] univ ×ˢ Icc 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ico_ae_eq_Icc
  rw [zero_add, setLIntegral_congr hsets] at hcurv
  exact (eNorm_integral_le_lintegral_eNorm _).trans
    ((lintegral_mono_set hs).trans hcurv)

variable [FiniteDimensional ℝ E]

/-- **The energy identity of the capped cylinder**, for a manifold target. Let `ω` be a
nondegenerate two-form on a finite-dimensional manifold `M`, `Hb` period-one `C¹` Hamiltonians
on `M` and `L > 4`, and let `u` be `C¹` with `u(s, 1) = u(s, 0)` for `s ∈ [a, b]`. If `a ≤ -3`
and `2 ≤ b`, and the energy density and the curvature along `u` are integrable over the rectangle,
then the Floer energy of `u` over `[a, b] × [0, 1]` for the capped datum on the cylinder is the
symplectic area of `u` over the rectangle, plus the Hamiltonian term of the input loop at `s = b`
for `Hb 0`, minus that of the output loop at `s = a` for `Hb ∞`, minus the integrated curvature:

`∫ E = ∫ u^*ω + ∫₀¹ Hb 0 (t, u(b, t)) dt - ∫₀¹ Hb ∞ (t, u(a, t)) dt - ∫ R_K(u)`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (ha : a ≤ -3) (hb : 2 ≤ b)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) (Icc a b ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (Icc a b ×ˢ Icc 0 1)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z =
      rectangleIntegral ω.val u (a, 0) (b, 1) + (∫ t in 0..1, Hb zero t (u (b, t))) -
        (∫ t in 0..1, Hb inf t (u (a, t))) -
        ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u z) := by
  have hab : a ≤ b := by linarith
  have hL₂ : 2 ≤ L := by linarith
  have hR' : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := Icc_prod_Icc _ _ _ _
  have hab' : ((a, 0) : ℝ × ℝ) ≤ (b, 1) := Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩
  have hω₀ : IsSmoothForm I 0 ω.val := ω.isSmoothForm.of_le (by simp)
  rw [hR'] at hE hR ⊢
  rw [hω.integral_floerEnergyDensity isOpen_univ hu.contMDiffOn
    (contMDiff_cappedCylinderComponent hHb hHbs hL 1).contMDiffOn
    (contMDiff_cappedCylinderComponent hHb hHbs hL Complex.I).contMDiffOn hab' (subset_univ _)
    hE hR, ← hω₀.setIntegral_eq_rectangleIntegral hu hab']
  -- The `ds` terms along the circles `t = 0` and `t = 1` cancel by periodicity.
  have hs : ∫ s in a..b, cappedCylinderComponent Hb L 1 (s, 1) (u (s, 1)) =
      ∫ s in a..b, cappedCylinderComponent Hb L 1 (s, 0) (u (s, 0)) := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le hab] at hs
    rw [hper s hs]
    simpa using congrFun (periodic_cappedCylinderComponent Hb L 1 s 0) (u (s, 0))
  -- The `dt` terms along the circles `s = b` and `s = a` are those of `Hb 0` and `Hb ∞`.
  have hb' : ∫ t in (0 : ℝ)..1, cappedCylinderComponent Hb L Complex.I (b, t) (u (b, t)) =
      ∫ t in (0 : ℝ)..1, Hb zero t (u (b, t)) :=
    intervalIntegral.integral_congr fun t _ ↦ by
      simp [cappedCylinderComponent_of_two_le (hHb zero) hL₂ (z := (b, t)) hb]
  have ha' : ∫ t in (0 : ℝ)..1, cappedCylinderComponent Hb L Complex.I (a, t) (u (a, t)) =
      ∫ t in (0 : ℝ)..1, Hb inf t (u (a, t)) :=
    intervalIntegral.integral_congr fun t _ ↦ by
      simp [cappedCylinderComponent_of_le_neg_three (hHb inf) hL₂ (z := (a, t)) ha]
  rw [hs, hb', ha']
  simp only [SmoothBundleForm.eval₂_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]
  ring

/-- **The energy of the capped cylinder in terms of capped actions**, for a manifold target.
Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent`, let
`u` be `C²` and `1`-periodic in `t`, and let `D` be a disc bounding the output loop
`γ_a = u(a, ·)`. Gluing to `D` the cylinder swept by `u` from `γ_a` to the input loop
`γ_b = u(b, ·)` gives a disc `D ⋆ u` bounding `γ_b`, and the Floer energy of `u` over
`[a, b] × [0, 1]` is the capped action of the input for `Hb 0` minus that of the output for `Hb ∞`,
minus the integrated curvature:

`∫ E = A_{Hb 0}(γ_b, D ⋆ u) - A_{Hb ∞}(γ_a, D) - ∫ R_K(u)`,

for the capped action `A_H(γ, D) = ∫ D^*ω + ∫₀¹ H(t, γ(t)) dt` (`TauCeti.cappedLoopAction`). -/
theorem IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_eq_cappedLoopAction_sub
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z)
    (ha : a ≤ -3) (hb : 2 ≤ b) {D : ℝ × ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) fun t ↦ u (a, t))
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) (Icc a b ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (Icc a b ×ˢ Icc 0 1)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z =
      cappedLoopAction ω.val (Hb zero) (fun t ↦ u (b, t))
          (rectangleTrans D (u ∘ Prod.map (fun σ ↦ a + (b - a) * σ) id)) -
        cappedLoopAction ω.val (Hb inf) (fun t ↦ u (a, t)) D -
        ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u z) := by
  have hω₀ : IsSmoothForm I 0 ω.val := ω.isSmoothForm.of_le (by simp)
  have h := cappedLoopAction_rectangleTrans_sub_cappedLoopAction hω₀ (Hb zero) hD
    (isLoopCylinder_comp_prodMap hu hper a b)
  rw [hω.integral_floerEnergyDensity_cappedCylinderComponent hHb hHbs hL (hu.of_le one_le_two) ha
    hb (fun s _ ↦ by simpa using hper (s, 0)) hE hR,
    ← rectangleIntegral_comp_prodMap_affine hω₀ (hu.of_le one_le_two) a b 0 1]
  rw [cappedLoopAction_def, cappedLoopAction_def] at h ⊢
  linarith

/-- **The energy bound of the capped cylinder**, for a manifold target. Under the hypotheses of
`IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_eq_cappedLoopAction_sub`, if
`|Hb r| ≤ Bb r`, then the Floer energy over `[a, b] × [0, 1]` differs from the change of capped
action `A_{Hb 0}(γ_b, D ⋆ u) - A_{Hb ∞}(γ_a, D)` by at most `Bb 1 + ∑ r, Bb r`, uniformly in the
neck length and in `a` and `b`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z)
    (ha : a ≤ -3) (hb : 2 ≤ b) {D : ℝ × ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) fun t ↦ u (a, t))
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) (Icc a b ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (Icc a b ×ˢ Icc 0 1)) :
    |(∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z) -
      (cappedLoopAction ω.val (Hb zero) (fun t ↦ u (b, t))
          (rectangleTrans D (u ∘ Prod.map (fun σ ↦ a + (b - a) * σ) id)) -
        cappedLoopAction ω.val (Hb inf) (fun t ↦ u (a, t)) D)| ≤ Bb one + ∑ r, Bb r := by
  have hsub (x y z : ℝ) : x - y - z - (x - y) = -z := by ring
  rw [hω.integral_floerEnergyDensity_cappedCylinderComponent_eq_cappedLoopAction_sub hHb hHbs hL
    hu hper ha hb hD hE hR, hsub, abs_neg]
  exact ω.abs_setIntegral_hamiltonianCurvature_cappedCylinderComponent_le hHb hHbs hL hBb u
    (prod_mono (subset_univ _) subset_rfl)

/-- **The action bound of the capped cylinder**, for a manifold target. Under the hypotheses of
`IsNondegenerate.abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le`, if `u` solves
the Floer equation on the rectangle for almost complex structures `J z` on `T_{u z} M` tamed by
`ω`, then the capped action of the output loop `γ_a = u(a, ·)` with its disc `D` is at most that
of the input loop `γ_b = u(b, ·)` with the transported disc `D ⋆ u`, plus `Bb 1 + ∑ r, Bb r`:

`A_{Hb ∞}(γ_a, D) ≤ A_{Hb 0}(γ_b, D ⋆ u) + Bb 1 + ∑ r, Bb r`.

This is the action filtration shift of the capping family on a manifold target, the same at
every neck length. -/
theorem IsNondegenerate.cappedLoopAction_le_add_add_sum_of_cappedCylinderComponent
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z)
    (ha : a ≤ -3) (hb : 2 ≤ b) {D : ℝ × ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) fun t ↦ u (a, t))
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z).toLinearMap)
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) (Icc a b ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (Icc a b ×ˢ Icc 0 1)) :
    cappedLoopAction ω.val (Hb inf) (fun t ↦ u (a, t)) D ≤
      cappedLoopAction ω.val (Hb zero) (fun t ↦ u (b, t))
          (rectangleTrans D (u ∘ Prod.map (fun σ ↦ a + (b - a) * σ) id)) +
        Bb one + ∑ r, Bb r := by
  have hE₀ := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (hω.abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le hHb hHbs
    hL hBb hu hper ha hb hD hE hR)).2
  linarith

/-- **The energy identity of the capped cylinder over the whole cylinder**, for a manifold target.
Let `ω` be a nondegenerate two-form on a finite-dimensional manifold, `Hb` bounded period-one `C¹`
Hamiltonians and `L > 4`, and let `u` be a `C¹` map with `u(s, 1) = u(s, 0)`, whose energy density,
symplectic area density and curvature for the capped datum are integrable over the strip
`ℝ × [0, 1]`. If along a countably generated filter `a i → -∞` and `b i → ∞`, and the loops
`u(a i, ·)` and `u(b i, ·)` converge pointwise to loops `x_inf` and `x₀`, then

`∫ E = ∫ u^*ω + ∫₀¹ Hb 0 (t, x₀(t)) dt - ∫₀¹ Hb ∞ (t, x_inf(t)) dt - ∫ R_K(u)`

over the strip: the input loop `x₀` is asymptotic to the end at `0` and the output loop `x_inf`
to the end at `∞`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_univ_prod
    {ι : Type*} (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hper : ∀ s, u (s, 1) = u (s, 0)) {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {a b : ι → ℝ} (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) {x_inf x₀ : ℝ → M}
    (hx_inf : ∀ t, Tendsto (fun i ↦ u (a i, t)) l (𝓝 (x_inf t)))
    (hx₀ : ∀ t, Tendsto (fun i ↦ u (b i, t)) l (𝓝 (x₀ t)))
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) (univ ×ˢ Icc 0 1))
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) (univ ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (univ ×ˢ Icc 0 1)) :
    ∫ z in univ ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z =
      (∫ z in univ ×ˢ Icc 0 1, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∫ t in 0..1, Hb zero t (x₀ t)) - (∫ t in 0..1, Hb inf t (x_inf t)) -
        ∫ z in univ ×ˢ Icc 0 1, ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u z) := by
  have hL₂ : 2 ≤ L := by linarith
  refine hω.integral_floerEnergyDensity_univ_prod (c := 3)
    (contMDiff_cappedCylinderComponent hHb hHbs hL 1)
    (contMDiff_cappedCylinderComponent hHb hHbs hL Complex.I)
    (fun z hz ↦ funext fun x ↦ ?_) (fun z hz ↦ funext fun x ↦ ?_)
    (fun t _ ↦ hBb inf t) (fun t _ ↦ hBb zero t) hu
    (fun s ↦ by
      rw [hper s]
      simpa using congrFun (periodic_cappedCylinderComponent Hb L 1 s 0) (u (s, 0)))
    ha hb hx_inf hx₀ hE hA hR
  · simp [cappedCylinderComponent_of_le_neg_three (hHb inf) hL₂ hz]
  · simp [cappedCylinderComponent_of_two_le (hHb zero) hL₂ (by linarith : 2 ≤ z.1)]

/-- **The action bound of the capped cylinder at its asymptotic loops**, for a manifold target.
Under the hypotheses of
`IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_univ_prod`, if `u` solves the
Floer equation on the strip `ℝ × [0, 1]` for almost complex structures `J z` on `T_{u z} M` tamed
by `ω`, then

`∫₀¹ Hb ∞ (t, x_inf(t)) dt ≤ ∫ u^*ω + ∫₀¹ Hb 0 (t, x₀(t)) dt + Bb 1 + ∑ r, Bb r`.

For a disc `D` bounding the output loop `x_inf`, this bounds the capped action of the output by
that of the input capped by `D` glued to `u`, up to the same constant at every neck length: the
action filtration shift of the capping family between asymptotic orbits. -/
theorem IsNondegenerate.intervalIntegral_le_add_add_sum_of_cappedCylinderComponent
    {ι : Type*} (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hper : ∀ s, u (s, 1) = u (s, 0)) {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {a b : ι → ℝ} (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) {x_inf x₀ : ℝ → M}
    (hx_inf : ∀ t, Tendsto (fun i ↦ u (a i, t)) l (𝓝 (x_inf t)))
    (hx₀ : ∀ t, Tendsto (fun i ↦ u (b i, t)) l (𝓝 (x₀ t)))
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) (univ ×ˢ Icc 0 1))
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) (univ ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (univ ×ˢ Icc 0 1))
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, IsComplexLinearMap
      (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z).toLinearMap) :
    ∫ t in 0..1, Hb inf t (x_inf t) ≤
      (∫ z in univ ×ˢ Icc 0 1, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∫ t in 0..1, Hb zero t (x₀ t)) + Bb one + ∑ r, Bb r := by
  have hpos := setIntegral_nonneg (μ := volume) (MeasurableSet.univ.prod measurableSet_Icc)
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  rw [hω.integral_floerEnergyDensity_cappedCylinderComponent_univ_prod hHb hHbs hL hBb hu hper ha
    hb hx_inf hx₀ hE hA hR] at hpos
  linarith [(abs_le.1 (ω.abs_setIntegral_hamiltonianCurvature_cappedCylinderComponent_le hHb hHbs
    hL hBb u subset_rfl)).1]

/-- **The energy bound of the capped cylinder over the whole cylinder**, for a manifold target.
Under the hypotheses of
`IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_univ_prod`, the Floer energy of
`u` over the strip `ℝ × [0, 1]` is at most

`∫ u^*ω + ∫₀¹ Hb 0 (t, x₀(t)) dt - ∫₀¹ Hb ∞ (t, x_inf(t)) dt + Bb 1 + ∑ r, Bb r`.

For a disc `D` bounding the output loop `x_inf`, the first three terms are the capped action of the
input `x₀`, capped by `D` glued to `u`, minus that of the output capped by `D`. So the energy is
bounded by the change of capped action, up to the same constant at every neck length. -/
theorem IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_univ_prod_le
    {ι : Type*} (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hper : ∀ s, u (s, 1) = u (s, 0)) {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {a b : ι → ℝ} (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) {x_inf x₀ : ℝ → M}
    (hx_inf : ∀ t, Tendsto (fun i ↦ u (a i, t)) l (𝓝 (x_inf t)))
    (hx₀ : ∀ t, Tendsto (fun i ↦ u (b i, t)) l (𝓝 (x₀ t)))
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) (univ ×ˢ Icc 0 1))
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) (univ ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (univ ×ˢ Icc 0 1)) :
    ∫ z in univ ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z ≤
      (∫ z in univ ×ˢ Icc 0 1, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∫ t in 0..1, Hb zero t (x₀ t)) - (∫ t in 0..1, Hb inf t (x_inf t)) +
        Bb one + ∑ r, Bb r := by
  rw [hω.integral_floerEnergyDensity_cappedCylinderComponent_univ_prod hHb hHbs hL hBb hu hper ha
    hb hx_inf hx₀ hE hA hR]
  linarith [(abs_le.1 (ω.abs_setIntegral_hamiltonianCurvature_cappedCylinderComponent_le hHb hHbs
    hL hBb u subset_rfl)).1]

omit [FiniteDimensional ℝ E] in
/-- **The energy density of the capping family in the coordinates of the end at `0`**, for a
manifold target. If `u` is differentiable at `φ_0(ζ)`, the Floer energy density of `u ∘ φ_0` at
`ζ` for the capped datum on the cylinder is the Jacobian determinant of `φ_0` at `ζ` times the
energy density of `u` at `φ_0(ζ)` for the datum obtained by plumbing the negative plane with
Hamiltonian `Hb 1` into the input end at `1` of the pair of pants with Hamiltonians `Hb`. -/
theorem floerEnergyDensity_cappedCylinderComponent_comp_endChart (ω : SmoothTwoForm I M)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    {ζ : ℝ × ℝ} (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart zero ζ)) :
    ω.floerEnergyDensity (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I)
        (u ∘ endChart zero) ζ =
      (fderiv ℝ (endChart zero) ζ).det * ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u (endChart zero ζ) := by
  rw [← perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineReal,
    ← perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineImag]
  exact ω.floerEnergyDensity_perturbationPullback
    ((contDiff_endChart zero 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_plumbedPerturbation_single_inf (by simp) hHb hHbs hL
      (eq_endCenter_one_or_of_ne_zero (equivRealProdCLM_symm_endChart_zero_ne_zero ζ)) 1 _)
    (mdifferentiableAt_plumbedPerturbation_single_inf (by simp) hHb hHbs hL
      (eq_endCenter_one_or_of_ne_zero (equivRealProdCLM_symm_endChart_zero_ne_zero ζ))
      Complex.I _)

omit [FiniteDimensional ℝ E] in
/-- **The energy of the capping family in the coordinates of the end at `0`**, for a manifold
target. For period-one `C¹` Hamiltonians `Hb` and `L > 4`, and a map `u` differentiable at the
points of the image under the end chart of `0` of a measurable set `s` in a band
`ℝ × [t₀, t₀ + 1)`, the Floer energy of `u` over this image for the datum obtained by plumbing the
negative plane with Hamiltonian `Hb 1` into the input end at `1` of the pair of pants with
Hamiltonians `Hb` is the Floer energy of `u ∘ φ_0` over `s` for the capped datum on the
cylinder. -/
theorem integral_floerEnergyDensity_image_endChart_zero_plumbedPerturbation
    (ω : SmoothTwoForm I M) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) {t₀ : ℝ} (hst : s ⊆ univ ×ˢ Ico t₀ (t₀ + 1))
    (hu : ∀ ζ ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart zero ζ)) :
    ∫ z in endChart zero '' s, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ ζ in s, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) (u ∘ endChart zero) ζ := by
  rw [ω.integral_floerEnergyDensity_image hs ((injOn_endChart_univ_prod_Ico zero t₀).mono hst)
      (fun ζ _ ↦ (contDiff_endChart zero 1).differentiable one_ne_zero ζ)
      (fun ζ _ ↦ det_fderiv_endChart_nonneg zero ζ) hu
      (fun ζ _ ↦ mdifferentiableAt_plumbedPerturbation_single_inf (by simp) hHb hHbs hL
        (eq_endCenter_one_or_of_ne_zero (equivRealProdCLM_symm_endChart_zero_ne_zero ζ)) 1 _)
      (fun ζ _ ↦ mdifferentiableAt_plumbedPerturbation_single_inf (by simp) hHb hHbs hL
        (eq_endCenter_one_or_of_ne_zero (equivRealProdCLM_symm_endChart_zero_ne_zero ζ))
        Complex.I _),
    perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineReal,
    perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineImag]

omit [FiniteDimensional ℝ E] in
/-- **The capping family on the cylinder**, for a manifold target. For period-one `C¹`
Hamiltonians `Hb` and `L > 4`, if `u` is differentiable at `φ_0(ζ)` and solves the Floer equation
there for an almost complex structure `J` on `T_{u(φ_0 ζ)} M` and the datum obtained by plumbing
the negative plane with Hamiltonian `Hb 1` into the input end at `1` of the pair of pants with
Hamiltonians `Hb`, then `u ∘ φ_0` solves the Floer equation at `ζ` for `J` and the capped datum on
the cylinder: the end chart `φ_0` of `0` is holomorphic. -/
theorem isComplexLinearMap_perturbedMFDeriv_cappedCylinderComponent_comp_endChart
    (ω : SmoothTwoForm I M) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    {ζ : ℝ × ℝ} {J : AlmostComplexStructure (TangentSpace I (u (endChart zero ζ)))}
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart zero ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedMFDeriv
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u (endChart zero ζ)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) (u ∘ endChart zero) ζ).toLinearMap := by
  rw [← perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineReal,
    ← perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineImag]
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    ((contDiff_endChart zero 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_plumbedPerturbation_single_inf (by simp) hHb hHbs hL
      (eq_endCenter_one_or_of_ne_zero (equivRealProdCLM_symm_endChart_zero_ne_zero ζ)) 1 _)
    (mdifferentiableAt_plumbedPerturbation_single_inf (by simp) hHb hHbs hL
      (eq_endCenter_one_or_of_ne_zero (equivRealProdCLM_symm_endChart_zero_ne_zero ζ))
      Complex.I _)
    (isComplexLinearMap_fderiv_endChart zero ζ) hfloer

omit [FiniteDimensional ℝ E] in
/-- **The energy density of the capping family is integrable on the capped plane**, for a manifold
target. Let `u` be differentiable on a measurable subset `Ω` of the capped plane `ℂ ∖ {0}`, in
real coordinates. If the Floer energy density of `u ∘ φ_0` for the capped datum on the cylinder is
integrable over the strip `ℝ × [0, 1]`, then the energy density of `u` for the datum obtained by
plumbing the negative plane with Hamiltonian `Hb 1` into the input end at `1` of the pair of pants
with Hamiltonians `Hb` is integrable on `Ω`. -/
theorem integrableOn_floerEnergyDensity_plumbedPerturbation_single_inf (ω : SmoothTwoForm I M)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    {Ω : Set (ℝ × ℝ)} (hΩ : MeasurableSet Ω) (hΩS : ∀ z ∈ Ω, Complex.equivRealProdCLM.symm z ≠ 0)
    (hu : ∀ z ∈ Ω, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) (u ∘ endChart zero)) (univ ×ˢ Icc 0 1)) :
    IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (Complex.equivRealProdCLM.symm z) x Complex.I) u) Ω := by
  -- `Ω` is the image under the end chart of the part of the band `ℝ × [0, 1)` over it.
  set s : Set (ℝ × ℝ) := endChart zero ⁻¹' Ω ∩ univ ×ˢ Ico 0 1
  have hs : MeasurableSet s := (hΩ.preimage (contDiff_endChart zero 0).continuous.measurable).inter
    (MeasurableSet.univ.prod measurableSet_Ico)
  have hinj : InjOn (endChart zero) s :=
    (injOn_endChart_univ_prod_Ico zero 0).mono fun ζ hζ ↦ by simpa using hζ.2
  rw [← image_endChart_preimage_inter_univ_prod_Ico (q := zero) (Ω := Ω) (by simpa using hΩS),
    integrableOn_image_iff_of_eq_abs_det_smul (f := ω.floerEnergyDensity
      (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I)
      (u ∘ endChart zero)) hs hinj
      (fun ζ _ ↦ (contDiff_endChart zero 1).differentiable one_ne_zero ζ) fun ζ hζ ↦ by
        rw [ω.floerEnergyDensity_cappedCylinderComponent_comp_endChart hHb hHbs hL (hu _ hζ.1),
          abs_of_nonneg (det_fderiv_endChart_nonneg zero ζ), smul_eq_mul]]
  exact hE.mono_set fun ζ hζ ↦ ⟨mem_univ _, Ico_subset_Icc_self hζ.2.2⟩

/-- **The energy of the capping family on the capped plane**, for a manifold target. Let `ω` be a
nondegenerate two-form on a finite-dimensional manifold `M`, `Hb` bounded period-one `C¹`
Hamiltonians, `|Hb r| ≤ Bb r`, and `L > 4`. Let `u` be a `C¹` map on the capped plane `ℂ ∖ {0}`,
in real coordinates, solving the Floer equation there for almost complex structures `J z` on
`T_{u z} M` tamed by `ω` and the datum obtained by plumbing the negative plane with Hamiltonian
`Hb 1` into the input end at `1` of the pair of pants with Hamiltonians `Hb`, along a neck of
length `L`. Read `u` in the coordinates `(s, t)` of the end at `0`, which cover the capped plane,
and suppose that its loops `t ↦ u(s, t)` converge pointwise to `x₀` as `s → ∞` and to `x_inf` as
`s → -∞`, and that its energy, area and curvature densities in these coordinates are integrable
over the strip `ℝ × [0, 1]`. Then the Floer energy of `u` over every measurable subset `Ω` of the
capped plane is at most

`∫ (u ∘ φ_0)^*ω + ∫₀¹ Hb 0 (t, x₀(t)) dt - ∫₀¹ Hb ∞ (t, x_inf(t)) dt + Bb 1 + ∑ r, Bb r`,

whatever the neck length. For a disc `D` bounding `x_inf`, the first three terms are the capped
action of the input `x₀`, capped by `D` glued to `u`, minus the capped action of the output
`x_inf`, capped by `D`. -/
theorem IsNondegenerate.setIntegral_floerEnergyDensity_plumbedPerturbation_single_inf_le
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z | Complex.equivRealProdCLM.symm z ≠ 0})
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 0 → (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, Complex.equivRealProdCLM.symm z ≠ 0 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedMFDeriv
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    {x₀ x_inf : ℝ → M} (hx₀ : ∀ t, Tendsto (fun s ↦ u (endChart zero (s, t))) atTop (𝓝 (x₀ t)))
    (hx_inf : ∀ t, Tendsto (fun s ↦ u (endChart zero (s, t))) atBot (𝓝 (x_inf t)))
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) (u ∘ endChart zero)) (univ ×ˢ Icc 0 1))
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω ((u ∘ endChart zero) z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart zero) z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart zero) z stdComplexLineImag) : ℝ)) (univ ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z ((u ∘ endChart zero) z)) (univ ×ˢ Icc 0 1))
    {Ω : Set (ℝ × ℝ)} (hΩ : MeasurableSet Ω)
    (hΩS : ∀ z ∈ Ω, Complex.equivRealProdCLM.symm z ≠ 0) :
    ∫ z in Ω, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u z ≤
      (∫ z in univ ×ˢ Icc 0 1, (SmoothBundleForm.eval₂ ω ((u ∘ endChart zero) z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart zero) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart zero) z stdComplexLineImag) : ℝ)) +
        (∫ t in 0..1, Hb zero t (x₀ t)) - (∫ t in 0..1, Hb inf t (x_inf t)) +
        Bb one + ∑ r, Bb r := by
  set S : Set (ℝ × ℝ) := {z | Complex.equivRealProdCLM.symm z ≠ 0}
  have hS : IsOpen S := isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const
  have hφS (ζ : ℝ × ℝ) : endChart zero ζ ∈ S := equivRealProdCLM_symm_endChart_zero_ne_zero ζ
  have hud (ζ : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart zero ζ) :=
    (hu.contMDiffAt (hS.mem_nhds (hφS ζ))).mdifferentiableAt one_ne_zero
  -- `Ω` is the image under the end chart of the part `s` of the band `ℝ × [0, 1)` over it, so its
  -- energy is the energy of `u ∘ φ_0` over `s`, at most the energy over the strip.
  set s : Set (ℝ × ℝ) := endChart zero ⁻¹' Ω ∩ univ ×ˢ Ico 0 1
  have hs : MeasurableSet s := (hΩ.preimage (contDiff_endChart zero 0).continuous.measurable).inter
    (MeasurableSet.univ.prod measurableSet_Ico)
  have himage := ω.integral_floerEnergyDensity_image_endChart_zero_plumbedPerturbation hHb hHbs hL
    hs (t₀ := 0) (fun ζ hζ ↦ by simpa using hζ.2) fun ζ _ ↦ hud ζ
  rw [image_endChart_preimage_inter_univ_prod_Ico (q := zero) (by simpa using hΩS)] at himage
  rw [himage]
  refine (setIntegral_mono_set hE ((ae_restrict_mem (MeasurableSet.univ.prod
    measurableSet_Icc)).mono fun ζ _ ↦ floerEnergyDensity_nonneg hω (hJ _ (hφS ζ))
      (ω.isComplexLinearMap_perturbedMFDeriv_cappedCylinderComponent_comp_endChart hHb hHbs hL
        (hud ζ) (hfloer _ (hφS ζ))))
    (Eventually.of_forall fun ζ (hζ : ζ ∈ s) ↦ ⟨mem_univ _, Ico_subset_Icc_self hζ.2.2⟩)).trans ?_
  -- Along `a n = -n` and `b n = n` the loops converge to the asymptotic loops.
  exact hω.integral_floerEnergyDensity_cappedCylinderComponent_univ_prod_le hHb hHbs hL hBb
    (hu.comp_contMDiff (contDiff_endChart zero 1).contMDiff hφS)
    (fun σ ↦ by simpa using congrArg u (endChart_add_one zero σ 0)) (l := atTop)
    (a := fun n : ℕ ↦ -(n : ℝ)) (b := fun n : ℕ ↦ (n : ℝ))
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
    (fun t ↦ (hx_inf t).comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
    (fun t ↦ (hx₀ t).comp tendsto_natCast_atTop_atTop) hE hA hR

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Hb : Puncture → ℝ → V → ℝ} {L : ℝ} {Bb : Puncture → ℝ}

/-- **The integrated curvature of the capped cylinder is bounded uniformly in the neck length.**
For period-one `C¹` Hamiltonians with `|Hb r| ≤ Bb r` and neck length `L > 4`, along every map `u`
the integral of `|R_K(z, u(z))|` over one period `ℝ × [t₀, t₀ + 1)` of the cylinder is at most
`Bb 1 + ∑ r, Bb r`. -/
theorem lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (t₀ : ℝ) (u : ℝ × ℝ → V) :
    ∫⁻ z in univ ×ˢ Ico t₀ (t₀ + 1), ‖ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) z (u z)‖ₑ ≤
      ENNReal.ofReal (Bb one) + ∑ r, ENNReal.ofReal (Bb r) := by
  simpa using ω.constSmooth.lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le hHb
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hL hBb t₀ u

/-- **The energy identity of the capped cylinder.** Let `Hb` be period-one `C¹` Hamiltonians and
`L > 4`, and let `u` be `C²` on an open neighbourhood `U` of `[a, b] × [0, 1]`, with
`u(s, 1) = u(s, 0)` for `s ∈ [a, b]`. If `a ≤ -3` and `2 ≤ b`, then the Floer energy of `u` over
the rectangle for the capped datum on the cylinder is the action of the input loop at `s = b` for
`Hb 0`, minus the action of the output loop at `s = a` for `Hb ∞`, minus the integrated
curvature:

`∫ E = A_{H_0}(u(b, ·)) - A_{H_∞}(u(a, ·)) - ∫ R_K(u)`. -/
theorem integral_floerEnergyDensity_cappedCylinderComponent (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u U) {a b : ℝ}
    (ha : a ≤ -3) (hb : 2 ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z =
      ω.hamiltonianAction (Hb zero) (fun t ↦ u (b, t)) -
        ω.hamiltonianAction (Hb inf) (fun t ↦ u (a, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u z) :=
  ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral_hamiltonianCurvature hU hu
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL 1).contDiffOn
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL Complex.I).contDiffOn (by linarith) hRU
    hper (fun s _ ↦ by simpa using periodic_cappedCylinderComponent Hb L 1 s 0)
    (fun t _ ↦ funext fun x ↦ by
      rw [cappedCylinderComponent_of_le_neg_three (hHb inf) (by linarith) ha]
      simp)
    (fun t _ ↦ funext fun x ↦ by
      rw [cappedCylinderComponent_of_two_le (hHb zero) (by linarith) hb]
      simp)

/-- **The energy bound of the capped cylinder.** Under the hypotheses of
`TauCeti.SymplecticForm.integral_floerEnergyDensity_cappedCylinderComponent`, if `|Hb r| ≤ Bb r`,
then the Floer energy over `[a, b] × [0, 1]` differs from the change of action
`A_{H_0}(u(b, ·)) - A_{H_∞}(u(a, ·))` by at most `Bb 1 + ∑ r, Bb r`, uniformly in the neck length
and in `a` and `b`. -/
theorem abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u U) {a b : ℝ} (ha : a ≤ -3) (hb : 2 ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    |(∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z) -
      (ω.hamiltonianAction (Hb zero) (fun t ↦ u (b, t)) -
        ω.hamiltonianAction (Hb inf) (fun t ↦ u (a, t)))| ≤ Bb one + ∑ r, Bb r := by
  have hsub (x y : ℝ) : x - y - x = -y := by ring
  rw [integral_floerEnergyDensity_cappedCylinderComponent ω hHb hHbs hL hU hu ha hb hRU hper,
    hsub, abs_neg]
  simpa using ω.constSmooth.abs_setIntegral_hamiltonianCurvature_cappedCylinderComponent_le hHb
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hL hBb u
    (s := Icc a b ×ˢ Icc 0 1) (prod_mono (subset_univ _) subset_rfl)

/-- **The action bound of the capped cylinder.** Under the hypotheses of
`TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le`, if `u`
solves the Floer equation on the rectangle for almost complex structures tamed by `ω`, then the
action of the output loop at `s = a` is at most the action of the input loop at `s = b` plus
`Bb 1 + ∑ r, Bb r`. -/
theorem hamiltonianAction_le_add_add_sum_of_cappedCylinderComponent (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u U) {a b : ℝ} (ha : a ≤ -3) (hb : 2 ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (Hb inf) (fun t ↦ u (a, t)) ≤
      ω.hamiltonianAction (Hb zero) (fun t ↦ u (b, t)) + Bb one + ∑ r, Bb r := by
  have hE := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le ω hHb hHbs
    hL hBb hU hu ha hb hRU hper)).2
  linarith

/-- **The action bound of the capped cylinder at its ends.** Let `u` be `C²` on an open
neighbourhood `U` of `ℝ × [0, 1]`, with `u(s, 1) = u(s, 0)`, solving the Floer equation there for
the capped datum on the cylinder and almost complex structures tamed by `ω`. If the actions of the
loops `t ↦ u(s, t)` for `Hb ∞` tend to `a_∞` as `s → -∞` and those for `Hb 0` tend to `a_0` as
`s → ∞`, then `a_∞ ≤ a_0 + Bb 1 + ∑ r, Bb r`. -/
theorem le_add_add_sum_of_tendsto_hamiltonianAction_cappedCylinderComponent
    (ω : SymplecticForm V) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u U)
    (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s, u (s, 1) = u (s, 0))
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    {a₀ a_inf : ℝ}
    (hinf : Tendsto (fun s ↦ ω.hamiltonianAction (Hb inf) (fun t ↦ u (s, t))) atBot (𝓝 a_inf))
    (h₀ : Tendsto (fun s ↦ ω.hamiltonianAction (Hb zero) (fun t ↦ u (s, t))) atTop (𝓝 a₀)) :
    a_inf ≤ a₀ + Bb one + ∑ r, Bb r := by
  have hsub {a b : ℝ} : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  -- Compare the output loop at `s = -R` with the input loop at `s = R`, for `R ≥ 3`.
  have hbound : ∀ᶠ R in atTop, ω.hamiltonianAction (Hb inf) (fun t ↦ u (-R, t)) ≤
      ω.hamiltonianAction (Hb zero) (fun t ↦ u (R, t)) + Bb one + ∑ r, Bb r :=
    eventually_atTop.2 ⟨3, fun R hR ↦ hamiltonianAction_le_add_add_sum_of_cappedCylinderComponent
      ω hHb hHbs hL hBb hU hu (by linarith) (by linarith) (hsub.trans hRU) (fun s _ ↦ hper s)
      (fun z hz ↦ hJ z (hsub hz)) fun z hz ↦ hfloer z (hsub hz)⟩
  exact le_of_tendsto_of_tendsto (hinf.comp tendsto_neg_atTop_atBot)
    ((h₀.add_const _).add_const _) hbound

/-- **The energy of the capped cylinder over finite rectangles.** Let `Hb` be period-one `C¹`
Hamiltonians with `|Hb r| ≤ Bb r` and `L > 4`, and let `u` be `C²` on an open neighbourhood `U` of
`ℝ × [0, 1]`, with `u(s, 1) = u(s, 0)`, solving the Floer equation there for the capped datum on the
cylinder and almost complex structures tamed by `ω`. If the actions of the loops `t ↦ u(s, t)` for
`Hb 0` tend to `a₀` as `s → ∞` and those for `Hb ∞` tend to `a_∞` as `s → -∞`, then the Floer
energy of `u` over every rectangle `[a, b] × [0, 1]` is at most `a₀ - a_∞ + Bb 1 + ∑ r, Bb r`,
whatever the neck length. -/
theorem setIntegral_floerEnergyDensity_cappedCylinderComponent_le (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s, u (s, 1) = u (s, 0))
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    {a₀ a_inf : ℝ}
    (h₀ : Tendsto (fun s ↦ ω.hamiltonianAction (Hb zero) (fun t ↦ u (s, t))) atTop (𝓝 a₀))
    (hinf : Tendsto (fun s ↦ ω.hamiltonianAction (Hb inf) (fun t ↦ u (s, t))) atBot (𝓝 a_inf))
    (a b : ℝ) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z ≤ a₀ - a_inf + Bb one + ∑ r, Bb r := by
  have hsub {a b : ℝ} : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  have hEc : ContinuousOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) U :=
    ω.continuousOn_floerEnergyDensity hU (hu.of_le one_le_two)
      (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL 1).contDiffOn
      (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL Complex.I).contDiffOn
  -- Over a longer rectangle `[-n, n] × [0, 1]` the energy is within `Bb 1 + ∑ r, Bb r` of the
  -- change of action; let `n → ∞`.
  have hlim : Tendsto (fun n : ℝ ↦ ω.hamiltonianAction (Hb zero) (fun t ↦ u (n, t)) -
      ω.hamiltonianAction (Hb inf) (fun t ↦ u (-n, t)) + Bb one + ∑ r, Bb r) atTop
      (𝓝 (a₀ - a_inf + Bb one + ∑ r, Bb r)) :=
    ((h₀.sub (hinf.comp tendsto_neg_atTop_atBot)).add_const _).add_const _
  refine ge_of_tendsto hlim ((eventually_ge_atTop (max (max (-a) b) 3)).mono fun n hn ↦ ?_)
  have hn₃ : 3 ≤ n := (le_max_right _ _).trans hn
  have hab := (le_max_left _ _).trans hn
  have hn' : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ Icc (-n) n ×ˢ Icc 0 1 :=
    prod_mono (Icc_subset_Icc (by linarith [le_max_left (-a) b])
      (by linarith [le_max_right (-a) b])) subset_rfl
  refine (ω.setIntegral_floerEnergyDensity_mono_set hn' (measurableSet_Icc.prod measurableSet_Icc)
    ((hEc.mono (hsub.trans hRU)).integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (fun z hz ↦ hJ z (hsub hz)) fun z hz ↦ hfloer z (hsub hz)).trans ?_
  linarith [(abs_le.1 (abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le ω hHb hHbs
    hL hBb hU hu (a := -n) (b := n) (by linarith) (by linarith) (hsub.trans hRU)
    fun s _ ↦ hper s)).2]

/-- **The energy of the capped cylinder.** Under the hypotheses of
`TauCeti.SymplecticForm.setIntegral_floerEnergyDensity_cappedCylinderComponent_le`, the Floer energy
of `u` over the strip `ℝ × [0, 1]`, one period of the cylinder, is at most
`a₀ - a_∞ + Bb 1 + ∑ r, Bb r`, whatever the neck length `L > 4`. -/
theorem lintegral_floerEnergyDensity_cappedCylinderComponent_le (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s, u (s, 1) = u (s, 0))
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    {a₀ a_inf : ℝ}
    (h₀ : Tendsto (fun s ↦ ω.hamiltonianAction (Hb zero) (fun t ↦ u (s, t))) atTop (𝓝 a₀))
    (hinf : Tendsto (fun s ↦ ω.hamiltonianAction (Hb inf) (fun t ↦ u (s, t))) atBot (𝓝 a_inf)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity
        (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u z) ≤
      ENNReal.ofReal (a₀ - a_inf + Bb one + ∑ r, Bb r) := by
  have hsub {a b : ℝ} : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  have hE := ω.continuousOn_floerEnergyDensity hU (hu.of_le one_le_two)
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL 1).contDiffOn
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL Complex.I).contDiffOn
  -- The strip is exhausted by the rectangles `[-n, n] × [0, 1]`, each of energy at most the bound.
  refine le_of_tendsto' (tendsto_setLIntegral_Icc_neg_prod volume (Icc (0 : ℝ) 1) _) fun n ↦ ?_
  have hm : MeasurableSet (Icc (-(n : ℝ)) n ×ˢ Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hE.mono (hsub.trans hRU)).integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (ae_restrict_of_forall_mem hm fun z hz ↦
      ω.floerEnergyDensity_nonneg (hJ z (hsub hz)) (hfloer z (hsub hz)))]
  exact ENNReal.ofReal_le_ofReal (setIntegral_floerEnergyDensity_cappedCylinderComponent_le ω hHb
    hHbs hL hBb hU hu hRU hper hJ hfloer h₀ hinf (-n) n)

/-- **The energy of the capped cylinder over several periods.** Under the hypotheses of
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_cappedCylinderComponent_le`, if `u` has period
one in `t`, then its Floer energy over a set `Ω` lying in the `N` periods `ℝ × [m, m + N)` of the
cylinder is at most `N (a₀ - a_∞ + Bb 1 + ∑ r, Bb r)`, whatever the neck length `L > 4`. -/
theorem setLIntegral_floerEnergyDensity_cappedCylinderComponent_le
    (ω : SymplecticForm V) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u U)
    (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s t, u (s, t + 1) = u (s, t))
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    {a₀ a_inf : ℝ}
    (h₀ : Tendsto (fun s ↦ ω.hamiltonianAction (Hb zero) (fun t ↦ u (s, t))) atTop (𝓝 a₀))
    (hinf : Tendsto (fun s ↦ ω.hamiltonianAction (Hb inf) (fun t ↦ u (s, t))) atBot (𝓝 a_inf))
    {Ω : Set (ℝ × ℝ)} {m : ℤ} {N : ℕ} (hΩ : Ω ⊆ (univ : Set ℝ) ×ˢ Ico (m : ℝ) (m + N)) :
    ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity
        (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u z) ≤
      ENNReal.ofReal (N * (a₀ - a_inf + Bb one + ∑ r, Bb r)) := by
  -- The datum and the map, hence the energy density, have period one in `t`.
  have hK (v : ℂ) : Periodic (cappedCylinderComponent Hb L v) ((0 : ℝ), (1 : ℝ)) :=
    fun ⟨s, t⟩ ↦ by simpa using periodic_cappedCylinderComponent Hb L v s t
  have hE := ω.periodic_floerEnergyDensity (hK 1) (hK Complex.I) fun ⟨s, t⟩ ↦ by
    simpa using hper s t
  calc _ ≤ ∫⁻ z in (univ : Set ℝ) ×ˢ Ico (m : ℝ) (m + N), ENNReal.ofReal (ω.floerEnergyDensity
        (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u z) :=
        lintegral_mono_set hΩ
    _ = N * ∫⁻ z in (univ : Set ℝ) ×ˢ Ico 0 1, ENNReal.ofReal (ω.floerEnergyDensity
        (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u z) :=
        (hE.comp ENNReal.ofReal).setLIntegral_prod_Ico_intCast_add_natCast MeasurableSet.univ m N
    _ ≤ N * ENNReal.ofReal (a₀ - a_inf + Bb one + ∑ r, Bb r) := by
        gcongr
        exact (lintegral_mono_set (Set.prod_mono le_rfl Ico_subset_Icc_self)).trans
          (lintegral_floerEnergyDensity_cappedCylinderComponent_le ω hHb hHbs hL hBb hU hu hRU
            (fun s ↦ by simpa using hper s 0) hJ hfloer h₀ hinf)
    _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]

/-- **The energy of the capping family in the coordinates of the end at `0`.** For period-one `C¹`
Hamiltonians `Hb` and `L > 4`, and a map `u` differentiable at the points of the image under the end
chart of `0` of a measurable set `s` in a band `ℝ × [t₀, t₀ + 1)`, the Floer energy of `u` over this
image for the datum obtained by plumbing the negative plane with Hamiltonian `Hb 1` into the input
end at `1` of the pair of pants with Hamiltonians `Hb` is the Floer energy of `u ∘ φ_0` over `s` for
the capped datum on the cylinder. -/
theorem integral_floerEnergyDensity_image_endChart_zero_plumbedPerturbation (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) {t₀ : ℝ} (hst : s ⊆ univ ×ˢ Ico t₀ (t₀ + 1))
    {u : ℝ × ℝ → V} (hu : ∀ ζ ∈ s, DifferentiableAt ℝ u (endChart zero ζ)) :
    ∫ z in endChart zero '' s, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ ζ in s, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) (u ∘ endChart zero) ζ := by
  rw [ω.integral_floerEnergyDensity_image hs ((injOn_endChart_univ_prod_Ico zero t₀).mono hst)
      (fun ζ _ ↦ (contDiff_endChart zero 1).differentiable one_ne_zero ζ)
      (fun ζ _ ↦ det_fderiv_endChart_nonneg zero ζ) hu
      (fun ζ _ ↦ differentiableAt_plumbedPerturbation_endChart_zero hHb hHbs hL 1 ζ _)
      (fun ζ _ ↦ differentiableAt_plumbedPerturbation_endChart_zero hHb hHbs hL Complex.I ζ _),
    perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineReal,
    perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineImag]

/-- **The capping family on the cylinder.** For period-one `C¹` Hamiltonians `Hb` and `L > 4`, if
`u` is differentiable at `φ_0(ζ)` and solves the Floer equation there for an almost complex
structure `J` and the datum obtained by plumbing the negative plane with Hamiltonian `Hb 1` into
the input end at `1` of the pair of pants with Hamiltonians `Hb`, then `u ∘ φ_0` solves the Floer
equation at `ζ` for `J` and the capped datum on the cylinder: the end chart `φ_0` of `0` is
holomorphic. -/
theorem isComplexLinearMap_perturbedFDeriv_cappedCylinderComponent_comp_endChart
    (ω : SymplecticForm V) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L) {u : ℝ × ℝ → V}
    {J : AlmostComplexStructure V} {ζ : ℝ × ℝ} (hu : DifferentiableAt ℝ u (endChart zero ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u (endChart zero ζ) :
        ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) (u ∘ endChart zero) ζ : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [← perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineReal,
    ← perturbationPullback_endChart_zero_plumbedPerturbation_stdComplexLineImag]
  exact ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback
    ((contDiff_endChart zero 1).differentiable one_ne_zero ζ) hu
    (differentiableAt_plumbedPerturbation_endChart_zero hHb hHbs hL 1 ζ _)
    (differentiableAt_plumbedPerturbation_endChart_zero hHb hHbs hL Complex.I ζ _)
    (isComplexLinearMap_fderiv_endChart zero ζ) hfloer

/-- **The energy density of the capping family is continuous on the capped plane.** For
period-one `C¹` Hamiltonians `Hb`, neck length `L > 4` and a `C¹` map `u` on the capped plane
`ℂ ∖ {0}`, in real coordinates, the Floer energy density of `u` for the datum obtained by plumbing
the negative plane with Hamiltonian `Hb 1` into the input end at `1` of the pair of pants with
Hamiltonians `Hb` is continuous on the capped plane. -/
theorem continuousOn_floerEnergyDensity_plumbedPerturbation_single_inf (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 1 u {z | Complex.equivRealProdCLM.symm z ≠ 0}) :
    ContinuousOn (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z | Complex.equivRealProdCLM.symm z ≠ 0} := by
  have hK (v : ℂ) : ContDiffOn ℝ 1 (uncurry fun z x ↦ plumbedPerturbation
      (Pi.single inf (Hb one)) Hb one L (Complex.equivRealProdCLM.symm z) x v)
      ({z | Complex.equivRealProdCLM.symm z ≠ 0} ×ˢ univ) := by
    rintro ⟨z, x⟩ ⟨hz, -⟩
    exact (contDiffAt_uncurry_plumbedPerturbation_single_inf (by simp) hHb hHbs hL
      (eq_endCenter_one_or_of_ne_zero hz) x v).contDiffWithinAt
  exact ω.continuousOn_floerEnergyDensity
    (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const) hu (hK 1)
    (hK Complex.I)

/-- **The energy of the capping family on compact windows of the capped plane.** Let `Hb` be
period-one `C¹` Hamiltonians with `|Hb r| ≤ Bb r` and `L > 4`. Let `u` be a `C²` map on the
capped plane `ℂ ∖ {0}`, in real coordinates, solving the Floer equation there for almost complex
structures `J z` tamed by `ω` and the datum obtained by plumbing the negative plane with
Hamiltonian `Hb 1` into the input end at `1` of the pair of pants with Hamiltonians `Hb`, along a
neck of length `L`. Read `u` in the coordinates `(s, t)` of the end at `0`, which cover the capped
plane. If the actions for `Hb 0` of its loops `t ↦ u(s, t)` tend to `a₀` as `s → ∞`, and their
actions for `Hb ∞` tend to `a_∞` as `s → -∞`, then the Floer energy of `u` over every compact
subset `D` of the capped plane is at most `a₀ - a_∞ + Bb 1 + ∑ r, Bb r`, whatever the neck
length. -/
theorem setIntegral_floerEnergyDensity_plumbedPerturbation_single_inf_le (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z | Complex.equivRealProdCLM.symm z ≠ 0})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 0 → ω.Tames (J z))
    (hfloer : ∀ z, Complex.equivRealProdCLM.symm z ≠ 0 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    {a₀ a_inf : ℝ}
    (h₀ : Tendsto (fun s ↦ ω.hamiltonianAction (Hb zero) (fun t ↦ u (endChart zero (s, t))))
      atTop (𝓝 a₀))
    (hinf : Tendsto (fun s ↦ ω.hamiltonianAction (Hb inf) (fun t ↦ u (endChart zero (s, t))))
      atBot (𝓝 a_inf))
    {D : Set (ℝ × ℝ)} (hD : IsCompact D) (hDS : ∀ z ∈ D, Complex.equivRealProdCLM.symm z ≠ 0) :
    ∫ z in D, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u z ≤
      a₀ - a_inf + Bb one + ∑ r, Bb r := by
  set S : Set (ℝ × ℝ) := {z | Complex.equivRealProdCLM.symm z ≠ 0}
  have hS : IsOpen S := isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const
  -- The end chart of `0` maps the cylinder into the capped plane.
  have hφS (ζ : ℝ × ℝ) : endChart zero ζ ∈ S := equivRealProdCLM_symm_endChart_zero_ne_zero ζ
  have hud (ζ : ℝ × ℝ) : DifferentiableAt ℝ u (endChart zero ζ) :=
    (hu.contDiffAt (hS.mem_nhds (hφS ζ))).differentiableAt (by norm_num)
  have hfl (ζ : ℝ × ℝ) := ω.isComplexLinearMap_perturbedFDeriv_cappedCylinderComponent_comp_endChart
    hHb hHbs hL (hud ζ) (hfloer _ (hφS ζ))
  have hw := hu.comp_contDiff (contDiff_endChart zero 2) hφS
  -- The window `D` lies in the image of a band `[-N, N] × [0, 1)` of the cylinder, whose image is
  -- compact: closing the band does not change it.
  obtain ⟨N, hDR⟩ := exists_subset_image_endChart_Icc_prod_Ico (q := zero) hD fun z hz ↦ by
    rw [endCenter_zero]
    exact hDS z hz
  have hcpt : IsCompact (endChart zero '' (Icc (-N) N ×ˢ Ico 0 1)) :=
    image_endChart_prod_Icc_zero_one zero _ ▸
      (isCompact_Icc.prod isCompact_Icc).image (contDiff_endChart zero 0).continuous
  have hR : Icc (-N) N ×ˢ Ico (0 : ℝ) 1 ⊆ Icc (-N) N ×ˢ Icc 0 1 :=
    prod_mono subset_rfl Ico_subset_Icc_self
  -- The energy over `D` is at most the energy over the image of the band, which is the energy of
  -- the capped cylinder over the band, at most its energy over `[-N, N] × [0, 1]`.
  have hRS : endChart zero '' (Icc (-N) N ×ˢ Ico 0 1) ⊆ S := image_subset_iff.2 fun ζ _ ↦ hφS ζ
  refine (ω.setIntegral_floerEnergyDensity_mono_set hDR hcpt.isClosed.measurableSet
    (((ω.continuousOn_floerEnergyDensity_plumbedPerturbation_single_inf hHb hHbs hL
      (hu.of_le one_le_two)).mono hRS).integrableOn_compact hcpt)
    (fun z hz ↦ hJ z (hRS hz)) fun z hz ↦ hfloer z (hRS hz)).trans ?_
  rw [ω.integral_floerEnergyDensity_image_endChart_zero_plumbedPerturbation hHb hHbs hL
    (measurableSet_Icc.prod measurableSet_Ico) (t₀ := 0)
    (prod_mono (subset_univ _) (by rw [zero_add])) fun ζ _ ↦ hud ζ]
  refine (ω.setIntegral_floerEnergyDensity_mono_set hR (measurableSet_Icc.prod measurableSet_Icc)
    (((ω.continuousOn_floerEnergyDensity isOpen_univ (hw.of_le one_le_two).contDiffOn
      (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL 1).contDiffOn
      (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL Complex.I).contDiffOn).mono
        (subset_univ _)).integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (fun ζ _ ↦ hJ _ (hφS ζ)) fun ζ _ ↦ hfl ζ).trans ?_
  exact setIntegral_floerEnergyDensity_cappedCylinderComponent_le ω hHb hHbs hL hBb isOpen_univ
    hw.contDiffOn (subset_univ _) (fun s ↦ by simpa using congrArg u (endChart_add_one zero s 0))
    (fun ζ _ ↦ hJ _ (hφS ζ)) (fun ζ _ ↦ hfl ζ) h₀ hinf (-N) N

end TauCeti.SymplecticForm
