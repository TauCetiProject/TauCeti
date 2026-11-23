/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Floer.Manifold
import TauCeti.Geometry.Symplectic.Floer.Manifold.Rectangle
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Topology.Separation.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The energy identity on spheres with moving input ends

The associativity of the pair-of-pants product compares the two broken products through a family
of four-punctured spheres whose inputs sit at moving punctures of `ℂ`, carrying the perturbation
datum `TauCeti.Floer.puncturedSpherePerturbation` of input ends with centers `c i`, scales `a i`
and Hamiltonians `H i`, and of an output end at `∞` with Hamiltonian `Hout`. Finiteness of the
counts below each energy level over that family needs the energy identity of its maps, with
bounds uniform in the configuration of the input ends. This file proves it for a manifold target.

Suppose the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, and the scales are nonzero. For `R ≥ 1` the truncation `Σ_R`
(`TauCeti.ThricePuncturedSphere.puncturedSphereTruncation`) cuts the sphere along the circle
`s = R` of every input end and the circle `s = -R` of the output end. For a map `u` which is `C¹`
on an open set containing `Σ_R`, into a finite-dimensional manifold with a nondegenerate
two-form `ω`,

`∫_{Σ_R} E = ∫_{Σ_R} u^*ω + β(R - 1) (∑ i, ∫₀¹ H_i(t, u(φ_i(R + i t))) dt -`
`  ∫₀¹ Hout(t, u(φ_∞(-R + i t))) dt) - ∫_{Σ_R} R_K(u)`,

where `φ_i(z) = c i + a i φ₀(z)` is the end lift of the input `i`, `φ_∞` that of the output, and
`β = smoothTransition`, so `β(R - 1) = 1` for `R ≥ 2`. With `|H i| ≤ B i` and `|Hout| ≤ Bout`,
the energy therefore differs from its topological part by at most `∑ i, B i + Bout`, uniformly in
`R` and in the configuration.

Over the whole sphere minus its punctures, the plane minus the centers `c i`, the identity holds at
the asymptotic loops. If `u` is `C¹` there with integrable energy and area densities, and its loops
along the circles of the input end `i` and of the output end converge pointwise to loops `x i` and
`xout` as `R → ∞`, then

`∫ E = ∫ u^*ω + (∑ i, ∫₀¹ H_i(t, x_i(t)) dt - ∫₀¹ Hout(t, xout(t)) dt) - ∫ R_K(u)`.

The truncations exhaust the sphere minus its punctures
(`TauCeti.ThricePuncturedSphere.iUnion_puncturedSphereTruncation`), so the three integrals over
`Σ_R` converge to the integrals over the whole sphere, the curvature being integrable there by its
bound on the plane, and the Hamiltonian terms converge by dominated convergence. The resulting
energy bound and lower bound on the topological energy of a Floer solution are again uniform in the
configuration of the input ends.

The truncation is the disjoint union of the pieces `1 ≤ s ≤ R` of the input ends, the piece
`-R ≤ s ≤ -1` of the output end, and a core on which the datum vanishes nearby. In the coordinates
of each end the datum is the continuation datum `β(±s - 1) H(t) dt`, so each piece is handled by
the energy identity over the image of a rectangle,
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_image_of_perturbationPullback`.

The vector-space statements are the specializations to the constant form
`SymplecticForm.constSmooth` of a symplectic vector space.

## Main results

In the namespace `TauCeti.SmoothTwoForm`:

* `integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_truncation`: the curvature is
  integrable over `Σ_R` along any map continuous on `Σ_R`.
* `IsNondegenerate.integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation`: the
  Floer energy density is integrable over `Σ_R` along any map `C¹` near `Σ_R`.
* `IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation`: the energy
  identity on `Σ_R`.
* `IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`:
  the resulting energy bound, uniform in `R` and in the configuration.
* `IsNondegenerate.neg_sum_add_le_integral_add_of_puncturedSpherePerturbation_truncation`: for a
  solution of the Floer equation with tame almost complex structures, the area plus the Hamiltonian
  boundary terms is at least `-(∑ i, B i + Bout)`.
* `IsNondegenerate.setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le`: for such a
  solution, the energy over any part of `Σ_R` is at most the topological energy on `Σ_R` plus
  `∑ i, B i + Bout`; this is the energy bound that compactness of the family consumes.
* `integrableOn_hamiltonianCurvature_puncturedSpherePerturbation`: for bounded Hamiltonians, the
  curvature is integrable over the whole sphere minus its punctures along any map continuous there.
* `IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation`: the energy identity on
  the whole sphere minus its punctures, with the Hamiltonian terms at the asymptotic loops.
* `IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_sub_le` and
  `IsNondegenerate.neg_sum_add_le_integral_add_of_puncturedSpherePerturbation`: the resulting
  energy bound, and the lower bound on the topological energy of a Floer solution.

In the namespace `TauCeti.SymplecticForm`, for a symplectic vector space target:

* `integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation`: the Floer energy
  density is integrable over `Σ_R` along any map `C¹` near `Σ_R`.
* `abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`: the energy
  bound on `Σ_R`, uniform in `R` and in the configuration.
* `setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le`: for a solution of the Floer
  equation with tame almost complex structures, the energy over any part of `Σ_R` is at most the
  area plus the Hamiltonian boundary terms plus `∑ i, B i + Bout`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for operations on punctured spheres.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 8–10, on
  families of punctured surfaces with cylindrical ends and consistent perturbation data over them.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations on punctured surfaces.
-/

public section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti.Floer

open TauCeti.Complex (realChart realChart_equivRealProdCLM equivRealProdCLM_symm_realChart
  contDiff_realChart)

section Pieces

variable {ι : Type*} {c a : ι → ℂ} {R : ℝ}

/-- If the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in `‖w‖ ≤ 2 exp (2π)`, the
end lift of the input end `i`, in real coordinates, maps the strip `1 ≤ s ≤ R` into `Σ_R`. -/
private theorem mapsTo_realChart_add_mul_cylindricalEndLift
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (i : ι) :
    MapsTo (realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (Icc 1 R ×ˢ univ)
      (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) := fun z hz ↦ by
  refine mem_preimage.2 ?_
  rw [equivRealProdCLM_symm_realChart]
  exact add_mul_cylindricalEndLift_mem_puncturedSphereTruncation hsep hout
    (by simpa using hz.1.1) (by simpa using hz.1.2)

/-- If the discs `‖w - c i‖ < ‖a i‖ / 2` lie in `‖w‖ ≤ 2 exp (2π)`, the end chart of the output
end maps the strip `-R ≤ s ≤ -1` into `Σ_R`. -/
private theorem mapsTo_endChart_inf (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) :
    MapsTo (endChart inf) (Icc (-R) (-1) ×ˢ univ)
      (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) := fun z hz ↦ by
  refine mem_preimage.2 ?_
  rw [equivRealProdCLM_symm_endChart]
  exact cylindricalEndLift_inf_mem_puncturedSphereTruncation hout (by simpa using hz.1.1)
    (by simpa using hz.1.2)

/-- The pieces of the ends in the truncation `Σ_R` of a sphere with moving input ends, in real
coordinates: for `some i`, the image of the part `1 ≤ s ≤ R`, `t ∈ [-1/2, 1/2)` of the input end
`i` under its end lift `z ↦ c i + a i φ₀(z)`; for `none`, the image of the part `-R ≤ s ≤ -1`,
`t ∈ [-1/2, 1/2)` of the output end under its end chart. -/
private noncomputable abbrev movingEndPiece (c a : ι → ℂ) (R : ℝ) : Option ι → Set (ℝ × ℝ)
  | none => endChart inf '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1))
  | some i => realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ''
      (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1))

/-- The piece of the input end `i` lies in the disc `‖w - c i‖ ≤ ‖a i‖ exp (-2π) / 2`. -/
private theorem norm_sub_le_of_mem_movingEndPiece {i : ι} {z : ℝ × ℝ}
    (hz : z ∈ movingEndPiece c a R (some i)) :
    ‖Complex.equivRealProdCLM.symm z - c i‖ ≤ ‖a i‖ * Real.exp (-(2 * π)) / 2 := by
  obtain ⟨p, hp, rfl⟩ := hz
  simp only [equivRealProdCLM_symm_realChart, norm_add_mul_cylindricalEndLift_sub]
  have h₁ : 1 ≤ (Complex.equivRealProdCLM.symm p).re := by simpa using hp.1.1
  have h₂ : Real.exp (-(2 * π * (Complex.equivRealProdCLM.symm p).re)) ≤
      Real.exp (-(2 * π)) := Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  nlinarith [norm_nonneg (a i)]

/-- The piece of the output end lies outside the open disc `‖w‖ < 2 exp (2π)`. -/
private theorem le_norm_of_mem_movingEndPiece_none {z : ℝ × ℝ}
    (hz : z ∈ movingEndPiece c a R none) :
    2 * Real.exp (2 * π) ≤ ‖Complex.equivRealProdCLM.symm z‖ := by
  obtain ⟨p, hp, rfl⟩ := hz
  rw [equivRealProdCLM_symm_endChart]
  simpa using two_mul_exp_le_norm_cylindricalEndLift_inf (R := 1)
    (z := Complex.equivRealProdCLM.symm p) (by simpa using hp.1.2)

/-- The pieces of the ends lie in the truncation `Σ_R`. -/
private theorem movingEndPiece_subset
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (o : Option ι) :
    movingEndPiece c a R o ⊆
      Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R := by
  cases o with
  | none => exact fun _ ⟨p, hp, h⟩ ↦ h ▸ mapsTo_endChart_inf hout ⟨hp.1, mem_univ _⟩
  | some i =>
    exact fun _ ⟨p, hp, h⟩ ↦ h ▸ mapsTo_realChart_add_mul_cylindricalEndLift hsep hout i
      ⟨hp.1, mem_univ _⟩

/-- The pieces of the ends are measurable. -/
private theorem measurableSet_movingEndPiece (ha : ∀ i, a i ≠ 0) (o : Option ι) :
    MeasurableSet (movingEndPiece c a R o) := by
  cases o with
  | none =>
    exact measurable_image_of_fderivWithin (measurableSet_Icc.prod measurableSet_Ico)
      (fun w _ ↦ (hasFDerivAt_endChart inf w).hasFDerivWithinAt)
      ((injOn_endChart_univ_prod_Ico inf (-1 / 2)).mono (prod_mono (subset_univ _) subset_rfl))
  | some i =>
    have hΦ : ContDiff ℝ 1 (realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) :=
      contDiff_realChart (by fun_prop)
    exact measurable_image_of_fderivWithin (measurableSet_Icc.prod measurableSet_Ico)
      (fun w _ ↦ (hΦ.differentiable one_ne_zero w).hasFDerivAt.hasFDerivWithinAt)
      (injOn_realChart_add_mul_cylindricalEndLift (ha i))

/-- For nonzero scales, if the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the
disc `‖w‖ ≤ 2 exp (2π)`, then the pieces of the ends are pairwise disjoint. -/
private theorem pairwise_disjoint_movingEndPiece (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) :
    Pairwise (Disjoint on movingEndPiece c a R) := by
  have hdisj {i : ι} {z : ℝ × ℝ} (hz : z ∈ movingEndPiece c a R (some i))
      (hz' : z ∈ movingEndPiece c a R none) : False := by
    have htri : ‖Complex.equivRealProdCLM.symm z‖ ≤
        ‖c i‖ + ‖Complex.equivRealProdCLM.symm z - c i‖ := by
      simpa using norm_add_le (c i) (Complex.equivRealProdCLM.symm z - c i)
    linarith [norm_sub_le_of_mem_movingEndPiece hz, le_norm_of_mem_movingEndPiece_none hz',
      norm_mul_exp_neg_two_pi_div_two_lt (ha i), hout i]
  intro o o' hoo'
  rw [Function.onFun, Set.disjoint_left]
  intro z hz hz'
  cases o with
  | none =>
    cases o' with
    | none => exact hoo' rfl
    | some j => exact hdisj hz' hz
  | some i =>
    cases o' with
    | none => exact hdisj hz hz'
    | some j =>
      have hij : i ≠ j := fun h ↦ hoo' (h ▸ rfl)
      have htri := norm_sub_le_norm_sub_add_norm_sub (c i) (Complex.equivRealProdCLM.symm z) (c j)
      rw [norm_sub_rev (c i) (Complex.equivRealProdCLM.symm z)] at htri
      linarith [norm_sub_le_of_mem_movingEndPiece hz, norm_sub_le_of_mem_movingEndPiece hz',
        norm_mul_exp_neg_two_pi_div_two_lt (ha i), norm_mul_exp_neg_two_pi_div_two_lt (ha j),
        hsep hij]

/-- Off the pieces of the ends, a point of the truncation `Σ_R` lies at distance more than
`‖a i‖ exp (-2π) / 2` from every center `c i`, inside the open disc `‖w‖ < 2 exp (2π)`. -/
private theorem lt_norm_of_notMem_movingEndPiece (ha : ∀ i, a i ≠ 0) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ∈ puncturedSphereTruncation c a R)
    (hA : z ∉ ⋃ o, movingEndPiece c a R o) :
    (∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 < ‖Complex.equivRealProdCLM.symm z - c i‖) ∧
      ‖Complex.equivRealProdCLM.symm z‖ < 2 * Real.exp (2 * π) := by
  rw [mem_puncturedSphereTruncation] at hz
  have hIco : Ico (-1 / 2 : ℝ) (-1 / 2 + 1) = Ico (-1 / 2) (1 / 2) := by norm_num
  refine ⟨fun i ↦ ?_, ?_⟩
  · by_contra! h
    obtain ⟨ζ, hζre, hζim, hζ⟩ :=
      exists_add_mul_cylindricalEndLift_eq (r := 1) (ha i) (hz.1 i) (by rwa [mul_one])
    refine hA (mem_iUnion.2 ⟨some i, Complex.equivRealProdCLM ζ,
      ⟨by simpa using hζre, by rw [hIco]; simpa using hζim⟩, ?_⟩)
    simp only [realChart_equivRealProdCLM, hζ, ContinuousLinearEquiv.apply_symm_apply]
  · by_contra! h
    obtain ⟨ζ, hζre, hζim, hζ⟩ := exists_cylindricalEndLift_inf_eq (r := 1) (by rwa [mul_one]) hz.2
    refine hA (mem_iUnion.2 ⟨none, Complex.equivRealProdCLM ζ,
      ⟨by simpa using hζre, by rw [hIco]; simpa using hζim⟩, ?_⟩)
    simp only [endChart_apply, ContinuousLinearEquiv.symm_apply_apply, hζ,
      ContinuousLinearEquiv.apply_symm_apply]

/-- For nonzero scales, if the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the
disc `‖w‖ ≤ 2 exp (2π)`, then so do the smaller discs `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` containing
the parts `s ≥ 1` of the input ends. -/
private theorem separation_norm_mul_exp_neg_two_pi_div_two (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) :
    (Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖) ∧
      ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π) := by
  have hr (i : ι) := (norm_mul_exp_neg_two_pi_div_two_lt (ha i)).le
  exact ⟨fun i j hij ↦ by linarith [hr i, hr j, hsep hij], fun i ↦ by linarith [hr i, hout i]⟩

end Pieces

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer
open TauCeti.Complex (realChart equivRealProdCLM_symm_realChart contDiff_realChart
  det_fderiv_realChart_nonneg)

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}

omit [TopologicalSpace M] in
/-- On the part `s > 0` of the input end `i`, the datum of a sphere with moving input ends is the
continuation datum `β(s - 1) H_i(t) dt` in the coordinates of the end lift
`z ↦ c i + a i φ₀(z)`. -/
private theorem perturbationPullback_realChart_puncturedSpherePerturbation
    (hH : ∀ i, Periodic (H i) 1) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (i : ι) {w : ℝ × ℝ} (hw : 0 < w.1)
    (v : ℝ × ℝ) (x : M) :
    perturbationPullback (realChart fun z ↦ c i + a i * zero.cylindricalEndLift z)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) v w x =
      (Complex.equivRealProdCLM.symm v).im * (smoothTransition (w.1 - 1) * H i w.2 x) := by
  rw [perturbationPullback_realChart _ (hasDerivAt_add_mul_cylindricalEndLift _ _ _), mul_assoc,
    puncturedSpherePerturbation_cylindricalEndLift_of_pos hsep hout (hH i) (ha i)
      (by simpa using hw)]
  simp

omit [Fintype ι] in
/-- Points with `s ≤ -1` on the output end lie outside every disc
`‖w‖ ≤ ‖c i‖ + ‖a i‖ exp (-2π) / 2`, if the discs `‖w - c i‖ < ‖a i‖ / 2` lie in
`‖w‖ ≤ 2 exp (2π)` and the scales are nonzero. -/
private theorem lt_norm_cylindricalEndLift_inf (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {w : ℝ × ℝ} (hw : w.1 ≤ -1) (i : ι) :
    ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 <
      ‖inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)‖ := by
  have h₁ : 2 * Real.exp (2 * π) ≤ ‖inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)‖ := by
    simpa using two_mul_exp_le_norm_cylindricalEndLift_inf (R := 1)
      (z := Complex.equivRealProdCLM.symm w) (by simpa using hw)
  linarith [hout i, norm_mul_exp_neg_two_pi_div_two_lt (ha i)]

omit [Fintype ι] in
/-- The points of the output end outside every disc `‖w‖ ≤ ‖c i‖ + ‖a i‖ exp (-2π) / 2` form an open
set. -/
private theorem isOpen_setOf_lt_norm_cylindricalEndLift_inf [Finite ι] :
    IsOpen {w : ℝ × ℝ | ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 <
      ‖inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)‖} := by
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const
    ((inf.contDiff_cylindricalEndLift 0).continuous.comp
      Complex.equivRealProdCLM.symm.continuous).norm

omit [TopologicalSpace M] in
/-- On the part of the output end outside every disc `‖w‖ ≤ ‖c i‖ + ‖a i‖ exp (-2π) / 2`, the datum
of a sphere with moving input ends is the continuation datum `β(-s - 1) Hout(t) dt` in the
coordinates of the end chart. -/
private theorem perturbationPullback_endChart_inf_puncturedSpherePerturbation
    (hHout : Periodic Hout 1) {w : ℝ × ℝ}
    (hw : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 <
      ‖inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)‖) (v : ℝ × ℝ) (x : M) :
    perturbationPullback (endChart inf)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) v w x =
      (Complex.equivRealProdCLM.symm v).im * (smoothTransition (-w.1 - 1) * Hout w.2 x) := by
  rw [perturbationPullback_endChart_eq_cylindricalEndLift _ inf v]
  beta_reduce
  rw [puncturedSpherePerturbation_eq_negativePlanePerturbation fun i ↦ ?_,
    negativePlanePerturbation_cylindricalEndLift_apply hHout]
  · simp
  · linarith [hw i,
      norm_sub_norm_le (inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)) (c i)]

omit [Fintype ι] in
/-- The points of the output end outside every disc `‖w‖ ≤ ‖c i‖ + ‖a i‖ exp (-2π) / 2` are not
centers of input ends. -/
private theorem endChart_inf_ne {w : ℝ × ℝ}
    (hw : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 <
      ‖inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)‖) (j : ι) :
    Complex.equivRealProdCLM.symm (endChart inf w) ≠ c j := by
  rw [equivRealProdCLM_symm_endChart]
  intro h
  have := hw j
  rw [h] at this
  linarith [mul_nonneg (norm_nonneg (a j)) (Real.exp_pos (-(2 * π))).le]

omit [TopologicalSpace M] in
/-- For nonzero scales, the datum of a sphere with moving input ends vanishes near every point of
the truncation `Σ_R` off the pieces of the ends. -/
private theorem eventually_puncturedSpherePerturbation_eq_zero (ha : ∀ i, a i ≠ 0) {R : ℝ}
    {z : ℝ × ℝ} (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R)
    (hA : z ∉ ⋃ o, movingEndPiece c a R o) :
    ∀ᶠ w in 𝓝 z,
      puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm w) = fun _ ↦ 0 := by
  have hO : IsOpen {w : ℝ × ℝ | (∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 <
      ‖Complex.equivRealProdCLM.symm w - c i‖) ∧
      ‖Complex.equivRealProdCLM.symm w‖ < 2 * Real.exp (2 * π)} := by
    simp only [ofPred_and, ofPred_forall]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt (by fun_prop) continuous_const)
  exact eventually_of_mem (hO.mem_nhds (lt_norm_of_notMem_movingEndPiece ha hz hA)) fun _ hw ↦
    puncturedSpherePerturbation_eq_zero_of_le_norm_sub_of_norm_le (fun i ↦ (hw.1 i).le) hw.2.le

/-- For nonzero scales, the curvature of the datum of a sphere with moving input ends vanishes at
the points of the truncation `Σ_R` off the pieces of the ends. -/
private theorem hamiltonianCurvature_puncturedSpherePerturbation_eq_zero (ω : SmoothTwoForm I M)
    (ha : ∀ i, a i ≠ 0) {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R)
    (hA : z ∉ ⋃ o, movingEndPiece c a R o) (x : M) :
    ω.hamiltonianCurvature
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) z x = 0 :=
  have h := eventually_puncturedSpherePerturbation_eq_zero (H := H) (Hout := Hout) ha hz hA
  ω.hamiltonianCurvature_eq_zero_of_eventuallyEq_zero
    (h.mono fun w hw ↦ funext fun x ↦ by simp [hw])
    (h.mono fun w hw ↦ funext fun x ↦ by simp [hw]) x

/-- For nonzero scales, at the points of the truncation `Σ_R` off the pieces of the ends, the Floer
energy density of the datum of a sphere with moving input ends is the symplectic area density. -/
private theorem floerEnergyDensity_puncturedSpherePerturbation_eq (ω : SmoothTwoForm I M)
    (ha : ∀ i, a i ≠ 0) {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R)
    (hA : z ∉ ⋃ o, movingEndPiece c a R o) (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) := by
  have hK := (eventually_puncturedSpherePerturbation_eq_zero (H := H) (Hout := Hout) ha hz
    hA).self_of_nhds
  exact ω.floerEnergyDensity_of_eq_zero u (funext fun x ↦ by simp [hK])
    (funext fun x ↦ by simp [hK])

/-- The curvature is integrable over the image of a rectangle `[a₁, b₁] × [-1/2, 1/2)` under a
change of coordinates `φ`, `C²` on an open set `U` containing the closed rectangle, along which
the datum of a sphere with moving input ends is the continuation datum `P(s) H(t) dt` and whose
image avoids the centers of the input ends, for a map `u` continuous on a set containing the image
of the closed rectangle. -/
private theorem integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_image
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    {u : ℝ × ℝ → M} {V : Set (ℝ × ℝ)} (hu : ContinuousOn u V)
    {φ : ℝ × ℝ → ℝ × ℝ} {P : ℝ → ℝ} {Hφ : ℝ → M → ℝ} {U : Set (ℝ × ℝ)} (hUo : IsOpen U)
    (hφ : ContDiffOn ℝ 2 φ U) (hdet : ∀ w ∈ U, 0 ≤ (fderiv ℝ φ w).det)
    (hne : ∀ w ∈ U, ∀ i, Complex.equivRealProdCLM.symm (φ w) ≠ c i)
    (hpull : ∀ w ∈ U, ∀ v x, perturbationPullback φ
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) v w x =
      (Complex.equivRealProdCLM.symm v).im * (P w.1 * Hφ w.2 x))
    (hP : ContDiff ℝ 1 P) (hHφ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hφ)) {a₁ b₁ : ℝ}
    (hUV : MapsTo φ (Icc a₁ b₁ ×ˢ Icc (-1 / 2 : ℝ) (-1 / 2 + 1)) V)
    (hrect : Icc a₁ b₁ ×ˢ Icc (-1 / 2 : ℝ) (-1 / 2 + 1) ⊆ U)
    (hinj : InjOn φ (Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1))) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z))
      (φ '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1))) :=
  ω.integrableOn_hamiltonianCurvature_image_of_perturbationPullback hUo hφ hdet hUV hu
    (fun w hw x ↦ (contMDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha
      (hne w hw) x 1).mdifferentiableAt one_ne_zero)
    (fun w hw x ↦ (contMDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha
      (hne w hw) x Complex.I).mdifferentiableAt one_ne_zero)
    (fun w hw ↦ funext fun x ↦ by rw [hpull w hw]; simp)
    (fun w hw ↦ funext fun x ↦ by rw [hpull w hw]; simp) hP hHφ hrect hinj

/-- Along a map `u` continuous on the truncation `Σ_R`, the curvature is integrable over the piece
`1 ≤ s ≤ R` of the input end `i`. -/
private theorem integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_inputPiece
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    (hu : ContinuousOn u (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R))
    (i : ι) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z))
      (movingEndPiece c a R (some i)) :=
  ω.integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_image hH hHs hHout hHouts ha hu
    (U := {w | 1 / 2 < w.1}) (P := fun s ↦ smoothTransition (s - 1))
    (isOpen_lt continuous_const continuous_fst) (contDiff_realChart (by fun_prop)).contDiffOn
    (fun _ _ ↦ det_fderiv_realChart_nonneg (hasDerivAt_add_mul_cylindricalEndLift _ _ _))
    (fun w (hw : 1 / 2 < w.1) j ↦ by
      rw [equivRealProdCLM_symm_realChart]
      exact add_mul_cylindricalEndLift_ne hsep (ha i) (by simp; linarith) j)
    (fun _ (hw : 1 / 2 < _) ↦
      perturbationPullback_realChart_puncturedSpherePerturbation hH ha hsep hout i (by linarith))
    (smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)) (hHs i)
    ((mapsTo_realChart_add_mul_cylindricalEndLift hsep hout i).mono_left
      (prod_mono subset_rfl (subset_univ _)))
    (fun _ hz ↦ mem_ofPred.2 <| by linarith [hz.1.1])
    (injOn_realChart_add_mul_cylindricalEndLift (ha i))

/-- Along a map `u` continuous on the truncation `Σ_R`, the curvature is integrable over the piece
`-R ≤ s ≤ -1` of the output end. -/
private theorem integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_outputPiece
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    (hu : ContinuousOn u (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R)) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z))
      (movingEndPiece c a R none) :=
  ω.integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_image hH hHs hHout hHouts ha hu
    (P := fun s ↦ smoothTransition (-s - 1)) isOpen_setOf_lt_norm_cylindricalEndLift_inf
    (contDiff_endChart inf 2).contDiffOn (fun w _ ↦ det_fderiv_endChart_nonneg inf w)
    (fun _ hw ↦ endChart_inf_ne hw)
    (fun _ hw ↦ perturbationPullback_endChart_inf_puncturedSpherePerturbation hHout hw)
    (smoothTransition.contDiff.comp (contDiff_neg.sub contDiff_const)) hHouts
    ((mapsTo_endChart_inf hout).mono_left (prod_mono subset_rfl (subset_univ _)))
    (fun _ hz i ↦ lt_norm_cylindricalEndLift_inf ha hout hz.1.2 i)
    ((injOn_endChart_univ_prod_Ico inf (-1 / 2)).mono (prod_mono (subset_univ _) subset_rfl))

/-- **The curvature is integrable over the truncated sphere with moving input ends.** Let `K` be
the datum `puncturedSpherePerturbation c a H Hout` of input ends with centers `c i`, nonzero
scales `a i` and period-one `C¹` Hamiltonians `H i`, and of the output end at `∞` with the
period-one `C¹` Hamiltonian `Hout`, and suppose the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise
disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`. Along a map `u` continuous on the truncation
`Σ_R`, the curvature `R_K(u)` is integrable over `Σ_R`. Nothing is assumed about `u` off `Σ_R`. -/
theorem integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_truncation
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    (hu : ContinuousOn u (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R)) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z))
      (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) := by
  -- The curvature is integrable on each piece of the ends, and vanishes off them.
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := ⋃ o, movingEndPiece c a R o)
    (integrableOn_finite_iUnion.2 fun o ↦ ?_)
    ((isCompact_puncturedSphereTruncation c a R).isClosed.preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet
    fun z hz ↦ ω.hamiltonianCurvature_puncturedSpherePerturbation_eq_zero ha hz.1 hz.2 _
  cases o with
  | none =>
    exact ω.integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_outputPiece hH hHs hHout
      hHouts ha hout hu
  | some i =>
    exact ω.integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_inputPiece hH hHs hHout
      hHouts ha hsep hout hu i

omit [Fintype ι] in
/-- The truncations `Σ_R` of a sphere with moving input ends, read in real coordinates, exhaust the
sphere minus its punctures: the points of the plane other than the centers of the input ends. -/
private theorem iUnion_preimage_puncturedSphereTruncation [Finite ι] (ha : ∀ i, a i ≠ 0) :
    ⋃ R : ℝ, Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R =
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} := by
  rw [← preimage_iUnion, iUnion_puncturedSphereTruncation ha, preimage_ofPred_eq]

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- The energy identity over the image of a rectangle `[a₁, b₁] × [-1/2, 1/2)` under a change of
coordinates `φ`, `C²` on an open set `U` containing the closed rectangle, along which the datum of
a sphere with moving input ends is the continuation datum `P(s) H(t) dt` and whose image avoids
the centers of the input ends, for a map `u` which is `C¹` on an open set containing `φ(U)`. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_image
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    {u : ℝ × ℝ → M} {V : Set (ℝ × ℝ)} (hVo : IsOpen V) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V)
    {φ : ℝ × ℝ → ℝ × ℝ} {P : ℝ → ℝ} {Hφ : ℝ → M → ℝ} {U : Set (ℝ × ℝ)} (hUo : IsOpen U)
    (hφ : ContDiffOn ℝ 2 φ U) (hdet : ∀ w ∈ U, 0 ≤ (fderiv ℝ φ w).det) (hUV : MapsTo φ U V)
    (hne : ∀ w ∈ U, ∀ i, Complex.equivRealProdCLM.symm (φ w) ≠ c i)
    (hpull : ∀ w ∈ U, ∀ v x, perturbationPullback φ
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) v w x =
      (Complex.equivRealProdCLM.symm v).im * (P w.1 * Hφ w.2 x))
    (hP : ContDiff ℝ 1 P) (hHφ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hφ))
    {a₁ b₁ : ℝ} (hab : a₁ ≤ b₁) (hrect : Icc a₁ b₁ ×ˢ Icc (-1 / 2 : ℝ) (-1 / 2 + 1) ⊆ U)
    (hinj : InjOn φ (Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1))) :
    ∫ z in φ '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in φ '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (P b₁ * (∫ t in (-1 / 2 : ℝ)..-1 / 2 + 1, Hφ t (u (φ (b₁, t)))) -
          P a₁ * ∫ t in (-1 / 2 : ℝ)..-1 / 2 + 1, Hφ t (u (φ (a₁, t)))) -
        ∫ z in φ '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
          ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) :=
  hω.integral_floerEnergyDensity_image_of_perturbationPullback hUo hVo hφ hdet hUV hu
    (fun w hw x ↦ (contMDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha
      (hne w hw) x 1).mdifferentiableAt one_ne_zero)
    (fun w hw x ↦ (contMDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha
      (hne w hw) x Complex.I).mdifferentiableAt one_ne_zero)
    (fun w hw ↦ funext fun x ↦ by rw [hpull w hw]; simp)
    (fun w hw ↦ funext fun x ↦ by rw [hpull w hw]; simp) hP hHφ hab (by norm_num) hrect hinj

/-- The energy identity on the piece `1 ≤ s ≤ R`, `t ∈ [-1/2, 1/2)` of the input end `i` of a
sphere with moving input ends, in the coordinates of its end lift `z ↦ c i + a i φ₀(z)`. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_inputPiece
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) (i : ι) :
    ∫ z in movingEndPiece c a R (some i), ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in movingEndPiece c a R (some i),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
          (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
        ∫ z in movingEndPiece c a R (some i), ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) := by
  have hUo : IsOpen {w : ℝ × ℝ | 1 / 2 < w.1 ∧
      realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) w ∈ V} :=
    (isOpen_lt continuous_const continuous_fst).inter
      (hVo.preimage (contDiff_realChart (n := 0) (by fun_prop)).continuous)
  have h := hω.integral_floerEnergyDensity_puncturedSpherePerturbation_image
    (P := fun s ↦ smoothTransition (s - 1)) hH hHs hHout hHouts ha hVo hu hUo
    (contDiff_realChart (by fun_prop)).contDiffOn
    (fun _ _ ↦ det_fderiv_realChart_nonneg (hasDerivAt_add_mul_cylindricalEndLift _ _ _))
    (fun _ hw ↦ hw.2)
    (fun w hw j ↦ by
      rw [equivRealProdCLM_symm_realChart]
      exact add_mul_cylindricalEndLift_ne hsep (ha i) (by simp; linarith [hw.1]) j)
    (fun _ hw ↦
      perturbationPullback_realChart_puncturedSpherePerturbation hH ha hsep hout i
        (by linarith [hw.1]))
    (smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)) (hHs i) hR
    (fun z hz ↦ ⟨by linarith [hz.1.1],
      hTV (mapsTo_realChart_add_mul_cylindricalEndLift hsep hout i ⟨hz.1, mem_univ _⟩)⟩)
    (injOn_realChart_add_mul_cylindricalEndLift (ha i))
  -- The boundary circle `s = R` is moved to `t ∈ [0, 1]` by periodicity.
  have hloop : ∫ t in (-1 / 2 : ℝ)..-1 / 2 + 1,
      H i t (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (R, t))) =
      ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
        (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) := by
    simp only [TauCeti.Complex.realChart_apply, Complex.equivRealProdCLM_symm_apply]
    exact (Periodic.intervalIntegral_add_eq (fun t ↦ by
      simp only [zero.periodic_cylindricalEndLift R t, hH i t]) (-1 / 2) 0).trans (by rw [zero_add])
  rw [hloop, sub_self, smoothTransition.zero, zero_mul, sub_zero] at h
  exact h

/-- The energy identity on the piece `-R ≤ s ≤ -1`, `t ∈ [-1/2, 1/2)` of the output end of a
sphere with moving input ends, in the coordinates of its end lift. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_outputPiece
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) :
    ∫ z in movingEndPiece c a R none, ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in movingEndPiece c a R none,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
          (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
        ∫ z in movingEndPiece c a R none, ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) := by
  have h := hω.integral_floerEnergyDensity_puncturedSpherePerturbation_image
    (P := fun s ↦ smoothTransition (-s - 1)) hH hHs hHout hHouts ha hVo hu
    (isOpen_setOf_lt_norm_cylindricalEndLift_inf.inter
      (hVo.preimage (contDiff_endChart inf 0).continuous))
    (contDiff_endChart inf 2).contDiffOn (fun w _ ↦ det_fderiv_endChart_nonneg inf w)
    (fun _ hw ↦ hw.2) (fun _ hw ↦ endChart_inf_ne hw.1)
    (fun _ hw ↦ perturbationPullback_endChart_inf_puncturedSpherePerturbation hHout hw.1)
    (smoothTransition.contDiff.comp (contDiff_neg.sub contDiff_const)) hHouts (by linarith)
    (fun z hz ↦ ⟨fun i ↦ lt_norm_cylindricalEndLift_inf ha hout hz.1.2 i,
      hTV (mapsTo_endChart_inf hout ⟨hz.1, mem_univ _⟩)⟩)
    ((injOn_endChart_univ_prod_Ico inf (-1 / 2)).mono (prod_mono (subset_univ _) subset_rfl))
  -- The boundary circle `s = -R` is moved to `t ∈ [0, 1]` by periodicity.
  have hloop : ∫ t in (-1 / 2 : ℝ)..-1 / 2 + 1, Hout t (u (endChart inf (-R, t))) =
      ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) := by
    simp only [endChart_apply, Complex.equivRealProdCLM_symm_apply]
    exact (Periodic.intervalIntegral_add_eq (fun t ↦ by
      simp only [inf.periodic_cylindricalEndLift (-R) t, hHout t]) (-1 / 2) 0).trans
      (by rw [zero_add])
  rw [hloop] at h
  simp only [neg_neg, sub_self, smoothTransition.zero, zero_mul, zero_sub] at h
  refine h.trans ?_
  ring

/-- For a map `u` which is `C¹` on an open set containing the truncation `Σ_R`, the Floer energy
density of the datum of a sphere with moving input ends is integrable over `Σ_R`. -/
theorem
    IsNondegenerate.integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u)
      (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) := by
  have hKP (v : ℂ) : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        v) ((V ∩ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) ×ˢ univ) :=
    fun p hp ↦ (contMDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hp.1.2
      p.2 v).contMDiffWithinAt
  exact hω.integrableOn_floerEnergyDensity
    (hVo.inter (isOpen_forall_ne Complex.equivRealProdCLM.symm.continuous))
    (hu.mono inter_subset_left) (hKP 1) (hKP Complex.I)
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_puncturedSphereTruncation c a R))
    (subset_inter hTV fun z hz i ↦ ne_of_mem_puncturedSphereTruncation (ha i) hz)
    (ω.integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_truncation hH hHs hHout hHouts
      ha hsep hout (hu.continuousOn.mono hTV))

/-- **The energy identity on the truncated sphere with moving input ends, for a manifold
target.** Let `K` be the datum `puncturedSpherePerturbation c a H Hout` of input ends with centers
`c i`, nonzero scales `a i` and period-one `C¹` Hamiltonians `H i` on a finite-dimensional
manifold with a nondegenerate two-form, and of the output end at `∞` with the period-one `C¹`
Hamiltonian `Hout`. Write its components in the global coordinate `z = s + i t` of `ℂ` as
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Suppose the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise
disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, and let `u` be `C¹` on an open set `V` containing
the truncation `Σ_R`, `R ≥ 1`. Then the Floer energy over `Σ_R` is the symplectic area, plus
`β(R - 1)` times the integrals of the input Hamiltonians along the circles `s = R` of the input
ends minus that of the output Hamiltonian along the circle `s = -R` of the output end, minus the
integrated curvature. The densities are integrable over `Σ_R` automatically, and nothing is assumed
about `u` off `V`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R, ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
              Complex.I) z (u z) := by
  classical
  -- The truncation `T` is the disjoint union of the pieces of the ends, indexed by `Option ι` with
  -- `none` the output end, and of the core `C`, near which the datum vanishes.
  set T := Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R
  set C := T \ ⋃ o, movingEndPiece c a R o
  have hT : IsCompact T :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_puncturedSphereTruncation c a R)
  have hAm := measurableSet_movingEndPiece (c := c) (R := R) ha
  have hCm : MeasurableSet C := hT.isClosed.measurableSet.diff (MeasurableSet.iUnion hAm)
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f T) :
      ∫ z in T, f z = (∫ z in C, f z) + ∑ o, ∫ z in movingEndPiece c a R o, f z :=
    setIntegral_eq_setIntegral_sdiff_iUnion_add_sum hAm
      (pairwise_disjoint_movingEndPiece ha hsep hout) (movingEndPiece_subset hsep hout) hf
  -- The densities are integrable over the truncation.
  have harea := ω.integrableOn_eval₂_mfderiv hVo hu hT hTV stdComplexLineReal stdComplexLineImag
  have hcurv := ω.integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_truncation hH hHs
    hHout hHouts ha hsep hout (hu.continuousOn.mono hTV)
  have hE := hω.integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation hH hHs hHout
    hHouts ha hsep hout hVo hTV hu
  -- On the core the energy is the area, and the curvature vanishes.
  have hCE : ∫ z in C, ω.floerEnergyDensity
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u z =
      ∫ z in C, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) :=
    setIntegral_congr_fun hCm fun z hz ↦
      ω.floerEnergyDensity_puncturedSpherePerturbation_eq ha hz.1 hz.2 u
  rw [hsplit _ hE, hsplit _ harea, hsplit _ hcurv, hCE,
    setIntegral_eq_zero_of_forall_eq_zero fun z (hz : z ∈ C) ↦
      ω.hamiltonianCurvature_puncturedSpherePerturbation_eq_zero ha hz.1 hz.2 _,
    Fintype.sum_option, Fintype.sum_option, Fintype.sum_option,
    hω.integral_floerEnergyDensity_puncturedSpherePerturbation_outputPiece hH hHs hHout hHouts ha
      hout hVo hTV hu hR,
    Finset.sum_congr rfl fun i _ ↦
      hω.integral_floerEnergyDensity_puncturedSpherePerturbation_inputPiece hH hHs hHout hHouts ha
        hsep hout hVo hTV hu hR i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **The energy bound on the truncated sphere with moving input ends, for a manifold target.**
Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation`,
if the Hamiltonians are bounded, `|H i| ≤ B i` and `|Hout| ≤ Bout`, then the Floer energy over the
truncation `Σ_R` differs from the symplectic area plus the Hamiltonian boundary terms by at most
`∑ i, B i + Bout`, uniformly in `R` and in the configuration of the input ends. -/
theorem
    IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))))| ≤ ∑ i, B i + Bout := by
  have hsub (x y z : ℝ) : x + y - z - x - y = -z := by ring
  rw [hω.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation hH hHs hHout hHouts ha
    hsep hout hVo hTV hu hR, hsub, abs_neg]
  -- The supports of the input end data lie in the discs `‖w - c i‖ < ‖a i‖ / 2`.
  obtain ⟨hsep', hout'⟩ := separation_norm_mul_exp_neg_two_pi_div_two ha hsep hout
  exact ω.abs_setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_le hH hHs hHout hHouts ha
    hsep' hout' hB hBout u _


/-- **The topological energy of a solution on a sphere with moving input ends is bounded below,
for a manifold target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on the truncation
`Σ_R` for almost complex structures `J z` on the tangent spaces `T_{u(z)} M` tamed by the two-form,
under the hypotheses of
`IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`.
Since its energy is nonnegative, its symplectic area over `Σ_R` plus the Hamiltonian terms of the
boundary circles is at least `-(∑ i, B i + Bout)`, whatever the configuration of the input ends. -/
theorem IsNondegenerate.neg_sum_add_le_integral_add_of_puncturedSpherePerturbation_truncation
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z).toLinearMap) :
    -(∑ i, B i + Bout) ≤
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) := by
  have hT : IsCompact (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_puncturedSphereTruncation c a R)
  have hE := setIntegral_nonneg (μ := volume) hT.isClosed.measurableSet fun z hz ↦
    floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (hω.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le hH hHs hHout
      hHouts ha hsep hout hB hBout hVo hTV hu hR)).2
  linarith

/-- **The energy of a solution over part of the truncated sphere with moving input ends is
bounded by its topological energy, for a manifold target.** Let `u` solve the Floer equation
`(du - X_K)^{0,1} = 0` on the truncation `Σ_R` for almost complex structures `J z` on the tangent
spaces `T_{u(z)} M` tamed by the two-form, under the hypotheses of
`IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`.
Then the Floer energy of `u` over every subset `S ⊆ Σ_R` is at most its symplectic area over
`Σ_R` plus the Hamiltonian terms of the boundary circles, plus `∑ i, B i + Bout`, whatever the
configuration of the input ends. -/
theorem IsNondegenerate.setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z).toLinearMap)
    {S : Set (ℝ × ℝ)}
    (hST : S ⊆ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) :
    ∫ z in S, ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z ≤
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) + (∑ i, B i + Bout) := by
  have hT : IsCompact (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_puncturedSphereTruncation c a R)
  -- The energy density is nonnegative on `Σ_R`, so the energy over `S` is at most that over `Σ_R`.
  have hmono := setIntegral_mono_set
    (hω.integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation hH hHs hHout hHouts
      ha hsep hout hVo hTV hu)
    (ae_restrict_of_forall_mem hT.isClosed.measurableSet fun z hz ↦
      floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz))
    (Eventually.of_forall hST)
  have h := (abs_le.1
    (hω.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le hH hHs hHout
      hHouts ha hsep hout hB hBout hVo hTV hu hR)).2
  linarith

omit [FiniteDimensional ℝ E] in
/-- **The curvature is integrable over the whole sphere with moving input ends.** For bounded
period-one `C¹` Hamiltonians `H i` and `Hout` on a manifold, nonzero scales, and discs
`‖w - c i‖ < ‖a i‖ / 2` pairwise disjoint and in the disc `‖w‖ ≤ 2 exp (2π)`, the curvature of the
datum `puncturedSpherePerturbation c a H Hout` is integrable over the sphere minus its punctures,
the points of the plane other than the centers `c i`, along every map `u` continuous there. -/
theorem integrableOn_hamiltonianCurvature_puncturedSpherePerturbation (ω : SmoothTwoForm I M)
    (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z))
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} := by
  set T : ℝ → Set (ℝ × ℝ) :=
    fun R ↦ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R
  have hmono : Monotone T := fun _ _ h ↦ preimage_mono (puncturedSphereTruncation_mono h)
  -- The truncations at integer cutoffs already exhaust the sphere minus its punctures.
  have hTn : ⋃ n : ℕ, T n = {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} := by
    rw [← iUnion_preimage_puncturedSphereTruncation ha]
    exact hmono.iUnion_comp_tendsto_atTop tendsto_natCast_atTop_atTop
  refine ⟨hTn ▸ aestronglyMeasurable_iUnion_iff.2 fun n ↦
    (ω.integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_truncation hH hHs hHout
      hHouts ha hsep hout (hu.mono fun _ hz i ↦
        ne_of_mem_puncturedSphereTruncation (ha i) hz)).aestronglyMeasurable, ?_⟩
  obtain ⟨hsep', hout'⟩ := separation_norm_mul_exp_neg_two_pi_div_two ha hsep hout
  refine ((setLIntegral_le_lintegral _ _).trans
    (ω.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le hH hHs hHout hHouts ha
      hsep' hout' hB hBout u)).trans_lt ?_
  simp [ENNReal.sum_lt_top]

omit [IsManifold I ⊤ M] [FiniteDimensional ℝ E] in
/-- The Hamiltonian terms of the energy identity on the truncation `Σ_R`, along the boundary
circles of the ends, converge to the Hamiltonian terms at the asymptotic loops as `R → ∞`, by
dominated convergence. -/
private theorem tendsto_smoothTransition_mul_sum_sub_intervalIntegral
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i)))
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    {x : ι → ℝ → M} {xout : ℝ → M}
    (hx : ∀ i (t : ℝ), Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x i t)))
    (hxout : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xout t))) :
    Tendsto (fun R : ℝ ↦ smoothTransition (R - 1) *
      ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
        (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
        ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
          (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))))) atTop
      (𝓝 ((∑ i, ∫ t in (0 : ℝ)..1, H i t (x i t)) - ∫ t in (0 : ℝ)..1, Hout t (xout t))) := by
  -- For `R ≥ 1` the boundary circles lie in `Σ_R`, where `u` is continuous.
  have hTsub {R : ℝ} {w : ℂ} (hw : w ∈ puncturedSphereTruncation c a R) :
      Complex.equivRealProdCLM w ∈ {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} :=
    fun i ↦ by
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact ne_of_mem_puncturedSphereTruncation (ha i) hw
  have hin (i : ι) : Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
      (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, H i t (x i t))) := by
    refine tendsto_intervalIntegral_comp_of_tendsto_of_norm_le (Φ := fun p ↦ H i p.1 p.2)
      (hHs i).continuous ?_ (.of_forall fun R t _ ↦ (Real.norm_eq_abs _).trans_le (hB i _ _))
      fun t _ ↦ hx i t
    filter_upwards [eventually_ge_atTop 1] with R hR
    refine hu.comp (Complex.equivRealProdCLM.continuous.comp (continuous_const.add
      (continuous_const.mul ((zero.contDiff_cylindricalEndLift 0).continuous.comp
        (by fun_prop))))).continuousOn fun t _ ↦ hTsub (R := R) ?_
    exact add_mul_cylindricalEndLift_mem_puncturedSphereTruncation hsep hout (by simpa using hR)
      (by simp)
  have hinf : Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, Hout t (xout t))) := by
    refine tendsto_intervalIntegral_comp_of_tendsto_of_norm_le (Φ := fun p ↦ Hout p.1 p.2)
      hHouts.continuous ?_ (.of_forall fun R t _ ↦ (Real.norm_eq_abs _).trans_le (hBout _ _))
      fun t _ ↦ hxout t
    filter_upwards [eventually_ge_atTop 1] with R hR
    refine hu.comp (Complex.equivRealProdCLM.continuous.comp
      ((inf.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop))).continuousOn
      fun t _ ↦ hTsub (R := R) ?_
    exact cylindricalEndLift_inf_mem_puncturedSphereTruncation hout (by simp) (by simpa using hR)
  -- The cutoff `β(R - 1)` is `1` for `R ≥ 2`.
  have hβ : Tendsto (fun R : ℝ ↦ smoothTransition (R - 1)) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' <| (eventually_ge_atTop 2).mono fun R hR ↦
      (smoothTransition.one_of_one_le (by linarith)).symm
  simpa only [one_mul] using hβ.mul ((tendsto_finsetSum _ fun i _ ↦ hin i).sub hinf)

/-- **The energy identity on the whole sphere with moving input ends, for a manifold target.**
Let `K` be the datum `puncturedSpherePerturbation c a H Hout` of input ends with centers `c i`,
nonzero scales `a i` and bounded period-one `C¹` Hamiltonians `H i` on a finite-dimensional
manifold with a nondegenerate two-form, and of the output end at `∞` with the bounded period-one
`C¹` Hamiltonian `Hout`, with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global
coordinate `z = s + i t` of `ℂ`. Suppose the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint
and lie in the disc `‖w‖ ≤ 2 exp (2π)`. Let `u` be `C¹` on the sphere minus its punctures, the
points `z` of the plane other than the centers, with Floer energy density and symplectic area
density integrable there. Suppose the loops `t ↦ u(c i + a i φ₀(R + i t))` along the circles of the
input end `i` converge pointwise to loops `x i`, and the loops `t ↦ u(φ_∞(-R + i t))` along the
circles of the output end converge pointwise to a loop `xout`, as `R → ∞`. Then

`∫ E = ∫ u^*ω + (∑ i, ∫₀¹ H_i(t, x_i(t)) dt - ∫₀¹ Hout(t, xout(t)) dt) - ∫ R_K(u)`,

the integrals over the sphere minus its punctures, the curvature term being integrable. -/
theorem IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    {x : ι → ℝ → M} {xout : ℝ → M}
    (hx : ∀ i (t : ℝ), Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x i t)))
    (hxout : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xout t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u)
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) :
    ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}, ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ i, ∫ t in (0 : ℝ)..1, H i t (x i t)) - ∫ t in (0 : ℝ)..1, Hout t (xout t)) -
        ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
          ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
              Complex.I) z (u z) := by
  set S := {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
  set T : ℝ → Set (ℝ × ℝ) :=
    fun R ↦ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R
  have hTm (R : ℝ) : MeasurableSet (T R) :=
    ((isCompact_puncturedSphereTruncation c a R).isClosed.preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet
  have hmono : Monotone T := fun _ _ h ↦ preimage_mono (puncturedSphereTruncation_mono h)
  have hTS : ⋃ R, T R = S := iUnion_preimage_puncturedSphereTruncation ha
  have hTsub (R : ℝ) : T R ⊆ S := fun _ hz i ↦ ne_of_mem_puncturedSphereTruncation (ha i) hz
  -- Integrals over the truncations converge to integrals over `S`.
  have hlim {f : ℝ × ℝ → ℝ} (hf : IntegrableOn f S) :
      Tendsto (fun R ↦ ∫ z in T R, f z) atTop (𝓝 (∫ z in S, f z)) := by
    simpa only [hTS] using tendsto_setIntegral_of_monotone hTm hmono (hTS ▸ hf)
  -- Both sides of the identity on the truncations converge as `R → ∞`.
  refine tendsto_nhds_unique ((hlim hE).congr' ?_) (((hlim hA).add
    (tendsto_smoothTransition_mul_sum_sub_intervalIntegral hHs hHouts ha hsep hout hB hBout
      hu.continuousOn hx hxout)).sub
    (hlim (ω.integrableOn_hamiltonianCurvature_puncturedSpherePerturbation hH hHs hHout hHouts ha
      hsep hout hB hBout hu.continuousOn)))
  filter_upwards [eventually_ge_atTop 1] with R hR
  exact hω.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation hH hHs hHout hHouts ha
    hsep hout (isOpen_forall_ne Complex.equivRealProdCLM.symm.continuous) (hTsub R) hu hR

/-- **The energy bound on the whole sphere with moving input ends, for a manifold target.** Under
the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation`, the Floer
energy differs from the symplectic area plus the Hamiltonian terms at the asymptotic loops by at
most `∑ i, B i + Bout`, uniformly in the configuration of the input ends. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    {x : ι → ℝ → M} {xout : ℝ → M}
    (hx : ∀ i (t : ℝ), Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x i t)))
    (hxout : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xout t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u)
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) :
    |(∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}, ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z) -
      (∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ((∑ i, ∫ t in (0 : ℝ)..1, H i t (x i t)) - ∫ t in (0 : ℝ)..1, Hout t (xout t))| ≤
      ∑ i, B i + Bout := by
  have hsub (x y z : ℝ) : x + y - z - x - y = -z := by ring
  rw [hω.integral_floerEnergyDensity_puncturedSpherePerturbation hH hHs hHout hHouts ha hsep hout
    hB hBout hu hx hxout hE hA, hsub, abs_neg]
  obtain ⟨hsep', hout'⟩ := separation_norm_mul_exp_neg_two_pi_div_two ha hsep hout
  exact ω.abs_setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_le hH hHs hHout hHouts ha
    hsep' hout' hB hBout u _

/-- **The topological energy of a solution on the whole sphere with moving input ends is bounded
below, for a manifold target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on the
sphere minus its punctures for almost complex structures `J z` on the tangent spaces `T_{u(z)} M`
tamed by the two-form, under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation`. Since its
energy is nonnegative, its symplectic area plus the Hamiltonian terms at the asymptotic loops is
at least `-(∑ i, B i + Bout)`, whatever the configuration of the input ends. -/
theorem IsNondegenerate.neg_sum_add_le_integral_add_of_puncturedSpherePerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    {x : ι → ℝ → M} {xout : ℝ → M}
    (hx : ∀ i (t : ℝ), Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x i t)))
    (hxout : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xout t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u)
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z).toLinearMap) :
    -(∑ i, B i + Bout) ≤
      (∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ i, ∫ t in (0 : ℝ)..1, H i t (x i t)) - ∫ t in (0 : ℝ)..1, Hout t (xout t)) := by
  have hE₀ := setIntegral_nonneg (μ := volume)
    (isOpen_forall_ne Complex.equivRealProdCLM.symm.continuous).measurableSet fun z hz ↦
    floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (hω.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_sub_le hH hHs hHout hHouts ha
      hsep hout hB hBout hu hx hxout hE hA)).2
  linarith

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ}

/-- For a symplectic vector space target and a map `u` which is `C¹` on an open set containing the
truncation `Σ_R`, the Floer energy density of the datum of a sphere with moving input ends is
integrable over `Σ_R`. This is the case of the constant form of the manifold statement
`IsNondegenerate.integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation`. -/
theorem integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → V} {R : ℝ}
    {U : Set (ℝ × ℝ)} (hUo : IsOpen U)
    (hTU : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u)
      (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) := by
  have hE : ω.constSmooth.floerEnergyDensity
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u :=
    funext (floerEnergyDensity_constSmooth ω _ _ u)
  have hω := isNondegenerate_constSmooth ω
  rw [← hE]
  exact hω.integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation
    hH (fun i ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs i).contMDiff) hHout
    (contMDiff_prod_modelWithCornersSelf_iff.2 hHouts.contMDiff) ha hsep hout hUo hTU
    (contMDiffOn_iff_contDiffOn.2 hu)

/-- **The energy bound on the truncated sphere with moving input ends, for a symplectic vector
space target.** Let the input ends have centers `c i`, nonzero scales `a i` and period-one `C¹`
Hamiltonians `H i` with `|H i| ≤ B i`, such that the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise
disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, and let the output end have a period-one `C¹`
Hamiltonian `Hout` with `|Hout| ≤ Bout`. For a map `u` which is `C¹` on an open set containing the
truncation `Σ_R`, `R ≥ 1`, the Floer energy over `Σ_R` differs from the symplectic area
`∫ ω(∂ₛu, ∂ₜu)` plus `β(R - 1)` times the Hamiltonian terms of the boundary circles by at most
`∑ i, B i + Bout`, uniformly in `R` and in the configuration of the input ends. -/
theorem abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → V} {R : ℝ}
    {U : Set (ℝ × ℝ)} (hUo : IsOpen U)
    (hTU : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * Puncture.zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (Puncture.inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))))| ≤ ∑ i, B i + Bout := by
  have hω := isNondegenerate_constSmooth ω
  have h := hω.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le
    hH (fun i ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs i).contMDiff) hHout
    (contMDiff_prod_modelWithCornersSelf_iff.2 hHouts.contMDiff) ha hsep hout hB hBout hUo hTU
    (contMDiffOn_iff_contDiffOn.2 hu) hR
  simp only [floerEnergyDensity_constSmooth, eval₂_constSmooth_mfderiv_stdComplexLine] at h
  exact h

/-- **The energy of a solution on part of the truncated sphere with moving input ends.** Under the
hypotheses of
`SymplecticForm.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`, let
`u` solve the Floer equation `(du - X_K)^{0,1} = 0` on the truncation `Σ_R` for almost complex
structures `J z` tamed by `ω`. Then the Floer energy of `u` over any measurable `Ω ⊆ Σ_R` is at
most its topological energy on `Σ_R`, the symplectic area plus `β(R - 1)` times the Hamiltonian
terms of the boundary circles, plus `∑ i, B i + Bout`. -/
theorem setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → V} {R : ℝ}
    {U : Set (ℝ × ℝ)} (hUo : IsOpen U)
    (hTU : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) (hR : 1 ≤ R) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
      ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    {Ω : Set (ℝ × ℝ)} (hΩ : Ω ⊆ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) :
    ∫ z in Ω, ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z ≤
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * Puncture.zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (Puncture.inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) +
        (∑ i, B i + Bout) := by
  have hT : MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) :=
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_puncturedSphereTruncation c a R)).isClosed.measurableSet
  have habs := ω.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le hH
    hHs hHout hHouts ha hsep hout hB hBout hUo hTU hu hR
  refine (setIntegral_mono_set
    (ω.integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation hH hHs hHout hHouts
      ha hsep hout hUo hTU hu)
    ((ae_restrict_iff' hT).2 (Eventually.of_forall fun z hz ↦
      ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)))
    hΩ.eventuallySubset).trans ?_
  linarith [(abs_sub_le_iff.1 habs).1]

end TauCeti.SymplecticForm
