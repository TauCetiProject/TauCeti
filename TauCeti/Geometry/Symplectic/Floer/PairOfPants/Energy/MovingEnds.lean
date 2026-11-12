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
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

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

The truncation is the disjoint union of the pieces `1 ≤ s ≤ R` of the input ends, the piece
`-R ≤ s ≤ -1` of the output end, and a core on which the datum vanishes nearby. In the coordinates
of each end the datum is the continuation datum `β(±s - 1) H(t) dt`, so each piece is handled by
the energy identity over the image of a rectangle,
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_image_of_perturbationPullback`.

## Main results

In the namespace `TauCeti.SmoothTwoForm`:

* `IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation`: the energy
  identity on `Σ_R`.
* `IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`:
  the resulting energy bound, uniform in `R` and in the configuration.

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

/-- The end lift `z ↦ c + a φ₀(z)` of an input end, in real coordinates, is injective on every
horizontal strip of height one. -/
private theorem injOn_realChart_add_mul_cylindricalEndLift {c a : ℂ} (ha : a ≠ 0) {S : Set ℝ}
    {t₀ : ℝ} :
    InjOn (realChart fun z ↦ c + a * zero.cylindricalEndLift z) (S ×ˢ Ico t₀ (t₀ + 1)) := by
  intro p hp q hq hpq
  have h := congrArg Complex.equivRealProdCLM.symm hpq
  simp only [equivRealProdCLM_symm_realChart, add_right_inj, mul_right_inj' ha] at h
  exact Complex.equivRealProdCLM.symm.injective
    (zero.injOn_cylindricalEndLift t₀ (by simpa using hp.2) (by simpa using hq.2) h)

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
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (hR : 1 ≤ R) (o : Option ι) :
    movingEndPiece c a R o ⊆
      Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R := by
  cases o with
  | none =>
    rintro _ ⟨p, hp, rfl⟩
    refine mem_preimage.2 ?_
    rw [equivRealProdCLM_symm_endChart]
    exact cylindricalEndLift_inf_mem_puncturedSphereTruncation hout (by simpa using hp.1.1)
      (by simpa using hp.1.2)
  | some i =>
    rintro _ ⟨p, hp, rfl⟩
    refine mem_preimage.2 ?_
    rw [equivRealProdCLM_symm_realChart]
    exact add_mul_cylindricalEndLift_mem_puncturedSphereTruncation hsep hout hR
      (by simpa using hp.1.1) (by simpa using hp.1.2)

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

/-- The pieces of the ends are pairwise disjoint: the piece of the input end `i` lies in the disc
`‖w - c i‖ ≤ ‖a i‖ exp (-2π) / 2`, and the piece of the output end off the disc
`‖w‖ < 2 exp (2π)`. -/
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
    obtain ⟨ζ, hζre, hζim, hζ⟩ := exists_add_mul_cylindricalEndLift_eq (ha i) (hz.1 i) h
    refine hA (mem_iUnion.2 ⟨some i, Complex.equivRealProdCLM ζ,
      ⟨by simpa using hζre, by rw [hIco]; simpa using hζim⟩, ?_⟩)
    simp only [realChart_equivRealProdCLM, hζ, ContinuousLinearEquiv.apply_symm_apply]
  · by_contra! h
    obtain ⟨ζ, hζre, hζim, hζ⟩ := exists_cylindricalEndLift_inf_eq h hz.2
    refine hA (mem_iUnion.2 ⟨none, Complex.equivRealProdCLM ζ,
      ⟨by simpa using hζre, by rw [hIco]; simpa using hζim⟩, ?_⟩)
    simp only [endChart_apply, ContinuousLinearEquiv.symm_apply_apply, hζ,
      ContinuousLinearEquiv.apply_symm_apply]

end Pieces

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer
open TauCeti.Complex (realChart equivRealProdCLM_symm_realChart contDiff_realChart
  det_fderiv_realChart_nonneg)

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}

omit [IsManifold I ⊤ M] in
/-- Off the centers of the input ends, the components of the datum on a sphere with moving input
ends are `C¹` jointly in the domain point, in real coordinates, and the target point. -/
private theorem contMDiffAt_puncturedSpherePerturbation_real (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    {z : ℝ × ℝ} (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) (x : M) (v : ℂ) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦
        puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x v) (z, x) := by
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I)
      (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 1
      (fun p : (ℝ × ℝ) × M ↦ ((c, a), (Complex.equivRealProdCLM.symm p.1, p.2))) (z, x) :=
    contMDiffAt_const.prodMk
      ((Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _
        contMDiffAt_fst).prodMk contMDiffAt_snd)
  exact ((contMDiffAt_puncturedSpherePerturbation hH hHs hHout hHouts ha hz x).comp (z, x)
    hφ).clm_apply contMDiffAt_const

/-- On a period of length one, the integral of a function of period one may be taken over
`[0, 1]`. -/
private theorem intervalIntegral_neg_half_eq {f : ℝ → ℝ} (hf : Periodic f 1) :
    ∫ t in (-1 / 2 : ℝ)..-1 / 2 + 1, f t = ∫ t in (0 : ℝ)..1, f t := by
  simpa using hf.intervalIntegral_add_eq (-1 / 2) 0

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- The energy identity on the piece `1 ≤ s ≤ R`, `t ∈ [-1/2, 1/2)` of the input end `i` of a
sphere with moving input ends, in the coordinates of its end lift `z ↦ c i + a i φ₀(z)`, together
with the integrability of the curvature over that piece. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_inputPiece
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) (i : ι) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z))
      (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ''
        (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1))) ∧
    ∫ z in realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ''
        (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ''
        (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
          (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
        ∫ z in realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ''
        (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
          ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) := by
  classical
  set K := puncturedSpherePerturbation c a H Hout
  set Ks : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I
  have hK (z : ℝ × ℝ) (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) (x : M) (v : ℂ) :=
    contMDiffAt_puncturedSpherePerturbation_real hH hHs hHout hHouts ha hz x v
  set Φ : ℝ × ℝ → ℝ × ℝ := realChart fun z ↦ c i + a i * zero.cylindricalEndLift z
  set Ri : Set (ℝ × ℝ) := Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)
  have hf (w : ℝ × ℝ) : HasDerivAt (fun z ↦ c i + a i * zero.cylindricalEndLift z)
      (a i * deriv zero.cylindricalEndLift (Complex.equivRealProdCLM.symm w))
      (Complex.equivRealProdCLM.symm w) :=
    ((zero.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt.const_mul (a i)).const_add
      (c i)
  have hΦ : ContDiff ℝ 2 Φ := contDiff_realChart (by fun_prop)
  have hΦinj : InjOn Φ Ri := injOn_realChart_add_mul_cylindricalEndLift (ha i)
  have hβ : ContDiff ℝ 1 fun s : ℝ ↦ smoothTransition (s - 1) :=
    smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  -- On the input end `i`, the datum is `β(s - 1) H i(t) dt` in the coordinates of `Φ`.
  have hpullIn {w : ℝ × ℝ} (hw : 0 < w.1) (v : ℝ × ℝ) (x : M) :
      perturbationPullback Φ Ks Kt v w x =
        (Complex.equivRealProdCLM.symm v).im * (smoothTransition (w.1 - 1) * H i w.2 x) := by
    rw [perturbationPullback_realChart K (hf w), mul_assoc,
      puncturedSpherePerturbation_cylindricalEndLift_of_pos hsep (fun i ↦ by
        linarith [hout i, norm_nonneg (a i)]) (hH i) (ha i) (by simpa using hw)]
    simp
  set U : Set (ℝ × ℝ) := {w | 1 / 2 < w.1 ∧ Φ w ∈ V}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_fst).inter (hVo.preimage hΦ.continuous)
  have hne {w : ℝ × ℝ} (hw : w ∈ U) (j : ι) :
      Complex.equivRealProdCLM.symm (Φ w) ≠ c j := by
    rw [equivRealProdCLM_symm_realChart]
    exact add_mul_cylindricalEndLift_ne hsep (ha i) (by simp; linarith [hw.1]) j
  have hKs (w : ℝ × ℝ) (hw : w ∈ U) (x : M) :=
    (hK _ (hne hw) x 1).mdifferentiableAt one_ne_zero
  have hKt (w : ℝ × ℝ) (hw : w ∈ U) (x : M) :=
    (hK _ (hne hw) x Complex.I).mdifferentiableAt one_ne_zero
  have hs (w : ℝ × ℝ) (hw : w ∈ U) :
      perturbationPullback Φ Ks Kt stdComplexLineReal w = 0 :=
    funext fun x ↦ by
      rw [hpullIn (by linarith [hw.1])]
      simp
  have ht (w : ℝ × ℝ) (hw : w ∈ U) :
      perturbationPullback Φ Ks Kt stdComplexLineImag w =
        fun x ↦ smoothTransition (w.1 - 1) * H i w.2 x :=
    funext fun x ↦ by
      rw [hpullIn (by linarith [hw.1])]
      simp
  have hstrip (z : ℝ × ℝ) (hz : z.1 ∈ Icc 1 R) : z ∈ U := ⟨by linarith [hz.1], hTV (by
    refine mem_preimage.2 ?_
    rw [equivRealProdCLM_symm_realChart]
    exact add_mul_cylindricalEndLift_mem_puncturedSphereTruncation
      (z := Complex.equivRealProdCLM.symm z) hsep hout hR
      (by simpa using hz.1) (by simpa using hz.2))⟩
  refine ⟨ω.integrableOn_hamiltonianCurvature_image_of_perturbationPullback hUo hΦ
    (fun w _ ↦ det_fderiv_realChart_nonneg (hf w)) (fun w hw ↦ hw.2) hu.continuousOn
    hKs hKt hs ht hβ (hHs i) (fun z hz ↦ hstrip z hz.1) hΦinj, ?_⟩
  have h := hω.integral_floerEnergyDensity_image_of_perturbationPullback hUo hVo hΦ
    (fun w _ ↦ det_fderiv_realChart_nonneg (hf w)) (fun w hw ↦ hw.2) hu hKs hKt hs ht hβ
    (hHs i) hR (by norm_num) (fun z hz ↦ hstrip z hz.1) hΦinj
  have hloop : ∫ t in (-1 / 2 : ℝ)..-1 / 2 + 1, H i t (u (Φ (R, t))) =
      ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
        (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) := by
    simp only [Φ, TauCeti.Complex.realChart_apply, Complex.equivRealProdCLM_symm_apply]
    exact intervalIntegral_neg_half_eq fun t ↦ by
      simp only [zero.periodic_cylindricalEndLift R t, hH i t]
  rw [h, hloop, sub_self, smoothTransition.zero, zero_mul, sub_zero]

/-- The energy identity on the piece `-R ≤ s ≤ -1`, `t ∈ [-1/2, 1/2)` of the output end of a
sphere with moving input ends, in the coordinates of its end lift, together with the integrability
of the curvature over that piece. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_outputPiece
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z))
      (endChart inf '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1))) ∧
    ∫ z in endChart inf '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in endChart inf '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
          (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
        ∫ z in endChart inf '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
          ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) := by
  classical
  set K := puncturedSpherePerturbation c a H Hout
  set Ks : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I
  have hK (z : ℝ × ℝ) (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) (x : M) (v : ℂ) :=
    contMDiffAt_puncturedSpherePerturbation_real hH hHs hHout hHouts ha hz x v
  set Ro : Set (ℝ × ℝ) := Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)
  have hβ' : ContDiff ℝ 1 fun s : ℝ ↦ smoothTransition (-s - 1) :=
    smoothTransition.contDiff.comp (contDiff_neg.sub contDiff_const)
  -- On the output end, the datum is `β(-s - 1) Hout(t) dt` in the coordinates of its end chart.
  have hcont : Continuous fun w : ℝ × ℝ ↦
      ‖inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)‖ :=
    ((inf.contDiff_cylindricalEndLift 0).continuous.comp
      Complex.equivRealProdCLM.symm.continuous).norm
  set Uo : Set (ℝ × ℝ) := {w | (∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 <
    ‖inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)‖) ∧ endChart inf w ∈ V}
  have hUoo : IsOpen Uo := by
    simp only [Uo, ofPred_and, ofPred_forall]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const hcont).inter
      (hVo.preimage (contDiff_endChart inf 0).continuous)
  have hpullOut {w : ℝ × ℝ} (hw : w ∈ Uo) (v : ℝ × ℝ) (x : M) :
      perturbationPullback (endChart inf) Ks Kt v w x =
        (Complex.equivRealProdCLM.symm v).im * (smoothTransition (-w.1 - 1) * Hout w.2 x) := by
    rw [perturbationPullback_endChart_eq_cylindricalEndLift K inf v]
    simp only [K]
    rw [puncturedSpherePerturbation_eq_negativePlanePerturbation fun i ↦ ?_,
      negativePlanePerturbation_cylindricalEndLift_apply hHout]
    · simp
    · have h := hw.1 i
      have htri :=
        norm_sub_norm_le (inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)) (c i)
      linarith
  have hne {w : ℝ × ℝ} (hw : w ∈ Uo) (j : ι) :
      Complex.equivRealProdCLM.symm (endChart inf w) ≠ c j := by
    rw [equivRealProdCLM_symm_endChart]
    intro h
    have := hw.1 j
    rw [h] at this
    linarith [mul_nonneg (norm_nonneg (a j)) (Real.exp_pos (-(2 * π))).le]
  have hKs (w : ℝ × ℝ) (hw : w ∈ Uo) (x : M) :=
    (hK _ (hne hw) x 1).mdifferentiableAt one_ne_zero
  have hKt (w : ℝ × ℝ) (hw : w ∈ Uo) (x : M) :=
    (hK _ (hne hw) x Complex.I).mdifferentiableAt one_ne_zero
  have hs (w : ℝ × ℝ) (hw : w ∈ Uo) :
      perturbationPullback (endChart inf) Ks Kt stdComplexLineReal w = 0 :=
    funext fun x ↦ by
      rw [hpullOut hw]
      simp
  have ht (w : ℝ × ℝ) (hw : w ∈ Uo) :
      perturbationPullback (endChart inf) Ks Kt stdComplexLineImag w =
        fun x ↦ smoothTransition (-w.1 - 1) * Hout w.2 x :=
    funext fun x ↦ by
      rw [hpullOut hw]
      simp
  have hstrip (z : ℝ × ℝ) (hz : z.1 ∈ Icc (-R) (-1)) : z ∈ Uo := by
    refine ⟨fun i ↦ ?_, hTV (by
      refine mem_preimage.2 ?_
      rw [equivRealProdCLM_symm_endChart]
      exact cylindricalEndLift_inf_mem_puncturedSphereTruncation
        (z := Complex.equivRealProdCLM.symm z) hout (by simpa using hz.1)
        (by simpa using hz.2))⟩
    have h₁ : 2 * Real.exp (2 * π) ≤
        ‖inf.cylindricalEndLift (Complex.equivRealProdCLM.symm z)‖ := by
      simpa using two_mul_exp_le_norm_cylindricalEndLift_inf (R := 1)
        (z := Complex.equivRealProdCLM.symm z) (by simpa using hz.2)
    linarith [hout i, norm_mul_exp_neg_two_pi_div_two_lt (ha i)]
  have hinj : InjOn (endChart inf) Ro :=
    (injOn_endChart_univ_prod_Ico inf (-1 / 2)).mono (prod_mono (subset_univ _) subset_rfl)
  refine ⟨ω.integrableOn_hamiltonianCurvature_image_of_perturbationPullback hUoo
    (contDiff_endChart inf 2) (fun w _ ↦ det_fderiv_endChart_nonneg inf w) (fun w hw ↦ hw.2)
    hu.continuousOn hKs hKt hs ht hβ' hHouts (fun z hz ↦ hstrip z hz.1) hinj, ?_⟩
  have h := hω.integral_floerEnergyDensity_image_of_perturbationPullback hUoo hVo
    (contDiff_endChart inf 2) (fun w _ ↦ det_fderiv_endChart_nonneg inf w) (fun w hw ↦ hw.2)
    hu hKs hKt hs ht hβ' hHouts (by linarith) (by norm_num) (fun z hz ↦ hstrip z hz.1) hinj
  have hloop : ∫ t in (-1 / 2 : ℝ)..-1 / 2 + 1, Hout t (u (endChart inf (-R, t))) =
      ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) := by
    simp only [endChart_apply, Complex.equivRealProdCLM_symm_apply]
    exact intervalIntegral_neg_half_eq fun t ↦ by
      simp only [inf.periodic_cylindricalEndLift (-R) t, hHout t]
  rw [h, hloop]
  simp only [neg_neg, sub_self, smoothTransition.zero, zero_mul, zero_sub]
  ring

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
  -- The truncation `T` is the disjoint union of the pieces `A o` of the ends, indexed by
  -- `o : Option ι` with `none` the output end, and of the core `C`. The energy identity holds on
  -- each piece by the piece lemmas, the datum vanishes near every point of the core, and the three
  -- integrals over `T` split accordingly.
  set K := puncturedSpherePerturbation c a H Hout
  set Ks : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I
  set T := Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R
  set A := movingEndPiece c a R
  set C := T \ ⋃ o, A o
  have hT : IsCompact T :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_puncturedSphereTruncation c a R)
  have hTc {z : ℝ × ℝ} (hz : z ∈ T) (i : ι) : Complex.equivRealProdCLM.symm z ≠ c i :=
    ne_of_mem_puncturedSphereTruncation (ha i) hz
  have hK (z : ℝ × ℝ) (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) (x : M) (v : ℂ) :=
    contMDiffAt_puncturedSpherePerturbation_real hH hHs hHout hHouts ha hz x v
  -- The energy identity and the integrability of the curvature on the pieces of the ends.
  have hEin (i : ι) :
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) (A (some i)) ∧
      ∫ z in A (some i), ω.floerEnergyDensity Ks Kt u z =
        (∫ z in A (some i), (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ z in A (some i), ω.hamiltonianCurvature Ks Kt z (u z) :=
    hω.integral_floerEnergyDensity_puncturedSpherePerturbation_inputPiece hH hHs hHout hHouts ha
      hsep hout hVo hTV hu hR i
  have hEout :
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) (A none) ∧
      ∫ z in A none, ω.floerEnergyDensity Ks Kt u z =
        (∫ z in A none, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
          smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
          ∫ z in A none, ω.hamiltonianCurvature Ks Kt z (u z) :=
    hω.integral_floerEnergyDensity_puncturedSpherePerturbation_outputPiece hH hHs hHout hHouts ha
      hout hVo hTV hu hR
  -- The pieces lie in the truncation, are measurable, and are pairwise disjoint.
  have hAT := movingEndPiece_subset hsep hout hR
  have hAm := measurableSet_movingEndPiece (c := c) (R := R) ha
  have hAd := pairwise_disjoint_movingEndPiece (R := R) ha hsep hout
  -- Off the pieces, the datum vanishes near every point of the truncation.
  set O : Set (ℝ × ℝ) := {z | (∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 <
    ‖Complex.equivRealProdCLM.symm z - c i‖) ∧ ‖Complex.equivRealProdCLM.symm z‖ <
      2 * Real.exp (2 * π)}
  have hOo : IsOpen O := by
    simp only [O, ofPred_and, ofPred_forall]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt (by fun_prop) continuous_const)
  have hKO {z : ℝ × ℝ} (hz : z ∈ O) : K (Complex.equivRealProdCLM.symm z) = fun _ ↦ 0 :=
    funext fun x ↦ by
      simp only [K]
      rw [puncturedSpherePerturbation_eq_negativePlanePerturbation fun i ↦ (hz.1 i).le,
        negativePlanePerturbation_eq_zero_of_norm_le hz.2.le]
  have hCO {z : ℝ × ℝ} (hz : z ∈ C) : z ∈ O := lt_norm_of_notMem_movingEndPiece ha hz.1 hz.2
  have hCm : MeasurableSet C := hT.isClosed.measurableSet.diff (MeasurableSet.iUnion hAm)
  have hCE : ∫ z in C, ω.floerEnergyDensity Ks Kt u z =
      ∫ z in C, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by
    refine setIntegral_congr_fun hCm fun z hz ↦ ?_
    have h := hKO (hCO hz)
    simp [Ks, Kt, floerEnergyDensity_def, h, hamiltonianVectorField_const]
  have hCR0 {z : ℝ × ℝ} (hz : z ∈ C) : ω.hamiltonianCurvature Ks Kt z (u z) = 0 := by
    have hev : ∀ᶠ w in 𝓝 z, w ∈ O := hOo.mem_nhds (hCO hz)
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (Ks' := fun _ _ ↦ 0)
      (Kt' := fun _ _ ↦ 0) (hev.mono fun w hw ↦ funext fun x ↦ by simp [Ks, hKO hw])
      (hev.mono fun w hw ↦ funext fun x ↦ by simp [Kt, hKO hw]), hamiltonianCurvature_zero]
  -- The densities are integrable over the truncation.
  have harea := (ω.isSmoothForm.of_le (by simp)).continuousOn_apply_mfderiv hVo hu
    stdComplexLineReal stdComplexLineImag
  simp only [← SmoothBundleForm.eval₂_apply] at harea
  replace harea := (harea.mono hTV).integrableOn_compact (μ := volume) hT
  have hcurv : IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) T := by
    have hA (o : Option ι) :
        IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) (A o) := by
      cases o with
      | none => exact hEout.1
      | some i => exact (hEin i).1
    refine ((integrableOn_zero.congr_fun (fun z hz ↦ (hCR0 hz).symm) hCm).union
      (integrableOn_finite_iUnion.2 hA)).mono_set fun z hz ↦ ?_
    by_cases h : z ∈ ⋃ o, A o
    · exact Or.inr h
    · exact Or.inl ⟨hz, h⟩
  set P : Set (ℝ × ℝ) := {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
  have hPo : IsOpen P := by
    simp only [P, ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun (by fun_prop) continuous_const
  have hKP (v : ℂ) : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) ((V ∩ P) ×ˢ univ) :=
    fun p hp ↦ (hK p.1 hp.1.2 p.2 v).contMDiffWithinAt
  have hE := hω.integrableOn_floerEnergyDensity (hVo.inter hPo) (hu.mono inter_subset_left)
    (hKP 1) (hKP Complex.I) hT (subset_inter hTV fun z hz ↦ hTc hz) hcurv
  -- The truncation is the disjoint union of the core `C` and the pieces.
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f T) :
      ∫ z in T, f z = (∫ z in C, f z) + ∑ o, ∫ z in A o, f z := by
    have hTC : T = C ∪ ⋃ o, A o := (sdiff_union_of_subset (iUnion_subset hAT)).symm
    conv_lhs => rw [hTC]
    rw [setIntegral_union disjoint_sdiff_left (MeasurableSet.iUnion hAm)
      (hf.mono_set sdiff_subset) (hf.mono_set (iUnion_subset hAT)),
      integral_iUnion_fintype hAm hAd fun o ↦ hf.mono_set (hAT o)]
  rw [hsplit _ hE, hsplit _ harea, hsplit _ hcurv, hCE,
    setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ hCR0 hz, Fintype.sum_option,
    Fintype.sum_option, Fintype.sum_option, hEout.2, Finset.sum_congr rfl fun i _ ↦ (hEin i).2]
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
  have hB₀ (i : ι) : 0 ≤ B i := (abs_nonneg _).trans (hB i 0 (u 0))
  have hBout₀ : 0 ≤ Bout := (abs_nonneg _).trans (hBout 0 (u 0))
  have hsum₀ : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ ↦ hB₀ i
  -- The supports of the input end data lie in the discs `‖w - c i‖ < ‖a i‖ / 2`.
  have hr (i : ι) := (norm_mul_exp_neg_two_pi_div_two_lt (ha i)).le
  rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg hsum₀ hBout₀), ← Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_add hsum₀ hBout₀, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hB₀ i]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (ω.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le hH hHs hHout hHouts ha
      (fun i j hij ↦ by linarith [hr i, hr j, hsep hij]) (fun i ↦ by linarith [hr i, hout i]) hB
      hBout u))

end TauCeti.SmoothTwoForm
