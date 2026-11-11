/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.Pullback

/-!
# The energy identity on spheres with moving input ends

Here we work on the punctured spheres of the associativity family of the pair-of-pants product.
Finitely many input ends sit at moving punctures `c i` of `ℂ`, with scales `a i`, and the output
end sits at `∞`. The perturbation is `K = TauCeti.Floer.puncturedSpherePerturbation c a H Hout`,
built from period-one Hamiltonians `H i` on the inputs and `Hout` on the output. In the end
coordinates `z = s + i t` of the input `i`, given by the end lift `z ↦ c i + a i φ₀(z)` with
`φ₀(z) = exp (-2πz) / 2`, the perturbation is `β(s - 1) H i(t) dt`. In the end coordinates of the
end lift `φ_∞(z) = 2 exp (-2πz)` of the output it is `β(-s - 1) Hout(t) dt`. Here `β` is the
cutoff `smoothTransition`.

The *truncation* `TauCeti.Floer.puncturedSphereTruncation c a R`, defined in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds`, is the closed disc
`‖w‖ ≤ 2 exp (2πR)` with the open discs `‖w - c i‖ < ‖a i‖ exp (-2πR) / 2` removed: the part of
the sphere where `s ≤ R` on every input end and `-s ≤ R` on the output end. This file proves the
energy identity over it, for a map `u` into a symplectic vector space which is `C¹` off the input
punctures, when the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`. For `R ≥ 1`,

`∫_T E = ∫_T u^*ω + β(R - 1) (∑ i, ∫₀¹ H i(t, ℓ_i(t)) dt - ∫₀¹ Hout(t, ℓ_∞(t)) dt) - ∫_T R_K(u)`

(`SymplecticForm.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation`). Here
`ℓ_i(t) = u(c i + a i φ₀(R + i t))` is the boundary loop of the input `i` and
`ℓ_∞(t) = u(φ_∞(-R + i t))` the boundary loop of the output. With the curvature bound of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds`, the energy therefore differs from the
area plus the Hamiltonian boundary terms by at most `∑ i, B i + Bout` when `|H i| ≤ B i` and
`|Hout| ≤ Bout`. This holds uniformly in the truncation and in the configuration of the
punctures
(`SymplecticForm.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`).
These are the energy bounds from which compactness of the moduli spaces of this family starts. They
are the counterpart, for every configuration of moving input ends, of the identity
`TauCeti.SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation` on the
pair of pants, which has inputs `0` and `1` with scales `1` and `-1`.

The proof splits the truncation into an annulus about each input puncture, where `1 ≤ s ≤ R`, an
annulus about `∞`, where `-R ≤ s ≤ -1`, and the core. On the core the perturbation vanishes
nearby, so the energy density is the area density and the curvature vanishes. Each annulus is the
image of a rectangle `[α, β] × [-1/2, 1/2)` under the real chart of its end lift, on which the
energy identity is
`TauCeti.SymplecticForm.integral_floerEnergyDensity_image_realChart_Icc_prod_Ico`, for the datum
`g(s) G(t) dt` in the end coordinates. The side `s = 1` of an input annulus and the side `s = -1`
of the output annulus carry the factor `β(0) = 0`, and the remaining side carries `β(R - 1)`.

## Main results

* `SymplecticForm.integrableOn_puncturedSphereTruncation_puncturedSpherePerturbation`: the energy,
  area and curvature densities are integrable over every truncation.
* `SymplecticForm.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation`: the energy
  identity over the truncation.
* `SymplecticForm.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`:
  the resulting energy bound, uniform in the truncation and in the configuration.

## References

* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 8 and 9, on
  perturbation data on surfaces with strip-like ends, their families and their energy.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations on punctured surfaces.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture TauCeti.Complex
open scoped Topology

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The pieces of the truncation -/

variable {ι : Type*} {c a : ι → ℂ} {R : ℝ}

/-- A point of a rectangle `[α, β] × [-1/2, 1/2)` is a complex number whose imaginary part lies in
the period `[-1/2, 1/2)`, on which the end lifts are injective. -/
private theorem mem_im_Ico_of_mem {α β : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Icc α β ×ˢ Ico (-1 / 2 : ℝ) (1 / 2)) :
    Complex.equivRealProdCLM.symm p ∈ {z : ℂ | z.im ∈ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)} := by
  have := hp.2
  norm_num at this ⊢
  exact this

/-- The real chart of an input end lift is injective on the rectangle `[1, R] × [-1/2, 1/2)`. -/
private theorem injOn_realChart_inputEndLift {c a : ℂ} (ha : a ≠ 0) (α β : ℝ) :
    InjOn (realChart fun z => c + a * zero.cylindricalEndLift z)
      (Icc α β ×ˢ Ico (-1 / 2 : ℝ) (1 / 2)) := by
  intro x hx y hy hxy
  rw [realChart_apply, realChart_apply] at hxy
  have h := mul_left_cancel₀ ha (add_left_cancel (Complex.equivRealProdCLM.injective hxy))
  exact Complex.equivRealProdCLM.symm.injective
    (injOn_cylindricalEndLift zero (-1 / 2) (mem_im_Ico_of_mem hx) (mem_im_Ico_of_mem hy) h)

/-- The real chart of the output end lift is injective on every rectangle
`[α, β] × [-1/2, 1/2)`. -/
private theorem injOn_realChart_cylindricalEndLift_inf (α β : ℝ) :
    InjOn (realChart inf.cylindricalEndLift) (Icc α β ×ˢ Ico (-1 / 2 : ℝ) (1 / 2)) := by
  intro x hx y hy hxy
  rw [realChart_apply, realChart_apply] at hxy
  exact Complex.equivRealProdCLM.symm.injective (injOn_cylindricalEndLift inf (-1 / 2)
    (mem_im_Ico_of_mem hx) (mem_im_Ico_of_mem hy) (Complex.equivRealProdCLM.injective hxy))

/-! ### The end pieces of the truncation -/

/-- The part `1 ≤ s ≤ R` of the input end with center `c` and scale `a`, over one period of the
angular coordinate. -/
private noncomputable def inputEndPiece (c a : ℂ) (R : ℝ) : Set (ℝ × ℝ) :=
  realChart (fun z ↦ c + a * zero.cylindricalEndLift z) '' (Icc 1 R ×ˢ Ico (-1 / 2) (1 / 2))

/-- The part `-R ≤ s ≤ -1` of the output end, over one period of the angular coordinate. -/
private noncomputable def outputEndPiece (R : ℝ) : Set (ℝ × ℝ) :=
  realChart inf.cylindricalEndLift '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2) (1 / 2))

/-- The end pieces of the truncation: `some i` for the input end `i`, `none` for the output. -/
private noncomputable def endPiece (c a : ι → ℂ) (R : ℝ) : Option ι → Set (ℝ × ℝ)
  | none => outputEndPiece R
  | some i => inputEndPiece (c i) (a i) R

private theorem measurableSet_endPiece (ha : ∀ i, a i ≠ 0) (o : Option ι) :
    MeasurableSet (endPiece c a R o) := by
  have hmeas (α β : ℝ) : MeasurableSet (Icc α β ×ˢ Ico (-1 / 2 : ℝ) (1 / 2)) :=
    measurableSet_Icc.prod measurableSet_Ico
  rcases o with _ | i
  · exact measurable_image_of_fderivWithin (hmeas _ _)
      (fun w _ ↦ ((contDiff_realChart (n := 1) (contDiff_cylindricalEndLift inf 1)).differentiable
        one_ne_zero w).hasFDerivAt.hasFDerivWithinAt)
      (injOn_realChart_cylindricalEndLift_inf _ _)
  · exact measurable_image_of_fderivWithin (hmeas _ _)
      (fun w _ ↦ ((contDiff_realChart (n := 1) (contDiff_const.add
        (contDiff_const.mul (contDiff_cylindricalEndLift zero 1)))).differentiable
          one_ne_zero w).hasFDerivAt.hasFDerivWithinAt)
      (injOn_realChart_inputEndLift (ha i) _ _)

/-- An input end piece lies in the disc `‖w - c‖ ≤ ‖a‖ exp (-2π) / 2` about its puncture. -/
private theorem norm_sub_le_of_mem_inputEndPiece {c a : ℂ} {z : ℝ × ℝ}
    (hz : z ∈ inputEndPiece c a R) :
    ‖Complex.equivRealProdCLM.symm z - c‖ ≤ ‖a‖ * Real.exp (-(2 * π)) / 2 := by
  obtain ⟨ζ, hζ, rfl⟩ := hz
  rw [equivRealProdCLM_symm_realChart, norm_inputEndLift_sub]
  have : Real.exp (-(2 * π * (Complex.equivRealProdCLM.symm ζ).re)) ≤ Real.exp (-(2 * π)) :=
    Real.exp_le_exp.2 (by
      rw [Complex.equivRealProdCLM_symm_apply_re]
      nlinarith [hζ.1.1, Real.pi_pos])
  nlinarith [norm_nonneg a]

/-- The output end piece lies off the disc `‖w‖ < 2 exp (2π)`. -/
private theorem le_norm_of_mem_outputEndPiece {z : ℝ × ℝ} (hz : z ∈ outputEndPiece R) :
    2 * Real.exp (2 * π) ≤ ‖Complex.equivRealProdCLM.symm z‖ := by
  obtain ⟨ζ, hζ, rfl⟩ := hz
  have hn := norm_cylindricalEndLift_sub_endCenter inf (Complex.equivRealProdCLM.symm ζ)
  rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at hn
  rw [equivRealProdCLM_symm_realChart, hn]
  have : Real.exp (2 * π) ≤ Real.exp (-(2 * π * (Complex.equivRealProdCLM.symm ζ).re)) :=
    Real.exp_le_exp.2 (by
      rw [Complex.equivRealProdCLM_symm_apply_re]
      nlinarith [hζ.1.2, Real.pi_pos])
  linarith

/-- The end pieces lie in the truncation. -/
private theorem endPiece_subset (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (o : Option ι) :
    endPiece c a R o ⊆ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R := by
  rcases o with _ | i <;> rintro _ ⟨z, hz, rfl⟩ <;>
    rw [mem_preimage, equivRealProdCLM_symm_realChart]
  · exact cylindricalEndLift_inf_mem_puncturedSphereTruncation hout (by simpa using hz.1.1)
      (by simpa using hz.1.2)
  · exact inputEndLift_mem_puncturedSphereTruncation hsep hout (by simpa using hz.1.1)
      (by simpa using hz.1.2)

/-- The end pieces are pairwise disjoint. -/
private theorem pairwise_disjoint_endPiece (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) :
    Pairwise (Disjoint on endPiece c a R) := by
  have he : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  have hio {i : ι} : Disjoint (endPiece c a R (some i)) (endPiece c a R none) := by
    refine Set.disjoint_left.2 fun z hz hz' ↦ ?_
    have h₁ := norm_sub_le_of_mem_inputEndPiece hz
    have h₂ := le_norm_of_mem_outputEndPiece hz'
    have h₃ : ‖Complex.equivRealProdCLM.symm z‖ ≤
        ‖c i‖ + ‖Complex.equivRealProdCLM.symm z - c i‖ := by
      simpa using norm_add_le (c i) (Complex.equivRealProdCLM.symm z - c i)
    nlinarith [hout i, norm_pos_iff.2 (ha i)]
  rintro (_ | i) (_ | j) hij
  · exact absurd rfl hij
  · exact hio.symm
  · exact hio
  · have hij' : i ≠ j := fun h ↦ hij (congrArg some h)
    refine Set.disjoint_left.2 fun z hz hz' ↦ ?_
    have h₁ := norm_sub_le_of_mem_inputEndPiece hz
    have h₂ := norm_sub_le_of_mem_inputEndPiece hz'
    have h₃ : ‖c i - c j‖ ≤ ‖Complex.equivRealProdCLM.symm z - c i‖ +
        ‖Complex.equivRealProdCLM.symm z - c j‖ := by
      simpa [norm_sub_rev] using norm_sub_le (c i - Complex.equivRealProdCLM.symm z)
        (c j - Complex.equivRealProdCLM.symm z)
    nlinarith [hsep hij', norm_pos_iff.2 (ha i), norm_pos_iff.2 (ha j)]

/-- **The core of the truncation.** A point of the truncation outside all the end pieces lies
outside the supports `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` of the input data, with strict inequality,
and inside the disc `‖w‖ < 2 exp (2π)` on which the output datum vanishes. -/
private theorem forall_lt_norm_sub_and_norm_lt_of_mem_sdiff (ha : ∀ i, a i ≠ 0) (hR : 0 ≤ R)
    {z : ℝ × ℝ} (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R \
      ⋃ o, endPiece c a R o) :
    (∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 < ‖Complex.equivRealProdCLM.symm z - c i‖) ∧
      ‖Complex.equivRealProdCLM.symm z‖ < 2 * Real.exp (2 * π) := by
  obtain ⟨hzT, hzA⟩ := hz
  replace hzT := mem_puncturedSphereTruncation.1 hzT
  have hz' (g : ℂ → ℂ) (ζ : ℂ) (h : g ζ = Complex.equivRealProdCLM.symm z) :
      realChart g (Complex.equivRealProdCLM ζ) = z := by
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, h,
      ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨fun i ↦ ?_, ?_⟩
  · by_contra! h
    obtain ⟨ζ, hζ, hζz⟩ := exists_inputEndLift_eq (ha i) (hzT.2 i) h
    exact hzA (mem_iUnion.2 ⟨some i, Complex.equivRealProdCLM ζ, ⟨hζ.1, hζ.2⟩, hz' _ ζ hζz⟩)
  · by_contra! h
    obtain ⟨ζ, hζ, hζz⟩ := exists_cylindricalEndLift_inf_eq hR h hzT.1
    exact hzA (mem_iUnion.2 ⟨none, Complex.equivRealProdCLM ζ, ⟨hζ.1, hζ.2⟩, hz' _ ζ hζz⟩)

/-! ### The energy identity on the truncation -/

variable [Fintype ι] {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ}

/-- Over a set of points outside the supports of the input data, with strict inequality, and
inside the open disc `‖w‖ < 2 exp (2π)`, the datum vanishes nearby: the Floer energy is the
symplectic area and the integrated curvature vanishes. -/
private theorem setIntegral_floerEnergyDensity_puncturedSpherePerturbation_of_forall_lt
    (ω : SymplecticForm V) (u : ℝ × ℝ → V) {C : Set (ℝ × ℝ)} (hC : MeasurableSet C)
    (hcore : ∀ z ∈ C,
      (∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 < ‖Complex.equivRealProdCLM.symm z - c i‖) ∧
        ‖Complex.equivRealProdCLM.symm z‖ < 2 * Real.exp (2 * π)) :
    (∫ z in C, ω.floerEnergyDensity
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u z) =
      (∫ z in C, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) ∧
    ∫ z in C, ω.hamiltonianCurvature
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) z (u z) = 0 := by
  have hO : IsOpen {z : ℝ × ℝ |
      (∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 < ‖Complex.equivRealProdCLM.symm z - c i‖) ∧
        ‖Complex.equivRealProdCLM.symm z‖ < 2 * Real.exp (2 * π)} := by
    simp only [ofPred_and, ofPred_forall]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const
      ((Complex.equivRealProdCLM.symm.continuous.sub continuous_const).norm)).inter
      (isOpen_lt Complex.equivRealProdCLM.symm.continuous.norm continuous_const)
  have hK0 {z : ℝ × ℝ} (hz : z ∈ C) : ∀ᶠ z' in 𝓝 z, ∀ x : V,
      puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z') x = 0 := by
    filter_upwards [hO.mem_nhds (hcore z hz)] with z' hz' x
    rw [puncturedSpherePerturbation_eq_negativePlanePerturbation fun i ↦ (hz'.1 i).le,
      negativePlanePerturbation_eq_zero_of_norm_le hz'.2.le]
  refine ⟨setIntegral_congr_fun hC fun z hz ↦ ?_, setIntegral_eq_zero_of_forall_eq_zero
    fun z hz ↦ ?_⟩
  · have hK := (hK0 hz).self_of_nhds
    simp [floerEnergyDensity_def, perturbedFDeriv_apply_stdComplexLineReal,
      perturbedFDeriv_apply_stdComplexLineImag, hK]
  · rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0)
      ((hK0 hz).mono fun z' hz' ↦ funext fun y ↦ by simp [hz'])
      ((hK0 hz).mono fun z' hz' ↦ funext fun y ↦ by simp [hz']), hamiltonianCurvature_zero_left]
    simp

omit [FiniteDimensional ℝ V] in
/-- The datum is `C¹` jointly in the domain point off the input punctures and the target
point. -/
private theorem contDiffOn_puncturedSpherePerturbation (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0) :
    ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × V ↦
      puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm p.1) p.2)
      ({z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  exact ((contDiffAt_puncturedSpherePerturbation_prod (n := 1) hH hHs hHout hHouts ha hz
    x).comp (z, x) ((Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp _
      contDiffAt_fst).prodMk contDiffAt_snd)).contDiffWithinAt

/-- The Floer energy density, the symplectic area density and the curvature of the datum of a
sphere with moving input ends, along a map that is `C¹` off the input punctures, are integrable
over every truncation. -/
theorem integrableOn_puncturedSphereTruncation_puncturedSpherePerturbation (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 1 u {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    (R : ℝ) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u)
        (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) ∧
      IntegrableOn (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag))
        (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) ∧
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (u z))
        (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) := by
  have hΩ : IsOpen {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} :=
    isOpen_setOf_forall_equivRealProdCLM_symm_ne c
  have hT : IsCompact (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_puncturedSphereTruncation c a R)
  have hTΩ : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆
      {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} :=
    fun z hz i ↦ ne_of_mem_puncturedSphereTruncation ha hz i
  have hK (v : ℂ) : ContDiffOn ℝ 1 (uncurry fun z x ↦
      puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x v)
      ({z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} ×ˢ univ) :=
    (contDiffOn_puncturedSpherePerturbation hH hHs hHout hHouts ha).clm_apply contDiffOn_const
  have hdu := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  refine ⟨?_, ?_, ?_⟩
  · exact ((ω.continuousOn_floerEnergyDensity hΩ hu (hK 1) (hK Complex.I)).mono
      hTΩ).integrableOn_compact hT
  · exact ((ω.continuousOn_apply_comp (hdu.clm_apply continuousOn_const)
      (hdu.clm_apply continuousOn_const)).mono hTΩ).integrableOn_compact hT
  · exact ((ω.continuousOn_hamiltonianCurvature_comp hΩ hu.continuousOn (hK 1)
      (hK Complex.I)).mono hTΩ).integrableOn_compact hT

/-- **The energy identity on an input end piece.** Over the part `1 ≤ s ≤ R` of the input end
`i`, the Floer energy is the symplectic area, plus `β(R - 1)` times the integral of `H i(t)` along
the boundary circle `s = R`, minus the integrated curvature. -/
private theorem integral_floerEnergyDensity_inputEndPiece (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) (hR : 1 ≤ R)
    (i : ι) :
    ∫ z in inputEndPiece (c i) (a i) R, ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in inputEndPiece (c i) (a i) R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
          (c i + a i * zero.cylindricalEndLift (R + t * Complex.I))))) -
        ∫ z in inputEndPiece (c i) (a i) R, ω.hamiltonianCurvature
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (u z) := by
  have hd (z : ℂ) : deriv (fun z ↦ c i + a i * zero.cylindricalEndLift z) z =
      a i * deriv zero.cylindricalEndLift z :=
    (((zero.hasDerivAt_cylindricalEndLift z).differentiableAt.hasDerivAt.const_mul
      (a i)).const_add (c i)).deriv
  have hper (s : ℝ) :
      Periodic (fun t : ℝ ↦ c i + a i * zero.cylindricalEndLift (s + t * Complex.I)) 1 :=
    fun t ↦ by
      have h : zero.cylindricalEndLift (s + ((t + 1 : ℝ) : ℂ) * Complex.I) =
          zero.cylindricalEndLift (s + t * Complex.I) := periodic_cylindricalEndLift zero s t
      simp only [h]
  rw [inputEndPiece, integral_floerEnergyDensity_image_realChart_Icc_prod_Ico ω
    (contDiff_const.add (contDiff_const.mul (contDiff_cylindricalEndLift zero 2))) hR
    (injOn_realChart_inputEndLift (ha i) 1 R) _
    (fun z hz ↦ ne_of_mem_puncturedSphereTruncation ha (by
      rw [equivRealProdCLM_symm_realChart]
      exact inputEndLift_mem_puncturedSphereTruncation hsep hout (by simpa using hz.1.1)
        (by simpa using hz.1.2)))
    (contDiffOn_puncturedSpherePerturbation hH hHs hHout hHouts ha) hu
    (g := fun s ↦ smoothTransition (s - 1)) (G := H i) fun z hz x v ↦ ?_,
    intervalIntegral_realChart_eq_of_periodic hper (hH i)]
  · simp only [sub_self, smoothTransition.zero, zero_mul, sub_zero]
  · exact isOpen_setOf_forall_equivRealProdCLM_symm_ne c
  · rw [hd, mul_assoc]
    have hz₀ : 0 < (Complex.equivRealProdCLM.symm z).re := by
      rw [Complex.equivRealProdCLM_symm_apply_re]
      linarith [hz.1.1]
    have h := puncturedSpherePerturbation_cylindricalEndLift_of_pos (Hout := Hout) hsep hout
      (hH i) (ha i) hz₀ x v
    rwa [Complex.equivRealProdCLM_symm_apply_re, Complex.equivRealProdCLM_symm_apply_im] at h

/-- **The energy identity on the output end piece.** Over the part `-R ≤ s ≤ -1` of the output
end, the Floer energy is the symplectic area, minus `β(R - 1)` times the integral of `Hout(t)`
along the boundary circle `s = -R`, minus the integrated curvature. -/
private theorem integral_floerEnergyDensity_outputEndPiece (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) (hR : 1 ≤ R) :
    ∫ z in outputEndPiece R, ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in outputEndPiece R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
          (inf.cylindricalEndLift ((-R : ℝ) + t * Complex.I))))) -
        ∫ z in outputEndPiece R, ω.hamiltonianCurvature
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (u z) := by
  rw [outputEndPiece, integral_floerEnergyDensity_image_realChart_Icc_prod_Ico ω
    (contDiff_cylindricalEndLift inf 2) (by linarith : -R ≤ -1)
    (injOn_realChart_cylindricalEndLift_inf (-R) (-1)) _
    (fun z hz ↦ ne_of_mem_puncturedSphereTruncation ha (by
      rw [equivRealProdCLM_symm_realChart]
      exact cylindricalEndLift_inf_mem_puncturedSphereTruncation hout (by simpa using hz.1.1)
        (by simpa using hz.1.2)))
    (contDiffOn_puncturedSpherePerturbation hH hHs hHout hHouts ha) hu
    (g := fun s ↦ smoothTransition (-s - 1)) (G := Hout) fun z hz x v ↦ ?_,
    intervalIntegral_realChart_eq_of_periodic (periodic_cylindricalEndLift inf) hHout u (-R)]
  · simp only [neg_neg, sub_self, smoothTransition.zero, zero_mul, zero_sub]
    ring
  · exact isOpen_setOf_forall_equivRealProdCLM_symm_ne c
  · have hz₀ : (Complex.equivRealProdCLM.symm z).re ≤ -1 := by
      rw [Complex.equivRealProdCLM_symm_apply_re]
      exact hz.1.2
    have h := puncturedSpherePerturbation_cylindricalEndLift_inf_of_le (H := H) hout hHout hz₀ x v
    rwa [Complex.equivRealProdCLM_symm_apply_re, Complex.equivRealProdCLM_symm_apply_im] at h

/-- **The energy identity on the truncated sphere with moving input ends.** Let `K` be the datum
`puncturedSpherePerturbation c a H Hout` of period-one `C¹` Hamiltonians `H i` on the input ends,
with centers `c i` and nonzero scales `a i`, and `Hout` on the output end, on a symplectic vector
space. Suppose that the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`. Let `u` be `C¹` off the input punctures. Then for `R ≥ 1`, over the truncation
`T` of height `R` the Floer energy of `u` is its symplectic area, plus `β(R - 1)` times the
integrals of the input Hamiltonians along the boundary circles `s = R` of the input ends minus that
of the output Hamiltonian along the boundary circle `s = -R` of the output end, minus the
integrated curvature:

`∫_T E = ∫_T u^*ω + β(R - 1) (∑ i, ∫₀¹ H i(t, ℓ_i(t)) dt - ∫₀¹ Hout(t, ℓ_∞(t)) dt) - ∫_T R_K(u)`.

Here `ℓ_i(t) = u(c i + a i φ₀(R + i t))` and `ℓ_∞(t) = u(φ_∞(-R + i t))`, where `φ₀` and `φ_∞` are
the end lifts of the pair of pants at `0` and `∞`, and `β = smoothTransition`, so `β(R - 1) = 1`
for `R ≥ 2`. The energy, area and curvature densities are integrable over `T` automatically. -/
theorem integral_floerEnergyDensity_puncturedSpherePerturbation_truncation (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R, ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        smoothTransition (R - 1) *
          ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
              (c i + a i * zero.cylindricalEndLift (R + t * Complex.I))))) -
            ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
              (inf.cylindricalEndLift ((-R : ℝ) + t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
              Complex.I) z (u z) := by
  classical
  set T := Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R
  set C := T \ ⋃ o, endPiece c a R o
  obtain ⟨hE, harea, hcurv⟩ := integrableOn_puncturedSphereTruncation_puncturedSpherePerturbation
    ω hH hHs hHout hHouts ha hu R
  have hAT := endPiece_subset (R := R) hsep hout
  have hAm := measurableSet_endPiece (c := c) (R := R) ha
  -- The truncation is the disjoint union of its core `C` and the end pieces.
  have hsplit (g : ℝ × ℝ → ℝ) (hg : IntegrableOn g T) :
      ∫ z in T, g z = (∫ z in C, g z) + ∑ o, ∫ z in endPiece c a R o, g z := by
    have hTC : T = C ∪ ⋃ o, endPiece c a R o := (sdiff_union_of_subset (iUnion_subset hAT)).symm
    conv_lhs => rw [hTC]
    rw [setIntegral_union disjoint_sdiff_left (MeasurableSet.iUnion hAm)
      (hg.mono_set sdiff_subset) (hg.mono_set (iUnion_subset hAT)),
      integral_iUnion_fintype hAm (pairwise_disjoint_endPiece ha hsep hout)
        fun o ↦ hg.mono_set (hAT o)]
  -- On the core the datum vanishes nearby.
  obtain ⟨hCE, hCR⟩ := setIntegral_floerEnergyDensity_puncturedSpherePerturbation_of_forall_lt
    (H := H) (Hout := Hout) (C := C) ω u
    ((Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_puncturedSphereTruncation c a R)).isClosed.measurableSet.diff
      (MeasurableSet.iUnion hAm))
    fun z hz ↦ forall_lt_norm_sub_and_norm_lt_of_mem_sdiff ha (by linarith) hz
  rw [hsplit _ hE, hsplit _ harea, hsplit _ hcurv, hCE, hCR, Fintype.sum_option,
    Fintype.sum_option, Fintype.sum_option]
  simp only [endPiece]
  rw [integral_floerEnergyDensity_outputEndPiece ω hH hHs hHout hHouts ha hout hu hR,
    Finset.sum_congr rfl fun i _ ↦
      integral_floerEnergyDensity_inputEndPiece ω hH hHs hHout hHouts ha hsep hout hu hR i]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_sub, Finset.mul_sum]
  ring

/-- **The energy bound on the truncated sphere with moving input ends.** Under the hypotheses of
`SymplecticForm.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation`, if the
Hamiltonians are bounded, `|H i| ≤ B i` and `|Hout| ≤ Bout`, then for every `R ≥ 1` the Floer
energy over the truncation differs from the symplectic area plus the Hamiltonian boundary terms by
at most `∑ i, B i + Bout`. The bound is uniform in the truncation and in the configuration of the
input punctures. -/
theorem abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        smoothTransition (R - 1) *
          ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
              (c i + a i * zero.cylindricalEndLift (R + t * Complex.I))))) -
            ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
              (inf.cylindricalEndLift ((-R : ℝ) + t * Complex.I)))))| ≤ ∑ i, B i + Bout := by
  have hπ := Real.pi_pos
  have he : Real.exp (-(2 * π)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hB₀ (i : ι) : 0 ≤ B i := (abs_nonneg _).trans (hB i 0 0)
  have hBout₀ : 0 ≤ Bout := (abs_nonneg _).trans (hBout 0 0)
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [integral_floerEnergyDensity_puncturedSpherePerturbation_truncation ω hH hHs hHout hHouts ha
    hsep hout hu hR, hsub, abs_neg]
  have hsum : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ ↦ hB₀ i
  rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg hsum hBout₀), ← Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_add hsum hBout₀, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hB₀ i]
  refine (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le ω hH hHs hHout hHouts ha
      (fun i j hij ↦ ?_) (fun i ↦ ?_) hB hBout u))
  · nlinarith [hsep hij, norm_nonneg (a i), norm_nonneg (a j)]
  · nlinarith [hout i, norm_nonneg (a i)]

end SymplecticForm

end TauCeti
