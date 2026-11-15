/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Asymptotic orbits and end convergence for Floer pairs of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and let `K` be a Hamiltonian perturbation on the pair of pants
`S = ℂ ∖ {0, 1}`, equal to `H_q(t) dt` beyond some height `T₀` on each end `q` for `1`-periodic
Hamiltonians `H_q : ℝ → M → ℝ`. Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on `S`
with finite energy and image in a compact set `B ⊆ M` (on a closed manifold `B` can be `M`
itself). This file proves the manifold counterparts of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence`:

1. **Positive end charts.** Along the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
   (`TauCeti.Floer.positiveEndChart`), where `s → ∞` on all three ends, `u ∘ φ'_q` solves the
   manifold half-cylinder Floer equation beyond `T₀` for the end Hamiltonian
   `H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`), and its energy over any
   half-cylinder `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0` is at most the energy of `u` over `S`.
   Time reversal `t ↦ ±t` identifies the `1`-periodic orbits of `H'_q` with those of `H_q`
   (`TauCeti.SmoothTwoForm.mem_periodicSolutions_positiveEndHamiltonian_iff`).
2. **Breaking along sequences** (in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). If the
   almost complex structures are uniformly tame on `S` with respect to a `C¹` immersion `e : M → F`
   injective on `B`, then at each end `q` there are `σ_n → ∞` and a `1`-periodic orbit `y_q` of
   `X_{H_q}` in `B` such that the end loops `t ↦ u(φ_q(±σ_n, t))` converge to `y_q`, pointwise in
   `M` and uniformly after applying `e`
   (`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`, and
   `exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer` on a compact manifold).
3. **Whole-end convergence at nondegenerate orbits.** If on some half-cylinder `s > b` of `φ'_q`
   the derivative of `e ∘ u ∘ φ'_q` is bounded and the almost complex structures are uniformly
   tame, and if every `1`-periodic orbit of `H_q` in `B` is isolated at `t = 0` — in particular, if
   `H_q` is `C²` and every `1`-periodic orbit of `H_q` in `B` is a nondegenerate fixed point of the
   time-one map — then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single
   `1`-periodic orbit `y_q` of `X_{H_q}` in `B`
   (`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, and
   `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer` on a compact manifold).
4. **The energy identity and topological energy bound at asymptotic orbits.** Combining whole-end
   convergence with `lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm` and
   `neg_sum_le_integral_add_sum_of_isComplexLinearMap` removes the assumed pointwise end limits from
   `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic`: the boundary terms of the
   pair-of-pants energy identity
   `∫_S E(u) = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`
   and the lower bound `-∑ q, M_q ≤ ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt` for `|H_q| ≤ M_q` are
   evaluated at the derived asymptotic `1`-periodic orbits `y_q` of `u`
   (`exists_mem_periodicSolutions_integral_floerEnergyDensity_of_isCompact`,
   `exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact`,
   and `exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits at
  nondegenerate orbits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics and the energy estimate of the pair-of-pants product.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Manifold

namespace TauCeti

namespace Floer

/-- If `u` maps `S` into a compact set `K ⊆ M` and its loops along the circles `±s = R` of the end
`q` converge pointwise to `x` as `R → ∞`, then the integrals of a continuous Hamiltonian `H` along
them converge to its integral along `x`. Unlike `TauCeti.Floer.tendsto_intervalIntegral_endLoop`,
no global bound on `H` over `M` is needed. -/
theorem tendsto_intervalIntegral_endLoop_of_isCompact {M : Type*} [TopologicalSpace M]
    {H : ℝ → M → ℝ} (hHc : Continuous (uncurry H)) {K : Set M} (hK : IsCompact K)
    {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal)
    (huK : ∀ z ∈ thricePuncturedSphereReal, u z ∈ K) {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, Tendsto (fun R : ℝ ↦ u (endChart q (q.endSign * R, t))) atTop (𝓝 (x t))) :
    Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H t (u (endChart q (q.endSign * R, t)))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, H t (x t))) := by
  -- On the compact set `[0, 1] × K`, the continuous Hamiltonian `H` is bounded.
  obtain ⟨C₀, hC₀⟩ :=
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn hHc.continuousOn
  have hmem {R : ℝ} (hR : 0 < R) (t : ℝ) :
      endChart q (q.endSign * R, t) ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (by simpa [← mul_assoc] using hR)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C₀) ?_ ?_
    intervalIntegrable_const
    (ae_of_all _ fun t _ ↦ (hHc.tendsto (t, x t)).comp (tendsto_const_nhds.prodMk_nhds (hx t)))
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have hloop : Continuous fun t : ℝ ↦ u (endChart q (q.endSign * R, t)) :=
      hu.comp_continuous ((contDiff_endChart q 0).continuous.comp (by fun_prop)) (hmem hR)
    exact (hHc.comp (continuous_id.prodMk hloop)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with R hR
    refine ae_of_all _ fun t ht ↦ ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht)
    exact hC₀ (t, u (endChart q (q.endSign * R, t))) ⟨ht', huK _ (hmem hR t)⟩

end Floer

namespace SmoothTwoForm

open Floer

section PositiveEndChart

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- Beyond `T₀` on the end `q`, the components of `K` in the positive end chart are differentiable
in the target point when the end Hamiltonian is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {q : Puncture} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (v : ℂ) (y : M) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) y := by
  have hre : T₀ ≤ q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]
    simpa [← mul_assoc] using hζ
  have h : (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) = fun x ↦
      q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v •
        H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im x := by
    funext x
    rw [hKH q _ x hre, smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [h]
  exact ((hHd q _) y).const_smul _

/-- Reading an orbit of the positive end Hamiltonian `H'_q` on a manifold with the time `±t` of the
end gives an orbit of `H_q`. -/
theorem hasMFDerivAt_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I x t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t))))
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t ↦ x (q.endSign * t)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))) := by
  have hg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ q.endSign * s) t
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id t).const_smul q.endSign)
  have hH' : positiveEndHamiltonian H q (q.endSign * t) = q.endSign • H q t := by
    funext y
    simp only [positiveEndHamiltonian_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      endSign_mul_self, one_mul]
  have hd : HasMFDerivAt 𝓘(ℝ, ℝ) I x (q.endSign * t)
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (q.endSign • ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))) := by
    simpa only [hH', ω.hamiltonianVectorField_const_smul] using hx (q.endSign * t)
  have hlin (v : TangentSpace I (x (q.endSign * t))) :
      ((1 : ℝ →L[ℝ] ℝ).smulRight (q.endSign • v)).comp (q.endSign • ContinuousLinearMap.id ℝ ℝ) =
        (1 : ℝ →L[ℝ] ℝ).smulRight v := by
    ext
    simp [smul_smul]
  exact (hd.comp t hg).congr_mfderiv (hlin _)

/-- A curve `x` in `M` is a `1`-periodic orbit of the positive end Hamiltonian `H'_q` if and only
if `t ↦ x (±t)` is a `1`-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  constructor
  · intro hx
    obtain ⟨hxd, hxper⟩ := mem_periodicSolutions.1 hx
    exact mem_periodicSolutions.2 ⟨hasMFDerivAt_comp_endSign_mul hxd,
      periodic_comp_endSign_mul hxper⟩
  · intro hx
    obtain ⟨hxd, hxper⟩ := mem_periodicSolutions.1 hx
    have hH'' : positiveEndHamiltonian (fun r ↦ positiveEndHamiltonian H r) q = H q := by
      funext t y
      simp only [positiveEndHamiltonian_apply, ← mul_assoc, endSign_mul_self, one_mul]
    have hx'' : (fun t ↦ x (q.endSign * (q.endSign * t))) = x := by
      funext t
      simp only [← mul_assoc, endSign_mul_self, one_mul]
    have hgoal (w : ℝ → M) (hw : w = fun t ↦ x (q.endSign * (q.endSign * t))) :
        ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I w t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (w t))) := by
      subst hw
      exact hasMFDerivAt_comp_endSign_mul (ω := ω)
        (H := fun r ↦ positiveEndHamiltonian H r) (q := q) (by rwa [hH''])
    have hper := periodic_comp_endSign_mul (q := q) (x := fun t ↦ x (q.endSign * t)) hxper
    rw [hx''] at hper
    exact mem_periodicSolutions.2 ⟨hgoal x hx''.symm, hper⟩

/-- On the positive end beyond `T₀`, the pulled-back perturbation has the same perturbed derivative
as `H'_q(t) dt`. -/
private theorem perturbedMFDeriv_comp_positiveEndChart_eq
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ =
      ω.perturbedMFDeriv
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal)
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag)
        (u ∘ positiveEndChart q) ζ := by
  have hs : perturbationPullback (positiveEndChart q)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal ζ =
        fun _ ↦ 0 :=
    funext (perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ)
  have ht : perturbationPullback (positiveEndChart q)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag ζ =
        positiveEndHamiltonian H q ζ.2 :=
    funext (perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ)
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [perturbedMFDeriv_apply, hs, ht]

/-- **The ends of a Floer pair of pants in a manifold solve the half-cylinder Floer equation.** Let
`K` be equal to `H_q(t) dt` beyond `T₀` on each end `q`, and let `u` solve `(du - X_K)^{0,1} = 0`
for an almost complex structure `J` on `T_{u(φ'_q(ζ))} M` at the image `φ'_q(ζ)` of a point `ζ`
with `ζ.1 ≥ T₀` of the positive end chart. Then `u ∘ φ'_q` solves the half-cylinder Floer equation
at `ζ` for the positive end Hamiltonian `H'_q`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {u : ℝ × ℝ → M}
    {q : Puncture} {ζ : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))}
    (hζ : T₀ ≤ ζ.1) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ).toLinearMap := by
  rw [perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζ]
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)
    (isComplexLinearMap_fderiv_positiveEndChart q ζ) hfloer

/-- **The energy of an end of a Floer pair of pants in a manifold.** Under the hypotheses of
`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`, the energy of
`u ∘ φ'_q` for the end Hamiltonian `H'_q` over the half-cylinder `(a, ∞) × [0, 1]`, for
`a ≥ max T₀ 0`, is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {u : ℝ × ℝ → M}
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal) (q : Puncture) {a : ℝ}
    (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  set ed : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set s : Set (ℝ × ℝ) := Ioi a ×ˢ Ioo 0 1
  have hs : MeasurableSet s := measurableSet_Ioi.prod measurableSet_Ioo
  -- The closed band differs from the open one by a null set.
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] s := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc.symm
  -- On the open band the energy density is the Jacobian times the energy density of `u`.
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * ed (positiveEndChart q ζ) := by
    intro ζ hζ
    have hζ₀ : 0 < ζ.1 := ha₀.trans_lt hζ.1
    have hζT : T₀ ≤ ζ.1 := haT.trans hζ.1.le
    have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) hζ₀
    rw [floerEnergyDensity_def, perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζT,
      ← floerEnergyDensity_def, abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
    exact ω.floerEnergyDensity_perturbationPullback
      (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
      ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
      ((hu _ hS).mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hS))
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT 1 _)
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT Complex.I _)
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs
    ((injOn_positiveEndChart q).mono (prod_mono (subset_univ _) le_rfl))
    (fun ζ _ ↦ (contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hdens]
  refine lintegral_mono_set ?_
  rintro _ ⟨ζ, hζ, rfl⟩
  exact positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ.1)

end PositiveEndChart

namespace IsNondegenerate

section BreakingAndConvergence

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M]
  [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ}
  {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ} {e : M → F}

omit [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- The positive end chart maps `(a, ∞) × ℝ` into `S` whenever `0 ≤ a`. -/
private theorem mapsTo_positiveEndChart_of_nonneg (q : Puncture) {a : ℝ} (ha₀ : 0 ≤ a) :
    MapsTo (positiveEndChart q) (Ioi a ×ˢ univ) thricePuncturedSphereReal :=
  fun _ hz ↦ positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz.1)

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Coordinate form of the half-cylinder Floer equation for `u ∘ φ'_q` beyond `max T₀ 0`. -/
private theorem mfderiv_comp_positiveEndChart_floer
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {q : Puncture} {z : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z))}
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q z)).toLinearMap)
    (hz₀ : 0 < z.1) (hzT : T₀ ≤ z.1) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z stdComplexLineReal +
      J (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z stdComplexLineImag -
          ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
            ((u ∘ positiveEndChart q) z)) = 0 := by
  have hHd : ∀ r t, MDifferentiable I 𝓘(ℝ) (H r t) := fun r t ↦
    ((hHs r).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) hz₀
  have hcl := ω.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd hzT
    ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).mdifferentiableAt one_ne_zero)
    hfloer
  have heq := (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z J).1 hcl
  rwa [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] at heq

/-- **A finite-energy Floer pair of pants in a manifold breaks off a periodic orbit at each end.**
Let `K` equal `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C¹` Hamiltonians `H_q` on
a finite-dimensional manifold `M` with a nondegenerate two-form `ω`. Let `u` be `C¹` on `S` with
image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy for almost
complex structures uniformly tame with respect to a `C¹` map `e : M → F` injective with injective
differential on `B`, `c ‖d e v‖² ≤ ω(v, J z v)` (`c > 0`). Then at each end `q` there are `σ_n → ∞`
and a `1`-periodic orbit `y` of `X_{H_q}` in `B` such that the end loops `t ↦ u(φ_q(±σ_n, t))`
converge to `y`, pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max T₀ 0
  have ha₀ : 0 ≤ a := le_max_right _ _
  have haT : T₀ ≤ a := le_max_left _ _
  have hHd : ∀ r t, MDifferentiable I 𝓘(ℝ) (H r t) := fun r t ↦
    ((hHs r).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hmaps := mapsTo_positiveEndChart_of_nonneg q ha₀
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ positiveEndChart q) (Ioi a ×ˢ univ) :=
    hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn hmaps
  have hE' := ne_top_of_le_ne_top hE
    (ω.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      (hu.mdifferentiableOn one_ne_zero) q ha₀ haT)
  let J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z)) :=
    fun z ↦ J (positiveEndChart q z)
  -- Apply the manifold half-cylinder theorem in the positive end chart.
  obtain ⟨x, hx, hxB, σ, -, hσ, hconv, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (hmaps ⟨hs, mem_univ _⟩)) J' hc
      (fun z hz v ↦ hJc _ (hmaps ⟨hz.1, mem_univ _⟩) v)
      (fun z hz ↦ mfderiv_comp_positiveEndChart_floer hKH hH hHs hu
        (hfloer _ (hmaps ⟨hz.1, mem_univ _⟩)) (ha₀.trans_lt hz.1) (haT.trans hz.1.le))
      hE'
  refine ⟨fun t ↦ x (q.endSign * t), (ω.mem_periodicSolutions_positiveEndHamiltonian_iff).1 hx,
    fun t ↦ hxB _, σ, hσ, ?_, fun t ↦ ?_⟩
  · have hloop (n : ℕ) : (fun t ↦ e (u (endChart q (q.endSign * σ n, t)))) =
        (fun t ↦ e ((u ∘ positiveEndChart q) (σ n, t))) ∘ fun t ↦ q.endSign * t := by
      funext t
      simp only [comp_apply, endChart_eq_positiveEndChart]
    rw [funext hloop]
    exact hconv.comp _
  · simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off a periodic orbit at each
end.** The specialization of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` to
`B = univ` when `M` is compact. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH hHs he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE q
  exact ⟨y, hy, h⟩

/-- **Whole-end convergence of a Floer pair of pants in a manifold to an isolated orbit.** Let `K`
equal `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C¹` Hamiltonians `H_q`, and let `u`
be `C¹` on `S`, with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with
finite energy. Fix an end `q` and a `C¹` map `e : M → F` injective with injective differential on
`B`, and suppose that on some half-cylinder `s > b` of `φ'_q` the derivative of `e ∘ u ∘ φ'_q` is
bounded and `c ‖d e v‖² ≤ ω(v, J v)` (`c > 0`). If every `1`-periodic orbit of `H_q` in `B` is
isolated at `t = 0` among `1`-periodic orbits of `H_q` in `B`, then the end loops
`t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}` in `B`,
pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_eventually_eq
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture)
    (hiso : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      ∀ᶠ p in 𝓝 (y 0), ∀ z ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, z t ∈ B) → z 0 = p → z = y)
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  have hHd : ∀ r t, MDifferentiable I 𝓘(ℝ) (H r t) := fun r t ↦
    ((hHs r).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hmaps := mapsTo_positiveEndChart_of_nonneg q ha₀
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ positiveEndChart q) (Ioi a ×ˢ univ) :=
    hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn hmaps
  have hE' := ne_top_of_le_ne_top hE
    (ω.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      (hu.mdifferentiableOn one_ne_zero) q ha₀ haT)
  -- Time reversal `t ↦ ±t` fixes `t = 0`, so isolation for `H_q` gives isolation for `H'_q`.
  have hiso' : ∀ x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
      (∀ t, x t ∈ B) →
      ∀ᶠ p in 𝓝 (x 0), ∀ z ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
        (∀ t, z t ∈ B) → z 0 = p → z = x := by
    intro x hx hxB
    have hx' := (ω.mem_periodicSolutions_positiveEndHamiltonian_iff).1 hx
    have h₀ := hiso _ hx' (fun t ↦ hxB _)
    rw [mul_zero] at h₀
    refine h₀.mono fun p hp z hz hzB hzp ↦ ?_
    have hz' := (ω.mem_periodicSolutions_positiveEndHamiltonian_iff).1 hz
    have heq := hp _ hz' (fun t ↦ hzB _) (by simpa only [mul_zero] using hzp)
    funext t
    simpa only [← mul_assoc, endSign_mul_self, one_mul] using congrFun heq (q.endSign * t)
  let J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z)) :=
    fun z ↦ J (positiveEndChart q z)
  obtain ⟨x, hx, hxB, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_eventually_eq
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (hmaps ⟨hs, mem_univ _⟩)) J' hc
      (fun z hz v ↦ hJc z (hab z hz.1) v)
      (fun z hz ↦ mfderiv_comp_positiveEndChart_floer hKH hH hHs hu
        (hfloer _ (hmaps ⟨hz.1, mem_univ _⟩)) (ha₀.trans_lt hz.1) (haT.trans hz.1.le))
      hE' (fun z hz ↦ hC z (hab z hz.1)) hiso'
  refine ⟨fun t ↦ x (q.endSign * t), (ω.mem_periodicSolutions_positiveEndHamiltonian_iff).1 hx,
    fun t ↦ hxB _, ?_, fun t ↦ ?_⟩
  · have hloop (s : ℝ) : (fun t ↦ e (u (endChart q (q.endSign * s, t)))) =
        (fun t ↦ e ((u ∘ positiveEndChart q) (s, t))) ∘ fun t ↦ q.endSign * t := by
      funext t
      simp only [comp_apply, endChart_eq_positiveEndChart]
    rw [funext hloop]
    exact hconv.comp _
  · simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **The ends of a Floer pair of pants in a manifold converge to nondegenerate orbits.** Let `ω` be
a nondegenerate two-form on a boundaryless Hausdorff manifold `M` modelled on a finite-dimensional
space, let `K` equal `H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C¹` Hamiltonians
`H_q`, and let `u` be `C¹` on `S`, with image in a compact set `B ⊆ M`, solving
`(du - X_K)^{0,1} = 0` on `S` with finite energy. Fix an end `q` on which `H_q` is `C²` and every
`1`-periodic orbit `y` of `H_q` in `B` is nondegenerate — `y(0)` is a nondegenerate fixed point of
the time-one map of `X_{H_q}` — and suppose that on some half-cylinder `s > b` of `φ'_q` the
derivative of `e ∘ u ∘ φ'_q` is bounded and `c ‖d e v‖² ≤ ω(v, J v)` (`c > 0`). Then the end loops
`t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}` in `B`,
pointwise in `M` and uniformly after applying `e`. -/
theorem
  exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  have hXH := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    (hHq.of_le (by norm_num))
  refine hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_eventually_eq
    hKH hH hHs he hB he_inj hde hu huB J hfloer hE q (fun y hy hyB ↦ ?_) hC hc hJc
  have hiso := eventually_forall_mem_periodicSolutions_eq_of_isNondegenerateFixedPt hXH
    (mem_periodicSolutions.1 hy).1 (s := 0) (T := 1) (by simpa only [zero_add] using hnd y hy hyB)
  exact hiso.mono fun p hp z hz _ ↦ hp z hz

/-- **The ends of a Floer pair of pants in a closed manifold converge to nondegenerate orbits.** The
specialization of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`
to `B = univ` when `M` is compact. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH
      hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE q
      hHq (fun y hy _ ↦ hnd y hy) hC hc hJc
  exact ⟨y, hy, h⟩

end BreakingAndConvergence

/-! ### The energy identity and topological energy bound at asymptotic orbits -/

section EnergyAtAsymptoticOrbits

-- `[IsManifold I ⊤ M]` matches `PairOfPants.Energy.Identity` and `PairOfPants.Energy.Asymptotic`.
variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ}
  {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ} {e : M → F}

/-- **The pair-of-pants energy identity with derived asymptotic orbits, for a manifold target.**
Let `ω` be a nondegenerate two-form on a boundaryless Hausdorff manifold `M` modelled on a
finite-dimensional space, and let `K` be `C¹` on `S × M` and equal to `H_q(t) dt` beyond `T₀` on
each end `q` for `1`-periodic `C²` Hamiltonians `H_q` whose `1`-periodic orbits in a compact set
`B ⊆ M` are nondegenerate. Let `u` be `C¹` on `S`, with image in `B`, solving
`(du - X_K)^{0,1} = 0` on `S` for `ω`-tamed almost complex structures `J` with finite energy,
integrable area density and integrable curvature `R_K(u)`. If on each end `q` there is a
half-cylinder `s > b_q` on which `e ∘ u ∘ φ'_q` has bounded derivative and `J` is uniformly tame
with respect to `e`, then `u` converges as `s → ∞` on each end `q` to a `1`-periodic orbit `y_q` of
`X_{H_q}` in `B`, its Floer energy density is integrable on `S`, and
`∫_S E(u) = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hend : ∀ q, ∃ b C c, 0 < c ∧
      (∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) ∧
      ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
        c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
          hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hHs₁ : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  have hex (q : Puncture) :
      ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
    obtain ⟨b, C, c, hc, hC, hJc⟩ := hend q
    exact hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      hKH hH hHs₁ he hB he_inj hde hu huB J hfloer hE q (hHs q) (hnd q) hC hc hJc
  choose y hy hyB hconv hpt using hex
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hh (q : Puncture) :
      Tendsto (fun σ ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t)))) atTop
        (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t))) :=
    tendsto_intervalIntegral_endLoop_of_isCompact (hHs q).continuous hB hu.continuousOn huB (hpt q)
  have hpos : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  rw [IntegrableOn, hS] at hA hR
  have hint := hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hpos hA hR hh
  refine ⟨y, fun q ↦ ⟨hy q, hyB q, hconv q, hpt q⟩, by rwa [IntegrableOn, hS], ?_⟩
  simp only [hS]
  exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hint hA hR hh

/-- **The energy identity and topological energy bound for `pairOfPantsPerturbation` at asymptotic
orbits.** For the pair-of-pants perturbation `K = pairOfPantsPerturbation H` of `1`-periodic `C²`
Hamiltonians `H_q` whose `1`-periodic orbits in `B` are nondegenerate, curvature integrability is
automatic; if moreover `|H_q| ≤ M_q`, the symplectic area plus the Hamiltonian boundary terms at the
derived asymptotic `1`-periodic orbits `y_q` is bounded below by `-∑ q, M_q`. -/
theorem
  exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hend : ∀ q, ∃ b C c, 0 < c ∧
      (∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) ∧
      ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
        c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
          hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      (∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z)) ∧
      ∀ ⦃M₀ : Puncture → ℝ⦄, (∀ q t x, |H q t x| ≤ M₀ q) →
        -∑ q, M₀ q ≤
          (∫ z in thricePuncturedSphereReal,
              (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
                (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
            ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  have hHs₁ : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  obtain ⟨y, hy, hint, hid⟩ :=
    hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_of_isCompact
      (K := pairOfPantsPerturbation H) (T₀ := 2)
      (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs₁ w x)
      (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x)
      hH hHs he hB he_inj hde hu huB hJ hfloer hE hA
      (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs₁ hu.continuousOn)
      hnd hend
  refine ⟨y, hy, hint, hid, fun M₀ hM₀ ↦ ?_⟩
  exact hω.neg_sum_le_integral_add_sum_of_isComplexLinearMap hH hHs₁ hM₀ hu
    (fun q t ↦ by simpa only [← endChart_mk] using (hy q).2.2.2 t) hint hA hJ hfloer

/-- **The energy identity and topological energy bound for `pairOfPantsPerturbation` on a closed
manifold.** The specialization of `IsNondegenerate` theorem
`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact` to
`B = univ` when `M` is compact. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hend : ∀ q, ∃ b C c, 0 < c ∧
      (∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) ∧
      ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
        c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
          hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      (∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z)) ∧
      ∀ ⦃M₀ : Puncture → ℝ⦄, (∀ q t x, |H q t x| ≤ M₀ q) →
        -∑ q, M₀ q ≤
          (∫ z in thricePuncturedSphereReal,
              (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
                (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
            ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  obtain ⟨y, hy, h⟩ :=
    hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
      hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hJ hfloer hE
      hA (fun q y hy _ ↦ hnd q y hy) hend
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2.1, (hy q).2.2.2⟩, h⟩

end EnergyAtAsymptoticOrbits

end IsNondegenerate

end SmoothTwoForm

end TauCeti
