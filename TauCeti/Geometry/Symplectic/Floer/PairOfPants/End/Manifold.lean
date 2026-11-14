/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# Asymptotic orbits and energy identity at the ends of a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}`
equal to `H_q(t) dt` beyond some height `T₀` on each end `q`, for period-one Hamiltonians `H_q` on
`M`, and let `u : S → M` solve the Floer equation `(du - X_K)^{0,1} = 0` with finite energy and
image in a compact set `B ⊆ M`. This file proves that `u` breaks off a `1`-periodic orbit of `H_q`
at each end `q`, converges along the whole end when the orbits of `H_q` in `B` are isolated or
nondegenerate, and satisfies the pair-of-pants energy identity with the boundary terms evaluated at
those asymptotic orbits.

The vector-space counterparts are `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence`. On a manifold target, uniform
convergence and uniform tameness near `B` are measured through a `C¹` map `e : M → F` into a
finite-dimensional normed space, injective on `B` and with injective differential at the points of
`B`.

**Positive end charts.** In the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
(`TauCeti.Floer.positiveEndChart`), with the sign `+1` on the input ends `0`, `1` and `-1` on the
output end `∞`, the coordinate `s` tends to `+∞` along every end and `K` pulls back to `H'_q(t) dt`
beyond `T₀` for `H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`). Holomorphic
changes of coordinates preserve the manifold Floer equation and the energy density, so `u ∘ φ'_q`
is a finite-energy Floer half-cylinder in `M` for `H'_q`
(`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart` and
`SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`). Reading a `1`-periodic
orbit of `H'_q` with the time `±t` of the end gives a `1`-periodic orbit of `H_q`
(`SmoothTwoForm.mem_periodicSolutions_positiveEndHamiltonian_iff`).

**Orbits and convergence at the ends.** Applying the manifold half-cylinder theorems of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold` to `u ∘ φ'_q` gives, at each end `q`:

* along a sequence `s_n → ∞`, uniform convergence (after `e`) and pointwise convergence in `M` of
  the end loops `t ↦ u(φ_q(±s_n, t))` to a `1`-periodic orbit of `H_q` in `B`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` and
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer`, in the namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate`);
* along the whole end `s → ∞`, when `(e ∘ u) ∘ φ'_q` has bounded derivative on a half-cylinder and
  the `1`-periodic orbits of `H_q` in `B` are isolated — in particular when `H_q` is `C²` on a
  Hausdorff boundaryless manifold and each `1`-periodic orbit in `B` starts at a nondegenerate
  fixed point of `timeDependentFlowOf X_{H_q} 0 1` — uniform and pointwise convergence of
  `t ↦ u(φ_q(±s, t))` to a single `1`-periodic orbit `y_q` of `H_q`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated`,
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, and
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer`). Since time reversal
  fixes `t = 0`, isolation of `1`-periodic orbits at `t = 0` transfers directly between `H_q` and
  `H'_q`.

**The energy identity at the asymptotic orbits.** Since `[0, 1] × B` is compact, a continuous `H_q`
is automatically bounded along the end loops in `B`, so dominated convergence gives
`∫₀¹ H_q(t, u(φ_q(±s, t))) dt → ∫₀¹ H_q(t, y_q(t)) dt` without assuming a global bound on `H_q`
(`TauCeti.Floer.tendsto_intervalIntegral_endChart_of_isCompact`). Combined with
`SmoothTwoForm.IsNondegenerate.integrable_floerEnergyDensity_of_eq_smul_endAngularForm` and
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm`, this makes
the Floer energy density integrable on `S` and gives

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`

at the broken-off nondegenerate `1`-periodic orbits `y_q`, both for general perturbations that are
cylindrical on the ends
(`exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm`) and for
`TauCeti.Floer.pairOfPantsPerturbation`
(`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact` and
`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits at
  nondegenerate orbits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics and the energy identity of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian perturbations on punctured surfaces and their energy identities.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold ENNReal

namespace TauCeti

namespace Floer

/-- For a `C^n` end Hamiltonian `H_q` on a manifold, its counterpart `H'_q(t, x) = ±H_q(±t, x)` in
the positive end chart is `C^n`. -/
theorem contMDiff_uncurry_positiveEndHamiltonian {E HM M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM}
    [TopologicalSpace M] [ChartedSpace HM M] {H : Puncture → ℝ → M → ℝ} {q : Puncture}
    {n : WithTop ℕ∞} (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (uncurry (H q))) :
    ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (uncurry (positiveEndHamiltonian H q)) := by
  have h : uncurry (positiveEndHamiltonian H q) =
      (fun r : ℝ ↦ q.endSign • r) ∘ uncurry (H q) ∘
        fun p : ℝ × M ↦ (q.endSign • p.1, p.2) := by
    funext ⟨t, x⟩
    simp [uncurry, positiveEndHamiltonian_apply]
  rw [h]
  exact (contDiff_const_smul q.endSign).contMDiff.comp
    (hH.comp (((contDiff_const_smul q.endSign).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd))

/-- If `u` maps `S` into a compact set `B`, `H_q` is continuous, and the end loops
`t ↦ u(φ_q(±s, t))` converge pointwise to `x` as `s → ∞`, then the integrals
`∫₀¹ H_q(t, u(φ_q(±s, t))) dt` converge to `∫₀¹ H_q(t, x(t)) dt`. Unlike
`TauCeti.Floer.tendsto_intervalIntegral_endLoop`, no global bound on `H_q` is needed. -/
theorem tendsto_intervalIntegral_endChart_of_isCompact {M : Type*} [TopologicalSpace M]
    {H : Puncture → ℝ → M → ℝ} {q : Puncture} (hHc : Continuous (uncurry (H q))) {B : Set M}
    (hB : IsCompact B) {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B) {x : ℝ → M}
    (hx : ∀ t, Tendsto (fun s : ℝ ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (x t))) :
    Tendsto (fun s : ℝ ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
      atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (x t))) := by
  -- Over `[0, 1] × B` the continuous Hamiltonian `H_q` is bounded.
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod hB).exists_bound_of_continuousOn
    hHc.continuousOn
  have hmem {s : ℝ} (hs : 0 < s) (t : ℝ) :
      endChart q (q.endSign * s, t) ∈ thricePuncturedSphereReal := by
    rw [endChart_eq_positiveEndChart]
    exact positiveEndChart_mem_thricePuncturedSphereReal hs
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C) ?_ ?_
    intervalIntegrable_const
    (ae_of_all _ fun t _ ↦ (hHc.tendsto (t, x t)).comp (tendsto_const_nhds.prodMk_nhds (hx t)))
  · filter_upwards [eventually_gt_atTop 0] with s hs
    have hloop : Continuous fun t : ℝ ↦ u (endChart q (q.endSign * s, t)) :=
      hu.comp_continuous
        ((contDiff_endChart q 0).continuous.comp (continuous_const.prodMk continuous_id))
        (hmem hs)
    exact (hHc.comp (continuous_id.prodMk hloop)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with s hs
    refine ae_of_all _ fun t ht ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact hC (t, u (endChart q (q.endSign * s, t))) ⟨⟨ht.1.le, ht.2⟩, huB _ (hmem hs t)⟩

end Floer

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : M → F}

/-- Beyond `T₀` on the end `q`, the components of `K` in the end coordinates are differentiable in
the target point when the end Hamiltonian is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {q : Puncture} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (v : ℂ) (p : M) :
    MDifferentiableAt I 𝓘(ℝ) (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v)
      p := by
  have hre : T₀ ≤ q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]
    simpa [← mul_assoc] using hζ
  have h : (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) = fun x ↦
      H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im x *
        q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v := by
    funext x
    rw [hKH q _ x hre, smul_apply, smul_eq_mul]
  rw [h]
  exact (hHd q _ p).mul mdifferentiableAt_const

variable [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}

/-! ### Orbits in positive end charts -/

/-- Reading a `1`-periodic orbit of the positive end Hamiltonian `H'_q` with the time `±t` of the
end gives a `1`-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈
      periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1) :
    (fun t ↦ x (q.endSign * t)) ∈
      periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  obtain ⟨hx1, hx2⟩ := mem_periodicSolutions.1 hx
  refine mem_periodicSolutions.2 ⟨fun t ↦ ?_, periodic_comp_endSign_mul hx2⟩
  have hg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ ↦ q.endSign * r) t
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id t).const_smul q.endSign)
  have hH' : positiveEndHamiltonian H q (q.endSign * t) = q.endSign • H q t := by
    funext y
    simp only [positiveEndHamiltonian_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      endSign_mul_self, one_mul]
  let L₁ : ℝ →L[ℝ] TangentSpace I (x (q.endSign * t)) :=
    (1 : ℝ →L[ℝ] ℝ).smulRight
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t)) (x (q.endSign * t)))
  let L₂ : ℝ →L[ℝ] ℝ := q.endSign • ContinuousLinearMap.id ℝ ℝ
  have hL : L₁.comp L₂ =
      (1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) := by
    ext
    simp [L₁, L₂, hH', ω.hamiltonianVectorField_const_smul, smul_smul, endSign_mul_self]
  exact ((hx1 (q.endSign * t)).comp t hg).congr_mfderiv hL

/-- A curve `x` is a `1`-periodic orbit of the positive end Hamiltonian `H'_q` if and only if
`t ↦ x(±t)`, with the sign of the end, is a `1`-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  refine ⟨mem_periodicSolutions_comp_endSign_mul, fun hx ↦ ?_⟩
  let H' : Puncture → ℝ → M → ℝ := fun r t y ↦ r.endSign * H r (r.endSign * t) y
  have hH'1 : positiveEndHamiltonian H' q = H q := by
    funext t y
    simp only [H', positiveEndHamiltonian_apply, ← mul_assoc, endSign_mul_self, one_mul]
  have hH'2 : H' q = positiveEndHamiltonian H q := by
    funext t y
    simp only [H', positiveEndHamiltonian_apply]
  have hx' : (fun t ↦ (fun r ↦ x (q.endSign * r)) (q.endSign * t)) = x := by
    funext t
    simp only [← mul_assoc, endSign_mul_self, one_mul]
  have h := mem_periodicSolutions_comp_endSign_mul (ω := ω) (H := H') (by rwa [hH'1])
  rwa [hx', hH'2] at h

/-! ### The ends of a Floer pair of pants in a manifold as Floer half-cylinders -/

/-- On the positive end beyond `T₀`, the pulled-back perturbation is `H'_q(t) dt`. -/
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
  rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply, hs, ht]

/-- **The ends of a Floer pair of pants in a manifold solve the half-cylinder Floer equation.** Let
`K` be equal to `H_q(t) dt` beyond `T₀` on each end `q`, and let `u` solve `(du - X_K)^{0,1} = 0`
for an almost complex structure `J` on `T_{u(φ'_q(ζ))} M` at the image `φ'_q(ζ)` of a point `ζ`
with `s ≥ T₀` of the positive end chart. Then `u ∘ φ'_q` solves the half-cylinder Floer equation
for the end Hamiltonian `H'_q` at `ζ`. -/
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
`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`, the energy of `u ∘ φ'_q`
for `H'_q` over `(a, ∞) × [0, 1]`, for `a ≥ max T₀ 0`, is at most the energy of `u` over `S`. -/
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
  set edens : ℝ × ℝ → ℝ := ω.floerEnergyDensity
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set s : Set (ℝ × ℝ) := Ioi a ×ˢ Ioo 0 1
  have hs : MeasurableSet s := measurableSet_Ioi.prod measurableSet_Ioo
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] s := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc.symm
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * edens (positiveEndChart q ζ) := by
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

/-- In the positive end chart beyond `a ≥ max T₀ 0`, a solution `u` of `(du - X_K)^{0,1} = 0` on
`S` satisfies the coordinate half-cylinder Floer equation for `H'_q`. -/
private theorem floer_comp_positiveEndChart_eq_zero
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    {q : Puncture} {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) {z : ℝ × ℝ}
    (hz : z ∈ Ioi a ×ˢ Icc 0 1) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineReal +
      J (positiveEndChart q z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineImag -
          ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
            (u (positiveEndChart q z))) = 0 := by
  have hHd : ∀ r t, MDifferentiable I 𝓘(ℝ) (H r t) := fun r t ↦
    ((hHs r).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hS : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz.1)
  have hcl := isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (haT.trans hz.1.le)
    ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).mdifferentiableAt one_ne_zero)
    (hfloer _ hS)
  have hiff := (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z
    (J (positiveEndChart q z))).1 hcl
  have h0 : ω.hamiltonianVectorField (fun _ : M ↦ (0 : ℝ)) (u (positiveEndChart q z)) = 0 := by
    rw [ω.hamiltonianVectorField_const]
    rfl
  rwa [h0, sub_zero] at hiff

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

namespace IsNondegenerate

/-! ### Breaking off periodic orbits along sequences -/

/-- **A finite-energy Floer pair of pants in a manifold breaks off an orbit at each end.** Let `ω`
be a nondegenerate two-form on a finite-dimensional manifold `M`, `K` equal to `H_q(t) dt` beyond
`T₀` on each end `q` for `1`-periodic `C¹` Hamiltonians `H_q`, and `u` a `C¹` map on `S` with image
in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy. Let `e : M → F`
be `C¹`, injective on `B` with injective differential at the points of `B`, and suppose that the
almost complex structures satisfy `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. Then at each end `q`
there are a `1`-periodic orbit `y` of `H_q` in `B` and `s_n → ∞` such that the end loops
`t ↦ u(φ_q(±s_n, t))` converge to `y`, uniformly after `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
  have hmem (z : ℝ × ℝ) (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  have hHd : ∀ r t, MDifferentiable I 𝓘(ℝ) (H r t) := fun r t ↦
    ((hHs r).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  obtain ⟨x, hx, hxB, σ, -, hσ, hconv, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (u := fun w ↦ u (positiveEndChart q w))
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q))
      (periodic_positiveEndHamiltonian (hH q)) he hB he_inj hde
      (hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn fun z hz ↦ hmem z hz.1)
      (fun s _ t ↦ by simp only [positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (hmem (s, t) hs)) (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc _ (hmem z hz.1) v)
      (fun z hz ↦ floer_comp_positiveEndChart_eq_zero hKH hH hHs hu hfloer ha₀ haT hz)
      (ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
        (hu.mdifferentiableOn one_ne_zero) q ha₀ haT))
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_comp_endSign_mul hx,
    fun t ↦ hxB _, σ, hσ, ?_, fun t ↦ ?_⟩
  · have hloop (n : ℕ) : (fun t ↦ e (u (endChart q (q.endSign * σ n, t)))) =
        (fun t ↦ e (u (positiveEndChart q (σ n, t)))) ∘ fun t ↦ q.endSign * t := by
      funext t
      simp only [comp_apply, endChart_eq_positiveEndChart]
    rw [funext hloop]
    exact hconv.comp _
  · simpa only [endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off an orbit at each end.**
Specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` when `M` is compact
and `B = univ`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
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

/-! ### Convergence of the ends to isolated and nondegenerate orbits -/

/-- **Convergence of an end of a Floer pair of pants in a manifold to an isolated orbit.** Let `K`
be equal to `H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C¹` Hamiltonians `H_q`, and
let `u` be `C¹` on `S` with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S`
with finite energy. Fix an end `q`, suppose that on `(b, ∞) × [0, 1]` in the positive end chart
`φ'_q` the derivative of `(e ∘ u) ∘ φ'_q` is bounded and `c ‖d e v‖² ≤ ω(v, J (φ'_q z) v)` with
`c > 0`, and suppose that each `1`-periodic orbit `y` of `H_q` in `B` is isolated among the
`1`-periodic orbits of `H_q` in `B`. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to
a single `1`-periodic orbit `y` of `H_q` in `B`, uniformly after `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
    (q : Puncture) {b C : ℝ}
    (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hiso : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab {z : ℝ × ℝ} (hz : z ∈ Ioi a ×ˢ Icc 0 1) : z ∈ Ioi b ×ˢ Icc 0 1 :=
    ⟨(le_max_right _ _).trans_lt hz.1, hz.2⟩
  have hmem (z : ℝ × ℝ) (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  have hHd : ∀ r t, MDifferentiable I 𝓘(ℝ) (H r t) := fun r t ↦
    ((hHs r).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  -- Time reversal fixes `t = 0`, so isolation at `0` transfers from `H_q` to `H'_q`.
  have hiso' : ∀ x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1, (∀ t, x t ∈ B) →
      ∀ᶠ p in 𝓝 (x 0), ∀ x' ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
        (∀ t, x' t ∈ B) → x' 0 = p → x' = x := by
    intro x hx hxB
    have h0 := hiso (fun t ↦ x (q.endSign * t)) (mem_periodicSolutions_comp_endSign_mul hx)
      (fun t ↦ hxB _)
    rw [mul_zero] at h0
    refine h0.mono fun p hp x' hx' hx'B hx'0 ↦ funext fun t ↦ ?_
    have heq := congrFun (hp (fun r ↦ x' (q.endSign * r))
      (mem_periodicSolutions_comp_endSign_mul hx') (fun r ↦ hx'B _)
      (by simpa only [mul_zero] using hx'0)) (q.endSign * t)
    simpa only [← mul_assoc, endSign_mul_self, one_mul] using heq
  obtain ⟨x, hx, hxB, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
      (u := fun w ↦ u (positiveEndChart q w))
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q))
      (periodic_positiveEndHamiltonian (hH q)) he hB he_inj hde
      (hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn fun z hz ↦ hmem z hz.1)
      (fun s _ t ↦ by simp only [positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (hmem (s, t) hs)) (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z (hab hz) v)
      (fun z hz ↦ floer_comp_positiveEndChart_eq_zero hKH hH hHs hu hfloer ha₀ haT hz)
      (ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
        (hu.mdifferentiableOn one_ne_zero) q ha₀ haT))
      (fun z hz ↦ hC z (hab hz)) hiso'
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_comp_endSign_mul hx,
    fun t ↦ hxB _, ?_, fun t ↦ ?_⟩
  · have hloop (s : ℝ) : (fun t ↦ e (u (endChart q (q.endSign * s, t)))) =
        (fun t ↦ e (u (positiveEndChart q (s, t)))) ∘ fun t ↦ q.endSign * t := by
      funext t
      simp only [comp_apply, endChart_eq_positiveEndChart]
    rw [funext hloop]
    exact hconv.comp _
  · simpa only [endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Convergence of an end of a Floer pair of pants in a manifold to a nondegenerate orbit.** Let
`ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, `K` equal to `H_q(t) dt`
beyond `T₀` on each end `q` for `1`-periodic `C²` Hamiltonians `H_q`, and `u` a `C¹` map on `S`
with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy. Fix
an end `q`, suppose that on `(b, ∞) × [0, 1]` in the positive end chart `φ'_q` the derivative of
`(e ∘ u) ∘ φ'_q` is bounded and `c ‖d e v‖² ≤ ω(v, J (φ'_q z) v)` with `c > 0`, and suppose that
every `1`-periodic orbit `y` of `H_q` in `B` is nondegenerate: `y 0` is a nondegenerate fixed point
of `timeDependentFlowOf X_{H_q} 0 1`. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞`
to a single `1`-periodic orbit `y` of `H_q` in `B`, uniformly after `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
    (q : Puncture) {b C : ℝ}
    (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  refine
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated hKH hH
      (fun r ↦ (hHs r).of_le one_le_two) he hB he_inj hde hu huB J hfloer hE q hC hc hJc
      fun y hy hyB ↦ ?_
  have hiso := IsNondegenerateFixedPt.eventually_forall_mem_periodicSolutions_eq (s := 0)
    (hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
      ((hHs q).of_le (by norm_num)))
    (fun t ↦ by rw [hH q t]) one_ne_zero hy (by simpa only [zero_add] using hnd y hy hyB)
  exact hiso.mono fun p hp y' hy' _ hy'0 ↦ hp y' hy' hy'0

/-- **Convergence of an end of a Floer pair of pants in a closed manifold to a nondegenerate
orbit.** Specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact` when `M` is
compact and `B = univ`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
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
    (q : Puncture) {b C : ℝ}
    (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH
      hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE q
      hC hc hJc fun y hy _ ↦ hnd y hy
  exact ⟨y, hy, h⟩

/-! ### The energy identity at the asymptotic nondegenerate orbits -/

/-- **The pair-of-pants energy identity with nondegenerate asymptotic orbits, for a manifold
target.** Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, `K` a `C¹`
perturbation on `S × M` equal to `H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C²`
Hamiltonians `H_q`, and `u` a `C¹` map on `S` with image in a compact set `B ⊆ M`, solving
`(du - X_K)^{0,1} = 0` on `S` with finite energy and integrable symplectic area and curvature. Let
`e : M → F` be `C¹`, injective on `B` with injective differential at the points of `B`, suppose that
`c ‖d e v‖² ≤ ω(v, J z v)` on `S` with `c > 0`, that `(e ∘ u) ∘ φ'_q` has bounded derivative on
some strip `(b, ∞) × [0, 1]` at each end `q`, and that every `1`-periodic orbit of `H_q` in `B` is
nondegenerate. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to `1`-periodic orbits
`y_q` of `H_q` in `B`, the Floer energy density of `u` is integrable on `S`, and

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
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
  have hy_ex : ∀ q, ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := fun q ↦ by
    obtain ⟨b, C, hbC⟩ := hC q
    have hmem (z : ℝ × ℝ) (hz : max b 0 < z.1) :
        positiveEndChart q z ∈ thricePuncturedSphereReal :=
      positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz)
    exact hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      hKH hH hHs he hB he_inj hde hu huB J hfloer hE q
      (b := max b 0) (fun z hz ↦ hbC z ⟨(le_max_left _ _).trans_lt hz.1, hz.2⟩) hc
      (fun z hz v ↦ hJc _ (hmem z hz.1) v) (hnd q)
  choose y hy hyB hyu hyp using hy_ex
  have hh (q : Puncture) :
      Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
        atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t))) :=
    tendsto_intervalIntegral_endChart_of_isCompact (hHs q).continuous hB hu.continuousOn huB
      (hyp q)
  -- Uniform tameness relative to `e` with injective `d e` on `B` tames `J z`, so `E ≥ 0` on `S`.
  have he_nonneg (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      0 ≤ ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z := by
    refine floerEnergyDensity_nonneg hω (fun v hv ↦ ?_) (hfloer z hz)
    have hdv : mvfderiv I e (u z) v ≠ 0 := fun h0 ↦
      hv (hde _ (huB z hz) (h0.trans (map_zero _).symm))
    exact (mul_pos hc (pow_pos (norm_pos_iff.2 hdv) 2)).trans_le (hJc z hz v)
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hA' : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by rwa [IntegrableOn, hS] at hA
  have hR' : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
    rwa [IntegrableOn, hS] at hR
  have hEint := hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu he_nonneg
    hA' hR' hh
  refine ⟨y, fun q ↦ ⟨hy q, hyB q, hyu q, hyp q, hh q⟩, ?_, ?_⟩
  · rwa [IntegrableOn, hS]
  · simp only [hS]
    exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hEint hA' hR' hh

/-- **The energy identity for `pairOfPantsPerturbation` with nondegenerate asymptotic orbits in a
compact set.** Specialization of
`exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm` to
`TauCeti.Floer.pairOfPantsPerturbation H`, whose curvature is automatically integrable along `u`. -/
theorem
    exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  have hHs1 : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  exact hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs1 w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB J hc hJc hfloer hE hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn) hC hnd

/-- **The energy identity for `pairOfPantsPerturbation` on a closed manifold.** Specialization of
`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact` when
`M` is compact and `B = univ`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  obtain ⟨y, hy, hEint, hid⟩ :=
    hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
      hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc
      hfloer hE hA hC fun q y hy _ ↦ hnd q y hy
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hid⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
