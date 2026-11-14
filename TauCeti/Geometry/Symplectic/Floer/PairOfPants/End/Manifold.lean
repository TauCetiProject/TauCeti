/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# Asymptotic periodic orbits at the ends of a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a symplectic
manifold, let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}`, equal to
`H_q(t) dt` beyond some height `T₀` on each end `q` for `1`-periodic Hamiltonians `H_q`, and let
`u : ℝ × ℝ → M` solve the Floer equation `(du - X_K)^{0,1} = 0` on `S` with image in a compact set
`B ⊆ M` and finite energy. This file proves that `u` breaks off a `1`-periodic orbit of `X_{H_q}`
along each end `q`, converges along the whole end `s → ∞` when the `1`-periodic orbits of `H_q` in
`B` are isolated or nondegenerate, and satisfies the manifold pair-of-pants energy identity at
these asymptotic periodic orbits. The vector-space counterparts are in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence`.

**Positive end charts.** In the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
(`TauCeti.Floer.positiveEndChart`), with the sign `+1` on the input ends `0`, `1` and `-1` on the
output end `∞`, every end has `s → +∞`, and beyond `T₀` the pulled-back perturbation is
`H'_q(t) dt` for `H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`). By the
conformal naturality of `SmoothTwoForm.perturbedMFDeriv` and `SmoothTwoForm.floerEnergyDensity`:

* `u ∘ φ'_q` has perturbed derivative `(du - X_K) ∘ dφ'_q`
  (`SmoothTwoForm.perturbedMFDeriv_comp_positiveEndChart`) and solves the half-cylinder Floer
  equation for `H'_q` beyond `T₀`
  (`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`);
* its energy density is multiplied by `det dφ'_q > 0`
  (`SmoothTwoForm.floerEnergyDensity_comp_positiveEndChart`), so its energy over `(a, ∞) × [0, 1]`
  for `a ≥ max T₀ 0` is at most the energy of `u` over `S`
  (`SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`).

**Asymptotic periodic orbits.** Reading a `1`-periodic orbit of `H'_q` with the time `±t` of the
end gives a `1`-periodic orbit of `H_q`, and vice versa
(`SmoothTwoForm.mem_periodicSolutions_positiveEndHamiltonian_iff`). Measuring uniform convergence
and uniform tameness near `B` through a `C¹` map `e : M → F` injective on `B` with injective
differential on `B`, the manifold half-cylinder theorems of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold` apply to `u ∘ φ'_q`:

* without nondegeneracy or derivative bounds, for `C¹` Hamiltonians `H_q`, there are a `1`-periodic
  orbit `y_q` of `X_{H_q}` in `B` and `s_n → ∞` such that the end loops `t ↦ u(φ_q(±s_n, t))`
  converge to `y_q` pointwise in `M` and uniformly after `e`
  (`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`);
* when `e ∘ u ∘ φ'_q` has bounded derivative on some half-cylinder `s > b` and the `1`-periodic
  orbits of `H_q` in `B` are isolated (or nondegenerate for `C²` Hamiltonians on a Hausdorff
  boundaryless manifold), the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single
  `1`-periodic orbit `y_q` of `X_{H_q}` in `B` (see
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact` in
  `TauCeti.SmoothTwoForm.IsNondegenerate`).

**The energy identity at the asymptotic orbits.** Unlike on a symplectic vector space, `ω` need not
be exact on `M`, so there is no global action functional on uncapped loops; instead, whole-end
convergence `u(φ_q(±s, t)) → y_q(t)` and compactness of `[0, 1] × B` give dominated convergence of
the boundary Hamiltonian integrals `∫₀¹ H_q(t, u(φ_q(±s, t))) dt → ∫₀¹ H_q(t, y_q(t)) dt` without
any global bound on `H_q` outside `B`. Combining this with nonnegativity of the Floer energy
density yields integrability of the energy density and the manifold pair-of-pants energy identity

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`

evaluated at the asymptotic `1`-periodic orbits `y_q`, both for general perturbations cylindrical
on the ends (`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`) and for
`TauCeti.Floer.pairOfPantsPerturbation`
(`exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact`), together with the
lower bound on the topological energy `∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt` when the `H_q` are
bounded (`exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Manifold

namespace TauCeti.SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

section Smooth

variable [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}

/-! ### Orbits in positive end charts -/

/-- Reading a solution curve of the positive end Hamiltonian `H'_q` with the time `±t` of the end
gives a solution curve of `H_q`. -/
theorem hasMFDerivAt_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I x t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t))))
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ x (q.endSign * s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))) := by
  have hmul : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ q.endSign * s) t
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id t).const_mul q.endSign)
  have hH : positiveEndHamiltonian H q (q.endSign * t) = q.endSign • H q t := by
    funext y
    rw [Pi.smul_apply, smul_eq_mul, positiveEndHamiltonian_apply, ← mul_assoc,
      endSign_mul_self, one_mul]
  set v := ω.hamiltonianVectorField (H q t) (x (q.endSign * t))
  have hlin : (((1 : ℝ →L[ℝ] ℝ).smulRight (q.endSign • v)).comp
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) :
        ℝ →L[ℝ] TangentSpace I (x (q.endSign * t))) = (1 : ℝ →L[ℝ] ℝ).smulRight v := by
    refine ContinuousLinearMap.ext fun r : ℝ ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul, smul_smul]
    exact congrArg (· • v) (by linear_combination r * q.endSign_mul_self)
  refine ((hx (q.endSign * t)).comp t hmul).congr_mfderiv ?_
  rw [hH, hamiltonianVectorField_const_smul]
  exact hlin

/-- A curve `x` is a `1`-periodic orbit of the positive end Hamiltonian `H'_q` if and only if
`t ↦ x(±t)`, with the sign of the end `q`, is a `1`-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  refine ⟨fun hx ↦ mem_periodicSolutions.2
    ⟨hasMFDerivAt_comp_endSign_mul (mem_periodicSolutions.1 hx).1,
      periodic_comp_endSign_mul (mem_periodicSolutions.1 hx).2⟩, fun hx ↦ ?_⟩
  -- Passing to the positive end Hamiltonian a second time recovers `H_q` and `x`.
  have hH : positiveEndHamiltonian (positiveEndHamiltonian H) q = H q := by
    funext t y
    simp only [positiveEndHamiltonian_apply, ← mul_assoc, endSign_mul_self, one_mul]
  have hx' : (fun t ↦ x (q.endSign * t)) ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField
        (positiveEndHamiltonian (positiveEndHamiltonian H) q t)) 1 := by
    rwa [hH]
  have hxx : (fun t ↦ x (q.endSign * (q.endSign * t))) = x := by
    funext t
    rw [← mul_assoc, endSign_mul_self, one_mul]
  rw [← hxx]
  exact mem_periodicSolutions.2
    ⟨hasMFDerivAt_comp_endSign_mul (H := positiveEndHamiltonian H) (mem_periodicSolutions.1 hx').1,
      periodic_comp_endSign_mul (x := fun t ↦ x (q.endSign * t)) (mem_periodicSolutions.1 hx').2⟩

/-! ### The ends of a Floer pair of pants as Floer half-cylinders -/

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- Beyond `T₀` on the end `q`, the components of `K` in the global coordinate are differentiable
in the target point whenever `H_q` is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    {q : Puncture} (hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t)) {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (v : ℂ) (y : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) y := by
  have hre : T₀ ≤ q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]
    simpa [← mul_assoc] using hζ
  have h : (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) =
      q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v •
        H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im := by
    funext x
    rw [hKH q _ x hre, smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [h]
  exact (hHd _ y).const_smul _

/-- Beyond `T₀` on the positive end `q`, the half-cylinder perturbed derivative of `u ∘ φ'_q` for
`H'_q` coincides with the perturbed derivative for the pulled-back datum `(φ'_q)^*K`. -/
private theorem perturbedMFDeriv_comp_positiveEndChart_eq_perturbationPullback
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
  have hs : (fun _ : M ↦ (0 : ℝ)) = perturbationPullback (positiveEndChart q)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal ζ :=
    funext fun x ↦ (perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ x).symm
  have ht : positiveEndHamiltonian H q ζ.2 = perturbationPullback (positiveEndChart q)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag ζ :=
    funext fun x ↦
      (perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ x).symm
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply, hs, ht]

/-- **The perturbed derivative in a positive end chart.** Where `K = H_q(t) dt` beyond `T₀` on each
end `q`, the half-cylinder perturbed derivative of `u ∘ φ'_q` for `H'_q` at a point `ζ` with
`ζ.1 ≥ T₀` is `(du - X_K) ∘ dφ'_q`. No nondegeneracy of `ω` is needed. -/
theorem perturbedMFDeriv_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t))
    {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ)) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ =
      (ω.perturbedMFDeriv
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (positiveEndChart q ζ)).comp (fderiv ℝ (positiveEndChart q) ζ) := by
  rw [perturbedMFDeriv_comp_positiveEndChart_eq_perturbationPullback hKH hH hζ]
  exact ω.perturbedMFDeriv_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)

/-- **The ends of a Floer pair of pants in a manifold solve the half-cylinder Floer equation.** Let
`K = H_q(t) dt` beyond `T₀` on each end `q`, and let `u` solve `(du - X_K)^{0,1} = 0` at `φ'_q(ζ)`
with `ζ.1 ≥ T₀` for an almost complex structure `J` on `T_{u(φ'_q(ζ))} M`. Then `u ∘ φ'_q` solves
the half-cylinder Floer equation for `H'_q` at `ζ`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t))
    {u : ℝ × ℝ → M} {ζ : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (positiveEndChart q ζ)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ).toLinearMap := by
  rw [ω.perturbedMFDeriv_comp_positiveEndChart hKH hH hHd hζ hu,
    ContinuousLinearMap.toLinearMap_comp]
  exact hfloer.comp (isComplexLinearMap_fderiv_positiveEndChart q ζ)

/-- **The energy density in a positive end chart.** Beyond `T₀` on each end `q`, the half-cylinder
Floer energy density of `u ∘ φ'_q` for `H'_q` at `ζ` is `det dφ'_q(ζ)` times the energy density of
`u` at `φ'_q(ζ)`. No nondegeneracy of `ω` is needed. -/
theorem floerEnergyDensity_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t))
    {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ)) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ =
      (fderiv ℝ (positiveEndChart q) ζ).det * ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u (positiveEndChart q ζ) := by
  rw [floerEnergyDensity_def,
    perturbedMFDeriv_comp_positiveEndChart_eq_perturbationPullback hKH hH hζ,
    ← floerEnergyDensity_def]
  exact ω.floerEnergyDensity_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)

/-- **The energy of an end of a Floer pair of pants in a manifold.** Where `K = H_q(t) dt` beyond
`T₀` on each end `q`, the energy of `u ∘ φ'_q` for `H'_q` over `(a, ∞) × [0, 1]` with
`a ≥ max T₀ 0` is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {u : ℝ × ℝ → M}
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal)
    (q : Puncture) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t)) {a : ℝ} (ha₀ : 0 ≤ a)
    (haT : T₀ ≤ a) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  set s : Set (ℝ × ℝ) := Ioi a ×ˢ Ioo 0 1
  have hs : MeasurableSet s := measurableSet_Ioi.prod measurableSet_Ioo
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] s := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc.symm
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u (positiveEndChart q ζ) := by
    intro ζ hζ
    have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) (ha₀.trans_lt hζ.1)
    rw [abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
    exact ω.floerEnergyDensity_comp_positiveEndChart hKH hH hHd (haT.trans hζ.1.le)
      ((hu _ hS).mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hS))
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs
    ((injOn_positiveEndChart q).mono (prod_mono (subset_univ _) le_rfl))
    (fun ζ _ ↦ (contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hdens]
  refine lintegral_mono_set ?_
  rintro _ ⟨ζ, hζ, rfl⟩
  exact positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ.1)

/-! ### Asymptotic periodic orbits at the ends -/

section Asymptotics

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] {e : M → F} {B : Set M} {u : ℝ × ℝ → M} {c : ℝ}

omit [FiniteDimensional ℝ E] in
/-- Beyond `max T₀ 0`, the positive end chart maps into `S` and transports the pair-of-pants Floer
equation to the coordinate half-cylinder Floer equation for `H'_q`. -/
private theorem floer_halfCylinder_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a)
    {J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z))}
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J' z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (positiveEndChart q z)).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ positiveEndChart q) (Ioi a ×ˢ univ) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1,
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z stdComplexLineReal +
          J' z (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z stdComplexLineImag -
            ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
              ((u ∘ positiveEndChart q) z)) = 0) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≠ ⊤ := by
  have hHd : ∀ t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t) := fun t ↦
    (hHq.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hmaps : MapsTo (positiveEndChart q) (Ioi a ×ˢ univ) thricePuncturedSphereReal :=
    fun _ hz ↦ positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz.1)
  refine ⟨hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn hmaps, fun z hz ↦ ?_,
    ne_top_of_le_ne_top hE (ω.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH
      (hu.mdifferentiableOn one_ne_zero) q hHd ha₀ haT)⟩
  have hS : positiveEndChart q z ∈ thricePuncturedSphereReal := hmaps ⟨hz.1, mem_univ _⟩
  have hcl := ω.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (haT.trans hz.1.le)
    ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).mdifferentiableAt one_ne_zero)
    (hfloer z hz)
  have hiff := (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z (J' z)).1 hcl
  rwa [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] at hiff

namespace IsNondegenerate

/-- **A finite-energy Floer pair of pants in a manifold breaks off a periodic orbit at each end.**
Let `ω` be a nondegenerate two-form on `M`, let `K = H_r(t) dt` beyond `T₀` on each end `r` for
`1`-periodic Hamiltonians `H_r`, and let `u` be `C¹` on `S`, with image in a compact set `B ⊆ M`,
solving `(du - X_K)^{0,1} = 0` on `S` with finite energy for almost complex structures uniformly
tame through a `C¹` map `e : M → F` injective on `B` with injective differential on `B`. If `H_q`
is `C¹` on a given end `q`, there are a `1`-periodic orbit `y` of `X_{H_q}` in `B` and `s_n → ∞`
such that the loops `t ↦ u(φ_q(±s_n, t))` converge to `y` pointwise in `M` and uniformly after
applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max T₀ 0
  have ha₀ : 0 ≤ a := le_max_right T₀ 0
  have haT : T₀ ≤ a := le_max_left T₀ 0
  let J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z)) :=
    fun z ↦ J (positiveEndChart q z)
  obtain ⟨hu', hfloer', hE'⟩ := floer_halfCylinder_comp_positiveEndChart hKH hH hu q hHq ha₀ haT
    (J' := J') (fun z hz ↦ hfloer _ (positiveEndChart_mem_thricePuncturedSphereReal
      (ha₀.trans_lt hz.1))) hE
  obtain ⟨x, hx, hxB, σ, -, hσ, hux, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      J' hc
      (fun z hz v ↦ hJc _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz.1)) v)
      hfloer' hE'
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun t ↦ hxB _, σ, hσ, ?_, fun t ↦ ?_⟩
  · have hloop : (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) =
        fun n ↦ (fun t ↦ e ((u ∘ positiveEndChart q) (σ n, t))) ∘ fun t ↦ q.endSign * t := by
      funext n t
      simp only [comp_apply, endChart_eq_positiveEndChart]
    rw [hloop]
    exact hux.comp (fun t ↦ q.endSign * t)
  · simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off a periodic orbit at each
end.** Specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` to a compact
manifold `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE q
      hHq
  exact ⟨y, hy, h⟩

/-- **Convergence of an end of a Floer pair of pants in a manifold to an isolated periodic orbit.**
Let `K = H_r(t) dt` beyond `T₀` on each end `r` for `1`-periodic Hamiltonians `H_r`, and let `u` be
`C¹` on `S` with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite
energy. Fix an end `q` with `H_q` `C¹`, and suppose that on some half-cylinder `s > b` of the
positive end chart `φ'_q` the almost complex structures are uniformly tame and `e ∘ u ∘ φ'_q` has
bounded derivative, and that every `1`-periodic orbit of `X_{H_q}` in `B` is isolated at time `0`
among the `1`-periodic orbits of `X_{H_q}` in `B`. Then the end loops `t ↦ u(φ_q(±s, t))` converge
as `s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}` in `B`, pointwise in `M` and uniformly
after applying `e`. -/
theorem
    exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hiso : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) →
      ∀ᶠ p in 𝓝 (y 0), ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right T₀ 0).trans (le_max_left _ b)
  have haT : T₀ ≤ a := (le_max_left T₀ 0).trans (le_max_left _ b)
  have hab : ∀ z : ℝ × ℝ, a < z.1 → b < z.1 := fun _ hz ↦ (le_max_right _ b).trans_lt hz
  let J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z)) :=
    fun z ↦ J (positiveEndChart q z)
  obtain ⟨hu', hfloer', hE'⟩ := floer_halfCylinder_comp_positiveEndChart hKH hH hu q hHq ha₀ haT
    (J' := J') (fun z hz ↦ hfloer _ (positiveEndChart_mem_thricePuncturedSphereReal
      (ha₀.trans_lt hz.1))) hE
  -- Isolation for `H_q` at `t = 0` gives isolation for `H'_q`, since `q.endSign * 0 = 0`.
  have hiso' : ∀ x ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1, (∀ t, x t ∈ B) →
      ∀ᶠ p in 𝓝 (x 0), ∀ x' ∈ periodicSolutions
          (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
        (∀ t, x' t ∈ B) → x' 0 = p → x' = x := by
    intro x hx hxB
    have hy := mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx
    have hev := hiso (fun t ↦ x (q.endSign * t)) hy fun t ↦ hxB _
    rw [mul_zero] at hev
    refine hev.mono fun p hp x' hx' hx'B hx'p ↦ funext fun t ↦ ?_
    have h := congrFun (hp (fun s ↦ x' (q.endSign * s))
      (mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx') (fun s ↦ hx'B _)
      (by simpa only [mul_zero] using hx'p)) (q.endSign * t)
    simpa only [← mul_assoc, endSign_mul_self, one_mul] using h
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact_of_eventually
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      J' hc (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE'
      (fun z hz ↦ hC z (hab z hz.1)) hiso'
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun t ↦ hxB _, ?_, fun t ↦ ?_⟩
  · have hloop : (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) =
        fun s ↦ (fun t ↦ e ((u ∘ positiveEndChart q) (s, t))) ∘ fun t ↦ q.endSign * t := by
      funext s t
      simp only [comp_apply, endChart_eq_positiveEndChart]
    rw [hloop]
    exact hux.comp (fun t ↦ q.endSign * t)
  · simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Convergence of an end of a Floer pair of pants in a manifold to a nondegenerate periodic
orbit.** Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, let
`K = H_r(t) dt` beyond `T₀` on each end `r` for `1`-periodic Hamiltonians `H_r`, and let `u` be `C¹`
on `S` with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite
energy. Fix an end `q` with `H_q` `C²`; if on some half-cylinder `s > b` of `φ'_q` the almost
complex structures are uniformly tame and `e ∘ u ∘ φ'_q` has bounded derivative, and every
`1`-periodic orbit `y` of `X_{H_q}` in `B` has `y 0` a nondegenerate fixed point of
`timeDependentFlowOf X_{H_q} 0 1`, then `t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a single
`1`-periodic orbit `y` of `X_{H_q}` in `B`, pointwise in `M` and uniformly after `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q))) {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    (hHq.of_le (by norm_num))
  have hiso : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y := fun y hy hyB ↦
    (eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt hX
      (mem_periodicSolutions.1 hy).1 (s := 0) (T := 1)
      (by simpa only [zero_add] using (hnd y hy hyB).eventually_not_isFixedPt)).mono
      fun p hp y' hy' _ hy'p ↦ hp y' hy' hy'p
  exact
    exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually
      hω hKH hH he hB he_inj hde hu huB J hfloer hE q (hHq.of_le one_le_two) hC hc hJc hiso

/-- **Convergence of an end of a Floer pair of pants in a closed manifold to a nondegenerate
periodic orbit.** Specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact` to a compact
Hausdorff boundaryless manifold `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q))) {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
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
      he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE
      q hHq hC hc hJc fun y hy _ ↦ hnd y hy
  exact ⟨y, hy, h⟩

end IsNondegenerate

end Asymptotics

end Smooth

/-! ### The manifold pair-of-pants energy identity at the asymptotic periodic orbits -/

section Energy

variable [IsManifold I ⊤ M] {ω : SmoothTwoForm I M} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {e : M → F} {B : Set M}
  {u : ℝ × ℝ → M} {c : ℝ}

namespace IsNondegenerate

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM] [ChartedSpace HM M]
  [IsManifold I ⊤ M] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] in
/-- If `u` maps `S` into a compact set `B` and its end loops on `q` converge pointwise to `y`, the
integrals of a continuous Hamiltonian `G` along the end loops converge to `∫₀¹ G(t, y(t)) dt`
without assuming any bound on `G` outside `[0, 1] × B`. -/
private theorem tendsto_intervalIntegral_endChart_of_isCompact {G : ℝ → M → ℝ}
    (hG : Continuous (uncurry G)) (hB : IsCompact B) (hu : ContinuousOn u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B) {q : Puncture} {y : ℝ → M}
    (hy : ∀ t, Tendsto (fun s : ℝ ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t))) :
    Tendsto (fun s : ℝ ↦ ∫ t in (0 : ℝ)..1, G t (u (endChart q (q.endSign * s, t)))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, G t (y t))) := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod hB).exists_bound_of_continuousOn hG.continuousOn
  have hmem (s : ℝ) (hs : 0 < s) (t : ℝ) :
      endChart q (q.endSign * s, t) ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal
      (by simpa only [← mul_assoc, endSign_mul_self, one_mul] using hs)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M₀) ?_ ?_
    intervalIntegrable_const
    (ae_of_all _ fun t _ ↦ (hG.tendsto (t, y t)).comp (tendsto_const_nhds.prodMk_nhds (hy t)))
  · filter_upwards [eventually_gt_atTop 0] with s hs
    have hloop : Continuous fun t : ℝ ↦ u (endChart q (q.endSign * s, t)) :=
      hu.comp_continuous ((contDiff_endChart q 0).continuous.comp (by fun_prop)) (hmem s hs)
    exact (hG.comp (continuous_id.prodMk hloop)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with s hs
    refine ae_of_all _ fun t ht ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact hM₀ (t, u (endChart q (q.endSign * s, t)))
      ⟨⟨ht.1.le, ht.2⟩, huB _ (hmem s hs t)⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Uniform coercivity `c ‖d e v‖² ≤ ω(v, J v)` with `c > 0` and injective `d e` implies that `ω`
tames `J`. -/
private theorem tames_of_tame_mvfderiv (hω : ω.IsNondegenerate) {p : M}
    (hde : Injective (mvfderiv I e p)) {J : AlmostComplexStructure (TangentSpace I p)} (hc : 0 < c)
    (hJc : ∀ v, c * ‖mvfderiv I e p v‖ ^ 2 ≤ hω.symplecticFormAt p v (J v)) :
    (hω.symplecticFormAt p).Tames J := fun v hv ↦
  have hev : mvfderiv I e p v ≠ 0 := fun h0 ↦ hv (hde (h0.trans (map_zero _).symm))
  (mul_pos hc (pow_pos (norm_pos_iff.2 hev) 2)).trans_le (hJc v)

/-- **The manifold pair-of-pants energy identity at nondegenerate asymptotic periodic orbits.** Let
`ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, let `K` be `C¹` on
`S × M` and equal to `H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C²` Hamiltonians
`H_q`, and let `u` be a `C¹` finite-energy solution of `(du - X_K)^{0,1} = 0` on `S` with image in
a compact set `B ⊆ M`, integrable symplectic area density, integrable curvature `R_K(u)`, uniformly
tame almost complex structures measured through `e : M → F`, and bounded end derivatives
`‖d(e ∘ u ∘ φ'_q)‖ ≤ C_q` beyond `b_q`. If every `1`-periodic orbit of `X_{H_q}` in `B` is
nondegenerate, then on each end `q` the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a
`1`-periodic orbit `y_q` of `X_{H_q}` in `B`, the Floer energy density of `u` is integrable over
`S`, and

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
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
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
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
  have hex : ∀ q, ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := fun q ↦ by
    obtain ⟨b, C, hbC⟩ := hC q
    have hmem (z : ℝ × ℝ) (hz : max b 0 < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
      positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right b 0).trans_lt hz)
    exact hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      hKH hH he hB he_inj hde hu huB J hfloer hE q (hHs q)
      (fun z hz ↦ hbC z ((le_max_left b 0).trans_lt hz)) hc
      (fun z hz v ↦ hJc _ (hmem z hz) v) (hnd q)
  choose y hy using hex
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hA' : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by rwa [IntegrableOn, hS] at hA
  have hR' : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
    rwa [IntegrableOn, hS] at hR
  have he_nonneg : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z := fun z hz ↦
    floerEnergyDensity_nonneg hω
      (tames_of_tame_mvfderiv hω (hde _ (huB z hz)) hc (hJc z hz)) (hfloer z hz)
  have hh : ∀ q, Tendsto (fun σ ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t))))
      atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t))) := fun q ↦
    tendsto_intervalIntegral_endChart_of_isCompact (hHs₁ q).continuous hB hu.continuousOn huB
      (hy q).2.2.2
  have hEint := hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu he_nonneg
    hA' hR' hh
  refine ⟨y, hy, by rwa [IntegrableOn, hS], ?_⟩
  simp only [hS]
  exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hEint hA' hR' hh

/-- **The manifold energy identity of the pair-of-pants perturbation at nondegenerate asymptotic
periodic orbits.** Specialization of
`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact` to
`TauCeti.Floer.pairOfPantsPerturbation H`, for which smoothness and integrability of the curvature
hold automatically. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
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
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
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
  have hHs₁ : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  exact hω.exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    (K := pairOfPantsPerturbation H) (T₀ := 2)
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs₁ w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB J hc hJc hfloer hE hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs₁ hu.continuousOn) hC hnd

/-- **The manifold energy identity of the pair-of-pants perturbation in a closed manifold.**
Specialization of `exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact` to a
compact Hausdorff boundaryless manifold `M`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
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
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
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
    hω.exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact hH hHs he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE hA
      hC fun q y hy _ ↦ hnd q y hy
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hid⟩

/-- **Lower bound on the topological energy at nondegenerate asymptotic periodic orbits.** Under
the hypotheses of `exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact`, if
moreover `|H_q(t, x)| ≤ M_H q`, then the topological energy
`∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt` at the asymptotic `1`-periodic orbits `y_q` is at least
`-(M_H 0 + M_H 1 + M_H ∞)`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    {M_H : Puncture → ℝ} (hMH : ∀ q t x, |H q t x| ≤ M_H q)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
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
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  obtain ⟨y, hy, hEint, -⟩ :=
    hω.exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact hH hHs he hB he_inj
      hde hu huB J hc hJc hfloer hE hA hC hnd
  refine ⟨y, hy, hω.neg_sum_le_integral_add_sum_of_isComplexLinearMap hH
    (fun q ↦ (hHs q).of_le one_le_two) hMH hu
    (fun q t ↦ by simpa only [endChart_mk] using (hy q).2.2.2 t) hEint hA
    (fun z hz ↦ tames_of_tame_mvfderiv hω (hde _ (huB z hz)) hc (hJc z hz)) hfloer⟩

/-- **Lower bound on the topological energy at nondegenerate asymptotic periodic orbits in a closed
manifold.** Specialization of
`exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact` to a compact Hausdorff
boundaryless manifold `M`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    {M_H : Puncture → ℝ} (hMH : ∀ q t x, |H q t x| ≤ M_H q)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
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
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  obtain ⟨y, hy, hle⟩ :=
    hω.exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact hH hHs hMH he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE hA
      hC fun q y hy _ ↦ hnd q y hy
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hle⟩

end IsNondegenerate

end Energy

end TauCeti.SmoothTwoForm
