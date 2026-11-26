/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.WeightCrossing
public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Index
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Hamiltonian.Basic

/-!
# The weighted linearized operator along a time-independent cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space with a compatible complex structure
`J`, let `H_s` be Hamiltonians depending on `s` and `γ` a curve, and let `D` be the linearized
Floer operator along the time-independent cylinder `(s, t) ↦ γ(s)`,
`D ξ = ∂s ξ + J (∂t ξ - dX_{H_s}(γ(s)) ξ)`. On the Sobolev spaces with the exponential weight
`e^{κ(s)}` of slope `c = κ'`, `D` acts as the operator `D - c(s)`
(`TauCeti.SymplecticForm.floerWeightedSobolevOperator`). This file computes its index. All
declarations below are in the namespace `TauCeti.SymplecticForm`.

* **A weight slope is a quadratic Hamiltonian.** For `Q(y) = (δ / 2) ‖y‖²`, where the inner
  product is the metric `ω(·, J ·)`, the Hamiltonian vector field is `X_Q = -δ J`, so
  `-J dX_{H + Q} = -J dX_H - δ`
  (`neg_comp_fderiv_hamiltonianVectorField_add_div_two_mul_norm_sq`). Hence `D - c(s)` is the
  linearized operator of the Hamiltonians `H_s + (c(s) / 2) ‖·‖²` along the same cylinder
  (`floerWeightedSobolevOperator_eq_floerSobolevOperator_add_div_two_mul_norm_sq`, in
  `TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization`). The curve `γ` need not be a solution
  for either family.
* **Fredholm property and index.** In a unitary trivialization, where `V = F` is a complex inner
  product space with `ω = Im ⟪·, ·⟫` and `J = i`, the linearized operator of a jointly `C²` family
  along `(s, t) ↦ γ(s)` with `‖dX_{H_s}(γ(s))‖ ≤ a < 2π` for every `s` has the index of its
  zero-mode Morse operator (`index_floerSobolevOperator_eq_index_trajectoryOperator`). For a `C²`
  slope `c` this operator is the trajectory operator of `A - c` with `A(s) = -i dX_{H_s}(γ(s))`,
  the trajectory operator on the spaces of weight `e^{κ(s)}`. Suppose `H_s` equals `H₋` near `-∞`
  and `H₊` near `+∞`, `γ` converges to `p±` at `±∞`, `c` tends to `δ±` at `±∞`, and
  `‖dX_{H_s}(γ(s))‖ + |c(s)| ≤ a < 2π` for every `s`. If `δ±` is not an eigenvalue of the
  asymptotic operator `A(p±) = -i dX_{H±}(p±)`, the negative of the Hessian of `H±` at `p±`, then
  `D - c` is Fredholm (`isFredholm_floerWeightedSobolevOperator_comp_fst`) of index
  `n_{< δ₋}(A(p₋)) - n_{< δ₊}(A(p₊))`, where `n_{< δ}(B)` is the number of eigenvalues of `B`
  below `δ`, counted with multiplicity
  (`index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank`). The points
  `p±` need not be nondegenerate critical points: `A(p±)` has finitely many eigenvalues, so every
  small nonzero limit `δ±` is non-exceptional even where `A(p±)` has a kernel. A constant slope
  `c = δ` and an autonomous Hamiltonian `H_s = H` are special cases.
* **Crossing an eigenvalue.** Hence the index depends on the slope only through the positions of
  its limits relative to the two spectra. Passing from a slope `c₁` to a slope `c₂` with limits
  `δ₁± ≤ δ₂±`, the index decreases by the number of eigenvalues of `A(p₊)` in `[δ₁₊, δ₂₊)` and
  increases by the number of eigenvalues of `A(p₋)` in `[δ₁₋, δ₂₋)`
  (`index_floerWeightedSobolevOperator_eq_add_finrank_pointSpectralSubspace_Ico`). The weight
  `e^{κ(s)}` is a decay weight at `+∞` and a growth weight at `-∞` when `c > 0`: as the limit at
  `+∞` increases through one exceptional value of `A(p₊)`, the index decreases by the dimension of
  its eigenspace (`index_floerWeightedSobolevOperator_eq_add_finrank_eigenspace_atTop`), and as the
  limit at `-∞` increases through one exceptional value of `A(p₋)`, it increases by that dimension
  (`index_floerWeightedSobolevOperator_eq_add_finrank_eigenspace_atBot`).

These are the statements of `TauCeti.Analysis.ODE.EnergyEstimate.WeightCrossing` for the trajectory
operator, carried to the Floer operator by the zero mode.

## References

* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) **12** (1985), 409–447 (the index on weighted spaces
  is locally constant in the weight and jumps at the exceptional weights by the dimension of the
  crossed asymptotic eigenspace).
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, on the linearized operator at
  time-independent solutions of a small Hamiltonian.
-/

public section

noncomputable section

open Real Set Filter Topology MeasureTheory ContinuousLinearMap
open TauCeti.CylinderSobolev
open scoped RealInnerProductSpace ENNReal

namespace TauCeti.SymplecticForm

section Unitary

/-! ### The index in a unitary trivialization -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {ω : SymplecticForm F} {H : ℝ → F → ℝ} {γ : ℝ → F} {Hm Hp : F → ℝ} {pminus pplus : F}

/-- The reduction of the weighted operator to the weight-crossing theorems. Under the hypotheses
of `index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank`, the weighted
operator `D - c` is the unweighted operator of `H_s + (c(s) / 2) ‖·‖²`, whose zero-mode comparison
is the trajectory operator of `s ↦ A(s) - c(s)` with `A(s) = -i dX_{H_s}(γ(s))`. That operator is
Fredholm of index `n_{< δ₋}(A(p₋)) - n_{< δ₊}(A(p₊))`, so `D - c` is too. -/
private theorem isFredholm_floerWeightedSobolevOperator_and_index_eq
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {c : ℝ → ℝ} (hc : ContDiff ℝ 2 c) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ + |c s| ≤ a)
    (hHm : ∀ᶠ s in atBot, H s = Hm) (hHp : ∀ᶠ s in atTop, H s = Hp)
    (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    {δminus δplus : ℝ} (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (hδminus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δminus)
    (hδplus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δplus) :
    (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) c).IsFredholm ∧
      (ω.floerWeightedSobolevOperator
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) c).index =
        (Module.finrank ℝ (Module.End.pointSpectralSubspace
        ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
          (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) (Iio δminus)) :
            ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F)
            (Iio δplus)) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hg := ω.apply_ofComplexModule_eq_inner hω
  set Jc := (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap
  have hHs (s : ℝ) : ContDiff ℝ 2 (H s) := hH.comp (contDiff_const.prodMk contDiff_id)
  have hH₁ (s : ℝ) : Differentiable ℝ (H s) := (hHs s).differentiable two_ne_zero
  have hX (s : ℝ) : Differentiable ℝ (ω.hamiltonianVectorField (H s)) :=
    (ω.contDiff_hamiltonianVectorField (n := 1) (hHs s)).differentiable one_ne_zero
  -- The shifted family `H_s + (c(s) / 2) ‖·‖²` is jointly `C²`, with `‖dX(γ(s))‖ ≤ a < 2π`.
  have hH' : ContDiff ℝ 2 (Function.uncurry fun s (x : F) ↦ H s x + c s / 2 * ‖x‖ ^ 2) :=
    hH.add (((hc.comp contDiff_fst).div_const 2).mul ((contDiff_norm_sq ℝ).comp contDiff_snd))
  have haγ' (s : ℝ) :
      ‖fderiv ℝ (ω.hamiltonianVectorField fun x ↦ H s x + c s / 2 * ‖x‖ ^ 2) (γ s)‖ ≤ a :=
    (norm_fderiv_hamiltonianVectorField_add_div_two_mul_norm_sq_le hg (hH₁ s) (hX s _)
      (c s)).trans (haγ s)
  -- `A(s) = -i dX_{H_s}(γ(s))` is continuous, and `A(s) - c(s)` is bounded.
  set A : ℝ → F →L[ℝ] F := fun s ↦ -(Jc.comp (fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)))
  have hAc : Continuous A := continuous_neg_comp_fderiv_hamiltonianVectorField_comp hH hγ
  have hshift (s : ℝ) : A s - c s • ContinuousLinearMap.id ℝ F =
      -(Jc.comp (fderiv ℝ (ω.hamiltonianVectorField fun x ↦ H s x + c s / 2 * ‖x‖ ^ 2) (γ s))) :=
    (neg_comp_fderiv_hamiltonianVectorField_add_div_two_mul_norm_sq hg (hH₁ s) (hX s _)
      (c s)).symm
  have hBL : MemLp (fun s ↦ A s - c s • ContinuousLinearMap.id ℝ F) ∞
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)) :=
    memLp_top_of_bound (hAc.sub (hc.continuous.smul continuous_const)).aestronglyMeasurable
      (‖Jc‖ * a) (.of_forall fun s ↦ by
        rw [hshift, norm_neg]
        exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (haγ' s) (norm_nonneg _)))
  have hB := hBL.coeFn_toLp.trans (.of_eq (funext hshift))
  rw [floerWeightedSobolevOperator_eq_floerSobolevOperator_add_div_two_mul_norm_sq hg
      (fun z ↦ hH₁ z.1) (fun z ↦ hX z.1 _) c,
    isFredholm_floerSobolevOperator_iff_isFredholm_trajectoryOperator hω hH' hγ ha haγ' hB,
    index_floerSobolevOperator_eq_index_trajectoryOperator hω hH' hγ ha haγ' hB]
  -- Near the ends `A` tends to `A(p±)`, the symmetric negative of the Hessian of `H±` at `p±`.
  have hsym {G : F → ℝ} {l : Filter ℝ} [l.NeBot] (hl : ∀ᶠ s in l, H s = G) (p : F) :=
    isSymmetric_neg_comp_fderiv_hamiltonianVectorField hω
      (contDiff_of_contDiff_uncurry_of_eventually_eq hH hl).contDiffAt (p := p)
  have hlim {G : F → ℝ} {l : Filter ℝ} [l.NeBot] {p : F} (hl : ∀ᶠ s in l, H s = G)
      (hγl : Tendsto γ l (𝓝 p)) :=
    tendsto_neg_comp_fderiv_hamiltonianVectorField_comp (ω := ω) hH hl hγl
  exact ⟨WeakDerivStep.isFredholm_trajectoryOperator_sub_smul_id hAc (hsym hHm pminus)
      (hsym hHp pplus) (hlim hHm hbot) (hlim hHp htop) hc.continuous hcbot hctop hδminus hδplus _
      hBL.coeFn_toLp,
    WeakDerivStep.index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank
      hAc (hsym hHm pminus) (hsym hHp pplus) (hlim hHm hbot) (hlim hHp htop) hc.continuous hcbot
      hctop hδminus hδplus _ hBL.coeFn_toLp⟩

/-- **The weighted operator along a time-independent cylinder is Fredholm.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H_s`
be jointly `C²` Hamiltonians depending on `s`, equal to `H₋` for `s` near `-∞` and to `H₊` for `s`
near `+∞`, and let `γ` be a continuous curve converging to `p₋` at `-∞` and to `p₊` at `+∞`. Let
`c` be a `C²` weight slope tending to `δ₋` at `-∞` and to `δ₊` at `+∞`, with
`‖dX_{H_s}(γ(s))‖ + |c(s)| ≤ a < 2π` for every `s`, where `δ₋` is not an eigenvalue of
`-i dX_{H₋}(p₋)` and `δ₊` is not one of `-i dX_{H₊}(p₊)`. Then the linearized operator along
`(s, t) ↦ γ(s)` on the spaces of weight `e^{κ(s)}`, `κ' = c`, the operator
`D - c : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)`, is Fredholm. -/
theorem isFredholm_floerWeightedSobolevOperator_comp_fst
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {c : ℝ → ℝ} (hc : ContDiff ℝ 2 c) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ + |c s| ≤ a)
    (hHm : ∀ᶠ s in atBot, H s = Hm) (hHp : ∀ᶠ s in atTop, H s = Hp)
    (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    {δminus δplus : ℝ} (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (hδminus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δminus)
    (hδplus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δplus) :
    (ω.floerWeightedSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) c).IsFredholm :=
  (isFredholm_floerWeightedSobolevOperator_and_index_eq hω hH hγ hc ha haγ hHm hHp hbot htop hcbot
    hctop hδminus hδplus).1

/-- **The index of the weighted operator along a time-independent cylinder.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H_s`
be jointly `C²` Hamiltonians depending on `s`, equal to `H₋` for `s` near `-∞` and to `H₊` for `s`
near `+∞`, and let `γ` be a continuous curve converging to `p₋` at `-∞` and to `p₊` at `+∞`. Let
`c` be a `C²` weight slope tending to `δ₋` at `-∞` and to `δ₊` at `+∞`, with
`‖dX_{H_s}(γ(s))‖ + |c(s)| ≤ a < 2π` for every `s`, where `δ±` is not an eigenvalue of
`A(p±) = -i dX_{H±}(p±)`, the negative of the Hessian of `H±` at `p±`. Then the linearized operator
along `(s, t) ↦ γ(s)` on the spaces of weight `e^{κ(s)}`, `κ' = c`, the operator
`D - c : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)`, has index `n_{< δ₋}(A(p₋)) - n_{< δ₊}(A(p₊))`,
where `n_{< δ}(B)` is the number of eigenvalues of `B` below `δ`, counted with multiplicity. -/
theorem index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {c : ℝ → ℝ} (hc : ContDiff ℝ 2 c) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ + |c s| ≤ a)
    (hHm : ∀ᶠ s in atBot, H s = Hm) (hHp : ∀ᶠ s in atTop, H s = Hp)
    (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    {δminus δplus : ℝ} (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (hδminus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δminus)
    (hδplus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δplus) :
    (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) c).index =
        (Module.finrank ℝ (Module.End.pointSpectralSubspace
        ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
          (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) (Iio δminus)) :
            ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F)
            (Iio δplus)) :=
  (isFredholm_floerWeightedSobolevOperator_and_index_eq hω hH hγ hc ha haγ hHm hHp hbot htop hcbot
    hctop hδminus hδplus).2

/-- **The index jumps by the eigenvalues crossed by the weight.** Under the hypotheses of
`index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank` for two weight
slopes `c₁` and `c₂` whose limits satisfy `δ₁₋ ≤ δ₂₋` at `-∞` and `δ₁₊ ≤ δ₂₊` at `+∞`, the index of
`D - c₁` is the index of `D - c₂`, plus the number of eigenvalues of `A(p₊) = -i dX_{H₊}(p₊)` in
`[δ₁₊, δ₂₊)`, minus the number of eigenvalues of `A(p₋) = -i dX_{H₋}(p₋)` in `[δ₁₋, δ₂₋)`,
counted with multiplicity. -/
theorem index_floerWeightedSobolevOperator_eq_add_finrank_pointSpectralSubspace_Ico
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ)
    {c₁ c₂ : ℝ → ℝ} (hc₁ : ContDiff ℝ 2 c₁) (hc₂ : ContDiff ℝ 2 c₂) {a : ℝ} (ha : a < 2 * π)
    (haγ₁ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ + |c₁ s| ≤ a)
    (haγ₂ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ + |c₂ s| ≤ a)
    (hHm : ∀ᶠ s in atBot, H s = Hm) (hHp : ∀ᶠ s in atTop, H s = Hp)
    (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    {δ₁minus δ₁plus δ₂minus δ₂plus : ℝ}
    (hc₁bot : Tendsto c₁ atBot (𝓝 δ₁minus)) (hc₁top : Tendsto c₁ atTop (𝓝 δ₁plus))
    (hc₂bot : Tendsto c₂ atBot (𝓝 δ₂minus)) (hc₂top : Tendsto c₂ atTop (𝓝 δ₂plus))
    (hminus : δ₁minus ≤ δ₂minus) (hplus : δ₁plus ≤ δ₂plus)
    (hδ₁minus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₁minus)
    (hδ₁plus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₁plus)
    (hδ₂minus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₂minus)
    (hδ₂plus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₂plus) :
    (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) c₁).index =
      (ω.floerWeightedSobolevOperator
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) c₂).index +
        Module.finrank ℝ (Module.End.pointSpectralSubspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F)
            (Ico δ₁plus δ₂plus)) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F)
            (Ico δ₁minus δ₂minus)) := by
  rw [index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank hω hH hγ hc₁
      ha haγ₁ hHm hHp hbot htop hc₁bot hc₁top hδ₁minus hδ₁plus,
    index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank hω hH hγ hc₂
      ha haγ₂ hHm hHp hbot htop hc₂bot hc₂top hδ₂minus hδ₂plus]
  simp only [Module.End.finrank_pointSpectralSubspace_Iio_eq_add hminus,
    Module.End.finrank_pointSpectralSubspace_Iio_eq_add hplus]
  push_cast
  ring

/-- **Crossing one exceptional value of the limit at `+∞`.** Under the hypotheses of
`index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank` for two weight
slopes `c₁` and `c₂`, with limits `δ₁₋ ≤ δ₂₋` at `-∞` and `δ₁ < δ₂` at `+∞`, suppose that
`ν ∈ (δ₁, δ₂)` is the only eigenvalue of `A(p₊) = -i dX_{H₊}(p₊)` in `[δ₁, δ₂]`, and that
`A(p₋) = -i dX_{H₋}(p₋)` has no eigenvalue in `[δ₁₋, δ₂₋]`. Then the index of `D - c₁` exceeds
that of `D - c₂` by the multiplicity of `ν`: as the limit at `+∞` of the slope of the weight, a
decay weight there when positive, increases through `ν`, the index decreases by the dimension of
the eigenspace of `A(p₊)` at `ν`. -/
theorem index_floerWeightedSobolevOperator_eq_add_finrank_eigenspace_atTop
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ)
    {c₁ c₂ : ℝ → ℝ} (hc₁ : ContDiff ℝ 2 c₁) (hc₂ : ContDiff ℝ 2 c₂) {a : ℝ} (ha : a < 2 * π)
    (haγ₁ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ + |c₁ s| ≤ a)
    (haγ₂ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ + |c₂ s| ≤ a)
    (hHm : ∀ᶠ s in atBot, H s = Hm) (hHp : ∀ᶠ s in atTop, H s = Hp)
    (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    {δ₁minus δ₂minus δ₁ δ₂ ν : ℝ}
    (hc₁bot : Tendsto c₁ atBot (𝓝 δ₁minus)) (hc₁top : Tendsto c₁ atTop (𝓝 δ₁))
    (hc₂bot : Tendsto c₂ atBot (𝓝 δ₂minus)) (hc₂top : Tendsto c₂ atTop (𝓝 δ₂))
    (hle : δ₁minus ≤ δ₂minus) (hν : ν ∈ Ioo δ₁ δ₂)
    (hminus : ∀ μ ∈ Icc δ₁minus δ₂minus, ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) μ)
    (hδ₁ : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₁)
    (hδ₂ : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₂)
    (hother : ∀ μ ∈ Ioo δ₁ δ₂, μ ≠ ν → ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) μ) :
    (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) c₁).index =
      (ω.floerWeightedSobolevOperator
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) c₂).index +
        Module.finrank ℝ (Module.End.eigenspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) ν) := by
  rw [index_floerWeightedSobolevOperator_eq_add_finrank_pointSpectralSubspace_Ico hω hH hγ hc₁ hc₂
      ha haγ₁ haγ₂ hHm hHp hbot htop hc₁bot hc₁top hc₂bot hc₂top hle (hν.1.trans hν.2).le
      (hminus _ (left_mem_Icc.2 hle)) hδ₁ (hminus _ (right_mem_Icc.2 hle)) hδ₂,
    Module.End.pointSpectralSubspace_eq_bot_iff.2 fun μ hμ ↦ hminus μ (Ico_subset_Icc_self hμ),
    Module.End.pointSpectralSubspace_Ico_eq_eigenspace (𝕜 := ℝ) (Ioo_subset_Ico_self hν) hδ₁
      hother]
  simp

/-- **Crossing one exceptional value of the limit at `-∞`.** Under the hypotheses of
`index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank` for two weight
slopes `c₁` and `c₂`, with limits `δ₁ < δ₂` at `-∞` and `δ₁₊ ≤ δ₂₊` at `+∞`, suppose that
`ν ∈ (δ₁, δ₂)` is the only eigenvalue of `A(p₋) = -i dX_{H₋}(p₋)` in `[δ₁, δ₂]`, and that
`A(p₊) = -i dX_{H₊}(p₊)` has no eigenvalue in `[δ₁₊, δ₂₊]`. Then the index of `D - c₂` exceeds
that of `D - c₁` by the multiplicity of `ν`: as the limit at `-∞` of the slope of the weight, a
growth weight there when positive, increases through `ν`, the index increases by the dimension of
the eigenspace of `A(p₋)` at `ν`. -/
theorem index_floerWeightedSobolevOperator_eq_add_finrank_eigenspace_atBot
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ)
    {c₁ c₂ : ℝ → ℝ} (hc₁ : ContDiff ℝ 2 c₁) (hc₂ : ContDiff ℝ 2 c₂) {a : ℝ} (ha : a < 2 * π)
    (haγ₁ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ + |c₁ s| ≤ a)
    (haγ₂ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ + |c₂ s| ≤ a)
    (hHm : ∀ᶠ s in atBot, H s = Hm) (hHp : ∀ᶠ s in atTop, H s = Hp)
    (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    {δ₁ δ₂ δ₁plus δ₂plus ν : ℝ}
    (hc₁bot : Tendsto c₁ atBot (𝓝 δ₁)) (hc₁top : Tendsto c₁ atTop (𝓝 δ₁plus))
    (hc₂bot : Tendsto c₂ atBot (𝓝 δ₂)) (hc₂top : Tendsto c₂ atTop (𝓝 δ₂plus))
    (hν : ν ∈ Ioo δ₁ δ₂) (hle : δ₁plus ≤ δ₂plus)
    (hplus : ∀ μ ∈ Icc δ₁plus δ₂plus, ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) μ)
    (hδ₁ : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₁)
    (hδ₂ : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₂)
    (hother : ∀ μ ∈ Ioo δ₁ δ₂, μ ≠ ν → ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) μ) :
    (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) c₂).index =
      (ω.floerWeightedSobolevOperator
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) c₁).index +
        Module.finrank ℝ (Module.End.eigenspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) ν) := by
  rw [index_floerWeightedSobolevOperator_eq_add_finrank_pointSpectralSubspace_Ico hω hH hγ hc₁ hc₂
      ha haγ₁ haγ₂ hHm hHp hbot htop hc₁bot hc₁top hc₂bot hc₂top (hν.1.trans hν.2).le hle hδ₁
      (hplus _ (left_mem_Icc.2 hle)) hδ₂ (hplus _ (right_mem_Icc.2 hle)),
    Module.End.pointSpectralSubspace_eq_bot_iff.2 fun μ hμ ↦ hplus μ (Ico_subset_Icc_self hμ),
    Module.End.pointSpectralSubspace_Ico_eq_eigenspace (𝕜 := ℝ) (Ioo_subset_Ico_self hν) hδ₁
      hother]
  simp

end Unitary

end TauCeti.SymplecticForm
