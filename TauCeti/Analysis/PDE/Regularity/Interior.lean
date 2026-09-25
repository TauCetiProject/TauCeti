/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Basic
public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Interior `H²` regularity for constant coefficients

Let `A` be a constant, uniformly elliptic coefficient matrix and let `u ∈ H¹(Ω)` be a weak
solution of the divergence-form equation

`-div(A ∇u) = f` in `Ω`, with `f ∈ L²(Ω)`,

meaning `∫_Ω ⟨∇v, A ∇u⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. No boundary condition is imposed on
`u` and nothing is assumed about `∂Ω`. This file proves that `u ∈ H²_loc(Ω)`: on every open `V`
whose closure is compact and contained in `Ω`, the restriction of `u` is the first-order part of
an element of `W^{2,2}(V)`.

## Localization

The whole-space theorem `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq` does the analytic
work; what is proved here is that a cutoff of a local solution is a global one. For `ψ` smooth
and compactly supported in `Ω`, the product `ψ u`, extended by zero, lies in `H¹(ℝⁿ)` and solves

`-div(A ∇(ψ u)) = ψ f - ⟨∇u, A ∇ψ⟩ - ⟨∇ψ, A ∇u⟩ - u div(A ∇ψ)` on `ℝⁿ`,

whose right-hand side is again in `L²`, because every term carrying `u` or `∇u` also carries a
bounded, compactly supported factor built from `ψ`. The identity is checked against test
functions `φ` on `ℝⁿ`, which suffices by density
(`TauCeti.PDE.isWeakSolutionDirichlet_iff_forall_testFunction`). The term `ψ ∇u` is handled by
testing the equation for `u` against `ψ φ ∈ H¹₀(Ω)`, and the term `u ∇ψ` by the definition of the
weak derivative of `u`, tested against the components of `φ A ∇ψ`, which are test functions on
`Ω`. Choosing `ψ = 1` near `closure V` makes `ψ u` agree with `u` on `V`.

## Main declarations

* `TauCeti.PDE.exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul`: a cutoff of a weak
  solution, extended by zero, is a weak solution on the whole space with `L²` data.
* `TauCeti.PDE.exists_isWeakSolutionDirichlet_top_ae_eq_on_of_isCompact`: near a compact subset
  of `Ω`, a weak solution agrees with a whole-space weak solution.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL`: interior `H²` regularity.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1, Theorem 1 (interior `H²` regularity).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.8.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ}

omit [mu.IsAddHaarMeasure] in
/-- Expanding the first argument of a matrix bilinear form in an orthonormal basis. -/
private theorem sum_inner_mul_matrixBilinearForm (ξ η : EuclideanSpace ℝ ι) :
    ∑ i, ⟪ξ, EuclideanSpace.basisFun ι ℝ i⟫_ℝ *
        matrixBilinearForm A (EuclideanSpace.basisFun ι ℝ i) η = matrixBilinearForm A ξ η := by
  conv_rhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr' ξ]
  simp [map_sum, map_smul]

/-- The divergence `div(A ∇ψ) = ∑ᵢ ∂ᵢ (A ∇ψ)ᵢ` of the conormal field of `ψ`, computed in the
standard basis. It is the zeroth-order coefficient that commuting the operator `-div(A ∇ ·)` past
a cutoff `ψ` produces. -/
private def divMatrixGradient (A : Matrix ι ι ℝ) (ψ : EuclideanSpace ℝ ι → ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, lineDeriv ℝ (fun y => matrixBilinearForm A (EuclideanSpace.basisFun ι ℝ i) (∇ ψ y)) x
    (EuclideanSpace.basisFun ι ℝ i)

/-- The components `(A ∇ψ)ᵢ` of the conormal field of a smooth `ψ` are smooth. -/
private theorem contDiff_matrixBilinearForm_gradient {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (η : EuclideanSpace ℝ ι) :
    ContDiff ℝ ∞ (fun y => matrixBilinearForm A η (∇ ψ y)) :=
  (matrixBilinearForm A η).contDiff.comp (hψ.gradient_right (m := ∞) (by simp))

/-- The components `(A ∇ψ)ᵢ` of the conormal field are supported where `ψ` is. -/
private theorem tsupport_matrixBilinearForm_gradient_subset (ψ : EuclideanSpace ℝ ι → ℝ)
    (η : EuclideanSpace ℝ ι) :
    tsupport (fun y => matrixBilinearForm A η (∇ ψ y)) ⊆ tsupport ψ :=
  closure_minimal (fun x hx => by_contra fun hxψ => hx (by
    simp [gradient_of_notMem_tsupport hxψ])) (isClosed_tsupport ψ)

/-- `div(A ∇ψ)` vanishes off the support of `ψ`. -/
private theorem divMatrixGradient_eq_zero_of_notMem_tsupport {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {x : EuclideanSpace ℝ ι} (hx : x ∉ tsupport ψ) :
    divMatrixGradient A ψ x = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have hxi : x ∉ tsupport (fun y => matrixBilinearForm A (EuclideanSpace.basisFun ι ℝ i)
      (∇ ψ y)) := fun h => hx (tsupport_matrixBilinearForm_gradient_subset ψ _ h)
  have hd : DifferentiableAt ℝ
      (fun y => matrixBilinearForm A (EuclideanSpace.basisFun ι ℝ i) (∇ ψ y)) x :=
    (contDiff_matrixBilinearForm_gradient hψ _).differentiable (by simp) x
  rw [hd.lineDeriv_eq_fderiv, fderiv_of_notMem_tsupport ℝ hxi]
  simp

/-- `div(A ∇ψ)` is continuous for smooth `ψ`. -/
private theorem continuous_divMatrixGradient {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : Continuous (divMatrixGradient A ψ) := by
  refine continuous_finsetSum _ fun i _ => ?_
  have hh : ContDiff ℝ ∞ (fun y => matrixBilinearForm A (EuclideanSpace.basisFun ι ℝ i)
      (∇ ψ y)) := contDiff_matrixBilinearForm_gradient hψ _
  have heq : (fun x => lineDeriv ℝ (fun y => matrixBilinearForm A
      (EuclideanSpace.basisFun ι ℝ i) (∇ ψ y)) x (EuclideanSpace.basisFun ι ℝ i)) =
      fun x => fderiv ℝ (fun y => matrixBilinearForm A (EuclideanSpace.basisFun ι ℝ i)
        (∇ ψ y)) x (EuclideanSpace.basisFun ι ℝ i) :=
    funext fun x => ((hh.differentiable (by simp)) x).lineDeriv_eq_fderiv
  rw [heq]
  exact (hh.continuous_fderiv (by simp)).clm_apply continuous_const

/-- **Integration by parts against the conormal field of a cutoff.** For `u ∈ H¹(Ω)`, a smooth
`φ`, and a smooth `ψ` compactly supported in `Ω`,

`∫_Ω u (⟨∇φ, A ∇ψ⟩ + φ div(A ∇ψ)) = -∫_Ω φ ⟨∇u, A ∇ψ⟩`,

the definition of the weak gradient of `u` tested against the components of `φ A ∇ψ`. -/
private theorem setIntegral_value_mul_eq_neg (u : W1p mu Omega 2)
    {ψ φ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (hφ : ContDiff ℝ ∞ φ) :
    ∫ x in Omega, W1p.value u x * (matrixBilinearForm A (∇ φ x) (∇ ψ x)
        + φ x * divMatrixGradient A ψ x) ∂mu
      = -∫ x in Omega, φ x * matrixBilinearForm A (W1p.gradient u x) (∇ ψ x) ∂mu := by
  set b := EuclideanSpace.basisFun ι ℝ
  set h : ι → EuclideanSpace ℝ ι → ℝ := fun i y => matrixBilinearForm A (b i) (∇ ψ y)
  have hh : ∀ i, ContDiff ℝ ∞ (h i) := fun i => contDiff_matrixBilinearForm_gradient hψ (b i)
  -- Each `φ hᵢ` is a test function on `Ω`, being supported where `ψ` is.
  have hsupp : ∀ i, Function.support (fun y => φ y * h i y) ⊆ tsupport ψ := fun i x hx =>
    tsupport_matrixBilinearForm_gradient_subset (A := A) ψ (b i)
      (subset_tsupport _ fun h0 => hx (by simp only [h, h0, mul_zero]))
  let χ : ι → 𝓓(Omega, ℝ) := fun i =>
    ⟨fun y => φ y * h i y, hφ.mul (hh i), hψc.mono' (hsupp i),
      (closure_minimal (hsupp i) (isClosed_tsupport ψ)).trans hts⟩
  have hχ : ∀ i, ((χ i : 𝓓(Omega, ℝ)) : EuclideanSpace ℝ ι → ℝ) = fun y => φ y * h i y :=
    fun _ => rfl
  have hloc := (W1p.hasWeakFDerivOn u).locallyIntegrableOn
  have key : ∀ i, ∫ x in Omega, lineDeriv ℝ (χ i : EuclideanSpace ℝ ι → ℝ) x (b i) •
        W1p.value u x ∂mu =
      -∫ x in Omega, (χ i : EuclideanSpace ℝ ι → ℝ) x • ⟪W1p.gradient u x, b i⟫_ℝ ∂mu := by
    intro i
    rw [setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul, setIntegral_smul_eq_integral_smul,
      ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn
        (b i)).integral_lineDeriv_smul_eq_neg_integral_smul (χ i)]
    simp [innerSL_apply_apply]
  -- The product rule for `φ hᵢ`, in the direction `bᵢ`.
  have hderiv : ∀ i x, lineDeriv ℝ (χ i : EuclideanSpace ℝ ι → ℝ) x (b i)
      = ⟪∇ φ x, b i⟫_ℝ * h i x + φ x * lineDeriv ℝ (h i) x (b i) := by
    intro i x
    have hφx : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
    have hhx : DifferentiableAt ℝ (h i) x := ((hh i).differentiable (by simp)) x
    have hmul : DifferentiableAt ℝ (fun y => φ y * h i y) x := hφx.mul hhx
    rw [hχ, hmul.lineDeriv_eq_fderiv, hhx.lineDeriv_eq_fderiv, fderiv_fun_mul hφx hhx,
      inner_gradient_left]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hint1 : ∀ i, Integrable (fun x => lineDeriv ℝ (χ i : EuclideanSpace ℝ ι → ℝ) x (b i) •
      W1p.value u x) (mu.restrict Omega) :=
    fun i => (integrable_lineDeriv_smul_of_locallyIntegrableOn hloc (χ i) (b i)).restrict
  have hint2 : ∀ i, Integrable (fun x => (χ i : EuclideanSpace ℝ ι → ℝ) x •
      ⟪W1p.gradient u x, b i⟫_ℝ) (mu.restrict Omega) := fun i =>
    (integrable_smul_of_locallyIntegrableOn (w := fun x => ⟪W1p.gradient u x, b i⟫_ℝ)
      (by simpa [innerSL_apply_apply] using
        ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (b i)).locallyIntegrableOn_deriv)
      (χ i)).restrict
  calc ∫ x in Omega, W1p.value u x * (matrixBilinearForm A (∇ φ x) (∇ ψ x)
        + φ x * divMatrixGradient A ψ x) ∂mu
      = ∫ x in Omega, ∑ i, lineDeriv ℝ (χ i : EuclideanSpace ℝ ι → ℝ) x (b i) •
          W1p.value u x ∂mu := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hderiv, smul_eq_mul, divMatrixGradient]
        rw [← sum_inner_mul_matrixBilinearForm (A := A)]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_add, add_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [h]
        ring
    _ = ∑ i, ∫ x in Omega, lineDeriv ℝ (χ i : EuclideanSpace ℝ ι → ℝ) x (b i) •
          W1p.value u x ∂mu := integral_finsetSum _ fun i _ => hint1 i
    _ = ∑ i, -∫ x in Omega, (χ i : EuclideanSpace ℝ ι → ℝ) x • ⟪W1p.gradient u x, b i⟫_ℝ ∂mu :=
        Finset.sum_congr rfl fun i _ => key i
    _ = -∫ x in Omega, ∑ i, (χ i : EuclideanSpace ℝ ι → ℝ) x • ⟪W1p.gradient u x, b i⟫_ℝ ∂mu := by
        rw [integral_finsetSum _ fun i _ => hint2 i, Finset.sum_neg_distrib]
    _ = -∫ x in Omega, φ x * matrixBilinearForm A (W1p.gradient u x) (∇ ψ x) ∂mu := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [← sum_inner_mul_matrixBilinearForm (A := A), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hχ, h, smul_eq_mul]
        ring

/-- The right-hand side of the equation satisfied by a cutoff `ψ u` of a weak solution `u` of
`-div(A ∇u) = f`:

`-div(A ∇(ψ u)) = ψ f - ⟨∇u, A ∇ψ⟩ - ⟨∇ψ, A ∇u⟩ - u div(A ∇ψ)`. -/
private def localizedForcing (A : Matrix ι ι ℝ) (ψ : EuclideanSpace ℝ ι → ℝ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2) (x : EuclideanSpace ℝ ι) : ℝ :=
  ψ x * f x - matrixBilinearForm A (W1p.gradient u x) (∇ ψ x)
    - matrixBilinearForm A (∇ ψ x) (W1p.gradient u x) - W1p.value u x * divMatrixGradient A ψ x

/-- The localized forcing term is square integrable, since each of its terms is an `L²(Ω)`
function times a bounded one. -/
private theorem memLp_localizedForcing {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2) :
    MemLp (localizedForcing A ψ f u) 2 (mu.restrict Omega) := by
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  have hDc : HasCompactSupport (divMatrixGradient A ψ) := hψc.mono' fun x hx =>
    by_contra fun hxψ => hx (divMatrixGradient_eq_zero_of_notMem_tsupport hψ hxψ)
  obtain ⟨C, hC⟩ :=
    (continuous_divMatrixGradient (A := A) hψ).norm.bddAbove_range_of_hasCompactSupport hDc.norm
  have hgψ := ContDiff.continuous_gradient hψ
  set B := matrixBilinearForm A
  have hB : ∀ η ξ : EuclideanSpace ℝ ι, ‖B η ξ‖ ≤ ‖B‖ * ‖η‖ * ‖ξ‖ := fun η ξ => B.le_opNorm₂ η ξ
  have h1 : MemLp (fun x => ψ x * f x) 2 (mu.restrict Omega) :=
    (Lp.memLp f).of_le_mul (c := M)
      (hψ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hψM x) (norm_nonneg _))
  have h2 : MemLp (fun x => B (W1p.gradient u x) (∇ ψ x)) 2 (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient u)).of_le_mul (c := ‖B‖ * M)
      (B.aestronglyMeasurable_comp₂ (Lp.aestronglyMeasurable _) hgψ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => (hB _ _).trans (by
        rw [mul_right_comm]
        gcongr
        exact hgradM x))
  have h3 : MemLp (fun x => B (∇ ψ x) (W1p.gradient u x)) 2 (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient u)).of_le_mul (c := ‖B‖ * M)
      (B.aestronglyMeasurable_comp₂ hgψ.aestronglyMeasurable (Lp.aestronglyMeasurable _))
      (Filter.Eventually.of_forall fun x => (hB _ _).trans (by gcongr; exact hgradM x))
  have h4 : MemLp (fun x => W1p.value u x * divMatrixGradient A ψ x) 2 (mu.restrict Omega) :=
    (Lp.memLp (W1p.value u)).of_le_mul (c := C)
      ((Lp.aestronglyMeasurable _).mul
        (continuous_divMatrixGradient hψ).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hC ⟨x, rfl⟩) (norm_nonneg _))
  exact ((h1.sub h2).sub h3).sub h4

/-- **The weak equation tested against `ψ φ`.** For a weak solution `u` of `-div(A ∇u) = f` in
`Ω`, a smooth `ψ` compactly supported in `Ω`, and a test function `φ` on the whole space, the
product `ψ φ` is an admissible test function, and its gradient is `ψ ∇φ + φ ∇ψ`. -/
private theorem setIntegral_matrixBilinearForm_smul_add_eq {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 (fun _ => A) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ)) :
    ∫ x in Omega, matrixBilinearForm A (ψ x • ∇ φ x + φ x • ∇ ψ x) (W1p.gradient u x) ∂mu =
      ∫ x in Omega, ψ x * f x * φ x ∂mu := by
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  have hΩ : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ ((⊤ : Opens (EuclideanSpace ℝ ι)) :
      Set (EuclideanSpace ℝ ι)) := SetLike.coe_subset_coe.mpr le_top
  -- `φ` as an element of `H¹(Ω)`, and the test function `ψ φ ∈ H¹₀(Ω)`.
  set φΩ := W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ 2 φ)
  have hφv : ∀ᵐ x ∂mu.restrict Omega, W1p.value φΩ x = φ x := by
    filter_upwards [W1p.value_restrictL_ae le_top (W1p.ofTestFunctionₗ mu ⊤ 2 φ),
      ae_restrict_of_ae_restrict_of_subset hΩ (testFunctionLp_apply_ae (mu := mu) 2 φ)]
      with x h1 h2
    rw [h1, W1p.value_ofTestFunctionₗ, h2]
  have hφg : ∀ᵐ x ∂mu.restrict Omega, W1p.gradient φΩ x = ∇ φ x := by
    filter_upwards [W1p.gradient_restrictL_ae le_top (W1p.ofTestFunctionₗ mu ⊤ 2 φ),
      ae_restrict_of_ae_restrict_of_subset hΩ (gradientTestFunctionLp_apply_ae (mu := mu) 2 φ)]
      with x h1 h2
    rw [h1, W1p.gradient_ofTestFunctionₗ, h2]
  set v := W1p.contDiffSMul ψ hψ hM hψM' hgradM' φΩ
  have hv : v ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hψ hM hψM' hgradM'
      hψc hts φΩ
  have h := hu ⟨v, hv⟩
  simp only at h
  rw [energyFormH1_const_eq_setIntegral] at h
  calc _ = ∫ x in Omega, matrixBilinearForm A (W1p.gradient v x) (W1p.gradient u x) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' φΩ, hφv, hφg]
          with x h1 h2 h3
        rw [h1, h2, h3]
    _ = ∫ x in Omega, f x * W1p.value v x ∂mu := h
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' φΩ, hφv] with x h1 h2
        rw [h1, h2, smul_eq_mul]
        ring

/-- **The localized weak equation, tested against a whole-space test function.** If `u` is a
weak solution of `-div(A ∇u) = f` in `Ω` and `ψ` is a smooth cutoff compactly supported in `Ω`,
then `ψ u`, whose weak gradient is `ψ ∇u + u ∇ψ`, satisfies the weak form of
`-div(A ∇(ψ u)) = localizedForcing A ψ f u` against every test function `φ` on the whole space. -/
private theorem setIntegral_matrixBilinearForm_cutoff_eq {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 (fun _ => A) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ)) :
    ∫ x in Omega, matrixBilinearForm A (∇ φ x)
        (ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) ∂mu
      = ∫ x in Omega, localizedForcing A ψ f u x * φ x ∂mu := by
  -- The weak equation tested against `ψ φ`.
  have hE1 := setIntegral_matrixBilinearForm_smul_add_eq hu hψ hψc hts φ
  -- Integration by parts moves the derivative off `φ` in the term `u ⟨∇φ, A ∇ψ⟩`.
  have hE2 := setIntegral_value_mul_eq_neg (A := A) u hψ hψc hts φ.contDiff
  -- Every weight below is continuous and vanishes off `tsupport ψ`.
  have hψ' := hψ.continuous
  have hφ' := φ.continuous
  have hgψ := ContDiff.continuous_gradient hψ
  have hgφ := continuous_gradient_testFunction φ
  have hD := continuous_divMatrixGradient (A := A) hψ
  have hcs : ∀ K : EuclideanSpace ℝ ι → ℝ, (∀ x, ψ x = 0 → ∇ ψ x = 0 →
      divMatrixGradient A ψ x = 0 → K x = 0) → HasCompactSupport K := fun K hK =>
    hψc.mono' fun x hx => by_contra fun hxψ => hx (hK x (image_eq_zero_of_notMem_tsupport hxψ)
      (gradient_of_notMem_tsupport hxψ)
      (divMatrixGradient_eq_zero_of_notMem_tsupport hψ hxψ))
  have hu_m := Lp.aestronglyMeasurable (W1p.value u)
  have hgu_m := Lp.aestronglyMeasurable (W1p.gradient u)
  -- An `L²(Ω)` function times a continuous compactly supported weight is integrable on `Ω`.
  have hint : ∀ {F K g : EuclideanSpace ℝ ι → ℝ}, MemLp F 2 (mu.restrict Omega) → Continuous K →
      HasCompactSupport K → AEStronglyMeasurable g (mu.restrict Omega) →
      (∀ x, ‖g x‖ ≤ K x * F x) → Integrable g (mu.restrict Omega) :=
    fun hF hK hKc hg hle => ((hK.memLp_of_hasCompactSupport hKc (p := 2)).integrable_mul
      hF).mono' hg (Filter.Eventually.of_forall hle)
  have hT1 : Integrable (fun x => matrixBilinearForm A (ψ x • ∇ φ x + φ x • ∇ ψ x)
      (W1p.gradient u x)) (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (K := fun x => ‖matrixBilinearForm A‖ * ‖ψ x • ∇ φ x + φ x • ∇ ψ x‖) (by fun_prop)
      (hcs _ fun x h1 h2 _ => by simp [h1, h2])
      ((matrixBilinearForm A).aestronglyMeasurable_comp₂
        (Continuous.aestronglyMeasurable (by fun_prop)) hgu_m)
      (fun x => (matrixBilinearForm A).le_opNorm₂ _ _)
  have hT2 : Integrable (fun x => φ x * matrixBilinearForm A (∇ ψ x) (W1p.gradient u x))
      (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (K := fun x => ‖φ x‖ * (‖matrixBilinearForm A‖ * ‖∇ ψ x‖)) (by fun_prop)
      (hcs _ fun x _ h2 _ => by simp [h2])
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        ((matrixBilinearForm A).aestronglyMeasurable_comp₂
          (Continuous.aestronglyMeasurable (by fun_prop)) hgu_m))
      (fun x => by
        rw [norm_mul, mul_assoc]
        gcongr
        exact (matrixBilinearForm A).le_opNorm₂ _ _)
  have hQ : Integrable (fun x => φ x * matrixBilinearForm A (W1p.gradient u x) (∇ ψ x))
      (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (K := fun x => ‖φ x‖ * (‖matrixBilinearForm A‖ * ‖∇ ψ x‖)) (by fun_prop)
      (hcs _ fun x _ h2 _ => by simp [h2])
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        ((matrixBilinearForm A).aestronglyMeasurable_comp₂ hgu_m
          (Continuous.aestronglyMeasurable (by fun_prop))))
      (fun x => by
        rw [norm_mul, mul_assoc]
        gcongr
        exact ((matrixBilinearForm A).le_opNorm₂ _ _).trans_eq (by ring))
  have hT3 : Integrable (fun x => W1p.value u x * (matrixBilinearForm A (∇ φ x) (∇ ψ x)
      + φ x * divMatrixGradient A ψ x)) (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.value u)).norm
      (K := fun x => ‖matrixBilinearForm A (∇ φ x) (∇ ψ x) + φ x * divMatrixGradient A ψ x‖)
      (by fun_prop) (hcs _ fun x _ h2 h3 => by simp [h2, h3])
      (hu_m.mul (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun x => by rw [norm_mul, mul_comm])
  have hT4 : Integrable (fun x => W1p.value u x * (φ x * divMatrixGradient A ψ x))
      (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.value u)).norm
      (K := fun x => ‖φ x * divMatrixGradient A ψ x‖)
      (by fun_prop) (hcs _ fun x _ _ h3 => by simp [h3])
      (hu_m.mul (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun x => by rw [norm_mul, mul_comm])
  have hP : Integrable (fun x => ψ x * f x * φ x) (mu.restrict Omega) :=
    hint (Lp.memLp f).norm (K := fun x => ‖ψ x * φ x‖)
      (by fun_prop) (hcs _ fun x h1 _ _ => by simp [h1])
      (((Continuous.aestronglyMeasurable (by fun_prop)).mul (Lp.aestronglyMeasurable f)).mul
        (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun x => by
        simp only [norm_mul]
        exact le_of_eq (by ring))
  -- Assemble: both sides are the same combination of the six integrals above.
  calc ∫ x in Omega, matrixBilinearForm A (∇ φ x)
        (ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) ∂mu
      = ∫ x in Omega, (matrixBilinearForm A (ψ x • ∇ φ x + φ x • ∇ ψ x) (W1p.gradient u x)
          - φ x * matrixBilinearForm A (∇ ψ x) (W1p.gradient u x)
          + W1p.value u x * (matrixBilinearForm A (∇ φ x) (∇ ψ x)
            + φ x * divMatrixGradient A ψ x)
          - W1p.value u x * (φ x * divMatrixGradient A ψ x)) ∂mu := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
        ring
    _ = (∫ x in Omega, ψ x * f x * φ x ∂mu)
          - ∫ x in Omega, φ x * matrixBilinearForm A (W1p.gradient u x) (∇ ψ x) ∂mu
          - ∫ x in Omega, φ x * matrixBilinearForm A (∇ ψ x) (W1p.gradient u x) ∂mu
          - ∫ x in Omega, W1p.value u x * (φ x * divMatrixGradient A ψ x) ∂mu := by
        rw [integral_sub ?_ hT4, integral_add ?_ hT3, integral_sub hT1 hT2, hE1, hE2]
        · ring
        · exact hT1.sub hT2
        · exact (hT1.sub hT2).add hT3
    _ = ∫ x in Omega, (ψ x * f x * φ x
          - φ x * matrixBilinearForm A (W1p.gradient u x) (∇ ψ x)
          - φ x * matrixBilinearForm A (∇ ψ x) (W1p.gradient u x)
          - W1p.value u x * (φ x * divMatrixGradient A ψ x)) ∂mu := by
        rw [integral_sub ?_ hT4, integral_sub ?_ hT2, integral_sub hP hQ]
        · exact hP.sub hQ
        · exact (hP.sub hQ).sub hT2
    _ = ∫ x in Omega, localizedForcing A ψ f u x * φ x ∂mu := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [localizedForcing]
        ring

/-- The whole-space weak equation for the extended cutoff product, against a test function. -/
private theorem energyFormH1_ofTestFunctionₗ_eq_of_ae_eq_indicator
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 (fun _ => A) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {w : W1p mu ⊤ 2}
    (hwg : ∀ᵐ x ∂mu, W1p.gradient w x = (Omega : Set (EuclideanSpace ℝ ι)).indicator
      (fun y => ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y) x)
    {g : EuclideanSpace ℝ ι → ℝ}
    (hg : ∀ᵐ x ∂mu, g x = (Omega : Set (EuclideanSpace ℝ ι)).indicator
      (localizedForcing A ψ f u) x)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ)) :
    energyFormH1 (fun _ => A) 0 0 w (W1p.ofTestFunctionₗ mu ⊤ 2 φ) =
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), g x * φ x ∂mu := by
  have hΩ := Omega.isOpen.measurableSet
  have htop : mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) = mu := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hint_top : ∀ F : EuclideanSpace ℝ ι → ℝ,
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), F x ∂mu =
        ∫ x, F x ∂mu := fun F => by rw [htop]
  have hφg := (gradientTestFunctionLp_apply_ae (mu := mu) 2 φ).filter_mono (ae_mono htop.ge)
  rw [energyFormH1_const_eq_setIntegral, hint_top, hint_top]
  calc ∫ x, matrixBilinearForm A (W1p.gradient (W1p.ofTestFunctionₗ mu ⊤ 2 φ) x)
          (W1p.gradient w x) ∂mu
      = ∫ x, (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => matrixBilinearForm A
          (∇ φ y) (ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y)) x ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [hφg, hwg] with x h1 h2
        rw [W1p.gradient_ofTestFunctionₗ, h1, h2]
        by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
        · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ]
        · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ, map_zero]
    _ = ∫ x in Omega, localizedForcing A ψ f u x * φ x ∂mu := by
        rw [integral_indicator hΩ]
        exact setIntegral_matrixBilinearForm_cutoff_eq hu hψ hψc hts φ
    _ = ∫ x, g x * φ x ∂mu := by
        rw [← integral_indicator hΩ]
        refine integral_congr_ae ?_
        filter_upwards [hg] with x h
        rw [h]
        by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
        · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ]
        · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ, zero_mul]

/-- **A cutoff of a weak solution solves an equation on the whole space.** Let `u ∈ H¹(Ω)` be a
weak solution of `-div(A ∇u) = f` in `Ω` for a constant matrix `A`, with `f ∈ L²(Ω)` and no
boundary condition, and let `ψ` be smooth and compactly supported in `Ω`. Then `ψ u`, extended by
zero, is a weak solution of `-div(A ∇w) = g` on the whole space for some `g ∈ L²(ℝⁿ)`, namely

`g = ψ f - ⟨∇u, A ∇ψ⟩ - ⟨∇ψ, A ∇u⟩ - u div(A ∇ψ)`, extended by zero.

No ellipticity and no regularity of `∂Ω` is needed. -/
theorem exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 (fun _ => A) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {M : ℝ} (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Omega, |ψ x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M)
    (hw : W1p.contDiffSMul ψ hψ hM hψM hgradM u ∈ w1p0Submodule mu Omega 2) :
    ∃ g : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      IsWeakSolutionDirichlet (fun _ => A) 0 0 g (W1p0.extendByZeroL le_top ⟨_, hw⟩) := by
  have hΩ := Omega.isOpen.measurableSet
  have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ⊆
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) :=
    SetLike.coe_subset_coe.mpr le_top
  -- The forcing term, extended by zero.
  have hG := memLp_localizedForcing (A := A) hψ hψc f u
  have hg : ∀ᵐ x ∂mu, extendByZeroLpₗᵢ ℝ mu hΩ hsub (hG.toLp (localizedForcing A ψ f u)) x =
      (Omega : Set (EuclideanSpace ℝ ι)).indicator (localizedForcing A ψ f u) x := by
    have h2 := (coeFn_extendByZeroLpₗᵢ ℝ (μ := mu) hΩ hsub
      (hG.toLp (localizedForcing A ψ f u))).filter_mono
        (ae_mono (by rw [Opens.coe_top, Measure.restrict_univ]))
    have h3 := (ae_restrict_iff' hΩ).1 hG.coeFn_toLp
    filter_upwards [h2, h3] with x hx2 hx3
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [hx2, indicator_of_mem hxΩ, indicator_of_mem hxΩ, hx3 hxΩ]
    · rw [hx2, indicator_of_notMem hxΩ, indicator_of_notMem hxΩ]
  -- The energy form is continuous, so testing against test functions suffices.
  have hcoeff : MemLp (fun x => energyIntegrand ((fun _ => A) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) := by
    simpa using memLp_top_const (α := EuclideanSpace ℝ ι)
      (μ := mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
      (energyIntegrand A 0 0)
  exact ⟨_, (isWeakSolutionDirichlet_iff_forall_testFunction hcoeff _ _).2 fun φ =>
    energyFormH1_ofTestFunctionₗ_eq_of_ae_eq_indicator hu hψ hψc hts
      (W1p.gradient_extendByZeroL_contDiffSMul_ae hψ hM hψM hgradM u hw) hg φ⟩

/-- **Localizing a weak solution to the whole space.** Let `u ∈ H¹(Ω)` be a weak solution of
`-div(A ∇u) = f` in `Ω` for a constant matrix `A`, with `f ∈ L²(Ω)` and no boundary condition.
Near any compact `S ⊆ Ω`, `u` agrees, in value and in gradient, with a weak solution
`w ∈ H¹(ℝⁿ)` of an equation `-div(A ∇w) = g` on the whole space, with `g ∈ L²(ℝⁿ)`.

One may take for `w` the product of `u` with a smooth cutoff equal to one near `S` and compactly
supported in `Ω`, extended by zero
(`TauCeti.PDE.exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul`). This is the device
that reduces interior regularity to regularity on the whole space. -/
theorem exists_isWeakSolutionDirichlet_top_ae_eq_on_of_isCompact
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 (fun _ => A) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {S : Set (EuclideanSpace ℝ ι)} (hS : IsCompact S)
    (hSΩ : S ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∃ w : W1p0 mu ⊤ 2, ∃ g : Lp ℝ 2
        (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      IsWeakSolutionDirichlet (fun _ => A) 0 0 g w ∧
        (∀ᵐ x ∂mu, x ∈ S → W1p.value (w : W1p mu ⊤ 2) x = W1p.value u x) ∧
        ∀ᵐ x ∂mu, x ∈ S → W1p.gradient (w : W1p mu ⊤ 2) x = W1p.gradient u x := by
  -- A smooth cutoff, equal to one near `S` and compactly supported in `Ω`.
  obtain ⟨ψ, M, hψ, -, hψ_one, hψc, hts, hM, hψM, hgradM⟩ :=
    hS.exists_contDiff_cutoff_with_bounds Omega.isOpen hSΩ
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  have hψ_S : ∀ x ∈ S, ψ x = 1 ∧ ∇ ψ x = 0 := fun x hx => by
    have hev : ψ =ᶠ[nhds x] fun _ => (1 : ℝ) := mem_interior_iff_mem_nhds.1 (hψ_one hx)
    exact ⟨hev.eq_of_nhds, hev.gradient_eq.trans (gradient_fun_const x 1)⟩
  have hw := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (p := 2) (by norm_num) hψ
    hM hψM' hgradM' hψc hts u
  obtain ⟨g, hg⟩ :=
    exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul hu hψ hψc hts hM hψM' hgradM' hw
  refine ⟨_, g, hg, ?_, ?_⟩
  · filter_upwards [W1p.value_extendByZeroL_contDiffSMul_ae hψ hM hψM' hgradM' u hw]
      with x hx hxS
    rw [hx, indicator_of_mem (hSΩ hxS), (hψ_S x hxS).1, one_mul]
  · filter_upwards [W1p.gradient_extendByZeroL_contDiffSMul_ae hψ hM hψM' hgradM' u hw]
      with x hx hxS
    rw [hx, indicator_of_mem (hSΩ hxS), (hψ_S x hxS).1, (hψ_S x hxS).2, one_smul, smul_zero,
      add_zero]

/-- **Interior `H²` regularity for constant coefficients.** Let `A` be a constant, uniformly
elliptic coefficient matrix, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ⱼ(Aⁱʲ ∂ᵢu) = f` in `Ω`, with `f ∈ L²(Ω)`,

in the sense that `∫_Ω ⟨A ∇u, ∇v⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with no boundary condition
on `u`. Then `u ∈ H²_loc(Ω)`: on every open `V` whose closure is compact and contained in `Ω`,
the restriction of `u` is the first-order part of an element of `W^{2,2}(V)`.

No regularity of `∂Ω` is assumed. The proof localizes `u` by a cutoff
(`TauCeti.PDE.exists_isWeakSolutionDirichlet_top_ae_eq_on_of_isCompact`) and applies the
whole-space theorem `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_restrictL {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 (fun _ => A) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ U : Wkp mu V 2 2, Wkp.lowerOrder 1 U =
      W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)) u := by
  obtain ⟨w, g, hw, -, hgrad⟩ := exists_isWeakSolutionDirichlet_top_ae_eq_on_of_isCompact hu hV hVΩ
  have htop : mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) = mu := by
    rw [Opens.coe_top, Measure.restrict_univ]
  -- On `V`, the gradient of the localized solution is that of `u`.
  have hgradV : ∀ᵐ x ∂mu.restrict V, W1p.gradient (w : W1p mu ⊤ 2) x =
      W1p.gradient (W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)) u) x := by
    filter_upwards [W1p.gradient_restrictL_ae (SetLike.coe_subset_coe.mp
        (subset_closure.trans hVΩ)) u,
      (ae_restrict_iff' V.isOpen.measurableSet).2
        (hgrad.mono fun x hx hxV => hx (subset_closure hxV))] with x h1 h2
    rw [h1, h2]
  refine W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn _ (EuclideanSpace.basisFun ι ℝ)
    fun i j => ?_
  obtain ⟨G, -, hG⟩ := UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient hlam hA hw
    (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i)
  have hmem : MemLp G 2 (mu.restrict V) :=
    (Lp.memLp G).mono_measure (by rw [htop]; exact Measure.restrict_le_self)
  refine ⟨hmem.toLp G, ((hG.mono le_top).congr_ae ?_).congr_ae_deriv hmem.coeFn_toLp.symm⟩
  filter_upwards [hgradV] with x hx
  rw [hx]

end PDE

end TauCeti
