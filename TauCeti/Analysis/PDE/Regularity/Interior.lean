/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Basic
public import TauCeti.Analysis.PDE.EnergyForm.Restriction
public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import TauCeti.Analysis.Sobolev.W1p.IntegrationByParts
public import TauCeti.Analysis.PDE.Ellipticity.Extension

/-!
# Interior `H²` regularity for Lipschitz principal coefficients

Let `a` be a coefficient field that is uniformly elliptic on `Ω` and whose bilinear forms
`x ↦ a(x)` are locally Lipschitz on `Ω`, and let `u ∈ H¹(Ω)` be a weak solution of the
divergence-form equation

`-div(a ∇u) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)` and `b, c ∈ L∞(Ω)`,

meaning `∫_Ω (⟨∇v, a ∇u⟩ + ⟨b, ∇u⟩ v + c u v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`.
No boundary condition is imposed on `u` and nothing is assumed about `∂Ω`. This file proves that
`u ∈ H²_loc(Ω)`: on every open `V` whose closure is compact and contained in `Ω`, the restriction
of `u` is the first-order part of an element of `W^{2,2}(V)`. A constant coefficient matrix is the
case of a field with Lipschitz constant zero.

## Localization

The lower-order terms belong to `L²`, so moving them to the right-hand side gives
`-div(a ∇u) = g` with `g = f - ⟨b, ∇u⟩ - c u ∈ L²(Ω)`. No sign or smallness condition on `b`
or `c` is needed. The whole-space theorem
`TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith`
does the analytic work; what is proved here is that a cutoff of a local solution is a global one.
For `ψ` smooth and compactly supported in `Ω`, the product `ψ u`, extended by zero, lies in
`H¹(ℝⁿ)` and solves

`-div(a ∇(ψ u)) = ψ g - ⟨∇u, a ∇ψ⟩ - ⟨∇ψ, a ∇u⟩ - u div(a ∇ψ)` on `ℝⁿ`,

whose right-hand side is again in `L²`, because every term carrying `u` or `∇u` also carries a
bounded, compactly supported factor built from `a` and `ψ`. For a Lipschitz field the conormal
components `⟨eᵢ, a ∇ψ⟩` of the cutoff are only Lipschitz
(`TauCeti.PDE.exists_lipschitzWith_matrixBilinearForm_gradient`), and `div(a ∇ψ)`
(`TauCeti.PDE.divMatrixGradient`) is the sum of their directional derivatives, which exist almost
everywhere and are bounded. The identity is checked against test functions `φ` on `ℝⁿ`, which
suffices by density (`TauCeti.PDE.isWeakSolutionDirichlet_iff_forall_testFunction`). The term
`ψ ∇u` is handled by testing the equation for `u` against `ψ φ ∈ H¹₀(Ω)`, and the term `u ∇ψ` by
integrating by parts against the Lipschitz functions `φ ⟨eᵢ, a ∇ψ⟩`
(`TauCeti.W1p.setIntegral_lineDeriv_mul_value_eq_neg`). Choosing `ψ = 1` near `closure V` makes
`ψ u` agree with `u` on `V`.

## Extending the coefficients

The whole-space theorem needs a coefficient field that is uniformly elliptic and Lipschitz on all
of `ℝⁿ`. For a cutoff `χ` equal to one near `closure V` and supported in `Ω`, the field
`χ a + (1 - χ) λ I` is such a field, with the same ellipticity constants, and it agrees with `a`
where `χ = 1` (`TauCeti.PDE.UniformlyEllipticOn.exists_lipschitzWith_eqOn`). On that set the
restriction of `u` solves the equation with the extended field.

## Main declarations

* `TauCeti.PDE.divMatrixGradient` and `TauCeti.PDE.localizedForcing`: the divergence of the
  conormal cutoff field and the forcing term in the localized equation.
* `TauCeti.PDE.exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul`: a cutoff of a weak
  solution, extended by zero, is a weak solution on the whole space with an explicit `L²` forcing
  term.
* `TauCeti.PDE.exists_isWeakSolutionDirichlet_top_ae_eq_on_of_isCompact`: near a compact subset
  of `Ω`, a weak solution and its forcing agree with a whole-space weak solution and its forcing.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`:
  interior `H²` regularity for locally Lipschitz principal coefficients.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL`: its case of a constant
  principal coefficient.
* `TauCeti.PDE.divMatrixGradient_eq_sum_fderiv_fderiv_apply`: the classical Hessian contraction.
* `ContDiffOn.integral_matrixBilinearForm_gradient_eq_neg_integral_divMatrixGradient`:
  integration by parts against the conormal gradient of a `C²` function.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1, Theorem 1 (interior `H²` regularity, for
  `C¹` coefficients).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.8 (for Lipschitz coefficients).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Set TopologicalSpace Filter
open scoped ContDiff Distributions ENNReal NNReal Gradient InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {K : ℝ≥0} {M : ℝ}

/-! ### The divergence of the conormal field of a cutoff -/

/-- The divergence `div(a ∇ψ) = ∑ᵢ ∂ᵢ ⟨eᵢ, a ∇ψ⟩` of the conormal field of `ψ`, computed in the
standard basis. It is the zeroth-order coefficient that commuting the operator `-div(a ∇ ·)` past
a cutoff `ψ` produces. For a Lipschitz field `a` and a smooth compactly supported `ψ`, the
directional derivatives exist almost everywhere and are bounded. -/
def divMatrixGradient (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (ψ : EuclideanSpace ℝ ι → ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, lineDeriv ℝ (fun y => matrixBilinearForm (a y) (EuclideanSpace.basisFun ι ℝ i) (∇ ψ y)) x
    (EuclideanSpace.basisFun ι ℝ i)

/-- The defining formula for `divMatrixGradient`: the sum of the directional derivatives of the
conormal components in the standard basis. -/
theorem divMatrixGradient_def (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (ψ : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    divMatrixGradient a ψ x =
      ∑ i, lineDeriv ℝ (fun y => matrixBilinearForm (a y) (EuclideanSpace.basisFun ι ℝ i)
        (∇ ψ y)) x (EuclideanSpace.basisFun ι ℝ i) := by
  rw [divMatrixGradient]

/-- `div(a ∇ψ)` vanishes off the support of `ψ`. -/
@[simp] theorem divMatrixGradient_eq_zero_of_notMem_tsupport {ψ : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} (hx : x ∉ tsupport ψ) :
    divMatrixGradient a ψ x = 0 :=
  Finset.sum_eq_zero fun _ _ =>
    lineDeriv_of_notMem_tsupport (fun h => hx (tsupport_matrixBilinearForm_gradient_subset ψ _ h))
      _

/-- For a bounded Lipschitz field `a` and a smooth compactly supported `ψ`, every conormal
component `y ↦ ⟨η, a(y) ∇ψ(y)⟩` is Lipschitz. -/
theorem exists_lipschitzWith_matrixBilinearForm_gradient
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (η : EuclideanSpace ℝ ι) :
    ∃ L : ℝ≥0, LipschitzWith L fun y => matrixBilinearForm (a y) η (∇ ψ y) := by
  have hgc : HasCompactSupport (∇ ψ) :=
    hψc.mono' fun x hx => by_contra fun h => hx (gradient_of_notMem_tsupport h)
  obtain ⟨Lg, hLg⟩ := (hψ.gradient_right (m := ∞) (by simp)).lipschitzWith_of_hasCompactSupport
    hgc (by simp)
  obtain ⟨N, -, -, hN⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  have h := ContinuousLinearMap.holderWith_comp₂ (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ ι →L[ℝ] ℝ) η)
    (holderWith_one.2 hK) (holderWith_one.2 hLg) (Mf := M.toNNReal) (Mg := N.toNNReal)
    (fun x => (hM x).trans (Real.le_coe_toNNReal _))
    (fun x => (hN x).trans (Real.le_coe_toNNReal _))
  exact ⟨_, by simpa only [ContinuousLinearMap.apply_apply] using holderWith_one.1 h⟩

section ClassicalOperator

variable {A : Matrix ι ι ℝ} {g : EuclideanSpace ℝ ι → ℝ}

/-- For a `C²` function, the divergence of its constant-matrix conormal gradient is the
contraction of the matrix against the classical Hessian. -/
theorem divMatrixGradient_eq_sum_fderiv_fderiv_apply
    (hg : ContDiffOn ℝ 2 g Omega) {x : EuclideanSpace ℝ ι} (hx : x ∈ Omega) :
    divMatrixGradient (fun _ => A) g x = ∑ j, ∑ i, A j i *
      fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.basisFun ι ℝ i)) x
        (EuclideanSpace.basisFun ι ℝ j) := by
  classical
  let b := EuclideanSpace.basisFun ι ℝ
  have hgder : ContDiffOn ℝ 1 (fderiv ℝ g) Omega :=
    hg.fderiv_of_isOpen Omega.isOpen (by norm_num)
  have hd : ∀ i, DifferentiableAt ℝ (fun y => fderiv ℝ g y (b i)) x := fun i =>
    ((hgder.clm_apply contDiffOn_const).differentiableOn one_ne_zero).differentiableAt
      (Omega.isOpen.mem_nhds hx)
  have hcoord : ∀ i y, (∇ g y) i = fderiv ℝ g y (b i) := fun i y => by
    rw [← EuclideanSpace.inner_basisFun_real, inner_gradient_left]
  have hflux : ∀ j, (fun y => matrixBilinearForm A (b j) (∇ g y)) =
      fun y => ∑ i, A j i * fderiv ℝ g y (b i) := fun j => by
    funext y
    simp [matrixBilinearForm_apply, b, EuclideanSpace.basisFun_apply, Matrix.mulVec,
      dotProduct, hcoord]
  rw [divMatrixGradient]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hflux, ((DifferentiableAt.fun_sum fun i _ => (hd i).const_mul _)).lineDeriv_eq_fderiv,
    fderiv_fun_sum fun i _ => (hd i).const_mul _]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_const_mul (hd i)]
  rfl

/-- The constant-coefficient operator applied to a `C²` function is continuous inside the
domain. -/
theorem continuousOn_divMatrixGradient (hg : ContDiffOn ℝ 2 g Omega) :
    ContinuousOn (divMatrixGradient (fun _ => A) g) Omega := by
  have hgrad : ContDiffOn ℝ 1 (∇ g) Omega :=
    (toDual ℝ (EuclideanSpace ℝ ι)).symm.contDiff.comp_contDiffOn
      (hg.fderiv_of_isOpen Omega.isOpen (by norm_num))
  unfold divMatrixGradient
  refine continuousOn_finsetSum _ fun i _ => ?_
  have hi : ContDiffOn ℝ 1
      (fun y => matrixBilinearForm A (EuclideanSpace.basisFun ι ℝ i) (∇ g y)) Omega :=
    (matrixBilinearForm A _).contDiff.comp_contDiffOn hgrad
  exact ((hi.continuousOn_fderiv_of_isOpen Omega.isOpen le_rfl).clm_apply
    (continuousOn_const (c := EuclideanSpace.basisFun ι ℝ i))).congr fun x hx =>
      ((hi.differentiableOn one_ne_zero).differentiableAt
        (Omega.isOpen.mem_nhds hx)).lineDeriv_eq_fderiv

/-- `div(A ∇ψ)` is continuous for smooth `ψ`. -/
theorem continuous_divMatrixGradient {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : Continuous (divMatrixGradient (fun _ => A) ψ) := by
  simpa only [Opens.coe_top, continuousOn_univ] using
    continuousOn_divMatrixGradient (A := A) (Omega := ⊤) (hψ.of_le (by simp)).contDiffOn

/-- Integration by parts for the constant-matrix conormal gradient of a `C²` function.
The test function is compactly supported in the open domain, so no boundary term occurs. -/
theorem _root_.ContDiffOn.integral_matrixBilinearForm_gradient_eq_neg_integral_divMatrixGradient
    {g : EuclideanSpace ℝ ι → ℝ} (hg : ContDiffOn ℝ 2 g Omega) (φ : 𝓓(Omega, ℝ)) :
    ∫ x, matrixBilinearForm A (∇ (φ : EuclideanSpace ℝ ι → ℝ) x) (∇ g x) ∂mu =
      -∫ x, φ x * divMatrixGradient (fun _ => A) g x ∂mu := by
  let b := EuclideanSpace.basisFun ι ℝ
  let q : ι → EuclideanSpace ℝ ι → ℝ := fun i y => matrixBilinearForm A (b i) (∇ g y)
  have hg1 : ContDiffOn ℝ 1 (∇ g) Omega :=
    (toDual ℝ (EuclideanSpace ℝ ι)).symm.contDiff.comp_contDiffOn
      (hg.fderiv_of_isOpen Omega.isOpen (by norm_num))
  have hq : ∀ i, ContDiffOn ℝ 1 (q i) Omega := fun i =>
    (matrixBilinearForm A (b i)).contDiff.comp_contDiffOn hg1
  have hqd : ∀ i, LocallyIntegrableOn (fun x => lineDeriv ℝ (q i) x (b i)) Omega mu :=
    fun i => (((hq i).continuousOn_fderiv_of_isOpen Omega.isOpen le_rfl).clm_apply
      continuousOn_const).congr (fun x hx =>
        ((hq i).differentiableOn one_ne_zero |>.differentiableAt
          (Omega.isOpen.mem_nhds hx)).lineDeriv_eq_fderiv)
      |>.locallyIntegrableOn Omega.isOpen.measurableSet
  have hqweak : ∀ i, HasWeakLineDerivOn mu Omega (q i)
      (fun x => lineDeriv ℝ (q i) x (b i)) (b i) := fun i =>
    hasWeakLineDerivOn_of_hasLineDerivAt
      ((hq i).continuousOn.locallyIntegrableOn Omega.isOpen.measurableSet) (hqd i)
      (fun x hx => ((hq i).differentiableOn one_ne_zero |>.differentiableAt
        (Omega.isOpen.mem_nhds hx)).lineDifferentiableAt.hasLineDerivAt)
  -- Expand the test gradient in the standard basis and integrate each conormal component.
  calc
    ∫ x, matrixBilinearForm A (∇ (φ : EuclideanSpace ℝ ι → ℝ) x) (∇ g x) ∂mu
      = ∑ i, ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (b i) * q i x ∂mu := by
      have hint : ∀ i, Integrable
          (fun x => lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (b i) * q i x) mu := fun i => by
        simpa only [smul_eq_mul] using
          integrable_lineDeriv_smul_of_locallyIntegrableOn (hqweak i).locallyIntegrableOn φ (b i)
      rw [← integral_finsetSum _ (fun i _ => hint i)]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      have hφd : ∀ v, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x v =
          fderiv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x v := fun v =>
        (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv
      simpa only [hφd, ← inner_gradient_left] using
        (sum_inner_mul_matrixBilinearForm (A := A) (∇ (φ : EuclideanSpace ℝ ι → ℝ) x) (∇ g x)).symm
    _ = -∫ x, φ x * divMatrixGradient (fun _ => A) g x ∂mu := by
      simp_rw [← smul_eq_mul, (hqweak _).integral_lineDeriv_smul_eq_neg_integral_smul φ]
      rw [Finset.sum_neg_distrib, ← integral_finsetSum _
        (fun i _ => integrable_smul_of_locallyIntegrableOn (hqd i) φ)]
      simp only [Finset.mul_sum, divMatrixGradient, b, q, smul_eq_mul]

end ClassicalOperator

/-- `div(a ∇ψ)` is bounded, for a bounded Lipschitz field `a` and a smooth compactly supported
`ψ`. -/
theorem exists_norm_divMatrixGradient_le (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∃ C, ∀ x, ‖divMatrixGradient a ψ x‖ ≤ C := by
  choose L hL using fun i => exists_lipschitzWith_matrixBilinearForm_gradient hM hK hψ hψc
    (EuclideanSpace.basisFun ι ℝ i)
  refine ⟨∑ i, (L i : ℝ) * ‖EuclideanSpace.basisFun ι ℝ i‖, fun x => ?_⟩
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ => norm_lineDeriv_le_of_lipschitz ℝ (hL i))

/-- `div(a ∇ψ)` is measurable, for a continuous field `a` and a smooth `ψ`. -/
theorem measurable_divMatrixGradient (ha : Continuous fun x => matrixBilinearForm (a x))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Measurable (divMatrixGradient a ψ) :=
  Finset.measurable_sum _ fun _ _ => measurable_lineDeriv
    ((ha.clm_apply continuous_const).clm_apply (ContDiff.continuous_gradient hψ))

/-- **Integration by parts against the conormal field of a cutoff.** For `u ∈ H¹(Ω)`, a test
function `φ` on the whole space, and a smooth `ψ` compactly supported in `Ω`,

`∫_Ω u (⟨∇φ, a ∇ψ⟩ + φ div(a ∇ψ)) = -∫_Ω φ ⟨∇u, a ∇ψ⟩`,

the integration by parts of `u` against the Lipschitz components of `φ a ∇ψ`. -/
private theorem setIntegral_value_mul_eq_neg (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) (u : W1p mu Omega 2)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ)) :
    ∫ x in Omega, W1p.value u x * (matrixBilinearForm (a x) (∇ φ x) (∇ ψ x)
        + φ x * divMatrixGradient a ψ x) ∂mu
      = -∫ x in Omega, φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x) ∂mu := by
  set b := EuclideanSpace.basisFun ι ℝ
  set h : ι → EuclideanSpace ℝ ι → ℝ := fun i y => matrixBilinearForm (a y) (b i) (∇ ψ y)
  choose Lh hLh using fun i => exists_lipschitzWith_matrixBilinearForm_gradient hM hK hψ hψc (b i)
  have hhc : ∀ i, HasCompactSupport (h i) := fun i =>
    hψc.mono' ((subset_tsupport _).trans (tsupport_matrixBilinearForm_gradient_subset ψ (b i)))
  choose Ch hCh using fun i => (hLh i).continuous.bounded_above_of_compact_support (hhc i)
  obtain ⟨Lφ, hLφ⟩ := φ.contDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport (by simp)
  obtain ⟨Cφ, hCφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  -- Each `gᵢ = φ hᵢ` is Lipschitz with compact support in `Ω`.
  set g : ι → EuclideanSpace ℝ ι → ℝ := fun i y => φ y * h i y
  have hLg : ∀ i, LipschitzWith _ (g i) := fun i =>
    holderWith_one.1 ((ContinuousLinearMap.mul ℝ ℝ).holderWith_comp₂ (holderWith_one.2 hLφ)
      (holderWith_one.2 (hLh i)) (Mf := Cφ.toNNReal) (Mg := (Ch i).toNNReal)
      (fun x => (hCφ x).trans (Real.le_coe_toNNReal _))
      (fun x => (hCh i x).trans (Real.le_coe_toNNReal _)))
  have hsupp : ∀ i, Function.support (g i) ⊆ tsupport ψ := fun i x hx =>
    tsupport_matrixBilinearForm_gradient_subset (a := a) ψ (b i)
      (subset_tsupport _ fun h0 => hx (by simp only [g, h, h0, mul_zero]))
  have hgc : ∀ i, HasCompactSupport (g i) := fun i => hψc.mono' (hsupp i)
  have hgs : ∀ i, tsupport (g i) ⊆ Omega := fun i =>
    (closure_minimal (hsupp i) (isClosed_tsupport ψ)).trans hts
  have key : ∀ i, ∫ x in Omega, lineDeriv ℝ (g i) x (b i) * W1p.value u x ∂mu =
      -∫ x in Omega, g i x * ⟪W1p.gradient u x, b i⟫_ℝ ∂mu := fun i =>
    W1p.setIntegral_lineDeriv_mul_value_eq_neg (by norm_num) u (hLg i) (hgc i) (hgs i) (b i)
  -- The product rule for `φ hᵢ`, in the direction `bᵢ`, at every point where `hᵢ` is
  -- differentiable, hence almost everywhere by Rademacher's theorem.
  have hderiv : ∀ᵐ x ∂mu, ∀ i, lineDeriv ℝ (g i) x (b i)
      = ⟪∇ φ x, b i⟫_ℝ * h i x + φ x * lineDeriv ℝ (h i) x (b i) := by
    refine ae_all_iff.2 fun i => (hLh i).ae_differentiableAt.mono fun x hhx => ?_
    have hφx : DifferentiableAt ℝ φ x := (φ.contDiff.differentiable (by simp)) x
    have hmul : DifferentiableAt ℝ (fun y => φ y * h i y) x := hφx.mul hhx
    rw [hmul.lineDeriv_eq_fderiv, hhx.lineDeriv_eq_fderiv, fderiv_fun_mul hφx hhx,
      inner_gradient_left]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hint1 : ∀ i, Integrable (fun x => lineDeriv ℝ (g i) x (b i) * W1p.value u x)
      (mu.restrict Omega) := fun i => by
    have hdgc : HasCompactSupport fun x => lineDeriv ℝ (g i) x (b i) :=
      (hgc i).mono' fun x hx => by_contra fun hx' => hx (lineDeriv_of_notMem_tsupport hx' _)
    exact ((hdgc.memLp_of_bound (p := 2) (aestronglyMeasurable_lineDeriv (hLg i).continuous mu) _
      (.of_forall fun _ => norm_lineDeriv_le_of_lipschitz ℝ (hLg i))).restrict _).integrable_mul
        (Lp.memLp (W1p.value u))
  have hint2 : ∀ i, Integrable (fun x => g i x * ⟪W1p.gradient u x, b i⟫_ℝ)
      (mu.restrict Omega) := fun i =>
    (((hLg i).continuous.memLp_of_hasCompactSupport (p := 2) (hgc i)).restrict _).integrable_mul
      ((Lp.memLp (W1p.gradient u)).inner_const (b i))
  calc ∫ x in Omega, W1p.value u x * (matrixBilinearForm (a x) (∇ φ x) (∇ ψ x)
        + φ x * divMatrixGradient a ψ x) ∂mu
      = ∫ x in Omega, ∑ i, lineDeriv ℝ (g i) x (b i) * W1p.value u x ∂mu := by
        refine integral_congr_ae ((ae_restrict_of_ae hderiv).mono fun x hx => ?_)
        simp only [hx, divMatrixGradient_def]
        rw [← sum_inner_mul_matrixBilinearForm (A := a x)]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_add, add_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [h]
        ring
    _ = ∑ i, ∫ x in Omega, lineDeriv ℝ (g i) x (b i) * W1p.value u x ∂mu :=
        integral_finsetSum _ fun i _ => hint1 i
    _ = ∑ i, -∫ x in Omega, g i x * ⟪W1p.gradient u x, b i⟫_ℝ ∂mu :=
        Finset.sum_congr rfl fun i _ => key i
    _ = -∫ x in Omega, ∑ i, g i x * ⟪W1p.gradient u x, b i⟫_ℝ ∂mu := by
        rw [integral_finsetSum _ fun i _ => hint2 i, Finset.sum_neg_distrib]
    _ = -∫ x in Omega, φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x) ∂mu := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [← sum_inner_mul_matrixBilinearForm (A := a x), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [g, h]
        ring

/-! ### The localized equation -/

/-- The right-hand side of the equation satisfied by a cutoff `ψ u` of a weak solution `u` of
`-div(a ∇u) = f`:

`-div(a ∇(ψ u)) = ψ f - ⟨∇u, a ∇ψ⟩ - ⟨∇ψ, a ∇u⟩ - u div(a ∇ψ)`. -/
def localizedForcing (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (ψ : EuclideanSpace ℝ ι → ℝ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2) (x : EuclideanSpace ℝ ι) : ℝ :=
  ψ x * f x - matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x)
    - matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x) - W1p.value u x * divMatrixGradient a ψ x

/-- The defining formula for `localizedForcing`. -/
theorem localizedForcing_def (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (ψ : EuclideanSpace ℝ ι → ℝ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2) (x : EuclideanSpace ℝ ι) :
    localizedForcing a ψ f u x =
      ψ x * f x - matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x)
        - matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)
        - W1p.value u x * divMatrixGradient a ψ x := by
  rw [localizedForcing]

/-- The localized forcing term is square integrable, since each of its terms is an `L²(Ω)`
function times a bounded one. -/
theorem memLp_localizedForcing (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p mu Omega 2) :
    MemLp (localizedForcing a ψ f u) 2 (mu.restrict Omega) := by
  obtain ⟨N, _, hψN, hgradN⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  obtain ⟨C, hC⟩ := exists_norm_divMatrixGradient_le hM hK hψ hψc
  have hM0 : 0 ≤ M := (norm_nonneg (matrixBilinearForm (a 0))).trans (hM 0)
  have hgψ := ContDiff.continuous_gradient hψ
  have hB : ∀ x (η ξ : EuclideanSpace ℝ ι), ‖matrixBilinearForm (a x) η ξ‖ ≤ M * ‖η‖ * ‖ξ‖ :=
    fun x η ξ => ((matrixBilinearForm (a x)).le_opNorm₂ η ξ).trans (by gcongr; exact hM x)
  have h1 : MemLp (fun x => ψ x * f x) 2 (mu.restrict Omega) :=
    (Lp.memLp f).of_le_mul (c := N)
      (hψ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hψN x) (norm_nonneg _))
  have h2 : MemLp (fun x => matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x)) 2
      (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient u)).of_le_mul (c := M * N)
      (aestronglyMeasurable_matrixBilinearForm_apply hK.continuous.aestronglyMeasurable
        (Lp.aestronglyMeasurable _) hgψ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => (hB _ _ _).trans (by
        rw [mul_right_comm]
        gcongr
        exact hgradN x))
  have h3 : MemLp (fun x => matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)) 2
      (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient u)).of_le_mul (c := M * N)
      (aestronglyMeasurable_matrixBilinearForm_apply hK.continuous.aestronglyMeasurable
        hgψ.aestronglyMeasurable (Lp.aestronglyMeasurable _))
      (Filter.Eventually.of_forall fun x => (hB _ _ _).trans (by
        gcongr
        exact hgradN x))
  have h4 : MemLp (fun x => W1p.value u x * divMatrixGradient a ψ x) 2 (mu.restrict Omega) :=
    (Lp.memLp (W1p.value u)).of_le_mul (c := C)
      ((Lp.aestronglyMeasurable _).mul
        (measurable_divMatrixGradient hK.continuous hψ).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  exact ((h1.sub h2).sub h3).sub h4

/-- **The weak equation tested against `ψ φ`.** For a weak solution `u` of `-div(a ∇u) = f` in
`Ω`, a smooth `ψ` compactly supported in `Ω`, and a test function `φ` on the whole space, the
product `ψ φ` is an admissible test function, and its gradient is `ψ ∇φ + φ ∇ψ`. -/
private theorem setIntegral_matrixBilinearForm_smul_add_eq {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ)) :
    ∫ x in Omega, matrixBilinearForm (a x) (ψ x • ∇ φ x + φ x • ∇ ψ x) (W1p.gradient u x) ∂mu =
      ∫ x in Omega, ψ x * f x * φ x ∂mu := by
  obtain ⟨N, hN, hψN, hgradN⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  have hψN' : ∀ x ∈ Omega, |ψ x| ≤ N := fun x _ => hψN x
  have hgradN' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ N := fun x _ => hgradN x
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
  set v := W1p.contDiffSMul ψ hψ hN hψN' hgradN' φΩ
  have hv : v ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hψ hN hψN' hgradN'
      hψc hts φΩ
  have h := hu ⟨v, hv⟩
  simp only at h
  rw [energyFormH1_zero_zero_eq_setIntegral] at h
  calc _ = ∫ x in Omega, matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_contDiffSMul_ae hψ hN hψN' hgradN' φΩ, hφv, hφg]
          with x h1 h2 h3
        rw [h1, h2, h3]
    _ = ∫ x in Omega, f x * W1p.value v x ∂mu := h
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.value_contDiffSMul_ae hψ hN hψN' hgradN' φΩ, hφv] with x h1 h2
        rw [h1, h2, smul_eq_mul]
        ring

/-- **The localized weak equation, tested against a whole-space test function.** If `u` is a
weak solution of `-div(a ∇u) = f` in `Ω` and `ψ` is a smooth cutoff compactly supported in `Ω`,
then `ψ u`, whose weak gradient is `ψ ∇u + u ∇ψ`, satisfies the weak form of
`-div(a ∇(ψ u)) = localizedForcing a ψ f u` against every test function `φ` on the whole space. -/
private theorem setIntegral_matrixBilinearForm_cutoff_eq
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ)) :
    ∫ x in Omega, matrixBilinearForm (a x) (∇ φ x)
        (ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) ∂mu
      = ∫ x in Omega, localizedForcing a ψ f u x * φ x ∂mu := by
  -- The weak equation tested against `ψ φ`.
  have hE1 := setIntegral_matrixBilinearForm_smul_add_eq hu hψ hψc hts φ
  -- Integration by parts moves the derivative off `φ` in the term `u ⟨∇φ, a ∇ψ⟩`.
  have hE2 := setIntegral_value_mul_eq_neg hM hK u hψ hψc hts φ
  -- Every weight below vanishes off `tsupport ψ`, and all but `div(a ∇ψ)` are continuous.
  have hBc := hK.continuous
  have hψ' := hψ.continuous
  have hφ' := φ.continuous
  have hgψ := ContDiff.continuous_gradient hψ
  have hgφ := ContDiff.continuous_gradient φ.contDiff
  have hBn : Continuous fun x => ‖matrixBilinearForm (a x)‖ :=
    Continuous.norm (E := EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) hBc
  obtain ⟨C, hC⟩ := exists_norm_divMatrixGradient_le hM hK hψ hψc
  obtain ⟨Cφ, hCφ⟩ := hφ'.bounded_above_of_compact_support φ.hasCompactSupport
  have hcs : ∀ W : EuclideanSpace ℝ ι → ℝ, (∀ x, ψ x = 0 → ∇ ψ x = 0 →
      divMatrixGradient a ψ x = 0 → W x = 0) → HasCompactSupport W := fun W hW =>
    hψc.mono' fun x hx => by_contra fun hxψ => hx (hW x (image_eq_zero_of_notMem_tsupport hxψ)
      (gradient_of_notMem_tsupport hxψ)
      (divMatrixGradient_eq_zero_of_notMem_tsupport hxψ))
  have hu_m := Lp.aestronglyMeasurable (W1p.value u)
  have hgu_m := Lp.aestronglyMeasurable (W1p.gradient u)
  -- An `L²(Ω)` function times a square-integrable weight is integrable on `Ω`.
  have hint : ∀ {F W g : EuclideanSpace ℝ ι → ℝ}, MemLp F 2 (mu.restrict Omega) →
      MemLp W 2 (mu.restrict Omega) → AEStronglyMeasurable g (mu.restrict Omega) →
      (∀ x, ‖g x‖ ≤ W x * F x) → Integrable g (mu.restrict Omega) :=
    fun hF hW hg hle => (hW.integrable_mul hF).mono' hg (Filter.Eventually.of_forall hle)
  have hcont : ∀ {W : EuclideanSpace ℝ ι → ℝ}, Continuous W → HasCompactSupport W →
      MemLp W 2 (mu.restrict Omega) := fun hW hWc =>
    (hW.memLp_of_hasCompactSupport hWc).restrict _
  -- The one discontinuous weight, `φ div(a ∇ψ)`, is bounded with compact support.
  have hφD : MemLp (fun x => φ x * divMatrixGradient a ψ x) 2 (mu.restrict Omega) :=
    ((hcs _ fun x _ _ h3 => by simp [h3]).memLp_of_bound
      (hφ'.measurable.mul (measurable_divMatrixGradient hBc hψ)).aestronglyMeasurable (Cφ * C)
      (Filter.Eventually.of_forall fun x => by
        simp only [Pi.mul_apply, norm_mul]
        exact mul_le_mul (hCφ x) (hC x) (norm_nonneg _) ((norm_nonneg _).trans (hCφ x)))).restrict _
  have hT1 : Integrable (fun x => matrixBilinearForm (a x) (ψ x • ∇ φ x + φ x • ∇ ψ x)
      (W1p.gradient u x)) (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (hcont (W := fun x => ‖matrixBilinearForm (a x)‖ * ‖ψ x • ∇ φ x + φ x • ∇ ψ x‖)
        (by fun_prop)
        (hcs _ fun x h1 h2 _ => by simp [h1, h2]))
      (aestronglyMeasurable_matrixBilinearForm_apply hBc.aestronglyMeasurable
        (Continuous.aestronglyMeasurable (by fun_prop)) hgu_m)
      (fun x => (matrixBilinearForm (a x)).le_opNorm₂ _ _)
  have hT2 : Integrable (fun x => φ x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x))
      (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (hcont (W := fun x => ‖φ x‖ * (‖matrixBilinearForm (a x)‖ * ‖∇ ψ x‖))
        (by fun_prop) (hcs _ fun x _ h2 _ => by simp [h2]))
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        (aestronglyMeasurable_matrixBilinearForm_apply hBc.aestronglyMeasurable
          (Continuous.aestronglyMeasurable (by fun_prop)) hgu_m))
      (fun x => by
        rw [norm_mul, mul_assoc]
        gcongr
        exact (matrixBilinearForm (a x)).le_opNorm₂ _ _)
  have hQ : Integrable (fun x => φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x))
      (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (hcont (W := fun x => ‖φ x‖ * (‖matrixBilinearForm (a x)‖ * ‖∇ ψ x‖))
        (by fun_prop) (hcs _ fun x _ h2 _ => by simp [h2]))
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        (aestronglyMeasurable_matrixBilinearForm_apply hBc.aestronglyMeasurable hgu_m
          (Continuous.aestronglyMeasurable (by fun_prop))))
      (fun x => by
        rw [norm_mul, mul_assoc]
        gcongr
        exact ((matrixBilinearForm (a x)).le_opNorm₂ _ _).trans_eq (by ring))
  have hT4 : Integrable (fun x => W1p.value u x * (φ x * divMatrixGradient a ψ x))
      (mu.restrict Omega) :=
    (Lp.memLp (W1p.value u)).integrable_mul hφD
  have hT3 : Integrable (fun x => W1p.value u x * (matrixBilinearForm (a x) (∇ φ x) (∇ ψ x)
      + φ x * divMatrixGradient a ψ x)) (mu.restrict Omega) := by
    have hT3' : Integrable (fun x => W1p.value u x * matrixBilinearForm (a x) (∇ φ x) (∇ ψ x))
        (mu.restrict Omega) :=
      hint (Lp.memLp (W1p.value u)).norm
        (hcont (W := fun x => ‖matrixBilinearForm (a x) (∇ φ x) (∇ ψ x)‖) (by fun_prop)
          (hcs _ fun x _ h2 _ => by simp [h2]))
        (hu_m.mul (Continuous.aestronglyMeasurable (by fun_prop)))
        (fun x => by rw [norm_mul, mul_comm])
    exact (hT3'.add hT4).congr (.of_forall fun x => by simp only [Pi.add_apply, mul_add])
  have hP : Integrable (fun x => ψ x * f x * φ x) (mu.restrict Omega) :=
    hint (Lp.memLp f).norm (hcont (W := fun x => ‖ψ x * φ x‖)
      (by fun_prop) (hcs _ fun x h1 _ _ => by simp [h1]))
      (((Continuous.aestronglyMeasurable (by fun_prop)).mul (Lp.aestronglyMeasurable f)).mul
        (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun x => by
        simp only [norm_mul]
        exact le_of_eq (by ring))
  -- Assemble: both sides are the same combination of the six integrals above.
  calc ∫ x in Omega, matrixBilinearForm (a x) (∇ φ x)
        (ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) ∂mu
      = ∫ x in Omega, (matrixBilinearForm (a x) (ψ x • ∇ φ x + φ x • ∇ ψ x) (W1p.gradient u x)
          - φ x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)
          + W1p.value u x * (matrixBilinearForm (a x) (∇ φ x) (∇ ψ x)
            + φ x * divMatrixGradient a ψ x)
          - W1p.value u x * (φ x * divMatrixGradient a ψ x)) ∂mu := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
        ring
    _ = (∫ x in Omega, ψ x * f x * φ x ∂mu)
          - ∫ x in Omega, φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x) ∂mu
          - ∫ x in Omega, φ x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x) ∂mu
          - ∫ x in Omega, W1p.value u x * (φ x * divMatrixGradient a ψ x) ∂mu := by
        rw [integral_sub ?_ hT4, integral_add ?_ hT3, integral_sub hT1 hT2, hE1, hE2]
        · ring
        · exact hT1.sub hT2
        · exact (hT1.sub hT2).add hT3
    _ = ∫ x in Omega, (ψ x * f x * φ x
          - φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x)
          - φ x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)
          - W1p.value u x * (φ x * divMatrixGradient a ψ x)) ∂mu := by
        rw [integral_sub ?_ hT4, integral_sub ?_ hT2, integral_sub hP hQ]
        · exact hP.sub hQ
        · exact (hP.sub hQ).sub hT2
    _ = ∫ x in Omega, localizedForcing a ψ f u x * φ x ∂mu := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [localizedForcing_def]
        ring

/-- The whole-space weak equation for the extended cutoff product, against a test function. -/
private theorem energyFormH1_ofTestFunctionₗ_eq_of_ae_eq_indicator
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {w : W1p mu ⊤ 2}
    (hwg : ∀ᵐ x ∂mu, W1p.gradient w x = (Omega : Set (EuclideanSpace ℝ ι)).indicator
      (fun y => ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y) x)
    {g : EuclideanSpace ℝ ι → ℝ}
    (hg : ∀ᵐ x ∂mu, g x = (Omega : Set (EuclideanSpace ℝ ι)).indicator
      (localizedForcing a ψ f u) x)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ)) :
    energyFormH1 a 0 0 w (W1p.ofTestFunctionₗ mu ⊤ 2 φ) =
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), g x * φ x ∂mu := by
  have hΩ := Omega.isOpen.measurableSet
  have htop : mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) = mu := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hint_top : ∀ F : EuclideanSpace ℝ ι → ℝ,
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), F x ∂mu =
        ∫ x, F x ∂mu := fun F => by rw [htop]
  have hφg := (gradientTestFunctionLp_apply_ae (mu := mu) 2 φ).filter_mono (ae_mono htop.ge)
  rw [energyFormH1_zero_zero_eq_setIntegral, hint_top, hint_top]
  calc ∫ x, matrixBilinearForm (a x) (W1p.gradient (W1p.ofTestFunctionₗ mu ⊤ 2 φ) x)
          (W1p.gradient w x) ∂mu
      = ∫ x, (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => matrixBilinearForm (a y)
          (∇ φ y) (ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y)) x ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [hφg, hwg] with x h1 h2
        rw [W1p.gradient_ofTestFunctionₗ, h1, h2]
        by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
        · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ]
        · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ, map_zero]
    _ = ∫ x in Omega, localizedForcing a ψ f u x * φ x ∂mu := by
        rw [integral_indicator hΩ]
        exact setIntegral_matrixBilinearForm_cutoff_eq hM hK hu hψ hψc hts φ
    _ = ∫ x, g x * φ x ∂mu := by
        rw [← integral_indicator hΩ]
        refine integral_congr_ae ?_
        filter_upwards [hg] with x h
        rw [h]
        by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
        · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ]
        · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ, zero_mul]

/-- **A cutoff of a weak solution solves an equation on the whole space.** Let `a` be a
coefficient field on the whole space with `‖a(x)‖ ≤ M` and `x ↦ a(x)` Lipschitz, both measured in
the operator norm of its bilinear forms. Let `u ∈ H¹(Ω)` be a weak solution of
`-div(a ∇u) = f` in `Ω`, with `f ∈ L²(Ω)` and no boundary condition, and let `ψ` be smooth and
compactly supported in `Ω`. Then `ψ u`, extended by zero, is a weak solution of
`-div(a ∇w) = g` on the whole space for `g ∈ L²(ℝⁿ)` given almost everywhere by

`g = ψ f - ⟨∇u, a ∇ψ⟩ - ⟨∇ψ, a ∇u⟩ - u div(a ∇ψ)`, extended by zero.

No ellipticity and no regularity of `∂Ω` is needed. -/
theorem exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∃ w : W1p0 mu ⊤ 2, ∃ g : Lp ℝ 2
        (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      IsWeakSolutionDirichlet a 0 0 g w ∧
        (∀ᵐ x ∂mu, g x = (Omega : Set (EuclideanSpace ℝ ι)).indicator
          (localizedForcing a ψ f u) x) ∧
        (∀ᵐ x ∂mu, W1p.value (w : W1p mu ⊤ 2) x =
          (Omega : Set (EuclideanSpace ℝ ι)).indicator
            (fun y => ψ y * W1p.value u y) x) ∧
        ∀ᵐ x ∂mu, W1p.gradient (w : W1p mu ⊤ 2) x =
          (Omega : Set (EuclideanSpace ℝ ι)).indicator
            (fun y => ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y) x := by
  have hΩ := Omega.isOpen.measurableSet
  have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ⊆
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) :=
    SetLike.coe_subset_coe.mpr le_top
  obtain ⟨N, hN, hψN, hgradN⟩ :=
    (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  have hψN' : ∀ x ∈ Omega, |ψ x| ≤ N := fun x _ => hψN x
  have hgradN' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ N := fun x _ => hgradN x
  have hw := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (p := 2) (by norm_num)
    hψ hN hψN' hgradN' hψc hts u
  let w : W1p0 mu ⊤ 2 := W1p0.extendByZeroL le_top ⟨_, hw⟩
  -- The forcing term, extended by zero.
  have hG := memLp_localizedForcing hM hK hψ hψc f u
  have hg : ∀ᵐ x ∂mu, extendByZeroLpₗᵢ ℝ mu hΩ hsub (hG.toLp (localizedForcing a ψ f u)) x =
      (Omega : Set (EuclideanSpace ℝ ι)).indicator (localizedForcing a ψ f u) x := by
    have h2 := (coeFn_extendByZeroLpₗᵢ ℝ (μ := mu) hΩ hsub
      (hG.toLp (localizedForcing a ψ f u))).filter_mono
        (ae_mono (by rw [Opens.coe_top, Measure.restrict_univ]))
    have h3 := (ae_restrict_iff' hΩ).1 hG.coeFn_toLp
    filter_upwards [h2, h3] with x hx2 hx3
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [hx2, indicator_of_mem hxΩ, indicator_of_mem hxΩ, hx3 hxΩ]
    · rw [hx2, indicator_of_notMem hxΩ, indicator_of_notMem hxΩ]
  -- The energy form is continuous, so testing against test functions suffices.
  have hcoeff := memLp_energyIntegrand_of_continuous (mu := mu) hM hK.continuous ⊤
  refine ⟨w, _, (isWeakSolutionDirichlet_iff_forall_testFunction hcoeff _ _).2
    (fun φ => ?_), hg, ?_, ?_⟩
  · exact
    energyFormH1_ofTestFunctionₗ_eq_of_ae_eq_indicator hM hK hu hψ hψc hts
      (W1p.gradient_extendByZeroL_contDiffSMul_ae hψ hN hψN' hgradN' u hw) hg φ
  · exact W1p.value_extendByZeroL_contDiffSMul_ae hψ hN hψN' hgradN' u hw
  · exact W1p.gradient_extendByZeroL_contDiffSMul_ae hψ hN hψN' hgradN' u hw

/-- **Localizing a weak solution to the whole space.** Let `a` be a coefficient field on the
whole space with `‖a(x)‖ ≤ M` and `x ↦ a(x)` Lipschitz, both measured in the operator norm of its
bilinear forms. Let `u ∈ H¹(Ω)` be a weak solution of `-div(a ∇u) = f` in `Ω`, with
`f ∈ L²(Ω)` and no boundary condition. Near any compact `S ⊆ Ω`, `u` agrees, in value and in
gradient, with a weak solution `w ∈ H¹(ℝⁿ)` of an equation `-div(a ∇w) = g` on the whole space,
with `g ∈ L²(ℝⁿ)` and `g = f` almost everywhere on `S`.

One may take for `w` the product of `u` with a smooth cutoff equal to one near `S` and compactly
supported in `Ω`, extended by zero
(`TauCeti.PDE.exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul`). This is the device
that reduces interior regularity to regularity on the whole space. -/
theorem exists_isWeakSolutionDirichlet_top_ae_eq_on_of_isCompact
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {S : Set (EuclideanSpace ℝ ι)} (hS : IsCompact S)
    (hSΩ : S ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∃ w : W1p0 mu ⊤ 2, ∃ g : Lp ℝ 2
        (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      IsWeakSolutionDirichlet a 0 0 g w ∧
        (∀ᵐ x ∂mu, x ∈ S → W1p.value (w : W1p mu ⊤ 2) x = W1p.value u x) ∧
        (∀ᵐ x ∂mu, x ∈ S → W1p.gradient (w : W1p mu ⊤ 2) x = W1p.gradient u x) ∧
        ∀ᵐ x ∂mu, x ∈ S → g x = f x := by
  -- A smooth cutoff, equal to one near `S` and compactly supported in `Ω`.
  obtain ⟨ψ, hψ, -, hψ_one, hψc, hts⟩ :=
    hS.exists_contDiff_cutoff Omega.isOpen hSΩ
  have hψ_S : ∀ x ∈ S, ψ x = 1 ∧ ∇ ψ x = 0 := fun x hx => by
    have hev : ψ =ᶠ[nhds x] fun _ => (1 : ℝ) := mem_interior_iff_mem_nhds.1 (hψ_one hx)
    exact ⟨hev.eq_of_nhds, hev.gradient_eq.trans (gradient_fun_const x 1)⟩
  -- Near `S` the conormal field of `ψ` vanishes, and with it its divergence.
  have hdiv_S : ∀ x ∈ S, divMatrixGradient a ψ x = 0 := by
    intro x hx
    have hgrad_near : ∀ᶠ y in nhds x, ∇ ψ y = 0 := by
      filter_upwards [IsOpen.mem_nhds isOpen_interior (hψ_one hx)] with y hy
      have hev : ψ =ᶠ[nhds y] fun _ => (1 : ℝ) := mem_interior_iff_mem_nhds.1 hy
      exact hev.gradient_eq.trans (gradient_fun_const y 1)
    refine Finset.sum_eq_zero fun i _ => ?_
    have hfield : (fun y => matrixBilinearForm (a y) (EuclideanSpace.basisFun ι ℝ i)
        (∇ ψ y)) =ᶠ[nhds x] 0 := by
      filter_upwards [hgrad_near] with y hy
      simp [hy]
    rw [hfield.lineDeriv_eq]
    simp [lineDeriv]
  obtain ⟨w, g, hg, hforce, hval, hgrad⟩ :=
    exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul hM hK hu hψ hψc hts
  refine ⟨w, g, hg, ?_, ?_, ?_⟩
  · filter_upwards [hval] with x hx hxS
    rw [hx, indicator_of_mem (hSΩ hxS), (hψ_S x hxS).1, one_mul]
  · filter_upwards [hgrad] with x hx hxS
    rw [hx, indicator_of_mem (hSΩ hxS), (hψ_S x hxS).1, (hψ_S x hxS).2, one_smul, smul_zero,
      add_zero]
  · filter_upwards [hforce] with x hx hxS
    rw [hx, indicator_of_mem (hSΩ hxS)]
    simp [localizedForcing_def, (hψ_S x hxS).1, (hψ_S x hxS).2, hdiv_S x hxS]

/-! ### Interior `H²` regularity -/

/-- **Interior `H²` regularity for Lipschitz principal coefficients.** Let `a` be uniformly
elliptic on `Ω`, with `x ↦ a(x)` locally Lipschitz on `Ω` in the operator norm of its bilinear
forms, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

in the sense that `∫_Ω (⟨∇v, a ∇u⟩ + ⟨b, ∇u⟩ v + c u v) = ∫_Ω f v` for every
`v ∈ H¹₀(Ω)`, with no boundary condition on `u`. Then `u ∈ H²_loc(Ω)`: on every open `V`
whose closure is compact and contained in `Ω`, the restriction of `u` is the first-order part
of an element of `W^{2,2}(V)`.

No regularity of `∂Ω`, sign of `c`, or smallness of the lower-order terms is assumed, and the
Lipschitz bound on `a` need not be uniform on `Ω`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn [DecidableEq ι]
    {lam Lam : ℝ}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LocallyLipschitzOn (Omega : Set (EuclideanSpace ℝ ι))
      fun x => matrixBilinearForm (a x))
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ U : Wkp mu V 2 2, Wkp.lowerOrder 1 U =
      W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)) u := by
  -- Near `closure V`, the field agrees with a Lipschitz uniformly elliptic field `a'` on `ℝⁿ`.
  obtain ⟨a', K', U, hVU, hUΩ, ha', hK', haa'⟩ := ha.exists_lipschitzWith_eqOn hK hV hVΩ
  have hUΩ' : (U : Set (EuclideanSpace ℝ ι)) ⊆ Omega := SetLike.coe_subset_coe.mpr hUΩ
  have hle : mu.restrict U ≤ mu.restrict Omega := Measure.restrict_mono hUΩ' le_rfl
  -- On `U`, the restriction of `u` solves the equation with the principal coefficient `a'`.
  have hfU : MemLp f 2 (mu.restrict U) := (Lp.memLp f).mono_measure hle
  have huU : ∀ v : W1p0 mu U 2, energyFormH1 a' b c (W1p.restrictL hUΩ u) (v : W1p mu U 2) =
      ∫ x in U, hfU.toLp f x * W1p.value (v : W1p mu U 2) x ∂mu := by
    intro v
    have h := energyFormH1_restrictL_eq_setIntegral hUΩ hu v
    rw [energyFormH1_def] at h ⊢
    rw [setIntegral_congr_fun U.isOpen.measurableSet fun x hx => by rw [haa' hx], h]
    refine integral_congr_ae ?_
    filter_upwards [hfU.coeFn_toLp] with x hx
    rw [hx]
  -- The lower-order terms move to the right-hand side.
  obtain ⟨g, hg⟩ := exists_forcing_energyFormH1_principal_eq
    (memLp_energyIntegrand_of_continuous (fun x => ha'.opNorm_matrixBilinearForm_le (mem_univ x))
      hK'.continuous U)
    (hb.mono_measure hle) (hc.mono_measure hle) huU
  obtain ⟨w, f', hw, -, hgrad, -⟩ := exists_isWeakSolutionDirichlet_top_ae_eq_on_of_isCompact
    (fun x => ha'.opNorm_matrixBilinearForm_le (mem_univ x)) hK' hg hV hVU
  have htop : mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) = mu := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hVU' : (V : Set (EuclideanSpace ℝ ι)) ⊆ U := subset_closure.trans hVU
  -- On `V`, the gradient of the localized solution is that of `u`.
  have hgradV : ∀ᵐ x ∂mu.restrict V, W1p.gradient (w : W1p mu ⊤ 2) x =
      W1p.gradient (W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)) u) x := by
    filter_upwards [W1p.gradient_restrictL_ae (SetLike.coe_subset_coe.mp
        (subset_closure.trans hVΩ)) u,
      ae_restrict_of_ae_restrict_of_subset hVU' (W1p.gradient_restrictL_ae hUΩ u),
      (ae_restrict_iff' V.isOpen.measurableSet).2
        (hgrad.mono fun x hx hxV => hx (subset_closure hxV))] with x h1 h2 h3
    rw [h1, h3, h2]
  refine W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn _ (EuclideanSpace.basisFun ι ℝ)
    fun i j => ?_
  obtain ⟨G, -, hG⟩ := ha'.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith hK' hw
    (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i)
  have hmem : MemLp G 2 (mu.restrict V) :=
    (Lp.memLp G).mono_measure (by rw [htop]; exact Measure.restrict_le_self)
  refine ⟨hmem.toLp G, ((hG.mono le_top).congr_ae ?_).congr_ae_deriv hmem.coeFn_toLp.symm⟩
  filter_upwards [hgradV] with x hx
  rw [hx]

/-- **Interior `H²` regularity for a constant principal coefficient.** Let `A` be a constant,
uniformly elliptic matrix, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ⱼ(Aⁱʲ ∂ᵢu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

in the sense that `∫_Ω (⟨∇v, A ∇u⟩ + ⟨b, ∇u⟩ v + c u v) = ∫_Ω f v` for every
`v ∈ H¹₀(Ω)`, with no boundary condition on `u`. Then `u ∈ H²_loc(Ω)`: on every open `V`
whose closure is compact and contained in `Ω`, the restriction of `u` is the first-order part
of an element of `W^{2,2}(V)`. This is the constant case of
`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_restrictL {A : Matrix ι ι ℝ} {lam : ℝ}
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ))
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 (fun _ => A) b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ U : Wkp mu V 2 2, Wkp.lowerOrder 1 U =
      W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)) u := by
  classical
  exact (uniformlyEllipticOn_const _ hlam hA).exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn
    (LipschitzWith.const _).locallyLipschitz.locallyLipschitzOn hb hc hu hV hVΩ

end PDE

end TauCeti
