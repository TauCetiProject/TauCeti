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
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.MeasureTheory.Function.Lp.Restriction

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
case of a field with Lipschitz constant zero. It also proves the corresponding estimate on balls:
if `a` is `K`-Lipschitz with constants `λ ≤ Λ` on `B(x₀, 2 r) ⊆ Ω`, and `‖b‖ ≤ β`, `|c| ≤ γ`
almost everywhere there, then the second weak derivatives of `u` on `B(x₀, r)` satisfy

`λ ‖D²u‖_{L²(B_r)} ≲ ‖f‖ + (β + K + Λ / r) ‖∇u‖ + (γ + K / r + Λ / r²) ‖u‖`,

with norms on `B(x₀, 2 r)` on the right and a constant depending only on the dimension.

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

## The estimate on balls

The localization above is made quantitative. For a cutoff with `|ψ| ≤ 1`, `‖∇ψ‖ ≤ N` and `∇ψ`
`L`-Lipschitz, the forcing of the localized equation is bounded in `L²` by
`‖f‖ + 2 Λ N ‖∇u‖ + n (K N + Λ L) ‖u‖` (`TauCeti.PDE.eLpNorm_localizedForcing_le`), and the
gradient of `ψ u` by `‖∇u‖ + N ‖u‖`; the whole-space estimate then bounds `D²(ψ u)`. On a ball the
field is extended by precomposing with the radial retraction onto a closed ball, which keeps the
ellipticity constants and at most doubles the Lipschitz constant, and the cutoff from radius `r`
to `3 r / 2` has `N ≲ 1 / r` and `L ≲ 1 / r²`
(`TauCeti.exists_forall_contDiff_cutoff_closedBall`).

## Main declarations

* `TauCeti.PDE.divMatrixGradient` and `TauCeti.PDE.localizedForcing`: the divergence of the
  conormal cutoff field and the forcing term in the localized equation.
* `TauCeti.PDE.exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem`: a cutoff `ψ u`
  of a weak solution on `Ω ⊆ H`, with `tsupport ψ ∩ H ⊆ Ω` and `ψ u ∈ H¹₀(Ω)`, extended by zero,
  is a weak solution on `H` with an explicit `L²` forcing term. This localizes up to a part of
  `∂Ω` that lies in `∂H`, where `u` vanishes.
* `TauCeti.PDE.exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul`: its case `H = ℝⁿ`, for
  a cutoff compactly supported in `Ω`.
* `TauCeti.PDE.exists_isWeakSolutionDirichlet_top_ae_eq_on_of_isCompact`: near a compact subset
  of `Ω`, a weak solution and its forcing agree with a whole-space weak solution and its forcing.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`:
  interior `H²` regularity for locally Lipschitz principal coefficients.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL`: its case of a constant
  principal coefficient.
* `TauCeti.PDE.norm_divMatrixGradient_le`, `TauCeti.PDE.norm_localizedForcing_le` and
  `TauCeti.PDE.eLpNorm_localizedForcing_le`: quantitative bounds for `div(a ∇ψ)` and the
  localized forcing.
* `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_eqOn_one`: the
  interior `H²` estimate on the set where a given cutoff equals one.
* `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_ball`: **the
  interior `H²` estimate on balls**, with lower-order terms and explicit dependence on the radius.
* `TauCeti.PDE.divMatrixGradient_eq_sum_fderiv_fderiv_apply`: the classical Hessian contraction.
* `TauCeti.PDE.contDiff_divMatrixGradient`: `div(a ∇ψ)` is smooth when `a` and `ψ` are.
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
  {Omega H : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {K : ℝ≥0}
  {M : ℝ}

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

/-- For a Lipschitz field `a` and a smooth compactly supported `ψ`, every conormal
component `y ↦ ⟨η, a(y) ∇ψ(y)⟩` is Lipschitz. -/
theorem exists_lipschitzWith_matrixBilinearForm_gradient
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (η : EuclideanSpace ℝ ι) :
    ∃ L : ℝ≥0, LipschitzWith L fun y => matrixBilinearForm (a y) η (∇ ψ y) := by
  obtain ⟨Lg, hLg, hN⟩ :=
    (hψ.gradient_right (m := 1) (by simp)).exists_holderWith_and_norm_le_of_hasCompactSupport
      hψc.gradient le_rfl
  -- The conormal component is the Lipschitz functional `⟨η, a ·⟩` evaluated at `∇ ψ`; the
  -- functional is bounded on the compact support of `∇ ψ`, off which `∇ ψ` vanishes.
  have hf := (ContinuousLinearMap.lipschitzWith_apply η).comp hK
  obtain ⟨B, hB⟩ := hψc.gradient.isCompact.exists_bound_of_continuousOn hf.continuous.continuousOn
  let ev : (EuclideanSpace ℝ ι →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ).flip
  have hmain := ev.holderWith_comp₂_of_eq_zero (s := tsupport (∇ ψ)) (Mf := B.toNNReal)
    (Mg := Lg) ((holderWith_one.2 hf).holderOnWith _) hLg
    (fun x hx => (hB x hx).trans (Real.le_coe_toNNReal B)) (fun x _ => hN x)
    (fun _ hx => image_eq_zero_of_notMem_tsupport hx)
  exact ⟨_, holderWith_one.1 hmain⟩

/-- **`div(a ∇ψ)` is smooth for smooth coefficients.** If the entries of `a` are smooth and `ψ` is
smooth, then `div(a ∇ψ)` is smooth. -/
theorem contDiff_divMatrixGradient (ha : ∀ i j, ContDiff ℝ ∞ fun x => a x i j)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (divMatrixGradient a ψ) := by
  set b := EuclideanSpace.basisFun ι ℝ
  have hφ : ∀ i, ContDiff ℝ ∞ fun y => matrixBilinearForm (a y) (b i) (∇ ψ y) := fun i =>
    contDiff_matrixBilinearForm_apply ha contDiff_const (hψ.gradient_right (m := ∞) (by simp))
  have h : divMatrixGradient a ψ =
      fun x => ∑ i, fderiv ℝ (fun y => matrixBilinearForm (a y) (b i) (∇ ψ y)) x (b i) := by
    funext x
    rw [divMatrixGradient_def]
    exact Finset.sum_congr rfl fun i _ =>
      ((hφ i).differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
  rw [h]
  exact ContDiff.sum fun i _ => ((hφ i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

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
        (fun i _ => φ.integrable_smul (hqd i))]
      simp only [Finset.mul_sum, divMatrixGradient, b, q, smul_eq_mul]

end ClassicalOperator

/-- `div(a ∇ψ)` is bounded, for a Lipschitz field `a` and a smooth compactly supported `ψ`. -/
theorem exists_norm_divMatrixGradient_le
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∃ C, ∀ x, ‖divMatrixGradient a ψ x‖ ≤ C := by
  choose L hL using fun i => exists_lipschitzWith_matrixBilinearForm_gradient hK hψ hψc
    (EuclideanSpace.basisFun ι ℝ i)
  refine ⟨∑ i, (L i : ℝ) * ‖EuclideanSpace.basisFun ι ℝ i‖, fun x => ?_⟩
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ => norm_lineDeriv_le_of_lipschitz ℝ (hL i))

/-- **A bound for `div(a ∇ψ)`.** If `‖a(x)‖ ≤ M` and `x ↦ a(x)` is `K`-Lipschitz, both in the
operator norm of the bilinear forms, and the gradient of `ψ` is bounded by `N` and `L`-Lipschitz,
then `|div(a ∇ψ)| ≤ n (K N + M L)` everywhere, where `n` is the dimension. -/
theorem norm_divMatrixGradient_le {M N L : ℝ} (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hN : ∀ x, ‖∇ ψ x‖ ≤ N) (hL : ∀ x y, ‖∇ ψ x - ∇ ψ y‖ ≤ L * ‖x - y‖)
    (x : EuclideanSpace ℝ ι) :
    ‖divMatrixGradient a ψ x‖ ≤ Fintype.card ι * (K * N + M * L) := by
  rw [divMatrixGradient_def]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _i : ι, (K * N + M * L) := Finset.sum_le_sum fun i _ => ?_
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have he : ‖EuclideanSpace.basisFun ι ℝ i‖ = 1 := by simp
  have hL0 : 0 ≤ L := by
    have h := (norm_nonneg _).trans (hL (EuclideanSpace.basisFun ι ℝ i) 0)
    rwa [sub_zero, he, mul_one] at h
  have hM0 : 0 ≤ M := (norm_nonneg (matrixBilinearForm (a 0))).trans (hM 0)
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  have h := norm_lineDeriv_le_of_lip' ℝ (f := fun y => matrixBilinearForm (a y)
    (EuclideanSpace.basisFun ι ℝ i) (∇ ψ y)) (x₀ := x) (v := EuclideanSpace.basisFun ι ℝ i)
    (C := K * N + M * L) (by positivity) (Eventually.of_forall fun y => ?_)
  · rwa [he, mul_one] at h
  -- Split the increment into the variation of the field and that of the gradient.
  set e := EuclideanSpace.basisFun ι ℝ i
  have hsplit : matrixBilinearForm (a y) e (∇ ψ y) - matrixBilinearForm (a x) e (∇ ψ x) =
      (matrixBilinearForm (a y) - matrixBilinearForm (a x)) e (∇ ψ y) +
        matrixBilinearForm (a x) e (∇ ψ y - ∇ ψ x) := by
    simp only [sub_apply, map_sub]
    ring
  have h1 : ‖(matrixBilinearForm (a y) - matrixBilinearForm (a x)) e (∇ ψ y)‖ ≤
      K * ‖y - x‖ * N := by
    refine ((ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_)
    rw [he, mul_one]
    gcongr
    · simpa [dist_eq_norm] using hK.dist_le_mul y x
    · exact hN y
  have h2 : ‖matrixBilinearForm (a x) e (∇ ψ y - ∇ ψ x)‖ ≤ M * (L * ‖y - x‖) := by
    refine ((ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_)
    rw [he, mul_one]
    gcongr
    · exact hM x
    · exact hL y x
  rw [hsplit]
  calc _ ≤ K * ‖y - x‖ * N + M * (L * ‖y - x‖) := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = (K * N + M * L) * ‖y - x‖ := by ring

/-- `div(a ∇ψ)` is measurable, for a continuous field `a` and a smooth `ψ`. -/
theorem measurable_divMatrixGradient (ha : Continuous fun x => matrixBilinearForm (a x))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Measurable (divMatrixGradient a ψ) :=
  Finset.measurable_sum _ fun _ _ => measurable_lineDeriv
    ((ha.clm_apply continuous_const).clm_apply (ContDiff.continuous_gradient hψ (by simp)))

/-- The test function `φ ⟨v, a ∇ψ⟩`, for a test function `φ` on `H` and a smooth cutoff `ψ` with
`tsupport ψ ∩ H ⊆ Ω`, is Lipschitz with compact support in `Ω`. -/
private theorem exists_lipschitzWith_mul_matrixBilinearForm_gradient
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ∩ H ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (φ : 𝓓(H, ℝ))
    (v : EuclideanSpace ℝ ι) :
    ∃ L : ℝ≥0, LipschitzWith L (fun y => φ y * matrixBilinearForm (a y) v (∇ ψ y)) ∧
      HasCompactSupport (fun y => φ y * matrixBilinearForm (a y) v (∇ ψ y)) ∧
      tsupport (fun y => φ y * matrixBilinearForm (a y) v (∇ ψ y)) ⊆ Omega := by
  obtain ⟨Lh, hLh⟩ := exists_lipschitzWith_matrixBilinearForm_gradient hK hψ hψc v
  have hhc : HasCompactSupport fun y => matrixBilinearForm (a y) v (∇ ψ y) :=
    hψc.mono' ((subset_tsupport _).trans (tsupport_matrixBilinearForm_gradient_subset ψ v))
  obtain ⟨Ch, hCh⟩ := hLh.continuous.bounded_above_of_compact_support hhc
  obtain ⟨Lφ, hLφ⟩ := φ.contDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport (by simp)
  obtain ⟨Cφ, hCφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hsupp : Function.support (fun y => φ y * matrixBilinearForm (a y) v (∇ ψ y)) ⊆
      tsupport ψ ∩ tsupport φ := fun x hx =>
    ⟨tsupport_matrixBilinearForm_gradient_subset (a := a) ψ v
      (subset_tsupport _ fun h0 => hx (by simp only [h0, mul_zero])),
      subset_tsupport _ fun h0 => hx (by simp only [h0, zero_mul])⟩
  refine ⟨_, holderWith_one.1 ((ContinuousLinearMap.mul ℝ ℝ).holderWith_comp₂
      (holderWith_one.2 hLφ) (holderWith_one.2 hLh) (Mf := Cφ.toNNReal) (Mg := Ch.toNNReal)
      (fun x => (hCφ x).trans (Real.le_coe_toNNReal _))
      (fun x => (hCh x).trans (Real.le_coe_toNNReal _))), hψc.mono' (hsupp.trans inter_subset_left),
    (closure_minimal hsupp ((isClosed_tsupport ψ).inter (isClosed_tsupport _))).trans
      fun x hx => hts ⟨hx.1, φ.tsupport_subset hx.2⟩⟩

/-- **Integration by parts against the conormal field of a cutoff.** For `u ∈ H¹(Ω)`, a test
function `φ` on an open set `H`, and a smooth compactly supported `ψ` with
`tsupport ψ ∩ H ⊆ Ω`,

`∫_Ω u (⟨∇φ, a ∇ψ⟩ + φ div(a ∇ψ)) = -∫_Ω φ ⟨∇u, a ∇ψ⟩`,

the integration by parts of `u` against the Lipschitz components of `φ a ∇ψ`, which are compactly
supported in `Ω`. -/
private theorem setIntegral_value_mul_eq_neg
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) (u : W1p mu Omega 2)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ∩ H ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (φ : 𝓓(H, ℝ)) :
    ∫ x in Omega, W1p.value u x * (matrixBilinearForm (a x) (∇ φ x) (∇ ψ x)
        + φ x * divMatrixGradient a ψ x) ∂mu
      = -∫ x in Omega, φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x) ∂mu := by
  set b := EuclideanSpace.basisFun ι ℝ
  set h : ι → EuclideanSpace ℝ ι → ℝ := fun i y => matrixBilinearForm (a y) (b i) (∇ ψ y)
  choose Lh hLh using fun i => exists_lipschitzWith_matrixBilinearForm_gradient hK hψ hψc (b i)
  choose L hLg hgc hgs using fun i =>
    exists_lipschitzWith_mul_matrixBilinearForm_gradient hK hψ hψc hts φ (b i)
  -- Each `gᵢ = φ hᵢ` is Lipschitz with compact support in `Ω`.
  set g : ι → EuclideanSpace ℝ ι → ℝ := fun i y => φ y * h i y
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
  have hint1 := fun i => W1p.integrable_lineDeriv_mul_value u (hLg i) (hgc i) (b i)
  have hint2 := fun i => W1p.integrable_mul_inner_gradient u (hLg i).continuous (hgc i) (b i)
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
theorem memLp_localizedForcing
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p mu Omega 2) :
    MemLp (localizedForcing a ψ f u) 2 (mu.restrict Omega) := by
  obtain ⟨N, _, hψN, -⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  obtain ⟨C, hC⟩ := exists_norm_divMatrixGradient_le hK hψ hψc
  have hgψ := ContDiff.continuous_gradient hψ (by simp)
  -- The field times `∇ ψ` is continuous with compact support, hence bounded.
  have ha : Continuous fun x => ‖matrixBilinearForm (a x)‖ :=
    hK.continuous.norm (E := EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
  obtain ⟨D, hD⟩ :=
    (ha.mul hgψ.norm).bounded_above_of_compact_support hψc.gradient.norm.mul_left
  have hM' (x : EuclideanSpace ℝ ι) : ‖matrixBilinearForm (a x)‖ * ‖∇ ψ x‖ ≤ D :=
    (Real.le_norm_self _).trans (by simpa only [Pi.mul_apply] using hD x)
  have h1 : MemLp (fun x => ψ x * f x) 2 (mu.restrict Omega) :=
    (Lp.memLp f).of_le_mul (c := N)
      (hψ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hψN x) (norm_nonneg _))
  have h2 : MemLp (fun x => matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x)) 2
      (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient u)).of_le_mul (c := D)
      (aestronglyMeasurable_matrixBilinearForm_apply hK.continuous.aestronglyMeasurable
        (Lp.aestronglyMeasurable _) hgψ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x =>
        ((matrixBilinearForm (a x)).le_opNorm₂ _ _).trans <| by
          calc _ = (‖matrixBilinearForm (a x)‖ * ‖∇ ψ x‖) * ‖W1p.gradient u x‖ := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (hM' x) (norm_nonneg _))
  have h3 : MemLp (fun x => matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)) 2
      (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient u)).of_le_mul (c := D)
      (aestronglyMeasurable_matrixBilinearForm_apply hK.continuous.aestronglyMeasurable
        hgψ.aestronglyMeasurable (Lp.aestronglyMeasurable _))
      (Filter.Eventually.of_forall fun x =>
        ((matrixBilinearForm (a x)).le_opNorm₂ _ _).trans <|
          mul_le_mul_of_nonneg_right (hM' x) (norm_nonneg _))
  have h4 : MemLp (fun x => W1p.value u x * divMatrixGradient a ψ x) 2 (mu.restrict Omega) :=
    (Lp.memLp (W1p.value u)).of_le_mul (c := C)
      ((Lp.aestronglyMeasurable _).mul
        (measurable_divMatrixGradient hK.continuous hψ).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  exact ((h1.sub h2).sub h3).sub h4

/-- **A pointwise bound for the localized forcing term.** If `|ψ| ≤ P`, `‖∇ψ‖ ≤ N`,
`|div(a ∇ψ)| ≤ D` and `‖a(x)‖ ≤ M` everywhere, then at every point

`|ψ f - ⟨∇u, a ∇ψ⟩ - ⟨∇ψ, a ∇u⟩ - u div(a ∇ψ)| ≤ P |f| + 2 M N ‖∇u‖ + D |u|`. -/
theorem norm_localizedForcing_le {M N P D : ℝ} (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hP : ∀ x, |ψ x| ≤ P) (hN : ∀ x, ‖∇ ψ x‖ ≤ N)
    (hD : ∀ x, ‖divMatrixGradient a ψ x‖ ≤ D) (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p mu Omega 2) (x : EuclideanSpace ℝ ι) :
    ‖localizedForcing a ψ f u x‖ ≤
      P * ‖f x‖ + 2 * (M * N) * ‖W1p.gradient u x‖ + D * ‖W1p.value u x‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg (matrixBilinearForm (a 0))).trans (hM 0)
  have hMN : ‖matrixBilinearForm (a x)‖ * ‖∇ ψ x‖ ≤ M * N :=
    mul_le_mul (hM x) (hN x) (norm_nonneg _) hM0
  have h1 := (matrixBilinearForm (a x)).le_opNorm₂ (W1p.gradient u x) (∇ ψ x)
  have h2 := (matrixBilinearForm (a x)).le_opNorm₂ (∇ ψ x) (W1p.gradient u x)
  rw [localizedForcing_def]
  refine ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)).trans ?_
  rw [norm_mul, norm_mul, Real.norm_eq_abs]
  nlinarith [mul_le_mul_of_nonneg_right (hP x) (norm_nonneg (f x)),
    mul_le_mul_of_nonneg_right hMN (norm_nonneg (W1p.gradient u x)),
    mul_le_mul_of_nonneg_left (hD x) (norm_nonneg (W1p.value u x))]

/-- **An `L²` bound for the localized forcing term.** If `|ψ| ≤ P`, `‖∇ψ‖ ≤ N`,
`|div(a ∇ψ)| ≤ D` and `‖a(x)‖ ≤ M` everywhere, then the forcing term of the localized equation
satisfies

`‖ψ f - ⟨∇u, a ∇ψ⟩ - ⟨∇ψ, a ∇u⟩ - u div(a ∇ψ)‖_{L²(Ω)} ≤ P ‖f‖ + 2 M N ‖∇u‖ + D ‖u‖`. -/
theorem eLpNorm_localizedForcing_le {M N P D : ℝ} (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (ha : Continuous fun x => matrixBilinearForm (a x)) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hP : ∀ x, |ψ x| ≤ P) (hN : ∀ x, ‖∇ ψ x‖ ≤ N)
    (hD : ∀ x, ‖divMatrixGradient a ψ x‖ ≤ D) (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p mu Omega 2) :
    eLpNorm (localizedForcing a ψ f u) 2 (mu.restrict Omega) ≤
      ENNReal.ofReal (P * ‖f‖ + 2 * (M * N) * ‖W1p.gradient u‖ + D * ‖W1p.value u‖) := by
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hP 0)
  have hMN : 0 ≤ 2 * (M * N) := mul_nonneg zero_le_two (mul_nonneg
    ((norm_nonneg (matrixBilinearForm (a 0))).trans (hM 0)) ((norm_nonneg _).trans (hN 0)))
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hgψ := (ContDiff.continuous_gradient hψ (by simp)).aestronglyMeasurable
    (μ := mu.restrict Omega)
  have hBm := ha.aestronglyMeasurable (μ := mu.restrict Omega)
  have hmeas : AEStronglyMeasurable (localizedForcing a ψ f u) (mu.restrict Omega) :=
    (((hψ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)).sub
      (aestronglyMeasurable_matrixBilinearForm_apply hBm (Lp.aestronglyMeasurable _) hgψ)).sub
      (aestronglyMeasurable_matrixBilinearForm_apply hBm hgψ (Lp.aestronglyMeasurable _))).sub
      ((Lp.aestronglyMeasurable _).mul
        (measurable_divMatrixGradient ha hψ).aestronglyMeasurable)
  set F₁ : EuclideanSpace ℝ ι → ℝ := fun x => P * ‖f x‖
  set F₂ : EuclideanSpace ℝ ι → ℝ := fun x => 2 * (M * N) * ‖W1p.gradient u x‖
  set F₃ : EuclideanSpace ℝ ι → ℝ := fun x => D * ‖W1p.value u x‖
  -- Each term of the pointwise bound is a nonnegative multiple of the norm of an `L²` function.
  have key : ∀ {C X : ℝ} {g : EuclideanSpace ℝ ι → ℝ}, 0 ≤ C →
      eLpNorm g 2 (mu.restrict Omega) = ENNReal.ofReal X →
      eLpNorm (fun x => C * g x) 2 (mu.restrict Omega) ≤ ENNReal.ofReal (C * X) :=
    fun {C _ g} hC hg => by
      rw [ENNReal.ofReal_mul hC, ← hg, ← Real.eNorm_of_nonneg hC]
      exact (eLpNorm_const_smul C g 2 (mu.restrict Omega)).le
  have h₁ : eLpNorm F₁ 2 (mu.restrict Omega) ≤ ENNReal.ofReal (P * ‖f‖) :=
    key hP0 (by rw [eLpNorm_norm _ (Lp.aestronglyMeasurable _), ofReal_norm, Lp.eNorm_def])
  have h₂ : eLpNorm F₂ 2 (mu.restrict Omega) ≤
      ENNReal.ofReal (2 * (M * N) * ‖W1p.gradient u‖) :=
    key hMN (by rw [eLpNorm_norm _ (Lp.aestronglyMeasurable _), ofReal_norm, Lp.eNorm_def])
  have h₃ : eLpNorm F₃ 2 (mu.restrict Omega) ≤ ENNReal.ofReal (D * ‖W1p.value u‖) :=
    key hD0 (by rw [eLpNorm_norm _ (Lp.aestronglyMeasurable _), ofReal_norm, Lp.eNorm_def])
  calc eLpNorm (localizedForcing a ψ f u) 2 (mu.restrict Omega)
      ≤ eLpNorm (F₁ + F₂ + F₃) 2 (mu.restrict Omega) :=
        eLpNorm_mono_ae_real hmeas (.of_forall fun x => by
          simpa only [F₁, F₂, F₃, Pi.add_apply] using norm_localizedForcing_le hM hP hN hD f u x)
    _ ≤ eLpNorm F₁ 2 (mu.restrict Omega) + eLpNorm F₂ 2 (mu.restrict Omega) +
          eLpNorm F₃ 2 (mu.restrict Omega) :=
        (eLpNorm_add_le one_le_two).trans (add_le_add (eLpNorm_add_le one_le_two) le_rfl)
    _ ≤ _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
        exact add_le_add (add_le_add h₁ h₂) h₃

/-- **The weak equation tested against `ψ φ`.** For a weak solution `u` of `-div(a ∇u) = f` in
`Ω ⊆ H`, a smooth compactly supported `ψ` with `tsupport ψ ∩ H ⊆ Ω`, and a test function `φ` on
`H`, the product `ψ φ` is an admissible test function, and its gradient is `ψ ∇φ + φ ∇ψ`. -/
private theorem setIntegral_matrixBilinearForm_smul_add_eq (hΩH : Omega ≤ H)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ∩ H ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (φ : 𝓓(H, ℝ)) :
    ∫ x in Omega, matrixBilinearForm (a x) (ψ x • ∇ φ x + φ x • ∇ ψ x) (W1p.gradient u x) ∂mu =
      ∫ x in Omega, ψ x * f x * φ x ∂mu := by
  obtain ⟨N, hN, hψN, hgradN⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  have hψN' : ∀ x ∈ Omega, |ψ x| ≤ N := fun x _ => hψN x
  have hgradN' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ N := fun x _ => hgradN x
  have hΩ : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ H := SetLike.coe_subset_coe.mpr hΩH
  -- `φ` as an element of `H¹(Ω)`, and the test function `ψ φ ∈ H¹₀(Ω)`.
  set φΩ := W1p.restrictL hΩH (W1p.ofTestFunctionₗ mu H 2 φ)
  have hφv : ∀ᵐ x ∂mu.restrict Omega, W1p.value φΩ x = φ x := by
    filter_upwards [W1p.value_restrictL_ae hΩH (W1p.ofTestFunctionₗ mu H 2 φ),
      ae_restrict_of_ae_restrict_of_subset hΩ (testFunctionLp_apply_ae (mu := mu) 2 φ)]
      with x h1 h2
    rw [h1, W1p.value_ofTestFunctionₗ, h2]
  have hφg : ∀ᵐ x ∂mu.restrict Omega, W1p.gradient φΩ x = ∇ φ x := by
    filter_upwards [W1p.gradient_restrictL_ae hΩH (W1p.ofTestFunctionₗ mu H 2 φ),
      ae_restrict_of_ae_restrict_of_subset hΩ (gradientTestFunctionLp_apply_ae (mu := mu) 2 φ)]
      with x h1 h2
    rw [h1, W1p.gradient_ofTestFunctionₗ, h2]
  set v := W1p.contDiffSMul ψ hψ hN hψN' hgradN' φΩ
  -- `ψ φ` vanishes off the compact set `tsupport φ ∩ tsupport ψ ⊆ Ω`.
  have hv : v ∈ w1p0Submodule mu Omega 2 := by
    refine W1p.mem_w1p0Submodule_of_isCompact (by norm_num)
      (φ.hasCompactSupport.inter_right (isClosed_tsupport ψ))
      (fun x hx => hts ⟨hx.2, φ.tsupport_subset hx.1⟩) ?_
    filter_upwards [W1p.value_contDiffSMul_ae hψ hN hψN' hgradN' φΩ, hφv] with x h1 h2 hxK
    rw [h1, h2, smul_eq_mul]
    by_cases hxφ : x ∈ tsupport φ
    · rw [image_eq_zero_of_notMem_tsupport fun hxψ => hxK ⟨hxφ, hxψ⟩, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxφ, mul_zero]
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

/-- A function vanishing wherever the cutoff `ψ`, its gradient, and `div(a ∇ψ)` vanish has compact
support if `ψ` does. -/
private theorem hasCompactSupport_of_forall_eq_zero_cutoff {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψc : HasCompactSupport ψ) (W : EuclideanSpace ℝ ι → ℝ)
    (hW : ∀ x, ψ x = 0 → ∇ ψ x = 0 → divMatrixGradient a ψ x = 0 → W x = 0) :
    HasCompactSupport W :=
  hψc.mono' fun x hx => by_contra fun hxψ => hx (hW x (image_eq_zero_of_notMem_tsupport hxψ)
    (gradient_of_notMem_tsupport hxψ) (divMatrixGradient_eq_zero_of_notMem_tsupport hxψ))


/-- An `L²` function times a square-integrable weight is integrable. -/
private theorem integrable_of_norm_le_mul_memLp {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {F W g : X → ℝ} (hF : MemLp F 2 ν) (hW : MemLp W 2 ν) (hg : AEStronglyMeasurable g ν)
    (hle : ∀ x, ‖g x‖ ≤ W x * F x) : Integrable g ν :=
  (hW.integrable_mul hF).mono' hg (Filter.Eventually.of_forall hle)

/-- The terms of the cutoff computation that pair the weak gradient of `u ∈ H¹(Ω)` with a bounded
weight supported in `tsupport ψ` are integrable on `Ω`. -/
private theorem integrable_matrixBilinearForm_gradient_terms
    (hBc : Continuous fun x => matrixBilinearForm (a x)) (u : W1p mu Omega 2)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (φ : 𝓓(H, ℝ)) :
    Integrable (fun x => matrixBilinearForm (a x) (ψ x • ∇ φ x + φ x • ∇ ψ x)
      (W1p.gradient u x)) (mu.restrict Omega) ∧
    Integrable (fun x => φ x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x))
      (mu.restrict Omega) ∧
    Integrable (fun x => φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x))
      (mu.restrict Omega) := by
  -- Every weight vanishes off `tsupport ψ` and is continuous.
  have hψ' := hψ.continuous
  have hφ' := φ.continuous
  have hgψ := ContDiff.continuous_gradient hψ (by simp)
  have hBn : Continuous fun x => ‖matrixBilinearForm (a x)‖ :=
    Continuous.norm (E := EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) hBc
  have hcs := hasCompactSupport_of_forall_eq_zero_cutoff (a := a) hψc
  have hgu_m := Lp.aestronglyMeasurable (W1p.gradient u)
  have hT1 : Integrable (fun x => matrixBilinearForm (a x) (ψ x • ∇ φ x + φ x • ∇ ψ x)
      (W1p.gradient u x)) (mu.restrict Omega) :=
    integrable_of_norm_le_mul_memLp (Lp.memLp (W1p.gradient u)).norm
      ((Continuous.memLp_of_hasCompactSupport (μ := mu) (p := 2)
        (f := fun x => ‖matrixBilinearForm (a x)‖ * ‖ψ x • ∇ φ x + φ x • ∇ ψ x‖)
        (by fun_prop) (hcs _ fun x h1 h2 _ => by simp [h1, h2])).restrict _)
      (aestronglyMeasurable_matrixBilinearForm_apply hBc.aestronglyMeasurable
        (Continuous.aestronglyMeasurable (by fun_prop)) hgu_m)
      (fun x => (matrixBilinearForm (a x)).le_opNorm₂ _ _)
  have hW : MemLp (fun x => ‖φ x‖ * (‖matrixBilinearForm (a x)‖ * ‖∇ ψ x‖)) 2 (mu.restrict Omega) :=
    (Continuous.memLp_of_hasCompactSupport (μ := mu) (p := 2) (by fun_prop)
      (hcs _ fun x _ h2 _ => by simp [h2])).restrict _
  have hT2 : Integrable (fun x => φ x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x))
      (mu.restrict Omega) :=
    integrable_of_norm_le_mul_memLp (Lp.memLp (W1p.gradient u)).norm
      hW
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        (aestronglyMeasurable_matrixBilinearForm_apply hBc.aestronglyMeasurable
          (Continuous.aestronglyMeasurable (by fun_prop)) hgu_m))
      (fun x => by
        rw [norm_mul, mul_assoc]
        gcongr
        exact (matrixBilinearForm (a x)).le_opNorm₂ _ _)
  have hQ : Integrable (fun x => φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x))
      (mu.restrict Omega) :=
    integrable_of_norm_le_mul_memLp (Lp.memLp (W1p.gradient u)).norm
      hW
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        (aestronglyMeasurable_matrixBilinearForm_apply hBc.aestronglyMeasurable hgu_m
          (Continuous.aestronglyMeasurable (by fun_prop))))
      (fun x => by
        rw [norm_mul, mul_assoc]
        gcongr
        exact ((matrixBilinearForm (a x)).le_opNorm₂ _ _).trans_eq (by ring))
  exact ⟨hT1, hT2, hQ⟩

/-- The terms of the cutoff computation that pair `u ∈ H¹(Ω)` or the right-hand side `f` with a
weight supported in `tsupport ψ` are integrable on `Ω`. -/
private theorem integrable_value_terms
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) {f : Lp ℝ 2 (mu.restrict Omega)}
    (u : W1p mu Omega 2) {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (φ : 𝓓(H, ℝ)) :
    Integrable (fun x => W1p.value u x * (matrixBilinearForm (a x) (∇ φ x) (∇ ψ x)
      + φ x * divMatrixGradient a ψ x)) (mu.restrict Omega) ∧
    Integrable (fun x => W1p.value u x * (φ x * divMatrixGradient a ψ x))
      (mu.restrict Omega) ∧
    Integrable (fun x => ψ x * f x * φ x) (mu.restrict Omega) := by
  -- Every weight vanishes off `tsupport ψ`, and all but `div(a ∇ψ)` are continuous.
  have hBc := hK.continuous
  have hψ' := hψ.continuous
  have hφ' := φ.continuous
  have hgψ := ContDiff.continuous_gradient hψ (by simp)
  obtain ⟨C, hC⟩ := exists_norm_divMatrixGradient_le hK hψ hψc
  obtain ⟨Cφ, hCφ⟩ := hφ'.bounded_above_of_compact_support φ.hasCompactSupport
  have hcs := hasCompactSupport_of_forall_eq_zero_cutoff (a := a) hψc
  have hu_m := Lp.aestronglyMeasurable (W1p.value u)
  -- The one discontinuous weight, `φ div(a ∇ψ)`, is bounded with compact support.
  have hφD : MemLp (fun x => φ x * divMatrixGradient a ψ x) 2 (mu.restrict Omega) :=
    ((hcs _ fun x _ _ h3 => by simp [h3]).memLp_of_bound
      (hφ'.measurable.mul (measurable_divMatrixGradient hBc hψ)).aestronglyMeasurable (Cφ * C)
      (Filter.Eventually.of_forall fun x => by
        simp only [Pi.mul_apply, norm_mul]
        exact mul_le_mul (hCφ x) (hC x) (norm_nonneg _) ((norm_nonneg _).trans (hCφ x)))).restrict _
  have hT4 : Integrable (fun x => W1p.value u x * (φ x * divMatrixGradient a ψ x))
      (mu.restrict Omega) :=
    (Lp.memLp (W1p.value u)).integrable_mul hφD
  have hT3 : Integrable (fun x => W1p.value u x * (matrixBilinearForm (a x) (∇ φ x) (∇ ψ x)
      + φ x * divMatrixGradient a ψ x)) (mu.restrict Omega) := by
    have hT3' : Integrable (fun x => W1p.value u x * matrixBilinearForm (a x) (∇ φ x) (∇ ψ x))
        (mu.restrict Omega) :=
      integrable_of_norm_le_mul_memLp (Lp.memLp (W1p.value u)).norm
        ((Continuous.memLp_of_hasCompactSupport (μ := mu) (p := 2)
          (f := fun x => ‖matrixBilinearForm (a x) (∇ φ x) (∇ ψ x)‖) (by fun_prop)
          (hcs _ fun x _ h2 _ => by simp [h2])).restrict _)
        (hu_m.mul (Continuous.aestronglyMeasurable (by fun_prop)))
        (fun x => by rw [norm_mul, mul_comm])
    exact (hT3'.add hT4).congr (.of_forall fun x => by simp only [Pi.add_apply, mul_add])
  have hP : Integrable (fun x => ψ x * f x * φ x) (mu.restrict Omega) :=
    integrable_of_norm_le_mul_memLp (Lp.memLp f).norm
      ((Continuous.memLp_of_hasCompactSupport (μ := mu) (p := 2) (f := fun x => ‖ψ x * φ x‖)
        (by fun_prop) (hcs _ fun x h1 _ _ => by simp [h1])).restrict _)
      (((Continuous.aestronglyMeasurable (by fun_prop)).mul (Lp.aestronglyMeasurable f)).mul
        (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun x => by
        simp only [norm_mul]
        exact le_of_eq (by ring))
  exact ⟨hT3, hT4, hP⟩

/-- **The localized weak equation, tested against a test function on `H`.** If `u` is a weak
solution of `-div(a ∇u) = f` in `Ω ⊆ H` and `ψ` is a smooth compactly supported cutoff with
`tsupport ψ ∩ H ⊆ Ω`, then `ψ u`, whose weak gradient is `ψ ∇u + u ∇ψ`, satisfies the weak form
of `-div(a ∇(ψ u)) = localizedForcing a ψ f u` against every test function `φ` on `H`. -/
private theorem setIntegral_matrixBilinearForm_cutoff_eq
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) (hΩH : Omega ≤ H)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ∩ H ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (φ : 𝓓(H, ℝ)) :
    ∫ x in Omega, matrixBilinearForm (a x) (∇ φ x)
        (ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) ∂mu
      = ∫ x in Omega, localizedForcing a ψ f u x * φ x ∂mu := by
  -- The weak equation tested against `ψ φ`.
  have hE1 := setIntegral_matrixBilinearForm_smul_add_eq hΩH hu hψ hψc hts φ
  -- Integration by parts moves the derivative off `φ` in the term `u ⟨∇φ, a ∇ψ⟩`.
  have hE2 := setIntegral_value_mul_eq_neg hK u hψ hψc hts φ
  obtain ⟨hT1, hT2, hQ⟩ :=
    integrable_matrixBilinearForm_gradient_terms (a := a) hK.continuous u hψ hψc φ
  obtain ⟨hT3, hT4, hP⟩ := integrable_value_terms hK (f := f) u hψ hψc φ
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

/-- The weak equation on `H` for an extended cutoff product, against a test function. -/
private theorem energyFormH1_ofTestFunctionₗ_eq_of_ae_eq_indicator
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) (hΩH : Omega ≤ H)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ∩ H ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {w : W1p mu H 2}
    (hwg : ∀ᵐ x ∂mu.restrict H, W1p.gradient w x = (Omega : Set (EuclideanSpace ℝ ι)).indicator
      (fun y => ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y) x)
    {g : EuclideanSpace ℝ ι → ℝ}
    (hg : ∀ᵐ x ∂mu.restrict H, g x = (Omega : Set (EuclideanSpace ℝ ι)).indicator
      (localizedForcing a ψ f u) x)
    (φ : 𝓓(H, ℝ)) :
    energyFormH1 a 0 0 w (W1p.ofTestFunctionₗ mu H 2 φ) = ∫ x in H, g x * φ x ∂mu := by
  have hΩ := Omega.isOpen.measurableSet
  -- Integrals over `H` of functions supported in `Ω ⊆ H` are integrals over `Ω`.
  have hHΩ : (H : Set (EuclideanSpace ℝ ι)) ∩ Omega = Omega :=
    inter_eq_right.2 (SetLike.coe_subset_coe.mpr hΩH)
  rw [energyFormH1_zero_zero_eq_setIntegral]
  calc ∫ x in H, matrixBilinearForm (a x) (W1p.gradient (W1p.ofTestFunctionₗ mu H 2 φ) x)
          (W1p.gradient w x) ∂mu
      = ∫ x in H, (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => matrixBilinearForm (a y)
          (∇ φ y) (ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y)) x ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 φ, hwg] with x h1 h2
        rw [W1p.gradient_ofTestFunctionₗ, h1, h2]
        by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
        · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ]
        · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ, map_zero]
    _ = ∫ x in Omega, localizedForcing a ψ f u x * φ x ∂mu := by
        rw [setIntegral_indicator hΩ, hHΩ]
        exact setIntegral_matrixBilinearForm_cutoff_eq hK hΩH hu hψ hψc hts φ
    _ = ∫ x in H, g x * φ x ∂mu := by
        rw [← hHΩ, ← setIntegral_indicator hΩ]
        refine integral_congr_ae ?_
        filter_upwards [hg] with x h
        rw [h]
        by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
        · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ]
        · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ, zero_mul]

/-- **A cutoff of a weak solution with zero boundary values solves an equation on a larger
domain.** Let `a` be a coefficient field on the whole space with `‖a(x)‖ ≤ M` and `x ↦ a(x)`
Lipschitz, both measured in the operator norm of its bilinear forms. Let `Ω ⊆ H` be open, let
`u ∈ H¹(Ω)` be a weak solution of `-div(a ∇u) = f` in `Ω`, with `f ∈ L²(Ω)`, and let `ψ` be smooth
and compactly supported with `tsupport ψ ∩ H ⊆ Ω` and `ψ u ∈ H¹₀(Ω)`. Then `ψ u`, extended by
zero, lies in `H¹₀(H)` and is a weak solution of `-div(a ∇w) = g` on `H` for `g ∈ L²(H)` given
almost everywhere by

`g = ψ f - ⟨∇u, a ∇ψ⟩ - ⟨∇ψ, a ∇u⟩ - u div(a ∇ψ)`, extended by zero.

The support of `ψ` may meet `∂Ω`, but only where `∂Ω` is part of `∂H`; there the hypothesis
`ψ u ∈ H¹₀(Ω)` expresses that `u` vanishes on that part of the boundary. No ellipticity and no
regularity of `∂Ω` is needed. -/
theorem exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) (hΩH : Omega ≤ H)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ∩ H ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {N : ℝ} (hN : 0 ≤ N)
    (hψN : ∀ x ∈ Omega, |ψ x| ≤ N) (hgradN : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ N)
    (hmem : W1p.contDiffSMul ψ hψ hN hψN hgradN u ∈ w1p0Submodule mu Omega 2) :
    ∃ w : W1p0 mu H 2, ∃ g : Lp ℝ 2 (mu.restrict H),
      IsWeakSolutionDirichlet a 0 0 g w ∧
        (∀ᵐ x ∂mu.restrict H, g x = (Omega : Set (EuclideanSpace ℝ ι)).indicator
          (localizedForcing a ψ f u) x) ∧
        (∀ᵐ x ∂mu.restrict H, W1p.value (w : W1p mu H 2) x =
          (Omega : Set (EuclideanSpace ℝ ι)).indicator
            (fun y => ψ y * W1p.value u y) x) ∧
        ∀ᵐ x ∂mu.restrict H, W1p.gradient (w : W1p mu H 2) x =
          (Omega : Set (EuclideanSpace ℝ ι)).indicator
            (fun y => ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y) x := by
  have hΩ := Omega.isOpen.measurableSet
  have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ H := SetLike.coe_subset_coe.mpr hΩH
  let w : W1p0 mu H 2 := W1p0.extendByZeroL hΩH ⟨_, hmem⟩
  -- The forcing term, extended by zero.
  have hG := memLp_localizedForcing hK hψ hψc f u
  have hg : ∀ᵐ x ∂mu.restrict H,
      extendByZeroLpₗᵢ ℝ mu hΩ.nullMeasurableSet hsub (hG.toLp (localizedForcing a ψ f u)) x =
        (Omega : Set (EuclideanSpace ℝ ι)).indicator (localizedForcing a ψ f u) x := by
    have h3 := (ae_restrict_iff' hΩ).1 hG.coeFn_toLp
    filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ (μ := mu) hΩ.nullMeasurableSet hsub
      (hG.toLp (localizedForcing a ψ f u)), ae_restrict_of_ae h3] with x hx2 hx3
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [hx2, indicator_of_mem hxΩ, indicator_of_mem hxΩ, hx3 hxΩ]
    · rw [hx2, indicator_of_notMem hxΩ, indicator_of_notMem hxΩ]
  have hwg := W1p.gradient_extendByZeroL_contDiffSMul_ae hΩH hψ hN hψN hgradN u hmem
  -- The energy form is continuous, so testing against test functions suffices.
  have hcoeff := memLp_energyIntegrand_of_continuous (mu := mu) hM hK.continuous H
  exact ⟨w, _, (isWeakSolutionDirichlet_iff_forall_testFunction hcoeff _ _).2
    (energyFormH1_ofTestFunctionₗ_eq_of_ae_eq_indicator hK hΩH hu hψ hψc hts hwg hg), hg,
    W1p.value_extendByZeroL_contDiffSMul_ae hΩH hψ hN hψN hgradN u hmem, hwg⟩

/-- **A cutoff of a weak solution solves an equation on the whole space.** Let `a` be a
coefficient field on the whole space with `‖a(x)‖ ≤ M` and `x ↦ a(x)` Lipschitz, both measured in
the operator norm of its bilinear forms. Let `u ∈ H¹(Ω)` be a weak solution of
`-div(a ∇u) = f` in `Ω`, with `f ∈ L²(Ω)` and no boundary condition, and let `ψ` be smooth and
compactly supported in `Ω`. Then `ψ u`, extended by zero, is a weak solution of
`-div(a ∇w) = g` on the whole space for `g ∈ L²(ℝⁿ)` given almost everywhere by

`g = ψ f - ⟨∇u, a ∇ψ⟩ - ⟨∇ψ, a ∇u⟩ - u div(a ∇ψ)`, extended by zero.

No ellipticity and no regularity of `∂Ω` is needed. This is the case `H = ℝⁿ` of
`TauCeti.PDE.exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem`. -/
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
  obtain ⟨N, hN, hψN, hgradN⟩ :=
    (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  have hmem := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (p := 2) (by norm_num)
    hψ hN (fun x _ => hψN x) (fun x _ => hgradN x) hψc hts u
  have h := exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem hM hK le_top hu hψ
    hψc (inter_subset_left.trans hts) hN _ _ hmem
  simpa only [Opens.coe_top, Measure.restrict_univ] using h

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
    hS.exists_contDiff_cutoff_eventuallyEq_one Omega.isOpen hSΩ
  have hψ_S : ∀ x ∈ S, ψ x = 1 ∧ ∇ ψ x = 0 := fun x hx => by
    have hev : ψ =ᶠ[nhds x] fun _ => (1 : ℝ) := hψ_one x hx
    exact ⟨hev.eq_of_nhds, hev.gradient_eq.trans (gradient_fun_const x 1)⟩
  -- Near `S` the conormal field of `ψ` vanishes, and with it its divergence.
  have hdiv_S : ∀ x ∈ S, divMatrixGradient a ψ x = 0 := by
    intro x hx
    have hgrad_near : ∀ᶠ y in nhds x, ∇ ψ y = 0 := by
      filter_upwards [(hψ_one x hx).eventually_nhds] with y hy
      exact (EventuallyEq.gradient_eq hy).trans (gradient_fun_const y 1)
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
  -- On `U`, the restriction of `u` solves the equation with the principal coefficient `a'`, and
  -- the lower-order terms move to the right-hand side.
  obtain ⟨g, hg, -⟩ := exists_forcing_restrictL_of_eqOn hUΩ haa'
    (memLp_energyIntegrand_of_continuous
      (fun x => ha'.opNorm_matrixBilinearForm_le (mem_univ x)) hK'.continuous _) hb hc hu
  obtain ⟨w, f', hw, -, hgrad, -⟩ := exists_isWeakSolutionDirichlet_top_ae_eq_on_of_isCompact
    (fun x => ha'.opNorm_matrixBilinearForm_le (mem_univ x)) hK' hg hV hVU
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
  exact W1p.exists_lowerOrder_eq_of_gradient_eq_of_hasWeakLineDerivOn (EuclideanSpace.basisFun ι ℝ)
    le_top hgradV fun i j => by
      obtain ⟨G, -, hG⟩ := ha'.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith hK' hw
        (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i)
      exact ⟨G, hG⟩

/-- **Interior `H²` regularity for a constant principal coefficient.** Let `A` be a constant,
uniformly elliptic matrix, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(Aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

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

/-! ### The interior `H²` estimate -/

/-- **The interior `H²` estimate, given a cutoff.** Let `a` be uniformly elliptic on the whole
space with constants `λ ≤ Λ`, with `x ↦ a(x)` `K`-Lipschitz in the operator norm of its bilinear
forms, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, with `f ∈ L²(Ω)` and
no boundary condition. Let `ψ` be smooth and compactly supported in `Ω`, with `|ψ| ≤ 1`,
`‖∇ψ‖ ≤ N` and `∇ψ` `L`-Lipschitz, and equal to one on an open `V`. Then on `V` every derivative
`∂_y u` has a weak derivative in every direction `w`, with

`‖∂_w ∂_y u‖_{L²(V)} ≤ ‖y‖ ‖w‖ (‖f‖ + (2 Λ N + K) ‖∇u‖ + (n (K N + Λ L) + K N) ‖u‖) / λ`,

the norms on the right being those of `L²(Ω)` and `n` the dimension. -/
theorem UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_eqOn_one
    [DecidableEq ι] {lam Lam N L : ℝ} (ha : UniformlyEllipticOn univ a lam Lam)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ Omega) (hP : ∀ x, |ψ x| ≤ 1) (hN : ∀ x, ‖∇ ψ x‖ ≤ N)
    (hL : ∀ x z, ‖∇ ψ x - ∇ ψ z‖ ≤ L * ‖x - z‖) {V : Opens (EuclideanSpace ℝ ι)}
    (hV : EqOn ψ 1 V) (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict V),
      ‖G‖ ≤ ‖y‖ * ‖w‖ * (‖f‖ + (2 * Lam * N + K) * ‖W1p.gradient u‖ +
        (Fintype.card ι * (K * N + Lam * L) + K * N) * ‖W1p.value u‖) / lam ∧
      HasWeakLineDerivOn mu V (fun x => ⟪W1p.gradient u x, y⟫_ℝ) G w := by
  have hlam := ha.pos
  have hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam := fun x =>
    ha.opNorm_matrixBilinearForm_le (mem_univ x)
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  have hD := norm_divMatrixGradient_le hM hK hN hL
  -- The cutoff `ψ u`, extended by zero, solves an equation on the whole space, whose forcing and
  -- gradient are bounded by those of `u`.
  obtain ⟨uψ, g, huψ, hg, -, hgrad⟩ :=
    exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul hM hK hu hψ hψc hts
  obtain ⟨G, hGle, hG⟩ := ha.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith hK huψ y w
  have hgle : ‖g‖ ≤ 1 * ‖f‖ + 2 * (Lam * N) * ‖W1p.gradient u‖ +
      Fintype.card ι * (K * N + Lam * L) * ‖W1p.value u‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (ae_restrict_of_ae hg), Opens.coe_top, Measure.restrict_univ,
      eLpNorm_indicator_eq_eLpNorm_restrict Omega.isOpen.measurableSet.nullMeasurableSet]
    have hD0 := (norm_nonneg _).trans (hD 0)
    have hLN : 0 ≤ Lam * N := _root_.mul_nonneg ha.upper_nonneg hN0
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (eLpNorm_localizedForcing_le hM hK.continuous hψ hP hN hD f u)
  have hgradle : ‖W1p.gradient (uψ : W1p mu ⊤ 2)‖ ≤ ‖W1p.gradient u‖ + N * ‖W1p.value u‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (ae_restrict_of_ae hgrad), Opens.coe_top,
      Measure.restrict_univ,
      eLpNorm_indicator_eq_eLpNorm_restrict Omega.isOpen.measurableSet.nullMeasurableSet,
      ← one_mul ‖W1p.gradient u‖]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (W1p.eLpNorm_smul_gradient_add_smul_le
      hψ zero_le_one hN0 (fun x _ => hP x) (fun x _ => hN x) u)
  -- On `V`, where `ψ = 1`, the localized solution agrees with `u`.
  have hle : mu.restrict V ≤
      mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) :=
    Measure.restrict_mono (by simp) le_rfl
  have hGV := (Lp.memLp G).mono_measure hle
  refine ⟨hGV.toLp G, ?_, ?_⟩
  · rw [Lp.norm_toLp]
    refine (ENNReal.toReal_mono (Lp.eLpNorm_ne_top G) (eLpNorm_mono_measure _ hle)).trans
      (hGle.trans ?_)
    rw [mul_div_assoc', ← mul_assoc]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hlam.le
    linarith [mul_le_mul_of_nonneg_left hgradle K.coe_nonneg]
  · have hψV : ∀ x ∈ V, ψ x = 1 ∧ ∇ ψ x = 0 := fun x hx => by
      have hev : ψ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
        Filter.eventuallyEq_of_mem (V.isOpen.mem_nhds hx) fun z hz => hV hz
      exact ⟨hev.eq_of_nhds, hev.gradient_eq.trans (gradient_fun_const x 1)⟩
    have hVΩ : (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega := fun x hx =>
      hts (subset_tsupport ψ (by simp [(hψV x hx).1]))
    refine ((hG.mono le_top).congr_ae ?_).congr_ae_deriv hGV.coeFn_toLp.symm
    filter_upwards [ae_restrict_of_ae hgrad, ae_restrict_mem V.isOpen.measurableSet] with x h1 hxV
    rw [h1, indicator_of_mem (hVΩ hxV), (hψV x hxV).1, (hψV x hxV).2, one_smul, smul_zero,
      add_zero]

/-- The arithmetic of the interior estimate on balls: with the cutoff from radius `r` to
`3 r / 2`, whose gradient and Hessian are bounded by `N = c / (r / 2)` and `L = c / (r / 2)²`, the
bound of `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_eqOn_one`
for the extended field, with Lipschitz constant `2 K`, implies the bound with `C = 4 c (n + 1)`. -/
private theorem le_of_le_ball_bound {X g Gu Vu F G V β γ c r lam Lam Y : ℝ} {K : ℝ≥0} {n : ℕ}
    (hX : X ≤ Y * (g + (2 * Lam * (c / (r / 2)) + (K * 2 : ℝ≥0)) * Gu +
      (n * ((K * 2 : ℝ≥0) * (c / (r / 2)) + Lam * (c / (r / 2) ^ 2)) +
        (K * 2 : ℝ≥0) * (c / (r / 2))) * Vu) / lam)
    (hg : g ≤ F + β * Gu + γ * Vu) (hGu : Gu ≤ G) (hVu : Vu ≤ V) (hGu0 : 0 ≤ Gu) (hVu0 : 0 ≤ Vu)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hr : 0 < r) (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hY : 0 ≤ Y) :
    X ≤ Y * (F + (β + 2 * K + 4 * c * (n + 1) * Lam / r) * G +
      (γ + 4 * c * (n + 1) * K / r + 4 * c * (n + 1) * Lam / r ^ 2) * V) / lam := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hc1 : 2 * Lam * (c / (r / 2)) ≤ 4 * c * (n + 1) * Lam / r := by
    rw [show 2 * Lam * (c / (r / 2)) = 4 * c * Lam / r by field_simp; ring]
    exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg (mul_nonneg hc hn) hLam]) hr.le
  have hc2 : n * (2 * K * (c / (r / 2)) + Lam * (c / (r / 2) ^ 2)) + 2 * K * (c / (r / 2)) ≤
      4 * c * (n + 1) * K / r + 4 * c * (n + 1) * Lam / r ^ 2 := by
    rw [show n * (2 * K * (c / (r / 2)) + Lam * (c / (r / 2) ^ 2)) + 2 * K * (c / (r / 2)) =
      4 * c * (n + 1) * K / r + 4 * c * n * Lam / r ^ 2 by field_simp; ring]
    exact add_le_add le_rfl
      (div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hc hLam]) (by positivity))
  push_cast at hX
  refine hX.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hY) hlam.le)
  have hA : 0 ≤ 2 * Lam * (c / (r / 2)) + K * 2 := by positivity
  have hD : 0 ≤ n * (K * 2 * (c / (r / 2)) + Lam * (c / (r / 2) ^ 2)) + K * 2 * (c / (r / 2)) := by
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hGu hA, mul_le_mul_of_nonneg_left hVu hD,
    mul_le_mul_of_nonneg_left hGu hβ, mul_le_mul_of_nonneg_left hVu hγ,
    mul_le_mul_of_nonneg_right hc1 (hGu0.trans hGu),
    mul_le_mul_of_nonneg_right hc2 (hVu0.trans hVu)]

/-- The two reductions behind the interior estimate on balls. Let `a` be uniformly elliptic and
`K`-Lipschitz on `S ⊇ closedBall x₀ ρ`, and let `U ⊆ closedBall x₀ ρ`. Precomposed with the radial
retraction onto `closedBall x₀ ρ`, `a` becomes a field on the whole space, uniformly elliptic with
the same constants and `2 K`-Lipschitz, that agrees with `a` on `U`. On `U` the restriction of `u`
solves the principal equation for this field with a forcing bounded by `‖f‖ + β ‖∇u‖ + γ ‖u‖`. -/
private theorem exists_forcing_restrictL_of_subset_closedBall [DecidableEq ι]
    {U : Opens (EuclideanSpace ℝ ι)} {S : Set (EuclideanSpace ℝ ι)} {x₀ : EuclideanSpace ℝ ι}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    {ρ lam Lam β γ : ℝ} (hρ : 0 ≤ ρ) (hU : U ≤ Omega)
    (hUρ : (U : Set (EuclideanSpace ℝ ι)) ⊆ Metric.closedBall x₀ ρ)
    (hρS : Metric.closedBall x₀ ρ ⊆ S) (ha : UniformlyEllipticOn S a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) S)
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega)) (hβ0 : 0 ≤ β)
    (hβ : ∀ᵐ x ∂mu.restrict U, ‖b x‖ ≤ β) (hγ0 : 0 ≤ γ) (hγ : ∀ᵐ x ∂mu.restrict U, |c x| ≤ γ)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ, UniformlyEllipticOn univ a' lam Lam ∧
      LipschitzWith (K * 2) (fun x => matrixBilinearForm (a' x)) ∧
      ∃ g : Lp ℝ 2 (mu.restrict U), (∀ v : W1p0 mu U 2,
        energyFormH1 a' 0 0 (W1p.restrictL hU u) (v : W1p mu U 2) =
          ∫ x in U, g x * W1p.value (v : W1p mu U 2) x ∂mu) ∧
        ‖g‖ ≤ (eLpNorm f 2 (mu.restrict U)).toReal + β * ‖W1p.gradient (W1p.restrictL hU u)‖ +
          γ * ‖W1p.value (W1p.restrictL hU u)‖ := by
  have ha' : UniformlyEllipticOn univ (a ∘ centeredRadialRetraction x₀ ρ) lam Lam :=
    ha.comp fun x _ => hρS (centeredRadialRetraction_mem_closedBall hρ x)
  have hK' : LipschitzWith (K * 2) fun x =>
      matrixBilinearForm ((a ∘ centeredRadialRetraction x₀ ρ) x) :=
    (hK.mono hρS).comp_centeredRadialRetraction hρ
  obtain ⟨g, hg, hgle⟩ := exists_forcing_restrictL_of_eqOn hU (fun x hx => by
      simp only [Function.comp_apply, centeredRadialRetraction_of_mem_closedBall (hUρ hx)])
    (memLp_energyIntegrand_of_continuous
      (fun x => ha'.opNorm_matrixBilinearForm_le (mem_univ x)) hK'.continuous U) hb hc hu
  have hle : mu.restrict U ≤ mu.restrict Omega :=
    Measure.restrict_mono (SetLike.coe_subset_coe.mpr hU) le_rfl
  refine ⟨_, ha', hK', g, hg, hgle.trans ?_⟩
  gcongr
  · refine ENNReal.toReal_le_of_le_ofReal hβ0 ?_
    rw [eLpNorm_exponent_top (hb.mono_measure hle).aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound hβ
  · refine ENNReal.toReal_le_of_le_ofReal hγ0 ?_
    rw [eLpNorm_exponent_top (hc.mono_measure hle).aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (hγ.mono fun x hx => (Real.norm_eq_abs _).trans_le hx)

/-- **The interior `H²` estimate on balls** (Gilbarg–Trudinger, Theorem 8.8; Evans, §6.3.1,
Theorem 1). There is a constant `C`, depending only on the dimension `n`, with the following
property. Let `a` be uniformly elliptic on `B(x₀, 2 r) ⊆ Ω` with constants `λ ≤ Λ`, with
`x ↦ a(x)` `K`-Lipschitz there in the operator norm of its bilinear forms, let `b, c ∈ L∞(Ω)` with
`‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere on `B(x₀, 2 r)`, and let `u ∈ H¹(Ω)` be a weak
solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`

and no boundary condition. Then on `B(x₀, r)` every derivative `∂_y u` has a weak derivative in
every direction `w`, with

`λ ‖∂_w ∂_y u‖_{L²(B(x₀, r))} ≤`
`  ‖y‖ ‖w‖ (‖f‖ + (β + 2 K + C Λ / r) ‖∇u‖ + (γ + C K / r + C Λ / r²) ‖u‖)`,

the norms on the right being those of `L²(B(x₀, 2 r))`. The estimate is invariant under dilation:
multiplied by `r²`, its coefficients are the dimensionless `r β`, `r K`, `Λ` and `r² γ`, divided by
`λ`. No sign of `c`, smallness of `b` or regularity of `∂Ω` is assumed. -/
theorem UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_ball [DecidableEq ι] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      ⦃Omega : Opens (EuclideanSpace ℝ ι)⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι⦄ ⦃c : EuclideanSpace ℝ ι → ℝ⦄
      ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃r lam Lam β γ : ℝ⦄ ⦃K : ℝ≥0⦄
      ⦃f : Lp ℝ 2 (mu.restrict Omega)⦄ ⦃u : W1p mu Omega 2⦄,
      0 < r → Metric.ball x₀ (2 * r) ⊆ Omega →
      UniformlyEllipticOn (Metric.ball x₀ (2 * r)) a lam Lam →
      LipschitzOnWith K (fun x => matrixBilinearForm (a x)) (Metric.ball x₀ (2 * r)) →
      MemLp b ⊤ (mu.restrict Omega) → MemLp c ⊤ (mu.restrict Omega) →
      (∀ᵐ x ∂mu.restrict (Metric.ball x₀ (2 * r)), ‖b x‖ ≤ β) →
      (∀ᵐ x ∂mu.restrict (Metric.ball x₀ (2 * r)), |c x| ≤ γ) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      ∀ y w : EuclideanSpace ℝ ι, ∃ G : Lp ℝ 2 (mu.restrict (Metric.ball x₀ r)),
        ‖G‖ ≤ ‖y‖ * ‖w‖ * ((eLpNorm f 2 (mu.restrict (Metric.ball x₀ (2 * r)))).toReal +
          (β + 2 * K + C * Lam / r) *
            (eLpNorm (W1p.gradient u) 2 (mu.restrict (Metric.ball x₀ (2 * r)))).toReal +
          (γ + C * K / r + C * Lam / r ^ 2) *
            (eLpNorm (W1p.value u) 2 (mu.restrict (Metric.ball x₀ (2 * r)))).toReal) / lam ∧
        HasWeakLineDerivOn mu ⟨Metric.ball x₀ r, Metric.isOpen_ball⟩
          (fun x => ⟪W1p.gradient u x, y⟫_ℝ) G w := by
  obtain ⟨c₀, hc₀, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  refine ⟨4 * c₀ * (Fintype.card ι + 1), by positivity, ?_⟩
  intro mu _ Omega a b c x₀ r lam Lam β γ K f u hr hΩ ha hK hb hc hβ hγ hu y w
  -- The ball has positive measure, so the almost everywhere bounds force `0 ≤ β` and `0 ≤ γ`.
  have : (ae (mu.restrict (Metric.ball x₀ (2 * r)))).NeBot :=
    ae_restrict_neBot.2 (Metric.measure_ball_pos mu x₀ (by positivity)).ne'
  have hβ0 : 0 ≤ β := let ⟨_, hx⟩ := hβ.exists; (norm_nonneg _).trans hx
  have hγ0 : 0 ≤ γ := let ⟨_, hx⟩ := hγ.exists; (abs_nonneg _).trans hx
  -- Work on `U = B(x₀, 7 r / 4)`, with the field extended to the whole space.
  let U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ (7 * r / 4), Metric.isOpen_ball⟩
  have hUB : (U : Set (EuclideanSpace ℝ ι)) ⊆ Metric.ball x₀ (2 * r) :=
    Metric.ball_subset_ball (by linarith)
  have hUΩ : U ≤ Omega := SetLike.coe_subset_coe.mp (hUB.trans hΩ)
  obtain ⟨a', ha', hK', g, hu₂, hg⟩ := exists_forcing_restrictL_of_subset_closedBall
    (by positivity) hUΩ Metric.ball_subset_closedBall (Metric.closedBall_subset_ball (by linarith))
    ha hK hb hc hβ0 (ae_restrict_of_ae_restrict_of_subset hUB hβ) hγ0
    (ae_restrict_of_ae_restrict_of_subset hUB hγ) hu
  -- A cutoff equal to one on `closedBall x₀ r` and supported in `closedBall x₀ (3 r / 2) ⊆ U`.
  obtain ⟨ψ, hψ, hψI, hψ1, hψs, hψN, hψL⟩ := hcut x₀ hr.le (by linarith : r < 3 * r / 2)
  rw [show 3 * r / 2 - r = r / 2 by ring] at hψN hψL
  obtain ⟨G, hGle, hG⟩ := ha'.exists_norm_le_hasWeakLineDerivOn_gradient_of_eqOn_one hK' hu₂ hψ
    ((isCompact_closedBall x₀ _).of_isClosed_subset (isClosed_tsupport ψ) hψs)
    (hψs.trans (Metric.closedBall_subset_ball (by linarith)))
    (fun x => abs_le.2 ⟨by linarith [(hψI (mem_range_self x)).1], (hψI (mem_range_self x)).2⟩)
    hψN (fun x z => convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun p _ => ((hψ.gradient_right (m := 1) (by simp)).differentiable (by simp)) p)
      (fun p _ => hψL p) (mem_univ z) (mem_univ x))
    (V := ⟨Metric.ball x₀ r, Metric.isOpen_ball⟩)
    (fun x hx => hψ1 (Metric.ball_subset_closedBall hx)) y w
  refine ⟨G, ?_, hG.congr_ae (ae_restrict_of_ae_restrict_of_subset
    (Metric.ball_subset_ball (by linarith))
    ((W1p.gradient_restrictL_ae hUΩ u).mono fun x hx => by simp only [hx]))⟩
  -- Compare the norms on `U` with those on `B(x₀, 2 r)`.
  have hGU : ‖W1p.gradient (W1p.restrictL hUΩ u)‖ ≤
      (eLpNorm (W1p.gradient u) 2 (mu.restrict (Metric.ball x₀ (2 * r)))).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (W1p.gradient_restrictL_ae hUΩ u)]
    exact Lp.toReal_eLpNorm_restrict_mono _ hUB hΩ
  have hVU : ‖W1p.value (W1p.restrictL hUΩ u)‖ ≤
      (eLpNorm (W1p.value u) 2 (mu.restrict (Metric.ball x₀ (2 * r)))).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (W1p.value_restrictL_ae hUΩ u)]
    exact Lp.toReal_eLpNorm_restrict_mono _ hUB hΩ
  have hF := Lp.toReal_eLpNorm_restrict_mono f hUB hΩ
  exact le_of_le_ball_bound hGle (hg.trans (by linarith)) hGU hVU (norm_nonneg _) (norm_nonneg _)
    hβ0 hγ0 hc₀ hr ha.pos ha.upper_nonneg (by positivity)

end PDE

end TauCeti
