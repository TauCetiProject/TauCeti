/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Basic
import TauCeti.Analysis.PDE.Regularity.LipschitzCoefficient

/-!
# Interior `H²` regularity for a constant principal coefficient

Let `A` be a constant, uniformly elliptic coefficient matrix and let `u ∈ H¹(Ω)` be a weak
solution of the divergence-form equation

`-div(A ∇u) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)` and `b, c ∈ L∞(Ω)`,

meaning `∫_Ω (⟨∇v, A ∇u⟩ + ⟨b, ∇u⟩ v + c u v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`.
No boundary condition is imposed on `u` and nothing is assumed about `∂Ω`. Then
`u ∈ H²_loc(Ω)`: on every open `V` whose closure is compact and contained in `Ω`, the restriction
of `u` is the first-order part of an element of `W^{2,2}(V)`. This is the constant-coefficient
case of the interior regularity theorem for locally Lipschitz coefficients
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`), whose
proof localizes with a cutoff and applies the whole-space difference-quotient estimate.

The file also introduces the divergence `div(A ∇ψ)` of the conormal field of a function `ψ`,
which is the classical operator for a constant coefficient matrix, together with its coordinate
formula and the integration by parts that relates it to the weak form of the equation.

## Main declarations

* `TauCeti.PDE.divMatrixGradient`: the divergence of the conormal field `A ∇ψ`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL`: interior `H²` regularity.
* `TauCeti.PDE.divMatrixGradient_eq_sum_fderiv_fderiv_apply`: the classical Hessian contraction.
* `ContDiffOn.integral_matrixBilinearForm_gradient_eq_neg_integral_divMatrixGradient`:
  integration by parts against the conormal gradient of a `C²` function.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1, Theorem 1 (interior `H²` regularity).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.8.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ}

/-- The divergence `div(A ∇ψ) = ∑ᵢ ∂ᵢ (A ∇ψ)ᵢ` of the conormal field of `ψ`, computed in the
standard basis. It is the zeroth-order coefficient that commuting the operator `-div(A ∇ ·)` past
a cutoff `ψ` produces. -/
def divMatrixGradient (A : Matrix ι ι ℝ) (ψ : EuclideanSpace ℝ ι → ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, lineDeriv ℝ (fun y => matrixBilinearForm A (EuclideanSpace.basisFun ι ℝ i) (∇ ψ y)) x
    (EuclideanSpace.basisFun ι ℝ i)

/-- `div(A ∇ψ)` vanishes off the support of `ψ`. -/
@[simp] theorem divMatrixGradient_eq_zero_of_notMem_tsupport {ψ : EuclideanSpace ℝ ι → ℝ}
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

section ClassicalOperator

variable {g : EuclideanSpace ℝ ι → ℝ}

/-- For a `C²` function, the divergence of its constant-matrix conormal gradient is the
contraction of the matrix against the classical Hessian. -/
theorem divMatrixGradient_eq_sum_fderiv_fderiv_apply
    (hg : ContDiffOn ℝ 2 g Omega) {x : EuclideanSpace ℝ ι} (hx : x ∈ Omega) :
    divMatrixGradient A g x = ∑ j, ∑ i, A j i *
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
    ContinuousOn (divMatrixGradient A g) Omega := by
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
    (hψ : ContDiff ℝ ∞ ψ) : Continuous (divMatrixGradient A ψ) := by
  simpa only [Opens.coe_top, continuousOn_univ] using
    continuousOn_divMatrixGradient (A := A) (Omega := ⊤) (hψ.of_le (by simp)).contDiffOn

/-- Integration by parts for the constant-matrix conormal gradient of a `C²` function.
The test function is compactly supported in the open domain, so no boundary term occurs. -/
theorem _root_.ContDiffOn.integral_matrixBilinearForm_gradient_eq_neg_integral_divMatrixGradient
    {g : EuclideanSpace ℝ ι → ℝ} (hg : ContDiffOn ℝ 2 g Omega) (φ : 𝓓(Omega, ℝ)) :
    ∫ x, matrixBilinearForm A (∇ (φ : EuclideanSpace ℝ ι → ℝ) x) (∇ g x) ∂mu =
      -∫ x, φ x * divMatrixGradient A g x ∂mu := by
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
    _ = -∫ x, φ x * divMatrixGradient A g x ∂mu := by
      simp_rw [← smul_eq_mul, (hqweak _).integral_lineDeriv_smul_eq_neg_integral_smul φ]
      rw [Finset.sum_neg_distrib, ← integral_finsetSum _
        (fun i _ => integrable_smul_of_locallyIntegrableOn (hqd i) φ)]
      simp only [Finset.mul_sum, divMatrixGradient, b, q, smul_eq_mul]

end ClassicalOperator

/-- **Interior `H²` regularity for a constant principal coefficient.** Let `A` be a constant,
uniformly elliptic matrix, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ⱼ(Aⁱʲ ∂ᵢu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

in the sense that `∫_Ω (⟨∇v, A ∇u⟩ + ⟨b, ∇u⟩ v + c u v) = ∫_Ω f v` for every
`v ∈ H¹₀(Ω)`, with no boundary condition on `u`. Then `u ∈ H²_loc(Ω)`: on every open `V`
whose closure is compact and contained in `Ω`, the restriction of `u` is the first-order part
of an element of `W^{2,2}(V)`.

No regularity of `∂Ω`, sign of `c`, or smallness of the lower-order terms is assumed. This is the
constant-coefficient case of
`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_restrictL {lam : ℝ} (hlam : 0 < lam)
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
    (LocallyLipschitz.const _).locallyLipschitzOn hb hc hu hV hVΩ

end PDE

end TauCeti
