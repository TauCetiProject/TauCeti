/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Analysis.Calculus.DifferentialForm.HodgeLaplacian
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum

/-!
# The Witten differential, codifferential and Laplacian of forms in an orthonormal frame

Let `V` be an oriented finite-dimensional real inner product space, `f : V → ℝ` a function and
`t` a real parameter. On differential forms `ω : V → V [⋀^Fin k]→L[ℝ] ℝ`, Witten's deformation
of the exterior derivative and its formal adjoint are

* `d_t ω = dω + t df ∧ ω` (`TauCeti.wittenExtDeriv`), where `df ∧ ·` is the exterior
  multiplication `TauCeti.wedgeCovector (∇f x)` by the gradient, and
* `δ_t ω = δω + t ι_{∇f} ω` (`Orientation.wittenCodifferential`), where `δ = ± ⋆ d ⋆` is the
  codifferential `Orientation.codifferential` built from the Hodge star and the interior product
  `ι_u α` is `α.curryLeft u`.

They are the conjugates `d_t = e^{-t f} d e^{t f}`
(`TauCeti.wittenExtDeriv_apply_eq_exp_smul`) and `δ_t = e^{t f} δ e^{-t f}`
(`Orientation.wittenCodifferential_apply_eq_exp_smul`), so `δ_t` is the formal adjoint of `d_t`:
`∫ ⟪d_t φ, ψ⟫ = ∫ ⟪φ, δ_t ψ⟫` for compactly supported `ψ`
(`Orientation.integral_alternatingFormInner_wittenExtDeriv_eq_wittenCodifferential`). In an
orthonormal frame `(eᵢ)`, with `∂ᵢ` the derivative in the direction `eᵢ` and `ε_{eᵢ}` exterior
multiplication by `eⁱ`, they read `d_t ω = ∑ᵢ ε_{eᵢ} (∂ᵢω + t ∂ᵢf ω)`
(`TauCeti.wittenExtDeriv_eq_sum`) and `δ_t ω = ∑ᵢ ι_{eᵢ} (-∂ᵢω + t ∂ᵢf ω)`
(`Orientation.wittenCodifferential_eq_sum`).

The main result is **Witten's frame formula** for the Witten Laplacian `Δ_t = δ_t d_t + d_t δ_t`
(`Orientation.wittenCodifferential_wittenExtDeriv_add_wittenExtDeriv_wittenCodifferential`): for
`f` and a form `ω` of intermediate degree that are `C²` at `x`,

`Δ_t ω = -Δω + t² |∇f|² ω + t ∑_{i,j} Hess f(eᵢ, eⱼ) [ε_{eᵢ}, ι_{eⱼ}] ω`,

where `Δ = ∑ᵢ ∂ᵢ²` is Mathlib's Laplacian of `ω` as a vector-valued function (so `-Δ` is the
Hodge Laplacian of Euclidean space,
`Orientation.codifferential_extDeriv_add_extDeriv_codifferential_eq_neg_laplacian`) and
`[ε_{eᵢ}, ι_{eⱼ}] = ε_{eᵢ} ι_{eⱼ} - ι_{eⱼ} ε_{eᵢ}`. In degree zero only `δ_t d_t` occurs and the
Hessian term is multiplication by `-t Δf`
(`Orientation.wittenCodifferential_wittenExtDeriv_of_degree_zero`); in the top degree only
`d_t δ_t` occurs and it is multiplication by `t Δf`
(`Orientation.wittenExtDeriv_wittenCodifferential_of_eq_finrank`). For `f = x²` on the line these
two formulas specialize to the harmonic oscillators `-∂² + 4 t² x² - 2 t` on functions and
`-∂² + 4 t² x² + 2 t` on one-forms.

These are the flat, chart-level versions of the Witten operators of a Riemannian manifold built
from the Hodge star, and the frame formula is the local model of the Witten Laplacian near a
critical point where the metric is Euclidean. The computation has the same shape as the frame
formula `TauCeti.euclideanWittenLaplacian_apply` for the coordinate operators acting on
coefficient families; here the operators are those of the Hodge star and act on the forms
themselves. The proof expands `δ_t d_t` and `d_t δ_t` as double sums over the frame and uses the
anticommutation relation `ι_{eⱼ} ε_{eᵢ} + ε_{eᵢ} ι_{eⱼ} = ⟪eⱼ, eᵢ⟫`
(`TauCeti.curryLeftFlipL_wedgeCovector_add`) together with the symmetry of second derivatives.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
* B. Helffer and J. Sjöstrand, *Puits multiples en mécanique semi-classique IV: étude du
  complexe de Witten*, Comm. Partial Differential Equations **10** (1985), 245–340, §2.
-/

public section

noncomputable section

open Module Laplacian InnerProductSpace
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {k : ℕ}

namespace TauCeti

/-- **The Witten differential** `d_t ω = dω + t df ∧ ω` of differential `k`-forms on a
finite-dimensional real inner product space, where `df ∧ ·` is exterior multiplication by the
covector `⟪∇f x, ·⟫ = df x`. -/
def wittenExtDeriv (f : V → ℝ) (t : ℝ) (ω : V → V [⋀^Fin k]→L[ℝ] ℝ) (x : V) :
    V [⋀^Fin (k + 1)]→L[ℝ] ℝ :=
  extDeriv ω x + t • wedgeCovector (gradient f x) k (ω x)

theorem wittenExtDeriv_apply (f : V → ℝ) (t : ℝ) (ω : V → V [⋀^Fin k]→L[ℝ] ℝ) (x : V) :
    wittenExtDeriv f t ω x = extDeriv ω x + t • wedgeCovector (gradient f x) k (ω x) :=
  (rfl)

/-- At `t = 0` the Witten differential is the exterior derivative. -/
@[simp]
theorem wittenExtDeriv_zero (f : V → ℝ) (ω : V → V [⋀^Fin k]→L[ℝ] ℝ) :
    wittenExtDeriv f 0 ω = extDeriv ω := by
  funext x
  simp [wittenExtDeriv_apply]

/-- **The Witten differential in an orthonormal frame**: `d_t ω = ∑ᵢ ε_{eᵢ} (∂ᵢω + t ∂ᵢf ω)`. -/
theorem wittenExtDeriv_eq_sum (b : OrthonormalBasis ι ℝ V) (f : V → ℝ) (t : ℝ)
    (ω : V → V [⋀^Fin k]→L[ℝ] ℝ) (x : V) :
    wittenExtDeriv f t ω x =
      ∑ i, wedgeCovector (b i) k (fderiv ℝ ω x (b i) + (t * fderiv ℝ f x (b i)) • ω x) := by
  rw [wittenExtDeriv_apply, extDeriv_eq_sum_wedgeCovector b, wedgeCovector_eq_sum b,
    sum_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm, inner_gradient_left, smul_apply, map_add, map_smul, smul_smul]

/-- **The Witten differential is the conjugate `d_t = e^{-t f} d e^{t f}` of the exterior
derivative**: for `f` and `ω` differentiable at `x`, `d_t ω = e^{-t f} d (e^{t f} ω)` at `x`. -/
theorem wittenExtDeriv_apply_eq_exp_smul {f : V → ℝ} {ω : V → V [⋀^Fin k]→L[ℝ] ℝ} {x : V}
    (hf : DifferentiableAt ℝ f x) (hω : DifferentiableAt ℝ ω x) (t : ℝ) :
    wittenExtDeriv f t ω x =
      Real.exp (-(t * f x)) • extDeriv (fun y ↦ Real.exp (t * f y) • ω y) x := by
  have hc : HasFDerivAt (fun y ↦ Real.exp (t * f y))
      (innerSL ℝ ((Real.exp (t * f x) * t) • gradient f x)) x :=
    (hf.hasFDerivAt.const_mul t).exp.congr_fderiv <| by
      ext v
      simp only [smul_apply, innerSL_apply_apply, real_inner_smul_left, inner_gradient_left,
        smul_eq_mul]
      ring
  -- `extDeriv_function_smul` is stated for the pointwise product `c • ω` of the two functions.
  rw [show (fun y ↦ Real.exp (t * f y) • ω y) = (fun y ↦ Real.exp (t * f y)) • ω from rfl,
    extDeriv_function_smul hc.differentiableAt hω, hc.fderiv,
    alternatizeUncurryFin_innerSL_smulRight, wedgeCovector_smul, wittenExtDeriv_apply]
  simp only [smul_apply, smul_add, smul_smul, ← mul_assoc, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, one_mul, one_smul]

/-! ### Witten's frame formula -/

section FrameFormula

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The part `-∂ᵢ∂ⱼω + t ∂ⱼf ∂ᵢω - t ∂ᵢf ∂ⱼω + t² ∂ᵢf ∂ⱼf ω` of the double frame sums of
`d_t δ_t ω` and `δ_t d_t ω` that does not involve the Hessian of `f`. -/
private def frameTerm (b : OrthonormalBasis ι ℝ V) (f : V → ℝ) (ω : V → F) (x : V) (t : ℝ)
    (i j : ι) : F :=
  -fderiv ℝ (fderiv ℝ ω) x (b i) (b j) + (t * fderiv ℝ f x (b j)) • fderiv ℝ ω x (b i) -
    (t * fderiv ℝ f x (b i)) • fderiv ℝ ω x (b j) +
      (t ^ 2 * fderiv ℝ f x (b i) * fderiv ℝ f x (b j)) • ω x

/-- The diagonal of `frameTerm` sums to `-Δω + t² |∇f|² ω`. -/
private theorem sum_frameTerm_self (b : OrthonormalBasis ι ℝ V) (f : V → ℝ) (ω : V → F) (x : V)
    (t : ℝ) : ∑ i, frameTerm b f ω x t i i = -Δ ω x + (t ^ 2 * ‖gradient f x‖ ^ 2) • ω x := by
  rw [laplacian_eq_sum_fderiv_fderiv_orthonormalBasis b, ← b.sum_sq_inner_left, Finset.mul_sum,
    Finset.sum_smul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [frameTerm, inner_gradient_left]
  module

end FrameFormula

end TauCeti

namespace Orientation

open TauCeti
open ContinuousAlternatingMap (curryLeftFlipL curryLeftFlipL_apply_apply)

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n)) {l : ℕ}

/-- **The Witten codifferential** `δ_t ω = δω + t ι_{∇f} ω` of differential `(k + 1)`-forms on an
oriented inner product space of dimension `k + 1 + l`, the formal adjoint of the Witten
differential `TauCeti.wittenExtDeriv`. Here `δ` is the codifferential
`Orientation.codifferential` and the interior product `ι_u α` is `α.curryLeft u`. -/
def wittenCodifferential (hkl : k + 1 + l = finrank ℝ V) (f : V → ℝ) (t : ℝ)
    (ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : V) : V [⋀^Fin k]→L[ℝ] ℝ :=
  o.codifferential hkl ω x + t • (ω x).curryLeft (gradient f x)

theorem wittenCodifferential_apply (hkl : k + 1 + l = finrank ℝ V) (f : V → ℝ) (t : ℝ)
    (ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : V) :
    o.wittenCodifferential hkl f t ω x =
      o.codifferential hkl ω x + t • (ω x).curryLeft (gradient f x) :=
  (rfl)

/-- At `t = 0` the Witten codifferential is the codifferential. -/
@[simp]
theorem wittenCodifferential_zero (hkl : k + 1 + l = finrank ℝ V) (f : V → ℝ)
    (ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    o.wittenCodifferential hkl f 0 ω = o.codifferential hkl ω := by
  funext x
  simp [wittenCodifferential_apply]

/-- **The Witten codifferential in an orthonormal frame**:
`δ_t ω = ∑ᵢ ι_{eᵢ} (-∂ᵢω + t ∂ᵢf ω)`. -/
theorem wittenCodifferential_eq_sum (b : OrthonormalBasis ι ℝ V) (hkl : k + 1 + l = finrank ℝ V)
    (f : V → ℝ) (t : ℝ) (ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : V) :
    o.wittenCodifferential hkl f t ω x =
      ∑ i, (-fderiv ℝ ω x (b i) + (t * fderiv ℝ f x (b i)) • ω x).curryLeft (b i) := by
  rw [wittenCodifferential_apply, o.codifferential_eq_neg_sum_curryLeft b,
    ← b.sum_repr' (gradient f x), map_sum, Finset.smul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm, inner_gradient_left]
  simp only [← curryLeftFlipL_apply_apply, map_add, map_neg, map_smul, smul_smul]

/-- **The Witten codifferential is the conjugate `δ_t = e^{t f} δ e^{-t f}` of the
codifferential**: for `f` and `ω` differentiable at `x`, `δ_t ω = e^{t f} δ (e^{-t f} ω)` at `x`. -/
theorem wittenCodifferential_apply_eq_exp_smul (hkl : k + 1 + l = finrank ℝ V) {f : V → ℝ}
    {ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ} {x : V} (hf : DifferentiableAt ℝ f x)
    (hω : DifferentiableAt ℝ ω x) (t : ℝ) :
    o.wittenCodifferential hkl f t ω x =
      Real.exp (t * f x) • o.codifferential hkl (fun y ↦ Real.exp (-(t * f y)) • ω y) x := by
  have hc : HasGradientAt (fun y ↦ Real.exp (-(t * f y)))
      ((Real.exp (-(t * f x)) * -t) • gradient f x) x :=
    hasGradientAt_iff_hasFDerivAt.mpr <| (hf.hasFDerivAt.const_mul t).neg.exp.congr_fderiv <| by
      ext v
      simp only [smul_apply, neg_apply, Pi.neg_apply, toDual_apply_apply, real_inner_smul_left,
        inner_gradient_left, smul_eq_mul]
      ring
  rw [o.codifferential_function_smul hkl hc.differentiableAt hω, hc.gradient,
    wittenCodifferential_apply]
  simp only [map_smul, smul_sub, smul_smul, ← mul_assoc, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, one_mul, one_smul]
  module

/-- **The Witten codifferential is the formal adjoint of the Witten differential**:
`∫ ⟪d_t φ, ψ⟫ = ∫ ⟪φ, δ_t ψ⟫` for a `C¹` function `f`, a `C¹` form `φ` of degree `k` and a
compactly supported `C¹` form `ψ` of degree `k + 1`, with the Gram inner product of forms integrated
against the volume measure. -/
theorem integral_alternatingFormInner_wittenExtDeriv_eq_wittenCodifferential [MeasurableSpace V]
    [BorelSpace V] (hkl : k + 1 + l = finrank ℝ V) {f : V → ℝ} {φ : V → V [⋀^Fin k]→L[ℝ] ℝ}
    {ψ : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hf : ContDiff ℝ 1 f) (hφ : ContDiff ℝ 1 φ)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (t : ℝ) :
    ∫ x, alternatingFormInner V (k + 1) (wittenExtDeriv f t φ x) (ψ x) =
      ∫ x, alternatingFormInner V k (φ x) (o.wittenCodifferential hkl f t ψ x) := by
  have hE : ContDiff ℝ 1 fun y ↦ Real.exp (t * f y) := (contDiff_const.mul hf).exp
  have hE' : ContDiff ℝ 1 fun y ↦ Real.exp (-(t * f y)) := (contDiff_const.mul hf).neg.exp
  -- Move the weights `e^{± t f}` across the pairing and apply the adjointness of `d` and `δ`.
  have h := o.integral_alternatingFormInner_extDeriv_eq_codifferential hkl (hE.smul hφ)
    (hE'.smul hψ) (hc.smul_left (f := fun y ↦ Real.exp (-(t * f y))))
  -- The two sides of `h` write the weighted forms as `c • φ` rather than `fun y ↦ c y • φ y`;
  -- the final `rfl`s identify the two spellings.
  convert h using 2 <;> funext x
  · rw [wittenExtDeriv_apply_eq_exp_smul (hf.differentiable one_ne_zero x)
      (hφ.differentiable one_ne_zero x)]
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply', smul_eq_mul]
    rfl
  · rw [o.wittenCodifferential_apply_eq_exp_smul hkl (hf.differentiable one_ne_zero x)
      (hψ.differentiable one_ne_zero x)]
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply', smul_eq_mul]
    rfl

/-! ### Witten's frame formula -/

section FrameFormula

variable {f : V → ℝ} {x : V}

/-- `d_t δ_t ω` as a double frame sum: `∑ᵢ ∑ⱼ ε_{eᵢ} ι_{eⱼ} (Zᵢⱼ + t Hess f(eᵢ, eⱼ) ω)`, with
`Zᵢⱼ` the Hessian-free part `TauCeti.frameTerm`. -/
private theorem wittenExtDeriv_wittenCodifferential_eq_sum (b : OrthonormalBasis ι ℝ V)
    (hkl : k + 1 + l = finrank ℝ V) {ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hω : ContDiffAt ℝ 2 ω x) (t : ℝ) :
    wittenExtDeriv f t (o.wittenCodifferential hkl f t ω) x =
      ∑ i, ∑ j, wedgeCovector (b i) k (curryLeftFlipL (n := k) (b j)
        (frameTerm b f ω x t i j + (t * fderiv ℝ (fderiv ℝ f) x (b i) (b j)) • ω x)) := by
  have hcod : o.wittenCodifferential hkl f t ω = fun y ↦ ∑ j, curryLeftFlipL (n := k) (b j)
      ((-1 : ℝ) • fderiv ℝ ω y (b j) + (t * fderiv ℝ f y (b j)) • ω y) := by
    funext y
    rw [o.wittenCodifferential_eq_sum b]
    -- `rw [neg_one_smul]` does not see the literal `(-1 : ℝ)` here; `neg_one_smul ℝ` unifies it.
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [curryLeftFlipL_apply_apply, (neg_one_smul ℝ (fderiv ℝ ω y (b j)) :)]
  rw [wittenExtDeriv_eq_sum b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hcod, fderiv_sum_comp_smul_fderiv_add_mul_fderiv_smul_apply _ _ hf hω t (-1) (b i),
    ← hcod, o.wittenCodifferential_eq_sum b, Finset.smul_sum, ← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [frameTerm, ← curryLeftFlipL_apply_apply, map_add, map_sub, map_smul, map_neg]
  module

/-- `δ_t d_t ω` as a double frame sum: `∑ᵢ ∑ⱼ ι_{eⱼ} ε_{eᵢ} (Zᵢⱼ - t Hess f(eᵢ, eⱼ) ω)`, with
`Zᵢⱼ` the Hessian-free part `TauCeti.frameTerm`. -/
private theorem wittenCodifferential_wittenExtDeriv_eq_sum (b : OrthonormalBasis ι ℝ V)
    (hkl : k + 1 + l = finrank ℝ V) {ω : V → V [⋀^Fin k]→L[ℝ] ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hω : ContDiffAt ℝ 2 ω x) (t : ℝ) :
    o.wittenCodifferential hkl f t (wittenExtDeriv f t ω) x =
      ∑ i, ∑ j, curryLeftFlipL (n := k) (b j) (wedgeCovector (b i) k
        (frameTerm b f ω x t i j - (t * fderiv ℝ (fderiv ℝ f) x (b i) (b j)) • ω x)) := by
  have hS (i j : ι) : fderiv ℝ (fderiv ℝ ω) x (b j) (b i) = fderiv ℝ (fderiv ℝ ω) x (b i) (b j) :=
    (hω.isSymmSndFDerivAt (by simp)) _ _
  have hH (i j : ι) : fderiv ℝ (fderiv ℝ f) x (b j) (b i) = fderiv ℝ (fderiv ℝ f) x (b i) (b j) :=
    (hf.isSymmSndFDerivAt (by simp)) _ _
  have hdiff : wittenExtDeriv f t ω = fun y ↦ ∑ i, wedgeCovector (b i) k
      ((1 : ℝ) • fderiv ℝ ω y (b i) + (t * fderiv ℝ f y (b i)) • ω y) := by
    funext y
    simp only [wittenExtDeriv_eq_sum b, one_smul]
  rw [o.wittenCodifferential_eq_sum b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← curryLeftFlipL_apply_apply, hdiff,
    fderiv_sum_comp_smul_fderiv_add_mul_fderiv_smul_apply (fun i ↦ wedgeCovector (b i) k) b hf
      hω t 1 (b j),
    ← hdiff, wittenExtDeriv_eq_sum b, Finset.smul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hS i j, hH i j]
  simp only [frameTerm, map_add, map_sub, map_smul, map_neg]
  module

/-- **Witten's frame formula** for the Witten Laplacian `Δ_t = δ_t d_t + d_t δ_t` on forms of
intermediate degree `0 < k + 1 < n`: for `f` and a `(k + 1)`-form `ω` that are `C²` at `x`, and an
orthonormal frame `(eᵢ)`,

`Δ_t ω = -Δω + t² |∇f|² ω + t ∑_{i,j} Hess f(eᵢ, eⱼ) (ε_{eᵢ} ι_{eⱼ} - ι_{eⱼ} ε_{eᵢ}) ω`

at `x`, where `Δ` is the Laplacian of `ω` as a vector-valued function, `ε_u` is exterior
multiplication `TauCeti.wedgeCovector u` and `ι_u α = α.curryLeft u`. -/
theorem wittenCodifferential_wittenExtDeriv_add_wittenExtDeriv_wittenCodifferential
    (b : OrthonormalBasis ι ℝ V) {l' : ℕ} (hkl : k + 1 + l = finrank ℝ V)
    (hkl' : k + 1 + 1 + l' = finrank ℝ V) {ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hω : ContDiffAt ℝ 2 ω x) (t : ℝ) :
    o.wittenCodifferential hkl' f t (wittenExtDeriv f t ω) x +
        wittenExtDeriv f t (o.wittenCodifferential hkl f t ω) x =
      -Δ ω x + (t ^ 2 * ‖gradient f x‖ ^ 2) • ω x +
        t • ∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (b i) (b j) •
          (wedgeCovector (b i) k ((ω x).curryLeft (b j)) -
            (wedgeCovector (b i) (k + 1) (ω x)).curryLeft (b j)) := by
  rw [o.wittenCodifferential_wittenExtDeriv_eq_sum b hkl' hf hω,
    o.wittenExtDeriv_wittenCodifferential_eq_sum b hkl hf hω, ← Finset.sum_add_distrib,
    ← sum_frameTerm_self b f ω x t, ← b.sum_sum_inner_smul, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- The anticommutation relation turns the `Zᵢⱼ` parts into `⟪eⱼ, eᵢ⟫ Zᵢⱼ`.
  rw [← curryLeftFlipL_wedgeCovector_add (b j) (b i) k (frameTerm b f ω x t i j)]
  simp only [← curryLeftFlipL_apply_apply, map_add, map_sub, map_smul, smul_sub, smul_smul]
  abel

/-- **Witten's frame formula on functions**: for `f` and a `0`-form `ω` that are `C²` at `x`,
`δ_t d_t ω = -Δω + (t² |∇f|² - t Δf) ω` at `x`. -/
theorem wittenCodifferential_wittenExtDeriv_of_degree_zero (hkl : 0 + 1 + l = finrank ℝ V)
    {ω : V → V [⋀^Fin 0]→L[ℝ] ℝ} (hf : ContDiffAt ℝ 2 f x) (hω : ContDiffAt ℝ 2 ω x) (t : ℝ) :
    o.wittenCodifferential hkl f t (wittenExtDeriv f t ω) x =
      -Δ ω x + (t ^ 2 * ‖gradient f x‖ ^ 2 - t * Δ f x) • ω x := by
  set b := stdOrthonormalBasis ℝ V
  rw [o.wittenCodifferential_wittenExtDeriv_eq_sum b hkl hf hω,
    Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      curryLeftFlipL_wedgeCovector_zero (b j) (b i) _, b.sum_sum_inner_smul fun i j ↦
        frameTerm b f ω x t i j - (t * fderiv ℝ (fderiv ℝ f) x (b i) (b j)) • ω x,
    Finset.sum_sub_distrib, sum_frameTerm_self b f ω x t,
    laplacian_eq_sum_fderiv_fderiv_orthonormalBasis b f, Finset.mul_sum, ← Finset.sum_smul]
  module

/-- **Witten's frame formula in the top degree**: for `f` and a form `ω` of degree
`k + 1 = dim V` that are `C²` at `x`, `d_t δ_t ω = -Δω + (t² |∇f|² + t Δf) ω` at `x`. -/
theorem wittenExtDeriv_wittenCodifferential_of_eq_finrank (hkl : k + 1 + 0 = finrank ℝ V)
    {ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hf : ContDiffAt ℝ 2 f x) (hω : ContDiffAt ℝ 2 ω x)
    (t : ℝ) :
    wittenExtDeriv f t (o.wittenCodifferential hkl f t ω) x =
      -Δ ω x + (t ^ 2 * ‖gradient f x‖ ^ 2 + t * Δ f x) • ω x := by
  set b := stdOrthonormalBasis ℝ V
  rw [o.wittenExtDeriv_wittenCodifferential_eq_sum b hkl hf hω,
    Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      wedgeCovector_curryLeftFlipL_of_eq_finrank (b j) (b i) hkl _, b.sum_sum_inner_smul fun i j ↦
        frameTerm b f ω x t i j + (t * fderiv ℝ (fderiv ℝ f) x (b i) (b j)) • ω x,
    Finset.sum_add_distrib, sum_frameTerm_self b f ω x t,
    laplacian_eq_sum_fderiv_fderiv_orthonormalBasis b f, Finset.mul_sum, ← Finset.sum_smul]
  module

end FrameFormula

end Orientation
