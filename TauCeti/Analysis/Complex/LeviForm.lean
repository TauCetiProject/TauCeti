/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Extend
public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.Calculus.SecondDerivative
public import TauCeti.LinearAlgebra.Complex.Finrank
public import TauCeti.LinearAlgebra.Complex.LeviForm

/-!
# The Levi form of a real function on a complex vector space

For a real-valued function `f` on a complex normed space `V`, the **Levi form** of `f` at `x` is
the Levi form `LinearMap.BilinForm.leviForm` of its real second derivative `D²f(x)`:
the sesquilinear form `leviForm f x` whose real and imaginary parts are

`Re (leviForm f x v w) = (D²f(x)(v, w) + D²f(x)(I • v, I • w)) / 4`,
`Im (leviForm f x v w) = (D²f(x)(I • v, w) - D²f(x)(v, I • w)) / 4`.

In holomorphic coordinates `z_j = x_j + I y_j` with coordinate vectors `e_j`, its matrix entries
are the Wirtinger second derivatives, with the arguments reversed: for `C²` `f`,
`leviForm f x (e_k) (e_j) = ∂²f / ∂z_j ∂(conj z_k)`. For `C²` `f` its diagonal value
`leviForm f x v v` is the real number `(D²f(x)(v, v) + D²f(x)(I • v, I • v)) / 4`. Unlike the
real Hessian, which is intrinsic only at critical points, the Levi form transforms as a Hermitian
form under holomorphic changes of variables at every point. Positive definiteness of the Levi form
is strict plurisubharmonicity.

This file gives the calculus of the Levi form: its value on the diagonal in terms of the Hessian
quadratic form, Hermitian symmetry, the sum rule, the product rule, the rule for post-composition
with a function of one real variable, and invariance under holomorphic maps. It also gives the
inertia of a Levi flat function, such as the real part of a holomorphic function.

## Main definitions

* `TauCeti.leviForm f x`: the Levi form of `f : V → ℝ` at `x`.

## Main results

* `TauCeti.leviForm_apply_self`: the diagonal of the Levi form is one quarter of
  `Hess f(v, v) + Hess f(I • v, I • v)`.
* `TauCeti.isSymm_leviForm`: the Levi form of a `C²` function is Hermitian.
* `TauCeti.leviForm_add`, `TauCeti.leviForm_neg`, `TauCeti.leviForm_smul`: the Levi form is
  real linear in the function.
* `TauCeti.leviForm_mul_apply`: the product rule
  `L(f g) = f L g + g L f + (conj (∂f) ⊗ ∂g + conj (∂g) ⊗ ∂f)`.
* `TauCeti.leviForm_scalar_comp_apply`: the composition rule
  `L(φ ∘ f) = φ'(f) L f + φ''(f) conj (∂f) ⊗ ∂f`, and
  `TauCeti.le_re_leviForm_scalar_comp_apply_self`: where `φ'' ≥ 0`, the diagonal of `L(φ ∘ f)`
  dominates `φ'(f)` times the diagonal of `L f`.
* `TauCeti.leviForm_comp_apply`: invariance under holomorphic maps,
  `L(f ∘ g)(v, w) = L f(Dg v, Dg w)`; in particular the Levi form transforms as a Hermitian form
  under holomorphic changes of coordinates.
* `ContDiffAt.leviForm_re_eq_zero`: the real part of a holomorphic function has vanishing Levi
  form.
* `TauCeti.morseIndex_neg_eq_of_leviForm_eq_zero`,
  `TauCeti.morseIndex_eq_finrank_of_leviForm_eq_zero`: if the Levi form vanishes, then
  multiplication by `I` exchanges the positive and negative directions of the Hessian, so a
  nondegenerate Hessian has Morse index the complex dimension.

Here `∂f = (Df(x)(·) - I * Df(x)(I • ·)) / 2` is the complex-linear part of the real
differential. The statements use the complex-linear extension
`StrongDual.extendRCLike (Df(x)) = 2 ∂f`, which accounts for their factor `1/4`.

## References

* R. Hain, *Notes on the Morse theory of complex manifolds*.
* L. Hörmander, *An introduction to complex analysis in several variables*, Chapter II.
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
-/

public section

open Complex ComplexConjugate Filter Topology

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {f g : V → ℝ} {x : V}

/-- The **Levi form** of a real function `f` at `x`: the sesquilinear form
`(D²f(x)(v, w) + D²f(x)(I • v, I • w) + I * (D²f(x)(I • v, w) - D²f(x)(v, I • w))) / 4`,
conjugate-linear in `v` and complex-linear in `w`. Its matrix entries in holomorphic coordinates
are the Wirtinger derivatives, with the arguments reversed: for `C²` `f` and coordinate vectors
`e_j`, `leviForm f x (e_k) (e_j) = ∂²f / ∂z_j ∂(conj z_k)`. -/
noncomputable def leviForm (f : V → ℝ) (x : V) : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
  (fderiv ℝ (fderiv ℝ f) x).toBilinForm.leviForm

theorem leviForm_def (f : V → ℝ) (x : V) :
    leviForm f x = (fderiv ℝ (fderiv ℝ f) x).toBilinForm.leviForm :=
  (rfl)

/-- The real part of the Levi form. -/
@[simp]
theorem re_leviForm_apply (f : V → ℝ) (x v w : V) :
    (leviForm f x v w).re =
      (fderiv ℝ (fderiv ℝ f) x v w + fderiv ℝ (fderiv ℝ f) x (I • v) (I • w)) / 4 := by
  simp [leviForm_def]

/-- The imaginary part of the Levi form. -/
@[simp]
theorem im_leviForm_apply (f : V → ℝ) (x v w : V) :
    (leviForm f x v w).im =
      (fderiv ℝ (fderiv ℝ f) x (I • v) w - fderiv ℝ (fderiv ℝ f) x v (I • w)) / 4 := by
  simp [leviForm_def]

/-- **The diagonal of the Levi form.** For a `C²` function, `leviForm f x v v` is the real number
`(Hess f(v, v) + Hess f(I • v, I • v)) / 4`. -/
theorem leviForm_apply_self (hf : ContDiffAt ℝ 2 f x) (v : V) :
    leviForm f x v v =
      ((hessianQuadraticForm f x v + hessianQuadraticForm f x (I • v)) / 4 : ℝ) := by
  have hB : (fderiv ℝ (fderiv ℝ f) x).toBilinForm.IsSymm := ⟨hf.isSymmSndFDerivAt (by simp)⟩
  rw [leviForm_def, LinearMap.BilinForm.leviForm_apply_self hB]
  simp

/-- The Levi form of a `C²` function is Hermitian. -/
theorem isSymm_leviForm (hf : ContDiffAt ℝ 2 f x) : (leviForm f x).IsSymm := by
  have hB : (fderiv ℝ (fderiv ℝ f) x).toBilinForm.IsSymm := ⟨hf.isSymmSndFDerivAt (by simp)⟩
  exact LinearMap.BilinForm.isSymm_leviForm hB

/-- The Levi form depends only on the germ of the function at the point. -/
theorem leviForm_congr_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) : leviForm f x = leviForm g x := by
  rw [leviForm_def, leviForm_def, hfg.fderiv.fderiv_eq]

/-- **The sum rule.** -/
theorem leviForm_add (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    leviForm (f + g) x = leviForm f x + leviForm g x := by
  have h2 (v w : V) : fderiv ℝ (fderiv ℝ (f + g)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w + fderiv ℝ (fderiv ℝ g) x v w := by
    simpa [iteratedFDeriv_two_apply] using
      congr($(iteratedFDeriv_add_apply (i := 2) hf hg) ![v, w])
  ext v w
  apply Complex.ext <;> simp [h2] <;> ring

/-- Negating a function negates its Levi form. -/
@[simp]
theorem leviForm_neg (f : V → ℝ) (x : V) : leviForm (-f) x = -leviForm f x := by
  have hfd : fderiv ℝ (-f) = -fderiv ℝ f := funext fun _ ↦ fderiv_neg
  have h2 : fderiv ℝ (fderiv ℝ (-f)) x = -fderiv ℝ (fderiv ℝ f) x := by
    rw [hfd, fderiv_neg]
  ext v w
  apply Complex.ext <;> simp [h2] <;> ring

/-- The Levi form is real homogeneous in the function. -/
@[simp]
theorem leviForm_smul (a : ℝ) (f : V → ℝ) (x : V) :
    leviForm (a • f) x = (a : ℂ) • leviForm f x := by
  have h2 : fderiv ℝ (fderiv ℝ (a • f)) x = a • fderiv ℝ (fderiv ℝ f) x := by
    rw [fderiv_const_smul_field, fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ f),
      Pi.smul_apply]
  ext v w
  apply Complex.ext <;> simp [h2] <;> ring

/-- **The product rule** for the Levi form. Writing `∂f` for the complex-linear extension
`StrongDual.extendRCLike` of the real differential `Df(x)`, the Levi form of `f g` at `x` is
`f(x) L g + g(x) L f + (conj (∂f v) ∂g w + conj (∂g v) ∂f w) / 4`. -/
theorem leviForm_mul_apply (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : V) :
    leviForm (f * g) x v w =
      f x * leviForm g x v w + g x * leviForm f x v w +
        (4 : ℂ)⁻¹ * (conj (StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ f x) v) *
            StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ g x) w +
          conj (StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ g x) v) *
            StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ f x) w) := by
  apply Complex.ext <;>
  simp [fderiv_fderiv_mul_apply hf hg, StrongDual.extendRCLike_apply] <;> ring

/-- **The composition rule** for post-composition with a function of one real variable. Writing
`∂f` for the complex-linear extension `StrongDual.extendRCLike` of `Df(x)`, the Levi form of
`φ ∘ f` at `x` is `φ'(f x) L f + φ''(f x) conj (∂f v) ∂f w / 4`. -/
theorem leviForm_scalar_comp_apply {φ : ℝ → ℝ} (hφ : ContDiffAt ℝ 2 φ (f x))
    (hf : ContDiffAt ℝ 2 f x) (v w : V) :
    leviForm (φ ∘ f) x v w =
      deriv φ (f x) * leviForm f x v w +
        iteratedDeriv 2 φ (f x) * ((4 : ℂ)⁻¹ *
          (conj (StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ f x) v) *
            StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ f x) w)) := by
  apply Complex.ext <;>
  simp [fderiv_fderiv_scalar_comp_apply hφ hf, StrongDual.extendRCLike_apply] <;> ring

/-- **Post-composition with a convex function.** If `φ'' ≥ 0` at `f x`, then the diagonal of the
Levi form of `φ ∘ f` dominates `φ'(f x)` times the diagonal of the Levi form of `f`. In particular,
if moreover `φ'(f x) > 0`, post-composition with `φ` preserves strict positivity of the Levi
form at `x`. -/
theorem le_re_leviForm_scalar_comp_apply_self {φ : ℝ → ℝ} (hφ : ContDiffAt ℝ 2 φ (f x))
    (hf : ContDiffAt ℝ 2 f x) (hφ₂ : 0 ≤ iteratedDeriv 2 φ (f x)) (v : V) :
    deriv φ (f x) * (leviForm f x v v).re ≤ (leviForm (φ ∘ f) x v v).re := by
  simp only [re_leviForm_apply, fderiv_fderiv_scalar_comp_apply hφ hf, smul_eq_mul]
  nlinarith [mul_nonneg hφ₂ (add_nonneg (sq_nonneg (fderiv ℝ f x v))
    (sq_nonneg (fderiv ℝ f x (I • v))))]

/-- **Invariance under holomorphic maps.** If `g : W → V` is complex `C²` at `b` and `f` is real
`C²` at `g b`, then the Levi form of `f ∘ g` at `b` is the Levi form of `f` at `g b` evaluated on
the images under the complex derivative of `g`. The second derivative of `g` contributes to the
real Hessian of `f ∘ g` but not to its Levi form, because it is complex bilinear. -/
theorem leviForm_comp_apply {g : W → V} {b : W} (hf : ContDiffAt ℝ 2 f (g b))
    (hg : ContDiffAt ℂ 2 g b) (v w : W) :
    leviForm (f ∘ g) b v w = leviForm f (g b) (fderiv ℂ g b v) (fderiv ℂ g b w) := by
  have h1 (u : W) : fderiv ℝ g b u = fderiv ℂ g b u := by
    rw [(hg.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
    rfl
  have h2 (u u' : W) : fderiv ℝ (fderiv ℝ g) b u u' = fderiv ℂ (fderiv ℂ g) b u u' :=
    hg.fderiv_fderiv_restrictScalars_apply u u'
  apply Complex.ext <;>
  simp [fderiv_fderiv_comp_apply hf (hg.restrict_scalars ℝ), h1, h2, smul_smul]
  ring

end TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℝ} {x : V}

/-- **The real part of a holomorphic function is Levi flat.** If `g` is complex `C²` at `x`, then
the Levi form of `Re g` vanishes at `x`. -/
theorem ContDiffAt.leviForm_re_eq_zero {g : V → ℂ} (hg : ContDiffAt ℂ 2 g x) :
    TauCeti.leviForm (fun z ↦ (g z).re) x = 0 := by
  -- `Re` is real linear, so its second derivative and hence its Levi form vanish everywhere.
  have hre (y : ℂ) : TauCeti.leviForm Complex.re y = 0 := by
    have h : fderiv ℝ Complex.re = fun _ ↦ reCLM := funext fun _ ↦ reCLM.fderiv
    refine LinearMap.ext fun v ↦ LinearMap.ext fun w ↦ ?_
    apply Complex.ext <;> simp [h]
  refine LinearMap.ext fun v ↦ LinearMap.ext fun w ↦ ?_
  have h := TauCeti.leviForm_comp_apply (f := Complex.re) reCLM.contDiff.contDiffAt hg v w
  rw [hre] at h
  exact h

namespace TauCeti

/-- **Inertia of a Levi-flat function.** If the Levi form of `f` vanishes at `x`, then
multiplication by `I` exchanges the positive and negative directions of the Hessian, so `f` and
`-f` have the same Morse index at `x`. -/
theorem morseIndex_neg_eq_of_leviForm_eq_zero (h : leviForm f x = 0) :
    morseIndex (-f) x = morseIndex f x := by
  have hB := (LinearMap.BilinForm.leviForm_eq_zero_iff _).1 ((leviForm_def f x).symm.trans h)
  have hI (v : V) : hessianQuadraticForm f x (I • v) = -hessianQuadraticForm f x v := by
    simpa [hessianQuadraticForm_apply] using hB v v
  let e : V ≃ₗ[ℝ] V := (LinearEquiv.smulOfNeZero ℂ V I I_ne_zero).restrictScalars ℝ
  have hcomp : (hessianQuadraticForm f x).comp (e : V →ₗ[ℝ] V) =
      hessianQuadraticForm (-f) x := by
    ext v
    simp [e, hessianQuadraticForm_neg, hI]
  rw [morseIndex_def, morseIndex_def, ← hcomp]
  exact (QuadraticMap.Equivalent.sigNeg_eq
    ⟨(hessianQuadraticForm f x).isometryEquivOfCompLinearEquiv e⟩).symm

/-- **The Morse index of a Levi-flat function.** If the Levi form of `f` vanishes at `x` and its
Hessian there is nondegenerate, then the Morse index of `f` at `x` is the complex dimension. This
applies to the real part of a holomorphic function, by `ContDiffAt.leviForm_re_eq_zero`. -/
theorem morseIndex_eq_finrank_of_leviForm_eq_zero [FiniteDimensional ℂ V]
    (h : leviForm f x = 0) (hnd : (hessianQuadraticForm f x).Nondegenerate) :
    morseIndex f x = Module.finrank ℂ V := by
  have hsum := morseIndex_neg_add_morseIndex_eq_finrank hnd
  rw [morseIndex_neg_eq_of_leviForm_eq_zero h, finrank_real_eq_two_mul_finrank_complex] at hsum
  omega

end TauCeti
