/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Extend
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Analysis.Calculus.DerivativeTest
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
with a function of one real variable, invariance under holomorphic maps, and the vanishing of the
Levi form of the real part of a holomorphic function.

It also shows that strict positivity of the Levi form survives small `C²` perturbations. The
real part of the Levi diagonal moves by at most `‖D²g(y) - D²f(x)‖ ‖v‖² / 2` when `(f, x)` is
replaced by `(g, y)`. On a finite-dimensional space a Levi form which depends continuously on
the point and is positive definite at every point of a compact set has a uniform lower bound
`c ‖v‖²` there, and the set of continuous bilinear forms with positive definite Levi form is open.
Consequently, for `f` whose second derivative is continuous on a set `U`, strict Levi positivity
of `f` on `U` is open in the fine (Whitney) `C²` topology: it survives every perturbation whose
second derivative stays within a continuous positive tolerance `ε(x)` of that of `f`.

Finally, it gives the inertia of a Levi flat function, such as the real part of a holomorphic
function.

## Main definitions

* `TauCeti.leviForm f x`: the Levi form of `f : V → ℝ` at `x`.

## Main results

* `TauCeti.leviForm_apply_self`: the diagonal of the Levi form is one quarter of
  `Hess f(v, v) + Hess f(I • v, I • v)`.
* `TauCeti.re_leviForm_nonpos_of_isLocalMax`: at a local maximum, the Levi form is nonpositive
  on every diagonal.
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
* `TauCeti.hessianQuadraticForm_re`, `TauCeti.leviForm_re_eq_zero`: the real Hessian of the real
  part of a holomorphic function is the real part of its complex Hessian, and its Levi form
  vanishes (it is pluriharmonic).
* `TauCeti.abs_re_leviForm_apply_self_sub_le`: the Levi diagonal is Lipschitz in the second
  derivative, with constant `‖v‖² / 2`.
* `IsCompact.exists_pos_mul_sq_norm_le_re_leviForm`: a continuous family of bilinear forms whose
  Levi forms are positive definite on a compact set has a uniform lower bound `c ‖v‖²` there.
* `IsCompact.exists_pos_forall_sub_mul_sq_norm_le_re_leviForm`: for `f` with second derivative
  continuous on a compact set `K` and Levi form positive definite there, the Levi form has a
  uniform lower bound `c ‖v‖²` on `K`, which a perturbation lowers by at most half the change of
  the second derivative.
* `TauCeti.isOpen_setOf_forall_re_leviForm_toBilinForm_pos`: positive definiteness of the Levi
  form is an open condition on continuous bilinear forms.
* `TauCeti.exists_continuousOn_pos_forall_re_leviForm_pos`: strict Levi positivity is open in the
  fine `C²` topology, with a continuous positive tolerance function.
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

open Complex ComplexConjugate Filter Metric Set Topology

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

/-- At a local maximum of a real `C²` function, the Levi form is nonpositive on the diagonal. -/
theorem re_leviForm_nonpos_of_isLocalMax (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (v : V) : (leviForm f x v v).re ≤ 0 := by
  rw [re_leviForm_apply]
  exact div_nonpos_of_nonpos_of_nonneg
    (add_nonpos (fderiv_fderiv_self_nonpos_of_isLocalMax hf hmax v)
      (fderiv_fderiv_self_nonpos_of_isLocalMax hf hmax (Complex.I • v))) (by norm_num)

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
  rw [leviForm_def, leviForm_def, fderiv_fderiv_const_smul, ← LinearMap.BilinForm.leviForm_smul]
  exact congrArg _ (map_smul ContinuousLinearMap.toLinearMap₁₂ a _)

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

/-! ### The real part of a holomorphic function -/

/-- The Hessian quadratic form of the real part of a holomorphic function is the real part of its
complex Hessian. -/
theorem hessianQuadraticForm_re {g : V → ℂ} (hg : ContDiffAt ℂ 2 g x) (v : V) :
    hessianQuadraticForm (fun z ↦ (g z).re) x v = (fderiv ℂ (fderiv ℂ g) x v v).re := by
  rw [hessianQuadraticForm_apply, fderiv_fderiv_re_apply hg]

/-- **The real part of a holomorphic function is pluriharmonic**: its Levi form vanishes. -/
@[simp]
theorem leviForm_re_eq_zero {g : V → ℂ} (hg : ContDiffAt ℂ 2 g x) :
    leviForm (fun z ↦ (g z).re) x = 0 := by
  rw [leviForm_def, LinearMap.BilinForm.leviForm_eq_zero_iff]
  intro v w
  simp [fderiv_fderiv_re_apply hg]

/-! ### Perturbations of the Levi form -/

/-- The real part of the Levi diagonal of a continuous real bilinear form `B` is at most
`‖B‖ ‖v‖² / 2` in absolute value. -/
theorem _root_.ContinuousLinearMap.abs_re_leviForm_toBilinForm_apply_self_le
    (B : V →L[ℝ] V →L[ℝ] ℝ) (v : V) :
    |(B.toBilinForm.leviForm v v).re| ≤ ‖B‖ * ‖v‖ ^ 2 / 2 := by
  have hI : ‖I • v‖ = ‖v‖ := by rw [norm_smul, norm_I, one_mul]
  have h₁ := B.le_opNorm₂ v v
  have h₂ := B.le_opNorm₂ (I • v) (I • v)
  rw [hI] at h₂
  rw [Real.norm_eq_abs] at h₁ h₂
  simp only [LinearMap.BilinForm.re_leviForm_apply, ContinuousLinearMap.toBilinForm_apply]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  nlinarith [abs_add_le (B v v) (B (I • v) (I • v))]

private theorem re_leviForm_toBilinForm_apply_self_sub (B B' : V →L[ℝ] V →L[ℝ] ℝ) (v : V) :
    (B.toBilinForm.leviForm v v).re - (B'.toBilinForm.leviForm v v).re =
      ((B - B').toBilinForm.leviForm v v).re := by
  simp only [LinearMap.BilinForm.re_leviForm_apply, ContinuousLinearMap.toBilinForm_apply,
    sub_apply]
  ring

/-- A lower bound `c ‖v‖²` for the Levi diagonal of `B₀` gives the lower bound
`(c - ‖B - B₀‖ / 2) ‖v‖²` for that of `B`. -/
private theorem sub_mul_sq_norm_le_re_leviForm_toBilinForm_apply_self
    {B B₀ : V →L[ℝ] V →L[ℝ] ℝ} {c : ℝ} {v : V}
    (h : c * ‖v‖ ^ 2 ≤ (B₀.toBilinForm.leviForm v v).re) :
    (c - ‖B - B₀‖ / 2) * ‖v‖ ^ 2 ≤ (B.toBilinForm.leviForm v v).re := by
  have h₂ := (abs_le.1 (ContinuousLinearMap.abs_re_leviForm_toBilinForm_apply_self_le
    (B - B₀) v)).1
  rw [← re_leviForm_toBilinForm_apply_self_sub] at h₂
  linarith

/-- **The Levi diagonal is Lipschitz in the second derivative.** Replacing `f` at `x` by `g` at
`y` changes the real part of the Levi diagonal by at most `‖D²g(y) - D²f(x)‖ ‖v‖² / 2`. -/
theorem abs_re_leviForm_apply_self_sub_le (f g : V → ℝ) (x y v : V) :
    |(leviForm g y v v).re - (leviForm f x v v).re| ≤
      ‖fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ f) x‖ * ‖v‖ ^ 2 / 2 := by
  rw [leviForm_def, leviForm_def, re_leviForm_toBilinForm_apply_self_sub]
  exact ContinuousLinearMap.abs_re_leviForm_toBilinForm_apply_self_le _ v

/-- **Uniform Levi positivity on compact sets.** Let `B` be a family of continuous real bilinear
forms on a finite-dimensional complex space, continuous on a compact set `K`. If the Levi form of
every `B x`, `x ∈ K`, is positive definite, then it is bounded below by `c ‖v‖²` for a single
`c > 0`. -/
theorem _root_.IsCompact.exists_pos_mul_sq_norm_le_re_leviForm [FiniteDimensional ℂ V]
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {B : X → V →L[ℝ] V →L[ℝ] ℝ} (hB : ContinuousOn B K)
    (hpos : ∀ x ∈ K, ∀ v, v ≠ 0 → 0 < ((B x).toBilinForm.leviForm v v).re) :
    ∃ c > 0, ∀ x ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ ((B x).toBilinForm.leviForm v v).re := by
  have := FiniteDimensional.proper ℂ V
  set φ : X × V → ℝ := fun p ↦ ((B p.1).toBilinForm.leviForm p.2 p.2).re
  have hS : IsCompact (K ×ˢ sphere (0 : V) 1) := hK.prod (isCompact_sphere 0 1)
  have hφ : ContinuousOn φ (K ×ˢ sphere (0 : V) 1) := by
    have h₁ : ContinuousOn (fun p : X × V ↦ B p.1) (K ×ˢ sphere (0 : V) 1) :=
      hB.comp continuousOn_fst fun p hp ↦ hp.1
    simp only [φ, LinearMap.BilinForm.re_leviForm_apply, ContinuousLinearMap.toBilinForm_apply]
    refine ContinuousOn.div_const (ContinuousOn.add ?_ ?_) _
    · exact (h₁.clm_apply continuousOn_snd).clm_apply continuousOn_snd
    · exact (h₁.clm_apply (continuousOn_snd.const_smul I)).clm_apply
        (continuousOn_snd.const_smul I)
  -- The Levi diagonal is homogeneous of degree two, so a bound on unit vectors suffices.
  have hhom (c : ℝ) (x : X) (h : ∀ u ∈ sphere (0 : V) 1, c ≤ φ (x, u)) (v : V) :
      c * ‖v‖ ^ 2 ≤ ((B x).toBilinForm.leviForm v v).re := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hu : ‖v‖⁻¹ • v ∈ sphere (0 : V) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv'.ne']
    have hsmul : φ (x, ‖v‖⁻¹ • v) = (‖v‖ ^ 2)⁻¹ * ((B x).toBilinForm.leviForm v v).re := by
      simp only [φ, LinearMap.BilinForm.re_leviForm_apply, ContinuousLinearMap.toBilinForm_apply,
        map_smul, smul_apply, smul_eq_mul, smul_comm I ‖v‖⁻¹]
      ring
    have := h _ hu
    rw [hsmul, inv_mul_eq_div, le_div_iff₀ (by positivity)] at this
    linarith
  rcases (K ×ˢ sphere (0 : V) 1).eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun x hx v ↦ hhom 1 x (fun u hu ↦ ?_) v⟩
    exact absurd (hempty.subset (mk_mem_prod hx hu)) (notMem_empty _)
  obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne hφ
  exact ⟨φ p, hpos p.1 hp.1 p.2 (ne_zero_of_mem_sphere one_ne_zero ⟨p.2, hp.2⟩),
    fun x hx v ↦ hhom _ x (fun u hu ↦ hmin (mk_mem_prod hx hu)) v⟩

/-- **Continuity of the Levi lower bound under `C²` perturbations on compact sets.** Let `f` have
second derivative continuous on a compact set `K` of a finite-dimensional complex space, with
positive definite Levi form at every point of `K`. Then there is `c > 0` such that, for every
function `g`, the Levi diagonal of `g` at `x ∈ K` is at least
`(c - ‖D²g(x) - D²f(x)‖ / 2) ‖v‖²`. In particular every `g` whose second derivative stays within
`2 c` of that of `f` on `K` has positive definite Levi form on `K`. -/
theorem _root_.IsCompact.exists_pos_forall_sub_mul_sq_norm_le_re_leviForm
    [FiniteDimensional ℂ V] {K : Set V} (hK : IsCompact K) {f : V → ℝ}
    (hf : ContinuousOn (fun x ↦ fderiv ℝ (fderiv ℝ f) x) K)
    (hpos : ∀ x ∈ K, ∀ v, v ≠ 0 → 0 < (leviForm f x v v).re) :
    ∃ c > 0, ∀ g : V → ℝ, ∀ x ∈ K, ∀ v,
      (c - ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ f) x‖ / 2) * ‖v‖ ^ 2 ≤
        (leviForm g x v v).re := by
  simp only [leviForm_def] at hpos ⊢
  obtain ⟨c, hc, hle⟩ := hK.exists_pos_mul_sq_norm_le_re_leviForm hf hpos
  exact ⟨c, hc, fun g x hx v ↦ sub_mul_sq_norm_le_re_leviForm_toBilinForm_apply_self (hle x hx v)⟩

/-- **Positivity of the Levi form is an open condition.** On a finite-dimensional complex space,
the continuous real bilinear forms whose Levi form is positive definite form an open set. -/
theorem isOpen_setOf_forall_re_leviForm_toBilinForm_pos [FiniteDimensional ℂ V] :
    IsOpen {B : V →L[ℝ] V →L[ℝ] ℝ | ∀ v, v ≠ 0 → 0 < (B.toBilinForm.leviForm v v).re} := by
  refine (Metric.isOpen_iff (α := V →L[ℝ] V →L[ℝ] ℝ)).2 fun B₀ hB₀ ↦ ?_
  obtain ⟨c, hc, hle⟩ := isCompact_singleton.exists_pos_mul_sq_norm_le_re_leviForm
    continuousOn_id fun B hB ↦ by rw [mem_singleton_iff.1 hB]; exact hB₀
  refine ⟨2 * c, by positivity, fun B hB v hv ↦ ?_⟩
  have hB' : ‖B - B₀‖ < 2 * c := (dist_eq_norm B B₀).symm.trans_lt hB
  have h := sub_mul_sq_norm_le_re_leviForm_toBilinForm_apply_self (B := B) (B₀ := B₀) (hle B₀ rfl v)
  have : 0 < (c - ‖B - B₀‖ / 2) * ‖v‖ ^ 2 := mul_pos (by linarith) (by positivity)
  linarith

/-- **Strict Levi positivity is open in the fine `C²` topology.** Let `f` have second derivative
continuous on a set `U` of a finite-dimensional complex space, with positive definite Levi form at
every point of `U`. Then there is a tolerance `ε`, continuous and positive on `U`, such that the
Levi form of any function `g` is positive definite at each `x ∈ U` where
`‖D²g(x) - D²f(x)‖ < ε x`. -/
theorem exists_continuousOn_pos_forall_re_leviForm_pos [FiniteDimensional ℂ V] {U : Set V}
    {f : V → ℝ} (hf : ContinuousOn (fun x ↦ fderiv ℝ (fderiv ℝ f) x) U)
    (hpos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < (leviForm f x v v).re) :
    ∃ ε : V → ℝ, ContinuousOn ε U ∧ (∀ x ∈ U, 0 < ε x) ∧
      ∀ g : V → ℝ, ∀ x ∈ U,
        ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ f) x‖ < ε x →
          ∀ v, v ≠ 0 → 0 < (leviForm g x v v).re := by
  simp only [leviForm_def] at hpos ⊢
  set S := {B : V →L[ℝ] V →L[ℝ] ℝ | ∀ v, v ≠ 0 → 0 < (B.toBilinForm.leviForm v v).re}
  have hS : IsOpen S := isOpen_setOf_forall_re_leviForm_toBilinForm_pos
  have hmem (x : V) : x ∈ U → fderiv ℝ (fderiv ℝ f) x ∈ S := hpos x
  rcases Sᶜ.eq_empty_or_nonempty with hempty | hne
  · -- Every form has positive definite Levi form, so any tolerance works.
    refine ⟨fun _ ↦ 1, continuousOn_const, fun _ _ ↦ one_pos, fun g x _ _ ↦ ?_⟩
    have h : fderiv ℝ (fderiv ℝ g) x ∈ S := by simp [compl_empty_iff.1 hempty]
    exact h
  -- Take the distance from the second derivative of `f` to the closed complement of `S`.
  refine ⟨fun x ↦ infDist (fderiv ℝ (fderiv ℝ f) x) Sᶜ,
    (continuous_infDist_pt _).comp_continuousOn hf,
    fun x hx ↦ (hS.isClosed_compl.notMem_iff_infDist_pos hne).1 (not_not.2 (hmem x hx)),
    fun g x _ hlt ↦ ?_⟩
  have hdist : dist (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ g) x) <
      infDist (fderiv ℝ (fderiv ℝ f) x) Sᶜ :=
    (dist_comm _ _).trans_lt
      ((dist_eq_norm (fderiv ℝ (fderiv ℝ g) x) (fderiv ℝ (fderiv ℝ f) x)).trans_lt hlt)
  exact not_not.1 (notMem_of_dist_lt_infDist hdist)

/-! ### Inertia of a Levi-flat function -/

/-- **Inertia of a Levi-flat function.** If the Levi form of `f` vanishes at `x`, then
multiplication by `I` exchanges the positive and negative directions of the Hessian, so `f` and
`-f` have the same Morse index at `x`. -/
theorem morseIndex_neg_eq_of_leviForm_eq_zero (h : leviForm f x = 0) :
    morseIndex (-f) x = morseIndex f x := by
  have hB := (LinearMap.BilinForm.leviForm_eq_zero_iff _).1 ((leviForm_def f x).symm.trans h)
  rw [morseIndex_def, morseIndex_def, hessianQuadraticForm_neg, sigNeg_neg]
  refine (QuadraticForm.sigNeg_eq_sigPos_of_comp_eq_neg _
    ((LinearEquiv.smulOfNeZero ℂ V I I_ne_zero).restrictScalars ℝ) fun v ↦ ?_).symm
  simpa [hessianQuadraticForm_apply] using hB v v

/-- **The Morse index of a Levi-flat function.** If the Levi form of `f` vanishes at `x` and its
Hessian there is nondegenerate, then the Morse index of `f` at `x` is the complex dimension. This
applies to the real part of a holomorphic function, by `TauCeti.leviForm_re_eq_zero`. -/
theorem morseIndex_eq_finrank_of_leviForm_eq_zero [FiniteDimensional ℂ V]
    (h : leviForm f x = 0) (hnd : (hessianQuadraticForm f x).Nondegenerate) :
    morseIndex f x = Module.finrank ℂ V := by
  have hsum := morseIndex_neg_add_morseIndex_eq_finrank hnd
  rw [morseIndex_neg_eq_of_leviForm_eq_zero h, finrank_real_eq_two_mul_finrank_complex] at hsum
  omega

end TauCeti
