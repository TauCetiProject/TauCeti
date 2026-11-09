/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Kernel and adjoint kernel of the Cauchy–Riemann operator on the annulus with real boundary values

Let `0 < r₁ < r₂` and let `A = closedBall 0 r₂ \ ball 0 r₁` be the closed annulus, with open
interior `ball 0 r₂ \ closedBall 0 r₁` and boundary circles `sphere 0 r₁` and `sphere 0 r₂`.
This file computes the kernel and the adjoint kernel of the Cauchy–Riemann operator
`D = ∂/∂(conj z)` on the trivial line bundle `ℂ` over `A`, with the totally real boundary
condition `ℝ` on both circles. These are the two counts in the annulus example of the
Riemann–Roch theorem for bordered Riemann surfaces (McDuff–Salamon, *J-holomorphic curves and
symplectic topology*, Theorem C.1.10): there `χ(A) = 0` and `μ(ℂ, ℝ) = 0`, so the index is `0`,
with kernel and cokernel both of real dimension `1`.

* Kernel. A function `f` that is holomorphic on the open annulus, continuous on `A` and real on
  both circles is a real constant on `A`
  (`TauCeti.Complex.exists_eq_ofReal_of_im_eq_zero_on_annulus_boundary`). The maximum modulus
  principle applied to `exp (± i f)`, whose modulus is `exp (∓ im f)`, forces `im f = 0` on `A`,
  and the open mapping theorem then makes `f` constant on the connected open annulus.
* Adjoint kernel. A `(0,1)`-form `η = conj g d(conj z)` satisfies the adjoint boundary condition
  `η(∂_θ) ∈ ℝ` on both circles exactly when `i z g z` is real there, because
  `d(conj z)(∂_θ) = conj (i z)`. Applying the kernel computation to `i z g z` shows that `g`
  is a real multiple of `(i z)⁻¹` on `A`
  (`TauCeti.Complex.exists_eq_mul_inv_of_im_I_mul_eq_zero_on_annulus_boundary`).

Restricting to `A`, both spaces are real lines
(`TauCeti.Complex.finrank_annulusRealBoundaryKernel`,
`TauCeti.Complex.finrank_annulusRealBoundaryAdjointKernel`), and the difference of their
dimensions is `0 = χ(A) + μ(ℂ, ℝ)` (`TauCeti.Complex.annulusRealBoundary_index_eq_zero`).

## Main definitions

* `TauCeti.Complex.realBoundaryHolomorphic r₁ r₂`: the real subspace of functions `ℂ → ℂ`
  holomorphic on the open annulus, continuous on the closed annulus and real on both circles.
* `TauCeti.Complex.realBoundaryAdjointHolomorphic r₁ r₂`: the same, with `i z g z` real on
  both circles in place of `g`.
* `TauCeti.Complex.annulusRealBoundaryKernel r₁ r₂`,
  `TauCeti.Complex.annulusRealBoundaryAdjointKernel r₁ r₂`: their restrictions to the closed
  annulus.
-/

public section

open Complex Set Metric Module

namespace TauCeti.Complex

/-- The open annulus `ball 0 r₂ \ closedBall 0 r₁` is the set of points with norm in
`Ioo r₁ r₂`. -/
private theorem ball_diff_closedBall_eq_preimage (r₁ r₂ : ℝ) :
    ball (0 : ℂ) r₂ \ closedBall 0 r₁ = norm ⁻¹' Ioo r₁ r₂ := by
  ext z
  simp only [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le, mem_preimage,
    mem_Ioo]
  exact and_comm

/-- The closed annulus `closedBall 0 r₂ \ ball 0 r₁` is the set of points with norm in
`Icc r₁ r₂`. -/
private theorem closedBall_diff_ball_eq_preimage (r₁ r₂ : ℝ) :
    closedBall (0 : ℂ) r₂ \ ball 0 r₁ = norm ⁻¹' Icc r₁ r₂ := by
  ext z
  simp only [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_lt, mem_preimage,
    mem_Icc]
  exact and_comm

/-- Polar coordinates `(r, θ) ↦ r e^{iθ}` map `S × ℝ` onto the set of points with norm in `S`,
for any set `S` of nonnegative radii. -/
private theorem image_polar_prod_univ {S : Set ℝ} (hS : S ⊆ Ici 0) :
    (fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I)) '' (S ×ˢ univ) = norm ⁻¹' S := by
  ext z
  constructor
  · rintro ⟨⟨r, θ⟩, ⟨hr, -⟩, rfl⟩
    rw [mem_preimage, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hS hr)]
    exact hr
  · intro hz
    exact ⟨(‖z‖, arg z), ⟨hz, mem_univ _⟩, norm_mul_exp_arg_mul_I z⟩

/-- Polar coordinates are continuous. -/
private theorem continuous_polar :
    Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I) := by
  fun_prop

/-- The open annulus is connected. -/
theorem isPreconnected_ball_diff_closedBall {r₁ : ℝ} (hr₁ : 0 ≤ r₁) (r₂ : ℝ) :
    IsPreconnected (ball (0 : ℂ) r₂ \ closedBall 0 r₁) := by
  rw [ball_diff_closedBall_eq_preimage,
    ← image_polar_prod_univ (S := Ioo r₁ r₂) fun r hr => hr₁.trans hr.1.le]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _
    continuous_polar.continuousOn

/-- The closure of the open annulus is the closed annulus. -/
theorem closure_ball_diff_closedBall {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ < r₂) :
    closure (ball (0 : ℂ) r₂ \ closedBall 0 r₁) = closedBall 0 r₂ \ ball 0 r₁ := by
  rw [ball_diff_closedBall_eq_preimage, closedBall_diff_ball_eq_preimage]
  refine Subset.antisymm
    (closure_minimal (preimage_mono Ioo_subset_Icc_self)
      (isClosed_Icc.preimage continuous_norm)) ?_
  rw [← image_polar_prod_univ (S := Icc r₁ r₂) fun r hr => hr₁.trans hr.1,
    ← image_polar_prod_univ (S := Ioo r₁ r₂) fun r hr => hr₁.trans hr.1.le]
  have hcl : closure (Ioo r₁ r₂ ×ˢ (univ : Set ℝ)) = Icc r₁ r₂ ×ˢ univ := by
    rw [closure_prod_eq, closure_Ioo h.ne, closure_univ]
  rw [← hcl]
  exact image_closure_subset_closure_image continuous_polar

/-- The frontier of the open annulus lies on the two boundary circles. -/
theorem frontier_ball_diff_closedBall_subset {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ < r₂) :
    frontier (ball (0 : ℂ) r₂ \ closedBall 0 r₁) ⊆ sphere 0 r₁ ∪ sphere 0 r₂ := by
  rw [(isOpen_ball.sdiff isClosed_closedBall).frontier_eq, closure_ball_diff_closedBall hr₁ h]
  intro z hz
  simp only [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_lt, not_and, not_le]
    at hz
  simp only [mem_union, mem_sphere_zero_iff_norm]
  rcases hz.1.1.lt_or_eq with h₂ | h₂
  · exact Or.inl (le_antisymm (hz.2 h₂) hz.1.2)
  · exact Or.inr h₂

/-- If `f` is holomorphic on the open annulus, continuous on the closed annulus and real on both
boundary circles, then its imaginary part is nonnegative on the closed annulus. This is the
maximum modulus principle for `exp (i f)`, whose modulus is `exp (-im f)`. -/
private theorem im_nonneg_of_im_eq_zero_on_annulus_boundary {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (h : r₁ < r₂) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 r₂ \ closedBall 0 r₁))
    (hfc : ContinuousOn f (closedBall 0 r₂ \ ball 0 r₁))
    (hbd : ∀ z ∈ sphere (0 : ℂ) r₁ ∪ sphere 0 r₂, (f z).im = 0) {z : ℂ}
    (hz : z ∈ closedBall 0 r₂ \ ball 0 r₁) : 0 ≤ (f z).im := by
  have hnorm : ∀ w, ‖exp (I * f w)‖ = Real.exp (-(f w).im) := fun w => by
    rw [norm_exp, mul_re, I_re, I_im]
    ring_nf
  have hd : DiffContOnCl ℂ (fun w => exp (I * f w)) (ball 0 r₂ \ closedBall 0 r₁) := by
    refine ⟨(hf.const_mul I).cexp, ?_⟩
    rw [closure_ball_diff_closedBall hr₁ h]
    exact (hfc.const_mul I).cexp
  have hle := Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball.subset sdiff_subset) hd (C := 1)
    (fun w hw => by
      rw [hnorm, hbd w (frontier_ball_diff_closedBall_subset hr₁ h hw), neg_zero, Real.exp_zero])
    (by rwa [closure_ball_diff_closedBall hr₁ h])
  rw [hnorm, Real.exp_le_one_iff] at hle
  linarith

/-- **Kernel of the Cauchy–Riemann operator on the annulus with real boundary values.** If `f`
is holomorphic on the open annulus `ball 0 r₂ \ closedBall 0 r₁`, continuous on the closed
annulus and real on both boundary circles, then `f` is a real constant on the closed annulus. -/
theorem exists_eq_ofReal_of_im_eq_zero_on_annulus_boundary {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (h : r₁ < r₂) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 r₂ \ closedBall 0 r₁))
    (hfc : ContinuousOn f (closedBall 0 r₂ \ ball 0 r₁))
    (hbd : ∀ z ∈ sphere (0 : ℂ) r₁ ∪ sphere 0 r₂, (f z).im = 0) :
    ∃ c : ℝ, ∀ z ∈ closedBall (0 : ℂ) r₂ \ ball 0 r₁, f z = c := by
  have hUA : ball (0 : ℂ) r₂ \ closedBall 0 r₁ ⊆ closedBall 0 r₂ \ ball 0 r₁ := by
    rw [← closure_ball_diff_closedBall hr₁ h]
    exact subset_closure
  -- the imaginary part vanishes on the closed annulus
  have him : ∀ z ∈ closedBall (0 : ℂ) r₂ \ ball 0 r₁, (f z).im = 0 := fun z hz =>
    le_antisymm
      (by
        have := im_nonneg_of_im_eq_zero_on_annulus_boundary hr₁ h hf.neg hfc.neg
          (fun w hw => by rw [Pi.neg_apply, neg_im, hbd w hw, neg_zero]) hz
        rw [Pi.neg_apply, neg_im] at this
        linarith)
      (im_nonneg_of_im_eq_zero_on_annulus_boundary hr₁ h hf hfc hbd hz)
  -- a point of the open annulus
  have hz₀ : (((r₁ + r₂) / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) r₂ \ closedBall 0 r₁ := by
    rw [ball_diff_closedBall_eq_preimage, mem_preimage, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith), mem_Ioo]
    constructor <;> linarith
  -- open mapping: `f` is constant on `U`
  obtain ⟨w, hw⟩ : ∃ w, ∀ z ∈ ball (0 : ℂ) r₂ \ closedBall 0 r₁, f z = w := by
    rcases (hf.analyticOnNhd (isOpen_ball.sdiff isClosed_closedBall)).is_constant_or_isOpen
      (isPreconnected_ball_diff_closedBall hr₁ r₂) with hc | ho
    · exact hc
    exfalso
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (ho _ Subset.rfl
      (isOpen_ball.sdiff isClosed_closedBall)) _ (mem_image_of_mem f hz₀)
    obtain ⟨z, hz, hfz⟩ := hball (show f _ + (ε / 2 : ℝ) * I ∈ ball (f _) ε by
      rw [mem_ball, dist_eq, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      exact half_lt_self hε)
    have := congrArg Complex.im hfz
    rw [him z (hUA hz), add_im, him _ (hUA hz₀), im_ofReal_mul, I_im, mul_one] at this
    linarith [half_pos hε]
  have hweq : EqOn f (fun _ => w) (closedBall 0 r₂ \ ball 0 r₁) :=
    EqOn.of_subset_closure hw hfc continuousOn_const hUA
      (closure_ball_diff_closedBall hr₁ h).ge
  refine ⟨w.re, fun z hz => ?_⟩
  rw [hweq hz]
  refine Complex.ext (by simp) ?_
  rw [ofReal_im, ← hw _ hz₀, him _ (hUA hz₀)]

/-- **Adjoint kernel of the Cauchy–Riemann operator on the annulus with real boundary
values.** If `g` is holomorphic on the open annulus, continuous on the closed annulus, and
`i z g z` is real on both boundary circles (the adjoint boundary condition for
`η = conj g d(conj z)`), then `g` is a real multiple of `(i z)⁻¹` on the closed annulus. -/
theorem exists_eq_mul_inv_of_im_I_mul_eq_zero_on_annulus_boundary {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (h : r₁ < r₂) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 r₂ \ closedBall 0 r₁))
    (hgc : ContinuousOn g (closedBall 0 r₂ \ ball 0 r₁))
    (hbd : ∀ z ∈ sphere (0 : ℂ) r₁ ∪ sphere 0 r₂, (I * z * g z).im = 0) :
    ∃ c : ℝ, ∀ z ∈ closedBall (0 : ℂ) r₂ \ ball 0 r₁, g z = c * (I * z)⁻¹ := by
  obtain ⟨c, hc⟩ := exists_eq_ofReal_of_im_eq_zero_on_annulus_boundary (f := fun z => I * z * g z)
    hr₁.le h ((differentiableOn_id.const_mul I).mul hg) ((continuousOn_id.const_mul I).mul hgc) hbd
  refine ⟨c, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [mem_sdiff, mem_ball_zero_iff, norm_zero] at hz
    exact hz.2 hr₁
  rw [eq_mul_inv_iff_mul_eq₀ (mul_ne_zero I_ne_zero hz0), ← hc z hz]
  ring

/-- The real subspace of functions `ℂ → ℂ` that are holomorphic on the open annulus
`ball 0 r₂ \ closedBall 0 r₁`, continuous on the closed annulus, and real on both boundary
circles: before restriction to the annulus, the kernel of `∂/∂(conj z)` with the totally real
boundary condition `ℝ`. -/
noncomputable def realBoundaryHolomorphic (r₁ r₂ : ℝ) : Submodule ℝ (ℂ → ℂ) where
  carrier := {f | DifferentiableOn ℂ f (ball 0 r₂ \ closedBall 0 r₁) ∧
    ContinuousOn f (closedBall 0 r₂ \ ball 0 r₁) ∧
    ∀ z ∈ sphere (0 : ℂ) r₁ ∪ sphere 0 r₂, (f z).im = 0}
  zero_mem' := ⟨differentiableOn_const 0, continuousOn_const, fun _ _ => zero_im⟩
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, fun z hz => by
    rw [Pi.add_apply, add_im, hf.2.2 z hz, hg.2.2 z hz, add_zero]⟩
  smul_mem' := fun c f hf => by
    have hsmul : c • f = fun z => (c : ℂ) * f z := funext fun z => by
      rw [Pi.smul_apply, real_smul]
    rw [hsmul]
    exact ⟨hf.1.const_mul _, hf.2.1.const_mul _, fun z hz => by
      rw [im_ofReal_mul, hf.2.2 z hz, mul_zero]⟩

/-- Membership in `realBoundaryHolomorphic` unfolds to its three defining conditions. -/
theorem mem_realBoundaryHolomorphic {r₁ r₂ : ℝ} {f : ℂ → ℂ} :
    f ∈ realBoundaryHolomorphic r₁ r₂ ↔
      DifferentiableOn ℂ f (ball 0 r₂ \ closedBall 0 r₁) ∧
        ContinuousOn f (closedBall 0 r₂ \ ball 0 r₁) ∧
          ∀ z ∈ sphere (0 : ℂ) r₁ ∪ sphere 0 r₂, (f z).im = 0 :=
  Iff.rfl

/-- The real subspace of functions `g : ℂ → ℂ` that are holomorphic on the open annulus,
continuous on the closed annulus, and satisfy the adjoint boundary condition that `i z g z` is
real on both boundary circles: before restriction to the annulus, the kernel of the formal
adjoint of `∂/∂(conj z)`, through `η = conj g d(conj z)`. -/
noncomputable def realBoundaryAdjointHolomorphic (r₁ r₂ : ℝ) : Submodule ℝ (ℂ → ℂ) where
  carrier := {g | DifferentiableOn ℂ g (ball 0 r₂ \ closedBall 0 r₁) ∧
    ContinuousOn g (closedBall 0 r₂ \ ball 0 r₁) ∧
    ∀ z ∈ sphere (0 : ℂ) r₁ ∪ sphere 0 r₂, (I * z * g z).im = 0}
  zero_mem' := ⟨differentiableOn_const 0, continuousOn_const, fun _ _ => by
    rw [Pi.zero_apply, mul_zero, zero_im]⟩
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, fun z hz => by
    rw [Pi.add_apply, mul_add, add_im, hf.2.2 z hz, hg.2.2 z hz, add_zero]⟩
  smul_mem' := fun c f hf => by
    have hsmul : c • f = fun z => (c : ℂ) * f z := funext fun z => by
      rw [Pi.smul_apply, real_smul]
    rw [hsmul]
    exact ⟨hf.1.const_mul _, hf.2.1.const_mul _, fun z hz => by
      rw [mul_left_comm, im_ofReal_mul, hf.2.2 z hz, mul_zero]⟩

/-- Membership in `realBoundaryAdjointHolomorphic` unfolds to its three defining conditions. -/
theorem mem_realBoundaryAdjointHolomorphic {r₁ r₂ : ℝ} {g : ℂ → ℂ} :
    g ∈ realBoundaryAdjointHolomorphic r₁ r₂ ↔
      DifferentiableOn ℂ g (ball 0 r₂ \ closedBall 0 r₁) ∧
        ContinuousOn g (closedBall 0 r₂ \ ball 0 r₁) ∧
          ∀ z ∈ sphere (0 : ℂ) r₁ ∪ sphere 0 r₂, (I * z * g z).im = 0 :=
  Iff.rfl

/-- The kernel of the Cauchy–Riemann operator `∂/∂(conj z)` on the closed annulus with real
boundary values on both circles: the restrictions to `closedBall 0 r₂ \ ball 0 r₁` of
`realBoundaryHolomorphic r₁ r₂`. -/
noncomputable def annulusRealBoundaryKernel (r₁ r₂ : ℝ) :
    Submodule ℝ (↥(closedBall (0 : ℂ) r₂ \ ball 0 r₁) → ℂ) :=
  (realBoundaryHolomorphic r₁ r₂).map (LinearMap.funLeft ℝ ℂ Subtype.val)

/-- The kernel of the formal adjoint of the Cauchy–Riemann operator `∂/∂(conj z)` on the closed
annulus with real boundary values on both circles: the restrictions to
`closedBall 0 r₂ \ ball 0 r₁` of `realBoundaryAdjointHolomorphic r₁ r₂`. -/
noncomputable def annulusRealBoundaryAdjointKernel (r₁ r₂ : ℝ) :
    Submodule ℝ (↥(closedBall (0 : ℂ) r₂ \ ball 0 r₁) → ℂ) :=
  (realBoundaryAdjointHolomorphic r₁ r₂).map (LinearMap.funLeft ℝ ℂ Subtype.val)

/-- The annulus kernel with real boundary values is the line of real constants. -/
theorem annulusRealBoundaryKernel_eq_span {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ < r₂) :
    annulusRealBoundaryKernel r₁ r₂ = ℝ ∙ fun _ => 1 := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨f, ⟨hf, hfc, hbd⟩, rfl⟩
    obtain ⟨c, hc⟩ := exists_eq_ofReal_of_im_eq_zero_on_annulus_boundary hr₁ h hf hfc hbd
    refine Submodule.mem_span_singleton.2 ⟨c, funext fun z => ?_⟩
    rw [Pi.smul_apply, real_smul, mul_one, LinearMap.funLeft_apply, hc z z.2]
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 ⟨fun _ => 1, ?_, rfl⟩
    exact ⟨differentiableOn_const 1, continuousOn_const, fun _ _ => one_im⟩

/-- The annulus adjoint kernel with real boundary values is the real line spanned by
`z ↦ (i z)⁻¹`. -/
theorem annulusRealBoundaryAdjointKernel_eq_span {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h : r₁ < r₂) :
    annulusRealBoundaryAdjointKernel r₁ r₂ =
      ℝ ∙ fun z : ↥(closedBall (0 : ℂ) r₂ \ ball 0 r₁) => (I * z)⁻¹ := by
  have hne : ∀ z ∈ closedBall (0 : ℂ) r₂ \ ball 0 r₁, z ≠ 0 := by
    rintro z hz rfl
    simp only [mem_sdiff, mem_ball_zero_iff, norm_zero] at hz
    exact hz.2 hr₁
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, ⟨hg, hgc, hbd⟩, rfl⟩
    obtain ⟨c, hc⟩ := exists_eq_mul_inv_of_im_I_mul_eq_zero_on_annulus_boundary hr₁ h hg hgc hbd
    refine Submodule.mem_span_singleton.2 ⟨c, funext fun z => ?_⟩
    rw [Pi.smul_apply, real_smul, LinearMap.funLeft_apply, hc z z.2]
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 ⟨fun z => (I * z)⁻¹, ?_, rfl⟩
    have hU : ∀ z ∈ ball (0 : ℂ) r₂ \ closedBall 0 r₁, I * z ≠ 0 := fun z hz =>
      mul_ne_zero I_ne_zero (hne z (by
        rw [← closure_ball_diff_closedBall hr₁.le h]
        exact subset_closure hz))
    refine ⟨(differentiableOn_id.const_mul I).inv hU,
      (continuousOn_id.const_mul I).inv₀ fun z hz => mul_ne_zero I_ne_zero (hne z hz),
      fun z hz => ?_⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      rcases hz with hz | hz <;>
        simp only [mem_sphere_zero_iff_norm, norm_zero] at hz <;> linarith
    rw [mul_inv_cancel₀ (mul_ne_zero I_ne_zero hz0), one_im]

/-- The annulus kernel with real boundary values has real dimension `1`. -/
theorem finrank_annulusRealBoundaryKernel {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ < r₂) :
    finrank ℝ (annulusRealBoundaryKernel r₁ r₂) = 1 := by
  rw [annulusRealBoundaryKernel_eq_span hr₁ h]
  refine finrank_span_singleton fun h0 => ?_
  have hz : (r₁ : ℂ) ∈ closedBall (0 : ℂ) r₂ \ ball 0 r₁ := by
    rw [closedBall_diff_ball_eq_preimage, mem_preimage, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr₁]
    exact ⟨le_rfl, h.le⟩
  simpa using congrFun h0 ⟨_, hz⟩

/-- The annulus adjoint kernel with real boundary values has real dimension `1`. -/
theorem finrank_annulusRealBoundaryAdjointKernel {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h : r₁ < r₂) :
    finrank ℝ (annulusRealBoundaryAdjointKernel r₁ r₂) = 1 := by
  rw [annulusRealBoundaryAdjointKernel_eq_span hr₁ h]
  refine finrank_span_singleton fun h0 => ?_
  have hz : (r₁ : ℂ) ∈ closedBall (0 : ℂ) r₂ \ ball 0 r₁ := by
    rw [closedBall_diff_ball_eq_preimage, mem_preimage, norm_real, Real.norm_eq_abs,
      abs_of_pos hr₁]
    exact ⟨le_rfl, h.le⟩
  have := congrFun h0 ⟨_, hz⟩
  simp only [Pi.zero_apply, inv_eq_zero, mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
    at this
  exact hr₁.ne' this

/-- The index of the Cauchy–Riemann operator on the annulus with real boundary values on both
circles is `0`, the value `χ + μ = 0 + 0` predicted by Riemann–Roch: kernel and adjoint kernel
are both real lines. -/
theorem annulusRealBoundary_index_eq_zero {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h : r₁ < r₂) :
    (finrank ℝ (annulusRealBoundaryKernel r₁ r₂) : ℤ) -
      finrank ℝ (annulusRealBoundaryAdjointKernel r₁ r₂) = 0 := by
  rw [finrank_annulusRealBoundaryKernel hr₁.le h, finrank_annulusRealBoundaryAdjointKernel hr₁ h,
    sub_self]

end TauCeti.Complex
