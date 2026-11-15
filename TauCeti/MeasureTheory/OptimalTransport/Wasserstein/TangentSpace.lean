/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Calculus.Gradient
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# The tangent space of the Wasserstein space

Let `E` be a finite-dimensional real inner product space and `μ` a measure on `E`. The *tangent
space* of the quadratic Wasserstein space at `μ` is the closure in `L²(μ; E)` of the gradients
`∇φ` of smooth compactly supported functions `φ : E → ℝ`,

`Tan_μ P₂(E) = closure {∇φ | φ ∈ C_c^∞(E)}`.

It is the space of velocity fields of the continuity equation `∂ₜ μₜ + div (vₜ μₜ) = 0` that
are relevant to Wasserstein geometry. A field `v ∈ L²(μ; E)` enters the continuity equation
only through its divergence `div (v μ)`, the distribution `φ ↦ -∫ ⟨∇φ, v⟩ dμ`, so two fields
with the same divergence move `μ` in the same way. The orthogonal complement of the tangent
space consists exactly of the fields with `div (w μ) = 0`, that is
`∫ ⟨∇φ, w⟩ dμ = 0` for every test function `φ`. Hence the orthogonal projection onto the
tangent space keeps the divergence of a field, and among all fields with the divergence of `v`
the projection of `v` is the unique one of least `L²(μ)` norm. A field lies in the tangent space
exactly when adding a divergence-free field never decreases its norm. These are the facts behind
the minimal-velocity representation of an absolutely continuous curve of measures, and behind
the Wasserstein subdifferential calculus built on it.

Following the convention of the continuity equation, the pairing `⟨∇φ (x), w (x)⟩` is written as
the Fréchet derivative `fderiv ℝ φ x (w x)`. As for the continuity equation, `E` is
finite-dimensional: in infinite dimensions every compactly supported continuous function
vanishes, and the tangent space is built from cylindrical functions instead, which is not done
here. No moment condition on `μ` is needed for the definition, only finiteness on compact sets
for gradients of test functions to be square integrable.

## Main definitions

* `TauCeti.wassersteinTangentSpace μ`: the tangent space `Tan_μ P₂(E)`, a closed subspace of
  `L²(μ; E)`.

## Main results

* `TauCeti.toLp_gradient_mem_wassersteinTangentSpace`: the gradient of a test function is
  tangent.
* `TauCeti.wassersteinTangentSpace_le_iff`: the tangent space is the least closed subspace of
  `L²(μ; E)` containing the gradients of test functions.
* `TauCeti.mem_orthogonal_wassersteinTangentSpace_iff`: the orthogonal complement of the
  tangent space consists of the fields `w` with `div (w μ) = 0`.
* `TauCeti.integral_fderiv_starProjection_wassersteinTangentSpace`: the projection onto the
  tangent space preserves the divergence.
* `TauCeti.starProjection_wassersteinTangentSpace_eq_iff`: the projection of `v` is the unique
  tangent field with the divergence of `v`.
* `TauCeti.starProjection_wassersteinTangentSpace_eq_of_integral_fderiv_eq`: the projection of a
  field depends only on its divergence.
* `TauCeti.norm_starProjection_wassersteinTangentSpace_le` and
  `TauCeti.eq_starProjection_wassersteinTangentSpace_of_norm_le`: the projection of `v` is the
  unique field of least norm with the divergence of `v`.
* `TauCeti.mem_wassersteinTangentSpace_iff_forall_norm_le`: a field is tangent if and only if
  adding a divergence-free field never decreases its norm.
* `TauCeti.wassersteinTangentSpace_dirac`: every field is tangent at a Dirac mass.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §8.4, Definition 8.4.1 and Lemma 8.4.2.
-/

public section

open MeasureTheory InnerProductSpace
open scoped Gradient RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E}

/-- The *tangent space* `Tan_μ P₂(E)` of the quadratic Wasserstein space at `μ`: the closure in
`L²(μ; E)` of the gradients `∇φ` of smooth compactly supported functions `φ : E → ℝ`. -/
noncomputable def wassersteinTangentSpace [FiniteDimensional ℝ E] (μ : Measure E) :
    Submodule ℝ (Lp E 2 μ) :=
  (Submodule.span ℝ {f : Lp E 2 μ | ∃ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    f =ᵐ[μ] ∇ φ}).topologicalClosure

variable [FiniteDimensional ℝ E]

/-- The tangent space is a closed subspace of `L²(μ; E)`. -/
theorem isClosed_wassersteinTangentSpace (μ : Measure E) :
    IsClosed (wassersteinTangentSpace μ : Set (Lp E 2 μ)) :=
  Submodule.isClosed_topologicalClosure _

/-- The tangent space is complete, so the orthogonal projection onto it exists. -/
instance (μ : Measure E) : CompleteSpace (wassersteinTangentSpace μ) :=
  (isClosed_wassersteinTangentSpace μ).completeSpace_coe

/-- An element of `L²(μ; E)` represented by the gradient of a test function is tangent. -/
theorem mem_wassersteinTangentSpace_of_ae_eq_gradient {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {f : Lp E 2 μ} (hf : f =ᵐ[μ] ∇ φ) :
    f ∈ wassersteinTangentSpace μ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, hφ, hφc, hf⟩)

/-- The `L²(μ)` class of the gradient of a test function is tangent. When `μ` is finite on
compact sets, `HasCompactSupport.memLp_gradient` supplies the square integrability. -/
theorem toLp_gradient_mem_wassersteinTangentSpace {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hm : MemLp (∇ φ) 2 μ) :
    hm.toLp (∇ φ) ∈ wassersteinTangentSpace μ :=
  mem_wassersteinTangentSpace_of_ae_eq_gradient hφ hφc hm.coeFn_toLp

/-- The tangent space is the least closed subspace of `L²(μ; E)` containing the gradients of the
smooth compactly supported functions. -/
theorem wassersteinTangentSpace_le_iff {K : Submodule ℝ (Lp E 2 μ)}
    (hK : IsClosed (K : Set (Lp E 2 μ))) :
    wassersteinTangentSpace μ ≤ K ↔ ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ f : Lp E 2 μ, f =ᵐ[μ] ∇ φ → f ∈ K := by
  refine ⟨fun h φ hφ hφc f hf ↦ h (mem_wassersteinTangentSpace_of_ae_eq_gradient hφ hφc hf),
    fun h ↦ Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hK⟩
  rintro f ⟨φ, hφ, hφc, hf⟩
  exact h φ hφ hφc f hf

/-- **The tangent space at a Dirac mass is everything.** At `δ_x` every field is tangent:
`Tan_{δ_x} P₂(E) = L²(δ_x; E)`, since a field in `L²(δ_x; E)` is determined by its value `c` at
`x`, and `c` is the gradient at `x` of the smooth compactly supported function
`y ↦ b y ⟨c, y - x⟩` for a bump function `b` equal to `1` near `x`. -/
@[simp]
theorem wassersteinTangentSpace_dirac [MeasurableSingletonClass E] (x : E) :
    wassersteinTangentSpace (Measure.dirac x) = ⊤ := by
  refine eq_top_iff.2 fun f _ ↦ ?_
  set c := f x
  let b : ContDiffBump x := ⟨1, 2, one_pos, one_lt_two⟩
  have hb : HasFDerivAt b (fderiv ℝ b x) x :=
    (b.contDiff (n := 1).differentiable one_ne_zero x).hasFDerivAt
  have hl : HasFDerivAt (fun y ↦ ⟪c, y - x⟫) (innerSL ℝ c) x := by
    convert (innerSL ℝ c).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x) using 1
    · ext y
      simp
    · ext y
      simp
  have hφ : ∇ (fun y ↦ b y * ⟪c, y - x⟫) x = c := by
    refine (hasGradientAt_iff_hasFDerivAt.2 ?_).gradient
    convert hb.mul hl using 1
    ext y
    simp [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  refine mem_wassersteinTangentSpace_of_ae_eq_gradient (φ := fun y ↦ b y * ⟪c, y - x⟫)
    (b.contDiff.mul (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)))
    b.hasCompactSupport.mul_right ?_
  filter_upwards [ae_eq_dirac (f : E → E), ae_eq_dirac (∇ fun y ↦ b y * ⟪c, y - x⟫)]
    with y h₁ h₂
  rw [h₁, h₂, Function.const_apply, Function.const_apply, hφ]

omit [FiniteDimensional ℝ E] in
/-- The `L²(μ)` pairing of the gradient of `φ` with a field `w` is `∫ ⟨∇φ, w⟩ dμ`, written as
`∫ fderiv ℝ φ x (w x) dμ`. -/
theorem inner_eq_integral_fderiv_of_ae_eq_gradient [CompleteSpace E] {φ : E → ℝ} {f : Lp E 2 μ}
    (hf : f =ᵐ[μ] ∇ φ) (w : Lp E 2 μ) : ⟪f, w⟫ = ∫ x, fderiv ℝ φ x (w x) ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf] with x hx
  rw [hx, gradient, toDual_symm_apply]

/-- A field is orthogonal to the tangent space if and only if it is orthogonal to every element
represented by the gradient of a test function. -/
private theorem mem_orthogonal_wassersteinTangentSpace_iff_inner {w : Lp E 2 μ} :
    w ∈ (wassersteinTangentSpace μ)ᗮ ↔ ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → ∀ f : Lp E 2 μ, f =ᵐ[μ] ∇ φ → ⟪f, w⟫ = 0 := by
  rw [wassersteinTangentSpace, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
  refine ⟨fun h φ hφ hφc f hf ↦ h f (Submodule.subset_span ⟨φ, hφ, hφc, hf⟩), fun h u hu ↦ ?_⟩
  induction hu using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, hφ, hφc, hf⟩ := hf
    exact h φ hφ hφc f hf
  | zero => exact inner_zero_left _
  | add f g _ _ hf hg => rw [inner_add_left, hf, hg, add_zero]
  | smul c f _ hf => rw [real_inner_smul_left, hf, mul_zero]

variable [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts μ]

/-- Two fields `w` and `v` differ by a field orthogonal to the tangent space if and only if they
have the same divergence: `∫ ⟨∇φ, w⟩ dμ = ∫ ⟨∇φ, v⟩ dμ` for every test function `φ`. -/
theorem sub_mem_orthogonal_wassersteinTangentSpace_iff {w v : Lp E 2 μ} :
    w - v ∈ (wassersteinTangentSpace μ)ᗮ ↔ ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → ∫ x, fderiv ℝ φ x (w x) ∂μ = ∫ x, fderiv ℝ φ x (v x) ∂μ := by
  simp_rw [mem_orthogonal_wassersteinTangentSpace_iff_inner, inner_sub_right, sub_eq_zero]
  refine ⟨fun h φ hφ hφc ↦ ?_, fun h φ hφ hφc f hf ↦ ?_⟩
  · -- The gradient of a test function is continuous with compact support, hence in `L²(μ)`.
    have hm : MemLp (∇ φ) 2 μ := hφc.memLp_gradient (hφ.of_le (by simp))
    simpa only [inner_eq_integral_fderiv_of_ae_eq_gradient hm.coeFn_toLp] using
      h φ hφ hφc _ hm.coeFn_toLp
  · simpa only [inner_eq_integral_fderiv_of_ae_eq_gradient hf] using h φ hφ hφc

/-- The orthogonal complement of the tangent space consists of the divergence-free fields: those
`w` with `div (w μ) = 0`, that is `∫ ⟨∇φ, w⟩ dμ = 0` for every test function `φ`. -/
theorem mem_orthogonal_wassersteinTangentSpace_iff {w : Lp E 2 μ} :
    w ∈ (wassersteinTangentSpace μ)ᗮ ↔ ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → ∫ x, fderiv ℝ φ x (w x) ∂μ = 0 := by
  have h0 (φ : E → ℝ) : ∫ x, fderiv ℝ φ x ((0 : Lp E 2 μ) x) ∂μ = 0 := by
    rw [integral_congr_ae ((Lp.coeFn_zero E 2 μ).mono fun x hx ↦ by rw [hx, Pi.zero_apply,
      map_zero])]
    exact integral_zero E ℝ
  simpa only [sub_zero, h0] using sub_mem_orthogonal_wassersteinTangentSpace_iff (w := w) (v := 0)

/-- The orthogonal projection onto the tangent space preserves the divergence:
`∫ ⟨∇φ, P v⟩ dμ = ∫ ⟨∇φ, v⟩ dμ` for every test function `φ`. -/
theorem integral_fderiv_starProjection_wassersteinTangentSpace (v : Lp E 2 μ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, fderiv ℝ φ x ((wassersteinTangentSpace μ).starProjection v x) ∂μ =
      ∫ x, fderiv ℝ φ x (v x) ∂μ :=
  (sub_mem_orthogonal_wassersteinTangentSpace_iff.1
    ((wassersteinTangentSpace μ).sub_starProjection_mem_orthogonal v) φ hφ hφc).symm

/-- The orthogonal projection of a field `v` onto the tangent space is the unique tangent field
with the divergence of `v`. -/
theorem starProjection_wassersteinTangentSpace_eq_iff {u v : Lp E 2 μ} :
    (wassersteinTangentSpace μ).starProjection v = u ↔ u ∈ wassersteinTangentSpace μ ∧
      ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, fderiv ℝ φ x (u x) ∂μ = ∫ x, fderiv ℝ φ x (v x) ∂μ := by
  rw [← sub_mem_orthogonal_wassersteinTangentSpace_iff]
  refine ⟨?_, fun ⟨hu, huv⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨Submodule.starProjection_apply_mem _ _,
      sub_mem_comm_iff.1 (Submodule.sub_starProjection_mem_orthogonal _)⟩
  · exact Submodule.eq_starProjection_of_mem_orthogonal' hu (neg_mem huv) (by abel)

/-- The projection of a field onto the tangent space depends only on its divergence. -/
theorem starProjection_wassersteinTangentSpace_eq_of_integral_fderiv_eq
    {w v : Lp E 2 μ} (hwv : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, fderiv ℝ φ x (w x) ∂μ = ∫ x, fderiv ℝ φ x (v x) ∂μ) :
    (wassersteinTangentSpace μ).starProjection w =
      (wassersteinTangentSpace μ).starProjection v :=
  starProjection_wassersteinTangentSpace_eq_iff.2 ⟨Submodule.starProjection_apply_mem _ v,
    fun φ hφ hφc ↦ (integral_fderiv_starProjection_wassersteinTangentSpace v hφ hφc).trans
      (hwv φ hφ hφc).symm⟩

/-- **Minimality of the tangent velocity.** The projection of `v` onto the tangent space has the
least `L²(μ)` norm among all fields with the divergence of `v`. -/
theorem norm_starProjection_wassersteinTangentSpace_le {w v : Lp E 2 μ}
    (hwv : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, fderiv ℝ φ x (w x) ∂μ = ∫ x, fderiv ℝ φ x (v x) ∂μ) :
    ‖(wassersteinTangentSpace μ).starProjection v‖ ≤ ‖w‖ := by
  rw [← starProjection_wassersteinTangentSpace_eq_of_integral_fderiv_eq hwv]
  exact Submodule.norm_starProjection_apply_le _ w

/-- **Uniqueness of the tangent velocity.** A field with the divergence of `v` whose norm is at
most that of the projection of `v` onto the tangent space is that projection. -/
theorem eq_starProjection_wassersteinTangentSpace_of_norm_le {w v : Lp E 2 μ}
    (hwv : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, fderiv ℝ φ x (w x) ∂μ = ∫ x, fderiv ℝ φ x (v x) ∂μ)
    (hw : ‖w‖ ≤ ‖(wassersteinTangentSpace μ).starProjection v‖) :
    w = (wassersteinTangentSpace μ).starProjection v := by
  rw [← starProjection_wassersteinTangentSpace_eq_of_integral_fderiv_eq hwv] at hw ⊢
  exact Submodule.eq_starProjection_of_norm_le _ hw

/-- **The tangent space is the space of minimal fields.** A field `v` is tangent if and only if
adding any divergence-free field `w` does not decrease its norm: `‖v‖ ≤ ‖v + w‖` whenever
`∫ ⟨∇φ, w⟩ dμ = 0` for every test function `φ`. -/
theorem mem_wassersteinTangentSpace_iff_forall_norm_le {v : Lp E 2 μ} :
    v ∈ wassersteinTangentSpace μ ↔ ∀ w : Lp E 2 μ, (∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → ∫ x, fderiv ℝ φ x (w x) ∂μ = 0) → ‖v‖ ≤ ‖v + w‖ := by
  simp_rw [← mem_orthogonal_wassersteinTangentSpace_iff]
  exact Submodule.mem_iff_forall_mem_orthogonal_norm_le_norm_add _

end TauCeti
