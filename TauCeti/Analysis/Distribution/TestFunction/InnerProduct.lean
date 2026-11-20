/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Postcomp
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Riesz transport on native test functions

For a complete complex Hilbert coefficient space, the native Riesz isometry induces a real
continuous linear equivalence on test functions, with their original topology. It is
conjugate-linear for the original complex action. No finite-dimensionality or nonzero-rank
hypothesis is required, and every finite differentiability order and infinity are allowed.
-/

public section
noncomputable section

open TopologicalSpace ComplexConjugate MeasureTheory
open scoped Distributions

namespace TestFunction

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {n : ℕ∞} {Ω : Opens E}

/-- Native Riesz transport of coefficient values, for the original test-function topologies.
The equivalence is real-linear and conjugates the complex scalar action. -/
def rieszEquiv : 𝓓^{n}(Ω, V) ≃L[ℝ] 𝓓^{n}(Ω, StrongDual ℂ V) :=
  postcompCLE ((InnerProductSpace.toDual ℂ V).toIsometryEquiv
    |>.toRealLinearIsometryEquivOfMapZero (map_zero (InnerProductSpace.toDual ℂ V))
    |>.toContinuousLinearEquiv)

/-- Riesz transport evaluates to the original complex Hilbert pairing. -/
@[simp]
theorem rieszEquiv_apply (u : 𝓓^{n}(Ω, V)) (x : E) (v : V) :
    rieszEquiv u x v = inner ℂ (u x) v := by
  simp only [rieszEquiv, postcompCLE_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  have he := IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero
    (InnerProductSpace.toDual ℂ V).toIsometryEquiv (map_zero (InnerProductSpace.toDual ℂ V))
  exact (congrArg (fun L : V → StrongDual ℂ V ↦ L (u x) v) he).trans
    InnerProductSpace.toDual_apply_apply

/-- The inverse native map recovers the Riesz representative of every original dual-valued test. -/
@[simp]
theorem rieszEquiv_symm_apply (φ : 𝓓^{n}(Ω, StrongDual ℂ V)) (x : E) (v : V) :
    inner ℂ (rieszEquiv.symm φ x) v = φ x v := by
  have h := congrArg (fun q : 𝓓^{n}(Ω, StrongDual ℂ V) ↦ q x v)
    (rieszEquiv.apply_symm_apply φ)
  simpa only [rieszEquiv_apply] using h

/-- Native Riesz transport conjugates the original complex test action. -/
theorem rieszEquiv_smul (c : ℂ) (u : 𝓓^{n}(Ω, V)) :
    rieszEquiv (c • u) = conj c • rieszEquiv u := by
  apply TestFunction.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simp only [rieszEquiv_apply, smul_apply, inner_smul_left]
  rfl

/-- The inverse Riesz transport has the same conjugate-scalar action. -/
theorem rieszEquiv_symm_smul (c : ℂ) (φ : 𝓓^{n}(Ω, StrongDual ℂ V)) :
    (rieszEquiv (V := V)).symm (c • φ) = conj c • (rieszEquiv (V := V)).symm φ := by
  apply (rieszEquiv (V := V)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, rieszEquiv_smul,
    starRingEnd_self_apply, ContinuousLinearEquiv.apply_symm_apply]

omit [CompleteSpace V] in
/-- Native tests are separated by their spatial Hilbert pairings. The measure need only be
finite on compact sets and charge every nonempty open set; no finite-dimensional base is needed. -/
theorem eq_of_forall_integral_inner_eq [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ] {f g : 𝓓^{n}(Ω, V)}
    (h : ∀ u : 𝓓^{n}(Ω, V), (∫ x, inner ℂ (u x) (f x) ∂μ) =
      ∫ x, inner ℂ (u x) (g x) ∂μ) : f = g := by
  have hint (a b : 𝓓^{n}(Ω, V)) : Integrable (fun x ↦ inner ℂ (a x) (b x)) μ :=
    (a.continuous.inner b.continuous).integrable_of_hasCompactSupport
      (a.hasCompactSupport.mono fun x hx hz ↦ hx (by simp [hz]))
  let d := f - g
  have hz : (∫ x, inner ℂ (d x) (d x) ∂μ) = 0 := by
    have he (x : E) : inner ℂ (d x) (d x) =
        inner ℂ (d x) (f x) - inner ℂ (d x) (g x) := inner_sub_right _ _ _
    simp_rw [he]
    rw [integral_sub (hint d f) (hint d g), h d, sub_self]
  have hi : Integrable (fun x ↦ ‖d x‖ ^ 2) μ :=
    (d.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (by
        have hc := d.hasCompactSupport.comp_left
          (g := fun v : V ↦ ‖v‖ ^ 2) (by simp)
        exact hc)
  have hnorm : (∫ x, ‖d x‖ ^ 2 ∂μ) = 0 := by
    have hr := congrArg (RCLike.re : ℂ → ℝ) hz
    rw [← integral_re (hint d d)] at hr
    simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow, map_zero] using hr
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg ‖d x‖) hi).mp hnorm
  have hdz : (d : E → V) =ᵐ[μ] 0 := by
    filter_upwards [hae] with x hx
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  have hde : (d : E → V) = 0 := (d.continuous.ae_eq_iff_eq μ continuous_zero).mp hdz
  apply sub_eq_zero.mp
  apply TestFunction.ext
  intro x
  exact congrFun hde x

end TestFunction
