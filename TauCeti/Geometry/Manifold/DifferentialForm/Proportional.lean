/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Proportional smooth one-forms

A smooth one-form annihilating the kernel of a nowhere-zero smooth real one-form is a unique
smooth function times that form. In particular, generators of the same annihilator line have
smooth transition functions. Smoothness is local: extend a tangent vector on which the first
form is nonzero and divide the two evaluations on that local field. No metric, finite-dimensionality
or global transverse vector field is needed.
-/

public noncomputable section

open Bundle Filter
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α β : SmoothForm I M ℝ 1} {f : M → ℝ}

/-- A pointwise multiplier of a nowhere-zero smooth one-form is automatically smooth. -/
theorem contMDiff_of_eq_fun_smul (hα : ∀ x, α.1 x ≠ 0)
    (hf : ∀ x, β.1 x = f x • α.1 x) : ContMDiff I 𝓘(ℝ) ∞ f := by
  intro x
  obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x, degreeOneEquiv α x v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hα x
    ext w
    have hw : (fun _ : Fin 1 ↦ w 0) = w := funext fun i ↦ congrArg w (Subsingleton.elim _ _)
    simpa only [degreeOneEquiv_apply_apply, hw, ContinuousAlternatingMap.coe_zero,
      Pi.zero_apply] using hn (w 0)
  let V := FiberBundle.extend E v
  have hV := FiberBundle.contMDiffAt_extend (k := ∞) I E v
  have heval (γ : SmoothForm I M ℝ 1) :
      ContMDiffAt I 𝓘(ℝ) ∞ (fun y ↦ degreeOneEquiv γ y (V y)) x := by
    have h := ((degreeOneEquiv γ).contMDiff x).clm_bundle_apply hV
    rw [contMDiffAt_section] at h
    simpa only [Trivial.eq_trivialization M ℝ, Trivial.trivialization_apply] using h
  have hne : degreeOneEquiv α x (V x) ≠ 0 := by
    simpa only [V, FiberBundle.extend_apply_self] using hv
  refine ((heval β).div₀ (heval α) hne).congr_of_eventuallyEq ?_
  filter_upwards [(heval α).continuousAt.eventually_ne hne] with y hy
  simp only [degreeOneEquiv_apply_apply, hf, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  simpa only [degreeOneEquiv_apply_apply, Pi.div_apply] using
    (mul_div_cancel_right₀ (f y) hy).symm

/-- A smooth one-form annihilating the kernel of a nowhere-zero smooth real one-form is a
unique smooth scalar multiple of it. The multiplier may vanish where the second form does. -/
theorem existsUnique_fun_smul_of_ker_le (hα : ∀ x, α.1 x ≠ 0)
    (hker : ∀ x, RoughForm.ker α.1 x ≤ RoughForm.ker β.1 x) :
    ∃! f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ ∀ x, β.1 x = f x • α.1 x := by
  have hpoint (x : M) : ∃ c : ℝ, β.1 x = c • α.1 x := by
    let a := (degreeOneEquiv α x).toLinearMap
    let b := (degreeOneEquiv β x).toLinearMap
    have hk : LinearMap.ker a ≤ LinearMap.ker b := by
      intro v hv
      have hv' : v ∈ RoughForm.ker α.1 x := RoughForm.mem_ker.mpr
        ((degreeOneEquiv_coe_apply α x v).symm.trans hv)
      exact (degreeOneEquiv_coe_apply β x v).trans (RoughForm.mem_ker.mp (hker x hv'))
    have hb : b ∈ Submodule.span ℝ ({a} : Set (Module.Dual ℝ (TangentSpace I x))) := by
      simpa only [Set.range_const, iInf_const] using
        (mem_span_of_iInf_ker_le_ker (L := fun _ : Unit ↦ a) (K := b)
          (by simpa only [iInf_const] using hk))
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
    refine ⟨c, ?_⟩
    ext w
    have h := congrArg (fun L : Module.Dual ℝ (TangentSpace I x) ↦ L (w 0)) hc
    have hw : (fun _ : Fin 1 ↦ w 0) = w := funext fun i ↦ congrArg w (Subsingleton.elim _ _)
    simpa only [LinearMap.smul_apply, smul_eq_mul, a, b, ContinuousLinearMap.coe_coe,
      degreeOneEquiv_apply_apply, hw, ContinuousAlternatingMap.smul_apply] using h.symm
  choose f hf using hpoint
  refine ⟨f, ⟨contMDiff_of_eq_fun_smul hα hf, hf⟩, ?_⟩
  intro g hg
  funext x
  exact smul_left_injective ℝ (hα x) ((hg.2 x).symm.trans (hf x))

end TauCeti.SmoothForm
