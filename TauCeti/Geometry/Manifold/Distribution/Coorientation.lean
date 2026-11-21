/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.Distribution.Annihilator
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Annihilator
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Topology.VectorBundle.Smul
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Coorientations of hyperplane fields and global defining forms

Let `D` be a smooth hyperplane field on a manifold `M`: a smooth distribution of rank
`dim M - 1`. Near every point it is the kernel of a nowhere-zero smooth one-form
(`TauCeti.IsContMDiffDistribution.exists_roughForm_ker_eq`), but in general there is no such form on
all of `M`. The local defining forms at a point are the nonzero elements of the annihilator line
`D⁰_x ⊆ T*_x M` (`TauCeti.CotangentBundle.annihilatorSpace`), so a global defining form is a
nowhere-zero smooth section of the line bundle `D⁰`.

This file proves that already a *continuous* nowhere-zero section `σ` of `D⁰`, that is, a
continuous choice of a nonzero annihilating covector at every point, gives a global defining form:
on a Hausdorff σ-compact manifold there is a smooth one-form `α` with `α_x` a positive multiple of
`σ_x` at every point (`TauCeti.IsContMDiffDistribution.exists_smoothForm_pos_smul`). The proof glues
local defining forms by a smooth partition of unity
(`exists_contMDiffSection_forall_mem_convex_of_local`). Near a point `x₀`, a local defining form
`a` is a nonzero multiple `σ_y = c(y) a_y`. The multiplier `c` is continuous
(`TauCeti.VectorBundle.continuousAt_of_eventually_eq_smul`), so it keeps the sign of `c(x₀)` near
`x₀`, and `c(x₀) a` is a local smooth form whose values lie in the open ray `{c σ_y | c > 0}`. These
rays are convex, so the glued form also takes values in them.

Consequently `D` is the kernel of a global nowhere-zero smooth one-form exactly when its annihilator
line has a continuous nowhere-zero section
(`TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_continuous`), and exactly when
the smooth line bundle `D⁰` is trivial: it has a smooth trivialization over all of `M`
(`TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_trivialization`). A choice of
such a section up to positive multiples is a coorientation of `D`. For a contact structure this is
the statement that a global contact form exists exactly when the contact structure is
coorientable; see `TauCeti.Geometry.Contact.Coorientation`.

## Main results

* `TauCeti.IsContMDiffDistribution.exists_local_pos_smul`: near every point a continuous
  nowhere-zero section of the annihilator line is a positive multiple of a smooth local section.
* `TauCeti.IsContMDiffDistribution.exists_smoothForm_pos_smul`: a continuous nowhere-zero section of
  the annihilator line is a positive multiple of a global smooth one-form.
* `TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_continuous`: a hyperplane
  field is the kernel of a global nowhere-zero smooth one-form exactly when its annihilator line
  has a continuous nowhere-zero section.
* `TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_trivialization`: it is the
  kernel of a global nowhere-zero smooth one-form exactly when its annihilator line bundle is
  smoothly trivial.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008, Section 1.1
  and Lemma 1.1.1 (a hyperplane field is the kernel of a global one-form exactly when it is
  coorientable).
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Theorem 2.25 and Chapter 19 (partitions of unity and local defining forms).
-/

public section

noncomputable section

open Bundle Set Filter Module
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}
  {σ : Π x : M, TangentSpace I x →L[ℝ] ℝ}

namespace IsContMDiffDistribution

/-- **A continuous section of the annihilator line is locally a positive multiple of a smooth
one.** Let `σ` be a continuous section of the annihilator line `D⁰` of a smooth hyperplane field
`D` which vanishes nowhere. Every point has a neighbourhood carrying a smooth covector field `a`
with `a_y` a positive multiple of `σ_y` at every point `y` of the neighbourhood. -/
theorem exists_local_pos_smul (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E)
    (hσ : Continuous fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x (σ x))
    (hσ₀ : ∀ x, σ x ≠ 0) (hσD : ∀ x, σ x ∈ CotangentBundle.annihilatorSpace I D x) (x₀ : M) :
    ∃ U ∈ 𝓝 x₀, ∃ a : Π x : M, TangentSpace I x →L[ℝ] ℝ,
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) y
          (a y)) U ∧
      ∀ y ∈ U, ∃ c : ℝ, 0 < c ∧ a y = c • σ y := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  obtain ⟨U, a, hU, hx₀U, ha, haD⟩ := hD.exists_local_annihilator hk x₀
  -- On `U` the covector `σ_y` is a nonzero multiple `c y • a_y` of the local defining covector.
  have hmul : ∀ y ∈ U, ∃ c : ℝ, c ≠ 0 ∧ σ y = c • a y := by
    intro y hy
    have hmem := hσD y
    rw [CotangentBundle.annihilatorSpace_eq_span_singleton (haD y hy).2,
      Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, fun hc0 ↦ hσ₀ y ?_, hc.symm⟩
    rw [← hc, hc0, zero_smul]
  choose! c hc₀ hσa using hmul
  -- The multiplier `c` is continuous at `x₀`, so near `x₀` it has the sign of `c x₀`, and
  -- `c x₀ • a` is a positive multiple of `σ` there.
  have hcont := VectorBundle.continuousAt_of_eventually_eq_smul
    ((ha x₀ hx₀U).contMDiffAt (hU.mem_nhds hx₀U)).continuousAt hσ.continuousAt
    (eventually_of_mem (hU.mem_nhds hx₀U) fun y hy ↦ by rw [hσa y hy]) (haD x₀ hx₀U).1
  have hpos : ∀ᶠ y in 𝓝 x₀, 0 < c x₀ * c y :=
    (continuousAt_const.mul hcont).eventually
      (lt_mem_nhds (mul_self_pos.2 (hc₀ x₀ hx₀U)))
  refine ⟨U ∩ {y | 0 < c x₀ * c y}, inter_mem (hU.mem_nhds hx₀U) hpos, fun y ↦ c x₀ • a y,
    (ha.mono inter_subset_left).const_smul_section (a := c x₀), ?_⟩
  rintro y ⟨hyU, hy⟩
  have hcy := hc₀ y hyU
  refine ⟨c x₀ * (c y)⁻¹, ?_, ?_⟩
  · have : c x₀ * (c y)⁻¹ = (c x₀ * c y) * ((c y)⁻¹ * (c y)⁻¹) := by field_simp
    rw [this]
    exact mul_pos hy (mul_self_pos.2 (inv_ne_zero hcy))
  · rw [hσa y hyU, smul_smul, mul_assoc, inv_mul_cancel₀ hcy, mul_one]

/-- **A one-form proportional to a nonzero annihilating covector defines the hyperplane.** If the
value at `x` of a smooth one-form `α` is a nonzero multiple of a nonzero covector `σ_x` annihilating
the hyperplane `D x`, then `α` does not vanish at `x` and its kernel there is `D x`. -/
theorem ne_zero_and_ker_eq_of_degreeOneEquiv_eq_smul (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) {α : SmoothForm I M ℝ 1} {x : M} {c : ℝ} (hc : c ≠ 0)
    (hσ₀ : σ x ≠ 0) (hσD : σ x ∈ CotangentBundle.annihilatorSpace I D x)
    (hαc : SmoothForm.degreeOneEquiv α x = c • σ x) :
    α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x := by
  have hne : RoughForm.eval α.val x ≠ 0 := by
    intro h
    refine hσ₀ (ContinuousLinearMap.ext fun v ↦ ?_)
    have hv := congr($h v)
    rw [RoughForm.eval_apply, ← SmoothForm.degreeOneEquiv_apply_apply_vec, hαc,
      smul_apply, smul_eq_mul, LinearMap.zero_apply] at hv
    rw [zero_apply]
    exact (mul_eq_zero.1 hv).resolve_left hc
  refine ⟨fun h ↦ hne ?_, ?_⟩
  · ext v
    rw [RoughForm.eval_apply, h, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
      LinearMap.zero_apply]
  rw [RoughForm.ker_eq_ker_eval]
  refine Module.Dual.ker_eq_of_le_of_finrank_add_one _ hne (fun v hv ↦ ?_)
    (by rw [hD.finrank_eq x]; exact hk)
  rw [LinearMap.mem_ker, RoughForm.eval_apply, ← SmoothForm.degreeOneEquiv_apply_apply_vec, hαc,
    smul_apply, (CotangentBundle.mem_annihilatorSpace_iff.1 hσD) v hv, smul_zero]

variable [T2Space M] [SigmaCompactSpace M]

/-- **A coorientation of a hyperplane field is induced by a global smooth one-form.** Let `σ` be a
continuous section of the annihilator line `D⁰` of a smooth hyperplane field `D` on a Hausdorff
σ-compact manifold, vanishing nowhere. Then some smooth one-form `α` is, at every point, a positive
multiple of `σ`. -/
theorem exists_smoothForm_pos_smul (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E)
    (hσ : Continuous fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x (σ x))
    (hσ₀ : ∀ x, σ x ≠ 0) (hσD : ∀ x, σ x ∈ CotangentBundle.annihilatorSpace I D x) :
    ∃ α : SmoothForm I M ℝ 1, ∀ x, ∃ c : ℝ, 0 < c ∧ SmoothForm.degreeOneEquiv α x = c • σ x := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  -- The positive multiples of `σ_x` form the convex image of `(0, ∞)` under `c ↦ c • σ_x`.
  have hloc (x₀ : M) : ∃ U ∈ 𝓝 x₀, ∃ a : Π x : M, TangentSpace I x →L[ℝ] ℝ,
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) y
          (a y)) U ∧ ∀ y ∈ U, a y ∈ LinearMap.toSpanSingleton ℝ _ (σ y) '' Ioi 0 := by
    obtain ⟨U, hU, a, ha, haσ⟩ := hD.exists_local_pos_smul hk hσ hσ₀ hσD x₀
    refine ⟨U, hU, a, ha, fun y hy ↦ ?_⟩
    obtain ⟨c, hc, hac⟩ := haσ y hy
    exact ⟨c, hc, by rw [LinearMap.toSpanSingleton_apply, hac]⟩
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I (F_fiber := E →L[ℝ] ℝ)
    (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
    (fun x ↦ LinearMap.toSpanSingleton ℝ _ (σ x) '' Ioi 0)
    (fun x ↦ (convex_Ioi 0).linear_image _) hloc
  refine ⟨SmoothForm.degreeOneEquiv.symm s, fun x ↦ ?_⟩
  obtain ⟨c, hc, hcs⟩ := hs x
  exact ⟨c, hc, by rw [LinearEquiv.apply_symm_apply, ← hcs, LinearMap.toSpanSingleton_apply]⟩

/-- **A hyperplane field is the kernel of a global one-form exactly when it is coorientable.** A
smooth hyperplane field `D` on a Hausdorff σ-compact manifold is the kernel of a smooth one-form
vanishing nowhere exactly when its annihilator line `D⁰` has a continuous section vanishing
nowhere. -/
theorem exists_smoothForm_ker_eq_iff_exists_continuous (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) :
    (∃ α : SmoothForm I M ℝ 1, ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x) ↔
      ∃ σ : Π x : M, TangentSpace I x →L[ℝ] ℝ,
        (Continuous fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x (σ x)) ∧
        ∀ x, σ x ≠ 0 ∧ σ x ∈ CotangentBundle.annihilatorSpace I D x := by
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨fun x ↦ SmoothForm.degreeOneEquiv α x,
      (SmoothForm.degreeOneEquiv α).contMDiff.continuous, fun x ↦ ⟨fun h ↦ (hα x).1 ?_, ?_⟩⟩
    · have h' : SmoothForm.degreeOneEquiv α x = 0 := h
      rw [← SmoothForm.degreeOneEquiv_coe_eq_zero_iff, h', ContinuousLinearMap.toLinearMap_zero]
    · rw [CotangentBundle.mem_annihilatorSpace_iff]
      intro v hv
      rw [← (hα x).2, RoughForm.mem_ker] at hv
      rw [SmoothForm.degreeOneEquiv_apply_apply_vec, hv]
  · rintro ⟨σ, hσ, hσD⟩
    obtain ⟨α, hα⟩ := hD.exists_smoothForm_pos_smul hk hσ (fun x ↦ (hσD x).1) fun x ↦ (hσD x).2
    refine ⟨α, fun x ↦ ?_⟩
    obtain ⟨c, hc, hαc⟩ := hα x
    exact hD.ne_zero_and_ker_eq_of_degreeOneEquiv_eq_smul hk hc.ne' (hσD x).1 (hσD x).2 hαc

/-- **A hyperplane field is the kernel of a global one-form exactly when its annihilator line is
trivial.** A smooth hyperplane field `D` on a Hausdorff σ-compact manifold is the kernel of a smooth
one-form vanishing nowhere exactly when its annihilator line bundle `D⁰`
(`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`) has a smooth linear trivialization over
all of `M`. -/
theorem exists_smoothForm_ker_eq_iff_exists_trivialization [FiniteDimensional ℝ E]
    (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E) :
    haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
    letI := hD.annihilatorFiberBundle hk
    letI := hD.annihilatorVectorBundle hk
    (∃ α : SmoothForm I M ℝ 1, ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x) ↔
      ∃ (e : Trivialization (Fin 1 → ℝ)
          (π (Fin 1 → ℝ) fun x ↦ CotangentBundle.annihilatorSpace I D x)) (_ : e.IsLinear ℝ),
        e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear M (Fin 1 → ℝ) I ∞).maximalAtlas
          (TotalSpace (Fin 1 → ℝ) fun x ↦ CotangentBundle.annihilatorSpace I D x) ∧
        e.baseSet = univ := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.annihilatorFiberBundle hk
  let := hD.annihilatorVectorBundle hk
  let := hD.annihilatorContMDiffVectorBundle hk
  have hemb := hD.isSmoothEmbedding_annihilatorInclusion hk
  rw [ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero
    (Module.finrank_fin_fun ℝ), hD.exists_smoothForm_ker_eq_iff_exists_continuous hk]
  constructor
  · rintro ⟨σ, hσ, hσD⟩
    -- A continuous section of `D⁰` glues to a smooth form, whose values are a smooth section.
    obtain ⟨α, hα⟩ := hD.exists_smoothForm_pos_smul hk hσ (fun x ↦ (hσD x).1) fun x ↦ (hσD x).2
    have hmem (x : M) : SmoothForm.degreeOneEquiv α x ∈ CotangentBundle.annihilatorSpace I D x := by
      obtain ⟨c, -, hc⟩ := hα x
      rw [hc]
      exact Submodule.smul_mem _ c (hσD x).2
    refine ⟨fun x ↦ ⟨SmoothForm.degreeOneEquiv α x, hmem x⟩, ?_, fun x h ↦ ?_⟩
    · rw [hemb.contMDiff_iff_comp]
      convert (SmoothForm.degreeOneEquiv α).contMDiff using 1
      funext x
      rw [Function.comp_apply, CotangentBundle.annihilatorInclusion_apply]
    · obtain ⟨c, hc, hαc⟩ := hα x
      have h' : SmoothForm.degreeOneEquiv α x = 0 := congrArg Subtype.val h
      rw [hαc] at h'
      exact (hσD x).1 ((smul_eq_zero.1 h').resolve_left hc.ne')
  · rintro ⟨σ, hσ, hσ₀⟩
    refine ⟨fun x ↦ (σ x : TangentSpace I x →L[ℝ] ℝ), ?_, fun x ↦ ⟨fun h ↦ hσ₀ x (Subtype.ext h),
      (σ x).property⟩⟩
    convert ((hD.contMDiff_annihilatorInclusion hk).comp hσ).continuous using 1
    funext x
    rw [Function.comp_apply, CotangentBundle.annihilatorInclusion_apply]

end IsContMDiffDistribution

end TauCeti
