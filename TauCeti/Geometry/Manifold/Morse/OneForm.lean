/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
public import TauCeti.Geometry.Manifold.DifferentialForm.Squared
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# Morse closed one-forms

A smooth closed real one-form is Morse when its zeros are nondegenerate critical points
of local potentials. `IsMorseOneForm` uses the actual alternating cotangent fibers and local
primitives; it imposes no condition on trajectories or periodic orbits.

Two local primitives differ locally by a constant. Their critical Hessians and Morse indices
therefore agree, and nondegeneracy can be checked with any local primitive. Zeros of a Morse
one-form are isolated and there are finitely many in every compact set. On a smooth
boundaryless manifold, the exact-form comparison identifies this notion with the existing
Morse-function predicate.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 1.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*,
  Forum Math. 14 (2002), Section 2.
-/

public section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {α : RoughForm I M ℝ 1} {f g : M → ℝ} {U V : Set M} {x : M}

/-- A smooth closed real one-form is Morse if each zero admits a local primitive with a
nondegenerate critical point there. This does not require Morse--Smale transversality or
nondegeneracy of periodic orbits. -/
structure IsMorseOneForm (α : RoughForm I M ℝ 1) : Prop where
  /-- The form is smooth. -/
  isSmoothForm : IsSmoothForm I ∞ α
  /-- The form is closed. -/
  mextDeriv_eq_zero : mextDeriv α = 0
  /-- Every zero is a nondegenerate critical point of a local primitive. -/
  exists_nondegenerate_primitive : ∀ x, α x = 0 →
    ∃ (f : M → ℝ) (U : Set M), x ∈ U ∧ IsPrimitiveOn α f U ∧
      IsManifoldNondegenerateCriticalPoint I f x

omit [IsManifold I 1 M] in
/-- The zeros of a one-form are the critical points of each of its local primitives. -/
theorem IsPrimitiveOn.eq_zero_iff_mem_criticalPoints (hf : IsPrimitiveOn α f U) (hx : x ∈ U) :
    α x = 0 ↔ x ∈ criticalPoints I f := by
  rw [← hf.mextDeriv_eq x hx, mextDeriv_ofFunction_apply_eq_zero_iff,
    mem_criticalPoints_iff_mfderiv_eq_zero]

section Independence

/-- Local primitives of the same one-form have the same preferred-chart Hessian at every
common point. At a zero this is the intrinsic critical Hessian. -/
theorem IsPrimitiveOn.criticalHessian_eq (hf : IsPrimitiveOn α f U)
    (hg : IsPrimitiveOn α g V) (hxU : x ∈ U) (hxV : x ∈ V) :
    criticalHessian I f x = criticalHessian I g x := by
  have hfg := hf.eventuallyEq_add_const hg hxU hxV
  have heq := criticalHessian_congr_of_eventuallyEq (I := I) hfg
  rw [heq, criticalHessian_def, criticalHessian_def]
  have hd : fderiv ℝ ((fun y ↦ g y + (f x - g x)) ∘ (extChartAt I x).symm) =
      fderiv ℝ (g ∘ (extChartAt I x).symm) := by
    funext y
    exact fderiv_add_const (𝕜 := ℝ) (f := g ∘ (extChartAt I x).symm) (x := y) (f x - g x)
  rw [hd]

/-- The Morse index of a local potential is independent of the potential chosen. -/
theorem IsPrimitiveOn.manifoldMorseIndex_eq (hf : IsPrimitiveOn α f U)
    (hg : IsPrimitiveOn α g V) (hxU : x ∈ U) (hxV : x ∈ V) :
    manifoldMorseIndex I f x = manifoldMorseIndex I g x := by
  simp only [manifoldMorseIndex_eq_sigNeg_criticalHessian, hf.criticalHessian_eq hg hxU hxV]

variable [I.Boundaryless]

/-- Nondegeneracy at a common point can be tested using either local potential. -/
theorem IsPrimitiveOn.isManifoldNondegenerateCriticalPoint_iff
    (hf : IsPrimitiveOn α f U) (hg : IsPrimitiveOn α g V) (hxU : x ∈ U) (hxV : x ∈ V) :
    IsManifoldNondegenerateCriticalPoint I f x ↔
      IsManifoldNondegenerateCriticalPoint I g x := by
  have transfer {f g : M → ℝ} {U V : Set M} (hf : IsPrimitiveOn α f U)
      (hg : IsPrimitiveOn α g V) (hxU : x ∈ U) (hxV : x ∈ V)
      (h : IsManifoldNondegenerateCriticalPoint I f x) :
      IsManifoldNondegenerateCriticalPoint I g x := by
    have hs : ContMDiffAt I 𝓘(ℝ) 2 g x :=
      (h.contMDiffAt.add contMDiffAt_const).congr_of_eventuallyEq
        (hg.eventuallyEq_add_const hf hxV hxU)
    rw [isManifoldNondegenerateCriticalPoint_iff_criticalHessian] at h ⊢
    refine ⟨hs, ?_, ?_⟩
    · have hz := (hf.eq_zero_iff_mem_criticalPoints hxU).2 (mem_criticalPoints.2 h.2.1)
      exact mem_criticalPoints.1 ((hg.eq_zero_iff_mem_criticalPoints hxV).1 hz)
    · rw [hg.criticalHessian_eq hf hxV hxU]
      exact h.2.2
  exact ⟨transfer hf hg hxU hxV, transfer hg hf hxV hxU⟩

/-- Every local primitive of a Morse one-form has a nondegenerate critical point at each zero
in its domain. -/
theorem IsMorseOneForm.isManifoldNondegenerateCriticalPoint (hα : IsMorseOneForm α)
    (hf : IsPrimitiveOn α f U) (hxU : x ∈ U) (hx : α x = 0) :
    IsManifoldNondegenerateCriticalPoint I f x := by
  obtain ⟨g, V, hxV, hg, hcrit⟩ := hα.exists_nondegenerate_primitive x hx
  exact (hg.isManifoldNondegenerateCriticalPoint_iff hf hxV hxU).1 hcrit

omit [I.Boundaryless] in
/-- A zero of a Morse one-form is isolated among its zeros. -/
theorem IsMorseOneForm.eventually_ne_zero (hα : IsMorseOneForm α) (hx : α x = 0) :
    ∀ᶠ y in 𝓝[≠] x, α y ≠ 0 := by
  obtain ⟨f, U, hxU, hf, hcrit⟩ := hα.exists_nondegenerate_primitive x hx
  filter_upwards [hcrit.eventually_notMem_criticalPoints,
    nhdsWithin_le_nhds (hf.isOpen.mem_nhds hxU)] with y hy hyU
  exact mt (hf.eq_zero_iff_mem_criticalPoints hyU).1 hy

end Independence

section Exact

variable [IsManifold I ∞ M] [I.Boundaryless]

/-- The differential of a smooth function is a Morse one-form exactly when the function is
Morse. In particular the one-form predicate includes the ordinary exact case. -/
@[simp]
theorem isMorseOneForm_mextDeriv_ofFunction_iff (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    IsMorseOneForm (mextDeriv (RoughForm.ofFunction I f)) ↔ IsMorse I f := by
  have hp : IsPrimitiveOn (mextDeriv (RoughForm.ofFunction I f)) f univ :=
    ⟨isOpen_univ, (hf.mdifferentiable (by simp)).mdifferentiableOn, fun _ _ ↦ rfl⟩
  constructor
  · intro hα
    rw [isMorse_iff]
    refine ⟨hf, fun x hx ↦ ?_⟩
    have hc : x ∈ criticalPoints I f :=
      mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero.2 hx
    exact hα.isManifoldNondegenerateCriticalPoint hp (mem_univ x)
      ((hp.eq_zero_iff_mem_criticalPoints (mem_univ x)).2 hc)
  · intro h
    refine ⟨isSmoothForm_mextDeriv ((isSmoothForm_ofFunction_iff (n := ∞)).2 hf) (by simp),
      mextDeriv_mextDeriv_ofFunction (hf.of_le (by simp)), fun x hx ↦ ?_⟩
    exact ⟨f, univ, mem_univ x, hp,
      h.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        ((hp.eq_zero_iff_mem_criticalPoints (mem_univ x)).1 hx)⟩

end Exact

section Finite

/-- A Morse one-form has finitely many zeros in every compact set. -/
theorem IsMorseOneForm.finite_zeroSet_inter (hα : IsMorseOneForm α) {K : Set M}
    (hK : IsCompact K) : ({x | α x = 0} ∩ K).Finite := by
  refine (hK.inter_left hα.isSmoothForm.isClosed_zeroSet).finite ?_
  rw [isDiscrete_iff_nhdsNE]
  rintro x ⟨hx, -⟩
  rw [inf_principal_eq_bot]
  filter_upwards [hα.eventually_ne_zero hx] with y hy using fun h ↦ hy h.1

/-- A Morse one-form on a compact manifold has finitely many zeros. -/
theorem IsMorseOneForm.finite_zeroSet [CompactSpace M] (hα : IsMorseOneForm α) :
    {x | α x = 0}.Finite := by
  simpa using hα.finite_zeroSet_inter isCompact_univ

end Finite

end TauCeti
