/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Squared
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph

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

Morse one-forms pull back along smooth local diffeomorphisms, and descend along surjective ones.
If `π` is a smooth local diffeomorphism and `g` is a potential with `dg = π^* α` for a Morse
one-form `α`, then `g` is a Morse function whose critical set is the preimage under `π` of the
zeros of `α`, with the Morse index at `x` equal to that of any local primitive of `α` at `π x`.

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
common point. -/
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

/-- Nondegeneracy at a common point can be tested using either local potential. -/
theorem IsPrimitiveOn.isManifoldNondegenerateCriticalPoint_iff
    (hf : IsPrimitiveOn α f U) (hg : IsPrimitiveOn α g V) (hxU : x ∈ U) (hxV : x ∈ V) :
    IsManifoldNondegenerateCriticalPoint I f x ↔
      IsManifoldNondegenerateCriticalPoint I g x := by
  have transfer {f g : M → ℝ} {U V : Set M} (hf : IsPrimitiveOn α f U)
      (hg : IsPrimitiveOn α g V) (hxU : x ∈ U) (hxV : x ∈ V)
      (h : IsManifoldNondegenerateCriticalPoint I f x) :
      IsManifoldNondegenerateCriticalPoint I g x := by
    rw [TauCeti.isManifoldNondegenerateCriticalPoint_iff] at h ⊢
    have hgf : g ∘ (extChartAt I x).symm =ᶠ[𝓝 (extChartAt I x x)]
        (fun y ↦ (f ∘ (extChartAt I x).symm) y + (g x - f x)) := by
      have heq := hg.eventuallyEq_add_const hf hxV hxU
      have hchart : (extChartAt I x).symm (extChartAt I x x) = x := by simp
      have ht : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
        simpa only [hchart] using (continuousAt_extChartAt_symm (I := I) x).tendsto
      exact heq.comp_tendsto ht
    have hd : fderiv ℝ (g ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)]
        fderiv ℝ (f ∘ (extChartAt I x).symm) :=
      hgf.fderiv.trans (Eventually.of_forall fun y ↦ fderiv_add_const (g x - f x))
    refine ⟨(h.contDiffAt.add contDiffAt_const).congr_of_eventuallyEq hgf, ?_, ?_⟩
    · rw [hd.eq_of_nhds, h.fderiv_eq_zero]
    · rw [hd.fderiv_eq]
      exact h.isInvertible
  exact ⟨transfer hf hg hxU hxV, transfer hg hf hxV hxU⟩

/-- Every local primitive of a Morse one-form has a nondegenerate critical point at each zero
in its domain. -/
theorem IsMorseOneForm.isManifoldNondegenerateCriticalPoint (hα : IsMorseOneForm α)
    (hf : IsPrimitiveOn α f U) (hxU : x ∈ U) (hx : α x = 0) :
    IsManifoldNondegenerateCriticalPoint I f x := by
  obtain ⟨g, V, hxV, hg, hcrit⟩ := hα.exists_nondegenerate_primitive x hx
  exact (hg.isManifoldNondegenerateCriticalPoint_iff hf hxV hxU).1 hcrit

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
    isPrimitiveOn_univ_of_mextDeriv_eq (hf.mdifferentiable (by simp)) rfl
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

section Pullback

variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] {π : N → M} {g : N → ℝ}

omit [IsManifold I 1 M] in
/-- **Critical points of a lifted potential.** If `π` is a local diffeomorphism and `g` is a
function with `dg = π^* α`, the critical points of `g` are the preimages of the zeros of `α`. -/
theorem _root_.IsLocalDiffeomorph.criticalPoints_eq_preimage_of_mextDeriv_eq_mpullback
    {n : WithTop ℕ∞} (hπ : IsLocalDiffeomorph I I n π) (hn : n ≠ 0)
    (hdg : mextDeriv (RoughForm.ofFunction I g) = mpullback I I π α) :
    criticalPoints I g = π ⁻¹' {y | α y = 0} := by
  ext x
  rw [mem_criticalPoints_iff_mfderiv_eq_zero, ← mextDeriv_ofFunction_apply_eq_zero_iff, hdg,
    (hπ x).mpullback_apply_eq_zero_iff hn, mem_preimage, mem_ofPred_eq]

variable [IsManifold I ∞ M] [IsManifold I ∞ N] [I.Boundaryless]

/-- **Morse one-forms pull back along local diffeomorphisms.** The pullback of a Morse one-form
along a smooth local diffeomorphism is a Morse one-form. -/
theorem IsMorseOneForm.mpullback (hα : IsMorseOneForm α) (hπ : IsLocalDiffeomorph I I ∞ π) :
    IsMorseOneForm (mpullback I I π α) := by
  refine ⟨hα.isSmoothForm.mpullback (hπ.contMDiff.of_le (by simp)),
    (hα.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero hα.mextDeriv_eq_zero
      (hπ.contMDiff.of_le (by simp)), fun x hx ↦ ?_⟩
  -- Each zero `x` of the pullback lies over a zero `π x` of the form, and a local primitive `f`
  -- near `π x` lifts to the local primitive `f ∘ π` near `x`.
  rw [(hπ x).mpullback_apply_eq_zero_iff (by simp)] at hx
  obtain ⟨f, U, hxU, hf, hcrit⟩ := hα.exists_nondegenerate_primitive (π x) hx
  exact ⟨f ∘ π, π ⁻¹' U, hxU, hf.mpullback (hπ.contMDiff.mdifferentiable (by simp)),
    ((hπ x).isManifoldNondegenerateCriticalPoint_comp_iff (by simp)).2 hcrit⟩

/-- **Morse one-forms descend along surjective local diffeomorphisms.** For a surjective smooth
local diffeomorphism `π`, a one-form is Morse exactly when its pullback along `π` is. -/
theorem _root_.IsLocalDiffeomorph.isMorseOneForm_mpullback_iff
    (hπ : IsLocalDiffeomorph I I ∞ π) (hsurj : Function.Surjective π) :
    IsMorseOneForm (TauCeti.mpullback I I π α) ↔ IsMorseOneForm α := by
  refine ⟨fun h ↦ ?_, fun hα ↦ hα.mpullback hπ⟩
  have hsmooth : IsSmoothForm I ∞ α :=
    (hπ.isSmoothForm_mpullback_iff hsurj (by simp)).mp h.isSmoothForm
  have hclosed : mextDeriv α = 0 := by
    refine (SmoothForm.isClosed_def ⟨α, hsmooth.mem_smoothBundleForms⟩).mp
      ((hπ.isClosed_mpullback_iff hsurj).mp ?_)
    rw [SmoothForm.isClosed_def, SmoothForm.coe_mpullback]
    exact h.mextDeriv_eq_zero
  refine ⟨hsmooth, hclosed, fun y hy ↦ ?_⟩
  -- For a local primitive `g` of the pullback near `x` and a local inverse `s` of `π`, `g ∘ s` is
  -- a local primitive of `α` near `y = π x`. It lifts back to a local primitive of the pullback,
  -- which is nondegenerate at `x` because the pullback is Morse.
  obtain ⟨x, rfl⟩ := hsurj y
  have hx : TauCeti.mpullback I I π α x = 0 := ((hπ x).mpullback_apply_eq_zero_iff (by simp)).2 hy
  obtain ⟨g, V, hxV, hg, -⟩ := h.exists_nondegenerate_primitive x hx
  set s := (hπ x).localInverse
  have hsx : s (π x) = x := (hπ x).localInverse_left_inv (hπ x).localInverse_mem_target
  have hf : IsPrimitiveOn α (g ∘ s) (s.source ∩ s ⁻¹' V) :=
    (hπ x).isPrimitiveOn_comp_localInverse (by simp) hg
  have hxU : π x ∈ s.source ∩ s ⁻¹' V :=
    ⟨(hπ x).localInverse_mem_source, by rwa [mem_preimage, hsx]⟩
  refine ⟨g ∘ s, _, hxU, hf, ((hπ x).isManifoldNondegenerateCriticalPoint_comp_iff (by simp)).1 ?_⟩
  exact h.isManifoldNondegenerateCriticalPoint
    (hf.mpullback (hπ.contMDiff.mdifferentiable (by simp))) hxU hx

/-- **A lifted potential is Morse.** If `π` is a smooth local diffeomorphism, `α` is a Morse
one-form and `g` is a smooth function with `dg = π^* α`, then `g` is a Morse function. -/
theorem IsMorseOneForm.isMorse_of_mextDeriv_eq_mpullback (hα : IsMorseOneForm α)
    (hπ : IsLocalDiffeomorph I I ∞ π) (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hdg : mextDeriv (RoughForm.ofFunction I g) = TauCeti.mpullback I I π α) : IsMorse I g :=
  (isMorseOneForm_mextDeriv_ofFunction_iff hg).mp (hdg ▸ hα.mpullback hπ)

/-- **Morse indices of a lifted potential.** If `π` is a smooth local diffeomorphism, `α` is a
Morse one-form and `g` is a differentiable function with `dg = π^* α`, then at a point `x` over a
zero of `α` the Morse index of `g` is the Morse index at `π x` of any local primitive of `α`. -/
theorem IsMorseOneForm.manifoldMorseIndex_eq_of_mextDeriv_eq_mpullback (hα : IsMorseOneForm α)
    (hπ : IsLocalDiffeomorph I I ∞ π) (hg : MDifferentiable I 𝓘(ℝ) g)
    (hdg : mextDeriv (RoughForm.ofFunction I g) = TauCeti.mpullback I I π α) {x : N}
    (hf : IsPrimitiveOn α f U) (hxU : π x ∈ U) (hx : α (π x) = 0) :
    manifoldMorseIndex I g x = manifoldMorseIndex I f (π x) := by
  have hcrit := hα.isManifoldNondegenerateCriticalPoint hf hxU hx
  rw [(isPrimitiveOn_univ_of_mextDeriv_eq hg hdg).manifoldMorseIndex_eq
      (hf.mpullback (hπ.contMDiff.mdifferentiable (by simp))) (mem_univ x) hxU,
    (hπ x).manifoldMorseIndex_comp (by simp) hcrit.contMDiffAt hcrit.mem_criticalPoints]

end Pullback

end TauCeti
