/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Analysis.Calculus.Morse.Basic

/-!
# Morse functions on smooth manifolds

This file lifts nondegenerate critical points and Morse functions from normed spaces to smooth
manifolds without boundary. A critical point is nondegenerate when the coordinate expression of
the function in the preferred extended chart has a nondegenerate critical point in the sense of
`TauCeti.IsNondegenerateCriticalPoint`. The latter notion is invariant under smooth changes of
coordinates, so this is the usual intrinsic definition.

`IsMorseOn I f s` additionally requires `f` to be smooth on `s` and every critical point in `s`
to be nondegenerate. The smoothness condition is what distinguishes a Morse function from the
weaker normed-space predicate `HasNondegenerateCriticalPointsOn`, which deliberately imposes no
regularity away from critical points. On a normed vector space, the manifold definitions reduce
exactly to the existing calculus definitions.

This is the manifold-level starting point for Morse homology: stable and unstable manifolds,
Morse--Smale trajectory spaces, and the Morse differential are attached to a Morse function on a
manifold, rather than to a function on one global coordinate space.

## Main declarations

* `TauCeti.IsManifoldNondegenerateCriticalPoint`: a nondegenerate critical point of a
  real-valued function on a smooth manifold.
* `TauCeti.IsMorseOn`: a smooth function whose critical points in a set are nondegenerate.
* `TauCeti.IsMorse`: a Morse function on the whole manifold.
* `TauCeti.isManifoldNondegenerateCriticalPoint_modelSpace_iff` and
  `TauCeti.isMorseOn_modelSpace_iff`: comparison with the normed-space definitions.

The definition follows Audin--Damian, *Morse Theory and Floer Homology*, Chapter 1.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
variable [TopologicalSpace M] [ChartedSpace H M]
variable {f g : M → ℝ} {s t : Set M} {x : M}

/-- A point `x` is a nondegenerate critical point of `f` when, in the preferred extended chart at
`x`, the coordinate expression of `f` has a nondegenerate critical point. As with `mfderiv` and
`ContMDiff`, the definition carries no smoothness or boundary hypotheses; it is the intended
chart-independent notion when `I.Boundaryless` and `IsManifold I ∞ M` hold, and results relying on
intrinsic meaning assume these. For models with boundary the unconstrained Hessian is not the
boundary Morse condition, which is a different theory. -/
def IsManifoldNondegenerateCriticalPoint (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) :
    Prop :=
  IsNondegenerateCriticalPoint (f ∘ (extChartAt I x).symm) (extChartAt I x x)

/-- The coordinate characterization of a nondegenerate critical point. -/
theorem isManifoldNondegenerateCriticalPoint_iff (I : ModelWithCorners ℝ E H) :
    IsManifoldNondegenerateCriticalPoint I f x ↔
      IsNondegenerateCriticalPoint (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
  Iff.rfl

/-- Negating a function preserves its nondegenerate critical points. -/
theorem IsManifoldNondegenerateCriticalPoint.neg {I : ModelWithCorners ℝ E H}
    (h : IsManifoldNondegenerateCriticalPoint I f x) :
    IsManifoldNondegenerateCriticalPoint I (-f) x := by
  rw [isManifoldNondegenerateCriticalPoint_iff] at h ⊢
  have hfun : (-f) ∘ (extChartAt I x).symm = -(f ∘ (extChartAt I x).symm) := by
    funext y
    rfl
  rw [hfun]
  exact h.neg

/-- Being a nondegenerate critical point is invariant under negating the function. -/
@[simp]
theorem isManifoldNondegenerateCriticalPoint_neg_iff {I : ModelWithCorners ℝ E H} :
    IsManifoldNondegenerateCriticalPoint I (-f) x ↔ IsManifoldNondegenerateCriticalPoint I f x :=
  ⟨fun h ↦ by simpa using h.neg, IsManifoldNondegenerateCriticalPoint.neg⟩

/-- On a normed vector space with its self-model manifold structure, a manifold nondegenerate
critical point is exactly a nondegenerate critical point in the existing calculus sense. -/
@[simp]
theorem isManifoldNondegenerateCriticalPoint_modelSpace_iff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {h : V → ℝ} {v : V} :
    IsManifoldNondegenerateCriticalPoint (modelWithCornersSelf ℝ V) h v ↔
      IsNondegenerateCriticalPoint h v := by
  simp only [IsManifoldNondegenerateCriticalPoint, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_id, id_eq]

/-- A function is Morse on `s` when it is smooth there and every critical point in `s` is a
nondegenerate critical point. Criticality is tested in the same preferred coordinates used by
`IsManifoldNondegenerateCriticalPoint`; on a vector space this is exactly `fderiv ℝ f x = 0`. -/
def IsMorseOn (I : ModelWithCorners ℝ E H) (f : M → ℝ) (s : Set M) : Prop :=
  ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞ f s ∧
    ∀ x, x ∈ s →
      fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 →
        IsManifoldNondegenerateCriticalPoint I f x

/-- The introduction and elimination rule for a function being Morse on a set. -/
theorem isMorseOn_iff {I : ModelWithCorners ℝ E H} :
    IsMorseOn I f s ↔
      ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞ f s ∧
        ∀ x, x ∈ s →
          fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 →
            IsManifoldNondegenerateCriticalPoint I f x :=
  Iff.rfl

/-- A function which is Morse on a set is smooth there. -/
theorem IsMorseOn.contMDiffOn {I : ModelWithCorners ℝ E H}
    (h : IsMorseOn I f s) : ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞ f s :=
  h.1

/-- Every critical point of a function which is Morse on `s` is a nondegenerate critical point. -/
theorem IsMorseOn.isManifoldNondegenerateCriticalPoint {I : ModelWithCorners ℝ E H}
    (h : IsMorseOn I f s) (hx : x ∈ s)
    (hcrit : fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0) :
    IsManifoldNondegenerateCriticalPoint I f x :=
  h.2 x hx hcrit

/-- The restriction of a Morse function to a smaller set is Morse there. -/
theorem IsMorseOn.mono {I : ModelWithCorners ℝ E H}
    (h : IsMorseOn I f t) (hst : s ⊆ t) : IsMorseOn I f s :=
  ⟨h.contMDiffOn.mono hst, fun _ hx ↦ h.isManifoldNondegenerateCriticalPoint (hst hx)⟩

/-- Negating a function preserves the property of being Morse on a set. -/
theorem IsMorseOn.neg {I : ModelWithCorners ℝ E H}
    (h : IsMorseOn I f s) : IsMorseOn I (-f) s := by
  have hneg : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : ℝ ↦ -y) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  refine ⟨hneg.comp_contMDiffOn h.contMDiffOn, ?_⟩
  intro x hx hcrit
  apply (h.isManifoldNondegenerateCriticalPoint hx ?_).neg
  have hfun : (-f) ∘ (extChartAt I x).symm = -(f ∘ (extChartAt I x).symm) := by
    funext y
    rfl
  rw [hfun, fderiv_neg] at hcrit
  simpa using congrArg Neg.neg hcrit

/-- Being Morse on a set is invariant under negating the function. -/
@[simp]
theorem isMorseOn_neg_iff {I : ModelWithCorners ℝ E H} :
    IsMorseOn I (-f) s ↔ IsMorseOn I f s :=
  ⟨fun h ↦ by simpa using h.neg, IsMorseOn.neg⟩

/-- On a normed vector space, being Morse on `s` means being smooth on `s` and having
nondegenerate critical points there in the existing calculus sense. -/
@[simp]
theorem isMorseOn_modelSpace_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : V → ℝ} {u : Set V} :
    IsMorseOn (modelWithCornersSelf ℝ V) h u ↔
      ContDiffOn ℝ ∞ h u ∧ HasNondegenerateCriticalPointsOn h u := by
  simp only [IsMorseOn, contMDiffOn_iff_contDiffOn, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_id,
    isManifoldNondegenerateCriticalPoint_modelSpace_iff, id_eq,
    hasNondegenerateCriticalPointsOn_iff]

/-- A Morse function is a function which is Morse on the whole manifold. -/
def IsMorse (I : ModelWithCorners ℝ E H) (f : M → ℝ) : Prop :=
  IsMorseOn I f univ

/-- A function is Morse exactly when it is smooth and all of its critical points are
nondegenerate. -/
theorem isMorse_iff {I : ModelWithCorners ℝ E H} :
    IsMorse I f ↔
      ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ f ∧
        ∀ x,
          fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 →
            IsManifoldNondegenerateCriticalPoint I f x := by
  simp [IsMorse, isMorseOn_iff, contMDiffOn_univ]

/-- A Morse function is smooth. -/
theorem IsMorse.contMDiff {I : ModelWithCorners ℝ E H}
    (h : IsMorse I f) : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ f := by
  rw [IsMorse] at h
  rw [← contMDiffOn_univ]
  exact h.contMDiffOn

/-- Every critical point of a Morse function is a nondegenerate critical point. -/
theorem IsMorse.isManifoldNondegenerateCriticalPoint {I : ModelWithCorners ℝ E H}
    (h : IsMorse I f)
    (hcrit : fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0) :
    IsManifoldNondegenerateCriticalPoint I f x := by
  rw [IsMorse] at h
  exact h.isManifoldNondegenerateCriticalPoint (mem_univ x) hcrit

/-- A Morse function is Morse on every subset. -/
theorem IsMorse.isMorseOn {I : ModelWithCorners ℝ E H}
    (h : IsMorse I f) (s : Set M) : IsMorseOn I f s := by
  rw [IsMorse] at h
  exact h.mono (subset_univ s)

/-- Negating a Morse function gives a Morse function. -/
theorem IsMorse.neg {I : ModelWithCorners ℝ E H}
    (h : IsMorse I f) : IsMorse I (-f) := by
  rw [IsMorse] at h ⊢
  exact h.neg

/-- Being Morse is invariant under negating the function. -/
@[simp]
theorem isMorse_neg_iff {I : ModelWithCorners ℝ E H} :
    IsMorse I (-f) ↔ IsMorse I f :=
  ⟨fun h ↦ by simpa using h.neg, IsMorse.neg⟩

/-- On a normed vector space, a Morse function is exactly a smooth function all of whose critical
points are nondegenerate in the existing calculus sense. -/
@[simp]
theorem isMorse_modelSpace_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : V → ℝ} :
    IsMorse (modelWithCornersSelf ℝ V) h ↔
      ContDiff ℝ ∞ h ∧ HasNondegenerateCriticalPointsOn h univ := by
  rw [IsMorse, isMorseOn_modelSpace_iff, contDiffOn_univ]

end TauCeti

end
