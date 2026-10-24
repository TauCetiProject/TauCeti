/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic

/-!
# Interior products and paired wedges of rough differential forms

Insertion is an antiderivation of degree `-1` for a fibrewise paired wedge, with sign `(-1)`
raised to the degree of the first factor. The displayed `Fin.cast` reindexes the first term
along the arithmetic equality between the two parenthesizations of the degree sum.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}

/-- Insertion is an antiderivation of degree `-1` for a fibrewise paired wedge.

The first term has degree `k + (l + 1)`, while the result of inserting into the original wedge
is indexed by `k + 1 + l`; the displayed `Fin.cast` along the arithmetic equality
`k + (l + 1) = k + 1 + l` reindexes the first term to the degree of the left-hand side.
The input fibres only need the continuity required by the topological currying theorem, while the
output fibre has the additive and scalar continuity needed to form the paired wedge. -/
theorem bundleInterior_wedgeWith_apply
    {V₁ V₂ V₃ : M → Type*}
    [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
    [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
    [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
    [∀ x, ContinuousAdd (V₁ x)] [∀ x, ContinuousConstSMul ℝ (V₁ x)]
    [∀ x, ContinuousAdd (V₂ x)] [∀ x, ContinuousConstSMul ℝ (V₂ x)]
    [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousConstSMul ℝ (V₃ x)]
    {k l : ℕ} (X : (x : M) → TangentSpace I x)
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (φ : RoughBundleForm I M V₁ (k + 1)) (ψ : RoughBundleForm I M V₂ (l + 1))
    (x : M) (v : Fin (k + 1 + l) → TangentSpace I x) :
    bundleInterior (k := k + 1 + l) X
        (bundleWedgeWith (k := k + 1) (l := l + 1) μ hμ φ ψ) x v =
      bundleWedgeWith (k := k) (l := l + 1) μ hμ (bundleInterior (k := k) X φ) ψ x
          (v ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) •
          bundleWedgeWith (k := k + 1) (l := l) μ hμ φ (bundleInterior (k := l) X ψ) x v := by
  rw [bundleInterior_apply, bundleWedgeWith_apply', bundleWedgeWith_apply',
    bundleWedgeWith_apply', bundleInterior_apply_eq_curryLeftTopological,
    bundleInterior_apply_eq_curryLeftTopological]
  simpa only [ContinuousAlternatingMap.curryLeftTopological_apply_apply,
    Pi.add_apply, Pi.smul_apply, Function.comp_apply] using
    (ContinuousAlternatingMap.curryLeftTopological_pairedWedge (E := TangentSpace I x)
      (μ x) (hμ x) (φ x) (ψ x) (X x) v)

/-- The fixed-coefficient paired wedge is an antiderivation for insertion into its first slot. -/
theorem RoughForm.interior_wedgeWith_apply
    {F₁ F₂ F₃ : Type*} [SeminormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [SeminormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [SeminormedAddCommGroup F₃] [NormedSpace ℝ F₃] {k l : ℕ}
    (X : (x : M) → TangentSpace I x) (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ (k + 1)) (ψ : RoughForm I M F₂ (l + 1))
    (x : M) (v : Fin (k + 1 + l) → TangentSpace I x) :
    (φ.wedgeWith μ ψ).interior X x v =
      (φ.interior X).wedgeWith μ ψ x
          (v ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) • φ.wedgeWith μ (ψ.interior X) x v := by
  have hφ : φ.interior X x = bundleInterior X φ x :=
    congrArg (fun η => η x) (RoughForm.interior_def X φ)
  have hψ : ψ.interior X x = bundleInterior X ψ x :=
    congrArg (fun η => η x) (RoughForm.interior_def X ψ)
  simpa only [RoughForm.interior_apply, RoughForm.wedgeWith_apply', bundleInterior_apply,
    bundleWedgeWith_apply',
    hφ, hψ] using
    (bundleInterior_wedgeWith_apply X (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) φ ψ x v)

/-- The real-valued wedge is an antiderivation for insertion into its first slot. -/
theorem RoughForm.interior_wedge_apply
    {k l : ℕ} (X : (x : M) → TangentSpace I x)
    (φ : RoughForm I M ℝ (k + 1)) (ψ : RoughForm I M ℝ (l + 1))
    (x : M) (v : Fin (k + 1 + l) → TangentSpace I x) :
    (φ.wedge ψ).interior X x v =
      (φ.interior X).wedge ψ x
          (v ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) • φ.wedge (ψ.interior X) x v := by
  simpa only [RoughForm.wedge_def] using
    RoughForm.interior_wedgeWith_apply X (ContinuousLinearMap.mul ℝ ℝ) φ ψ x v

end TauCeti
