/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Smooth Gram pairings of alternating forms

The Gram inner product on real alternating forms varies smoothly with the metric of a
finite-rank Riemannian bundle. Its normalization is the sum over increasing tuples of an
orthonormal frame, rather than over all ordered tuples. In particular, this gives the smooth
fibre pairing needed to integrate inner products of differential forms without choosing an
orientation or replacing their continuous-alternating-map fibres.

The regularity theorem works locally and at every differentiability order. The proof uses
the smooth orthonormal frames constructed by Gram–Schmidt and the pointwise formula
`TauCeti.alternatingFormInner_eq_sum`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [∀ x, FiniteDimensional ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsContMDiffRiemannianBundle I n F V]
  {k : ℕ}

/-- The Gram pairing of two `C^n` sections of the real alternating-form bundle is `C^n`
within a set. No orientation of the original bundle is required. -/
theorem ContMDiffWithinAt.alternatingFormInner_bundle
    {α β : ∀ y, V y [⋀^Fin k]→L[ℝ] ℝ} {s : Set M} {x : M}
    (hα : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (α y)) s x)
    (hβ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (β y)) s x) :
    ContMDiffWithinAt I 𝓘(ℝ) n
      (fun y ↦ TauCeti.alternatingFormInner (V y) k (α y) (β y)) s x := by
  classical
  let : FiniteDimensional ℝ F :=
    (VectorBundle.continuousLinearEquivAt ℝ F V x).finiteDimensional
  let e := trivializationAt F V x
  let b := Module.finBasis ℝ F
  let v : Fin (Module.finrank ℝ F) → ∀ y, V y := fun i y ↦
    if hy : y ∈ e.baseSet then e.orthonormalBasis b ⟨y, hy⟩ i else 0
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  have hv (i) : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F y (v i y)) x :=
    (e.contMDiffOn_orthonormalBasis b i).contMDiffAt (e.open_baseSet.mem_nhds hx)
  have hval (γ : ∀ y, V y [⋀^Fin k]→L[ℝ] ℝ)
      (hγ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
        (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (γ y)) s x)
      (t : powersetCard (Fin (Module.finrank ℝ F)) k) :
      ContMDiffWithinAt I 𝓘(ℝ) n
        (fun y ↦ γ y (fun i ↦ v (powersetCard.ofFinEmbEquiv.symm t i) y)) s x :=
    (contMDiffWithinAt_totalSpace_iff.1 (hγ.continuousAlternatingMap_bundle_apply
      (fun i ↦ (hv _).contMDiffWithinAt))).2
  have hs := contMDiffWithinAt_finsetSum (t := Finset.univ) fun t _ ↦
    (hval α hα t).mul (hval β hβ t)
  have heq (y : M) (hy : y ∈ e.baseSet) :
      (∑ t : powersetCard (Fin (Module.finrank ℝ F)) k,
        α y (fun i ↦ v (powersetCard.ofFinEmbEquiv.symm t i) y) *
          β y (fun i ↦ v (powersetCard.ofFinEmbEquiv.symm t i) y)) =
        TauCeti.alternatingFormInner (V y) k (α y) (β y) := by
    simpa only [v, dite_eq_left hy, Function.comp_def] using
      (TauCeti.alternatingFormInner_eq_sum (e.orthonormalBasis b ⟨y, hy⟩) (α y) (β y)).symm
  exact hs.congr_of_eventuallyEq
    (Filter.mem_of_superset (nhdsWithin_le_nhds (e.open_baseSet.mem_nhds hx))
      fun y hy ↦ (heq y hy).symm) ((heq x hx).symm)

/-- The Gram pairing of two alternating-form sections smooth at a point is smooth there. -/
theorem ContMDiffAt.alternatingFormInner_bundle
    {α β : ∀ y, V y [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (hα : ContMDiffAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (α y)) x)
    (hβ : ContMDiffAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (β y)) x) :
    ContMDiffAt I 𝓘(ℝ) n
      (fun y ↦ TauCeti.alternatingFormInner (V y) k (α y) (β y)) x :=
  ContMDiffWithinAt.alternatingFormInner_bundle hα hβ

/-- The Gram pairing preserves regularity of alternating-form sections on arbitrary sets. -/
theorem ContMDiffOn.alternatingFormInner_bundle
    {α β : ∀ y, V y [⋀^Fin k]→L[ℝ] ℝ} {s : Set M}
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (α y)) s)
    (hβ : ContMDiffOn I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (β y)) s) :
    ContMDiffOn I 𝓘(ℝ) n
      (fun y ↦ TauCeti.alternatingFormInner (V y) k (α y) (β y)) s :=
  fun x hx ↦ (hα x hx).alternatingFormInner_bundle (hβ x hx)

/-- The Gram pairing of smooth real alternating-form sections is smooth. -/
theorem ContMDiff.alternatingFormInner_bundle
    {α β : ∀ y, V y [⋀^Fin k]→L[ℝ] ℝ}
    (hα : ContMDiff I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (α y)))
    (hβ : ContMDiff I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (β y))) :
    ContMDiff I 𝓘(ℝ) n
      (fun y ↦ TauCeti.alternatingFormInner (V y) k (α y) (β y)) :=
  fun x ↦ (hα x).alternatingFormInner_bundle (hβ x)
