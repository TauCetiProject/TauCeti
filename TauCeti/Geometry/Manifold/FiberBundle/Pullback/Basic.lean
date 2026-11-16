/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.Pullback

/-!
# Pullbacks of smooth fibre bundles

Let `E` be a fibre bundle over a manifold `B` modelled on `IB`, whose model fibre `F` is a manifold
modelled on `IF`, and let `f : B' → B` be a map from a manifold modelled on `IB'`. Mathlib's
pullback bundle `f *ᵖ E` over `B'` has fibre `E (f x)` over `x`, and its atlas consists of the
pullbacks `e.pullback f` of the trivializations of `E`.

When `E` is a `C^n` fibre bundle and `f` is `C^n`, the pullback is a `C^n` fibre bundle
(`TauCeti.ContMDiffFiberBundle.pullback`): the coordinate change between `e.pullback f` and
`e'.pullback f` over `x` is the coordinate change between `e` and `e'` over `f x`. Its total space,
charted through the fibre by `TauCeti.ManifoldTotalSpace F (f *ᵖ E)`, has the smooth universal
property of a pullback: a map into it is `C^n` exactly when its projection to `B'` and its
composite with the canonical map `Bundle.Pullback.lift f` to the total space of `E` are `C^n`
(`TauCeti.ManifoldTotalSpace.contMDiffWithinAt_pullback_iff`). In particular the canonical map is
`C^n` (`TauCeti.ManifoldTotalSpace.contMDiff_pullbackLift`).

Combined with `TauCeti.PrincipalBundle.pullback`, this makes the pullback of a `C^n` principal
`G`-bundle along a `C^n` map a `C^n` principal `G`-bundle. A map into the total space of `P` that
covers `f` and is equivariant fibrewise is the same fibrewise data as a map into the total space
of `f *ᵖ P`, and the universal property says that the two are `C^n` together, once the map on the
base is.

## Main results

* `TauCeti.ContMDiffFiberBundle.pullback`: the pullback of a `C^n` fibre bundle along a `C^n` map
  is a `C^n` fibre bundle.
* `TauCeti.ManifoldTotalSpace.contMDiffWithinAt_pullback_iff` and its variants at a point and
  everywhere: maps into the total space of a pullback are `C^n` exactly when their projection and
  their lift to the original total space are.
* `TauCeti.ManifoldTotalSpace.contMDiff_pullbackLift`: the canonical map from the total space of
  the pullback to the original total space is `C^n`.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 2 (induced bundles and their universal property) and Chapter 4 (induced principal
  bundles).
* The smooth universal property follows `Bundle.Pullback.contMDiffAt_iff`, for normed fibres with
  Mathlib's charts, and the coordinate-change computation follows Mathlib's
  `ContMDiffVectorBundle.pullback`.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ∞ω} {𝕜 B B' F M : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EB' : Type*} [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB'] {HB' : Type*} [TopologicalSpace HB']
  {IB' : ModelWithCorners 𝕜 EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B']
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [∀ b, Nonempty (E b)]

variable (n IB' IF) in
/-- **The pullback of a `C^n` fibre bundle is a `C^n` fibre bundle.** For a `C^n` fibre bundle `E`
over `B` with a manifold `F` as fibre and a `C^n` map `f : B' → B`, the pullback `f *ᵖ E` is a
`C^n` fibre bundle over `B'`. -/
instance ContMDiffFiberBundle.pullback [ContMDiffFiberBundle n F E IB IF]
    (f : C^n⟮IB', B'; IB, B⟯) : ContMDiffFiberBundle n F ((f : B' → B) *ᵖ E) IB' IF where
  contMDiffOn_coordChange := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    refine ((ContMDiffFiberBundle.contMDiffOn_coordChange e e').comp
      (f.contMDiff.contMDiffOn.prodMap contMDiffOn_id) fun p hp ↦ ⟨hp.1, mem_univ _⟩).congr ?_
    rintro ⟨x, v⟩ ⟨hx, -⟩
    exact e.coordChange_pullback e' f hx.1 v

namespace ManifoldTotalSpace

section UniversalProperty

variable {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] (f : K)

/-- **Maps into the total space of a pullback.** A map `q` into the total space of `f *ᵖ E` is
`C^n` within a set at a point exactly when its projection to `B'` and its composite with the
canonical map `Bundle.Pullback.lift f` to the total space of `E` are `C^n` there, provided that `f`
is `C^n` at the base point. -/
theorem contMDiffWithinAt_pullback_iff {q : M → TotalSpace F ((f : B' → B) *ᵖ E)} {s : Set M}
    {x₀ : M} (hf : ContMDiffAt IB' IB n f (q x₀).proj) :
    ContMDiffWithinAt IM (IB'.prod IF) n (fun x ↦ homeomorph F ((f : B' → B) *ᵖ E) (q x)) s x₀ ↔
      ContMDiffWithinAt IM IB' n (fun x ↦ (q x).proj) s x₀ ∧
        ContMDiffWithinAt IM (IB.prod IF) n (fun x ↦ homeomorph F E (Pullback.lift f (q x))) s
          x₀ := by
  simp only [ManifoldTotalSpace.contMDiffWithinAt_iff, trivializationAt,
    FiberBundle.pullback_trivializationAt', Trivialization.pullback_apply, Pullback.lift_proj]
  exact ⟨fun ⟨hq, hcoord⟩ ↦ ⟨hq, hf.comp_contMDiffWithinAt x₀ hq, hcoord⟩,
    fun ⟨hq, _, hcoord⟩ ↦ ⟨hq, hcoord⟩⟩

/-- A map `q` into the total space of `f *ᵖ E` is `C^n` at a point exactly when its projection to
`B'` and its composite with `Bundle.Pullback.lift f` are `C^n` there, provided that `f` is `C^n` at
the base point. -/
theorem contMDiffAt_pullback_iff {q : M → TotalSpace F ((f : B' → B) *ᵖ E)} {x₀ : M}
    (hf : ContMDiffAt IB' IB n f (q x₀).proj) :
    ContMDiffAt IM (IB'.prod IF) n (fun x ↦ homeomorph F ((f : B' → B) *ᵖ E) (q x)) x₀ ↔
      ContMDiffAt IM IB' n (fun x ↦ (q x).proj) x₀ ∧
        ContMDiffAt IM (IB.prod IF) n (fun x ↦ homeomorph F E (Pullback.lift f (q x))) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]
  exact contMDiffWithinAt_pullback_iff f hf

/-- A map `q` into the total space of `f *ᵖ E` is `C^n` exactly when its projection to `B'` and its
composite with `Bundle.Pullback.lift f` are `C^n`, provided that `f` is `C^n`. -/
theorem contMDiff_pullback_iff (hf : ContMDiff IB' IB n f)
    {q : M → TotalSpace F ((f : B' → B) *ᵖ E)} :
    ContMDiff IM (IB'.prod IF) n (fun x ↦ homeomorph F ((f : B' → B) *ᵖ E) (q x)) ↔
      ContMDiff IM IB' n (fun x ↦ (q x).proj) ∧
        ContMDiff IM (IB.prod IF) n (fun x ↦ homeomorph F E (Pullback.lift f (q x))) := by
  simp only [ContMDiff, ← forall_and]
  exact forall_congr' fun x ↦ contMDiffAt_pullback_iff f (hf _)

variable (n IF) in
/-- The canonical map `Bundle.Pullback.lift f` from the total space of `f *ᵖ E` to the total space
of `E` is `C^n` for the charts through the fibre, when `f` is `C^n`. -/
theorem contMDiff_pullbackLift (hf : ContMDiff IB' IB n f) :
    ContMDiff (IB'.prod IF) (IB.prod IF) n fun z : ManifoldTotalSpace F ((f : B' → B) *ᵖ E) ↦
      homeomorph F E (Pullback.lift f ((homeomorph F ((f : B' → B) *ᵖ E)).symm z)) :=
  ((contMDiff_pullback_iff f hf).1 <| contMDiff_id.congr fun z ↦ by simp).2

end UniversalProperty

end ManifoldTotalSpace

end TauCeti
