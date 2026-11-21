/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.BilinMap
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Smoothness of invariant bilinear maps on associated vector bundles

A `G`-invariant continuous bilinear map `β : F × F → W` induces a bilinear map on every fibre of
the associated vector bundle `P ×_G F` (`TauCeti.AssociatedBundle.bilinMap`). In every
associated chart this fibre map is `β` applied to the chart coordinates, with no dependence on the
base point. So the pairing of two smooth maps into the associated bundle, over a common base map,
is smooth (`ContMDiff.bilinMap_associatedBundle`). In particular an invariant bilinear form on
the model fibre induces a smooth fibre pairing on the associated vector bundle. Smoothness is
measured in the charts of the associated fibre bundle; no smoothness of the principal bundle or of
the action is needed.

The underlying step is stated once in general: a function which near `x` is a fixed smooth map
applied to the chart coordinates of two smooth maps into the associated bundle is smooth
(`TauCeti.AssociatedBundle.contMDiffWithinAt_of_trivializationAt`). The smoothness of the bracket
of the adjoint bundle uses it as well.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §10.7.
-/

public section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace TauCeti.AssociatedBundle

variable {n : ℕ∞ω} {𝕜 B G F W EB HB : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [DistribMulAction G F] [ContinuousSMul G F]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {β : F →L[𝕜] F →L[𝕜] W}
  {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {v w : ∀ m, AssociatedBundle G P F (b m)} {s : Set M} {x : M}

/-- **Fibrewise operations read in charts by a fixed smooth map are smooth.** Let `f` be a function
on `M` which, wherever the base map `b` lies in the chart at `b x`, is a fixed smooth map `φ`
applied to the chart coordinates of two maps into the associated bundle. If these maps are smooth
within `s` at `x`, then so is `f`. -/
theorem contMDiffWithinAt_of_trivializationAt {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace 𝕜 Z] {f : M → Z} {φ : F × F → Z} (hφ : ContDiff 𝕜 n φ)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F (AssociatedBundle G P F))) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F (AssociatedBundle G P F))) s x)
    (hf : ∀ y, b y ∈ (trivializationAt G P (b x)).baseSet →
      f y = φ ((trivializationAt F (AssociatedBundle G P F) (b x) ⟨b y, v y⟩).2,
        (trivializationAt F (AssociatedBundle G P F) (b x) ⟨b y, w y⟩).2)) :
    ContMDiffWithinAt IM 𝓘(𝕜, Z) n f s x := by
  obtain ⟨hb, hv'⟩ := contMDiffWithinAt_totalSpace_iff.mp hv
  have hw' := (contMDiffWithinAt_totalSpace_iff.mp hw).2
  have hx := mem_baseSet_trivializationAt G P (b x)
  have hmem := hb.continuousWithinAt.preimage_mem_nhdsWithin
    ((trivializationAt G P (b x)).open_baseSet.mem_nhds hx)
  -- Near `x`, `f` is `φ` applied to the coordinates in the chart at `b x`.
  exact (hφ.contMDiff.contMDiffAt.comp_contMDiffWithinAt x
    (hv'.prodMk_space hw')).congr_of_eventuallyEq (Filter.mem_of_superset hmem hf) (hf x hx)

/-- **Invariant pairings of smooth maps into an associated bundle are smooth**, within a set:
the fibre map of a `G`-invariant bilinear map `β`, applied to two maps into the associated bundle
over a common base map, smooth within `s` at `x`, is smooth within `s` at `x`. -/
theorem _root_.ContMDiffWithinAt.bilinMap_associatedBundle
    (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F (AssociatedBundle G P F))) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F (AssociatedBundle G P F))) s x) :
    ContMDiffWithinAt IM 𝓘(𝕜, W) n (fun m ↦ bilinMap G P β (b m) (v m) (w m)) s x :=
  contMDiffWithinAt_of_trivializationAt β.isBoundedBilinearMap.contDiff hv hw fun y hy ↦
    (bilinMap_trivializationAt hβ hy (v y) (w y)).symm

/-- Invariant pairings of maps into an associated bundle smooth at a point are smooth there. -/
theorem _root_.ContMDiffAt.bilinMap_associatedBundle
    (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    (hv : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F (AssociatedBundle G P F))) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F (AssociatedBundle G P F))) x) :
    ContMDiffAt IM 𝓘(𝕜, W) n (fun m ↦ bilinMap G P β (b m) (v m) (w m)) x := by
  rw [← contMDiffWithinAt_univ] at *
  exact hv.bilinMap_associatedBundle hβ hw

/-- Invariant pairings of maps into an associated bundle smooth on a set are smooth there. -/
theorem _root_.ContMDiffOn.bilinMap_associatedBundle
    (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    (hv : ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F (AssociatedBundle G P F))) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F (AssociatedBundle G P F))) s) :
    ContMDiffOn IM 𝓘(𝕜, W) n (fun m ↦ bilinMap G P β (b m) (v m) (w m)) s :=
  fun x hx ↦ (hv x hx).bilinMap_associatedBundle hβ (hw x hx)

/-- **The invariant pairing of two smooth maps into an associated bundle is smooth.** -/
theorem _root_.ContMDiff.bilinMap_associatedBundle
    (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    (hv : ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F (AssociatedBundle G P F))))
    (hw : ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F (AssociatedBundle G P F)))) :
    ContMDiff IM 𝓘(𝕜, W) n (fun m ↦ bilinMap G P β (b m) (v m) (w m)) :=
  fun x ↦ (hv x).bilinMap_associatedBundle hβ (hw x)

end TauCeti.AssociatedBundle
