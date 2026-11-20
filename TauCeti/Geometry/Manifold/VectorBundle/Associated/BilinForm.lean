/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.BilinForm
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Smoothness of invariant bilinear maps on associated vector bundles

A `G`-invariant continuous bilinear map `β : F × F → W` induces a bilinear map on every fibre of
the associated vector bundle `P ×_G F` (`TauCeti.AssociatedBundle.bilinForm`). In every
associated chart this fibre map is `β` applied to the chart coordinates, with no dependence on the
base point. So the pairing of two smooth maps into the associated bundle, over a common base map,
is smooth (`ContMDiff.bilinForm_associatedBundle`). In particular an invariant bilinear form on
the model fibre induces a smooth fibre pairing on the associated vector bundle. Smoothness is
measured in the charts of the associated fibre bundle; no smoothness of the principal bundle or of
the action is needed.

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

/-- **Invariant pairings of smooth maps into an associated bundle are smooth**, within a set:
the fibre map of a `G`-invariant bilinear map `β`, applied to two maps into the associated bundle
over a common base map, smooth within `s` at `x`, is smooth within `s` at `x`. -/
theorem _root_.ContMDiffWithinAt.bilinForm_associatedBundle
    (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F (AssociatedBundle G P F))) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F (AssociatedBundle G P F))) s x) :
    ContMDiffWithinAt IM 𝓘(𝕜, W) n (fun m ↦ bilinForm G P β (b m) (v m) (w m)) s x := by
  obtain ⟨hb, hv'⟩ := contMDiffWithinAt_totalSpace_iff.mp hv
  have hw' := (contMDiffWithinAt_totalSpace_iff.mp hw).2
  have hx := mem_baseSet_trivializationAt G P (b x)
  have hmem := hb.continuousWithinAt.preimage_mem_nhdsWithin
    ((trivializationAt G P (b x)).open_baseSet.mem_nhds hx)
  -- Near `x`, the pairing is `β` applied to the coordinates in the chart at `b x`.
  apply (β.isBoundedBilinearMap.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt x
    (hv'.prodMk_space hw')).congr_of_eventuallyEq
  · filter_upwards [hmem] with y hy
    exact (bilinForm_trivializationAt hβ hy (v y) (w y)).symm
  · exact (bilinForm_trivializationAt hβ hx (v x) (w x)).symm

/-- Invariant pairings of maps into an associated bundle smooth at a point are smooth there. -/
theorem _root_.ContMDiffAt.bilinForm_associatedBundle
    (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    (hv : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F (AssociatedBundle G P F))) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F (AssociatedBundle G P F))) x) :
    ContMDiffAt IM 𝓘(𝕜, W) n (fun m ↦ bilinForm G P β (b m) (v m) (w m)) x := by
  rw [← contMDiffWithinAt_univ] at *
  exact hv.bilinForm_associatedBundle hβ hw

/-- Invariant pairings of maps into an associated bundle smooth on a set are smooth there. -/
theorem _root_.ContMDiffOn.bilinForm_associatedBundle
    (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    (hv : ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F (AssociatedBundle G P F))) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F (AssociatedBundle G P F))) s) :
    ContMDiffOn IM 𝓘(𝕜, W) n (fun m ↦ bilinForm G P β (b m) (v m) (w m)) s :=
  fun x hx ↦ (hv x hx).bilinForm_associatedBundle hβ (hw x hx)

/-- **The invariant pairing of two smooth maps into an associated bundle is smooth.** -/
theorem _root_.ContMDiff.bilinForm_associatedBundle
    (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    (hv : ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F (AssociatedBundle G P F))))
    (hw : ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F (AssociatedBundle G P F)))) :
    ContMDiff IM 𝓘(𝕜, W) n (fun m ↦ bilinForm G P β (b m) (v m) (w m)) :=
  fun x ↦ (hv x).bilinForm_associatedBundle hβ (hw x)

end TauCeti.AssociatedBundle
