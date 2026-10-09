/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.VectorBundle

/-!
# Smooth maps in Euclidean normal-bundle coordinates

The smooth structure on the normal bundle agrees with its ambient coordinates: a map into
the normal bundle is `C^n` exactly when its base component and its ambient normal vector are
`C^n`. In particular, the ambient fibre inclusion and the normal addition map are `C^n`.
This lets tubular maps and their inverses be checked without choosing local normal frames.

Install `normalFiberBundle` locally as in `VectorBundle.lean`. The results use the same
projected normal-coordinate atlas, with an arbitrary fixed model fibre of the codimension.
No compactness or injectivity of the core immersion is required.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., the construction of the normal
  bundle and its addition map preceding Theorem 6.24.
-/

public section

noncomputable section

open Set Function Filter Topology Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M] {f : M → V}

/-- The ambient normal-vector component is `C^n` on the normal bundle of a `C^(n+1)`
immersion, with the projected normal-coordinate atlas. -/
theorem contMDiff_normalBundle_snd
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) n
      (fun p : TotalSpace F (fun x => normalSubspace I f x) => (p.2 : V)) := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  intro p
  let e := normalBundleTrivialization (hf.of_le le_add_self) himm hdim p.proj
  have hid := (Bundle.contMDiffAt_totalSpace.mp
    (contMDiffAt_id (I := I.prod 𝓘(ℝ, F)) (n := n)
      (x := p)))
  have hc : ContMDiffAt (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) n (fun q => (e q).2) p := by
    simpa only [normalFiberBundle_trivializationAt, id_eq, e] using hid.2
  have hproj := (contMDiff_normalSubspace_starProjection hf himm).contMDiffAt.comp p hid.1
  have hv := (normalFiberEquiv hdim p.proj
    (himm p.proj)).symm.toContinuousLinearMap.contMDiff.contMDiffAt.comp p hc
  have hval := (normalSubspace I f p.proj).subtypeL.contMDiff.contMDiffAt.comp p hv
  apply (hproj.clm_apply hval).congr_of_eventuallyEq
  have hp : p.proj ∈ e.baseSet := by simp [e]
  have hevent := hid.1.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hp)
  filter_upwards [hevent] with q hq
  have hx : IsUnit (normalCompression I f p.proj q.proj) :=
    (mem_normalBundleTrivialization_baseSet (hf.of_le le_add_self) himm hdim
      p.proj q.proj).mp hq
  simpa [e, normalBundleTrivialization_apply] using
    (starProjection_normalCoordinateMap p.proj q.proj
      ((finrank_normalSubspace (himm p.proj)).trans
        (finrank_normalSubspace (himm q.proj)).symm) hx q.2.property).symm

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- Smoothness within a set of a normal-bundle-valued map can be tested on its base
component and its ambient normal vector. -/
theorem contMDiffWithinAt_normalBundle_iff
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {g : N → TotalSpace F (fun x => normalSubspace I f x)} {s : Set N} {x : N} :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    ContMDiffWithinAt J (I.prod 𝓘(ℝ, F)) n g s x ↔
      ContMDiffWithinAt J I n (fun y => (g y).proj) s x ∧
      ContMDiffWithinAt J 𝓘(ℝ, V) n (fun y => ((g y).2 : V)) s x := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  constructor
  · intro hg
    exact ⟨(Bundle.contMDiffWithinAt_totalSpace.mp hg).1,
      (contMDiff_normalBundle_snd hf himm hdim).contMDiffAt.comp_contMDiffWithinAt x hg⟩
  · rintro ⟨hbase, hvec⟩
    rw [Bundle.contMDiffWithinAt_totalSpace]
    refine ⟨hbase, ?_⟩
    have hcoord := (contMDiffAt_normalCoordinateMap hf himm (g x).proj
      (by simp)).comp_contMDiffWithinAt x hbase
    have hfixed := (normalFiberEquiv hdim (g x).proj
      (himm (g x).proj)).toContinuousLinearMap.contMDiff (n := n)
    convert hfixed.contMDiffAt.comp_contMDiffWithinAt x (hcoord.clm_apply hvec) using 1
    funext y
    simp only [normalFiberBundle_trivializationAt, normalBundleTrivialization_apply,
      Function.comp_apply, ContinuousLinearEquiv.coe_coe]

/-- Smoothness at a point of a normal-bundle-valued map is equivalent to smoothness of
its base component and its ambient normal vector. -/
theorem contMDiffAt_normalBundle_iff
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {g : N → TotalSpace F (fun x => normalSubspace I f x)} {x : N} :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    ContMDiffAt J (I.prod 𝓘(ℝ, F)) n g x ↔
      ContMDiffAt J I n (fun y => (g y).proj) x ∧
      ContMDiffAt J 𝓘(ℝ, V) n (fun y => ((g y).2 : V)) x := by
  simp only [← contMDiffWithinAt_univ]
  exact contMDiffWithinAt_normalBundle_iff hf himm hdim

/-- A map into the normal bundle is `C^n` on a set exactly when both ambient components
are `C^n` on that set. -/
theorem contMDiffOn_normalBundle_iff
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {g : N → TotalSpace F (fun x => normalSubspace I f x)} {s : Set N} :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    ContMDiffOn J (I.prod 𝓘(ℝ, F)) n g s ↔
      ContMDiffOn J I n (fun y => (g y).proj) s ∧
      ContMDiffOn J 𝓘(ℝ, V) n (fun y => ((g y).2 : V)) s := by
  simp only [ContMDiffOn, contMDiffWithinAt_normalBundle_iff hf himm hdim, forall_and]

/-- A map into the normal bundle is `C^n` exactly when its base component and its ambient
normal vector are `C^n`. -/
theorem contMDiff_normalBundle_iff
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {g : N → TotalSpace F (fun x => normalSubspace I f x)} :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    ContMDiff J (I.prod 𝓘(ℝ, F)) n g ↔
      ContMDiff J I n (fun y => (g y).proj) ∧
      ContMDiff J 𝓘(ℝ, V) n (fun y => ((g y).2 : V)) := by
  simp only [ContMDiff, contMDiffAt_normalBundle_iff hf himm hdim, forall_and]

/-- Normal addition is `C^n` on the entire normal bundle of a `C^(n+1)` immersion.
Restricting this map to an injective normal tube gives the forward tubular map. -/
theorem contMDiff_normalBundle_add
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) n
      (fun p : TotalSpace F (fun x => normalSubspace I f x) => f p.proj + (p.2 : V)) := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  exact ((hf.of_le (by simp)).comp (Bundle.contMDiff_proj _)).add
    (contMDiff_normalBundle_snd hf himm hdim)

end TauCeti
