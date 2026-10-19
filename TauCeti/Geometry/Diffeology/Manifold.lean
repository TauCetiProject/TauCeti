/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Geometry.Diffeology.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Parametrization

/-!
# The diffeology of a smooth manifold

`manifoldDiffeology E M` equips a finite-dimensional boundaryless real manifold with the
native diffeology whose plots are its smooth Cartesian parametrizations. Its D-topology is
the original manifold topology. Smoothness between these diffeologies is precisely ordinary
manifold smoothness, so this construction does not depend on a choice of smooth atlas.

As for Mathlib's `NormedSpace.toDiffeology`, the construction is not a global instance:
`IsContMDiffCompatible` records agreement with a diffeology already installed on a manifold.
This avoids conflicting diffeologies on normed spaces and products. In particular, the normed
space construction agrees with the manifold construction.

After `open TauCeti`, the plot conversion lemmas support dot notation: `hp.isPlot` turns
a smooth Cartesian parametrization into a plot, and `hp.contMDiff` turns a plot into a smooth
manifold map. The equivalence is also available as `isPlot_iff_contMDiff`.

The plot axioms and compatibility interface follow Mathlib's
`DiffeologicalSpace.ofCorePlotsOn` and `Diffeology.IsContDiffCompatible`.
-/

public noncomputable section

open Set Function Diffeology
open scoped Manifold Topology ContDiff

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (M : Type*) [tM : TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The standard diffeology of a finite-dimensional boundaryless real smooth manifold.
Its plots are smooth manifold maps, and its D-topology is the given topology. -/
@[instance_reducible]
def manifoldDiffeology : DiffeologicalSpace M :=
  .ofCorePlotsOn {
    isPlotOn := fun {_ u} _ p => ContMDiffOn 𝓘(ℝ, _) 𝓘(ℝ, E) ∞ p u
    isPlotOn_congr := fun _ _ _ h => contMDiffOn_congr h
    isPlot := fun p => ContMDiff 𝓘(ℝ, _) 𝓘(ℝ, E) ∞ p
    isPlotOn_univ := contMDiffOn_univ
    isPlot_const := fun _ => contMDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf => hp.comp hf.contMDiffOn h
    locality := fun _ _ h x hx => by
      obtain ⟨v, hv, hxv, hp⟩ := h x hx
      exact (hp.contMDiffAt (hv.mem_nhds hxv)).contMDiffWithinAt
    dTopology := tM
    isOpen_iff_preimages_plots := fun {u} => by
      refine ⟨fun hu _ p hp => IsOpen.preimage hp.continuous hu,
        fun h => isOpen_iff_mem_nhds.mpr ?_⟩
      intro x hx
      obtain ⟨e, hs, he, hp, _⟩ := exists_contMDiff_parametrization (E := E) x
      have ho := (e.isOpenEmbedding hs).isOpenMap _ (h e hp)
      have hm : x ∈ e '' (e ⁻¹' u) := ⟨e.symm x, by simpa [e.right_inv he], e.right_inv he⟩
      exact Filter.mem_of_superset (ho.mem_nhds hm) (image_preimage_subset _ _) }

variable {E M}

/-- A diffeology agrees with the smooth manifold structure if its Cartesian plots are
exactly the smooth manifold maps. -/
class IsContMDiffCompatible (E : outParam (Type*)) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [DiffeologicalSpace M] : Prop where
  /-- A Cartesian parametrization is a plot exactly when it is smooth in manifold charts. -/
  isPlot_iff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M} :
    IsPlot p ↔ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p

section

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

variable [DiffeologicalSpace M] [IsContMDiffCompatible E M]

/-- A Cartesian parametrization is a plot exactly when it is smooth as a manifold map. -/
theorem isPlot_iff_contMDiff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M} :
    IsPlot p ↔ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p :=
  IsContMDiffCompatible.isPlot_iff

/-- A smooth Cartesian parametrization of a compatible manifold is a plot. -/
@[fun_prop]
protected theorem ContMDiff.isPlot {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M}
    (hp : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p) : IsPlot p :=
  isPlot_iff_contMDiff.mpr hp

/-- A plot of a compatible manifold is smooth as a manifold map. -/
protected theorem Diffeology.IsPlot.contMDiff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M}
    (hp : IsPlot p) : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p :=
  isPlot_iff_contMDiff.mp hp

end

instance : @IsContMDiffCompatible E _ _ M _ _ (manifoldDiffeology E M) := by
  let := manifoldDiffeology E M
  exact ⟨Iff.rfl⟩

instance : @IsDTopologyCompatible M _ (manifoldDiffeology E M) := by
  let := manifoldDiffeology E M
  exact ⟨rfl⟩

/-- Characterization of the manifold diffeology by its plots. -/
theorem isContMDiffCompatible_iff_eq_manifoldDiffeology [d : DiffeologicalSpace M] :
    IsContMDiffCompatible (E := E) (M := M) ↔ d = manifoldDiffeology E M := by
  refine ⟨fun h => ?_, fun h => h ▸ inferInstance⟩
  ext n p
  exact h.isPlot_iff

/-- The manifold construction agrees with Mathlib's standard normed-space diffeology. -/
@[simp]
theorem manifoldDiffeology_self : manifoldDiffeology E E = NormedSpace.toDiffeology E := by
  ext n p
  exact contMDiff_iff_contDiff

/-- Smoothly equivalent atlases give the same diffeology, even when their model spaces differ. -/
theorem manifoldDiffeology_eq_of_contMDiff_id
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    (h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (id : M → M))
    (h' : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ (id : M → M)) :
    manifoldDiffeology E M = manifoldDiffeology F M := by
  ext n p
  exact ⟨fun hp => h.comp hp, fun hp => h'.comp hp⟩

variable [DiffeologicalSpace M] [IsContMDiffCompatible (E := E) (M := M)]

/-- The D-topology of a manifold-compatible diffeology equals its original topology. -/
instance : IsDTopologyCompatible M := by
  rw [isContMDiffCompatible_iff_eq_manifoldDiffeology.mp
    (inferInstance : IsContMDiffCompatible (E := E) (M := M))]
  infer_instance

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  [DiffeologicalSpace N] [IsContMDiffCompatible (E := F) (M := N)]

/-- A map between manifold-compatible diffeologies is smooth exactly when it is smooth
as a map of manifolds. -/
theorem dSmooth_iff_contMDiff {f : M → N} :
    DSmooth f ↔ ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
  constructor
  · intro hf x
    obtain ⟨e, _, hx, he, hei⟩ := exists_contMDiff_parametrization (E := E) x
    have hfe := (IsContMDiffCompatible.isPlot_iff (E := F)).mp
      (hf _ e (IsContMDiffCompatible.isPlot_iff.mpr he))
    have hg := hfe.contMDiffAt.comp x
      (hei.contMDiffAt (e.open_target.mem_nhds hx))
    exact hg.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
      (e.open_target.mem_nhds hx) (fun y hy => congrArg f (e.right_inv hy).symm))
  · intro hf n p hp
    exact IsContMDiffCompatible.isPlot_iff.mpr
      (hf.comp (IsContMDiffCompatible.isPlot_iff.mp hp))

/-- A normed-space-compatible diffeology is also compatible with the normed space's
canonical manifold structure. No finite-dimensionality is needed for this implication. -/
instance {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [DiffeologicalSpace V] [IsContDiffCompatible V] : IsContMDiffCompatible V V where
  isPlot_iff := isPlot_iff_contDiff.trans contMDiff_iff_contDiff.symm

end TauCeti
