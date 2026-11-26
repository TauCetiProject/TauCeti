/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.TietzeExtension

/-!
# Density on compact sets

A family of functions approximates continuous functions on compact sets if it can approximate
every continuous restriction to any compact set, to arbitrarily small uniform error. The
approximants may be arbitrary functions. For a family of continuous maps, Tietze extension
identifies this property with density in the compact-open topology.
-/

public section

open scoped Topology

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [PseudoMetricSpace Y]

/-- A family is dense on compact sets if it approximates every function continuous on a compact
set uniformly on that set, to arbitrary accuracy. -/
def DenseOnCompacts (S : Set (X → Y)) : Prop :=
  ∀ ⦃K : Set X⦄, IsCompact K → ∀ ⦃f : X → Y⦄, ContinuousOn f K → ∀ ⦃ε : ℝ⦄, 0 < ε →
    ∃ g ∈ S, ∀ x ∈ K, dist (f x) (g x) < ε

/-- The uniform approximation formulation of density on compact sets. -/
theorem denseOnCompacts_iff {S : Set (X → Y)} :
    DenseOnCompacts S ↔
      ∀ ⦃K : Set X⦄, IsCompact K → ∀ ⦃f : X → Y⦄, ContinuousOn f K → ∀ ⦃ε : ℝ⦄, 0 < ε →
        ∃ g ∈ S, ∀ x ∈ K, dist (f x) (g x) < ε := (Iff.rfl)

/-- A dense family can be replaced by any family approximating its members uniformly on compact
sets. -/
theorem DenseOnCompacts.of_approx {S T : Set (X → Y)} (hT : DenseOnCompacts T)
    (hST : ∀ g ∈ T, ∀ ⦃K : Set X⦄, IsCompact K → ∀ ⦃ε : ℝ⦄, 0 < ε →
      ∃ h ∈ S, ∀ x ∈ K, dist (g x) (h x) < ε) :
    DenseOnCompacts S := by
  refine denseOnCompacts_iff.mpr fun K hK f hf ε hε => ?_
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨g, hg, hfg⟩ := denseOnCompacts_iff.mp hT hK hf hhalf
  obtain ⟨h, hh, hgh⟩ := hST g hg hK hhalf
  refine ⟨h, hh, fun x hx => (dist_triangle _ (g x) _).trans_lt ?_⟩
  simpa [add_halves] using add_lt_add (hfg x hx) (hgh x hx)

/-- On a normal Hausdorff space, approximation by continuous maps on all compact sets agrees
with density in the compact-open topology, for a target admitting Tietze extension. -/
theorem dense_iff_denseOnCompacts [NormalSpace X] [T2Space X] [TietzeExtension.{u, v} Y]
    {S : Set C(X, Y)} :
    Dense S ↔ DenseOnCompacts ((fun g : C(X, Y) => (g : X → Y)) '' S) := by
  have hb (f : C(X, Y)) :=
    mem_closure_iff_nhds_basis
      (nhds_basis_uniformity' Metric.uniformity_basis_dist.compactConvergenceUniformity (x := f))
      (t := S)
  rw [TauCeti.denseOnCompacts_iff]
  constructor
  · intro h K hK f hf ε hε
    let fK : C(K, Y) := ⟨K.domRestrict f, continuousOn_iff_continuous_domRestrict.mp hf⟩
    obtain ⟨F, hF⟩ := fK.exists_restrict_eq hK.isClosed
    obtain ⟨g, hg, hfg⟩ := (hb F).mp (h F) (K, ε) ⟨hK, hε⟩
    refine ⟨g, ⟨g, hg, rfl⟩, fun x hx => ?_⟩
    have hxF : F x = f x := congrFun (congrArg DFunLike.coe hF) ⟨x, hx⟩
    exact hxF ▸ hfg x hx
  · intro h f
    refine (hb f).mpr fun ⟨K, ε⟩ ⟨hK, hε⟩ => ?_
    obtain ⟨_, ⟨g, hg, rfl⟩, hfg⟩ := h hK f.continuous.continuousOn hε
    exact ⟨g, hg, hfg⟩

end TauCeti
