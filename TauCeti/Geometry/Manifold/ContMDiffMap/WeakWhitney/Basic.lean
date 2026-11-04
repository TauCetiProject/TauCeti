/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Maps.Basic

/-!
# The weak Whitney topology in one global chart

For maps between normed spaces, the weak Whitney `C^n` topology is the initial topology for all
iterated derivatives of order at most `n`, each regarded as a continuous map with the compact-open
topology. Thus a family converges precisely when every derivative converges uniformly on compact
sets (in the compact-open sense).

This is the global-chart building block for the weak Whitney topology on smooth maps between
manifolds. On a manifold, the same construction is applied to coordinate representatives on
compact subsets of chart domains. In particular, for `n = ∞` it supplies the chart-level
topology used to topologize diffeomorphism groups.

We also characterize continuity of arbitrary families by their compact-open derivative maps.
When `E` is locally compact, this is equivalent to joint continuity of every spatial derivative;
no differentiability in the parameter is required for this characterization.

## Main definitions

* `ContMDiffMap.iteratedFDerivContinuousMap`: the `m`th derivative of a bundled `C^n` map,
  bundled as a continuous map.
* `ContMDiffMap.weakWhitneyJet`: the family of all compact-open-valued derivatives through
  order `n`.
* `ContMDiffMap.weakWhitneyTopology`: the initial topology induced by the compact-open topologies
  of all derivatives through order `n`.

## Main results

* `ContMDiffMap.continuous_iteratedFDerivContinuousMap`: every derivative projection is
  continuous for the weak Whitney topology.
* `ContMDiffMap.continuous_toContinuousMap`: forgetting differentiability continuously maps the
  weak Whitney topology to the compact-open topology.
* `ContMDiffMap.isInducing_weakWhitneyJet`: the weak Whitney topology is exactly the topology
  induced by the full jet.
* `ContMDiffMap.isEmbedding_weakWhitneyJet`: the full jet realizes the weak Whitney map space as
  a subspace of the product of compact-open map spaces.
* `ContMDiffMap.tendsto_weakWhitney_iff`: convergence is equivalent to compact-open convergence
  of every derivative through order `n`.
* `ContMDiffMap.tendsto_weakWhitney_iff_eventually_mapsTo`: the same criterion in terms of the
  compact-open subbasic sets.
* `ContMDiffMap.continuous_weakWhitney_iff`: a family is continuous exactly when every derivative
  through order `n` is continuous as a compact-open-valued map.
* `ContMDiffMap.continuous_weakWhitney_iff_continuous_iteratedFDeriv`: for locally compact `E`,
  a family is continuous exactly when every derivative through order `n` is jointly continuous
  in the parameter and the point.

The construction follows M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33,
Chapter 2, §1, specialized to maps whose source and target each have one global chart.
-/

public section

open Filter Set Topology
open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}

/-- The `m`th derivative of a bundled `C^n` map between normed spaces, bundled as a continuous
map. The bound `m ≤ n` guarantees that this derivative is continuous. -/
noncomputable def iteratedFDerivContinuousMap
    (f : C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯)
    (m : ℕ) (hm : m ≤ n) :
    C(E, E [×m]→L[𝕜] F) :=
  ⟨fun x ↦ iteratedFDeriv 𝕜 m f x,
    f.contMDiff.contDiff.continuous_iteratedFDeriv hm⟩

@[simp]
theorem iteratedFDerivContinuousMap_apply
    (f : C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯)
    (m : ℕ) (hm : m ≤ n) (x : E) :
    iteratedFDerivContinuousMap f m hm x = iteratedFDeriv 𝕜 m f x :=
  (rfl)

/-- The weak Whitney `C^n` jet of a bundled map is the family of its derivatives of every order
at most `n`, each bundled as a continuous map with the compact-open topology. -/
noncomputable def weakWhitneyJet
    (f : C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯) :
    (m : {m : ℕ // m ≤ n}) → C(E, E [×(m : ℕ)]→L[𝕜] F) :=
  fun m ↦ iteratedFDerivContinuousMap f m m.property

@[simp]
theorem weakWhitneyJet_apply
    (f : C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯)
    (m : {m : ℕ // m ≤ n}) :
    weakWhitneyJet f m = iteratedFDerivContinuousMap f m m.property :=
  (rfl)

/-- The weak Whitney `C^n` topology on bundled `C^n` maps between normed spaces. It is the
coarsest topology making the compact-open-valued derivative maps of every order `m ≤ n`
continuous. -/
@[instance_reducible]
noncomputable def weakWhitneyTopology :
    TopologicalSpace C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ :=
  TopologicalSpace.induced weakWhitneyJet inferInstance

/-- Bundled `C^n` maps between normed spaces carry the weak Whitney topology. -/
noncomputable instance instTopologicalSpaceWeakWhitney :
    TopologicalSpace C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ :=
  weakWhitneyTopology

/-- The full weak Whitney jet is continuous. -/
theorem continuous_weakWhitneyJet :
    Continuous (weakWhitneyJet :
      C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ →
        (m : {m : ℕ // m ≤ n}) → C(E, E [×(m : ℕ)]→L[𝕜] F)) :=
  continuous_induced_dom

/-- The `m`th derivative map from the weak Whitney `C^n` topology to the compact-open topology is
continuous. -/
theorem continuous_iteratedFDerivContinuousMap (m : ℕ) (hm : m ≤ n) :
    Continuous (fun f : C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ ↦
      iteratedFDerivContinuousMap f m hm) := by
  simpa [Function.comp_def] using (continuous_apply ⟨m, hm⟩).comp continuous_weakWhitneyJet

/-- Forgetting the derivatives is a continuous map from the weak Whitney `C^n` topology to the
compact-open topology on continuous maps. This is the order-zero derivative projection, followed
by the canonical identification of zero-linear maps with their values. -/
theorem continuous_toContinuousMap :
    Continuous (fun f : C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ ↦
      (f : C(E, F))) := by
  refine ((ContinuousMap.continuous_postcomp
    (continuousMultilinearCurryFin0 𝕜 E F : C(E [×0]→L[𝕜] F, F))).comp
      (continuous_iteratedFDerivContinuousMap 0 (by simp))).congr fun f ↦ ?_
  ext x
  simp

/-- The weak Whitney jet remembers the original map: its derivative of order zero is the map
itself, viewed as a zero-linear map. -/
theorem weakWhitneyJet_injective :
    Function.Injective (weakWhitneyJet :
      C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ →
        (m : {m : ℕ // m ≤ n}) → C(E, E [×(m : ℕ)]→L[𝕜] F)) := by
  intro f g h
  ext x
  simpa using congr($(congrFun h ⟨0, by simp⟩) x 0)

/-- The weak Whitney topology is exactly the topology induced by the full jet. -/
theorem isInducing_weakWhitneyJet :
    IsInducing (weakWhitneyJet :
      C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ →
        (m : {m : ℕ // m ≤ n}) → C(E, E [×(m : ℕ)]→L[𝕜] F)) :=
  ⟨rfl⟩

/-- The full jet is a topological embedding of the weak Whitney map space into the product of its
compact-open derivative spaces. -/
theorem isEmbedding_weakWhitneyJet :
    IsEmbedding (weakWhitneyJet :
      C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ →
        (m : {m : ℕ // m ≤ n}) → C(E, E [×(m : ℕ)]→L[𝕜] F)) :=
  ⟨isInducing_weakWhitneyJet, weakWhitneyJet_injective⟩

/-- The weak Whitney topology on `C^n` maps between normed spaces is Hausdorff. -/
instance instT2SpaceWeakWhitney :
    T2Space C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ :=
  isEmbedding_weakWhitneyJet.t2Space

/-- A family of `C^n` maps converges in the weak Whitney topology exactly when every derivative
through order `n` converges in the compact-open topology. -/
theorem tendsto_weakWhitney_iff {X : Type*} {l : Filter X}
    {f : X → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯}
    {g : C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯} :
    Tendsto f l (𝓝 g) ↔
      ∀ (m : ℕ) (hm : m ≤ n), Tendsto
        (fun x ↦ iteratedFDerivContinuousMap (f x) m hm) l
        (𝓝 (iteratedFDerivContinuousMap g m hm)) := by
  rw [isInducing_weakWhitneyJet.tendsto_nhds_iff]
  simp only [tendsto_pi_nhds, Function.comp_apply, weakWhitneyJet_apply, Subtype.forall]

/-- The weak Whitney convergence criterion written using compact-open subbasic sets: for every
derivative order, compact set, and open target containing the limiting derivative on that compact,
the derivatives of the family eventually have the same containment. -/
theorem tendsto_weakWhitney_iff_eventually_mapsTo {X : Type*} {l : Filter X}
    {f : X → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯}
    {g : C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯} :
    Tendsto f l (𝓝 g) ↔
      ∀ (m : ℕ) (hm : m ≤ n) (K : Set E), IsCompact K →
        ∀ (U : Set (E [×m]→L[𝕜] F)), IsOpen U →
          MapsTo (iteratedFDerivContinuousMap g m hm) K U →
            ∀ᶠ x in l, MapsTo (iteratedFDerivContinuousMap (f x) m hm) K U := by
  rw [tendsto_weakWhitney_iff]
  simp only [ContinuousMap.tendsto_nhds_compactOpen]

/-- Continuity into the weak Whitney topology is equivalent to continuity of each derivative
as a map into its compact-open function space. -/
theorem continuous_weakWhitney_iff {X : Type*} [TopologicalSpace X]
    {f : X → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯} :
    Continuous f ↔ ∀ (m : ℕ) (hm : m ≤ n),
      Continuous (fun p ↦ iteratedFDerivContinuousMap (f p) m hm) := by
  rw [isInducing_weakWhitneyJet.continuous_iff]
  simp only [continuous_pi_iff, Function.comp_apply, weakWhitneyJet_apply,
    Subtype.forall]

/-- A family is continuous in the weak Whitney topology if every spatial derivative through
order `n` varies jointly continuously in the parameter and evaluation point. -/
theorem continuous_weakWhitney_of_continuous_iteratedFDeriv {X : Type*} [TopologicalSpace X]
    {f : X → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯}
    (hf : ∀ (m : ℕ), m ≤ n →
      Continuous (fun z : X × E ↦ iteratedFDeriv 𝕜 m (f z.1) z.2)) :
    Continuous f :=
  continuous_weakWhitney_iff.mpr fun m hm ↦
    ContinuousMap.continuous_of_continuous_uncurry _ <| by
      simpa [Function.uncurry_def] using hf m hm

/-- For a locally compact source, continuity of a family in the weak Whitney topology is
exactly joint continuity of all spatial derivatives through order `n`. -/
theorem continuous_weakWhitney_iff_continuous_iteratedFDeriv [LocallyCompactSpace E]
    {X : Type*} [TopologicalSpace X]
    {f : X → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯} :
    Continuous f ↔ ∀ (m : ℕ), m ≤ n →
      Continuous (fun z : X × E ↦ iteratedFDeriv 𝕜 m (f z.1) z.2) := by
  refine ⟨fun hf m hm ↦ ?_, continuous_weakWhitney_of_continuous_iteratedFDeriv⟩
  simpa [Function.uncurry_def] using ContinuousMap.continuous_uncurry_of_continuous
    ⟨_, continuous_weakWhitney_iff.mp hf m hm⟩

end ContMDiffMap
