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
compact subsets of chart domains. In particular, the `n = ∞` instance below supplies the
chart-level topology used to topologize diffeomorphism groups.

We also characterize continuity of arbitrary families by their compact-open derivative maps.
When `E` is locally compact, this is equivalent to joint continuity of every spatial derivative;
no differentiability in the parameter is required for this characterization.

## Main definitions

* `ContMDiffMap.iteratedFDerivContinuousMap`: the `k`th derivative of a bundled `C^n` map,
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

The construction follows M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33,
Chapter 2, §1, specialized to maps whose source and target each have one global chart.
-/

public section

open Filter Set Topology
open scoped Manifold

namespace ContMDiffMap

variable {k : Type*} [NontriviallyNormedField k]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace k F]
  {n : WithTop ℕ∞}

/-- The `m`th derivative of a bundled `C^n` map between normed spaces, bundled as a continuous
map. The bound `m ≤ n` is exactly what makes this derivative continuous. -/
noncomputable def iteratedFDerivContinuousMap
    (f : C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯)
    (m : ℕ) (hm : m ≤ n) :
    C(E, E [×m]→L[k] F) :=
  ⟨fun x ↦ iteratedFDeriv k m f x,
    f.contMDiff.contDiff.continuous_iteratedFDeriv hm⟩

@[simp]
theorem iteratedFDerivContinuousMap_apply
    (f : C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯)
    (m : ℕ) (hm : m ≤ n) (x : E) :
    iteratedFDerivContinuousMap f m hm x = iteratedFDeriv k m f x :=
  (rfl)

/-- The weak Whitney `C^n` jet of a bundled map is the family of its derivatives of every order
at most `n`, each bundled as a continuous map with the compact-open topology. -/
noncomputable def weakWhitneyJet
    (f : C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯) :
    (m : {m : ℕ // m ≤ n}) → C(E, E [×(m : ℕ)]→L[k] F) :=
  fun m ↦ iteratedFDerivContinuousMap f m m.property

@[simp]
theorem weakWhitneyJet_apply
    (f : C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯)
    (m : {m : ℕ // m ≤ n}) :
    weakWhitneyJet f m = iteratedFDerivContinuousMap f m m.property :=
  (rfl)

/-- The weak Whitney `C^n` topology on bundled `C^n` maps between normed spaces. It is the
coarsest topology making the compact-open-valued derivative maps of every order `m ≤ n`
continuous. -/
@[instance_reducible]
noncomputable def weakWhitneyTopology :
    TopologicalSpace C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯ :=
  TopologicalSpace.induced weakWhitneyJet inferInstance

/-- Bundled `C^n` maps between normed spaces carry the weak Whitney topology. -/
noncomputable instance instTopologicalSpaceWeakWhitney :
    TopologicalSpace C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯ :=
  weakWhitneyTopology

/-- The full weak Whitney jet is continuous. -/
theorem continuous_weakWhitneyJet :
    Continuous (weakWhitneyJet :
      C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯ →
        (m : {m : ℕ // m ≤ n}) → C(E, E [×(m : ℕ)]→L[k] F)) :=
  continuous_induced_dom

/-- The `m`th derivative map from the weak Whitney `C^n` topology to the compact-open topology is
continuous. -/
theorem continuous_iteratedFDerivContinuousMap (m : ℕ) (hm : m ≤ n) :
    Continuous (fun f : C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯ ↦
      iteratedFDerivContinuousMap f m hm) := by
  simpa only [Function.comp_def, weakWhitneyJet_apply] using
    (continuous_apply ⟨m, hm⟩).comp
      (continuous_weakWhitneyJet (k := k) (E := E) (F := F) (n := n))

/-- Forgetting the derivatives is a continuous map from the weak Whitney `C^n` topology to the
compact-open topology on continuous maps. This is the order-zero derivative projection, followed
by the canonical identification of zero-linear maps with their values. -/
theorem continuous_toContinuousMap :
    Continuous (fun f : C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯ ↦
      (f : C(E, F))) := by
  let curryZero : C(E [×0]→L[k] F, F) :=
    ⟨continuousMultilinearCurryFin0 k E F,
      (continuousMultilinearCurryFin0 k E F).continuous⟩
  have h := (ContinuousMap.continuous_postcomp (X := E) curryZero).comp
    (continuous_iteratedFDerivContinuousMap (k := k) (E := E) (F := F) (n := n)
      0 (by simp))
  convert h using 1
  ext f x
  simp only [Function.comp_apply, curryZero, ContinuousMap.comp_apply,
    iteratedFDerivContinuousMap_apply]
  rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
  exact (continuousMultilinearCurryFin0 k E F).apply_symm_apply (f x) |>.symm

/-- The weak Whitney jet remembers the original map: its derivative of order zero is the map
itself, viewed as a zero-linear map. -/
theorem weakWhitneyJet_injective :
    Function.Injective (weakWhitneyJet :
      C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯ →
        (m : {m : ℕ // m ≤ n}) → C(E, E [×(m : ℕ)]→L[k] F)) := by
  intro f g h
  apply ContMDiffMap.ext
  intro x
  have hzero := congrFun h (⟨0, by simp⟩ : {m : ℕ // m ≤ n})
  have hx := DFunLike.congr_fun hzero x
  have hvalue := congrArg (fun A : E [×0]→L[k] F ↦ A 0) hx
  simpa only [weakWhitneyJet_apply, iteratedFDerivContinuousMap_apply,
    iteratedFDeriv_zero_apply] using hvalue

/-- The weak Whitney topology is exactly the topology induced by the full jet. -/
theorem isInducing_weakWhitneyJet :
    IsInducing (weakWhitneyJet :
      C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯ →
        (m : {m : ℕ // m ≤ n}) → C(E, E [×(m : ℕ)]→L[k] F)) :=
  ⟨rfl⟩

/-- The full jet is a topological embedding of the weak Whitney map space into the product of its
compact-open derivative spaces. -/
theorem isEmbedding_weakWhitneyJet :
    IsEmbedding (weakWhitneyJet :
      C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯ →
        (m : {m : ℕ // m ≤ n}) → C(E, E [×(m : ℕ)]→L[k] F)) :=
  ⟨isInducing_weakWhitneyJet, weakWhitneyJet_injective⟩

/-- The weak Whitney topology on `C^n` maps between normed spaces is Hausdorff. -/
instance instT2SpaceWeakWhitney :
    T2Space C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯ :=
  isEmbedding_weakWhitneyJet.t2Space

/-- A family of `C^n` maps converges in the weak Whitney topology exactly when every derivative
through order `n` converges in the compact-open topology. -/
theorem tendsto_weakWhitney_iff {X : Type*} {l : Filter X}
    {f : X → C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯}
    {g : C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯} :
    Tendsto f l (nhds g) ↔
      ∀ (m : ℕ) (hm : m ≤ n), Tendsto
        (fun x ↦ iteratedFDerivContinuousMap (f x) m hm) l
        (nhds (iteratedFDerivContinuousMap g m hm)) := by
  rw [isInducing_weakWhitneyJet.tendsto_nhds_iff]
  simp only [tendsto_pi_nhds, Function.comp_apply, weakWhitneyJet_apply, Subtype.forall]

/-- The weak Whitney convergence criterion written using compact-open subbasic sets: for every
derivative order, compact set, and open target containing the limiting derivative on that compact,
the derivatives of the family eventually have the same containment. -/
theorem tendsto_weakWhitney_iff_eventually_mapsTo {X : Type*} {l : Filter X}
    {f : X → C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯}
    {g : C^n⟮modelWithCornersSelf k E, E; modelWithCornersSelf k F, F⟯} :
    Tendsto f l (nhds g) ↔
      ∀ (m : ℕ) (hm : m ≤ n) (K : Set E), IsCompact K →
        ∀ (U : Set (E [×m]→L[k] F)), IsOpen U →
          MapsTo (iteratedFDerivContinuousMap g m hm) K U →
            ∀ᶠ x in l, MapsTo (iteratedFDerivContinuousMap (f x) m hm) K U := by
  rw [tendsto_weakWhitney_iff]
  simp only [ContinuousMap.tendsto_nhds_compactOpen]

end ContMDiffMap

namespace _root_.ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}

/-- Continuity into the weak Whitney topology is equivalent to continuity of each derivative
as a map into its compact-open function space. -/
theorem continuous_weakWhitney_iff {X : Type*} [TopologicalSpace X]
    {f : X → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯} :
    Continuous f ↔ ∀ (m : ℕ) (hm : m ≤ n),
      Continuous (fun p ↦ ContMDiffMap.iteratedFDerivContinuousMap (f p) m hm) := by
  rw [ContMDiffMap.isInducing_weakWhitneyJet.continuous_iff]
  simp only [continuous_pi_iff, Function.comp_apply, ContMDiffMap.weakWhitneyJet_apply,
    Subtype.forall]

/-- A family is continuous in the weak Whitney topology if every spatial derivative through
order `n` varies jointly continuously in the parameter and evaluation point. -/
theorem continuous_weakWhitney_of_continuous_iteratedFDeriv {X : Type*} [TopologicalSpace X]
    {f : X → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯}
    (hf : ∀ (m : ℕ), m ≤ n →
      Continuous (fun z : X × E ↦ iteratedFDeriv 𝕜 m (f z.1) z.2)) :
    Continuous f := by
  rw [continuous_weakWhitney_iff]
  intro m hm
  apply ContinuousMap.continuous_of_continuous_uncurry
  simpa only [Function.uncurry_def, ContMDiffMap.iteratedFDerivContinuousMap_apply]
    using hf m hm

/-- For a locally compact source, continuity of a family in the weak Whitney topology is
exactly joint continuity of all spatial derivatives through order `n`. -/
theorem continuous_weakWhitney_iff_continuous_iteratedFDeriv [LocallyCompactSpace E]
    {X : Type*} [TopologicalSpace X]
    {f : X → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯} :
    Continuous f ↔ ∀ (m : ℕ), m ≤ n →
      Continuous (fun z : X × E ↦ iteratedFDeriv 𝕜 m (f z.1) z.2) := by
  constructor
  · intro hf m hm
    simpa only [Function.uncurry_def, ContinuousMap.coe_mk,
      ContMDiffMap.iteratedFDerivContinuousMap_apply] using
      ContinuousMap.continuous_uncurry_of_continuous
        ⟨_, (continuous_weakWhitney_iff.mp hf) m hm⟩
  · exact continuous_weakWhitney_of_continuous_iteratedFDeriv

end _root_.ContMDiffMap
