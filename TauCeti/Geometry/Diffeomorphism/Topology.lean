/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.ManifoldFamily
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The weak Whitney topology on diffeomorphisms

The diffeomorphisms `M ≃ₘ^n⟮I, J⟯ N` carry the subspace topology inherited from the weak
Whitney topology on `C^n⟮I, M; J, N⟯`: a net of diffeomorphisms converges when every coordinate
derivative, of every order at most `n`, converges uniformly on compact subsets of a chart. On a
compact source this is the `C^n` topology in the usual sense, the weak and the strong Whitney
topologies agreeing there. Only the forward map is topologized; no continuity is claimed for
inversion, which needs an inverse-function estimate that is not developed here.

Use `open scoped TauCeti.DiffeomorphWeakWhitney` to select this topology, for instance when
forming continuous maps into the space of diffeomorphisms.

The reason to have the topology is to turn a *smooth family* of diffeomorphisms, which is what a
geometric construction produces, into a *continuous map into the space of diffeomorphisms*, which
is what a homotopy-theoretic statement about that space needs. `Diffeomorph.ofSmoothFamily` is
that map; `TauCeti.Diffeotopy.toPath` in `TauCeti.Geometry.Diffeomorphism.Diffeotopy.Path` is its
first use.

## Main definitions

* `Diffeomorph.weakWhitneyTopology`: the topology induced from the weak Whitney topology on
  `C^n⟮I, M; J, N⟯`.
* `Diffeomorph.ofSmoothFamily`: a jointly `C^n` family of diffeomorphisms, as a continuous map
  into the space of diffeomorphisms `M ≃ₘ^n⟮I, J⟯ N`.

## Main results

* `Diffeomorph.isEmbedding_toContMDiffMap`: the forgetful map to `C^n⟮I, M; J, N⟯` is an
  embedding.
* `Diffeomorph.continuous_weakWhitney_iff`: a family of diffeomorphisms is continuous exactly
  when the underlying family of `C^n` maps is.
* `Diffeomorph.continuous_eval_const`: evaluation at a fixed point of the source is continuous.
* `Diffeomorph.t2Space_weakWhitney`: a Hausdorff target gives a Hausdorff diffeomorphism space.
* `ContMDiff.continuous_diffeomorphWeakWhitney`: joint `C^n` regularity of a family of
  diffeomorphisms gives continuity of the family.

The weak topology convention follows M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1.
-/

public section

open Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

/-- A diffeomorphism is determined by its underlying `C^n` map. -/
theorem toContMDiffMap_injective :
    Function.Injective (toContMDiffMap : (M ≃ₘ^n⟮I, J⟯ N) → C^n⟮I, M; J, N⟯) := fun _ _ h ↦
  Diffeomorph.ext fun x ↦ congrFun (congrArg DFunLike.coe h) x

variable [IsManifold I n M] [IsManifold J n N]

/-- The weak Whitney topology on the `C^n` diffeomorphisms from `M` to `N`: the topology induced
along the forgetful map to `C^n⟮I, M; J, N⟯`. -/
@[instance_reducible]
noncomputable def weakWhitneyTopology : TopologicalSpace (M ≃ₘ^n⟮I, J⟯ N) :=
  .induced toContMDiffMap ContMDiffMap.manifoldWeakWhitneyTopology

scoped[TauCeti.DiffeomorphWeakWhitney] attribute [instance 1100] Diffeomorph.weakWhitneyTopology

open scoped TauCeti.DiffeomorphWeakWhitney

/-- The forgetful map to `C^n⟮I, M; J, N⟯` realizes the diffeomorphisms as a subspace of the
weak Whitney map space. -/
theorem isEmbedding_toContMDiffMap :
    Topology.IsEmbedding (toContMDiffMap : (M ≃ₘ^n⟮I, J⟯ N) → C^n⟮I, M; J, N⟯) :=
  ⟨⟨rfl⟩, toContMDiffMap_injective⟩

/-- The forgetful map to `C^n⟮I, M; J, N⟯` is continuous. -/
theorem continuous_toContMDiffMap :
    Continuous (toContMDiffMap : (M ≃ₘ^n⟮I, J⟯ N) → C^n⟮I, M; J, N⟯) :=
  isEmbedding_toContMDiffMap.continuous

/-- A family of diffeomorphisms is continuous exactly when the underlying family of `C^n` maps
is. -/
theorem continuous_weakWhitney_iff {Q : Type*} [TopologicalSpace Q] {f : Q → M ≃ₘ^n⟮I, J⟯ N} :
    Continuous f ↔ Continuous fun q ↦ (f q).toContMDiffMap :=
  isEmbedding_toContMDiffMap.continuous_iff

/-- Evaluation at a fixed point of the source is continuous. -/
theorem continuous_eval_const (x : M) : Continuous fun f : M ≃ₘ^n⟮I, J⟯ N ↦ f x :=
  (ContMDiffMap.continuous_eval_manifoldWeakWhitney x).comp continuous_toContMDiffMap

/-- A Hausdorff target gives a Hausdorff space of diffeomorphisms. -/
theorem t2Space_weakWhitney [T2Space N] : T2Space (M ≃ₘ^n⟮I, J⟯ N) :=
  isEmbedding_toContMDiffMap.t2Space

scoped[TauCeti.DiffeomorphWeakWhitney] attribute [instance] Diffeomorph.t2Space_weakWhitney

variable [IsManifold I' n P]

/-- The smooth-families map: a family of diffeomorphisms which is jointly `C^n` on the product of
the parameter manifold with the source is continuous for the weak Whitney topology. The converse
fails for a general parameter space, so only this direction is available. -/
theorem _root_.ContMDiff.continuous_diffeomorphWeakWhitney {f : P → M ≃ₘ^n⟮I, J⟯ N}
    (hf : ContMDiff (I'.prod I) J n fun z : P × M ↦ f z.1 z.2) :
    Continuous f :=
  continuous_weakWhitney_iff.mpr
    (ContMDiff.continuous_manifoldWeakWhitney (f := fun p ↦ (f p).toContMDiffMap) hf)

/-- A jointly `C^n` family of diffeomorphisms, bundled as a continuous map into the
diffeomorphisms. -/
noncomputable def ofSmoothFamily (f : P → M ≃ₘ^n⟮I, J⟯ N)
    (hf : ContMDiff (I'.prod I) J n fun z : P × M ↦ f z.1 z.2) :
    C(P, M ≃ₘ^n⟮I, J⟯ N) :=
  ⟨f, hf.continuous_diffeomorphWeakWhitney⟩

/-- The smooth-families map is the family it was built from. -/
@[simp]
theorem ofSmoothFamily_apply (f : P → M ≃ₘ^n⟮I, J⟯ N)
    (hf : ContMDiff (I'.prod I) J n fun z : P × M ↦ f z.1 z.2) (p : P) :
    ofSmoothFamily f hf p = f p := (rfl)

end Diffeomorph
