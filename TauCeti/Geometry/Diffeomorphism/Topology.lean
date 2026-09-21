/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.ManifoldFamily
public import Mathlib.Topology.Homotopy.Path

/-!
# The weak Whitney topology on diffeomorphisms

The diffeomorphisms `M ≃ₘ^n⟮I, J⟯ N` carry the subspace topology inherited from the weak
Whitney topology on `C^n⟮I, M; J, N⟯`: a net of diffeomorphisms converges when every coordinate
derivative, of every order at most `n`, converges uniformly on compact subsets of a chart. On a
compact source this is the `C^n` topology in the usual sense, the weak and the strong Whitney
topologies agreeing there. Only the forward map is topologized; no continuity is claimed for
inversion, which needs an inverse-function estimate that is not developed here.

Use `open scoped TauCeti.WeakWhitney` to select this topology, for instance when forming
continuous maps into a diffeomorphism group.

The reason to have the topology is to turn a *smooth family* of diffeomorphisms, which is what a
geometric construction produces, into a *continuous map into the diffeomorphism group*, which is
what a homotopy-theoretic statement about that group needs. `Diffeomorph.ofSmoothFamily` is that
map, and `TauCeti.Diffeotopy.toPath` is its first use: a smooth ambient isotopy of `M` is a path
from the identity to its final diffeomorphism in `Diff(M)`, so diffeotopic diffeomorphisms lie in
one path component.

## Main definitions

* `Diffeomorph.weakWhitneyTopology`: the topology induced from the weak Whitney topology on
  `C^n⟮I, M; J, N⟯`.
* `Diffeomorph.ofSmoothFamily`: a jointly `C^n` family of diffeomorphisms, as a continuous map
  into the diffeomorphism group.
* `TauCeti.Diffeotopy.toPath`: the path traced in `TauCeti.Diff` by a diffeotopy.

## Main results

* `Diffeomorph.isEmbedding_toContMDiffMap`: the forgetful map to `C^n⟮I, M; J, N⟯` is an
  embedding.
* `Diffeomorph.continuous_weakWhitney_iff`: a family of diffeomorphisms is continuous exactly
  when the underlying family of `C^n` maps is.
* `Diffeomorph.continuous_eval`: evaluation at a point of the source is continuous.
* `Diffeomorph.t2Space_weakWhitney`: a Hausdorff target gives a Hausdorff diffeomorphism space.
* `ContMDiff.continuous_diffeomorphWeakWhitney`: joint `C^n` regularity of a family of
  diffeomorphisms gives continuity of the family.
* `TauCeti.Diffeotopy.continuous_timeSlice`: the time slices of a diffeotopy move continuously.

The weak topology convention follows M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1.
-/

public section

open Topology
open scoped Manifold ContDiff

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

scoped[TauCeti.WeakWhitney] attribute [instance 1100] Diffeomorph.weakWhitneyTopology

attribute [local instance] ContMDiffMap.manifoldWeakWhitneyTopology weakWhitneyTopology

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
theorem continuous_eval (x : M) : Continuous fun f : M ≃ₘ^n⟮I, J⟯ N ↦ f x :=
  (ContMDiffMap.continuous_eval_manifoldWeakWhitney x).comp continuous_toContMDiffMap

/-- A Hausdorff target gives a Hausdorff space of diffeomorphisms. -/
theorem t2Space_weakWhitney [T2Space N] : T2Space (M ≃ₘ^n⟮I, J⟯ N) :=
  have : T2Space C^n⟮I, M; J, N⟯ := ContMDiffMap.t2Space_manifoldWeakWhitney
  isEmbedding_toContMDiffMap.t2Space

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

namespace TauCeti.Diffeotopy

open unitInterval
open scoped TauCeti.WeakWhitney

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  (Φ : Diffeotopy J n M)

variable [IsManifold J n M]

/-- The time slices of a diffeotopy move continuously in the weak Whitney topology. -/
theorem continuous_timeSlice : Continuous Φ.timeSlice :=
  Φ.contMDiff_timeSlice.continuous_diffeomorphWeakWhitney

/-- A diffeotopy is a path in `TauCeti.Diff` from the identity to its final diffeomorphism; in
particular diffeotopic self-diffeomorphisms lie in the same path component. -/
noncomputable def toPath : Path (1 : Diff J M n) Φ.final where
  toFun := Φ.timeSlice
  continuous_toFun := Φ.continuous_timeSlice
  source' := (Φ.timeSlice_zero).trans _root_.Diffeomorph.one_def.symm
  target' := Φ.final_def.symm

/-- The path traced by a diffeotopy is its family of time slices. -/
@[simp]
theorem toPath_apply (t : I) : Φ.toPath t = Φ.timeSlice t := (rfl)

end TauCeti.Diffeotopy
