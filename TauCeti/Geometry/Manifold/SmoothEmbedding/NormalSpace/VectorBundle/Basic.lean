/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.NormalSpace.VectorBundle
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology

/-!
# Intrinsic normal vector bundles of embeddings

The intrinsic normal spaces of a positive-regularity embedding between finite-dimensional
manifolds form a vector bundle, with the quotient topology from the pulled-back ambient tangent
bundle. It is the quotient normal bundle of the underlying immersion
(`Manifold.IsImmersion.normalSpaceFiberBundle`), stated here for the bundled embedding so that
its fibres are the embedding's `TauCeti.SmoothEmbedding.NormalSpace`. These are the normal
bundles needed for tubular neighbourhoods in an arbitrary ambient manifold.

For the tubular-neighbourhood context, see M. Hirsch, *Differential Topology*, Chapter 4, §§5–6.
-/

public section

noncomputable section

open Set Function Topology Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V P H G M N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

section Topological

variable [IsManifold I 1 M] [IsManifold J 1 N]

/-- Preferred local coordinates on the intrinsic normal bundle in an arbitrary ambient
manifold, using a fixed model of the codimension: those of the underlying immersion. The total
space has its quotient topology. -/
@[expose] def normalSpaceTrivialization (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    Trivialization P (π P (fun x => f.NormalSpace x hn)) :=
  f.isImmersion.normalSpaceTrivialization hn hdim x₀

/-- The preferred intrinsic normal coordinates contain their reference point. -/
@[simp] theorem mem_normalSpaceTrivialization_baseSet
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x : M) :
    x ∈ (f.normalSpaceTrivialization hn hdim x).baseSet :=
  f.isImmersion.mem_normalSpaceTrivialization_baseSet hn hdim x

/-- The preferred intrinsic normal coordinates at `x₀` invert by one fixed complementary
representative: their base set lies in the source and ambient charts at `x₀`, and over it the
normal vector with coordinates `w` is the normal class of the ambient tangent vector whose
coordinates in the tangent chart at `f x₀` are `B w`, for a fixed `B : P →L[𝕜] V`. -/
theorem exists_normalSpaceTrivialization_symm_apply
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    ∃ B : P →L[𝕜] V,
      (f.normalSpaceTrivialization hn hdim x₀).baseSet ⊆
        (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source ∧
      ∀ x ∈ (f.normalSpaceTrivialization hn hdim x₀).baseSet, ∀ w : P,
        (f.normalSpaceTrivialization hn hdim x₀).symm x w =
          f.normalClass x hn ((trivializationAt V (TangentSpace J) (f x₀)).symm (f x) (B w)) :=
  f.isImmersion.exists_normalSpaceTrivialization_symm_apply hn hdim x₀

/-- Preferred intrinsic normal coordinates are linear on each fibre. -/
instance instIsLinearNormalSpaceTrivialization
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x : M) :
    (f.normalSpaceTrivialization hn hdim x).IsLinear 𝕜 :=
  f.isImmersion.instIsLinearNormalSpaceTrivialization hn hdim x

/-- The intrinsic normal fibre bundle in an arbitrary finite-dimensional ambient manifold: the
quotient normal bundle of the underlying immersion. Install it locally to select the
complementary-coordinate atlas. Its topology is the existing quotient topology on intrinsic
normal classes. -/
@[instance_reducible, expose]
def normalSpaceFiberBundle (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    FiberBundle P (fun x => f.NormalSpace x hn) :=
  f.isImmersion.normalSpaceFiberBundle hn hdim

/-- The preferred bundle chart is the chosen complementary normal chart. -/
@[simp] theorem normalSpaceFiberBundle_trivializationAt
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x : M) :
    letI := f.normalSpaceFiberBundle hn hdim
    trivializationAt P (fun x => f.NormalSpace x hn) x =
      f.normalSpaceTrivialization hn hdim x :=
  f.isImmersion.normalSpaceFiberBundle_trivializationAt hn hdim x

/-- The intrinsic normal fibres form a vector bundle with their quotient topology. -/
theorem normalSpaceVectorBundle (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    letI := f.normalSpaceFiberBundle hn hdim
    VectorBundle 𝕜 P (fun x => f.NormalSpace x hn) :=
  f.isImmersion.normalSpaceVectorBundle hn hdim

end Topological

/-- The intrinsic normal spaces of a `C^n` embedding form a `C^m` vector bundle when
`m + 1 ≤ n`, retaining their quotient total-space topology. -/
theorem normalSpaceContMDiffVectorBundle {m : ℕ∞ω}
    [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ContMDiffVectorBundle m P (fun x => f.NormalSpace x hn) I :=
  f.isImmersion.normalSpaceContMDiffVectorBundle hn hm hdim

end TauCeti.SmoothEmbedding
