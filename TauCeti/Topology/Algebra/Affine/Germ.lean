/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.AffineSpace.Generic
public import Mathlib.Topology.Separation.Basic

/-!
# Generic affine germs in scalar neighborhoods

The cofinite affine-germ results in `TauCeti.LinearAlgebra.AffineSpace.Generic`
give avoidance on every punctured scalar neighborhood. Scalars form a division ring
with a T1 topology; a preorder suffices for the right-neighborhood variants. Every
variant allows an arbitrary parameter `t₀`. Neither affine point torsor needs a
topology, norm, or chosen origin.

For a finite family of affine maps `g` and directions `v`, each map
`(x, t) ↦ t • v j +ᵥ g j x` must be surjective. One source arrangement `F` then works
at every `F`-generic point simultaneously for all `j` and for every puncture `t₀`.
The maps `g j` themselves need not be surjective. Fixed transverse directions also
work from exceptional base points. The cofinite conclusions do not require topology.

Adapted from `Mei/Geometry/Affine/IncomingGerm.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
-/

public section

open Set Filter Topology

namespace AffineSubspace

variable {k V P : Type*} [DivisionRing k] [TopologicalSpace k] [T1Space k]
  [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- A transverse affine germ avoids a subspace on every punctured scalar neighborhood,
even from an exceptional base point. -/
theorem eventually_smul_vadd_notMem_nhdsNE (S : AffineSubspace k P)
    {v : V} (hv : v ∉ S.direction) (x : P) (t₀ : k) :
    ∀ᶠ t : k in 𝓝[≠] t₀, t • v +ᵥ x ∉ S :=
  (S.eventually_smul_vadd_notMem_cofinite hv x).filter_mono (nhdsNE_le_cofinite t₀)

/-- A transverse affine germ avoids a subspace on the right neighborhood of any scalar
parameter, even from an exceptional base point. Only a scalar preorder is required. -/
theorem eventually_smul_vadd_notMem_nhdsGT [Preorder k] (S : AffineSubspace k P)
    {v : V} (hv : v ∉ S.direction) (x : P) (t₀ : k) :
    ∀ᶠ t : k in 𝓝[>] t₀, t • v +ᵥ x ∉ S :=
  (S.eventually_smul_vadd_notMem_nhdsNE hv x t₀).filter_mono
    (nhdsWithin_mono t₀ fun _ ht => ne_of_gt ht)

end AffineSubspace

namespace TauCeti.ExceptionalArrangement

section FixedDirection

variable {k V P : Type*} [DivisionRing k] [TopologicalSpace k] [T1Space k]
  [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- A direction transverse to every nonempty exception gives a generic punctured germ
at every scalar parameter from every base point, including exceptional points. -/
theorem eventually_isGeneric_smul_vadd_nhdsNE (E : ExceptionalArrangement k P)
    {v : V} (hv : ∀ S ∈ E.exceptions, (S : Set P).Nonempty → v ∉ S.direction)
    (x : P) (t₀ : k) :
    ∀ᶠ t : k in 𝓝[≠] t₀, E.IsGeneric (t • v +ᵥ x) :=
  (E.eventually_isGeneric_smul_vadd_cofinite hv x).filter_mono (nhdsNE_le_cofinite t₀)

/-- A fixed direction transverse to every nonempty exception gives a generic right-hand
germ at every scalar parameter from every base point. -/
theorem eventually_isGeneric_smul_vadd_nhdsGT [Preorder k] (E : ExceptionalArrangement k P)
    {v : V} (hv : ∀ S ∈ E.exceptions, (S : Set P).Nonempty → v ∉ S.direction)
    (x : P) (t₀ : k) :
    ∀ᶠ t : k in 𝓝[>] t₀, E.IsGeneric (t • v +ᵥ x) :=
  (E.eventually_isGeneric_smul_vadd_nhdsNE hv x t₀).filter_mono
    (nhdsWithin_mono t₀ fun _ ht => ne_of_gt ht)

end FixedDirection

section AffineFamilies

variable {k U V P Q ι : Type*} [DivisionRing k] [TopologicalSpace k] [T1Space k]
  [AddCommGroup U] [Module k U] [AddTorsor U P]
  [AddCommGroup V] [Module k V] [AddTorsor V Q] [Finite ι]

/-- If each `(x, t) ↦ t • v j +ᵥ g j x` is surjective, one source arrangement `F`
makes all germs from every `F`-generic point eventually generic at every puncture,
simultaneously for the finite family. -/
theorem exists_forall_eventually_isGeneric_smul_vadd_nhdsNE
    (E : ExceptionalArrangement k Q) (g : ι → P →ᵃ[k] Q) (v : ι → V)
    (hg : ∀ j, Function.Surjective (fun z : P × k => z.2 • v j +ᵥ g j z.1)) :
    ∃ F : ExceptionalArrangement k P, ∀ x, F.IsGeneric x → ∀ t₀ : k,
      ∀ᶠ t : k in 𝓝[≠] t₀, ∀ j, E.IsGeneric (t • v j +ᵥ g j x) := by
  obtain ⟨F, hF⟩ := E.exists_forall_eventually_isGeneric_smul_vadd_cofinite g v hg
  exact ⟨F, fun x hx t₀ => (hF x hx).filter_mono (nhdsNE_le_cofinite t₀)⟩

/-- If each `(x, t) ↦ t • v j +ᵥ g j x` is surjective, one source arrangement `F`
makes all germs from every `F`-generic point eventually generic to the right of every
parameter, simultaneously for the finite family. -/
theorem exists_forall_eventually_isGeneric_smul_vadd_nhdsGT [Preorder k]
    (E : ExceptionalArrangement k Q) (g : ι → P →ᵃ[k] Q) (v : ι → V)
    (hg : ∀ j, Function.Surjective (fun z : P × k => z.2 • v j +ᵥ g j z.1)) :
    ∃ F : ExceptionalArrangement k P, ∀ x, F.IsGeneric x → ∀ t₀ : k,
      ∀ᶠ t : k in 𝓝[>] t₀, ∀ j, E.IsGeneric (t • v j +ᵥ g j x) := by
  obtain ⟨F, hF⟩ := E.exists_forall_eventually_isGeneric_smul_vadd_nhdsNE g v hg
  exact ⟨F, fun x hx t₀ => (hF x hx t₀).filter_mono
    (nhdsWithin_mono t₀ fun _ ht => ne_of_gt ht)⟩

end AffineFamilies

end TauCeti.ExceptionalArrangement
