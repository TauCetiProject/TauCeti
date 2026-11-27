/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.Matrix
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Continuity of homomorphisms into the general linear group

For the units topology on `GL n A = Matrix.GeneralLinearGroup n A`, a homomorphism from a group
with continuous inversion into `GL n A` is continuous exactly when its matrix entries are
continuous: by `MonoidHom.continuous_iff_continuous_val` the inverse matrices `ρ(g)⁻¹ = ρ(g⁻¹)`
come for free, and a matrix-valued map is continuous exactly when its entries are.

Entrywise application of a ring homomorphism `f : R →+* S` that is an open embedding, such as the
inclusion of an open subring, is an open embedding `GL n R → GL n S`: its range consists of the
invertible matrices whose entries and inverse entries lie in the open range of `f`.

## Main results

* `MonoidHom.continuous_iff_continuous_matrix_elem`: continuity of a homomorphism into `GL n A`
  through its matrix entries.
* `Topology.IsOpenEmbedding.generalLinearGroup_map`: `GL n R → GL n S` is an open embedding when
  `f` is.
-/

public section

/-- **Continuity into `GL n A` through the matrix entries.** For the units topology on `GL n A`, a
homomorphism `ρ : G →* GL n A` from a group with continuous inversion is continuous exactly when
every entry `g ↦ ρ(g)ᵢⱼ` is continuous; the inverse matrices are handled by
`MonoidHom.continuous_iff_continuous_val`. -/
theorem MonoidHom.continuous_iff_continuous_matrix_elem {G n A : Type*} [Group G]
    [TopologicalSpace G] [ContinuousInv G] [Fintype n] [DecidableEq n] [Semiring A]
    [TopologicalSpace A] (ρ : G →* GL n A) :
    Continuous ρ ↔ ∀ i j, Continuous fun g => (ρ g : Matrix n n A) i j :=
  ρ.continuous_iff_continuous_val.trans ⟨fun h i j => h.matrix_elem i j, continuous_matrix⟩

/-- **Change of scalars along an open embedding is an open embedding** `GL n R → GL n S`, for a
ring homomorphism `f : R →+* S` that is an open embedding. It is an embedding as `f` is one, and its
range, the invertible matrices whose entries and inverse entries lie in the range of `f`
(`Matrix.GeneralLinearGroup.mem_range_map_iff_of_injective`), is open as that range is. -/
theorem Topology.IsOpenEmbedding.generalLinearGroup_map {n R S : Type*} [Fintype n]
    [DecidableEq n] [CommRing R] [TopologicalSpace R] [CommRing S] [TopologicalSpace S]
    {f : R →+* S} (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (Matrix.GeneralLinearGroup.map (n := n) f) := by
  refine ⟨hf.isEmbedding.generalLinearGroup_map, ?_⟩
  have h : Set.range (Matrix.GeneralLinearGroup.map (n := n) f) =
      Units.val ⁻¹' (Set.range f).matrix ∩
        (fun g : GL n S ↦ ((g⁻¹ : GL n S) : Matrix n n S)) ⁻¹' (Set.range f).matrix := by
    ext g
    rw [← MonoidHom.coe_range, SetLike.mem_coe,
      Matrix.GeneralLinearGroup.mem_range_map_iff_of_injective hf.injective]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_matrix, RingHom.mem_range,
      Set.mem_range]
  rw [h]
  exact (hf.isOpen_range.matrix.preimage Units.continuous_val).inter
    (hf.isOpen_range.matrix.preimage Units.continuous_coe_inv)
