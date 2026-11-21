/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Axis
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# Centralizers of hyperbolic elements of a tree

Let `g` be a hyperbolic element of a group acting on a tree without inversions, and let
`c : ℤ → V` be its axis, a geodesic line on which `g` acts as the translation by its translation
length `ℓ(g) > 0`. An element `h` commuting with `g` maps the axis of `g` to itself, so it acts on
`c` as an isometry of `ℤ`: a translation `n ↦ n + k` or a reflection `n ↦ k - n`. A reflection
would conjugate the translation by `ℓ(g)` into the translation by `-ℓ(g)`, so `h` translates the
axis by some integer `k(h)`, positive, negative or zero
(`TauCeti.GTree.exists_smul_eq_add_of_commute`). The map `h ↦ k(h)` is a homomorphism from
the centralizer of `g` to `ℤ`, and its kernel fixes the axis pointwise. Hence the centralizer of
`g` is cyclic as soon as only the identity fixes every vertex of the axis.

## Main results

* `TauCeti.GTree.IsHyperbolic.isCyclic_centralizer`: a hyperbolic element whose axis has trivial
  pointwise stabilizer has cyclic centralizer.

## References

* J.-P. Serre, *Trees*, Chapter I, §6.4, Proposition 24 (the axis of a hyperbolic automorphism).
-/

public section

universe u v w

namespace TauCeti
namespace GTree

variable {G : Type w} [Group G] {T : GTree.{u, v} G}

/-- **Centralizers of hyperbolic elements.** If only the identity fixes every vertex of the axis
of a hyperbolic element `g`, then the centralizer of `g` is cyclic: it acts faithfully on the axis
by translations. -/
theorem IsHyperbolic.isCyclic_centralizer {g : G} (hg : T.IsHyperbolic g)
    (hfix : fixingSubgroup G (T.axis g) = ⊥) : IsCyclic (Subgroup.centralizer {g}) := by
  obtain ⟨c, -, hc, hgc, hrange⟩ := hg.exists_range_eq_axis (T.axis_nonempty g).some_mem
  have hinj := SerreGraph.injective_of_dist_eq_natAbs hc
  have hℓ : (T.translationLength g : ℤ) ≠ 0 := by
    have := translationLength_pos_iff.mpr hg
    omega
  choose k hk using fun h : Subgroup.centralizer {g} =>
    exists_smul_eq_add_of_commute hc hℓ hgc
      (Subgroup.mem_centralizer_singleton_iff.1 h.property).symm
  have hmul (x y : Subgroup.centralizer {g}) : k (x * y) = k x + k y := by
    have h := hk (x * y) 0
    rw [Subgroup.coe_mul, mul_smul, hk y 0, hk x (0 + k y)] at h
    have := hinj h
    omega
  refine isCyclic_of_injective (MonoidHom.mk' (fun y => Multiplicative.ofAdd (k y)) fun y z => by
    rw [hmul, ofAdd_add]) ((injective_iff_map_eq_one _).2 fun y hy => Subtype.ext ?_)
  have hy₀ : k y = 0 := by simpa using hy
  rw [Subgroup.coe_one, ← Subgroup.mem_bot, ← hfix, mem_fixingSubgroup_iff, ← hrange]
  rintro _ ⟨n, rfl⟩
  rw [hk, hy₀, add_zero]

end GTree
end TauCeti
