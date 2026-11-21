/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Axis
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# Centralizers of hyperbolic elements of a tree

Let `g` be a hyperbolic element of a group acting on a tree without inversions, and let
`c : ℤ → V` be its axis, a geodesic line on which `g` acts as the translation by its translation
length `ℓ(g) > 0`. An element `h` commuting with `g` maps the axis of `g` to itself, so it acts on
`c` as an isometry of `ℤ`: a translation `n ↦ n + k` or a reflection `n ↦ k - n`. A reflection
would conjugate the translation by `ℓ(g)` into the translation by `-ℓ(g)`, so `h` translates the
axis by some integer `k(h)`, positive, negative or zero. The map `h ↦ k(h)` is a homomorphism from
the centralizer of `g` to `ℤ`, and its kernel fixes the axis pointwise. Hence the centralizer of
`g` is cyclic as soon as only the identity fixes every vertex of the axis.

## Main results

* `TauCeti.GTree.exists_smul_eq_add_of_commute`: an element commuting with a hyperbolic element
  translates its axis.
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

/-- **An element commuting with a hyperbolic element translates its axis.** Let `c` be a geodesic
line that `g` translates by a nonzero amount `t`, so that `g` is hyperbolic with axis `c`. Then
every `h` commuting with `g` acts on `c` as a translation `c n ↦ c (n + k)`. -/
theorem exists_smul_eq_add_of_commute {g h : G} {c : ℤ → T.V}
    (hc : ∀ m n, T.dist (c m) (c n) = (m - n).natAbs) {t : ℤ} (ht : t ≠ 0)
    (hgc : ∀ n, g • c n = c (n + t)) (hgh : Commute g h) : ∃ k : ℤ, ∀ n, h • c n = c (n + k) := by
  have hinj := SerreGraph.injective_of_dist_eq_natAbs hc
  have hrange := (axis_eq_range_of_smul_eq_add hc ht hgc).symm
  -- `h` maps the axis `Set.range c` of `g` into itself, so `h • c n = c (φ n)` for an isometry
  -- `φ` of `ℤ`.
  have hmem (n : ℤ) : h • c n ∈ Set.range c := by
    rw [hrange, smul_mem_axis_iff_of_commute hgh, ← hrange]
    exact Set.mem_range_self n
  choose φ hφ using hmem
  have hiso (m n : ℤ) : (φ m - φ n).natAbs = (m - n).natAbs := by
    rw [← hc, hφ, hφ, dist_smul, hc]
  -- Since `h` commutes with `g`, the isometry `φ` commutes with the translation by `t`, which
  -- rules out a reflection.
  have hcomm : g • h • c 0 = h • g • c 0 := by rw [smul_smul, hgh.eq, mul_smul]
  simp only [← hφ, hgc, zero_add] at hcomm
  have hper := hinj hcomm
  refine ⟨φ 0, fun n => ?_⟩
  have h₁ := hiso 1 0
  have ht₁ := hiso t 1
  have hn₀ := hiso n 0
  have hn₁ := hiso n 1
  rw [← hφ]
  congr 1
  omega

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
    rw [Subgroup.coe_mul, mul_smul, hk, hk] at h
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
