/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# `n`-connected maps

A continuous map `f : X → Y` is **`n`-connected** if every point of `Y` is joined by a path to a
point of the image of `f`, and the induced map `π_k(X, x) → π_k(Y, f x)` is injective for every
`k < n` and surjective for every `k ≤ n`, at every point `x : X`. Equivalently, the pair formed
by the mapping cylinder of `f` and its bottom face is `n`-connected (Hatcher, *Algebraic
Topology*, Section 4.1). Weak homotopy equivalences are exactly the maps that are `n`-connected
for every `n`.

`n`-connected maps are the range in which homotopy groups control homology: an `n`-connected map
induces isomorphisms on singular homology below degree `n` and a surjection in degree `n`
(`ContinuousMap.IsNConnected.isIso_singularHomologyMap` and
`ContinuousMap.IsNConnected.epi_singularHomologyMap`, in
`TauCeti.AlgebraicTopology.Singular.Homotopy.ConnectedMap`). For instance, the inclusion of the
`n`-skeleton of a CW complex is `n`-connected (`TauCeti.isNConnected_inclusion_skeletonLT`).

This file defines the predicate on Mathlib's cubical homotopy groups and proves its closure
properties: it depends only on the homotopy class of the map, it is preserved by composition, and
composing on either side with a weak homotopy equivalence neither creates nor destroys it.

## Main declarations

* `ContinuousMap.IsNConnected`: the predicate.
* `ContinuousMap.IsNConnected.map_injective`, `ContinuousMap.IsNConnected.map_surjective`: the
  conditions for homotopy groups indexed by any finite type of cube directions.
* `ContinuousMap.isWeakHomotopyEquivalence_iff_forall_isNConnected`: a map is a weak homotopy
  equivalence exactly when it is `n`-connected for every `n`.
* `ContinuousMap.IsNConnected.of_homotopic`, `ContinuousMap.IsNConnected.comp`: invariance under
  homotopy and closure under composition.
* `ContinuousMap.IsWeakHomotopyEquivalence.isNConnected_iff_of_comp_eq`: in a square
  `g ∘ i = j ∘ f` with `f` and `g` weak homotopy equivalences, `i` and `j` have the same
  connectivity.
* `ContinuousMap.IsWeakHomotopyEquivalence.isNConnected_comp_iff`,
  `ContinuousMap.IsWeakHomotopyEquivalence.isNConnected_comp_iff'`: composing with a weak homotopy
  equivalence, on the left or on the right, does not change the connectivity.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, the discussion of `n`-connected maps and mapping cylinders.
-/

public section

open scoped Topology Topology.Homotopy ContinuousMap
open Topology.Homotopy

namespace ContinuousMap

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : C(X, Y)} {g : C(Y, Z)} {n : ℕ}

/-- A continuous map `f : X → Y` is **`n`-connected** if every point of `Y` is joined by a path to
a point of the image of `f`, and the induced map `π_k(X, x) → π_k(Y, f x)` is injective for every
`k < n` and surjective for every `k ≤ n`, at every point `x : X`.

In degree `0`, where `π_0(X, x)` is the set of path components of `X`, injectivity says that `f`
is injective on path components. -/
structure IsNConnected (f : C(X, Y)) (n : ℕ) : Prop where
  /-- Every point of the target is joined by a path to a point of the image. -/
  exists_joined (y : Y) : ∃ x, Joined (f x) y
  /-- The induced map `π_k(X, x) → π_k(Y, f x)` is injective for `k < n`. -/
  injective (k : ℕ) (hk : k < n) (x : X) :
    Function.Injective (HomotopyGroup.map (N := Fin k) f (rfl : f x = f x))
  /-- The induced map `π_k(X, x) → π_k(Y, f x)` is surjective for `k ≤ n`. -/
  surjective (k : ℕ) (hk : k ≤ n) (x : X) :
    Function.Surjective (HomotopyGroup.map (N := Fin k) f (rfl : f x = f x))

namespace IsNConnected

/-- An `n`-connected map induces an injection on the homotopy group indexed by any finite type of
fewer than `n` cube directions. -/
theorem map_injective (hf : f.IsNConnected n) (N : Type*) [Finite N] (hN : Nat.card N < n)
    (x : X) : Function.Injective (HomotopyGroup.map (N := N) f (rfl : f x = f x)) := by
  rw [HomotopyGroup.map_eq_congrEquiv_symm_comp f rfl (Finite.equivFin N)]
  exact (Equiv.injective _).comp ((hf.injective _ hN x).comp (Equiv.injective _))

/-- An `n`-connected map induces a surjection on the homotopy group indexed by any finite type of
at most `n` cube directions. -/
theorem map_surjective (hf : f.IsNConnected n) (N : Type*) [Finite N] (hN : Nat.card N ≤ n)
    (x : X) : Function.Surjective (HomotopyGroup.map (N := N) f (rfl : f x = f x)) := by
  rw [HomotopyGroup.map_eq_congrEquiv_symm_comp f rfl (Finite.equivFin N)]
  exact (Equiv.surjective _).comp ((hf.surjective _ hN x).comp (Equiv.surjective _))

/-- An `n`-connected map is `m`-connected for every `m ≤ n`. -/
theorem mono (hf : f.IsNConnected n) {m : ℕ} (hmn : m ≤ n) : f.IsNConnected m where
  exists_joined := hf.exists_joined
  injective k hk := hf.injective k (hk.trans_le hmn)
  surjective k hk := hf.surjective k (hk.trans hmn)

/-- A map homotopic to an `n`-connected map is `n`-connected. -/
theorem of_homotopic {f₀ f₁ : C(X, Y)} (hf : f₀.IsNConnected n) (h : f₀.Homotopic f₁) :
    f₁.IsNConnected n := by
  refine ⟨fun y ↦ ?_, fun k hk x ↦ ?_, fun k hk x ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hf.exists_joined y
    exact ⟨x, (Joined.symm ⟨h.some.evalAt x⟩).trans hx⟩
  · rw [HomotopyGroup.map_eq_homotopyGroupEquivOfPath_comp_of_homotopy h.some]
    exact (Equiv.injective _).comp (hf.injective k hk x)
  · rw [HomotopyGroup.map_eq_homotopyGroupEquivOfPath_comp_of_homotopy h.some]
    exact (Equiv.surjective _).comp (hf.surjective k hk x)

/-- A composite of `n`-connected maps is `n`-connected. -/
theorem comp (hg : g.IsNConnected n) (hf : f.IsNConnected n) : (g.comp f).IsNConnected n where
  exists_joined z := by
    obtain ⟨y, hy⟩ := hg.exists_joined z
    obtain ⟨x, hx⟩ := hf.exists_joined y
    exact ⟨x, (hx.map g.continuous).trans hy⟩
  injective k hk x :=
    HomotopyGroup.map_comp_map g rfl f rfl ▸ (hg.injective k hk (f x)).comp (hf.injective k hk x)
  surjective k hk x :=
    HomotopyGroup.map_comp_map g rfl f rfl ▸
      (hg.surjective k hk (f x)).comp (hf.surjective k hk x)

end IsNConnected

namespace IsWeakHomotopyEquivalence

/-- A weak homotopy equivalence is `n`-connected for every `n`. -/
theorem isNConnected (hf : f.IsWeakHomotopyEquivalence) (n : ℕ) : f.IsNConnected n where
  exists_joined := hf.exists_joined
  injective k _ x := (hf.bijective k x).injective
  surjective k _ x := (hf.bijective k x).surjective

section Square

variable {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y'] {g : C(X', Y')}
  {i : C(X, X')} {j : C(Y, Y')}

/-- In a square `g ∘ i = j ∘ f` whose maps `f` and `g` are weak homotopy equivalences, `j` is
`n`-connected exactly when `i` is. -/
theorem isNConnected_iff_of_comp_eq (hf : f.IsWeakHomotopyEquivalence)
    (hg : g.IsWeakHomotopyEquivalence) (hi : g.comp i = j.comp f) :
    j.IsNConnected n ↔ i.IsNConnected n := by
  have h₀ := hf.forall_exists_joined_iff_of_comp_eq hg hi
  have h₁ (k : ℕ) := hf.forall_injective_map_iff_of_comp_eq hg hi (Fin k)
  have h₂ (k : ℕ) := hf.forall_surjective_map_iff_of_comp_eq hg hi (Fin k)
  exact ⟨fun hj ↦ ⟨h₀.1 hj.exists_joined, fun k hk ↦ (h₁ k).1 (hj.injective k hk),
      fun k hk ↦ (h₂ k).1 (hj.surjective k hk)⟩,
    fun h ↦ ⟨h₀.2 h.exists_joined, fun k hk ↦ (h₁ k).2 (h.injective k hk),
      fun k hk ↦ (h₂ k).2 (h.surjective k hk)⟩⟩

end Square

/-- **Composing on the left with a weak homotopy equivalence does not change connectivity.** If
`g` is a weak homotopy equivalence, then `g ∘ f` is `n`-connected exactly when `f` is. -/
theorem isNConnected_comp_iff (hg : g.IsWeakHomotopyEquivalence) :
    (g.comp f).IsNConnected n ↔ f.IsNConnected n :=
  IsWeakHomotopyEquivalence.id.isNConnected_iff_of_comp_eq hg rfl

/-- **Composing on the right with a weak homotopy equivalence does not change connectivity.** If
`f` is a weak homotopy equivalence, then `g ∘ f` is `n`-connected exactly when `g` is. -/
theorem isNConnected_comp_iff' (hf : f.IsWeakHomotopyEquivalence) :
    (g.comp f).IsNConnected n ↔ g.IsNConnected n :=
  (hf.isNConnected_iff_of_comp_eq (i := g.comp f) (j := g) IsWeakHomotopyEquivalence.id rfl).symm

end IsWeakHomotopyEquivalence

/-- **A map is a weak homotopy equivalence exactly when it is `n`-connected for every `n`.** -/
theorem isWeakHomotopyEquivalence_iff_forall_isNConnected :
    f.IsWeakHomotopyEquivalence ↔ ∀ n, f.IsNConnected n :=
  ⟨fun hf n ↦ hf.isNConnected n, fun hf ↦
    ⟨(hf 0).exists_joined, fun k x ↦
      ⟨(hf (k + 1)).injective k (Nat.lt_add_one k) x, (hf k).surjective k le_rfl x⟩⟩⟩

end ContinuousMap
