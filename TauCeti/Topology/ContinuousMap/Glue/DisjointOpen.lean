/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import TauCeti.Algebra.BigOperators.Finprod

/-!
# Gluing on pairwise disjoint open sets

Functions and continuous maps given on the pieces of a family of pairwise disjoint open sets glue
to a function or a continuous map on their union. For functions to a commutative monoid the glued
function is the product `∏ᶠ k, (T k).mulIndicator (f k)` of the indicators, which equals `f j` on
`T j` (`TauCeti.finprod_mulIndicator_of_mem`). When `T j` is open it equals `f j` near every point
of `T j`, so it inherits any local property of `f j` there. Continuous maps on the products
`X × T j` glue by Mathlib's `ContinuousMap.liftCover` to a continuous map on `X × ⋃ j, T j`; the
factor `X` carries a time parameter when gluing homotopies.

## Main results

* `TauCeti.finprod_mulIndicator_eventuallyEq` and `TauCeti.finsum_indicator_eventuallyEq`: near a
  point of an open piece `T j`, the glued function equals `f j`.
* `TauCeti.exists_continuousMap_prod_iUnion`: continuous maps `X × T j → Y` on pairwise disjoint
  open sets `T j` glue to a continuous map `X × ⋃ j, T j → Y`.
-/

public section

namespace TauCeti

open Function Set Filter Topology

variable {α ι : Type*} [TopologicalSpace α] {T : ι → Set α}

/-- If the sets `T k` are pairwise disjoint and `T j` is open, then near a point of `T j` the
product of the multiplicative indicators of `f k` on `T k` equals `f j`. -/
@[to_additive /-- If the sets `T k` are pairwise disjoint and `T j` is open, then near a point of
`T j` the sum of the indicators of `f k` on `T k` equals `f j`. -/]
theorem finprod_mulIndicator_eventuallyEq {M : Type*} [CommMonoid M]
    (hT : Pairwise (Disjoint on T)) (f : ι → α → M) {j : ι} (hTj : IsOpen (T j)) {x : α}
    (hx : x ∈ T j) : (fun y ↦ ∏ᶠ k, (T k).mulIndicator (f k) y) =ᶠ[𝓝 x] f j :=
  eventually_of_mem (hTj.mem_nhds hx) fun _ hy ↦ finprod_mulIndicator_of_mem hT f hy

/-- Continuous maps `φ j : X × T j → Y` on pairwise disjoint open sets `T j` glue to a continuous
map of `X × ⋃ j, T j` to `Y`. -/
theorem exists_continuousMap_prod_iUnion {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (hTo : ∀ j, IsOpen (T j)) (hT : Pairwise (Disjoint on T)) (φ : ∀ j, C(X × T j, Y)) :
    ∃ ψ : C(X × ↥(⋃ j, T j), Y),
      ∀ j p (x : ↥(⋃ j, T j)) (hx : (x : α) ∈ T j), ψ (p, x) = φ j (p, ⟨x, hx⟩) := by
  let S (j : ι) : Set (X × ↥(⋃ j, T j)) := {q | (q.2 : α) ∈ T j}
  let φ' (j : ι) : C(S j, Y) :=
    ⟨fun q ↦ φ j (q.val.1, ⟨q.val.2, q.property⟩), (φ j).continuous.comp
      ((continuous_fst.comp continuous_subtypeVal).prodMk
        ((continuous_subtypeVal.comp (continuous_snd.comp continuous_subtypeVal)).subtype_mk _))⟩
  have hφ' (j k : ι) (q : X × ↥(⋃ j, T j)) (hj : q ∈ S j) (hk : q ∈ S k) :
      φ' j ⟨q, hj⟩ = φ' k ⟨q, hk⟩ := by
    obtain rfl : j = k := by_contra fun hjk ↦ (hT hjk).ne_of_mem hj hk rfl
    rfl
  have hS (q : X × ↥(⋃ j, T j)) : ∃ j, S j ∈ 𝓝 q := by
    obtain ⟨j, hj⟩ := mem_iUnion.1 q.2.property
    exact ⟨j, ((hTo j).preimage (continuous_subtypeVal.comp continuous_snd)).mem_nhds hj⟩
  exact ⟨ContinuousMap.liftCover S φ' hφ' hS, fun j p x hx ↦
    ContinuousMap.liftCover_coe (S := S) (φ := φ') (hφ := hφ') (hS := hS) (i := j) ⟨(p, x), hx⟩⟩

end TauCeti
