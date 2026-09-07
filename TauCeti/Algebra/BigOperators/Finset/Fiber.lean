/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Regrouping a finite sum by the fibres of a map

A sum over a finite type can be taken fibrewise along any map out of it: sum over the values the
map actually takes, and within each value over the indices sent there.

Mathlib's `Fintype.sum_fiberwise` says this with the outer sum ranging over the whole codomain,
which needs the codomain finite. The version here indexes the outer sum by the *image* instead,
so it applies to a map into an arbitrary type — the situation whenever the codomain is a
quotient or a subtype with no finiteness available.

## Main results

* `TauCeti.sum_eq_sum_image_fiber`: `∑ i, F i` is the sum, over the values `g` takes, of the sums
  of `F` over the fibres of `g`.
-/

public section

namespace TauCeti

open Finset

/-- **A finite sum is the sum over the values actually taken of the sums over their fibres.**
Summing `F` over all of `ι` is summing, over each `k` in the image of `g`, the contribution of
the indices `g` sends to `k`.

The outer index is `Finset.univ.image g` rather than all of `κ`, so no finiteness of `κ` is
needed; that is the difference from `Fintype.sum_fiberwise`. -/
theorem sum_eq_sum_image_fiber {ι κ M : Type*} [Fintype ι] [DecidableEq κ] [AddCommMonoid M]
    (g : ι → κ) (F : ι → M) :
    ∑ i, F i = ∑ k ∈ univ.image g, ∑ i : {i // g i = k}, F i := by
  rw [← sum_fiberwise_of_maps_to (g := g) fun i _ ↦ mem_image_of_mem _ (mem_univ i)]
  exact sum_congr rfl fun k _ ↦
    sum_subtype (p := fun i ↦ g i = k) (univ.filter fun i ↦ g i = k) (fun i ↦ by simp) F

end TauCeti
