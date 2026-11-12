/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Constructions
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# The squares are open in the units of a normed field

Squaring has derivative `2` at `1`, so by the inverse function theorem every complete nontrivially
normed field in which `2 ≠ 0` has the squares open in `Kˣ`.

## Main results

* `TauCeti.isOpen_square_units`: the squares are open in the units of a complete nontrivially
  normed field in which `2 ≠ 0`.
-/

public section

namespace TauCeti

open scoped Topology in
/-- **The squares are open in the units of a complete nontrivially normed field** in which `2` is
nonzero: squaring has derivative `2` at `1`, so by the inverse function theorem the squares
contain a neighbourhood of `1`. -/
theorem isOpen_square_units {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) : IsOpen (Subgroup.square Kˣ : Set Kˣ) := by
  have hd : HasStrictDerivAt (fun x : K ↦ x ^ 2) ((2 : ℕ) * (1 : K) ^ (2 - 1)) 1 :=
    hasStrictDerivAt_pow 2 1
  have hne : ((2 : ℕ) * (1 : K) ^ (2 - 1)) ≠ 0 := by simpa using h2
  have hmap := hd.map_nhds_eq hne
  have hrange : Set.range (fun x : K ↦ x ^ 2) ∈ 𝓝 (1 : K) := by
    have := Filter.range_mem_map (m := fun x : K ↦ x ^ 2) (f := 𝓝 (1 : K))
    rw [hmap] at this
    simpa using this
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
    (Filter.mem_of_superset (Units.continuous_val.continuousAt.preimage_mem_nhds
      (by simpa using hrange)) ?_)
  rintro u ⟨x, hx⟩
  obtain ⟨w, rfl⟩ : IsUnit x := isUnit_of_mul_isUnit_left (x := x) (y := x)
    (by have h : x ^ 2 = u := hx; rw [← sq, h]; exact u.isUnit)
  exact ⟨w, Units.ext (by simpa [sq] using hx.symm)⟩

end TauCeti
