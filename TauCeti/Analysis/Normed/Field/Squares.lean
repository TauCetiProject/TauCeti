/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Constructions
public import TauCeti.Algebra.Group.PowMonoidHom
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# The powers are open in the units of a normed field

Openness of the `n`-th powers, and in particular of the squares, in the units `Kˣ` of a complete
normed field is what makes the square-class group `Kˣ ⧸ (Kˣ)²` discrete, so that invariants with
values in it, such as the spinor norm, have open kernels. This is the `NormedField` counterpart of
`TauCeti.isOpen_range_powMonoidHom`, which is stated for nonarchimedean local fields.

## Main results

* `TauCeti.isOpen_range_powMonoidHom_units`: the `n`-th powers are open in the units of a complete
  normed field in which `n ≠ 0`.
* `TauCeti.isOpen_square_units`: the squares are open in the units of a complete normed field in
  which `2 ≠ 0`.
-/

public section

namespace TauCeti

open scoped Topology in
/-- **The `n`-th powers are open in the units of a complete normed field** in which `n` is
nonzero. -/
theorem isOpen_range_powMonoidHom_units {K : Type*} [NormedField K] [CompleteSpace K] {n : ℕ}
    (hn : (n : K) ≠ 0) : IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with h | ⟨⟨h', rfl⟩⟩
  · exact isOpen_discrete _
  have hd : HasStrictDerivAt (fun x : K ↦ x ^ n) ((n : ℕ) * (1 : K) ^ (n - 1)) 1 :=
    hasStrictDerivAt_pow n 1
  have hne : ((n : ℕ) * (1 : K) ^ (n - 1)) ≠ 0 := by simpa using hn
  have hmap := hd.map_nhds_eq hne
  have hrange : Set.range (fun x : K ↦ x ^ n) ∈ 𝓝 (1 : K) := by
    have := Filter.range_mem_map (m := fun x : K ↦ x ^ n) (f := 𝓝 (1 : K))
    rw [hmap] at this
    simpa using this
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
    (Filter.mem_of_superset (Units.continuous_val.continuousAt.preimage_mem_nhds
      (by simpa using hrange)) ?_)
  rintro u ⟨x, hx⟩
  obtain ⟨w, rfl⟩ : IsUnit x :=
    (isUnit_pow_iff hn0).1 (by have h : x ^ n = u := hx; rw [h]; exact u.isUnit)
  exact ⟨w, Units.ext (by simpa using hx)⟩

/-- **The squares are open in the units of a complete normed field** in which `2` is nonzero. -/
theorem isOpen_square_units {K : Type*} [NormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) : IsOpen (Subgroup.square Kˣ : Set Kˣ) := by
  rw [square_eq_range_powMonoidHom]
  exact isOpen_range_powMonoidHom_units (n := 2) (by exact_mod_cast h2)

end TauCeti
