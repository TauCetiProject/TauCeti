/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Minpoly
public import TauCeti.NumberTheory.NumberField.Units.Regulator.Basic

/-!
# Conjugates of a unit in unit rank one

In a number field of unit rank one, a unit whose value at a real infinite place exceeds `1` has
all its other conjugates of absolute value at most `1`.

## Main results

* `TauCeti.NumberField.Units.norm_le_one_of_mem_roots_erase`: the roots in `ℂ` of the minimal
  polynomial of such a unit, other than its value at that real place, have norm at most `1`.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace NumberField.Units TauCeti.NumberField
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- The conjugates of a unit of a number field of unit rank one, other than its value at a real
place where it exceeds `1`, have absolute value at most `1`. -/
theorem norm_le_one_of_mem_roots_erase (hr : rank K = 1) {w : InfinitePlace K}
    (hw : w.IsReal) (v : (𝓞 K)ˣ) (hw1 : 1 < w v) {z : ℂ}
    (hz : z ∈ ((minpoly ℚ (v : K)).map (algebraMap ℚ ℂ)).roots.erase (embedding w v)) :
    ‖z‖ ≤ 1 := by
  have hintQ : IsIntegral ℚ (v : K) := IsIntegral.of_finite ℚ _
  rw [(minpoly.irreducible hintQ).separable.map |> nodup_roots |>.mem_erase_iff] at hz
  obtain ⟨φ, rfl⟩ := (mem_roots_map_minpoly_iff _ _).mp hz.2
  have hne : InfinitePlace.mk φ ≠ w := by
    intro hφ
    have hreal : ComplexEmbedding.IsReal φ := isReal_of_mk_isReal (hφ.symm ▸ hw)
    exact hz.1 (DFunLike.congr_fun (hφ ▸ embedding_mk_eq_of_isReal hreal).symm _)
  exact (lt_one_of_rank_eq_one_of_ne_of_one_lt hr hne hw1).le

end TauCeti.NumberField.Units
