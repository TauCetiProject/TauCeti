/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Free groups of rank at least two are not nilpotent

Let `x` and `y` be two distinct generators of the free group `FreeGroup X`. The left-normed
commutators

`w_0 = x`, `w_{n+1} = ⁅w_n, y⁆`

satisfy `w_n ∈ γ_n`, the `n`-th term of the lower central series, and none of them is trivial.
Hence no term of the lower central series of a free group of rank at least two is trivial, and such
a free group is not nilpotent.

The nontriviality is detected in the infinite dihedral group `DihedralGroup 0`, the group of
isometries `t ↦ ±t + m` of `ℤ`. Send `x` to the translation `r 1 : t ↦ t + 1` and every other
generator to the reflection `sr 0 : t ↦ -t`. The commutator of a translation `r m` with the
reflection is the translation `r (2 * m)`, so `w_n` maps to the translation `r (2 ^ n)`, which is
not the identity.

## Main results

* `FreeGroup.iterate_commutatorElement_ne_one`: the left-normed commutator
  `⁅⋯⁅⁅x, y⁆, y⁆, ⋯, y⁆` of two distinct generators is nontrivial.
* `FreeGroup.lowerCentralSeries_ne_bot`: no term of the lower central series of a free group of
  rank at least two is trivial.
* `FreeGroup.not_isNilpotent`: a free group of rank at least two is not nilpotent.

## References

* W. Magnus, A. Karrass and D. Solitar, *Combinatorial Group Theory*, Chapter 5, for the lower
  central series of free groups.
-/

public section

open Subgroup
open scoped commutatorElement

namespace FreeGroup

variable {X : Type*}

/-- **Left-normed commutators of two generators are nontrivial.** For distinct generators `x_i`
and `x_j` of a free group, the iterated commutator `⁅⋯⁅⁅x_i, x_j⁆, x_j⁆, ⋯, x_j⁆` with `n`
brackets is not the identity. -/
theorem iterate_commutatorElement_ne_one {i j : X} (hij : i ≠ j) (n : ℕ) :
    (fun w ↦ ⁅w, of j⁆)^[n] (of i) ≠ 1 := by
  classical
  let f : FreeGroup X →* DihedralGroup 0 :=
    lift fun k ↦ if k = i then DihedralGroup.r 1 else DihedralGroup.sr 0
  have hf : ∀ m, f ((fun w ↦ ⁅w, of j⁆)^[m] (of i)) = DihedralGroup.r (2 ^ m) := by
    intro m
    induction m with
    | zero => simp [f]
    | succ m ih =>
      rw [Function.iterate_succ_apply', map_commutatorElement, ih, commutatorElement_def]
      simp only [f, lift_apply_of, hij.symm, ↓reduceIte, DihedralGroup.inv_r,
        DihedralGroup.inv_sr, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr]
      congr 1
      ring
  intro h
  have h2 := hf n
  rw [h, _root_.map_one, DihedralGroup.one_def, DihedralGroup.r.injEq] at h2
  exact pow_ne_zero n (two_ne_zero (α := ℤ)) h2.symm

/-- **The lower central series of a free group of rank at least two never vanishes.** Every term
`γ_n` contains the nontrivial left-normed commutator `⁅⋯⁅⁅x_i, x_j⁆, x_j⁆, ⋯, x_j⁆` of two
distinct generators. -/
theorem lowerCentralSeries_ne_bot [Nontrivial X] (n : ℕ) :
    (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries n ≠ ⊥ := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne X
  have hmem : ∀ m, (fun w ↦ ⁅w, of j⁆)^[m] (of i) ∈
      (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', Subgroup.lowerCentralSeries_succ]
      exact commutator_mem_commutator ih (mem_top _)
  exact (ne_bot_iff_exists_ne_one).2
    ⟨⟨_, hmem n⟩, fun h ↦ iterate_commutatorElement_ne_one hij n (congrArg Subtype.val h)⟩

/-- **Free groups of rank at least two are not nilpotent.** -/
theorem not_isNilpotent [Nontrivial X] : ¬ Group.IsNilpotent (FreeGroup X) := by
  rw [Subgroup.nilpotent_iff_lowerCentralSeries]
  rintro ⟨n, hn⟩
  exact lowerCentralSeries_ne_bot n hn

end FreeGroup
