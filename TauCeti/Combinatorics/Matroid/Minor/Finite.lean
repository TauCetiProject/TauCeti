/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Matroid.Minor.Contract

/-!
# Finite ground sets of single-element minors

For a finite matroid `M`, this file identifies the finite ground sets of the deletion `M ＼ {e}`
and the contraction `M ／ {e}`, as finsets, with the ground set of `M` with `e` erased. Sums over
the subsets of the ground set, such as the one defining the Tutte polynomial, use these to compare
a matroid with its single-element minors.

## Main declarations

* `Matroid.toFinset_ground_deleteElem`: the ground finset of `M ＼ {e}`.
* `Matroid.toFinset_ground_contractElem`: the ground finset of `M ／ {e}`.
-/

public section

namespace Matroid

variable {α : Type*} [DecidableEq α] (M : Matroid α) [M.Finite] {e : α}

/-- The ground set of `M ＼ {e}`, as a finset, is the ground set of `M` with `e` erased. -/
lemma toFinset_ground_deleteElem :
    (M ＼ {e}).ground_finite.toFinset = M.ground_finite.toFinset.erase e := by
  ext
  simp [and_comm]

/-- The ground set of `M ／ {e}`, as a finset, is the ground set of `M` with `e` erased. -/
lemma toFinset_ground_contractElem :
    (M ／ {e}).ground_finite.toFinset = M.ground_finite.toFinset.erase e := by
  ext
  simp [and_comm]

end Matroid
