/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite intersections of covering sieves

For sieves on a single object of a site `(C, J)`, the intersection of a finite family of sieves is
covering if and only if every member is. The intersection of infinitely many covering sieves need
not be covering.

## Main declarations

* `CategoryTheory.GrothendieckTopology.iInf_covering`,
  `CategoryTheory.GrothendieckTopology.iInf_covering_iff`: the intersection of a finite family of
  sieves is covering if and only if every member is.
-/

public section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- The intersection of a finite family of covering sieves is covering. -/
theorem iInf_covering (J : GrothendieckTopology C) {ι : Type*} [Finite ι] {X : C}
    {R : ι → Sieve X} (hR : ∀ i, R i ∈ J X) : ⨅ i, R i ∈ J X := by
  cases nonempty_fintype ι
  simpa [Finset.inf_eq_iInf] using Finset.inf_induction (p := (· ∈ J X)) (J.top_mem X)
    (fun _ h₁ _ h₂ ↦ J.intersection_covering h₁ h₂) fun i (_ : i ∈ Finset.univ) ↦ hR i

/-- The intersection of a finite family of sieves is covering if and only if every member is. -/
@[simp]
theorem iInf_covering_iff (J : GrothendieckTopology C) {ι : Type*} [Finite ι] {X : C}
    {R : ι → Sieve X} : ⨅ i, R i ∈ J X ↔ ∀ i, R i ∈ J X :=
  ⟨fun h i ↦ J.superset_covering (iInf_le R i) h, J.iInf_covering⟩

end CategoryTheory.GrothendieckTopology
