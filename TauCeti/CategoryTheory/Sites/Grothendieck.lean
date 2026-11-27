/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Lattice

/-!
# Finite intersections of covering sieves

For a Grothendieck topology `J`, the intersection of finitely many sieves on `X` covers `X` if
and only if each of them does (`CategoryTheory.GrothendieckTopology.finset_inf_mem_iff`). This
extends Mathlib's `CategoryTheory.GrothendieckTopology.intersection_covering_iff` from two sieves
to the infimum of a finite family; for a family indexed by a finite type this is
`CategoryTheory.GrothendieckTopology.iInf_mem_iff`.
-/

public section

namespace CategoryTheory.GrothendieckTopology

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {ι : Type*} {X : C}

/-- The intersection of finitely many covering sieves is a covering sieve. -/
theorem finset_inf_mem {S : ι → Sieve X} {t : Finset ι} (h : ∀ i ∈ t, S i ∈ J X) :
    t.inf S ∈ J X :=
  Finset.inf_induction (J.top_mem X) (fun _ h₁ _ h₂ ↦ J.intersection_covering h₁ h₂) h

/-- The intersection of finitely many sieves is a covering sieve if and only if each of them is
a covering sieve. -/
@[simp]
theorem finset_inf_mem_iff {S : ι → Sieve X} {t : Finset ι} :
    t.inf S ∈ J X ↔ ∀ i ∈ t, S i ∈ J X :=
  ⟨fun h _ hi ↦ J.superset_covering (Finset.inf_le hi) h, J.finset_inf_mem⟩

/-- The intersection of a family of covering sieves indexed by a finite type is a covering
sieve. -/
theorem iInf_mem [Finite ι] {S : ι → Sieve X} (h : ∀ i, S i ∈ J X) : ⨅ i, S i ∈ J X := by
  have := Fintype.ofFinite ι
  simpa [Finset.inf_univ_eq_iInf] using J.finset_inf_mem (t := Finset.univ) fun i _ ↦ h i

/-- The intersection of a family of sieves indexed by a finite type is a covering sieve if and
only if each of them is a covering sieve. -/
@[simp]
theorem iInf_mem_iff [Finite ι] {S : ι → Sieve X} : ⨅ i, S i ∈ J X ↔ ∀ i, S i ∈ J X :=
  ⟨fun h i ↦ J.superset_covering (iInf_le S i) h, J.iInf_mem⟩

end CategoryTheory.GrothendieckTopology
