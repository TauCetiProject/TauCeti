/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Pi
import Mathlib.Order.WellFoundedSet

/-!
# Finiteness of nonnegative integer vectors in subgroup cosets

Dickson's lemma shows that each coset of a subgroup of `ι → ℤ` has finitely many nonnegative
vectors exactly when the subgroup has no nonzero nonnegative vector. For periodic domains of a
pointed Heegaard diagram, this is the algebraic finiteness result used in the admissibility
argument of Ozsváth–Szabó, *Holomorphic disks and topological invariants for closed
three-manifolds*, Lemma 4.13. Applying it to Whitney disk classes also requires a geometric
correspondence with domain vectors and control of its fibers.

## Main result

* `AddSubgroup.finite_setOf_nonneg_sub_mem_iff`.
-/

public section

namespace TauCeti

/-- A subgroup `P` of `ι → ℤ` contains no nonzero nonnegative vector exactly when each coset
`D₀ + P` contains only finitely many nonnegative vectors. -/
theorem _root_.AddSubgroup.finite_setOf_nonneg_sub_mem_iff {ι : Type*} [Finite ι]
    (P : AddSubgroup (ι → ℤ)) :
    (∀ D₀ : ι → ℤ, {D | 0 ≤ D ∧ D - D₀ ∈ P}.Finite) ↔ ∀ p ∈ P, 0 ≤ p → p = 0 := by
  refine ⟨fun hfin p hp hp0 => by_contra fun hne => ?_, fun h D₀ => ?_⟩
  · refine Set.infinite_of_injective_forall_mem
      (nsmul_left_strictMono (hp0.lt_of_ne' hne)).injective (fun n => ?_) (hfin 0)
    exact ⟨nsmul_nonneg hp0 n, by simpa using nsmul_mem hp n⟩
  · -- Dickson's lemma: the nonnegative vectors of `ι → ℤ` are partially well-ordered.
    have hpwo : (Set.univ.pi fun _ : ι => Set.Ici (0 : ℤ)).IsPWO :=
      Set.IsPWO.pi fun _ => Set.IsWF.isPWO (BddBelow.wellFoundedOn_lt bddBelow_Ici)
    -- Two comparable vectors in the coset differ by a nonnegative vector of `P`.
    refine IsAntichain.finite_of_partiallyWellOrderedOn (fun D hD D' hD' hne hle => hne ?_)
      (hpwo.mono fun D hD i _ => hD.1 i)
    exact (sub_eq_zero.1 (h _ (by simpa using sub_mem hD'.2 hD.2) (sub_nonneg.2 hle))).symm

end TauCeti
