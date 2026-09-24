/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Module.Basic
import Mathlib.Algebra.Group.Pi.Torsion
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

* `TauCeti.addSubgroup_finite_setOf_nonneg_sub_mem_iff`.
-/

public section

namespace TauCeti

/-- A subgroup `P` of `ι → ℤ` contains no nonzero nonnegative vector exactly when each coset
`D₀ + P` contains only finitely many nonnegative vectors. -/
theorem addSubgroup_finite_setOf_nonneg_sub_mem_iff {ι : Type*} [Finite ι]
    (P : AddSubgroup (ι → ℤ)) :
    (∀ D₀ : ι → ℤ, {D | 0 ≤ D ∧ D - D₀ ∈ P}.Finite) ↔ ∀ p ∈ P, 0 ≤ p → p = 0 := by
  constructor
  · intro hfin p hp hp0
    by_contra hne
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℤ) • p)
      (fun m n hmn => Nat.cast_injective (smul_left_injective ℤ hne hmn))
      (fun n => ?_) (hfin 0)
    exact ⟨smul_nonneg (Nat.cast_nonneg n) hp0, by simpa using zsmul_mem hp n⟩
  · intro h D₀
    by_contra hinf
    -- Dickson's lemma: the nonnegative vectors of `ι → ℤ` are partially well-ordered.
    have hpwo : (Set.univ.pi fun _ : ι => Set.Ici (0 : ℤ)).IsPWO :=
      Set.IsPWO.pi fun _ => Set.IsWF.isPWO (BddBelow.wellFoundedOn_lt bddBelow_Ici)
    set f := Set.Infinite.natEmbedding _ hinf
    obtain ⟨m, n, hmn, hle⟩ := hpwo.exists_lt (f := fun n => (f n : ι → ℤ))
      fun n i _ => (f n).2.1 i
    have hsub : (f n : ι → ℤ) - f m ∈ P := by
      simpa using sub_mem (f n).2.2 (f m).2.2
    have := h _ hsub (sub_nonneg.2 hle)
    exact hmn.ne (f.injective (Subtype.ext (sub_eq_zero.1 this).symm))

end TauCeti
