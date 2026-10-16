/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Separable.Adjoin
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Separable commutative subalgebras of maximal dimension

A finite-dimensional algebra over a field has a separable commutative subalgebra of maximal
dimension. In a domain, such a subalgebra contains exactly the separable elements of its
centralizer: adjoining any other separable centralizing element would give a larger separable
commutative subalgebra.

In a finite-dimensional division algebra, a commutative subalgebra is a subfield. These results
provide the maximality argument used to construct separable maximal subfields of central
division algebras. They do not assert that the entire centralizer is already commutative.

## References

* R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 13.
-/

public section

namespace TauCeti

variable (K A : Type*) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- A finite-dimensional algebra has a separable commutative subalgebra whose dimension is
at least that of every separable commutative subalgebra. -/
theorem exists_isMulCommutative_isSeparable_forall_finrank_le :
    ∃ L : Subalgebra K A, IsMulCommutative L ∧ Algebra.IsSeparable K L ∧
      ∀ M : Subalgebra K A, IsMulCommutative M → Algebra.IsSeparable K M →
        Module.finrank K M ≤ Module.finrank K L := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ M : Subalgebra K A,
    IsMulCommutative M ∧ Algebra.IsSeparable K M ∧ Module.finrank K M = n
  have hcomm : IsMulCommutative (⊥ : Subalgebra K A) :=
    Algebra.adjoin_empty K A ▸ Algebra.isMulCommutative_adjoin K (by simp)
  have hsep : Algebra.IsSeparable K (⊥ : Subalgebra K A) := by
    apply Subalgebra.isSeparable_iff.mpr
    rintro x hx
    obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp hx
    exact isSeparable_algebraMap r
  have hle (M : Subalgebra K A) : Module.finrank K M ≤ Module.finrank K A :=
    Submodule.finrank_le M.toSubmodule
  have hstart : P (Module.finrank K (⊥ : Subalgebra K A)) := ⟨⊥, hcomm, hsep, rfl⟩
  obtain ⟨L, hLcomm, hLsep, hLn⟩ := Nat.findGreatest_spec (hle ⊥) hstart
  refine ⟨L, hLcomm, hLsep, fun M hMcomm hMsep ↦ ?_⟩
  rw [hLn]
  exact Nat.le_findGreatest (hle M) ⟨M, hMcomm, hMsep, rfl⟩

end TauCeti

namespace Subalgebra

variable {K A : Type*} [Field K] [Ring A] [IsDomain A] [Algebra K A]
  [FiniteDimensional K A]

/-- A separable commutative subalgebra of maximal dimension consists exactly of the separable
elements of its centralizer. -/
theorem mem_iff_isSeparable_and_mem_centralizer (L : Subalgebra K A)
    [IsMulCommutative L] [Algebra.IsSeparable K L]
    (hmax : ∀ M : Subalgebra K A, IsMulCommutative M → Algebra.IsSeparable K M →
      Module.finrank K M ≤ Module.finrank K L) (x : A) :
    x ∈ L ↔ IsSeparable K x ∧ x ∈ centralizer K (L : Set A) := by
  refine ⟨fun hx ↦ ⟨isSeparable_iff.mp inferInstance x hx,
    (mem_centralizer_iff K).mpr fun y hy ↦ setLike_mul_comm hy hx⟩, ?_⟩
  rintro ⟨hsep, hcent⟩
  have hcomm : (insert x (L : Set A)).Pairwise Commute := by
    apply Set.Pairwise.insert
    · exact fun a ha b hb _ ↦ setLike_mul_comm ha hb
    · intro y hy _
      exact ⟨((mem_centralizer_iff K).mp hcent y hy).symm,
        (mem_centralizer_iff K).mp hcent y hy⟩
  have hMcomm := Algebra.isMulCommutative_adjoin K hcomm
  have hMsep : Algebra.IsSeparable K (Algebra.adjoin K (insert x (L : Set A))) := by
    apply hcomm.isSeparable_adjoin_iff.mpr
    rintro y (rfl | hy)
    · exact hsep
    · exact isSeparable_iff.mp inferInstance y hy
  have hle : L ≤ Algebra.adjoin K (insert x (L : Set A)) := fun y hy ↦
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ hy)
  have heq := eq_of_le_of_finrank_le hle (hmax _ hMcomm hMsep)
  exact heq.symm ▸ Algebra.subset_adjoin (Set.mem_insert x (L : Set A))

end Subalgebra
