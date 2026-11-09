/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Separable.Adjoin
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.Algebra.Algebra.Subalgebra.Lattice
import TauCeti.Algebra.Algebra.Subalgebra.MaximalCommutative

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
  have hsep : Algebra.IsSeparable K (⊥ : Subalgebra K A) := by
    apply Subalgebra.isSeparable_iff.mpr
    rintro x hx
    obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp hx
    exact isSeparable_algebraMap r
  obtain ⟨L, ⟨hLcomm, hLsep⟩, hL⟩ := exists_forall_finrank_le K A
    (fun M ↦ IsMulCommutative M ∧ Algebra.IsSeparable K M) ⟨⊥, inferInstance, hsep⟩
  exact ⟨L, hLcomm, hLsep, fun M hMcomm hMsep ↦ hL M ⟨hMcomm, hMsep⟩⟩

end TauCeti

namespace Subalgebra

variable {K A : Type*} [Field K] [Ring A] [IsDomain A] [Algebra K A]
  [FiniteDimensional K A]

/-- A separable commutative subalgebra of maximal dimension consists exactly of the separable
elements of its centralizer.

Maximality enters as the hypothesis `hmax`: no separable commutative subalgebra of `A` containing
`L` has larger dimension over `K`. The bound over all separable commutative subalgebras that
`TauCeti.exists_isMulCommutative_isSeparable_forall_finrank_le` produces implies it. -/
theorem mem_iff_isSeparable_and_mem_centralizer (L : Subalgebra K A)
    [IsMulCommutative L] [Algebra.IsSeparable K L]
    (hmax : ∀ M : Subalgebra K A, L ≤ M → IsMulCommutative M → Algebra.IsSeparable K M →
      Module.finrank K M ≤ Module.finrank K L) (x : A) :
    x ∈ L ↔ IsSeparable K x ∧ x ∈ centralizer K (L : Set A) := by
  refine ⟨fun hx ↦ ⟨isSeparable_iff.mp inferInstance x hx,
    (mem_centralizer_iff K).mpr fun y hy ↦ setLike_mul_comm hy hx⟩, ?_⟩
  rintro ⟨hsep, hcent⟩
  have hcomm := L.pairwise_commute_insert_of_mem_centralizer hcent
  have hMsep : Algebra.IsSeparable K (Algebra.adjoin K (insert x (L : Set A))) := by
    apply hcomm.isSeparable_adjoin_iff.mpr
    rintro y (rfl | hy)
    · exact hsep
    · exact isSeparable_iff.mp inferInstance y hy
  exact mem_of_finrank_adjoin_insert_le <| hmax _
    (fun _ ha ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha))
    (Algebra.isMulCommutative_adjoin K hcomm) hMsep

end Subalgebra
