/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.SetTheory.Cardinal.Order

/-!
# Submodules of free modules over principal ideal rings without zero divisors

Every submodule of a free module over a principal ideal ring without zero divisors is free,
without a finiteness hypothesis on the ambient module. The ring need not be commutative: as in
`IsPrincipalIdealRing`, it suffices that every left ideal is principal. The construction
well-orders an ambient basis and chooses a pivot for each nonzero left ideal of possible leading
coordinates. The pivots form a basis of the submodule by elimination of the greatest coordinate in
the finite support of each vector.

This is the arbitrary-rank form of Lang, *Algebra*, Chapter III, Theorem 7.1.  Mathlib's
`Submodule.nonempty_basis_of_pid` is the finite-rank form.  A projective module embeds in a free
module, so every submodule of a projective module is free as well
(`Submodule.free_of_projective_of_isPrincipalIdealRing`), and so is every module that injects into
a projective module (`Module.Free.of_injective_of_projective_of_isPrincipalIdealRing`).
-/

public section

open Module Set Submodule
open Submodule.IsPrincipal

namespace Submodule

variable {R M : Type*} [Ring R] [NoZeroDivisors R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M]

/-- Every submodule of a free module over a principal ideal ring without zero divisors is free,
with no finiteness assumption on either module. -/
theorem free_of_isPrincipalIdealRing (N : Submodule R M) [Module.Free R M] :
    Module.Free R N := by
  classical
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨_, _⟩ := exists_wellFoundedLT ι
  -- The left ideal of possible `i`-th coordinates of vectors of `N` supported in `Iic i`.
  let I : ι → Ideal R := fun i ↦ (N ⊓ span R (b '' Iic i)).map (b.coord i)
  choose x hx hx_coord using fun i ↦ mem_map.mp (generator_mem (I i))
  -- The pivots: for each index whose ideal is nonzero, a vector of `N` supported in `Iic i`
  -- whose `i`-th coordinate generates that ideal.
  let J : Set ι := {i | generator (I i) ≠ 0}
  let pivot (i : J) : N := ⟨x i, (hx i).1⟩
  have coord_pivot (i : J) : b.coord i (pivot i) = generator (I i) := hx_coord i
  have coord_pivot_eq_zero {i : J} {j : ι} (hij : i.1 < j) : b.coord j (pivot i) = 0 :=
    Finsupp.notMem_support_iff.mp fun hj ↦ (b.mem_span_image.mp (hx i).2 hj).not_gt hij
  -- In a relation among pivots, the greatest index isolates one nonzero coordinate.
  have pivot_linearIndependent : LinearIndependent R pivot := by
    rw [linearIndependent_iff']
    intro s
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert a s hsa ih =>
      have ha : a ∉ s := fun h ↦ (hsa a h).false
      intro g hsum
      have hga : g a = 0 := by
        have := congrArg (b.coord a ∘ₗ N.subtype) hsum
        simp only [Finset.sum_insert ha, map_add, map_sum, map_smul, map_zero, smul_eq_mul,
          LinearMap.comp_apply, subtype_apply, coord_pivot] at this
        rw [Finset.sum_eq_zero fun j hj ↦ by rw [coord_pivot_eq_zero (hsa j hj), mul_zero],
          add_zero] at this
        exact (mul_eq_zero.mp this).resolve_right a.2
      simp only [Finset.sum_insert ha, hga, zero_smul, zero_add] at hsum
      intro i hi
      obtain rfl | hi := Finset.mem_insert.mp hi
      · exact hga
      · exact ih g hsum i hi
  -- Every vector of `N` lies in the span of the pivots: eliminate the greatest coordinate, by
  -- well-founded induction on it, which is valid even when the basis is infinite.
  let P : Submodule R N := span R (range pivot)
  have mem_P (i : ι) : ∀ y : N, ↑(b.repr y).support ⊆ Iic i → y ∈ P := by
    induction i using WellFoundedLT.induction with | _ i ih
    -- A vector with vanishing `i`-th coordinate is supported strictly below `i`.
    have lower (z : N) (hz : ↑(b.repr z).support ⊆ Iic i) (hzi : b.coord i z = 0) :
        z ∈ P := by
      obtain rfl | hz0 := eq_or_ne z 0
      · exact zero_mem P
      have hne : (b.repr z).support.Nonempty := by simpa using hz0
      refine ih _ (lt_of_le_of_ne (hz (Finset.max'_mem _ hne)) fun h ↦ ?_) z
        fun j hj ↦ Finset.le_max' _ _ hj
      exact Finsupp.mem_support_iff.mp (h ▸ Finset.max'_mem _ hne) hzi
    intro y hy
    have hy_span : (y : M) ∈ span R (b '' Iic i) := b.mem_span_image.mpr hy
    obtain ⟨c, hc⟩ := (mem_iff_eq_smul_generator (I i)).mp (mem_map_of_mem ⟨y.2, hy_span⟩)
    by_cases hg : generator (I i) = 0
    · exact lower y hy (by rw [hc, hg, smul_zero])
    rw [← sub_add_cancel y (c • pivot ⟨i, hg⟩)]
    refine add_mem (lower _ ?_ ?_) (smul_mem _ _ (subset_span ⟨_, rfl⟩))
    · exact b.mem_span_image.mp (sub_mem hy_span (smul_mem _ _ (hx i).2))
    · simp only [pivot, Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul, hx_coord, hc,
        sub_self]
  refine .of_basis (Basis.mk pivot_linearIndependent fun y _ ↦ ?_)
  obtain rfl | hy0 := eq_or_ne y 0
  · exact zero_mem P
  have hne : (b.repr y).support.Nonempty := by simpa using hy0
  exact mem_P ((b.repr y).support.max' hne) y fun j hj ↦ Finset.le_max' _ _ hj

/-- Every submodule of a projective module over a principal ideal ring without zero divisors is
free. -/
theorem free_of_projective_of_isPrincipalIdealRing (N : Submodule R M) [Module.Projective R M] :
    Module.Free R N := by
  obtain ⟨s, hs⟩ := Module.projective_def.mp ‹Module.Projective R M›
  have := (N.map s).free_of_isPrincipalIdealRing
  exact .of_equiv (N.equivMapOfInjective s hs.injective).symm

end Submodule

namespace Module.Free

variable {R M N : Type*} [Ring R] [NoZeroDivisors R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A module that injects into a projective module over a principal ideal ring without zero
divisors is free. -/
theorem of_injective_of_projective_of_isPrincipalIdealRing [Module.Projective R M]
    (f : N →ₗ[R] M) (hf : Function.Injective f) : Module.Free R N :=
  have := (LinearMap.range f).free_of_projective_of_isPrincipalIdealRing
  .of_equiv (LinearEquiv.ofInjective f hf).symm

end Module.Free
