/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: `Subalgebra`, `Subalgebra.centralizer` and the lattice of subalgebras, together with
-- `IsMulCommutative` and `Module.finrank`, all occur in the statements below.
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- Non-public: used only inside the proofs. `Algebra.isMulCommutative_adjoin` comes with the lattice
-- import above; `Subalgebra.eq_of_le_of_finrank_le` turns an inclusion of subalgebras of equal
-- dimension into an equality, and `Submodule.finrank_le` bounds the dimension of a subalgebra by
-- that of the ambient algebra.
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Commutative subalgebras of maximal dimension

Let `A` be a finite-dimensional algebra over a field `K`. Dimensions of subalgebras of `A` are
bounded by `finrank K A`, so among the commutative subalgebras there is one of largest dimension,
and such a subalgebra is its own centralizer: an element commuting with all of it generates,
together with it, a commutative subalgebra, which maximal dimension forces to be it again.

Neither statement needs anything of `A` beyond finite-dimensionality. They become interesting in a
division algebra, where a commutative subalgebra of maximal dimension is a maximal subfield
(`TauCeti.Algebra.exists_subalgebra_isField_isSeparable_finrank_eq_deg` in
`TauCeti/Algebra/CentralSimple/MaximalSubfield/Separable.lean`).

## Main results

* `TauCeti.exists_isMulCommutative_forall_finrank_le`: a finite-dimensional algebra has a
  commutative subalgebra of maximal dimension.
* `Subalgebra.centralizer_eq_self_of_forall_finrank_le`: a commutative subalgebra of maximal
  dimension among the commutative subalgebras containing it, in particular one of maximal
  dimension, is its own centralizer.

## Implementation notes

Commutativity of a subalgebra is Mathlib's `IsMulCommutative` on its coercion to a type, which is
what `Algebra.isMulCommutative_adjoin` produces, rather than a hand-rolled
`∀ x ∈ L, ∀ y ∈ L, x * y = y * x`; `setLike_mul_comm` is the lemma that reads the second off the
first.

Maximality is in dimension over `K`, stated as a bound on commutative subalgebras, and not as
maximality for inclusion; the two agree here, but the dimension form is what the count in a central
simple algebra consumes.
-/

public section

open Module

namespace TauCeti

variable (K A : Type*) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- **A finite-dimensional algebra has a commutative subalgebra of maximal dimension.**

Maximality is in dimension over `K` and is stated as a bound on every commutative subalgebra of
`A`, not as maximality for inclusion.

No hypothesis beyond finite-dimensionality is needed; it is in a division algebra that such a
subalgebra becomes interesting
(`TauCeti.Algebra.exists_subalgebra_isField_isSeparable_finrank_eq_deg`). -/
theorem exists_isMulCommutative_forall_finrank_le :
    ∃ L : Subalgebra K A, IsMulCommutative L ∧
      ∀ M : Subalgebra K A, IsMulCommutative M → finrank K M ≤ finrank K L := by
  classical
  have hle (M : Subalgebra K A) : finrank K M ≤ finrank K A := Submodule.finrank_le M.toSubmodule
  -- `⊥` is commutative, so a commutative subalgebra attains the greatest such dimension.
  obtain ⟨L, hL, hLn⟩ := Nat.findGreatest_spec (hle ⊥)
    (P := fun n ↦ ∃ M : Subalgebra K A, IsMulCommutative M ∧ finrank K M = n)
    ⟨⊥, Algebra.adjoin_empty K A ▸ Algebra.isMulCommutative_adjoin K (by simp), rfl⟩
  exact ⟨L, hL, fun M hM ↦ hLn ▸ Nat.le_findGreatest (hle M) ⟨M, hM, rfl⟩⟩

end TauCeti

namespace Subalgebra

variable {K A : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- **A commutative subalgebra of maximal dimension is its own centralizer.**

Maximality enters as the hypothesis `hmax`: no commutative subalgebra of `A` containing `L` has
larger dimension over `K`. The bound over all commutative subalgebras of `A` that
`TauCeti.exists_isMulCommutative_forall_finrank_le` produces implies it.

Nothing beyond finite-dimensionality is asked of `A`; it is in a division algebra that the
conclusion becomes the maximality of a subfield
(`TauCeti.Algebra.exists_subalgebra_isField_isSeparable_finrank_eq_deg`). -/
theorem centralizer_eq_self_of_forall_finrank_le (L : Subalgebra K A) [IsMulCommutative L]
    (hmax : ∀ M : Subalgebra K A, L ≤ M → IsMulCommutative M → finrank K M ≤ finrank K L) :
    centralizer K (L : Set A) = L := by
  refine le_antisymm (fun x hx ↦ ?_)
    fun y hy ↦ (mem_centralizer_iff K).2 fun z hz ↦ setLike_mul_comm hz hy
  -- `L` and `x` generate a commutative subalgebra containing `L`, which `hmax` forces to be `L`.
  have hsub : L ≤ Algebra.adjoin K (insert x (L : Set A)) := fun a ha ↦
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha)
  have hM := Algebra.isMulCommutative_adjoin K <|
    Set.Pairwise.insert_of_symm_of_refl (fun a ha b hb _ ↦ setLike_mul_comm ha hb)
      fun b hb ↦ ((mem_centralizer_iff K).1 hx b hb).symm
  rw [eq_of_le_of_finrank_le hsub (hmax _ hsub hM)]
  exact Algebra.subset_adjoin (Set.mem_insert _ _)

end Subalgebra

end
