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
-- `Subalgebra.isMulCommutative_bot` supplies the commutative subalgebra `⊥` that starts the search
-- for one of maximal dimension.
import TauCeti.Algebra.Algebra.Subalgebra.Lattice

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

* `TauCeti.exists_forall_finrank_le`: among the subalgebras of a finite-dimensional algebra
  satisfying a predicate, if there are any, one has maximal dimension.
* `TauCeti.exists_isMulCommutative_forall_finrank_le`: a finite-dimensional algebra has a
  commutative subalgebra of maximal dimension.
* `Subalgebra.pairwise_commute_insert_of_mem_centralizer`: adjoining to a commutative subalgebra an
  element of its centralizer gives a set of pairwise commuting elements.
* `Subalgebra.mem_of_finrank_adjoin_insert_le`: an element whose adjunction does not raise the
  dimension of a subalgebra already lies in it.
* `Subalgebra.centralizer_eq_self_of_forall_finrank_le`: a commutative subalgebra of maximal
  dimension among the commutative subalgebras containing it, in particular one of maximal
  dimension, is its own centralizer.

## Implementation notes

Commutativity of a subalgebra is Mathlib's `IsMulCommutative` on its coercion to a type, which is
what `Algebra.isMulCommutative_adjoin` produces, rather than a hand-rolled
`∀ x ∈ L, ∀ y ∈ L, x * y = y * x`; `setLike_mul_comm` is the lemma that reads the second off the
first.

The hypothesis of the centralizer theorem is maximality for inclusion among commutative
subalgebras, phrased as a dimension bound over the commutative subalgebras containing `L` (the two
are equivalent by `Subalgebra.eq_of_le_of_finrank_le`). The bound over all commutative subalgebras
produced by `TauCeti.exists_isMulCommutative_forall_finrank_le` implies it, and is the form that the
count in a central simple algebra consumes.
-/

public section

open Module

namespace Subalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Adjoining to a commutative subalgebra an element of its centralizer gives a set of pairwise
commuting elements. -/
theorem pairwise_commute_insert_of_mem_centralizer (L : Subalgebra R A) [IsMulCommutative L]
    {x : A} (hx : x ∈ centralizer R (L : Set A)) : (insert x (L : Set A)).Pairwise Commute :=
  Set.Pairwise.insert_of_symm_of_refl (fun _ ha _ hb _ ↦ setLike_mul_comm ha hb)
    fun b hb ↦ ((mem_centralizer_iff R).1 hx b hb).symm

end Subalgebra

namespace TauCeti

variable (K A : Type*) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- **Among the subalgebras satisfying a predicate, one has maximal dimension**, provided that some
subalgebra satisfies it: dimensions of subalgebras are bounded by `finrank K A`. -/
theorem exists_forall_finrank_le (P : Subalgebra K A → Prop) (hP : ∃ M, P M) :
    ∃ L, P L ∧ ∀ M, P M → finrank K M ≤ finrank K L := by
  classical
  have hle (M : Subalgebra K A) : finrank K M ≤ finrank K A := Submodule.finrank_le M.toSubmodule
  obtain ⟨M₀, hM₀⟩ := hP
  obtain ⟨L, hL, hLn⟩ := Nat.findGreatest_spec (hle M₀)
    (P := fun n ↦ ∃ M, P M ∧ finrank K M = n) ⟨M₀, hM₀, rfl⟩
  exact ⟨L, hL, fun M hM ↦ hLn ▸ Nat.le_findGreatest (hle M) ⟨M, hM, rfl⟩⟩

/-- **A finite-dimensional algebra has a commutative subalgebra of maximal dimension.**

Maximality is in dimension over `K` and is stated as a bound on every commutative subalgebra of
`A`, not as maximality for inclusion.

No hypothesis beyond finite-dimensionality is needed; it is in a division algebra that such a
subalgebra becomes interesting
(`TauCeti.Algebra.exists_subalgebra_isField_isSeparable_finrank_eq_deg`). -/
theorem exists_isMulCommutative_forall_finrank_le :
    ∃ L : Subalgebra K A, IsMulCommutative L ∧
      ∀ M : Subalgebra K A, IsMulCommutative M → finrank K M ≤ finrank K L :=
  exists_forall_finrank_le K A (fun M ↦ IsMulCommutative M) ⟨⊥, inferInstance⟩

end TauCeti

namespace Subalgebra

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- An element whose adjunction to a subalgebra does not raise its dimension already lies in it. -/
theorem mem_of_finrank_adjoin_insert_le {L : Subalgebra K A} {x : A}
    [FiniteDimensional K (Algebra.adjoin K (insert x (L : Set A)))]
    (h : finrank K (Algebra.adjoin K (insert x (L : Set A))) ≤ finrank K L) : x ∈ L :=
  eq_of_le_of_finrank_le (fun _ ha ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha)) h ▸
    Algebra.subset_adjoin (Set.mem_insert _ _)

variable [FiniteDimensional K A]

/-- **A commutative subalgebra of maximal dimension is its own centralizer.**

Maximality enters as the hypothesis `hmax`: no commutative subalgebra of `A` containing `L` has
larger dimension over `K`. The bound over all commutative subalgebras of `A` that
`TauCeti.exists_isMulCommutative_forall_finrank_le` produces implies it.

Nothing beyond finite-dimensionality is asked of `A`; it is in a division algebra that the
conclusion becomes the maximality of a subfield
(`TauCeti.Algebra.exists_subalgebra_isField_isSeparable_finrank_eq_deg`). -/
theorem centralizer_eq_self_of_forall_finrank_le (L : Subalgebra K A) [IsMulCommutative L]
    (hmax : ∀ M : Subalgebra K A, L ≤ M → IsMulCommutative M → finrank K M ≤ finrank K L) :
    centralizer K (L : Set A) = L :=
  le_antisymm
    (fun _ hx ↦ mem_of_finrank_adjoin_insert_le <| hmax _
      (fun _ ha ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha))
      (Algebra.isMulCommutative_adjoin K (L.pairwise_commute_insert_of_mem_centralizer hx)))
    fun _ hy ↦ (mem_centralizer_iff K).2 fun _ hz ↦ setLike_mul_comm hz hy

end Subalgebra

end
