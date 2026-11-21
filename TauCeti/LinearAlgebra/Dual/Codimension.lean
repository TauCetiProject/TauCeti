/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.LinearAlgebra.Dual.Basic

/-!
# Codimension of common kernels of functionals

The common kernel of finitely many linear functionals `L i` on a vector space `V` has
codimension the dimension of their span, whether or not `V` is finite-dimensional. Hence it has
codimension at most the number of functionals, with equality exactly when the functionals are
linearly independent. Conversely, a subspace of finite codimension `n` is the common kernel of
`n` linearly independent functionals.

Read as a statement about systems of linear equations, a subspace `W` of finite codimension is
cut out by `finrank K (V ⧸ W)` equations and by no fewer, and a system of that minimal size is
independent. Applied to the range of a linear map `f`, the minimal number of solvability
conditions for `f x = y` is the dimension of the cokernel of `f`. When the kernel is also
finite-dimensional, so that `f` is Fredholm, this number equals the dimension of the kernel
exactly when `f` has index zero (`LinearMap.isLeast_finrank_ker_iff_index_eq_zero`).

## Main results

* `Subspace.finrank_quotient_dualCoannihilator_eq`: the dual coannihilator of a
  finite-dimensional space `W` of functionals has codimension `finrank K W`.
* `Module.Dual.finrank_quotient_iInf_ker_eq_finrank_span`: the common kernel of finitely many
  functionals has codimension the dimension of their span.
* `Module.Dual.finrank_quotient_iInf_ker_le_card` and
  `Module.Dual.linearIndependent_iff_finrank_quotient_iInf_ker_eq_card`: that codimension is at
  most the number of functionals, with equality exactly for linearly independent families.
* `Module.Dual.natCast_finrank_quotient_iInf_ker_le_mk`: the cardinal form of this bound for an
  arbitrary family.
* `Submodule.exists_linearIndependent_iInf_ker_eq` and `Submodule.isLeast_card_iInf_ker_eq`: a
  subspace of finite codimension `n` is the common kernel of `n` linearly independent
  functionals, and of no fewer.
* `LinearMap.isLeast_finrank_ker_iff_index_eq_zero`: for a linear map with finite-dimensional
  kernel and cokernel, the dimension of the kernel is the minimal number of functionals cutting
  out its range exactly when the map has index zero.
-/

public section

open Module

namespace Subspace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The dual coannihilator of a finite-dimensional space `W` of functionals has codimension
`finrank K W`. The ambient space need not be finite-dimensional. -/
theorem finrank_quotient_dualCoannihilator_eq (W : Subspace K (Dual K V)) [FiniteDimensional K W] :
    finrank K (V ⧸ W.dualCoannihilator) = finrank K W := by
  -- `dual_finrank_eq` is stated for an `AddCommGroup`, while `Dual K W` is built over the
  -- additive monoid structure of the submodule.
  let : AddCommGroup W := inferInstance
  exact (LinearEquiv.ofBijective _ W.quotDualCoannihilatorToDual_bijective).finrank_eq.trans
    dual_finrank_eq

end Subspace

namespace Module.Dual

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The common kernel of finitely many functionals has codimension the dimension of their span.
The ambient space need not be finite-dimensional. -/
theorem finrank_quotient_iInf_ker_eq_finrank_span [Finite ι] (L : ι → Dual K V) :
    finrank K (V ⧸ ⨅ i, LinearMap.ker (L i)) = finrank K (Submodule.span K (Set.range L)) := by
  have := FiniteDimensional.span_of_finite K (Set.finite_range L)
  rw [← Submodule.dualCoannihilator_span_range]
  exact Subspace.finrank_quotient_dualCoannihilator_eq _

/-- The common kernel of finitely many functionals has codimension at most their number: a
subspace cut out by `m` linear equations has codimension at most `m`. -/
theorem finrank_quotient_iInf_ker_le_card [Fintype ι] (L : ι → Dual K V) :
    finrank K (V ⧸ ⨅ i, LinearMap.ker (L i)) ≤ Fintype.card ι := by
  rw [finrank_quotient_iInf_ker_eq_finrank_span]
  exact finrank_range_le_card L

/-- Finitely many functionals are linearly independent exactly when the codimension of their
common kernel equals their number. -/
theorem linearIndependent_iff_finrank_quotient_iInf_ker_eq_card [Fintype ι] {L : ι → Dual K V} :
    LinearIndependent K L ↔ finrank K (V ⧸ ⨅ i, LinearMap.ker (L i)) = Fintype.card ι := by
  rw [finrank_quotient_iInf_ker_eq_finrank_span, linearIndependent_iff_card_eq_finrank_span,
    eq_comm, Set.finrank]

/-- The codimension of the common kernel of an arbitrary family of functionals is at most the
cardinality of the family. The bound has content when the common kernel has finite codimension;
otherwise its left-hand side is `0` by the convention for `Module.finrank`. -/
theorem natCast_finrank_quotient_iInf_ker_le_mk (L : ι → Dual K V) :
    (finrank K (V ⧸ ⨅ i, LinearMap.ker (L i)) : Cardinal) ≤ Cardinal.mk ι := by
  cases finite_or_infinite ι
  · have := Fintype.ofFinite ι
    rw [Cardinal.mk_fintype]
    exact_mod_cast finrank_quotient_iInf_ker_le_card L
  · exact (Cardinal.natCast_lt_aleph0).le.trans (Cardinal.aleph0_le_mk ι)

end Module.Dual

namespace Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A subspace of finite codimension `n` is the common kernel of `n` linearly independent
functionals: the coordinate functionals of a basis of the quotient. -/
theorem exists_linearIndependent_iInf_ker_eq (W : Submodule K V) [FiniteDimensional K (V ⧸ W)] :
    ∃ L : Fin (finrank K (V ⧸ W)) → Dual K V,
      LinearIndependent K L ∧ ⨅ i, LinearMap.ker (L i) = W := by
  let b := Module.finBasis K (V ⧸ W)
  have hker : ⨅ i, LinearMap.ker ((b.coord i).comp W.mkQ) = W := by
    ext x
    simp only [mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply, mkQ_apply,
      b.forall_coord_eq_zero_iff, Quotient.mk_eq_zero]
  refine ⟨fun i ↦ (b.coord i).comp W.mkQ, ?_, hker⟩
  rw [Dual.linearIndependent_iff_finrank_quotient_iInf_ker_eq_card, hker, Fintype.card_fin]

/-- A subspace of finite codimension is the common kernel of `finrank K (V ⧸ W)` functionals,
and of no smaller finite family. -/
theorem isLeast_card_iInf_ker_eq (W : Submodule K V) [FiniteDimensional K (V ⧸ W)] :
    IsLeast {n : ℕ | ∃ L : Fin n → Dual K V, ⨅ i, LinearMap.ker (L i) = W}
      (finrank K (V ⧸ W)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨L, -, hL⟩ := W.exists_linearIndependent_iInf_ker_eq
    exact ⟨L, hL⟩
  · rintro n ⟨L, rfl⟩
    simpa using Dual.finrank_quotient_iInf_ker_le_card L

end Submodule

namespace LinearMap

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- For a linear map `f` with finite-dimensional cokernel, `finrank K (ker f)` is the least
number of functionals whose common kernel is the range of `f` (the least number of solvability
conditions for `f x = y`) if and only if `f.index = 0`. When the kernel is finite-dimensional this
says that the dimension of the kernel is that least number exactly when `f` has index zero.
Otherwise both sides use the convention `finrank K (ker f) = 0`, under which `f.index` is minus
the dimension of the cokernel and is not a genuine index. -/
theorem isLeast_finrank_ker_iff_index_eq_zero (f : M →ₗ[K] N)
    [FiniteDimensional K (N ⧸ range f)] :
    IsLeast {n : ℕ | ∃ L : Fin n → Dual K N, ⨅ i, ker (L i) = range f} (finrank K (ker f)) ↔
      f.index = 0 := by
  rw [index_eq_finrank_sub, sub_eq_zero, Nat.cast_inj]
  exact ⟨fun h ↦ h.unique (range f).isLeast_card_iInf_ker_eq,
    fun h ↦ h ▸ (range f).isLeast_card_iInf_ker_eq⟩

end LinearMap
