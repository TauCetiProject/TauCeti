/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Multiset.Fintype
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Hermite interpolation

Let `K` be a field of characteristic zero and `D` a multiset of `m` points of `K`. For every
choice of values `t a j`, one for each point `a` of `D` and each order `j` below the
multiplicity of `a` in `D`, there is a polynomial `p` of degree less than `m` whose `j`-th
derivative takes the value `t a j` at `a`
(`Polynomial.exists_degree_lt_eval_iterate_derivative_eq`).

The proof is linear algebra: the map sending a polynomial of degree less than `m` to these
derivatives is linear between spaces of dimension `m`. It is injective because a nonzero `p` with
vanishing derivatives of order below the multiplicity of each point of `D` has every point of `D`
as a root of at least that multiplicity
(`Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative`), so it has at least `m` roots
counted with multiplicity, more than its degree.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- **Hermite interpolation.** Over a field of characteristic zero, for a multiset `D` of points
and values `t ⟨a, j⟩` indexed by the points `a` of `D` and the orders `j` below the multiplicity of
`a` in `D`, there is a polynomial `p` of degree less than the number of points of `D` with
`p⁽ʲ⁾(a) = t ⟨a, j⟩` for all such `a` and `j`. -/
theorem exists_degree_lt_eval_iterate_derivative_eq (D : Multiset K) (t : D.ToType → K) :
    ∃ p : K[X], p.degree < Multiset.card D ∧
      ∀ i : D.ToType, (derivative^[i.2] p).eval i.1 = t i := by
  set m := Multiset.card D
  -- The derivatives at the points of `D`, on polynomials of degree less than `m`.
  let J : degreeLT K m →ₗ[K] D.ToType → K := LinearMap.pi fun i ↦
    leval i.1 ∘ₗ (derivative ^ (i.2 : ℕ)) ∘ₗ (degreeLT K m).subtype
  have hJ (q : degreeLT K m) (i : D.ToType) : J q i = (derivative^[i.2] (q : K[X])).eval i.1 := by
    simp [J, pow_apply_eq_iterate]
  have hinj : Function.Injective J := by
    refine (injective_iff_map_eq_zero J).2 fun q hq ↦ ?_
    by_contra hq0
    have hp : (q : K[X]) ≠ 0 := fun h ↦ hq0 (Subtype.ext h)
    -- Every point of `D` is a root of `q` of at least its multiplicity in `D`.
    have hle : D ≤ (q : K[X]).roots := Multiset.le_iff_count.2 fun a ↦ by
      rw [count_roots]
      by_cases h0 : Multiset.count a D = 0
      · simp [h0]
      · have hlt : Multiset.count a D - 1 < rootMultiplicity a (q : K[X]) :=
          (lt_rootMultiplicity_iff_isRoot_iterate_derivative hp).2 fun j hj ↦ by
            rw [IsRoot.def, ← hJ q ⟨a, ⟨j, by omega⟩⟩, hq]
            rfl
        omega
    have hdeg : (q : K[X]).natDegree < m :=
      (natDegree_lt_iff_degree_lt hp).2 (mem_degreeLT.1 q.2)
    have := (Multiset.card_le_card hle).trans (card_roots' _)
    omega
  have : FiniteDimensional K (degreeLT K m) := (degreeLTEquiv K m).symm.finiteDimensional
  have hfin : Module.finrank K (degreeLT K m) = Module.finrank K (D.ToType → K) := by
    rw [(degreeLTEquiv K m).finrank_eq, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card,
      Multiset.card_coe]
  obtain ⟨q, hq⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj t
  exact ⟨q, mem_degreeLT.1 q.2, fun i ↦ by rw [← hJ, hq]⟩

end Polynomial
