/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Fintype
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.Data.Multiset.Fintype
import TauCeti.RingTheory.Polynomial.DegreeLT

/-!
# The partial-fraction basis of the polynomials of degree below a split polynomial

Let `D` be a multiset of points of a field `K` and `P = ∏_{a ∈ D} (X - a)`. For every point
`⟨a, j⟩` of `D`, that is a value `a` of `D` together with an occurrence index `j` below its
multiplicity, the polynomial `P / (X - a)^(j+1)` is the product over `D` with `j + 1` copies of `a`
removed. These polynomials form a basis of the space `K[X]_{<|D|}` of polynomials of degree less
than `|D|`. Dividing by `P`, this says that every rational function `R / P` with `deg R < deg P`
has a unique partial-fraction decomposition `∑ c_{a,j} / (X - a)^(j+1)`.

## Main results

* `Polynomial.linearIndependent_multiset_prod_X_sub_C_sub_replicate`: the polynomials
  `P / (X - a)^(j+1)` are linearly independent, over every integral domain.
* `Polynomial.span_range_multiset_prod_X_sub_C_sub_replicate_eq_degreeLT`: over a field, they
  span `K[X]_{<|D|}`.

Independence compares vanishing orders at `a`: `P / (X - a)^(j+1)` vanishes to order exactly
`n - j - 1` at `a`, where `n` is the multiplicity of `a` in `D`, while `P / (X - b)^(l+1)` vanishes
there to order `n` for `b ≠ a`. So in a vanishing combination the coefficient with the largest `j`
at `a` is zero, and downward induction on `j` clears all of them. Spanning follows by counting
dimensions.
-/

public section

namespace Polynomial

section Independent

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

/-- **Partial-fraction polynomials are independent.** For a multiset `D` of points of an integral
domain and `P = ∏_{a ∈ D} (X - a)`, the polynomials `P / (X - a) ^ (j + 1)`, for the points
`⟨a, j⟩` of `D`, are linearly independent. -/
theorem linearIndependent_multiset_prod_X_sub_C_sub_replicate (D : Multiset R) :
    LinearIndependent R fun i : D.ToType ↦
      ((D - Multiset.replicate ((i.2 : ℕ) + 1) i.1).map fun b ↦ X - C b).prod := by
  classical
  refine Fintype.linearIndependent_iff.2 fun c hc ↦ ?_
  -- Downward induction on the occurrence index, through `d = n - j` at the point `⟨a, j⟩`.
  suffices h : ∀ d, ∀ i : D.ToType, D.count i.1 - (i.2 : ℕ) = d → c i = 0 from
    fun i ↦ h _ i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro i hi
  by_contra hci
  have hj := i.add_one_le_count
  -- Every other term vanishes to order at least `n - j` at `a`.
  have hdvd : (X - C i.1) ^ d ∣ ∑ k ∈ Finset.univ.erase i,
      c k • ((D - Multiset.replicate ((k.2 : ℕ) + 1) k.1).map fun b ↦ X - C b).prod := by
    refine Finset.dvd_sum fun k hk ↦ ?_
    by_cases hck : c k = 0
    · simp [hck]
    rw [X_sub_C_pow_dvd_smul_multiset_prod_iff hck, Multiset.count_sub, Multiset.count_replicate]
    have hkj := k.add_one_le_count
    split_ifs with hki
    · -- At the same point `a`, only lower occurrence indices remain.
      obtain ⟨b, l⟩ := k
      obtain ⟨a, j⟩ := i
      dsimp only at hki hi hkj ⊢
      subst hki
      rcases lt_trichotomy (l : ℕ) j with hlj | hlj | hlj
      · omega
      · exact (Finset.ne_of_mem_erase hk (Sigma.ext rfl (heq_of_eq (Fin.ext hlj)))).elim
      · exact absurd (ih (D.count b - l) (by omega) ⟨b, l⟩ rfl) hck
    · omega
  have hQ := (dvd_add_left hdvd).1 (by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ i), hc]
    exact dvd_zero _)
  rw [X_sub_C_pow_dvd_smul_multiset_prod_iff hci, Multiset.count_sub,
    Multiset.count_replicate_self] at hQ
  omega

end Independent

variable {K : Type*} [Field K] [DecidableEq K]

/-- **Partial fractions of a split polynomial.** For a multiset `D` of points of a field `K` and
`P = ∏_{a ∈ D} (X - a)`, the polynomials `P / (X - a) ^ (j + 1)`, for the points `⟨a, j⟩` of `D`,
span the polynomials of degree less than the degree of `P`. They form a basis by
`Polynomial.linearIndependent_multiset_prod_X_sub_C_sub_replicate`. -/
theorem span_range_multiset_prod_X_sub_C_sub_replicate_eq_degreeLT (D : Multiset K) :
    Submodule.span K (Set.range fun i : D.ToType ↦
      ((D - Multiset.replicate ((i.2 : ℕ) + 1) i.1).map fun b ↦ X - C b).prod) =
      degreeLT K (Multiset.card D) := by
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨i, rfl⟩
    have hle := Multiset.le_count_iff_replicate_le.1 i.add_one_le_count
    have hcard := Multiset.card_le_card hle
    simp only [Multiset.card_replicate] at hcard
    simp only [SetLike.mem_coe, mem_degreeLT, degree_eq_natDegree
      (monic_multisetProd_X_sub_C _).ne_zero, natDegree_multiset_prod_X_sub_C_eq_card,
      Multiset.card_sub hle, Multiset.card_replicate, Nat.cast_lt]
    omega
  · rw [finrank_span_eq_card (linearIndependent_multiset_prod_X_sub_C_sub_replicate D),
      Multiset.card_coe, finrank_degreeLT]

end Polynomial
