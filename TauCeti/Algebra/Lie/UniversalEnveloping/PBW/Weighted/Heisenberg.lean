/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Weighted.Basis
public import TauCeti.Algebra.Lie.Heisenberg

/-!
# The seven-dimensional weighted Heisenberg quotient

Give the standard Heisenberg generators `x, y, z` weights `1, 1, 2` and truncate at
weight three. The resulting associative algebra has ordered basis
`1, x, y, x², xy, y², z`, over any commutative coefficient ring. In particular the
central bracket survives in this finite target, including in characteristics two and three.

The coordinates are inherited from `Module.Basis.weightedPBWQuotientBasis`.

## References

* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§1.2 and 17.
-/

public section

namespace TauCeti.HeisenbergWeightedPBW

open Module

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lower-central weights on the standard Heisenberg generators `x, y, z`. -/
def weight : Fin 3 → ℕ := ![1, 1, 2]

/-- The lower-central weight vector is `(1, 1, 2)`. -/
theorem weight_def : weight = ![1, 1, 2] := (rfl)

/-- The weight of an exponent vector is `a + b + 2c`. -/
theorem weight_eq {n : Fin 3 →₀ ℕ} :
    Finsupp.weight weight n = n 0 + n 1 + 2 * n 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, weight, mul_comm]

variable (R : Type*) [CommRing R]

/-- The standard Heisenberg bracket preserves the lower-central weight bound. -/
theorem bracket_weight (i j k : Fin 3) (h : weight k < weight i + weight j) :
    (heisenbergBasis R).repr ⁅heisenbergBasis R i, heisenbergBasis R j⁆ k = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [weight, ← Basis.equivFun_apply, lie_self,
      heisenbergBasis_equivFun, heisenbergEquivFun_apply]

/-- The weighted Heisenberg enveloping quotient at cutoff three. -/
noncomputable abbrev Quotient :=
  _root_.UniversalEnvelopingAlgebra R (heisenberg R) ⧸
    (heisenbergBasis R).weightedPBWIdeal weight (bracket_weight R) 3

/-- The seven surviving exponent vectors, ordered as `1, x, y, x², xy, y², z`. -/
noncomputable def exponent : Fin 7 → (Fin 3 →₀ ℕ) :=
  ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 0 2,
    Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2, Finsupp.single 2 1]

/-- The explicit exponent list for the ordered quotient basis. -/
theorem exponent_def : exponent =
    ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 0 2,
      Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2, Finsupp.single 2 1] := (rfl)

private theorem exponent_lt (i : Fin 7) : Finsupp.weight weight (exponent i) < 3 := by
  fin_cases i <;> norm_num [exponent, weight_eq, Finsupp.single_apply]

private theorem exponent_bijective :
    Function.Bijective (fun i : Fin 7 ↦
      (⟨exponent i, exponent_lt i⟩ : {n : Fin 3 →₀ ℕ // Finsupp.weight weight n < 3})) := by
  constructor
  · intro i j hij
    have h := congrArg (fun n : {n : Fin 3 →₀ ℕ // Finsupp.weight weight n < 3} ↦
      ![n.val 0, n.val 1, n.val 2]) hij
    clear hij
    fin_cases i <;> fin_cases j <;> simp_all [exponent]
  · rintro ⟨n, hn⟩
    rw [weight_eq] at hn
    have hcases :
        (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0) ∨
        (n 0 = 1 ∧ n 1 = 0 ∧ n 2 = 0) ∨
        (n 0 = 0 ∧ n 1 = 1 ∧ n 2 = 0) ∨
        (n 0 = 2 ∧ n 1 = 0 ∧ n 2 = 0) ∨
        (n 0 = 1 ∧ n 1 = 1 ∧ n 2 = 0) ∨
        (n 0 = 0 ∧ n 1 = 2 ∧ n 2 = 0) ∨
        (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 1) := by omega
    rcases hcases with h | h | h | h | h | h | h
    · refine ⟨0, Subtype.ext ?_⟩
      ext k; fin_cases k <;> simp [exponent, h.1, h.2.1, h.2.2]
    · refine ⟨1, Subtype.ext ?_⟩
      ext k; fin_cases k <;> simp [exponent, h.1, h.2.1, h.2.2]
    · refine ⟨2, Subtype.ext ?_⟩
      ext k; fin_cases k <;> simp [exponent, h.1, h.2.1, h.2.2]
    · refine ⟨3, Subtype.ext ?_⟩
      ext k; fin_cases k <;> simp [exponent, h.1, h.2.1, h.2.2]
    · refine ⟨4, Subtype.ext ?_⟩
      ext k; fin_cases k <;> simp [exponent, h.1, h.2.1, h.2.2]
    · refine ⟨5, Subtype.ext ?_⟩
      ext k; fin_cases k <;> simp [exponent, h.1, h.2.1, h.2.2]
    · refine ⟨6, Subtype.ext ?_⟩
      ext k; fin_cases k <;> simp [exponent, h.1, h.2.1, h.2.2]

private noncomputable def exponentEquiv :
    Fin 7 ≃ {n : Fin 3 →₀ ℕ // Finsupp.weight weight n < 3} :=
  Equiv.ofBijective _ exponent_bijective

/-- The seven ordered monomials form a basis of the weighted Heisenberg quotient. -/
noncomputable def basis : Basis (Fin 7) R (Quotient R) :=
  ((heisenbergBasis R).weightedPBWQuotientBasis weight (bracket_weight R) 3).reindex
    exponentEquiv.symm

/-- Each basis vector is the class of its explicit PBW monomial. -/
@[simp]
theorem basis_apply (i : Fin 7) :
    basis R i = Ideal.Quotient.mk
      ((heisenbergBasis R).weightedPBWIdeal weight (bracket_weight R) 3)
      ((heisenbergBasis R).pbwBasis (exponent i)) := by
  simp [basis, Basis.reindex_apply, exponentEquiv]

/-- The quotient coordinates are the seven surviving PBW coefficients. -/
@[simp]
theorem basis_repr_mk (a : _root_.UniversalEnvelopingAlgebra R (heisenberg R)) (i : Fin 7) :
    (basis R).repr (Ideal.Quotient.mk
      ((heisenbergBasis R).weightedPBWIdeal weight (bracket_weight R) 3) a) i =
      (heisenbergBasis R).pbwBasis.repr a (exponent i) := by
  simp [basis, exponentEquiv]

local notation "q" => Ideal.Quotient.mk
  (Module.Basis.weightedPBWIdeal (heisenbergBasis R) weight (bracket_weight R) 3)
local notation "ιL" => _root_.UniversalEnvelopingAlgebra.ι R (L := heisenberg R)

/-- The basis consists of `1, x, y, x², xy, y², z`, in that order. -/
theorem basis_eq : (basis R : Fin 7 → Quotient R) =
    ![1, q (ιL (heisenbergX R)), q (ιL (heisenbergY R)),
      q (ιL (heisenbergX R)) ^ 2, q (ιL (heisenbergX R)) * q (ιL (heisenbergY R)),
      q (ιL (heisenbergY R)) ^ 2, q (ιL (heisenbergZ R))] := by
  have hxy : (heisenbergBasis R).pbwBasis (Finsupp.single 0 1 + Finsupp.single 1 1) =
      ιL (heisenbergX R) * ιL (heisenbergY R) := by
    rw [Basis.pbwBasis_apply]
    simp [Finsupp.toMultiset_add, Finsupp.toMultiset_single,
      Multiset.sort_cons, UniversalEnvelopingAlgebra.pbwMonomial_def]
  funext i
  fin_cases i <;> simp [basis_apply, exponent, hxy, ← map_pow, ← map_mul]

/-- In the weighted quotient the reverse product is `yx = xy - z`. -/
theorem basis_two_mul_one : basis R 2 * basis R 1 = basis R 4 - basis R 6 := by
  have h := congrArg q ((ιL).map_lie (heisenbergX R) (heisenbergY R))
  simp only [lie_heisenbergX_heisenbergY, LieRing.of_associative_ring_bracket,
    map_sub, map_mul] at h
  have hprod : q (ιL (heisenbergY R)) * q (ιL (heisenbergX R)) =
      q (ιL (heisenbergX R)) * q (ιL (heisenbergY R)) - q (ιL (heisenbergZ R)) :=
    eq_sub_iff_add_eq.mpr (by
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp h.symm).symm)
  simpa [basis_eq, -basis_apply] using hprod

/-- The central bracket survives the weighted quotient over every nontrivial ring. -/
theorem mk_heisenbergZ_ne_zero [Nontrivial R] : q (ιL (heisenbergZ R)) ≠ 0 := by
  have h := (basis R).ne_zero 6
  simpa [basis_eq, -basis_apply] using h

instance : Module.Free R (Quotient R) := Module.Free.of_basis (basis R)

instance : Module.Finite R (Quotient R) := Module.Finite.of_basis (basis R)

/-- The weighted Heisenberg quotient is free of rank seven. -/
@[simp]
theorem finrank_quotient [StrongRankCondition R] : Module.finrank R (Quotient R) = 7 := by
  rw [Module.finrank_eq_card_basis (basis R), Fintype.card_fin]

end TauCeti.HeisenbergWeightedPBW
