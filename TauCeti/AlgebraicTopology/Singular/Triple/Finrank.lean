/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.LinearAlgebra.Exact
import TauCeti.Algebra.BigOperators.AlternatingSum

/-!
# Dimensions of relative homology along the long exact sequence of a triple

Let `B ⊆ A ⊆ X` be a triple of spaces and `V` a module over a division ring `k`, and write
`Hᵢ(-)` for relative singular homology with coefficients in `V`. The long exact sequence of the
triple

`⋯ ⟶ Hₙ₊₁(X, A) ⟶ Hₙ(A, B) ⟶ Hₙ(X, B) ⟶ Hₙ(X, A) ⟶ ⋯ ⟶ H₀(X, A) ⟶ 0`

controls the dimensions of the homology of `(X, B)` by those of `(A, B)` and `(X, A)`:

* `Hₙ(X, B)` is finite-dimensional when `Hₙ(A, B)` and `Hₙ(X, A)` are
  (`TauCeti.TopTriple.finite_singularHomology_totalPair`), and then
  `dim Hₙ(X, B) ≤ dim Hₙ(A, B) + dim Hₙ(X, A)`
  (`TauCeti.TopTriple.finrank_singularHomology_totalPair_le`);
* when the homology of `(A, B)` and `(X, A)` is finite-dimensional in every degree, the
  alternating sums `Sₙ(P) = dim Hₙ(P) - dim Hₙ₋₁(P) + ⋯ ± dim H₀(P)` satisfy
  `Sₙ(A, B) - Sₙ(X, B) + Sₙ(X, A) = dim im (Hₙ₊₁(X, A) ⟶ Hₙ(A, B))`
  (`TauCeti.TopTriple.sum_range_neg_one_pow_mul_finrank_singularHomology_eq`). Hence `Sₙ` is
  subadditive, `Sₙ(X, B) ≤ Sₙ(A, B) + Sₙ(X, A)`
  (`TauCeti.TopTriple.sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_le`), and
  when moreover `Hₙ₊₁(X, A)` vanishes, the alternating sums with signs `(-1)ⁱ` are additive
  (`TauCeti.TopTriple.sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_eq`).

Milnor derives the Morse inequalities from these two subadditivity properties, applied to the
triples of sublevels of a Morse function.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

noncomputable section

open CategoryTheory Module

universe w

namespace TauCeti.TopTriple

variable (T : TopTriple.{w}) {k : Type*} [DivisionRing k] (V : ModuleCat.{w} k)

/-- Exactness of `Hₙ(A, B) ⟶ Hₙ(X, B) ⟶ Hₙ(X, A)` as linear maps. -/
private lemma exact_total (n : ℕ) :
    Function.Exact (TopPair.singularHomologyMap (innerToTotal.app T) V n).hom
      (TopPair.singularHomologyMap (totalToOuter.app T) V n).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (T.singularHomology_exact_total V n)

/-- **Finiteness along a triple.** If `Hₙ(A, B)` and `Hₙ(X, A)` are finite-dimensional, so is
`Hₙ(X, B)`. -/
theorem finite_singularHomology_totalPair (n : ℕ)
    [Module.Finite k ((innerPair.obj T).singularHomology V n : ModuleCat k)]
    [Module.Finite k ((outerPair.obj T).singularHomology V n : ModuleCat k)] :
    Module.Finite k ((totalPair.obj T).singularHomology V n : ModuleCat k) :=
  finiteDimensional_of_exact (T.exact_total V n)

/-- **Subadditivity of dimension along a triple.** If `Hₙ(A, B)` and `Hₙ(X, A)` are
finite-dimensional, then `dim Hₙ(X, B) ≤ dim Hₙ(A, B) + dim Hₙ(X, A)`. -/
theorem finrank_singularHomology_totalPair_le (n : ℕ)
    [Module.Finite k ((innerPair.obj T).singularHomology V n : ModuleCat k)]
    [Module.Finite k ((outerPair.obj T).singularHomology V n : ModuleCat k)] :
    finrank k ((totalPair.obj T).singularHomology V n : ModuleCat k) ≤
      finrank k ((innerPair.obj T).singularHomology V n : ModuleCat k) +
        finrank k ((outerPair.obj T).singularHomology V n : ModuleCat k) := by
  have := T.finite_singularHomology_totalPair V n
  set f := (TopPair.singularHomologyMap (innerToTotal.app T) V n).hom
  set g := (TopPair.singularHomologyMap (totalToOuter.app T) V n).hom
  -- `dim Hₙ(X, B) = dim im g + dim ker g`, and `ker g = im f` by exactness.
  rw [← g.finrank_range_add_finrank_ker, (T.exact_total V n).linearMap_ker_eq, add_comm]
  exact add_le_add (LinearMap.finrank_range_le f) (Submodule.finrank_le (LinearMap.range g))

/-- The dimension count along the long exact sequence of a triple, with the signs `(-1) ^ i` of
`TauCeti.sum_range_neg_one_pow_finrank_eq_of_exact`. -/
private lemma sum_range_neg_one_pow_mul_finrank_eq
    [∀ n, Module.Finite k ((innerPair.obj T).singularHomology V n : ModuleCat k)]
    [∀ n, Module.Finite k ((outerPair.obj T).singularHomology V n : ModuleCat k)] (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        ((finrank k ((innerPair.obj T).singularHomology V i : ModuleCat k) : ℤ) -
          finrank k ((totalPair.obj T).singularHomology V i : ModuleCat k) +
          finrank k ((outerPair.obj T).singularHomology V i : ModuleCat k)) =
      (-1) ^ n * finrank k (LinearMap.range (T.singularHomologyδ V (n + 1) n rfl).hom) := by
  have hgδ (i : ℕ) := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (T.singularHomology_exact_outer V (i + 1) i rfl)
  have hδf (i : ℕ) := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (T.singularHomology_exact_inner V (i + 1) i rfl)
  have hg := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (TopPair.singularHomologyMap (totalToOuter.app T) V 0))
  exact sum_range_neg_one_pow_finrank_eq_of_exact
    (A := fun i ↦ ((innerPair.obj T).singularHomology V i : ModuleCat k))
    (B := fun i ↦ ((totalPair.obj T).singularHomology V i : ModuleCat k))
    (C := fun i ↦ ((outerPair.obj T).singularHomology V i : ModuleCat k))
    (f := fun i ↦ (TopPair.singularHomologyMap (innerToTotal.app T) V i).hom)
    (g := fun i ↦ (TopPair.singularHomologyMap (totalToOuter.app T) V i).hom)
    (δ := fun i ↦ (T.singularHomologyδ V (i + 1) i rfl).hom) (T.exact_total V) hgδ hδf hg n

/-- **The dimension count along the long exact sequence of a triple.** If the relative homology of
`(A, B)` and of `(X, A)` is finite-dimensional in every degree, then the alternating sums through
degree `n` satisfy `Sₙ(A, B) - Sₙ(X, B) + Sₙ(X, A) = dim im (Hₙ₊₁(X, A) ⟶ Hₙ(A, B))`, where
`Sₙ(P) = dim Hₙ(P) - dim Hₙ₋₁(P) + ⋯ ± dim H₀(P)`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_eq
    [∀ n, Module.Finite k ((innerPair.obj T).singularHomology V n : ModuleCat k)]
    [∀ n, Module.Finite k ((outerPair.obj T).singularHomology V n : ModuleCat k)] (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        ((finrank k ((innerPair.obj T).singularHomology V i : ModuleCat k) : ℤ) -
          finrank k ((totalPair.obj T).singularHomology V i : ModuleCat k) +
          finrank k ((outerPair.obj T).singularHomology V i : ModuleCat k)) =
      finrank k (LinearMap.range (T.singularHomologyδ V (n + 1) n rfl).hom) := by
  -- Pull the sign `(-1) ^ n` out of the sum, reducing to the identity with signs `(-1) ^ i`.
  -- The sign `(-1) ^ n` then appears squared.
  rw [TauCeti.sum_range_neg_one_pow_sub_mul, T.sum_range_neg_one_pow_mul_finrank_eq V n,
    ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩, one_mul]

/-- **Subadditivity of the alternating sums along a triple.** If the relative homology of `(A, B)`
and of `(X, A)` is finite-dimensional in every degree, then `Sₙ(X, B) ≤ Sₙ(A, B) + Sₙ(X, A)`,
where `Sₙ(P) = dim Hₙ(P) - dim Hₙ₋₁(P) + ⋯ ± dim H₀(P)`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_le
    [∀ n, Module.Finite k ((innerPair.obj T).singularHomology V n : ModuleCat k)]
    [∀ n, Module.Finite k ((outerPair.obj T).singularHomology V n : ModuleCat k)] (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k ((totalPair.obj T).singularHomology V i : ModuleCat k) ≤
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
          finrank k ((innerPair.obj T).singularHomology V i : ModuleCat k) +
        ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
          finrank k ((outerPair.obj T).singularHomology V i : ModuleCat k) := by
  have h := (Nat.cast_nonneg _).trans
    (T.sum_range_neg_one_pow_mul_finrank_singularHomology_eq V n).ge
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
  linarith

/-- **Additivity of the alternating sums along a triple.** If the relative homology of `(A, B)`
and of `(X, A)` is finite-dimensional in every degree and `Hₙ₊₁(X, A)` vanishes, then
`∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(X, B) = ∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(A, B) + ∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(X, A)`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_eq
    [∀ n, Module.Finite k ((innerPair.obj T).singularHomology V n : ModuleCat k)]
    [∀ n, Module.Finite k ((outerPair.obj T).singularHomology V n : ModuleCat k)] (n : ℕ)
    (hn : Limits.IsZero ((outerPair.obj T).singularHomology V (n + 1))) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k ((totalPair.obj T).singularHomology V i : ModuleCat k) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
          finrank k ((innerPair.obj T).singularHomology V i : ModuleCat k) +
        ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
          finrank k ((outerPair.obj T).singularHomology V i : ModuleCat k) := by
  have h := T.sum_range_neg_one_pow_mul_finrank_eq V n
  rw [hn.eq_of_src (T.singularHomologyδ V (n + 1) n rfl) 0, ModuleCat.hom_zero,
    LinearMap.range_zero, finrank_bot, Nat.cast_zero, mul_zero] at h
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
  linarith

end TauCeti.TopTriple
