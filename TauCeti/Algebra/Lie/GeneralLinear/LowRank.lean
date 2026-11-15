/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Casimir
public import TauCeti.Algebra.Lie.GeneralLinear.Classification
public import TauCeti.Algebra.Lie.Sl2.Standard
public import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight

/-!
# The irreducible modules of `gl 2` and `gl 1`, concretely

The general theory of `TauCeti.glIrreducible` describes `L(mu)` only through its highest weight
vector. In rank two everything can be read off the weight `mu = (μ₀, μ₁)`, because `gl 2` is
`sl 2` together with the scalar matrices: `mu` is dominant exactly when `n = μ₀ - μ₁` is a natural
number, `L(mu)` restricts to the standard module `V(n)` of `sl 2`, so it has dimension `n + 1`, and
the identity matrix acts by `μ₀ + μ₁`. These two numbers determine the module: the pair
`(n, μ₀ + μ₁)` and the weight `mu` are two coordinates for the same thing. The trace-form Casimir
acts by `μ₀ (μ₀ + 1) + μ₁ (μ₁ - 1)`.

Rank one is the degenerate case. Every `mu : Fin 1 → K` is dominant, `L(mu)` is a line on which a
matrix `(a)` acts by `a * mu 0`, and the entry `mu 0` is free. The central direction of `gl n` thus
shows up already here, and is not constrained to be integral, in contrast with the group-level
weights `TauCeti.DominantWeight 1`, which only see the integers.

## Main results

* `TauCeti.existsUnique_natCast_sub_and_nonempty_lieModuleEquiv_glIrreducible_fin_two`: the
  classification of the irreducibles of `gl 2` by the pairs `(μ₀, μ₁)` with `μ₀ - μ₁` a natural
  number, which is dominance in rank two (`TauCeti.isGlDominantIntegral_fin_two_iff`).
* `TauCeti.IsGlHighestWeightVector.hasPrimitiveVectorWith`: a highest weight vector of weight
  `(μ₀, μ₁)` for `gl 2` is a primitive vector of weight `μ₀ - μ₁` for the standard triple of `sl 2`.
* `TauCeti.nonempty_lieModuleEquiv_glIrreducible_sl2Std` and
  `TauCeti.finrank_glIrreducible_fin_two`: when `μ₀ - μ₁ = n` is a natural number, `L(mu)` restricts
  to `V(n)` and has dimension `n + 1`.
* `TauCeti.one_lie_glIrreducible_fin_two` and
  `TauCeti.representation_glCasimir_glIrreducible_fin_two`: the scalars by which the identity matrix
  and the trace-form Casimir act.
* `TauCeti.nonempty_lieModuleEquiv_glIrreducible_of_sl2Std`: conversely, a `gl 2`-module restricting
  to `V(n)` with the identity acting by the matching scalar is `L(mu)`.
* `TauCeti.lie_glIrreducible_fin_one` and `TauCeti.finrank_glIrreducible_fin_one`: `L(mu)` for
  `gl 1` is a line with the evident action.
* `TauCeti.exists_isGlDominantIntegral_fin_one_forall_dominantWeight_ne`: `gl 1` has a dominant
  weight coming from no group-level dominant weight.

## References

* R. Goodman, N. R. Wallach, *Symmetry, Representations, and Invariants*, GTM 255, §5.5.
-/

public section

namespace TauCeti

open Matrix Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

section Primitive

variable {R : Type*} [CommRing R] [Nontrivial R]
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule (Matrix (Fin 2) (Fin 2) R) M]

/-- A highest weight vector of weight `(μ₀, μ₁)` for `gl 2` is a primitive vector of weight
`μ₀ - μ₁` for the standard `sl₂` triple of `sl (Fin 2) R`. -/
theorem IsGlHighestWeightVector.hasPrimitiveVectorWith {mu : Fin 2 → R} {v : M}
    (hv : IsGlHighestWeightVector mu v) :
    (isSl2Triple_single (R := R) (zero_ne_one : (0 : Fin 2) ≠ 1)).HasPrimitiveVectorWith
      v (mu 0 - mu 1) where
  ne_zero := hv.ne_zero
  lie_h := by
    rw [LieSubalgebra.coe_bracket_of_module, LieAlgebra.SpecialLinear.val_singleSubSingle, sub_lie,
      hv.lie_single_self_eq_smul, hv.lie_single_self_eq_smul, sub_smul]
  lie_e := by
    rw [LieSubalgebra.coe_bracket_of_module]
    exact hv.lie_single_eq_zero Fin.zero_lt_one

end Primitive

section FinTwo

variable {K : Type u} [Field K] [CharZero K]

section Module

variable {M : Type*} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix (Fin 2) (Fin 2) K) M] [LieModule K (Matrix (Fin 2) (Fin 2) K) M]

variable (M) in
/-- **The classification of the irreducibles of `gl 2`.** Over a field of characteristic zero, a
finite-dimensional irreducible `gl 2`-module on which the diagonal Cartan subalgebra acts
triangularizably is `L(mu)` for exactly one pair `mu = (μ₀, μ₁)` with `μ₀ - μ₁` a natural number. -/
theorem existsUnique_natCast_sub_and_nonempty_lieModuleEquiv_glIrreducible_fin_two
    [FiniteDimensional K M] [LieModule.IsIrreducible K (Matrix (Fin 2) (Fin 2) K) M]
    [LieModule.IsTriangularizable K (diagonalCartan K (Fin 2)) M] :
    ∃! mu : Fin 2 → K, (∃ n : ℕ, mu 0 - mu 1 = n) ∧
      Nonempty (M ≃ₗ⁅K, Matrix (Fin 2) (Fin 2) K⁆ glIrreducible 2 mu) := by
  simpa only [isGlDominantIntegral_fin_two_iff] using
    existsUnique_isGlDominantIntegral_and_nonempty_lieModuleEquiv_glIrreducible (K := K) (N := 2) M

variable [LieModule.IsIrreducible K (Matrix (Fin 2) (Fin 2) K) M] {mu : Fin 2 → K} {v : M} {n : ℕ}

/-- **An irreducible `gl 2`-module with highest weight `(μ₀, μ₁)`, where `μ₀ - μ₁ = n` is a natural
number, restricts to `V(n)`.** The module is not assumed finite-dimensional: for such a weight that
is a consequence of the classification `TauCeti.nonempty_lieModuleEquiv_glIrreducible`. -/
theorem nonempty_lieModuleEquiv_sl2Std_of_isGlHighestWeightVector
    (hv : IsGlHighestWeightVector mu v) (hn : mu 0 - mu 1 = n) :
    Nonempty (M ≃ₗ⁅K, LieAlgebra.SpecialLinear.sl (Fin 2) K⁆ Sl2Std K n) := by
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_glIrreducible
    (isGlDominantIntegral_fin_two_iff.mpr ⟨n, hn⟩) hv
  have : IsNoetherian K M := isNoetherian_of_linearEquiv e.symm.toLinearEquiv
  have htop := toLieSubalgebra_isSl2Triple_single_eq_top (R := K) (zero_ne_one : (0 : Fin 2) ≠ 1)
  have := isIrreducible_restrict_sl_of_isGlHighestWeightVector
    (fun h => Nat.cast_ne_zero.mpr h) hv
  have := (isIrreducible_iff_of_eq_top (M := M) htop).2 inferInstance
  exact ⟨lieModuleEquivOfEqTop htop (Sl2Std.lieModuleEquiv (hn ▸ hv.hasPrimitiveVectorWith))⟩

/-- **An irreducible `gl 2`-module with highest weight `(μ₀, μ₁)`, where `μ₀ - μ₁ = n` is a natural
number, has dimension `n + 1`.** The module is not assumed finite-dimensional: for such a weight
that is a consequence of the classification `TauCeti.nonempty_lieModuleEquiv_glIrreducible`. -/
theorem finrank_eq_add_one_of_isGlHighestWeightVector_fin_two
    (hv : IsGlHighestWeightVector mu v) (hn : mu 0 - mu 1 = n) :
    finrank K M = n + 1 := by
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_sl2Std_of_isGlHighestWeightVector hv hn
  exact e.toLinearEquiv.finrank_eq.trans Sl2Std.finrank_eq

end Module

variable {mu : Fin 2 → K} {n : ℕ}

/-- **`L(μ₀, μ₁)` restricts to `V(n)` on `sl 2`, where `μ₀ - μ₁ = n` is a natural number.** -/
theorem nonempty_lieModuleEquiv_glIrreducible_sl2Std (hn : mu 0 - mu 1 = n) :
    Nonempty (glIrreducible 2 mu ≃ₗ⁅K, LieAlgebra.SpecialLinear.sl (Fin 2) K⁆ Sl2Std K n) :=
  have hmu := isGlDominantIntegral_fin_two_iff.mpr ⟨n, hn⟩
  let _ := isIrreducible_glIrreducible hmu
  nonempty_lieModuleEquiv_sl2Std_of_isGlHighestWeightVector
    (isGlHighestWeightVector_glIrreducibleGenerator hmu) hn

/-- **`L(μ₀, μ₁)` has dimension `n + 1`, where `μ₀ - μ₁ = n` is a natural number.** -/
theorem finrank_glIrreducible_fin_two (hn : mu 0 - mu 1 = n) :
    finrank K (glIrreducible 2 mu) = n + 1 :=
  have hmu := isGlDominantIntegral_fin_two_iff.mpr ⟨n, hn⟩
  let _ := isIrreducible_glIrreducible hmu
  finrank_eq_add_one_of_isGlHighestWeightVector_fin_two
    (isGlHighestWeightVector_glIrreducibleGenerator hmu) hn

/-- **The identity matrix acts on `L(μ₀, μ₁)` by `μ₀ + μ₁`.** -/
@[simp]
theorem one_lie_glIrreducible_fin_two (hmu : IsGlDominantIntegral mu) (x : glIrreducible 2 mu) :
    ⁅(1 : Matrix (Fin 2) (Fin 2) K), x⁆ = (mu 0 + mu 1) • x := by
  rw [one_lie_glIrreducible_eq_smul hmu, Fin.sum_univ_two]

/-- **The trace-form Casimir acts on `L(μ₀, μ₁)` by `μ₀ (μ₀ + 1) + μ₁ (μ₁ - 1)`.** -/
@[simp]
theorem representation_glCasimir_glIrreducible_fin_two (hmu : IsGlDominantIntegral mu)
    (x : glIrreducible 2 mu) :
    UniversalEnvelopingAlgebra.representation K (Matrix (Fin 2) (Fin 2) K) (glIrreducible 2 mu)
        (glCasimir K (Fin 2)) x =
      (mu 0 * (mu 0 + 1) + mu 1 * (mu 1 - 1)) • x := by
  rw [glCasimir_smul_of_isGlHighestWeightVector_of_lieSpan_eq_top K
    (isGlHighestWeightVector_glIrreducibleGenerator hmu)
    (lieSpan_glIrreducibleGenerator_eq_top hmu) x, Fin.sum_univ_two]
  congr 1
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  ring

/-- **The restriction to `sl 2` and the central scalar determine a `gl 2`-module.** A module
restricting to `V(n)` on which the identity matrix acts by `μ₀ + μ₁`, where `μ₀ - μ₁ = n`, is
`L(μ₀, μ₁)`. -/
theorem nonempty_lieModuleEquiv_glIrreducible_of_sl2Std {M : Type u} [AddCommGroup M] [Module K M]
    [LieRingModule (Matrix (Fin 2) (Fin 2) K) M] [LieModule K (Matrix (Fin 2) (Fin 2) K) M]
    (hn : mu 0 - mu 1 = n)
    (hM : ∀ x : M, ⁅(1 : Matrix (Fin 2) (Fin 2) K), x⁆ = (mu 0 + mu 1) • x)
    (e : Nonempty (M ≃ₗ⁅K, LieAlgebra.SpecialLinear.sl (Fin 2) K⁆ Sl2Std K n)) :
    Nonempty (M ≃ₗ⁅K, Matrix (Fin 2) (Fin 2) K⁆ glIrreducible 2 mu) := by
  obtain ⟨e⟩ := e
  obtain ⟨e'⟩ := nonempty_lieModuleEquiv_glIrreducible_sl2Std hn
  exact gl_equiv_of_sl_equiv_of_central_scalar _ hM
    (one_lie_glIrreducible_fin_two (isGlDominantIntegral_fin_two_iff.mpr ⟨n, hn⟩))
    ⟨e.trans e'.symm⟩

end FinTwo

section FinOne

variable {K : Type u} [Field K] [CharZero K]

/-- **A matrix `(a)` acts on `L(μ)` for `gl 1` by `a * μ`.** Every `μ` is dominant, and a matrix
over a one-element index type is a scalar multiple of the identity. -/
@[simp]
theorem lie_glIrreducible_fin_one (mu : Fin 1 → K) (A : Matrix (Fin 1) (Fin 1) K)
    (x : glIrreducible 1 mu) : ⁅A, x⁆ = (A 0 0 * mu 0) • x := by
  have hA : A = A 0 0 • (1 : Matrix (Fin 1) (Fin 1) K) := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp
  rw [congrArg (⁅·, x⁆) hA, smul_lie,
    one_lie_glIrreducible_eq_smul (isGlDominantIntegral_of_le_one le_rfl mu), Fin.sum_univ_one,
    smul_smul]

/-- **`L(μ)` for `gl 1` is a line**, for every `μ`. -/
@[simp]
theorem finrank_glIrreducible_fin_one (mu : Fin 1 → K) : finrank K (glIrreducible 1 mu) = 1 := by
  -- The line through the generator is a Lie submodule, and the generator generates.
  have hmu := isGlDominantIntegral_of_le_one le_rfl mu
  refine (finrank_eq_one_iff_of_ne_zero' _
    (isGlHighestWeightVector_glIrreducibleGenerator hmu).ne_zero).mpr fun w => ?_
  let P : LieSubmodule K (Matrix (Fin 1) (Fin 1) K) (glIrreducible 1 mu) :=
    { K ∙ glIrreducibleGenerator 1 mu with
      lie_mem := fun {A y} hy => by
        rw [lie_glIrreducible_fin_one]
        exact Submodule.smul_mem _ _ hy }
  have hP : LieSubmodule.lieSpan K (Matrix (Fin 1) (Fin 1) K) {glIrreducibleGenerator 1 mu} ≤ P :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr (Submodule.mem_span_singleton_self _))
  rw [lieSpan_glIrreducibleGenerator_eq_top hmu] at hP
  exact Submodule.mem_span_singleton.mp (hP (LieSubmodule.mem_top w))

/-- **`gl 1` has a dominant weight coming from no group-level dominant weight**: every weight of
`gl 1` is dominant, including those with a non-integral entry, while `TauCeti.DominantWeight 1` only
sees the integers. The half-integer staircase is a witness. -/
theorem exists_isGlDominantIntegral_fin_one_forall_dominantWeight_ne :
    ∃ mu : Fin 1 → ℚ, IsGlDominantIntegral mu ∧
      ∀ l : DominantWeight 1, mu ≠ fun i => (l.1 i : ℚ) :=
  ⟨glStaircase 1, isGlDominantIntegral_glStaircase 1, fun l h =>
    glStaircase_ne_intCast 0 (l.1 0) (congrFun h 0)⟩

end FinOne

end TauCeti
