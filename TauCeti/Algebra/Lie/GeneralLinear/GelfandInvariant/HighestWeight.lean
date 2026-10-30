/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.GelfandInvariant.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# Highest-weight eigenvalues of the Gelfand invariants

For a highest-weight vector of weight `μ`, the strictly upper-triangular entries of powers of the
generator matrix annihilate the vector. The diagonal entries act by scalars `aᵣ(i)`, given by

`a₀(i) = 1`, `aᵣ₊₁(i) = μ(i) aᵣ(i) + ∑ j > i, (aᵣ(i) - aᵣ(j))`.

Consequently the Gelfand invariant `trace (𝔼 ^ r)` acts by `∑ i, aᵣ(i)`. This recurrence
computes its highest-weight eigenvalue using only additions and multiplications, over every
commutative ring. Centrality extends the scalar action to the whole cyclic highest-weight
module. Applied at the successive general-linear corners, these are the scalars needed for
the Gelfand-Tsetlin joint eigencharacters.

The calculation uses `lie_ι_single_glGeneratorMatrix_pow_apply` and the enveloping-algebra
action on Lie modules from `TauCeti.Algebra.Lie.UniversalEnveloping.Module`.

## References

* A. Molev, *Yangians and Classical Lie Algebras* (2007), Chapter 7.
-/

public section

open Finset Matrix

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K n : Type*} [CommRing K] [Fintype n] [LinearOrder n]

/-- The scalar by which the `i`-th diagonal entry of the `r`-th power of the generator matrix
acts on a highest-weight vector of weight `μ`. -/
def gelfandEigenvalueEntry (μ : n → K) : ℕ → n → K
  | 0, _ => 1
  | r + 1, i => μ i * gelfandEigenvalueEntry μ r i +
      ∑ j, if i < j then gelfandEigenvalueEntry μ r i - gelfandEigenvalueEntry μ r j else 0

@[simp] theorem gelfandEigenvalueEntry_zero (μ : n → K) (i : n) :
    gelfandEigenvalueEntry μ 0 i = 1 := (rfl)

/-- The recursion determining the diagonal scalars. -/
theorem gelfandEigenvalueEntry_succ (μ : n → K) (r : ℕ) (i : n) :
    gelfandEigenvalueEntry μ (r + 1) i = μ i * gelfandEigenvalueEntry μ r i +
      ∑ j, if i < j then gelfandEigenvalueEntry μ r i - gelfandEigenvalueEntry μ r j else 0 := (rfl)

@[simp] theorem gelfandEigenvalueEntry_one (μ : n → K) (i : n) :
    gelfandEigenvalueEntry μ 1 i = μ i := by
  simp [gelfandEigenvalueEntry_succ]

/-- The highest-weight eigenvalue of the Gelfand invariant of degree `r`. -/
def gelfandEigenvalue (μ : n → K) (r : ℕ) : K := ∑ i, gelfandEigenvalueEntry μ r i

/-- The eigenvalue is the sum of the diagonal scalars. -/
theorem gelfandEigenvalue_def (μ : n → K) (r : ℕ) :
    gelfandEigenvalue μ r = ∑ i, gelfandEigenvalueEntry μ r i := (rfl)

@[simp] theorem gelfandEigenvalue_zero (μ : n → K) :
    gelfandEigenvalue μ 0 = Fintype.card n := by
  simp [gelfandEigenvalue_def]

@[simp] theorem gelfandEigenvalue_one (μ : n → K) :
    gelfandEigenvalue μ 1 = ∑ i, μ i := by
  simp [gelfandEigenvalue_def]

section Action

variable [DecidableEq n]

variable {M : Type*} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix n n K) M] [LieModule K (Matrix n n K) M]
  {μ : n → K} {v : M}

local notation "ρ" => UniversalEnvelopingAlgebra.representation K (Matrix n n K) M

omit [LinearOrder n] in
private theorem representation_ι_single_mul_pow_apply (a b i j : n) (r : ℕ) (w : M) :
    ⁅single a b (1 : K), ρ ((glGeneratorMatrix K n ^ r) i j) w⁆ =
      ρ ((glGeneratorMatrix K n ^ r) i j) ⁅single a b (1 : K), w⁆ +
        ρ ((if b = i then (glGeneratorMatrix K n ^ r) a j else 0) -
          if j = a then (glGeneratorMatrix K n ^ r) i b else 0) w := by
  have h := congrArg (fun u => ρ u w)
    (lie_ι_single_glGeneratorMatrix_pow_apply K n a b i j r)
  simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul,
    LinearMap.sub_apply, Module.End.mul_apply,
    UniversalEnvelopingAlgebra.representation_ι_apply] at h
  rw [map_sub, LinearMap.sub_apply]
  exact (eq_add_of_sub_eq h).trans (add_comm _ _)

/-- Strict upper-triangular entries of every power of the generator matrix annihilate a
highest-weight vector. -/
theorem representation_glGeneratorMatrix_pow_apply_eq_zero
    (hv : IsGlHighestWeightVector μ v) (r : ℕ) {i j : n} (hij : i < j) :
    ρ ((glGeneratorMatrix K n ^ r) i j) v = 0 := by
  induction r generalizing i j with
  | zero => simp [hij.ne]
  | succ r ih =>
    rw [pow_succ', Matrix.mul_apply, map_sum, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [map_mul, Module.End.mul_apply, glGeneratorMatrix_apply,
      UniversalEnvelopingAlgebra.representation_ι_apply]
    -- A raising entry on the right kills the vector. Otherwise commute the raising
    -- generator past the power entry and use the commutator identity.
    by_cases hkj : k < j
    · rw [ih hkj, lie_zero]
    · rw [representation_ι_single_mul_pow_apply,
        hv.lie_single_eq_zero (hij.trans_le (le_of_not_gt hkj)), map_zero]
      simp [hij.ne', ih hij]

/-- Diagonal entries of powers of the generator matrix act on a highest-weight vector by the
scalars given by `gelfandEigenvalueEntry`. -/
theorem representation_glGeneratorMatrix_pow_apply_eq_smul
    (hv : IsGlHighestWeightVector μ v) (r : ℕ) (i : n) :
    ρ ((glGeneratorMatrix K n ^ r) i i) v = gelfandEigenvalueEntry μ r i • v := by
  induction r generalizing i with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Matrix.mul_apply, map_sum, LinearMap.sum_apply,
      gelfandEigenvalueEntry_succ, add_smul, Finset.sum_smul]
    -- Only the diagonal product and commutators with raising generators survive.
    have hterm (j : n) :
        ρ (glGeneratorMatrix K n i j * (glGeneratorMatrix K n ^ r) j i) v =
          if i = j then (μ i * gelfandEigenvalueEntry μ r i) • v else
            if i < j then (gelfandEigenvalueEntry μ r i -
              gelfandEigenvalueEntry μ r j) • v else 0 := by
      rw [map_mul, Module.End.mul_apply, glGeneratorMatrix_apply,
        UniversalEnvelopingAlgebra.representation_ι_apply]
      rcases lt_trichotomy i j with hij | rfl | hji
      · rw [representation_ι_single_mul_pow_apply, hv.lie_single_eq_zero hij, map_zero]
        simp [hij.ne, hij, ih, sub_smul]
      · rw [ih, lie_smul, hv.lie_single_self_eq_smul, smul_smul]
        simp [mul_comm]
      · rw [representation_glGeneratorMatrix_pow_apply_eq_zero hv r hji, lie_zero]
        simp [hji.ne', hji.not_gt]
    simp_rw [hterm]
    have hsplit (j : n) :
        (if i = j then (μ i * gelfandEigenvalueEntry μ r i) • v else
          if i < j then (gelfandEigenvalueEntry μ r i -
            gelfandEigenvalueEntry μ r j) • v else 0) =
        (if j = i then (μ i * gelfandEigenvalueEntry μ r i) • v else 0) +
          (if i < j then (gelfandEigenvalueEntry μ r i -
            gelfandEigenvalueEntry μ r j) else 0) • v := by
      by_cases h : i = j <;> simp [h, eq_comm]
    simp_rw [hsplit, Finset.sum_add_distrib]
    simp

/-- Every Gelfand invariant has the recursively computed scalar action on a highest-weight
vector, without a dominance, characteristic, or finite-dimensionality assumption. -/
theorem gelfandInvariant_smul_of_isGlHighestWeightVector
    (hv : IsGlHighestWeightVector μ v) (r : ℕ) :
    ρ (gelfandInvariant K n r) v = gelfandEigenvalue μ r • v := by
  simp only [gelfandInvariant_def, Matrix.trace, Matrix.diag_apply, map_sum,
    LinearMap.sum_apply, representation_glGeneratorMatrix_pow_apply_eq_smul hv,
    gelfandEigenvalue_def, Finset.sum_smul]

/-- The Gelfand invariant acts by its highest-weight eigenvalue throughout a cyclic
highest-weight module. -/
theorem gelfandInvariant_smul_of_isGlHighestWeightVector_of_lieSpan_eq_top
    (hv : IsGlHighestWeightVector μ v)
    (hgen : LieSubmodule.lieSpan K (Matrix n n K) {v} = ⊤) (r : ℕ) (w : M) :
    ρ (gelfandInvariant K n r) w = gelfandEigenvalue μ r • w := by
  apply UniversalEnvelopingAlgebra.representation_eq_smul_of_mem_center_of_lieSpan_eq_top
    K (Matrix n n K) M (gelfandInvariant_mem_center K n r) _ hgen w
  simpa only [Set.mem_singleton_iff, forall_eq] using
    gelfandInvariant_smul_of_isGlHighestWeightVector hv r

end Action

end TauCeti
