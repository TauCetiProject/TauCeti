/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

/-!
# Finite coefficient descent of polynomial presentation morphisms

A morphism between finitely presented algebras can be specified by polynomial images of
its generators. The defining relations must map into the target relation ideal, not
necessarily to zero as polynomials. This file descends such data to a finitely generated
intermediate field, retaining validity of the relations. This is the affine algebra input
for descending maps and gluing isomorphisms between schemes of finite presentation.

The coefficient field includes the finitely many coefficients of the presentations, the
images of the generators, and the ideal-membership witnesses. No algebraicity or
characteristic assumption on the extension is needed.

`exists_fg_intermediateField_aeval_mem_span` retains the actual polynomial presentations and
generator images under coefficient extension. The resulting relation-preserving substitution
induces a quotient algebra homomorphism using `Ideal.span_le` and `Ideal.quotientMapₐ`;
no separate quotient-map construction is needed here.

## References

* The Stacks Project, Section 10.127, colimits and maps of finite presentation.
-/

public section

open MvPolynomial

namespace TauCeti

universe u

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable (k) in
/-- Finitely many polynomials, possibly with different sets of variables, have coefficients
in a common finitely generated intermediate field. The variable sets need not be finite. -/
theorem exists_fg_intermediateField_map_eq {ι : Type*} [Finite ι]
    {σ : ι → Type*} (p : (i : ι) → MvPolynomial (σ i) K) :
    ∃ M : IntermediateField k K, M.FG ∧
      ∃ p₀ : (i : ι) → MvPolynomial (σ i) M,
        ∀ i, map M.subtype (p₀ i) = p i := by
  classical
  let S : Set K := ⋃ i, (p i).coeffs
  have hS : S.Finite := Set.finite_iUnion fun i ↦ (p i).coeffs.finite_toSet
  let M := IntermediateField.adjoin k S
  refine ⟨M, IntermediateField.fg_adjoin_of_finite hS, ?_⟩
  have hp (i) : p i ∈ Set.range (map M.subtype) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    exact ⟨⟨a, IntermediateField.subset_adjoin k S (Set.mem_iUnion.mpr ⟨i, ha⟩)⟩, rfl⟩
  choose p₀ hp₀ using hp
  exact ⟨p₀, hp₀⟩

variable {σ τ : Type u} {ι κ : Type*}

variable (k) in
/-- A polynomial substitution between presentations with finitely many source variables and
relations descends to a finitely generated intermediate field, retaining ideal membership of
the substituted relations. No finiteness of the target variable set is required. -/
theorem exists_fg_intermediateField_aeval_mem_span [Finite σ] [Finite ι] [Finite κ]
    (p : ι → MvPolynomial σ K) (q : κ → MvPolynomial τ K)
    (x : σ → MvPolynomial τ K)
    (h : ∀ i, aeval x (p i) ∈ Ideal.span (Set.range q)) :
    ∃ M : IntermediateField k K, M.FG ∧
      ∃ (p₀ : ι → MvPolynomial σ M) (q₀ : κ → MvPolynomial τ M)
        (x₀ : σ → MvPolynomial τ M),
        (∀ i, map M.subtype (p₀ i) = p i) ∧
        (∀ j, map M.subtype (q₀ j) = q j) ∧
        (∀ a, map M.subtype (x₀ a) = x a) ∧
        ∀ i, aeval x₀ (p₀ i) ∈ Ideal.span (Set.range q₀) := by
  classical
  let _ := Fintype.ofFinite σ
  let _ := Fintype.ofFinite ι
  let _ := Fintype.ofFinite κ
  have hw (i) : ∃ w : κ → MvPolynomial τ K, ∑ j, w j * q j = aeval x (p i) := by
    simpa only [Ideal.span, smul_eq_mul] using
      (Submodule.mem_span_range_iff_exists_fun (MvPolynomial τ K)).mp (h i)
  choose w hw using hw
  -- One dependent family collects both presentations, the substitution, and the witnesses.
  let vars : ι ⊕ (κ ⊕ (σ ⊕ (ι × κ))) → Type _ :=
    Sum.elim (fun _ ↦ σ) (fun _ ↦ τ)
  let data : (a : ι ⊕ (κ ⊕ (σ ⊕ (ι × κ)))) → MvPolynomial (vars a) K :=
    fun a ↦ match a with
      | .inl i => p i
      | .inr (.inl j) => q j
      | .inr (.inr (.inl a)) => x a
      | .inr (.inr (.inr (i, j))) => w i j
  obtain ⟨M, hM, data₀, hdata₀⟩ := exists_fg_intermediateField_map_eq k data
  let p₀ : ι → MvPolynomial σ M := fun i ↦ data₀ (.inl i)
  let q₀ : κ → MvPolynomial τ M := fun j ↦ data₀ (.inr (.inl j))
  let x₀ : σ → MvPolynomial τ M := fun a ↦ data₀ (.inr (.inr (.inl a)))
  let w₀ : ι → κ → MvPolynomial τ M := fun i j ↦ data₀ (.inr (.inr (.inr (i, j))))
  have hp₀ : ∀ i, map M.subtype (p₀ i) = p i := fun i ↦ hdata₀ (.inl i)
  have hq₀ : ∀ j, map M.subtype (q₀ j) = q j := fun j ↦ hdata₀ (.inr (.inl j))
  have hx₀ : ∀ a, map M.subtype (x₀ a) = x a := fun a ↦ hdata₀ (.inr (.inr (.inl a)))
  have hw₀ : ∀ i j, map M.subtype (w₀ i j) = w i j :=
    fun i j ↦ hdata₀ (.inr (.inr (.inr (i, j))))
  -- Polynomial identities descend by injectivity of the coefficient-field inclusion.
  have h₀ (i) : aeval x₀ (p₀ i) ∈ Ideal.span (Set.range q₀) := by
    have heq : ∑ j, w₀ i j * q₀ j = aeval x₀ (p₀ i) := by
      apply map_injective M.subtype Subtype.val_injective
      simpa only [map_sum, map_mul, hw₀, hq₀, aeval_def, algebraMap_eq, map_eval₂,
        Function.comp_def, hx₀, hp₀] using hw i
    rw [← heq]
    exact sum_mem fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  exact ⟨M, hM, p₀, q₀, x₀, hp₀, hq₀, hx₀, h₀⟩

end TauCeti
