/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Basic.Finite.Sum
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.MvPolynomial.Tower
import TauCeti.RingTheory.MvPolynomial.Ideal.BaseChange

/-!
# Finite coefficient descent of polynomial presentation morphisms

A morphism between finitely presented algebras can be specified by polynomial images of
its generators. The defining relations must map into the target relation ideal, not
necessarily to zero as polynomials. This file descends such data to a finitely generated
intermediate field, retaining validity of the relations. This is the affine algebra input
for descending maps and gluing isomorphisms between schemes of finite presentation.

No algebraicity or characteristic assumption on the extension is needed.

`exists_fg_intermediateField_mvPolynomial_map_eq_and_aeval_mem_span` retains the actual
polynomial presentations and generator images under coefficient extension. The resulting
substitution induces a quotient algebra homomorphism using `Ideal.span_le` and `Ideal.quotientMapₐ`;
no separate quotient-map construction is needed here.

## References

* The Stacks Project, Section 10.127, colimits and maps of finite presentation.
-/

public section

open MvPolynomial

namespace TauCeti

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable (k) in
/-- Finitely many polynomials, possibly with different sets of variables, have coefficients
in a common finitely generated intermediate field. The variable sets need not be finite. -/
theorem exists_fg_intermediateField_mvPolynomial_map_eq {ι : Type*} [Finite ι]
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

variable {σ τ ι κ : Type*}

attribute [local instance] MvPolynomial.algebraMvPolynomial in
variable (k) in
/-- A polynomial substitution between presentations with finitely many source variables and
relations descends to a finitely generated intermediate field, retaining ideal membership of
the substituted relations. No finiteness of the target variable set is required. -/
theorem exists_fg_intermediateField_mvPolynomial_map_eq_and_aeval_mem_span
    [Finite σ] [Finite ι] [Finite κ]
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
  obtain ⟨L, hL, p₁, hp₁⟩ := exists_fg_intermediateField_mvPolynomial_map_eq k p
  obtain ⟨N, hN, y, hy⟩ := exists_fg_intermediateField_mvPolynomial_map_eq k (Sum.elim q x)
  let M := L ⊔ N
  let fL := (IntermediateField.inclusion (show L ≤ M from le_sup_left)).toRingHom
  let fN := (IntermediateField.inclusion (show N ≤ M from le_sup_right)).toRingHom
  let p₀ (i : ι) := map fL (p₁ i)
  let q₀ (j : κ) := map fN (y (.inl j))
  let x₀ (a : σ) := map fN (y (.inr a))
  have hp₀ (i) : map (algebraMap M K) (p₀ i) = p i := by
    simp only [p₀, map_map]
    exact hp₁ i
  have hq₀ (j) : map (algebraMap M K) (q₀ j) = q j := by
    simp only [q₀, map_map]
    exact hy (.inl j)
  have hx₀ (a) : map (algebraMap M K) (x₀ a) = x a := by
    simp only [x₀, map_map]
    exact hy (.inr a)
  refine ⟨M, IntermediateField.fg_sup hL hN, p₀, q₀, x₀, hp₀, hq₀, hx₀, ?_⟩
  intro i
  have hf : (algebraMap M K).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hq : map (algebraMap M K) ∘ q₀ = q := funext hq₀
  rw [← (Ideal.span (Set.range q₀)).comap_map_mvPolynomial_eq_self_of_faithfullyFlat hf,
    Ideal.mem_comap, Ideal.map_span, ← Set.range_comp, hq]
  have hx : map (algebraMap M K) ∘ x₀ = x := funext hx₀
  have heq : map (algebraMap M K) (aeval x₀ (p₀ i)) = aeval x (p i) := by
    rw [← hp₀ i, aeval_map_algebraMap K, ← hx]
    exact (aeval_algebraMap_apply (MvPolynomial τ K) x₀ (p₀ i)).symm
  exact heq ▸ h i

end TauCeti
