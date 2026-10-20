/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Nonvanishing of polynomials at points of a simple extension

A nonzero multivariate polynomial `F` over a field `k` need not have a nonzero value at a point of
`k^σ`, for example `X ^ q - X` over a field with `q` elements. It does have one at a point of a
finite simple extension `k[Y] ⧸ (g)`: there are a monic irreducible `g` and polynomials `q i` with
`g ∤ F(q)`. When `k` is infinite the point is rational, with `g = Y`. When `k` is finite, choose a
nonvanishing point over the algebraic closure whose coordinates vanish outside the variables of
`F`; its coordinates generate a finite extension of `k`, which is simple.

This form is suited to lifting along a surjection of rings: a monic lift of `g` and lifts of the
`q i` define a point of a finite extension of a valued field whose residue is the given point.
-/

public section

open Polynomial

universe u

namespace MvPolynomial

variable {k : Type u} {σ : Type*} [Field k]

/-- A nonzero multivariate polynomial over a field does not vanish at some point of a
finite simple extension: there are a monic irreducible `g` and polynomials `q i` such that `g` does
not divide `F(q)`, that is, the residue of `F(q)` in `k[Y] ⧸ (g)` is nonzero. -/
theorem exists_monic_irreducible_not_dvd_aeval {F : MvPolynomial σ k} (hF : F ≠ 0) :
    ∃ (g : k[X]) (q : σ → k[X]), g.Monic ∧ Irreducible g ∧ ¬ g ∣ aeval q F := by
  -- It suffices to find an element `α`, integral over `k`, and polynomials `q i` with
  -- `F(q(α)) ≠ 0`; then `g` is the minimal polynomial of `α`.
  suffices h : ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (α : E) (q : σ → k[X]),
      IsIntegral k α ∧ aeval (fun i ↦ Polynomial.aeval α (q i)) F ≠ 0 by
    obtain ⟨E, _, _, α, q, hα, hFα⟩ := h
    refine ⟨minpoly k α, q, minpoly.monic hα, minpoly.irreducible hα, fun hdvd ↦ hFα ?_⟩
    rw [← comp_aeval_apply]
    exact minpoly.dvd_iff.mp hdvd
  -- Over the algebraic closure, which is infinite, `F` has a nonzero value at a point with
  -- finitely many coordinates, since only the variables of `F` matter.
  classical
  obtain ⟨x, hx, hxfin⟩ : ∃ x : σ → AlgebraicClosure k, aeval x F ≠ 0 ∧ (Set.range x).Finite := by
    obtain ⟨x, hx⟩ : ∃ x : σ → AlgebraicClosure k, aeval x F ≠ 0 := by
      by_contra! h
      refine hF (map_injective (algebraMap k (AlgebraicClosure k)) (algebraMap k _).injective ?_)
      exact funext fun x ↦ by simpa [eval_map, ← aeval_def] using h x
    refine ⟨fun i ↦ if i ∈ F.vars then x i else 0, ?_, ?_⟩
    · rwa [aeval_eq_eval₂Hom, eval₂Hom_congr' (g₂ := x) rfl (fun i hi _ ↦ by simp [hi]) rfl,
        ← aeval_eq_eval₂Hom]
    · refine ((F.vars.finite_toSet.image x).insert 0).subset ?_
      rintro _ ⟨i, rfl⟩
      by_cases hi : i ∈ F.vars
      · exact Or.inr ⟨i, hi, by simp [hi]⟩
      · exact Or.inl (by simp [hi])
  -- When `k` is infinite, a rational point suffices.
  by_cases hk : Finite k
  swap
  · have : Infinite k := not_finite_iff_infinite.mp hk
    obtain ⟨y, hy⟩ : ∃ y : σ → k, aeval y F ≠ 0 := by
      by_contra! h
      exact hF (funext fun y ↦ by simpa using h y)
    refine ⟨k, inferInstance, inferInstance, 0, fun i ↦ Polynomial.C (y i), isIntegral_zero, ?_⟩
    simpa using hy
  -- When `k` is finite, the coordinates of `x` generate a finite, hence simple, extension.
  let E := IntermediateField.adjoin k (Set.range x)
  have : FiniteDimensional k E := by
    have : Finite (Set.range x) := hxfin
    exact IntermediateField.finiteDimensional_adjoin fun y _ ↦
      (Algebra.IsIntegral.isIntegral (R := k) y)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_bot k E
  have hαi : IsIntegral k α := .of_finite k α
  have hq (i : σ) :
      ∃ p : k[X], Polynomial.aeval α p = ⟨x i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ := by
    have hmem : (⟨x i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E) ∈
        (IntermediateField.adjoin k {α}).toSubalgebra := by
      rw [hα]
      exact IntermediateField.mem_top
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαi.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hmem
    exact hmem
  choose q hq using hq
  refine ⟨E, inferInstance, inferInstance, α, q, hαi, fun h ↦ hx ?_⟩
  simp only [hq] at h
  simpa [comp_aeval_apply] using congrArg E.val h

end MvPolynomial
