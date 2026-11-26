/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Basic
public import TauCeti.RepresentationTheory.Irreducible.FiniteIndex

/-!
# Dimensions of the irreducible representations of the archimedean Weil groups

This file proves the dimension half of the classification of the irreducible finite-dimensional
complex representations of the archimedean Weil groups `W_ℂ = ℂˣ` and `W_ℝ = ℂˣ ⊔ jℂˣ`: those of
`W_ℂ` are one-dimensional, and those of `W_ℝ` have dimension at most two. No continuity is needed.

For `W_ℂ` this is Mathlib's Schur's lemma for a commutative group,
`Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative`, applied to `ρ` with
`[ρ.IsIrreducible]`. For `W_ℝ` it is the case of the commutative subgroup `ℂˣ` of index two in
`Representation.IsIrreducible.finrank_le_index`. Concretely, for a common eigenvector `v` of `ℂˣ`
the span of `v` and `j v` is stable under `W_ℝ`, because `z (j v) = j (conj z) v` and
`j (j v) = (-1) v`; this explicit spanning pair is what identifies a two-dimensional irreducible
representation with an induced character.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupReal.apply_mem_span_pair`: the span of a common eigenvector
  `v` of `ℂˣ` and of `j v` is stable under `W_ℝ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.finrank_le_two_of_isIrreducible`: an irreducible
  finite-dimensional complex representation of `W_ℝ` has dimension at most two.

## References

* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in *Motives*,
  Proc. Sympos. Pure Math. 55, Part 2 (1994), §3.
-/

public section

namespace TauCeti.ClassFieldTheory

open Module

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

namespace WeilGroupReal

omit [FiniteDimensional ℂ V] in
/-- The span of a vector `v` and of its image under `j` is stable under `W_ℝ` when `v` is an
eigenvector of every element of `ℂˣ`. -/
theorem apply_mem_span_pair (ρ : Representation ℂ WeilGroupReal V) {v : V}
    (hv : ∀ z, ∃ c : ℂ, ρ (includeComplex z) v = c • v) (w : WeilGroupReal) {x : V}
    (hx : x ∈ Submodule.span ℂ (Set.range ![v, ρ j v])) :
    ρ w x ∈ Submodule.span ℂ (Set.range ![v, ρ j v]) := by
  set W := Submodule.span ℂ (Set.range ![v, ρ j v])
  have hv₀ : v ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have hv₁ : ρ j v ∈ W := Submodule.subset_span ⟨1, rfl⟩
  -- `W` is stable under a linear map sending both generators into `W`
  have hstable (f : V →ₗ[ℂ] V) (h₀ : f v ∈ W) (h₁ : f (ρ j v) ∈ W) : ∀ y ∈ W, f y ∈ W := by
    intro y hy
    refine (Submodule.span_le (p := W.comap f)).mpr ?_ hy
    rintro _ ⟨i, rfl⟩
    fin_cases i
    exacts [h₀, h₁]
  have hz (z : WeilGroupComplex) : ∀ y ∈ W, ρ (includeComplex z) y ∈ W := by
    refine hstable _ ?_ ?_
    · obtain ⟨c, hc⟩ := hv z
      exact hc ▸ W.smul_mem c hv₀
    · obtain ⟨c, hc⟩ := hv (star z)
      rw [← mul_apply_eq_comp, ← map_mul, includeComplex_mul_j, map_mul, mul_apply_eq_comp,
        hc, map_smul]
      exact W.smul_mem c hv₁
  have hj : ∀ y ∈ W, ρ j y ∈ W := by
    refine hstable _ hv₁ ?_
    rw [← mul_apply_eq_comp, ← map_mul, j_mul_j]
    exact hz (-1) v hv₀
  rcases exists_includeComplex_or_j_mul w with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact hz z x hx
  · rw [map_mul, mul_apply_eq_comp]
    exact hj _ (hz z x hx)

/-- **The irreducible representations of `W_ℝ` have dimension at most two.** This is the bound
by the index of a commutative subgroup of finite index, for `ℂˣ`, of index two in `W_ℝ`. -/
theorem finrank_le_two_of_isIrreducible (ρ : Representation ℂ WeilGroupReal V)
    (h : ρ.IsIrreducible) : finrank ℂ V ≤ 2 := by
  have : IsMulCommutative includeComplex.range := includeComplex.range_eq_map ▸ inferInstance
  have : includeComplex.range.FiniteIndex := ⟨by simp [index_range_includeComplex]⟩
  simpa [index_range_includeComplex] using h.finrank_le_index includeComplex.range

end WeilGroupReal

end TauCeti.ClassFieldTheory
