/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Basic
public import TauCeti.RepresentationTheory.CommonEigenvector

/-!
# Dimensions of the irreducible representations of the archimedean Weil groups

This file proves the dimension half of the classification of the irreducible finite-dimensional
complex representations of the archimedean Weil groups `W_ℂ = ℂˣ` and `W_ℝ = ℂˣ ⊔ jℂˣ`: those of
`W_ℂ` are one-dimensional, and those of `W_ℝ` have dimension at most two. No continuity is needed.

For `W_ℂ` this is Schur's lemma for a commutative group
(`Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative`). For `W_ℝ`, a nonzero
finite-dimensional representation of the commutative group `ℂˣ` has a common eigenvector `v`
(`Representation.exists_ne_zero_forall_exists_apply_eq_smul`), and the span of `v` and `j v` is
stable under `W_ℝ`: `z (j v) = j (conj z) v` and `j (j v) = (-1) v`. In an irreducible
representation it is everything.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupComplex.finrank_eq_one_of_isIrreducible`: an irreducible
  finite-dimensional complex representation of `W_ℂ` is one-dimensional.
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

/-- **The irreducible representations of `W_ℂ` are characters.** An irreducible finite-dimensional
complex representation of the commutative group `W_ℂ = ℂˣ` is one-dimensional. -/
theorem WeilGroupComplex.finrank_eq_one_of_isIrreducible
    (ρ : Representation ℂ WeilGroupComplex V) (h : ρ.IsIrreducible) : finrank ℂ V = 1 :=
  have := h
  Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ

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

/-- **The irreducible representations of `W_ℝ` have dimension at most two.** A common eigenvector
`v` of `ℂˣ` and its image `j v` span a subrepresentation, which is everything. -/
theorem finrank_le_two_of_isIrreducible (ρ : Representation ℂ WeilGroupReal V)
    (h : ρ.IsIrreducible) : finrank ℂ V ≤ 2 := by
  have := h.nontrivial
  obtain ⟨v, hv0, hv⟩ :=
    Representation.exists_ne_zero_forall_exists_apply_eq_smul (ρ.comp includeComplex)
  let σ : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ (Set.range ![v, ρ j v])
      apply_mem_toSubmodule := fun w _ hx ↦ apply_mem_span_pair ρ hv w hx }
  have hσ : σ = ⊤ := by
    refine (h.eq_bot_or_eq_top σ).resolve_left fun hbot ↦ hv0 ?_
    have hmem : v ∈ σ.toSubmodule := Submodule.subset_span ⟨0, rfl⟩
    rw [hbot, Subrepresentation.toSubmodule_bot, Submodule.mem_bot] at hmem
    exact hmem
  have htop : Submodule.span ℂ (Set.range ![v, ρ j v]) = ⊤ := by
    simpa [σ] using congrArg Subrepresentation.toSubmodule hσ
  calc finrank ℂ V = finrank ℂ (⊤ : Submodule ℂ V) := (finrank_top ℂ V).symm
    _ = finrank ℂ (Submodule.span ℂ (Set.range ![v, ρ j v])) := by rw [htop]
    _ ≤ Fintype.card (Fin 2) := finrank_range_le_card _
    _ = 2 := Fintype.card_fin 2

end WeilGroupReal

end TauCeti.ClassFieldTheory
