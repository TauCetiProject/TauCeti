/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel

/-!
# Trace left ideals and augmentation lifting in group algebras

This file proves three group-algebra ideal lemmas used in Ribet's method to first order:
1. `TauCeti.map_mem_span_range`: a ring homomorphism maps the left ideal spanned by a finite
   family `y` into the left ideal spanned by `f ∘ y`.
2. `TauCeti.trace_mul_mem_of_mem_span`: if `r ∈ O[G]` lies in the left ideal spanned by elements
   whose traces against every group element `g` lie in an `A`-submodule `𝒥 ≤ (Y → L)`, then
   `(ρ (b * mapRingHom G κ r)).trace ∈ 𝒥` for every `b : A[G]`.
3. `TauCeti.exists_mem_span_add_mul_eq_add_mul`: if every group element `g` agrees under a family
   of representations `χ x` with `m + 1` for some `m` in the left ideal spanned by `y`, then any
   sum `b + m * ρ₀` with `b` in the trace left ideal and `η₀ m = 0` can be rewritten as
   `b' + m' * ρ₀` with `b'` in the trace left ideal and `m'` in the left ideal spanned by `y`.

## Provenance

Adapted from `src/New/Congruences/FirstOrder/RibetMethod.lean` (`New.Selmer.map_mem_span_range`,
`New.Selmer.trace_mul_mem_of_mem_span`) and `src/New/Congruences/FirstOrder/FittingBlock.lean`
(`New.Selmer.exists_mem_span_add_mul_eq_add_mul`) in <https://github.com/lsernau/grh-lean> at
commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Finset Matrix MonoidAlgebra Submodule

/-- A ring homomorphism `f : A →+* B` sends the left ideal spanned by a family `y : ι → A`
into the left ideal spanned by `f ∘ y`. -/
theorem map_mem_span_range {A B ι : Type*} [Ring A] [Ring B] (f : A →+* B) (y : ι → A)
    {w : A} (hw : w ∈ span A (Set.range y)) :
    f w ∈ span B (Set.range (f ∘ y)) := by
  induction hw using span_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩
    exact subset_span ⟨i, rfl⟩
  | zero => simp
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul r x _ hx => rw [smul_eq_mul, map_mul]; exact smul_mem _ (f r) hx

/-- Let `u x` (`x : Y`) be matrix representations of `O[G]`, and let `ρ` be a representation of
`A[G]` over `Y → L` agreeing with `u x` at `x` on the image of `O[G]` along `κ : O →+* A`. If `r`
lies in the left ideal spanned by elements whose traces against every group element lie in `𝒥`,
then `(ρ (b * mapRingHom G κ r)).trace ∈ 𝒥` for every `b : A[G]`. -/
theorem trace_mul_mem_of_mem_span {O L Y G σ A : Type*} [CommRing O] [CommRing L] [Algebra O L]
    [Group G] [Fintype σ] [DecidableEq σ] [CommSemiring A] [Algebra A (Y → L)]
    (u : Y → O[G] →ₐ[O] Matrix σ σ O) (κ : O →+* A)
    (ρ : A[G] →ₐ[A] Matrix σ σ (Y → L))
    (hρ : ∀ (x : Y) (r : O[G]) (i j : σ),
      ρ (MonoidAlgebra.mapRingHom G κ r) i j x = algebraMap O L (u x r i j))
    (𝒥 : Submodule A (Y → L)) {r : O[G]}
    (hr : r ∈ span O[G] {w : O[G] | ∀ g : G,
      (fun x : Y ↦ algebraMap O L (u x w * u x (.single g 1)).trace) ∈ 𝒥})
    (b : A[G]) :
    (ρ (b * MonoidAlgebra.mapRingHom G κ r)).trace ∈ 𝒥 := by
  induction hr using span_induction generalizing b with
  | mem r hr =>
    induction b using MonoidAlgebra.induction_on with
    | of g =>
      have h_trace :
          (ρ (MonoidAlgebra.of A G g * MonoidAlgebra.mapRingHom G κ r)).trace =
            fun x : Y ↦ algebraMap O L (u x r * u x (.single g 1)).trace := by
        have hg : MonoidAlgebra.of A G g = MonoidAlgebra.mapRingHom G κ (.single g 1) := by
          simp [MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single]
        rw [hg, ← map_mul]
        funext x
        rw [trace_mul_comm (u x r), ← map_mul]
        simp only [Matrix.trace, diag_apply, Finset.sum_apply, map_sum, hρ]
      rw [h_trace]
      exact hr g
    | add b b' hb hb' =>
      rw [add_mul, map_add, trace_add]
      exact add_mem hb hb'
    | smul c b hb =>
      rw [smul_mul_assoc, map_smul, trace_smul]
      exact 𝒥.smul_mem c hb
  | zero =>
    rw [map_zero, mul_zero, map_zero, trace_zero]
    exact zero_mem 𝒥
  | add r r' _ _ hr hr' =>
    rw [map_add, mul_add, map_add, trace_add]
    exact add_mem (hr b) (hr' b)
  | smul s r _ hr =>
    rw [smul_eq_mul, map_mul (MonoidAlgebra.mapRingHom G κ), ← mul_assoc]
    exact hr (b * MonoidAlgebra.mapRingHom G κ s)

/-- Let `χ x` (`x : Y`) be matrix representations of `Λ[G]` and `η₀ : Λ[G] →ₐ[Λ] Λ` the
augmentation, and suppose every `g - 1` agrees under all `χ x` with an element of the left ideal
spanned by `y`. If `b` lies in the trace left ideal for `𝒥` and `η₀ m = 0`, then
`b + m * ρ₀ = b' + m' * ρ₀` with `b'` in the trace left ideal and `m'` in the span of `y`. -/
theorem exists_mem_span_add_mul_eq_add_mul {S L Y G σ Λ ι : Type*} [CommRing S] [CommRing L]
    [Algebra S (Y → L)] [Group G] [Fintype σ] [DecidableEq σ] [CommRing Λ] [Algebra Λ L]
    (𝒥 : Submodule S (Y → L)) (χ : Y → Λ[G] →ₐ[Λ] Matrix σ σ Λ) (η₀ : Λ[G] →ₐ[Λ] Λ)
    (hη₀ : ∀ g : G, η₀ (.single g 1) = 1) (y : ι → Λ[G])
    (hy : ∀ g : G, ∃ m ∈ span Λ[G] (Set.range y), ∀ x : Y, χ x (.single g 1) = χ x m + 1)
    (ρ₀ : Λ[G]) {b m : Λ[G]}
    (hb : b ∈ span Λ[G] {w : Λ[G] | ∀ g : G,
      (fun x : Y ↦ algebraMap Λ L (χ x w * χ x (.single g 1)).trace) ∈ 𝒥})
    (hm : η₀ m = 0) :
    ∃ b' ∈ span Λ[G] {w : Λ[G] | ∀ g : G,
        (fun x : Y ↦ algebraMap Λ L (χ x w * χ x (.single g 1)).trace) ∈ 𝒥},
      ∃ m' ∈ span Λ[G] (Set.range y), b + m * ρ₀ = b' + m' * ρ₀ := by
  have h_aug (l : Λ[G]) : ∃ l' ∈ span Λ[G] (Set.range y),
      ∀ x : Y, χ x l = χ x l' + algebraMap Λ (Matrix σ σ Λ) (η₀ l) := by
    induction l using MonoidAlgebra.induction_on with
    | of g => simpa [MonoidAlgebra.of_apply, hη₀] using hy g
    | add l₁ l₂ ih₁ ih₂ =>
      obtain ⟨l₁', hl₁', hl₁'_eq⟩ := ih₁
      obtain ⟨l₂', hl₂', hl₂'_eq⟩ := ih₂
      refine ⟨l₁' + l₂', add_mem hl₁' hl₂', fun x ↦ ?_⟩
      simp only [map_add, hl₁'_eq, hl₂'_eq]
      abel
    | smul c l ih =>
      obtain ⟨l', hl', hl'_eq⟩ := ih
      refine ⟨c • l', smul_of_tower_mem _ c hl', fun x ↦ ?_⟩
      simp only [hl'_eq, map_mul, Algebra.smul_def, mul_add, AlgHom.commutes,
        Algebra.algebraMap_self_apply]
  obtain ⟨m', hm', hm'_eq⟩ : ∃ m' ∈ span Λ[G] (Set.range y), ∀ x : Y, χ x m = χ x m' := by
    simpa [hm] using h_aug m
  have h_kill : (m - m') * ρ₀ ∈ span Λ[G] {w : Λ[G] | ∀ g : G,
      (fun x : Y ↦ algebraMap Λ L (χ x w * χ x (.single g 1)).trace) ∈ 𝒥} :=
    subset_span fun g ↦ by simp [hm'_eq, ← Pi.zero_def]
  refine ⟨b + (m - m') * ρ₀, add_mem hb h_kill, m', hm', ?_⟩
  rw [sub_mul, add_assoc, sub_add_cancel]

end TauCeti
