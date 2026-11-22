/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.Algebra.Module.SnakeLemma
public import TauCeti.LinearAlgebra.Exact
public import TauCeti.LinearAlgebra.LinearMap.Ker
public import TauCeti.LinearAlgebra.LinearMap.Range
public import TauCeti.LinearAlgebra.Prod
public import TauCeti.LinearAlgebra.Quotient.Basic

import Mathlib.Algebra.Exact.Sequence

/-!
# The kernel–cokernel sequence of a map of short exact sequences

Consider a commutative diagram of modules with exact rows
```
M₁ -f₁→ M₂ -f₂→ M₃
|       |       |
i₁      i₂      i₃
↓       ↓       ↓
N₁ -g₁→ N₂ -g₂→ N₃
```
in which `f₁` and `g₁` are injective and `f₂` and `g₂` are surjective. The snake lemma gives the
six-term exact sequence
```
0 → ker i₁ → ker i₂ → ker i₃ → coker i₁ → coker i₂ → coker i₃ → 0.
```
Its outer maps are the restrictions of `f₁, f₂` to the kernels and the maps `g₁, g₂` induce on
the cokernels; the connecting map `Function.Exact.snakeδ` is Mathlib's `SnakeLemma.δ'` applied to
the kernel inclusion of `i₃` and the cokernel projection of `i₁`. This file records the exactness
of the kernel row, of the cokernel row and at both ends of the connecting map, and derives the
two-out-of-three property for vertical maps with finite-dimensional kernel and cokernel together
with the additivity of the index, `index i₂ = index i₁ + index i₃`. These are the algebraic
inputs for the corresponding statements about Fredholm operators.

The sequence is built from Mathlib's module form of the snake lemma rather than from the
categorical `CategoryTheory.ShortComplex.SnakeInput`, so that the six modules may live in
different universes.

## Main declarations

* `Function.Exact.restrict_ker`: the kernel row `ker i₁ → ker i₂ → ker i₃` is exact.
* `Function.Exact.mapQ_range`: the cokernel row `coker i₁ → coker i₂ → coker i₃` is exact.
* `Function.Exact.snakeδ`: the connecting map `ker i₃ → coker i₁`, with exactness
  `Function.Exact.restrict_ker_snakeδ` at `ker i₃` and `Function.Exact.snakeδ_mapQ_range` at
  `coker i₁`.
* `LinearMap.snakeδ_prodMap_eq_zero`: the connecting map of a direct sum, with split rows,
  vanishes.
* `LinearMap.finiteDimensional_ker₂_of_finiteDimensional_ker₁₃` and
  `LinearMap.finiteDimensional_coker₂_of_finiteDimensional_coker₁₃`: finiteness in the middle.
* `LinearMap.finiteDimensional_ker₃_of_finiteDimensional_ker₂_coker₁` and
  `LinearMap.finiteDimensional_coker₁_of_finiteDimensional_ker₃_coker₂`: finiteness across the
  connecting map.
* `LinearMap.index_eq_add_of_exact`: the index of `i₂` is the sum of the indices of `i₁`
  and `i₃`.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §1.
-/

public section

open Function Module Submodule LinearMap

variable {R M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]

section Ring

variable [Ring R] [Module R M₁] [Module R M₂] [Module R M₃] [Module R N₁] [Module R N₂]
  [Module R N₃]
  {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
  {i₁ : M₁ →ₗ[R] N₁} {i₂ : M₂ →ₗ[R] N₂} {i₃ : M₃ →ₗ[R] N₃}

/-- **Exactness of the kernel row.** For a commutative diagram with exact top row `f₁, f₂` and
injective `g₁`, the restrictions of `f₁` and `f₂` to the kernels of the vertical maps form an
exact sequence `ker i₁ → ker i₂ → ker i₃`. -/
theorem Function.Exact.restrict_ker (hf : Exact f₁ f₂) (hg₁ : Injective g₁)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    Exact (f₁.restrict (fun _ ↦ map_mem_ker_of_comp_eq f₁ h₁))
      (f₂.restrict (fun _ ↦ map_mem_ker_of_comp_eq f₂ h₂)) := by
  rintro ⟨y, hy⟩
  constructor
  · intro h0
    obtain ⟨x, rfl⟩ := (hf y).1 (congrArg Subtype.val h0)
    refine ⟨⟨x, hg₁ ?_⟩, rfl⟩
    rw [map_zero, ← LinearMap.comp_apply, h₁, LinearMap.comp_apply]
    exact hy
  · rintro ⟨⟨x, _⟩, hxy⟩
    ext
    rw [← hxy, coe_restrict_apply, coe_restrict_apply, hf.apply_apply_eq_zero,
      ZeroMemClass.coe_zero]

/-- **Exactness of the cokernel row.** For a commutative diagram with exact bottom row `g₁, g₂`
and surjective `f₂`, the maps induced by `g₁` and `g₂` on the cokernels of the vertical maps form
an exact sequence `coker i₁ → coker i₂ → coker i₃`. -/
theorem Function.Exact.mapQ_range (hg : Exact g₁ g₂) (hf₂ : Surjective f₂)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    Exact ((range i₁).mapQ (range i₂) g₁ (range_le_comap_range_of_comp_eq h₁))
      ((range i₂).mapQ (range i₃) g₂ (range_le_comap_range_of_comp_eq h₂)) := by
  rw [hg.exact_mapQ_iff]
  rintro _ ⟨-, z, rfl⟩
  obtain ⟨w, rfl⟩ := hf₂ z
  exact ⟨i₂ w, ⟨w, rfl⟩, LinearMap.congr_fun h₂ w⟩

end Ring

section CommRing

variable [CommRing R] [Module R M₁] [Module R M₂] [Module R M₃] [Module R N₁] [Module R N₂]
  [Module R N₃]
  {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
  {i₁ : M₁ →ₗ[R] N₁} {i₂ : M₂ →ₗ[R] N₂} {i₃ : M₃ →ₗ[R] N₃}

/-- The connecting map `ker i₃ → coker i₁` of the snake lemma, for a commutative diagram with
exact rows, `f₂` surjective and `g₁` injective. It is Mathlib's `SnakeLemma.δ'` for the kernel
inclusion of `i₃` and the cokernel projection of `i₁`. -/
noncomputable def Function.Exact.snakeδ (hf : Exact f₁ f₂) (hg : Exact g₁ g₂)
    (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) : ker i₃ →ₗ[R] N₁ ⧸ range i₁ :=
  SnakeLemma.δ' i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ (ker i₃).subtype (exact_subtype_ker_map i₃)
    (range i₁).mkQ (exact_map_mkQ_range i₁) hf₂ hg₁

/-- The connecting map `Function.Exact.snakeδ` is Mathlib's `SnakeLemma.δ'`. -/
theorem Function.Exact.snakeδ_eq_δ' (hf : Exact f₁ f₂) (hg : Exact g₁ g₂)
    (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    hf.snakeδ hg hf₂ hg₁ h₁ h₂ = SnakeLemma.δ' i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ (ker i₃).subtype
      (exact_subtype_ker_map i₃) (range i₁).mkQ (exact_map_mkQ_range i₁) hf₂ hg₁ :=
  (rfl)

/-- The connecting map sends `x ∈ ker i₃` to the class of `z`, where `f₂ y = x` and
`g₁ z = i₂ y`. -/
theorem Function.Exact.snakeδ_apply (hf : Exact f₁ f₂) (hg : Exact g₁ g₂)
    (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) (x : ker i₃) (y : M₂)
    (hy : f₂ y = x) (z : N₁) (hz : g₁ z = i₂ y) :
    hf.snakeδ hg hf₂ hg₁ h₁ h₂ x = Submodule.Quotient.mk z :=
  SnakeLemma.δ'_eq i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ _ _ _ _ hf₂ hg₁ x y hy z hz

/-- **Exactness at `ker i₃`.** The snake sequence `ker i₂ → ker i₃ → coker i₁` is exact. -/
theorem Function.Exact.restrict_ker_snakeδ (hf : Exact f₁ f₂) (hg : Exact g₁ g₂)
    (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    Exact (f₂.restrict fun _ ↦ map_mem_ker_of_comp_eq f₂ h₂) (hf.snakeδ hg hf₂ hg₁ h₁ h₂) :=
  SnakeLemma.exact_δ'_right i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ (ker i₂).subtype
    (exact_subtype_ker_map i₂) (ker i₃).subtype (exact_subtype_ker_map i₃) (range i₁).mkQ
    (exact_map_mkQ_range i₁) hf₂ hg₁ _ (by ext; simp) (ker i₃).injective_subtype

/-- **Exactness at `coker i₁`.** The snake sequence `ker i₃ → coker i₁ → coker i₂` is exact. -/
theorem Function.Exact.snakeδ_mapQ_range (hf : Exact f₁ f₂) (hg : Exact g₁ g₂)
    (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    Exact (hf.snakeδ hg hf₂ hg₁ h₁ h₂)
      ((range i₁).mapQ (range i₂) g₁ (range_le_comap_range_of_comp_eq h₁)) :=
  SnakeLemma.exact_δ'_left i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ (ker i₃).subtype
    (exact_subtype_ker_map i₃) (range i₁).mkQ (exact_map_mkQ_range i₁) (range i₂).mkQ
    (exact_map_mkQ_range i₂) hf₂ hg₁ _ (mapQ_mkQ ..) (range i₁).mkQ_surjective

/-- **The connecting map of a direct sum vanishes.** For the split rows
`0 → M₁ → M₁ × M₃ → M₃ → 0` and `0 → N₁ → N₁ × N₃ → N₃ → 0` and the vertical maps `j₁`,
`j₁.prodMap j₃` and `j₃`, the connecting map `ker j₃ → coker j₁` is zero: `x ∈ ker j₃` lifts to
`(0, x) ∈ ker (j₁.prodMap j₃)`. -/
theorem LinearMap.snakeδ_prodMap_eq_zero (j₁ : M₁ →ₗ[R] N₁) (j₃ : M₃ →ₗ[R] N₃) :
    Exact.inl_snd.snakeδ Exact.inl_snd (snd_surjective (R := R)) (inl_injective (R := R))
      (prodMap_comp_inl j₁ j₃).symm (snd_comp_prodMap j₁ j₃) = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  rw [Exact.inl_snd.snakeδ_apply Exact.inl_snd (snd_surjective (R := R)) (inl_injective (R := R))
    (prodMap_comp_inl j₁ j₃).symm (snd_comp_prodMap j₁ j₃) x (0, x) rfl 0
    (by simp [mem_ker.1 x.property])]
  simp

end CommRing

namespace LinearMap

section DivisionRing

variable {k : Type*} [DivisionRing k] [Module k M₁] [Module k M₂] [Module k M₃] [Module k N₁]
  [Module k N₂] [Module k N₃]
  {f₁ : M₁ →ₗ[k] M₂} {f₂ : M₂ →ₗ[k] M₃} {g₁ : N₁ →ₗ[k] N₂} {g₂ : N₂ →ₗ[k] N₃}
  {i₁ : M₁ →ₗ[k] N₁} {i₂ : M₂ →ₗ[k] N₂} {i₃ : M₃ →ₗ[k] N₃}

/-- In a commutative diagram with exact top row and injective `g₁`, if the outer vertical maps
have finite-dimensional kernels, so does the middle one. -/
theorem finiteDimensional_ker₂_of_finiteDimensional_ker₁₃ [FiniteDimensional k (ker i₁)]
    [FiniteDimensional k (ker i₃)] (hf : Exact f₁ f₂) (hg₁ : Injective g₁)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    FiniteDimensional k (ker i₂) :=
  (hf.restrict_ker hg₁ h₁ h₂).moduleFinite

/-- In a commutative diagram with exact bottom row and surjective `f₂`, if the outer vertical maps
have finite-dimensional cokernels, so does the middle one. -/
theorem finiteDimensional_coker₂_of_finiteDimensional_coker₁₃
    [FiniteDimensional k (N₁ ⧸ range i₁)] [FiniteDimensional k (N₃ ⧸ range i₃)]
    (hg : Exact g₁ g₂) (hf₂ : Surjective f₂)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    FiniteDimensional k (N₂ ⧸ range i₂) :=
  (hg.mapQ_range hf₂ h₁ h₂).moduleFinite

/-- In a commutative square `g₁ ∘ i₁ = i₂ ∘ f₁` with `f₁` injective, a finite-dimensional kernel
of `i₂` forces a finite-dimensional kernel of `i₁`. -/
theorem finiteDimensional_ker₁_of_finiteDimensional_ker₂ [FiniteDimensional k (ker i₂)]
    (hf₁ : Injective f₁) (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) :
    FiniteDimensional k (ker i₁) :=
  .of_injective _ (injective_restrict hf₁ fun _ ↦ map_mem_ker_of_comp_eq f₁ h₁)

/-- In a commutative square `g₂ ∘ i₂ = i₃ ∘ f₂` with `g₂` surjective, a finite-dimensional
cokernel of `i₂` forces a finite-dimensional cokernel of `i₃`. -/
theorem finiteDimensional_coker₃_of_finiteDimensional_coker₂
    [FiniteDimensional k (N₂ ⧸ range i₂)] (hg₂ : Surjective g₂) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    FiniteDimensional k (N₃ ⧸ range i₃) :=
  .of_surjective _ (mapQ_surjective _ _ g₂ (range_le_comap_range_of_comp_eq h₂) hg₂)

end DivisionRing

section Field

variable {k : Type*} [Field k] [Module k M₁] [Module k M₂] [Module k M₃] [Module k N₁]
  [Module k N₂] [Module k N₃]
  {f₁ : M₁ →ₗ[k] M₂} {f₂ : M₂ →ₗ[k] M₃} {g₁ : N₁ →ₗ[k] N₂} {g₂ : N₂ →ₗ[k] N₃}
  {i₁ : M₁ →ₗ[k] N₁} {i₂ : M₂ →ₗ[k] N₂} {i₃ : M₃ →ₗ[k] N₃}

/-- In a commutative diagram with exact rows, `f₂` surjective and `g₁` injective, if the kernel
of `i₂` and the cokernel of `i₁` are finite dimensional, so is the kernel of `i₃`: the snake
sequence `ker i₂ → ker i₃ → coker i₁` is exact. -/
theorem finiteDimensional_ker₃_of_finiteDimensional_ker₂_coker₁ [FiniteDimensional k (ker i₂)]
    [FiniteDimensional k (N₁ ⧸ range i₁)] (hf : Exact f₁ f₂) (hg : Exact g₁ g₂)
    (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    FiniteDimensional k (ker i₃) :=
  (hf.restrict_ker_snakeδ hg hf₂ hg₁ h₁ h₂).moduleFinite

/-- In a commutative diagram with exact rows, `f₂` surjective and `g₁` injective, if the kernel
of `i₃` and the cokernel of `i₂` are finite dimensional, so is the cokernel of `i₁`: the snake
sequence `ker i₃ → coker i₁ → coker i₂` is exact. -/
theorem finiteDimensional_coker₁_of_finiteDimensional_ker₃_coker₂ [FiniteDimensional k (ker i₃)]
    [FiniteDimensional k (N₂ ⧸ range i₂)] (hf : Exact f₁ f₂) (hg : Exact g₁ g₂)
    (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    FiniteDimensional k (N₁ ⧸ range i₁) :=
  (hf.snakeδ_mapQ_range hg hf₂ hg₁ h₁ h₂).moduleFinite

/-- **Additivity of the index along a map of short exact sequences.** For a commutative diagram
whose rows `0 → M₁ → M₂ → M₃ → 0` and `0 → N₁ → N₂ → N₃ → 0` are short exact, if the outer
vertical maps have finite-dimensional kernels and cokernels, then
`index i₂ = index i₁ + index i₃`. The middle map then has finite-dimensional kernel and cokernel
as well, by `finiteDimensional_ker₂_of_finiteDimensional_ker₁₃` and
`finiteDimensional_coker₂_of_finiteDimensional_coker₁₃`. -/
theorem index_eq_add_of_exact [FiniteDimensional k (ker i₁)] [FiniteDimensional k (ker i₃)]
    [FiniteDimensional k (N₁ ⧸ range i₁)] [FiniteDimensional k (N₃ ⧸ range i₃)]
    (hf : Exact f₁ f₂) (hg : Exact g₁ g₂) (hf₁ : Injective f₁) (hf₂ : Surjective f₂)
    (hg₁ : Injective g₁) (hg₂ : Surjective g₂)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    i₂.index = i₁.index + i₃.index := by
  -- `0 → ker i₁ → ker i₂ → ker i₃ → coker i₁ → coker i₂ → coker i₃ → 0`
  have := finiteDimensional_ker₂_of_finiteDimensional_ker₁₃ hf hg₁ h₁ h₂
  have := finiteDimensional_coker₂_of_finiteDimensional_coker₁₃ hg hf₂ h₁ h₂
  have := Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six _ _ _ _ _
    (injective_restrict hf₁ fun _ ↦ map_mem_ker_of_comp_eq f₁ h₁) (hf.restrict_ker hg₁ h₁ h₂)
    (hf.restrict_ker_snakeδ hg hf₂ hg₁ h₁ h₂) (hf.snakeδ_mapQ_range hg hf₂ hg₁ h₁ h₂)
    (hg.mapQ_range hf₂ h₁ h₂) (mapQ_surjective _ _ g₂ (range_le_comap_range_of_comp_eq h₂) hg₂)
  simp only [index_eq_finrank_sub]
  linarith

end Field

end LinearMap
