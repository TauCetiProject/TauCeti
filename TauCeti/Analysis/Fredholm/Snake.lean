/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.SnakeLemma
public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Fredholm operators along maps of short exact sequences

Consider a commutative diagram of continuous linear maps between normed spaces
```
0 → E₁ -f₁→ E₂ -f₂→ E₃ → 0
    |       |       |
    i₁      i₂      i₃
    ↓       ↓       ↓
0 → F₁ -g₁→ F₂ -g₂→ F₃ → 0
```
whose rows are exact. If two of the three vertical maps are Fredholm, then so is the third,
provided its domain and codomain are complete, and `index i₂ = index i₁ + index i₃`.

Only algebraic exactness of the rows is assumed: no topological splitting of the rows, and no
completeness of the spaces carrying the two given Fredholm maps. The snake lemma
(`TauCeti.Algebra.Module.SnakeLemma`) shows that the kernel and cokernel of the third map are
finite dimensional, and between Banach spaces over `ℝ` or `ℂ` this already makes it Fredholm
(`ContinuousLinearMap.IsFredholm.of_finite_ker_coker`). The index formula needs neither
completeness nor norms: it holds for Fredholm maps between topological vector spaces.

Some exactness hypotheses are not needed in each two-out-of-three statement and are omitted: for
example, the middle map is Fredholm without injectivity of `f₁` or surjectivity of `g₂`.

## Main declarations

* `ContinuousLinearMap.IsFredholm.isFredholm₂_of_exact`,
  `ContinuousLinearMap.IsFredholm.isFredholm₃_of_exact` and
  `ContinuousLinearMap.IsFredholm.isFredholm₁_of_exact`: two out of three.
* `ContinuousLinearMap.IsFredholm.index_eq_add_of_exact`: the index is additive along a map of
  short exact sequences.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §1.
-/

public section

open Function LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}

section IsRCLikeNormedField

variable [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
  {i₁ : E₁ →L[𝕜] F₁} {i₂ : E₂ →L[𝕜] F₂} {i₃ : E₃ →L[𝕜] F₃}

/-- **Two out of three, middle.** In a commutative diagram with exact rows, `f₂` surjective and
`g₁` injective, if the outer vertical maps are Fredholm, then so is the middle one, provided its
domain and codomain are complete. -/
theorem IsFredholm.isFredholm₂_of_exact [CompleteSpace E₂] [CompleteSpace F₂]
    (hi₁ : i₁.IsFredholm) (hi₃ : i₃.IsFredholm) (hf : Exact f₁ f₂) (hg : Exact g₁ g₂)
    (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (h₁ : g₁ ∘L i₁ = i₂ ∘L f₁) (h₂ : g₂ ∘L i₂ = i₃ ∘L f₂) :
    i₂.IsFredholm := by
  have := hi₁.finite_ker
  have := hi₁.finite_coker
  have := hi₃.finite_ker
  have := hi₃.finite_coker
  exact .of_finite_ker_coker i₂
    (finiteDimensional_ker₂_of_finiteDimensional_ker₁₃ hf hg₁ (toLinearMap_comp_eq h₁)
      (toLinearMap_comp_eq h₂))
    (finiteDimensional_coker₂_of_finiteDimensional_coker₁₃ hg hf₂ (toLinearMap_comp_eq h₁)
      (toLinearMap_comp_eq h₂))

/-- **Two out of three, right.** In a commutative diagram with exact rows, `f₂` surjective and
`g₁`, `g₂` respectively injective and surjective, if the first two vertical maps are Fredholm,
then so is the third one, provided its domain and codomain are complete. -/
theorem IsFredholm.isFredholm₃_of_exact [CompleteSpace E₃] [CompleteSpace F₃]
    (hi₁ : i₁.IsFredholm) (hi₂ : i₂.IsFredholm) (hf : Exact f₁ f₂) (hg : Exact g₁ g₂)
    (hf₂ : Surjective f₂) (hg₁ : Injective g₁) (hg₂ : Surjective g₂)
    (h₁ : g₁ ∘L i₁ = i₂ ∘L f₁) (h₂ : g₂ ∘L i₂ = i₃ ∘L f₂) :
    i₃.IsFredholm := by
  have := hi₁.finite_coker
  have := hi₂.finite_ker
  have := hi₂.finite_coker
  exact .of_finite_ker_coker i₃
    (finiteDimensional_ker₃_of_finiteDimensional_ker₂_coker₁ hf hg hf₂ hg₁
      (toLinearMap_comp_eq h₁) (toLinearMap_comp_eq h₂))
    (finiteDimensional_coker₃_of_finiteDimensional_coker₂ hg₂ (toLinearMap_comp_eq h₂))

/-- **Two out of three, left.** In a commutative diagram with exact rows, `f₁`, `f₂`
respectively injective and surjective and `g₁` injective, if the last two vertical maps are
Fredholm, then so is the first one, provided its domain and codomain are complete. -/
theorem IsFredholm.isFredholm₁_of_exact [CompleteSpace E₁] [CompleteSpace F₁]
    (hi₂ : i₂.IsFredholm) (hi₃ : i₃.IsFredholm) (hf : Exact f₁ f₂) (hg : Exact g₁ g₂)
    (hf₁ : Injective f₁) (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (h₁ : g₁ ∘L i₁ = i₂ ∘L f₁) (h₂ : g₂ ∘L i₂ = i₃ ∘L f₂) :
    i₁.IsFredholm := by
  have := hi₂.finite_ker
  have := hi₂.finite_coker
  have := hi₃.finite_ker
  exact .of_finite_ker_coker i₁
    (finiteDimensional_ker₁_of_finiteDimensional_ker₂ hf₁ (toLinearMap_comp_eq h₁))
    (finiteDimensional_coker₁_of_finiteDimensional_ker₃_coker₂ hf hg hf₂ hg₁
      (toLinearMap_comp_eq h₁) (toLinearMap_comp_eq h₂))

end IsRCLikeNormedField

section TVS

variable [AddCommGroup E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
  [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
  [AddCommGroup E₃] [Module 𝕜 E₃] [TopologicalSpace E₃]
  [AddCommGroup F₁] [Module 𝕜 F₁] [TopologicalSpace F₁]
  [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂]
  [AddCommGroup F₃] [Module 𝕜 F₃] [TopologicalSpace F₃]
  {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
  {i₁ : E₁ →L[𝕜] F₁} {i₂ : E₂ →L[𝕜] F₂} {i₃ : E₃ →L[𝕜] F₃}

/-- **Additivity of the index along a map of short exact sequences.** In a commutative diagram
with short exact rows, if the outer vertical maps are Fredholm, then
`index i₂ = index i₁ + index i₃`. No completeness is needed; between Banach spaces over `ℝ` or
`ℂ` the middle map is then Fredholm by `IsFredholm.isFredholm₂_of_exact`. -/
theorem IsFredholm.index_eq_add_of_exact (hi₁ : i₁.IsFredholm) (hi₃ : i₃.IsFredholm)
    (hf : Exact f₁ f₂) (hg : Exact g₁ g₂) (hf₁ : Injective f₁) (hf₂ : Surjective f₂)
    (hg₁ : Injective g₁) (hg₂ : Surjective g₂)
    (h₁ : g₁ ∘L i₁ = i₂ ∘L f₁) (h₂ : g₂ ∘L i₂ = i₃ ∘L f₂) :
    i₂.index = i₁.index + i₃.index := by
  have := hi₁.finite_ker
  have := hi₁.finite_coker
  have := hi₃.finite_ker
  have := hi₃.finite_coker
  rw [index_def, index_def, index_def]
  exact LinearMap.index_eq_add_of_exact hf hg hf₁ hf₂ hg₁ hg₂ (toLinearMap_comp_eq h₁)
    (toLinearMap_comp_eq h₂)

end TVS

end ContinuousLinearMap
