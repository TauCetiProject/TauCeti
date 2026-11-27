/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.SnakeLemma
public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Snake
import TauCeti.Analysis.Fredholm.Prod

/-!
# Fredholm operators along maps of short exact sequences

Consider a commutative diagram of continuous linear maps between topological vector spaces
```
0 → E₁ -f₁→ E₂ -f₂→ E₃ → 0
    |       |       |
    i₁      i₂      i₃
    ↓       ↓       ↓
0 → F₁ -g₁→ F₂ -g₂→ F₃ → 0
```
whose rows are exact. If two of the three vertical maps are Fredholm, then so is the third,
provided its domain and codomain are complete normed spaces over an `IsRCLikeNormedField`, and
`index i₂ = index i₁ + index i₃`.

Only algebraic exactness of the rows is assumed: no topological splitting of the rows, and no
completeness of the spaces carrying the two given Fredholm maps. The snake lemma
(`TauCeti.Algebra.Module.SnakeLemma`) shows that the kernel and cokernel of the third map are
finite dimensional, and between Banach spaces over `ℝ` or `ℂ` this already makes it Fredholm
(`ContinuousLinearMap.IsFredholm.of_finite_ker_coker`). The index formula needs neither
completeness nor norms: it holds for Fredholm maps between topological vector spaces.

Some exactness hypotheses are not needed in each two-out-of-three statement and are omitted: for
example, the middle map is Fredholm without injectivity of `f₁` or surjectivity of `g₂`.

We also record the specialization of index additivity to upper-triangular block operators
(`upperTriangularBlock A B D`) and the composition snake diagram (`compSnakeMiddle T S`).

## Main declarations

* `ContinuousLinearMap.IsFredholm.isFredholm₂_of_exact`,
  `ContinuousLinearMap.IsFredholm.isFredholm₃_of_exact` and
  `ContinuousLinearMap.IsFredholm.isFredholm₁_of_exact`: two out of three.
* `ContinuousLinearMap.IsFredholm.index_eq_add_of_exact`,
  `ContinuousLinearMap.IsFredholm.index_eq_add_of_exact_of_left_middle`, and
  `ContinuousLinearMap.IsFredholm.index_eq_add_of_exact_of_middle_right`: the index is additive
  along a map of short exact sequences.
* `ContinuousLinearMap.index_upperTriangularBlock`,
  `ContinuousLinearMap.index_upperTriangularBlock_of_left`, and
  `ContinuousLinearMap.index_upperTriangularBlock_of_right`: index additivity for upper-triangular
  blocks.
* `ContinuousLinearMap.isFredholm_compSnakeMiddle_iff`: `(compSnakeMiddle T S).IsFredholm ↔
  (S ∘L T).IsFredholm`.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.1,
  Theorem 19.1.2 and Corollary 19.1.7.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

open Function LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}

section IsRCLikeNormedField

variable [IsRCLikeNormedField 𝕜]

/-- **Two out of three, middle.** In a commutative diagram with exact rows, `f₂` surjective and
`g₁` injective, if the outer vertical maps are Fredholm, then so is the middle one, provided its
domain and codomain are complete normed spaces. -/
theorem IsFredholm.isFredholm₂_of_exact
    [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [TopologicalSpace E₃] [AddCommGroup E₃] [Module 𝕜 E₃]
    [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
    [TopologicalSpace F₃] [AddCommGroup F₃] [Module 𝕜 F₃]
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    {i₁ : E₁ →L[𝕜] F₁} {i₂ : E₂ →L[𝕜] F₂} {i₃ : E₃ →L[𝕜] F₃}
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
then so is the third one, provided its domain and codomain are complete normed spaces. -/
theorem IsFredholm.isFredholm₃_of_exact
    [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
    [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
    [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [CompleteSpace E₃]
    [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁]
    [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
    [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [CompleteSpace F₃]
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    {i₁ : E₁ →L[𝕜] F₁} {i₂ : E₂ →L[𝕜] F₂} {i₃ : E₃ →L[𝕜] F₃}
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
Fredholm, then so is the first one, provided its domain and codomain are complete normed spaces. -/
theorem IsFredholm.isFredholm₁_of_exact
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
    [TopologicalSpace E₃] [AddCommGroup E₃] [Module 𝕜 E₃]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [CompleteSpace F₁]
    [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
    [TopologicalSpace F₃] [AddCommGroup F₃] [Module 𝕜 F₃]
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    {i₁ : E₁ →L[𝕜] F₁} {i₂ : E₂ →L[𝕜] F₂} {i₃ : E₃ →L[𝕜] F₃}
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

/-- Index additivity along short exact sequences when the left and middle vertical operators are
Fredholm. -/
theorem IsFredholm.index_eq_add_of_exact_of_left_middle (hi₁ : i₁.IsFredholm) (hi₂ : i₂.IsFredholm)
    (hf : Exact f₁ f₂) (hg : Exact g₁ g₂) (hf₁ : Injective f₁) (hf₂ : Surjective f₂)
    (hg₁ : Injective g₁) (hg₂ : Surjective g₂)
    (h₁ : g₁ ∘L i₁ = i₂ ∘L f₁) (h₂ : g₂ ∘L i₂ = i₃ ∘L f₂) :
    i₂.index = i₁.index + i₃.index := by
  have := hi₁.finite_ker
  have := hi₁.finite_coker
  have := hi₂.finite_ker
  have := hi₂.finite_coker
  rw [index_def, index_def, index_def]
  exact LinearMap.index_eq_add_of_exact_of_left_middle hf hg hf₁ hf₂ hg₁ hg₂
    (toLinearMap_comp_eq h₁) (toLinearMap_comp_eq h₂)

/-- Index additivity along short exact sequences when the middle and right vertical operators are
Fredholm. -/
theorem IsFredholm.index_eq_add_of_exact_of_middle_right (hi₂ : i₂.IsFredholm) (hi₃ : i₃.IsFredholm)
    (hf : Exact f₁ f₂) (hg : Exact g₁ g₂) (hf₁ : Injective f₁) (hf₂ : Surjective f₂)
    (hg₁ : Injective g₁) (hg₂ : Surjective g₂)
    (h₁ : g₁ ∘L i₁ = i₂ ∘L f₁) (h₂ : g₂ ∘L i₂ = i₃ ∘L f₂) :
    i₂.index = i₁.index + i₃.index := by
  have := hi₂.finite_ker
  have := hi₂.finite_coker
  have := hi₃.finite_ker
  have := hi₃.finite_coker
  rw [index_def, index_def, index_def]
  exact LinearMap.index_eq_add_of_exact_of_middle_right hf hg hf₁ hf₂ hg₁ hg₂
    (toLinearMap_comp_eq h₁) (toLinearMap_comp_eq h₂)

end TVS

section FredholmBlockIndex

variable {E₁ E₂ F₁ F₂ : Type*}
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
  (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)

/-- The index of an upper-triangular block operator `[[A, B], [0, D]]` with Fredholm diagonal
blocks is `A.index + D.index`, independently of the off-diagonal block `B`. -/
theorem index_upperTriangularBlock (hA : A.IsFredholm) (hD : D.IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  hA.index_eq_add_of_exact hD .inl_snd .inl_snd LinearMap.inl_injective LinearMap.snd_surjective
    LinearMap.inl_injective LinearMap.snd_surjective
    (A.upperTriangularBlock_comp_inl B D).symm (A.snd_comp_upperTriangularBlock B D)

/-- Index additivity for `upperTriangularBlock A B D` when `A` and the block operator are
Fredholm. -/
theorem index_upperTriangularBlock_of_left
    (hA : A.IsFredholm) (hM : (upperTriangularBlock A B D).IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  hA.index_eq_add_of_exact_of_left_middle hM .inl_snd .inl_snd LinearMap.inl_injective
    LinearMap.snd_surjective LinearMap.inl_injective LinearMap.snd_surjective
    (A.upperTriangularBlock_comp_inl B D).symm (A.snd_comp_upperTriangularBlock B D)

/-- Index additivity for `upperTriangularBlock A B D` when the block operator and `D` are
Fredholm. -/
theorem index_upperTriangularBlock_of_right
    (hM : (upperTriangularBlock A B D).IsFredholm) (hD : D.IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  hM.index_eq_add_of_exact_of_middle_right hD .inl_snd .inl_snd LinearMap.inl_injective
    LinearMap.snd_surjective LinearMap.inl_injective LinearMap.snd_surjective
    (A.upperTriangularBlock_comp_inl B D).symm (A.snd_comp_upperTriangularBlock B D)

end FredholmBlockIndex

section FredholmCompSnake

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F]
  [TopologicalSpace G] [AddCommGroup G] [Module 𝕜 G] [IsTopologicalAddGroup G]

/-- `compSnakeMiddle T S` is Fredholm if and only if the composite `S ∘L T` is Fredholm. Combined
with `index_compSnakeMiddle` and `index_upperTriangularBlock`, applying the snake index theorem to
`(T, compSnakeMiddle T S, S)` directly recovers `IsFredholm.index_comp`:
`(S ∘L T).index = (compSnakeMiddle T S).index = T.index + S.index = S.index + T.index`. -/
@[simp] theorem isFredholm_compSnakeMiddle_iff (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (compSnakeMiddle T S).IsFredholm ↔ (S ∘L T).IsFredholm := by
  have hconj : (S.compSnakeMiddleCodEquiv.symm : F × G →L[𝕜] F × G) ∘L compSnakeMiddle T S =
      ((ContinuousLinearMap.id 𝕜 F).prodMap (S ∘L T)) ∘L
        (T.compSnakeMiddleDomEquiv : E × F →L[𝕜] F × E) := by
    rw [T.compSnakeMiddle_eq_comp_prodMap_comp S]
    ext x <;> simp
  rw [isFredholm_iff_of_comp_eq T.compSnakeMiddleDomEquiv S.compSnakeMiddleCodEquiv.symm hconj,
    isFredholm_prodMap_iff]
  exact ⟨And.right, fun hST ↦ ⟨.id, hST⟩⟩

end FredholmCompSnake

end ContinuousLinearMap
