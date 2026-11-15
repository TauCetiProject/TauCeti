/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LinearMap.Snake
public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.InnerProductSpace.ShortExact
public import TauCeti.Topology.Algebra.Module.Quotient

/-!
# Snake sequences, two-out-of-three Fredholmness, and block operators

A commuting diagram of continuous linear maps between two exact three-term rows
```text
      E₁ --f₁--> E₂ --f₂--> E₃ ⟶ 0
      |          |          |
     T₁         T₂         T₃
      v          v          v
0 ⟶ F₁ --g₁--> F₂ --g₂--> F₃
```
induces continuous linear maps on kernels (`ContinuousLinearMap.kerMapL`) and on topological
quotient cokernels (`ContinuousLinearMap.cokerMapL`). When `f₂` admits a continuous linear right
inverse `σ` and `g₁` admits a continuous linear left inverse `ρ`, the connecting map
`TauCeti.snakeδ` is bundled as a continuous linear map
`TauCeti.snakeδL : T₃.ker →L[R] F₁ ⧸ T₁.range` via
`T₁.range.mkQL ∘L ρ ∘L T₂ ∘L σ ∘L T₃.ker.subtypeL`. Because its underlying linear map equals
`TauCeti.snakeδ` (`TauCeti.toLinearMap_snakeδL`), `TauCeti.snakeδL` is independent of the chosen
continuous splittings `σ` and `ρ` (`TauCeti.snakeδL_eq_snakeδL`), and the six continuous linear
maps form an exact sequence.

When the middle spaces `E₂, F₂` are Hilbert spaces and `E₃, F₁` are Banach spaces over an `RCLike`
field, `TauCeti.Analysis.InnerProductSpace.ShortExact` supplies orthogonal continuous linear
splittings from algebraic exactness alone, so `TauCeti.snakeδ` is automatically continuous
(`TauCeti.continuous_snakeδ`, bundled as `TauCeti.hilbertSnakeδL`).

From the algebraic two-out-of-three finiteness of kernels and cokernels in
`TauCeti.Algebra.Module.LinearMap.Snake` together with
`ContinuousLinearMap.IsFredholm.of_finite_ker_coker`:

* If any two of `T₁, T₂, T₃` are Fredholm in a short exact diagram, their indices satisfy
  `T₂.index = T₁.index + T₃.index` (`TauCeti.index_eq_add_of_isFredholm_left_right` and its two
  companions, needing no completeness on the spaces).
* If the target column consists of Banach spaces over an `IsRCLikeNormedField` and the other two
  vertical maps are Fredholm, then the third vertical map is natively Fredholm
  (`TauCeti.isFredholm_middle_of_exact`, `TauCeti.isFredholm_right_of_exact`,
  `TauCeti.isFredholm_left_of_exact`).

## Upper-triangular block operators and parametrices

For `A : E₁ →L[R] F₁`, `B : E₂ →L[R] F₁`, and `D : E₂ →L[R] F₂`,
`ContinuousLinearMap.upperTriangularBlock A B D` acts on `E₁ × E₂ → F₁ × F₂` by
`(x, y) ↦ (A x + B y, D y)`. Intertwining the canonical split exact product rows
`0 → E₁ → E₁ × E₂ → E₂ → 0` and `0 → F₁ → F₁ × F₂ → F₂ → 0` identifies its snake connecting map
with `y ↦ [B y]` (`ContinuousLinearMap.upperTriangularBlock_snakeδL_eq`), yields two-out-of-three
Fredholmness between Banach spaces, and proves
`(upperTriangularBlock A B D).index = A.index + D.index` independently of `B`.

Comparing with the parametrix viewpoint: given left or right parametrices `P_A` of `A` and `P_D` of
`D` modulo compact operators, `ContinuousLinearMap.upperTriangularBlockParametrix P_A B P_D`, given
by `[[P_A, -P_A ∘ B ∘ P_D], [0, P_D]]`, is an explicit left or right parametrix of
`upperTriangularBlock A B D` modulo compact operators on arbitrary topological additive groups, with
no completeness hypothesis
(`ContinuousLinearMap.isCompactOperator_upperTriangularBlockParametrix_comp_sub_one`,
`ContinuousLinearMap.isCompactOperator_comp_upperTriangularBlockParametrix_sub_one`). Conversely,
the snake sequence establishes the two-out-of-three directions (`A` and the block imply `D`; `D` and
the block imply `A`) where a block parametrix need not be upper-triangular, and computes the index
without homotopy or compact-perturbation arguments.

## Composition snake diagram

Specializing `upperTriangularBlock T (-id) S` gives `ContinuousLinearMap.compSnakeMiddle T S`, the
continuous realization `(x, y) ↦ (T x - y, S y)` of `CategoryTheory.kernelCokernelCompSequence.φ`.
Explicit shear equivalences conjugate it to `id.prodMap (S ∘L T)`, identifying its Fredholmness and
index with those of `S ∘L T` and recovering `(S ∘L T).index = S.index + T.index`
(`ContinuousLinearMap.IsFredholm.index_comp`) from the snake index formula.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.1,
  Theorem 19.1.2 and Corollary 19.1.7.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace ContinuousLinearMap

section KerMapL

variable {R E₁ E₂ F₁ F₂ : Type*} [Semiring R]
  [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommMonoid F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommMonoid F₂] [Module R F₂]

/-- Continuous linear map `ker T₁ →L[R] ker T₂` induced by a commuting square
`g ∘L T₁ = T₂ ∘L f`. -/
def kerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂}
    (h : g ∘L T₁ = T₂ ∘L f) : T₁.ker →L[R] T₂.ker :=
  (f ∘L T₁.ker.subtypeL).codRestrict T₂.ker fun x ↦ by
    have hx : T₁ x = 0 := LinearMap.mem_ker.mp x.2
    rw [LinearMap.mem_ker]
    simpa only [comp_apply, Submodule.subtypeL_apply, coe_coe, hx, map_zero] using
      (DFunLike.congr_fun h (x : E₁)).symm

@[simp]
theorem coe_kerMapL_apply {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) (x : T₁.ker) :
    (kerMapL h x : E₂) = f x :=
  (rfl)

@[simp, norm_cast]
theorem toLinearMap_kerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) :
    (kerMapL h).toLinearMap = LinearMap.kerMap (congrArg toLinearMap h) :=
  LinearMap.ext fun x ↦ Subtype.ext <|
    (coe_kerMapL_apply h x).trans (LinearMap.coe_kerMap_apply _ x).symm

@[simp]
theorem subtypeL_comp_kerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) :
    T₂.ker.subtypeL ∘L kerMapL h = f ∘L T₁.ker.subtypeL :=
  (rfl)

/-- If `f` is injective, then the induced continuous linear map on kernels is injective. -/
theorem kerMapL_injective {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) (hf : Function.Injective f) :
    Function.Injective (kerMapL h) := fun _ _ hxy ↦
  Subtype.ext (hf (congrArg Subtype.val hxy))

end KerMapL

section CokerMapL

variable {R E₁ E₂ F₁ F₂ : Type*} [Ring R]
  [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]

/-- Continuous linear map `(F₁ ⧸ range T₁) →L[R] (F₂ ⧸ range T₂)` on quotient cokernels induced by
a commuting square `g ∘L T₁ = T₂ ∘L f`. -/
def cokerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂}
    (h : g ∘L T₁ = T₂ ∘L f) : (F₁ ⧸ T₁.range) →L[R] (F₂ ⧸ T₂.range) :=
  T₁.range.mapQL T₂.range g <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simpa only [comp_apply, coe_coe] using (DFunLike.congr_fun h x).symm⟩

@[simp]
theorem cokerMapL_mk {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) (y : F₁) :
    cokerMapL h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (g y) := by
  simp [cokerMapL]

@[simp, norm_cast]
theorem toLinearMap_cokerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) :
    (cokerMapL h).toLinearMap = LinearMap.cokerMap (congrArg toLinearMap h) := by
  ext y
  exact (cokerMapL_mk h y).trans (LinearMap.cokerMap_mk _ y).symm

@[simp]
theorem cokerMapL_comp_mkQL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) :
    cokerMapL h ∘L T₁.range.mkQL = T₂.range.mkQL ∘L g :=
  ContinuousLinearMap.ext fun y ↦ cokerMapL_mk h y

/-- If `g` is surjective, then the induced continuous linear map on quotient cokernels is
surjective. -/
theorem cokerMapL_surjective {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) (hg : Function.Surjective g) :
    Function.Surjective (cokerMapL h) := by
  change Function.Surjective (cokerMapL h).toLinearMap
  rw [toLinearMap_cokerMapL]
  exact LinearMap.cokerMap_surjective _ hg

end CokerMapL

end ContinuousLinearMap

namespace TauCeti

section ContinuousSnake

variable {R E₁ E₂ E₃ F₁ F₂ F₃ : Type*} [Ring R]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace E₃] [AddCommGroup E₃] [Module R E₃]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]
  [TopologicalSpace F₃] [AddCommGroup F₃] [Module R F₃]

/-- Continuous connecting linear map `ker T₃ →L[R] F₁ ⧸ range T₁` of a snake diagram whose top
surjection `f₂` has a continuous linear right inverse `σ` and whose bottom injection `g₁` has a
continuous linear left inverse `ρ`. -/
def snakeδL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (_hf : Function.Exact f₁ f₂) (_hg : Function.Exact g₁ g₂)
    (_h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (_h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (_hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (_hρ : Function.LeftInverse ρ g₁) :
    T₃.ker →L[R] F₁ ⧸ T₁.range :=
  T₁.range.mkQL ∘L ρ ∘L T₂ ∘L σ ∘L T₃.ker.subtypeL

@[simp]
theorem snakeδL_apply {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) (x₃ : T₃.ker) :
    snakeδL hf hg h₁₂ h₂₃ hσ hρ x₃ = Submodule.Quotient.mk (ρ (T₂ (σ x₃))) :=
  (rfl)

/-- The underlying linear map of `TauCeti.snakeδL` is the algebraic snake connecting map
`TauCeti.snakeδ`. -/
@[simp, norm_cast]
theorem toLinearMap_snakeδL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    (snakeδL hf hg h₁₂ h₂₃ hσ hρ).toLinearMap =
      snakeδ hf hσ.surjective hg hρ.injective
        (congrArg ContinuousLinearMap.toLinearMap h₁₂)
        (congrArg ContinuousLinearMap.toLinearMap h₂₃) :=
  (snakeδ_eq_of_rightInverse_of_leftInverse hf hg
    (congrArg ContinuousLinearMap.toLinearMap h₁₂)
    (congrArg ContinuousLinearMap.toLinearMap h₂₃) hσ hρ).symm

/-- **Splitting independence of `TauCeti.snakeδL`**: any two choices `(σ, ρ)` and `(σ', ρ')` of
continuous linear splittings induce the same continuous connecting map. -/
theorem snakeδL_eq_snakeδL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ σ' : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂) (hσ' : Function.RightInverse σ' f₂)
    {ρ ρ' : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) (hρ' : Function.LeftInverse ρ' g₁) :
    snakeδL hf hg h₁₂ h₂₃ hσ hρ = snakeδL hf hg h₁₂ h₂₃ hσ' hρ' :=
  ContinuousLinearMap.coe_injective <|
    (toLinearMap_snakeδL hf hg h₁₂ h₂₃ hσ hρ).trans
      (toLinearMap_snakeδL hf hg h₁₂ h₂₃ hσ' hρ').symm

/-- Exactness of the continuous snake sequence at `ker T₂`. -/
theorem exact_kerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Function.Exact (ContinuousLinearMap.kerMapL h₁₂) (ContinuousLinearMap.kerMapL h₂₃) := by
  change Function.Exact (ContinuousLinearMap.kerMapL h₁₂).toLinearMap
    (ContinuousLinearMap.kerMapL h₂₃).toLinearMap
  rw [ContinuousLinearMap.toLinearMap_kerMapL, ContinuousLinearMap.toLinearMap_kerMapL]
  exact LinearMap.exact_kerMap hf hg₁ _ _

/-- Exactness of the continuous snake sequence at `ker T₃`. -/
theorem exact_kerMapL_snakeδL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    Function.Exact (ContinuousLinearMap.kerMapL h₂₃) (snakeδL hf hg h₁₂ h₂₃ hσ hρ) := by
  change Function.Exact (ContinuousLinearMap.kerMapL h₂₃).toLinearMap
    (snakeδL hf hg h₁₂ h₂₃ hσ hρ).toLinearMap
  rw [ContinuousLinearMap.toLinearMap_kerMapL, toLinearMap_snakeδL]
  exact exact_kerMap_snakeδ hf hσ.surjective hg hρ.injective _ _

/-- Exactness of the continuous snake sequence at `F₁ ⧸ range T₁`. -/
theorem exact_snakeδL_cokerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    Function.Exact (snakeδL hf hg h₁₂ h₂₃ hσ hρ) (ContinuousLinearMap.cokerMapL h₁₂) := by
  change Function.Exact (snakeδL hf hg h₁₂ h₂₃ hσ hρ).toLinearMap
    (ContinuousLinearMap.cokerMapL h₁₂).toLinearMap
  rw [toLinearMap_snakeδL, ContinuousLinearMap.toLinearMap_cokerMapL]
  exact exact_snakeδ_cokerMap hf hσ.surjective hg hρ.injective _ _

/-- Exactness of the continuous snake sequence at `F₂ ⧸ range T₂`. -/
theorem exact_cokerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf₂ : Function.Surjective f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Function.Exact (ContinuousLinearMap.cokerMapL h₁₂) (ContinuousLinearMap.cokerMapL h₂₃) := by
  change Function.Exact (ContinuousLinearMap.cokerMapL h₁₂).toLinearMap
    (ContinuousLinearMap.cokerMapL h₂₃).toLinearMap
  rw [ContinuousLinearMap.toLinearMap_cokerMapL, ContinuousLinearMap.toLinearMap_cokerMapL]
  exact LinearMap.exact_cokerMap hf₂ hg _ _

end ContinuousSnake

section HilbertSnake

variable {𝕜 E₁ H₂ E₃ F₁ K₂ F₃ : Type*} [RCLike 𝕜]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [CompleteSpace E₃]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [CompleteSpace F₁]
  [NormedAddCommGroup K₂] [InnerProductSpace 𝕜 K₂] [CompleteSpace K₂]
  [TopologicalSpace F₃] [AddCommGroup F₃] [Module 𝕜 F₃] [T1Space F₃]

/-- Continuous snake connecting map for an algebraically exact diagram through Hilbert middle
spaces `H₂` and `K₂` with Banach `E₃` and `F₁`; no topological splittings are assumed as data,
because orthogonal complements supply them automatically. -/
noncomputable def hilbertSnakeδL {T₁ : E₁ →L[𝕜] F₁} {T₂ : H₂ →L[𝕜] K₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] H₂} {f₂ : H₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] K₂} {g₂ : K₂ →L[𝕜] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    T₃.ker →L[𝕜] F₁ ⧸ T₁.range :=
  snakeδL hf hg h₁₂ h₂₃
    (f₂.rightInverse_orthogonalRightInverse hf₂)
    (g₁.leftInverse_orthogonalLeftInverse hg₁ (ContinuousLinearMap.isClosed_range_of_exact hg))

@[simp, norm_cast]
theorem toLinearMap_hilbertSnakeδL {T₁ : E₁ →L[𝕜] F₁} {T₂ : H₂ →L[𝕜] K₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] H₂} {f₂ : H₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] K₂} {g₂ : K₂ →L[𝕜] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    (hilbertSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃).toLinearMap =
      snakeδ hf hf₂ hg hg₁
        (congrArg ContinuousLinearMap.toLinearMap h₁₂)
        (congrArg ContinuousLinearMap.toLinearMap h₂₃) :=
  toLinearMap_snakeδL _ _ _ _ _ _

/-- In an algebraically exact diagram through Hilbert middle spaces `H₂` and `K₂` with Banach `E₃`
and `F₁`, the algebraic snake connecting map `TauCeti.snakeδ` is continuous. -/
theorem continuous_snakeδ {T₁ : E₁ →L[𝕜] F₁} {T₂ : H₂ →L[𝕜] K₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] H₂} {f₂ : H₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] K₂} {g₂ : K₂ →L[𝕜] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Continuous (snakeδ hf hf₂ hg hg₁
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃)) := by
  rw [← toLinearMap_hilbertSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃]
  exact (hilbertSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃).continuous

/-- Exactness of the Hilbert-space continuous snake sequence at `ker T₃`. -/
theorem exact_kerMapL_hilbertSnakeδL {T₁ : E₁ →L[𝕜] F₁} {T₂ : H₂ →L[𝕜] K₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] H₂} {f₂ : H₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] K₂} {g₂ : K₂ →L[𝕜] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Function.Exact (ContinuousLinearMap.kerMapL h₂₃)
      (hilbertSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃) :=
  exact_kerMapL_snakeδL hf hg h₁₂ h₂₃ _ _

/-- Exactness of the Hilbert-space continuous snake sequence at `F₁ ⧸ range T₁`. -/
theorem exact_hilbertSnakeδL_cokerMapL {T₁ : E₁ →L[𝕜] F₁} {T₂ : H₂ →L[𝕜] K₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] H₂} {f₂ : H₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] K₂} {g₂ : K₂ →L[𝕜] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Function.Exact (hilbertSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃)
      (ContinuousLinearMap.cokerMapL h₁₂) :=
  exact_snakeδL_cokerMapL hf hg h₁₂ h₂₃ _ _

end HilbertSnake

section FredholmIndex

variable {𝕜 E₁ E₂ E₃ F₁ F₂ F₃ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [TopologicalSpace E₃] [AddCommGroup E₃] [Module 𝕜 E₃]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
  [TopologicalSpace F₃] [AddCommGroup F₃] [Module 𝕜 F₃]

/-- **Index additivity along short exact sequences** when the left and right vertical operators
are Fredholm: `T₂.index = T₁.index + T₃.index`. -/
theorem index_eq_add_of_isFredholm_left_right
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₁ : T₁.IsFredholm) (hT₃ : T₃.IsFredholm) :
    T₂.index = T₁.index + T₃.index := by
  have := hT₁.finite_ker
  have := hT₃.finite_ker
  have := hT₁.finite_coker
  have := hT₃.finite_coker
  simp only [ContinuousLinearMap.index_def]
  exact index_eq_add_of_shortExact hf₁ hf hf₂ hg₁ hg hg₂
    (congrArg ContinuousLinearMap.toLinearMap h₁₂)
    (congrArg ContinuousLinearMap.toLinearMap h₂₃)

/-- Index additivity along short exact sequences when the left and middle vertical operators are
Fredholm. -/
theorem index_eq_add_of_isFredholm_left_middle
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₁ : T₁.IsFredholm) (hT₂ : T₂.IsFredholm) :
    T₂.index = T₁.index + T₃.index := by
  have := hT₁.finite_ker
  have := hT₂.finite_ker
  have := hT₁.finite_coker
  have := hT₂.finite_coker
  simp only [ContinuousLinearMap.index_def]
  exact index_eq_add_of_shortExact_of_left_middle hf₁ hf hf₂ hg₁ hg hg₂
    (congrArg ContinuousLinearMap.toLinearMap h₁₂)
    (congrArg ContinuousLinearMap.toLinearMap h₂₃)

/-- Index additivity along short exact sequences when the middle and right vertical operators are
Fredholm. -/
theorem index_eq_add_of_isFredholm_middle_right
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₂ : T₂.IsFredholm) (hT₃ : T₃.IsFredholm) :
    T₂.index = T₁.index + T₃.index := by
  have := hT₂.finite_ker
  have := hT₃.finite_ker
  have := hT₂.finite_coker
  have := hT₃.finite_coker
  simp only [ContinuousLinearMap.index_def]
  exact index_eq_add_of_shortExact_of_middle_right hf₁ hf hf₂ hg₁ hg hg₂
    (congrArg ContinuousLinearMap.toLinearMap h₁₂)
    (congrArg ContinuousLinearMap.toLinearMap h₂₃)

end FredholmIndex

section TwoOutOfThree

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]

/-- **Two-out-of-three Fredholmness (middle column)**: if the left and right vertical operators in
a snake diagram are Fredholm and the middle column consists of Banach spaces over an
`IsRCLikeNormedField`, then the middle vertical operator is Fredholm. -/
theorem isFredholm_middle_of_exact
    {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}
    [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [TopologicalSpace E₃] [AddCommGroup E₃] [Module 𝕜 E₃]
    [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
    [TopologicalSpace F₃] [AddCommGroup F₃] [Module 𝕜 F₃]
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₁ : T₁.IsFredholm) (hT₃ : T₃.IsFredholm) :
    T₂.IsFredholm := by
  have := hT₁.finite_ker
  have := hT₃.finite_ker
  have := hT₁.finite_coker
  have := hT₃.finite_coker
  exact .of_finite_ker_coker T₂
    (finiteDimensional_ker_middle hf hg₁
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃))
    (finiteDimensional_coker_middle hf₂ hg
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃))

/-- **Two-out-of-three Fredholmness (right column)**: if the left and middle vertical operators in
a snake diagram with surjective `g₂` are Fredholm and the right column consists of Banach spaces
over an `IsRCLikeNormedField`, then the right vertical operator is Fredholm. -/
theorem isFredholm_right_of_exact
    {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}
    [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
    [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
    [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [CompleteSpace E₃]
    [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁]
    [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
    [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [CompleteSpace F₃]
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₁ : T₁.IsFredholm) (hT₂ : T₂.IsFredholm) :
    T₃.IsFredholm := by
  have := hT₂.finite_ker
  have := hT₁.finite_coker
  have := hT₂.finite_coker
  exact .of_finite_ker_coker T₃
    (finiteDimensional_ker_right hf hf₂ hg hg₁
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃))
    (finiteDimensional_coker_right hg₂ (congrArg ContinuousLinearMap.toLinearMap h₂₃))

/-- **Two-out-of-three Fredholmness (left column)**: if the middle and right vertical operators in
a snake diagram with injective `f₁` are Fredholm and the left column consists of Banach spaces
over an `IsRCLikeNormedField`, then the left vertical operator is Fredholm. -/
theorem isFredholm_left_of_exact
    {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
    [TopologicalSpace E₃] [AddCommGroup E₃] [Module 𝕜 E₃]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [CompleteSpace F₁]
    [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
    [TopologicalSpace F₃] [AddCommGroup F₃] [Module 𝕜 F₃]
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₂ : T₂.IsFredholm) (hT₃ : T₃.IsFredholm) :
    T₁.IsFredholm := by
  have := hT₂.finite_ker
  have := hT₃.finite_ker
  have := hT₂.finite_coker
  exact .of_finite_ker_coker T₁
    (finiteDimensional_ker_left hf₁ (congrArg ContinuousLinearMap.toLinearMap h₁₂))
    (finiteDimensional_coker_left hf hf₂ hg hg₁
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃))

end TwoOutOfThree

end TauCeti

namespace ContinuousLinearMap

section UpperTriangularBlock

section Semiring

variable {R E₁ E₂ F₁ F₂ G₁ G₂ : Type*} [Semiring R]
  [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommMonoid F₁] [Module R F₁] [ContinuousAdd F₁]
  [TopologicalSpace F₂] [AddCommMonoid F₂] [Module R F₂]
  [TopologicalSpace G₁] [AddCommMonoid G₁] [Module R G₁] [ContinuousAdd G₁]
  [TopologicalSpace G₂] [AddCommMonoid G₂] [Module R G₂]

/-- The **upper-triangular block operator** `[[A, B], [0, D]] : E₁ × E₂ →L[R] F₁ × F₂` sending
`(x, y)` to `(A x + B y, D y)`. -/
def upperTriangularBlock (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂) :
    E₁ × E₂ →L[R] F₁ × F₂ :=
  (A ∘L fst R E₁ E₂ + B ∘L snd R E₁ E₂).prod (D ∘L snd R E₁ E₂)

@[simp]
theorem upperTriangularBlock_apply (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    (x : E₁ × E₂) :
    upperTriangularBlock A B D x = (A x.1 + B x.2, D x.2) :=
  (rfl)

@[simp]
theorem upperTriangularBlock_zero_mid (A : E₁ →L[R] F₁) (D : E₂ →L[R] F₂) :
    upperTriangularBlock A 0 D = A.prodMap D := by
  apply ContinuousLinearMap.ext
  rintro ⟨x₁, x₂⟩
  ext <;> simp

theorem upperTriangularBlock_id [ContinuousAdd E₁] :
    upperTriangularBlock (.id R E₁) 0 (.id R E₂) = .id R (E₁ × E₂) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x₁, x₂⟩
  ext <;> simp

/-- Composition of upper-triangular block operators multiplies blocks by `[[A₁, B₁], [0, D₁]] ∘
[[A₂, B₂], [0, D₂]] = [[A₁ ∘ A₂, A₁ ∘ B₂ + B₁ ∘ D₂], [0, D₁ ∘ D₂]]`. -/
theorem upperTriangularBlock_comp (A₁ : F₁ →L[R] G₁) (B₁ : F₂ →L[R] G₁) (D₁ : F₂ →L[R] G₂)
    (A₂ : E₁ →L[R] F₁) (B₂ : E₂ →L[R] F₁) (D₂ : E₂ →L[R] F₂) :
    upperTriangularBlock A₁ B₁ D₁ ∘L upperTriangularBlock A₂ B₂ D₂ =
      upperTriangularBlock (A₁ ∘L A₂) (A₁ ∘L B₂ + B₁ ∘L D₂) (D₁ ∘L D₂) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x₁, x₂⟩
  ext <;> simp [add_assoc]

/-- Left intertwining of `upperTriangularBlock A B D` with `inl`. -/
theorem inl_comp_upperTriangularBlock_eq (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂) :
    inl R F₁ F₂ ∘L A = upperTriangularBlock A B D ∘L inl R E₁ E₂ := by
  ext x <;> simp

/-- Right intertwining of `upperTriangularBlock A B D` with `snd`. -/
theorem snd_comp_upperTriangularBlock_eq (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂) :
    snd R F₁ F₂ ∘L upperTriangularBlock A B D = D ∘L snd R E₁ E₂ := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- Exactness of the canonical product row `E₁ --inl--> E₁ × E₂ --snd--> E₂` of continuous linear
maps. -/
theorem exact_inl_snd : Function.Exact (inl R E₁ E₂) (snd R E₁ E₂) :=
  Function.Exact.inl_snd

/-- An upper-triangular block operator whose three nonzero blocks are compact operators is
compact. -/
theorem _root_.IsCompactOperator.upperTriangularBlock [ContinuousAdd F₂]
    {A : E₁ →L[R] F₁} {B : E₂ →L[R] F₁} {D : E₂ →L[R] F₂}
    (hA : IsCompactOperator A) (hB : IsCompactOperator B) (hD : IsCompactOperator D) :
    IsCompactOperator (ContinuousLinearMap.upperTriangularBlock A B D) := by
  have hrw : ContinuousLinearMap.upperTriangularBlock A B D =
      inl R F₁ F₂ ∘L A ∘L fst R E₁ E₂ + inl R F₁ F₂ ∘L B ∘L snd R E₁ E₂ +
        inr R F₁ F₂ ∘L D ∘L snd R E₁ E₂ := by
    apply ContinuousLinearMap.ext
    rintro ⟨x₁, x₂⟩
    ext <;> simp
  rw [hrw]
  exact (((hA.comp_clm (fst R E₁ E₂)).clm_comp (inl R F₁ F₂)).add
    ((hB.comp_clm (snd R E₁ E₂)).clm_comp (inl R F₁ F₂))).add
    ((hD.comp_clm (snd R E₁ E₂)).clm_comp (inr R F₁ F₂))

end Semiring

section Ring

variable {R E₁ E₂ F₁ F₂ : Type*} [Ring R]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]

/-- In the split product snake diagram for `upperTriangularBlock A B D`, the continuous connecting
map `ker D →L[R] F₁ ⧸ range A` sends `y ∈ ker D` to the class of `B y` modulo `range A`. -/
theorem upperTriangularBlock_snakeδL_eq [ContinuousAdd F₁]
    (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    {σ : E₂ →L[R] E₁ × E₂} (hσ : Function.RightInverse σ (snd R E₁ E₂))
    {ρ : F₁ × F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ (inl R F₁ F₂)) :
    TauCeti.snakeδL exact_inl_snd exact_inl_snd
      (inl_comp_upperTriangularBlock_eq A B D) (snd_comp_upperTriangularBlock_eq A B D) hσ hρ =
        A.range.mkQL ∘L B ∘L D.ker.subtypeL := by
  rw [TauCeti.snakeδL_eq_snakeδL _ _ _ _ hσ (σ' := inr R E₁ E₂) (fun _ ↦ rfl)
    hρ (ρ' := fst R F₁ F₂) (fun _ ↦ rfl)]
  ext y
  simp [TauCeti.snakeδL]

/-- Candidate **upper-triangular block parametrix** `[[P_A, -P_A ∘ B ∘ P_D], [0, P_D]]` built from
one-sided inverses or parametrices `P_A` of `A` and `P_D` of `D`. -/
def upperTriangularBlockParametrix [IsTopologicalAddGroup E₁]
    (P_A : F₁ →L[R] E₁) (B : E₂ →L[R] F₁) (P_D : F₂ →L[R] E₂) :
    F₁ × F₂ →L[R] E₁ × E₂ :=
  upperTriangularBlock P_A (-(P_A ∘L B ∘L P_D)) P_D

@[simp]
theorem upperTriangularBlockParametrix_apply [IsTopologicalAddGroup E₁]
    (P_A : F₁ →L[R] E₁) (B : E₂ →L[R] F₁) (P_D : F₂ →L[R] E₂) (y : F₁ × F₂) :
    upperTriangularBlockParametrix P_A B P_D y = (P_A y.1 - P_A (B (P_D y.2)), P_D y.2) := by
  simp [upperTriangularBlockParametrix, sub_eq_add_neg]

/-- Left remainder of `upperTriangularBlockParametrix`:
`[[P_A, -P_A B P_D], [0, P_D]] ∘ [[A, B], [0, D]] - 1` is upper-triangular with blocks
`P_A ∘ A - 1`, `-(P_A ∘ B ∘ (P_D ∘ D - 1))`, and `P_D ∘ D - 1`. -/
theorem upperTriangularBlockParametrix_comp_sub_one
    [IsTopologicalAddGroup E₁] [IsTopologicalAddGroup E₂] [ContinuousAdd F₁]
    (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    (P_A : F₁ →L[R] E₁) (P_D : F₂ →L[R] E₂) :
    upperTriangularBlockParametrix P_A B P_D ∘L upperTriangularBlock A B D - 1 =
      upperTriangularBlock (P_A ∘L A - 1) (-(P_A ∘L B ∘L (P_D ∘L D - 1))) (P_D ∘L D - 1) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x₁, x₂⟩
  ext
  · simp only [sub_apply, comp_apply, upperTriangularBlock_apply,
      upperTriangularBlockParametrix_apply, neg_apply, one_apply_eq_self, Prod.fst_sub, map_add,
      map_sub]
    abel
  · simp

/-- Right remainder of `upperTriangularBlockParametrix`:
`[[A, B], [0, D]] ∘ [[P_A, -P_A B P_D], [0, P_D]] - 1` is upper-triangular with blocks
`A ∘ P_A - 1`, `-((A ∘ P_A - 1) ∘ B ∘ P_D)`, and `D ∘ P_D - 1`. -/
theorem comp_upperTriangularBlockParametrix_sub_one
    [IsTopologicalAddGroup E₁] [IsTopologicalAddGroup F₁] [IsTopologicalAddGroup F₂]
    (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    (P_A : F₁ →L[R] E₁) (P_D : F₂ →L[R] E₂) :
    upperTriangularBlock A B D ∘L upperTriangularBlockParametrix P_A B P_D - 1 =
      upperTriangularBlock (A ∘L P_A - 1) (-((A ∘L P_A - 1) ∘L B ∘L P_D)) (D ∘L P_D - 1) := by
  apply ContinuousLinearMap.ext
  rintro ⟨y₁, y₂⟩
  ext
  · simp only [sub_apply, comp_apply, upperTriangularBlock_apply,
      upperTriangularBlockParametrix_apply, neg_apply, one_apply_eq_self, Prod.fst_sub, map_sub]
    abel
  · simp

/-- If `P_A` and `P_D` are left parametrices of `A` and `D` modulo compact operators, then
`upperTriangularBlockParametrix P_A B P_D` is a left parametrix of `upperTriangularBlock A B D`
modulo compact operators. -/
theorem isCompactOperator_upperTriangularBlockParametrix_comp_sub_one
    [IsTopologicalAddGroup E₁] [IsTopologicalAddGroup E₂] [ContinuousAdd F₁]
    {A : E₁ →L[R] F₁} (B : E₂ →L[R] F₁) {D : E₂ →L[R] F₂}
    {P_A : F₁ →L[R] E₁} {P_D : F₂ →L[R] E₂}
    (hPA : IsCompactOperator (P_A ∘L A - 1 : E₁ →L[R] E₁))
    (hPD : IsCompactOperator (P_D ∘L D - 1 : E₂ →L[R] E₂)) :
    IsCompactOperator
      (upperTriangularBlockParametrix P_A B P_D ∘L upperTriangularBlock A B D - 1 :
        E₁ × E₂ →L[R] E₁ × E₂) := by
  rw [upperTriangularBlockParametrix_comp_sub_one]
  have hmid : (⇑(-(P_A ∘L B ∘L (P_D ∘L D - 1))) : E₂ → E₁) =
      -(⇑(P_A ∘L B) ∘ ⇑(P_D ∘L D - 1 : E₂ →L[R] E₂)) := by
    ext x
    simp
  exact .upperTriangularBlock hPA (hmid ▸ (hPD.clm_comp (P_A ∘L B)).neg) hPD

/-- If `P_A` and `P_D` are right parametrices of `A` and `D` modulo compact operators, then
`upperTriangularBlockParametrix P_A B P_D` is a right parametrix of `upperTriangularBlock A B D`
modulo compact operators. -/
theorem isCompactOperator_comp_upperTriangularBlockParametrix_sub_one
    [IsTopologicalAddGroup E₁] [IsTopologicalAddGroup F₁] [IsTopologicalAddGroup F₂]
    {A : E₁ →L[R] F₁} (B : E₂ →L[R] F₁) {D : E₂ →L[R] F₂}
    {P_A : F₁ →L[R] E₁} {P_D : F₂ →L[R] E₂}
    (hPA : IsCompactOperator (A ∘L P_A - 1 : F₁ →L[R] F₁))
    (hPD : IsCompactOperator (D ∘L P_D - 1 : F₂ →L[R] F₂)) :
    IsCompactOperator
      (upperTriangularBlock A B D ∘L upperTriangularBlockParametrix P_A B P_D - 1 :
        F₁ × F₂ →L[R] F₁ × F₂) := by
  rw [comp_upperTriangularBlockParametrix_sub_one]
  have hmid : (⇑(-((A ∘L P_A - 1) ∘L B ∘L P_D)) : F₂ → F₁) =
      -(⇑(A ∘L P_A - 1 : F₁ →L[R] F₁) ∘ ⇑(B ∘L P_D)) := by
    ext y
    simp
  exact .upperTriangularBlock hPA (hmid ▸ (hPA.comp_clm (B ∘L P_D)).neg) hPD

end Ring

section FredholmBlock

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]

/-- The index of an upper-triangular block operator `[[A, B], [0, D]]` with Fredholm diagonal
blocks is `A.index + D.index`, independently of the off-diagonal block `B`. -/
theorem index_upperTriangularBlock {A : E₁ →L[𝕜] F₁} (B : E₂ →L[𝕜] F₁) {D : E₂ →L[𝕜] F₂}
    (hA : A.IsFredholm) (hD : D.IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  TauCeti.index_eq_add_of_isFredholm_left_right
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (inl_comp_upperTriangularBlock_eq A B D) (snd_comp_upperTriangularBlock_eq A B D)
    hA hD

/-- Index additivity for `upperTriangularBlock A B D` when `A` and the block operator are
Fredholm. -/
theorem index_upperTriangularBlock_of_left {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hA : A.IsFredholm) (hM : (upperTriangularBlock A B D).IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  TauCeti.index_eq_add_of_isFredholm_left_middle
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (inl_comp_upperTriangularBlock_eq A B D) (snd_comp_upperTriangularBlock_eq A B D)
    hA hM

/-- Index additivity for `upperTriangularBlock A B D` when the block operator and `D` are
Fredholm. -/
theorem index_upperTriangularBlock_of_right {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hM : (upperTriangularBlock A B D).IsFredholm) (hD : D.IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  TauCeti.index_eq_add_of_isFredholm_middle_right
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (inl_comp_upperTriangularBlock_eq A B D) (snd_comp_upperTriangularBlock_eq A B D)
    hM hD

end FredholmBlock

section BanachBlock

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]

/-- Between Banach spaces over an `IsRCLikeNormedField`, an upper-triangular block operator with
Fredholm diagonal blocks `A` and `D` is Fredholm for any bounded off-diagonal block `B`. -/
theorem IsFredholm.upperTriangularBlock
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
    {A : E₁ →L[𝕜] F₁} (B : E₂ →L[𝕜] F₁) {D : E₂ →L[𝕜] F₂}
    (hA : A.IsFredholm) (hD : D.IsFredholm) :
    (ContinuousLinearMap.upperTriangularBlock A B D).IsFredholm :=
  TauCeti.isFredholm_middle_of_exact
    exact_inl_snd LinearMap.snd_surjective exact_inl_snd LinearMap.inl_injective
    (inl_comp_upperTriangularBlock_eq A B D) (snd_comp_upperTriangularBlock_eq A B D)
    hA hD

/-- Two-out-of-three for upper-triangular blocks (bottom-right block): if `A` and
`upperTriangularBlock A B D` are Fredholm and `E₂, F₂` are Banach spaces over an
`IsRCLikeNormedField`, then `D` is Fredholm. -/
theorem IsFredholm.of_upperTriangularBlock_right
    {E₁ E₂ F₁ F₂ : Type*}
    [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hA : A.IsFredholm) (hM : (ContinuousLinearMap.upperTriangularBlock A B D).IsFredholm) :
    D.IsFredholm :=
  TauCeti.isFredholm_right_of_exact
    exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (inl_comp_upperTriangularBlock_eq A B D) (snd_comp_upperTriangularBlock_eq A B D)
    hA hM

/-- Two-out-of-three for upper-triangular blocks (top-left block): if `upperTriangularBlock A B D`
and `D` are Fredholm and `E₁, F₁` are Banach spaces over an `IsRCLikeNormedField`, then `A` is
Fredholm. -/
theorem IsFredholm.of_upperTriangularBlock_left
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [CompleteSpace F₁]
    [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hM : (ContinuousLinearMap.upperTriangularBlock A B D).IsFredholm) (hD : D.IsFredholm) :
    A.IsFredholm :=
  TauCeti.isFredholm_left_of_exact
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd
    (inl_comp_upperTriangularBlock_eq A B D) (snd_comp_upperTriangularBlock_eq A B D)
    hM hD

end BanachBlock

end UpperTriangularBlock

section CompSnake

section Ring

variable {R E F G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F]
  [TopologicalSpace G] [AddCommGroup G] [Module R G]

section CodEquiv

variable [IsTopologicalAddGroup G]

/-- Codomain shear equivalence `(v, z) ↦ (v, z + S v)` conjugating `compSnakeMiddle T S` to
`id.prodMap (S ∘L T)`. -/
def compSnakeCodEquiv (S : F →L[R] G) : (F × G) ≃L[R] (F × G) :=
  ContinuousLinearEquiv.equivOfInverse
    ((fst R F G).prod (snd R F G + S ∘L fst R F G))
    ((fst R F G).prod (snd R F G - S ∘L fst R F G))
    (fun vz ↦ by ext <;> simp)
    (fun vz ↦ by ext <;> simp)

@[simp]
theorem compSnakeCodEquiv_apply (S : F →L[R] G) (vz : F × G) :
    compSnakeCodEquiv S vz = (vz.1, vz.2 + S vz.1) :=
  (rfl)

@[simp]
theorem compSnakeCodEquiv_symm_apply (S : F →L[R] G) (vz : F × G) :
    (compSnakeCodEquiv S).symm vz = (vz.1, vz.2 - S vz.1) :=
  (rfl)

end CodEquiv

variable [IsTopologicalAddGroup F]

/-- The middle vertical map `(x, y) ↦ (T x - y, S y)` of the composition snake diagram
```text
0 ⟶ E ⟶ E × F ⟶ F ⟶ 0
    |T     |φ    |S
    v      v     v
0 ⟶ F ⟶ F × G ⟶ G ⟶ 0
```
realizing `CategoryTheory.kernelCokernelCompSequence.φ` for continuous linear maps. -/
def compSnakeMiddle (T : E →L[R] F) (S : F →L[R] G) : E × F →L[R] F × G :=
  upperTriangularBlock T (-ContinuousLinearMap.id R F) S

@[simp]
theorem compSnakeMiddle_apply (T : E →L[R] F) (S : F →L[R] G) (xy : E × F) :
    compSnakeMiddle T S xy = (T xy.1 - xy.2, S xy.2) := by
  simp [compSnakeMiddle, sub_eq_add_neg]

/-- Domain shear equivalence `(v, x) ↦ (x, T x - v)` conjugating `compSnakeMiddle T S` to
`id.prodMap (S ∘L T)`. -/
def compSnakeDomEquiv (T : E →L[R] F) : (F × E) ≃L[R] (E × F) :=
  ContinuousLinearEquiv.equivOfInverse
    ((snd R F E).prod (T ∘L snd R F E - fst R F E))
    ((T ∘L fst R E F - snd R E F).prod (fst R E F))
    (fun vx ↦ by ext <;> simp)
    (fun xy ↦ by ext <;> simp)

@[simp]
theorem compSnakeDomEquiv_apply (T : E →L[R] F) (vx : F × E) :
    compSnakeDomEquiv T vx = (vx.2, T vx.2 - vx.1) :=
  (rfl)

@[simp]
theorem compSnakeDomEquiv_symm_apply (T : E →L[R] F) (xy : E × F) :
    (compSnakeDomEquiv T).symm xy = (T xy.1 - xy.2, xy.1) :=
  (rfl)

/-- In the composition snake diagram `(T, compSnakeMiddle T S, S)`, the continuous connecting map
`ker S →L[R] F ⧸ range T` equals `-(T.range.mkQL ∘L S.ker.subtypeL)`, matching
`CategoryTheory.kernelCokernelCompSequence.δ_fac`. -/
theorem compSnakeMiddle_snakeδL_eq (T : E →L[R] F) (S : F →L[R] G)
    {σ : F →L[R] E × F} (hσ : Function.RightInverse σ (snd R E F))
    {ρ : F × G →L[R] F} (hρ : Function.LeftInverse ρ (inl R F G)) :
    TauCeti.snakeδL exact_inl_snd exact_inl_snd
      (inl_comp_upperTriangularBlock_eq T (-ContinuousLinearMap.id R F) S)
      (snd_comp_upperTriangularBlock_eq T (-ContinuousLinearMap.id R F) S) hσ hρ =
        -(T.range.mkQL ∘L S.ker.subtypeL) := by
  rw [upperTriangularBlock_snakeδL_eq T (-ContinuousLinearMap.id R F) S hσ hρ]
  ext y
  simp

variable [IsTopologicalAddGroup G]

/-- Explicit conjugation of `compSnakeMiddle T S` to `id.prodMap (S ∘L T)`. -/
theorem compSnakeCodEquiv_comp_compSnakeMiddle_comp_compSnakeDomEquiv
    (T : E →L[R] F) (S : F →L[R] G) :
    (compSnakeCodEquiv S : F × G →L[R] F × G) ∘L compSnakeMiddle T S ∘L
      (compSnakeDomEquiv T : F × E →L[R] E × F) =
        (ContinuousLinearMap.id R F).prodMap (S ∘L T) := by
  apply ContinuousLinearMap.ext
  rintro ⟨v, x⟩
  ext <;> simp [map_sub]

/-- `compSnakeMiddle T S` has the same index as the composite `S ∘L T`, with no finiteness
assumptions. -/
@[simp]
theorem index_compSnakeMiddle (T : E →L[R] F) (S : F →L[R] G) :
    (compSnakeMiddle T S).index = (S ∘L T).index := by
  have hconj := congrArg index (compSnakeCodEquiv_comp_compSnakeMiddle_comp_compSnakeDomEquiv T S)
  rw [index_equiv_comp, index_comp_equiv] at hconj
  rw [hconj, index_eq_finrank_sub, index_eq_finrank_sub, coe_prodMap, coe_id,
    LinearMap.ker_prodMap, LinearMap.ker_id, LinearMap.range_prodMap, LinearMap.range_id]
  have hker : Module.finrank R ((⊥ : Submodule R F).prod (S ∘L T).ker) =
      Module.finrank R (S ∘L T).ker := by
    let : Unique (⊥ : Submodule R F) := uniqueOfSubsingleton 0
    exact (Submodule.prodEquiv _ _ ≪≫ₗ LinearEquiv.uniqueProd).finrank_eq
  have hcoker : Module.finrank R ((F × G) ⧸ (⊤ : Submodule R F).prod (S ∘L T).range) =
      Module.finrank R (G ⧸ (S ∘L T).range) := by
    have : Subsingleton (F ⧸ (⊤ : Submodule R F)) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    let : Unique (F ⧸ (⊤ : Submodule R F)) := uniqueOfSubsingleton 0
    exact (Submodule.quotientProdEquiv _ _ ≪≫ₗ LinearEquiv.uniqueProd).finrank_eq
  rw [hker, hcoker]

end Ring

section FredholmCompSnake

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F]
  [TopologicalSpace G] [AddCommGroup G] [Module 𝕜 G] [IsTopologicalAddGroup G]

/-- `compSnakeMiddle T S` is Fredholm if and only if the composite `S ∘L T` is Fredholm. Combined
with `index_compSnakeMiddle` and `index_upperTriangularBlock`, applying the snake index theorem to
`(T, compSnakeMiddle T S, S)` directly recovers `IsFredholm.index_comp`:
`(S ∘L T).index = (compSnakeMiddle T S).index = T.index + S.index = S.index + T.index`. -/
@[simp]
theorem isFredholm_compSnakeMiddle_iff (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (compSnakeMiddle T S).IsFredholm ↔ (S ∘L T).IsFredholm := by
  have h := isFredholm_iff_of_comp_eq (compSnakeDomEquiv T).symm (compSnakeCodEquiv S)
    (T := compSnakeMiddle T S) (S := (ContinuousLinearMap.id 𝕜 F).prodMap (S ∘L T)) <| by
    apply ContinuousLinearMap.ext
    intro xy
    simp [comp_apply]
  rw [h, isFredholm_prodMap_iff]
  exact ⟨And.right, fun hST ↦ ⟨.id, hST⟩⟩

end FredholmCompSnake

end CompSnake

end ContinuousLinearMap
