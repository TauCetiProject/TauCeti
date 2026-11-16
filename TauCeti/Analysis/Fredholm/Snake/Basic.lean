/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.LinearAlgebra.Snake
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# Snake sequences of Fredholm operators

Given a commuting morphism `(T₀, T₁, T₂)` of continuous linear maps between exact sequences
`E₀ --i--> E₁ --p--> E₂ → 0` and `0 → F₀ --j--> F₁ --q--> F₂`, this file develops the continuous
six-term snake sequence, topological splittings on Banach and Hilbert spaces, the two-out-of-three
Fredholm theorem, and index additivity `T₁.index = T₀.index + T₂.index`.

## Main declarations

* `ContinuousLinearMap.snakeKerMapL`, `ContinuousLinearMap.snakeCokerMapL`,
  `ContinuousLinearMap.snakeConnectingL`: continuous maps of the snake sequence, with splitting
  independence (`snakeConnectingL_eq_of_rightInverse_leftInverse`), agreement with
  `ShortComplex.moduleCatSnakeInput.δ`, and six-term exactness.
* `ContinuousLinearMap.isClosed_range_of_exact`, `ContinuousLinearMap.exactEquivKer`,
  `ContinuousLinearMap.orthogonalLeftInverse`, `ContinuousLinearMap.orthogonalRightInverse`,
  `ContinuousLinearMap.orthogonalSplitEquiv`, `ContinuousLinearMap.hilbertSnakeConnectingL`:
  canonical continuous splittings and connecting map when the middle spaces are Hilbert spaces.
* `ContinuousLinearMap.index_eq_add_of_exact_of_isFredholm_left_right`,
  `ContinuousLinearMap.index_eq_add_of_exact_of_isFredholm_middle_right`,
  `ContinuousLinearMap.index_eq_add_of_exact_of_isFredholm_left_middle`: index additivity for
  topological vector spaces over a nontrivially normed field.
* `ContinuousLinearMap.isFredholm_middle_of_left_right`,
  `ContinuousLinearMap.isFredholm_left_of_middle_right`,
  `ContinuousLinearMap.isFredholm_right_of_left_middle`: two-out-of-three Fredholm theorem for
  Banach spaces over an `IsRCLikeNormedField`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 1.3.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

open CategoryTheory Module
open scoped InnerProduct

namespace ContinuousLinearMap

section ContinuousSnakeMaps

variable {𝕜 E E' F F' : Type*} [Ring 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F']
  {T : E →L[𝕜] F} {T' : E' →L[𝕜] F'}

/-- Continuous kernel restriction `ker T →L[𝕜] ker T'` induced by `g ∘L T = T' ∘L f`. -/
def snakeKerMapL (f : E →L[𝕜] E') {g : F →L[𝕜] F'} (h : g ∘L T = T' ∘L f) :
    T.ker →L[𝕜] T'.ker :=
  (f.domRestrict T.ker).codRestrict T'.ker fun x ↦ LinearMap.mem_ker.mpr <| by
    have hx : T x = 0 := LinearMap.mem_ker.mp x.2
    change T' (f x) = 0
    rw [← comp_apply, ← h, comp_apply, hx, map_zero]

/-- Evaluating `snakeKerMapL` in the ambient module applies the horizontal map. -/
@[simp]
lemma coe_snakeKerMapL_apply (f : E →L[𝕜] E') {g : F →L[𝕜] F'} (h : g ∘L T = T' ∘L f)
    (x : T.ker) : (snakeKerMapL f h x : E') = f x := (rfl)

/-- The underlying linear map of `snakeKerMapL` is `LinearMap.snakeKerMap`. -/
@[simp]
lemma toLinearMap_snakeKerMapL (f : E →L[𝕜] E') {g : F →L[𝕜] F'} (h : g ∘L T = T' ∘L f) :
    (snakeKerMapL f h : T.ker →ₗ[𝕜] T'.ker) =
      LinearMap.snakeKerMap (f : E →ₗ[𝕜] E') (g := (g : F →ₗ[𝕜] F'))
        (by simpa only [toLinearMap_comp] using congrArg toLinearMap h) :=
  LinearMap.ext fun x ↦ Subtype.ext (LinearMap.coe_snakeKerMap_apply (f : E →ₗ[𝕜] E')
    (by simpa only [toLinearMap_comp] using congrArg toLinearMap h) x).symm

/-- Continuous cokernel map `(F ⧸ range T) →L[𝕜] (F' ⧸ range T')` induced by `g ∘L T = T' ∘L f`. -/
def snakeCokerMapL {f : E →L[𝕜] E'} (g : F →L[𝕜] F') (h : g ∘L T = T' ∘L f) :
    (F ⧸ T.range) →L[𝕜] (F' ⧸ T'.range) :=
  T.range.liftQL (T'.range.mkQL.comp g) <| by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk (g (T x)) = 0
    rw [← comp_apply, h, comp_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨f x, rfl⟩

/-- Evaluating `snakeCokerMapL` on a quotient class applies the horizontal map. -/
@[simp]
lemma snakeCokerMapL_mk {f : E →L[𝕜] E'} (g : F →L[𝕜] F') (h : g ∘L T = T' ∘L f) (y : F) :
    snakeCokerMapL g h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (g y) := (rfl)

/-- The underlying linear map of `snakeCokerMapL` is `LinearMap.snakeCokerMap`. -/
@[simp]
lemma toLinearMap_snakeCokerMapL {f : E →L[𝕜] E'} (g : F →L[𝕜] F') (h : g ∘L T = T' ∘L f) :
    (snakeCokerMapL g h : (F ⧸ T.range) →ₗ[𝕜] (F' ⧸ T'.range)) =
      LinearMap.snakeCokerMap (f := (f : E →ₗ[𝕜] E')) (g : F →ₗ[𝕜] F')
        (by simpa only [toLinearMap_comp] using congrArg toLinearMap h) :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun y ↦
    (LinearMap.snakeCokerMap_mk (f := (f : E →ₗ[𝕜] E')) (g : F →ₗ[𝕜] F')
      (by simpa only [toLinearMap_comp] using congrArg toLinearMap h) y).symm

end ContinuousSnakeMaps

section ContinuousSnake

variable {𝕜 E₀ E₁ E₂ F₀ F₁ F₂ : Type*} [Ring 𝕜]
  [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
  [AddCommGroup E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
  [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
  [AddCommGroup F₀] [Module 𝕜 F₀] [TopologicalSpace F₀]
  [AddCommGroup F₁] [Module 𝕜 F₁] [TopologicalSpace F₁]
  [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂]

/-- Continuous snake connecting map `ker T₂ →L[𝕜] (F₀ ⧸ range T₀)` associated with a continuous
right inverse `s` of `p` and continuous left inverse `r` of `j`. -/
def snakeConnectingL (T₀ : E₀ →L[𝕜] F₀) (T₁ : E₁ →L[𝕜] F₁) (T₂ : E₂ →L[𝕜] F₂)
    (s : E₂ →L[𝕜] E₁) (r : F₁ →L[𝕜] F₀) : T₂.ker →L[𝕜] (F₀ ⧸ T₀.range) :=
  T₀.range.mkQL.comp (r.comp (T₁.comp (s.comp T₂.ker.subtypeL)))

/-- Evaluating `snakeConnectingL` applies `s`, `T₁`, `r`, and passes to the cokernel. -/
@[simp]
lemma snakeConnectingL_apply (T₀ : E₀ →L[𝕜] F₀) (T₁ : E₁ →L[𝕜] F₁) (T₂ : E₂ →L[𝕜] F₂)
    (s : E₂ →L[𝕜] E₁) (r : F₁ →L[𝕜] F₀) (x : T₂.ker) :
    snakeConnectingL T₀ T₁ T₂ s r x = Submodule.Quotient.mk (r (T₁ (s x))) := (rfl)

variable {i : E₀ →L[𝕜] E₁} {p : E₁ →L[𝕜] E₂} {j : F₀ →L[𝕜] F₁} {q : F₁ →L[𝕜] F₂}
  {T₀ : E₀ →L[𝕜] F₀} {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂}

section SnakeExact

variable (hip : Function.Exact i p) (hj : Function.Injective j) (hjq : Function.Exact j q)
  (h₁ : j ∘L T₀ = T₁ ∘L i) (h₂ : q ∘L T₁ = T₂ ∘L p)

include hip hj hjq h₁ h₂

/-- **Zigzag formula for `snakeConnectingL`**: whenever `p x₁ = x₂` and `j y₀ = T₁ x₁`, the
continuous connecting map sends `x₂` to `[y₀]`, regardless of the chosen splittings `(s, r)`. -/
theorem snakeConnectingL_apply_eq_mk
    {s : E₂ →L[𝕜] E₁} (hs : Function.RightInverse s p)
    {r : F₁ →L[𝕜] F₀} (hr : Function.LeftInverse r j)
    (x₂ : T₂.ker) {x₁ : E₁} (hx₁ : p x₁ = x₂) {y₀ : F₀} (hy₀ : j y₀ = T₁ x₁) :
    snakeConnectingL T₀ T₁ T₂ s r x₂ = Submodule.Quotient.mk y₀ := by
  obtain ⟨x₀, hx₀⟩ := (hip (s x₂ - x₁)).mp (by rw [map_sub, hs x₂, hx₁, sub_self])
  have hx₂0 : T₂ x₂ = 0 := LinearMap.mem_ker.mp x₂.2
  have hqs : q (T₁ (s x₂)) = 0 := by rw [← comp_apply, h₂, comp_apply, hs x₂, hx₂0]
  obtain ⟨y₀', hy₀'⟩ := (hjq (T₁ (s x₂))).mp hqs
  have hdiff : y₀' - y₀ = T₀ x₀ := hj <| by
    rw [map_sub, hy₀', hy₀, ← map_sub, ← hx₀, ← comp_apply, ← h₁, comp_apply]
  rw [snakeConnectingL_apply, ← hy₀', hr y₀']
  exact (Submodule.Quotient.eq _).mpr ⟨x₀, hdiff.symm⟩

/-- **Splitting independence**: `snakeConnectingL` is independent of the choice of continuous right
inverse `s` of `p` and continuous left inverse `r` of `j`. -/
theorem snakeConnectingL_eq_of_rightInverse_leftInverse
    {s s' : E₂ →L[𝕜] E₁} (hs : Function.RightInverse s p) (hs' : Function.RightInverse s' p)
    {r r' : F₁ →L[𝕜] F₀} (hr : Function.LeftInverse r j) (hr' : Function.LeftInverse r' j) :
    snakeConnectingL T₀ T₁ T₂ s r = snakeConnectingL T₀ T₁ T₂ s' r' := by
  ext x₂
  have hx₂0 : T₂ x₂ = 0 := LinearMap.mem_ker.mp x₂.2
  have hqs : q (T₁ (s' x₂)) = 0 := by rw [← comp_apply, h₂, comp_apply, hs' x₂, hx₂0]
  obtain ⟨y₀, hy₀⟩ := (hjq (T₁ (s' x₂))).mp hqs
  rw [snakeConnectingL_apply_eq_mk hip hj hjq h₁ h₂ hs hr x₂ (hs' x₂) hy₀,
    snakeConnectingL_apply_eq_mk hip hj hjq h₁ h₂ hs' hr' x₂ (hs' x₂) hy₀]

/-- The underlying linear map of `snakeConnectingL` agrees with `LinearMap.snakeConnecting`. -/
theorem toLinearMap_snakeConnectingL_eq_snakeConnecting
    {s : E₂ →L[𝕜] E₁} (hs : Function.RightInverse s p)
    {r : F₁ →L[𝕜] F₀} (hr : Function.LeftInverse r j) :
    (snakeConnectingL T₀ T₁ T₂ s r : T₂.ker →ₗ[𝕜] (F₀ ⧸ T₀.range)) =
      LinearMap.snakeConnecting (i := (i : E₀ →ₗ[𝕜] E₁)) (p := (p : E₁ →ₗ[𝕜] E₂))
        (j := (j : F₀ →ₗ[𝕜] F₁)) (q := (q : F₁ →ₗ[𝕜] F₂))
        (T₀ := (T₀ : E₀ →ₗ[𝕜] F₀)) (T₁ := (T₁ : E₁ →ₗ[𝕜] F₁)) (T₂ := (T₂ : E₂ →ₗ[𝕜] F₂))
        hip hs.surjective hj hjq (congrArg toLinearMap h₁) (congrArg toLinearMap h₂) :=
  LinearMap.eq_snakeConnecting_of_zigzag hip hs.surjective hj hjq
    (congrArg toLinearMap h₁) (congrArg toLinearMap h₂) _
    fun x₂ _ _ hx₁ hy₀ ↦ snakeConnectingL_apply_eq_mk hip hj hjq h₁ h₂ hs hr x₂ hx₁ hy₀

/-- Exactness at `ker T₂`: `ker T₁ →L[𝕜] ker T₂ →L[𝕜] (F₀ ⧸ range T₀)`. -/
theorem exact_snakeKerMapL_snakeConnectingL
    {s : E₂ →L[𝕜] E₁} (hs : Function.RightInverse s p)
    {r : F₁ →L[𝕜] F₀} (hr : Function.LeftInverse r j) :
    Function.Exact (snakeKerMapL p h₂) (snakeConnectingL T₀ T₁ T₂ s r) :=
  show Function.Exact (snakeKerMapL p h₂).toLinearMap (snakeConnectingL T₀ T₁ T₂ s r).toLinearMap by
    rw [toLinearMap_snakeKerMapL,
      toLinearMap_snakeConnectingL_eq_snakeConnecting hip hj hjq h₁ h₂ hs hr]
    exact LinearMap.exact_snakeKerMap_snakeConnecting hip hs.surjective hj hjq
      (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)

/-- Exactness at `F₀ ⧸ range T₀`: `ker T₂ →L[𝕜] (F₀ ⧸ range T₀) →L[𝕜] (F₁ ⧸ range T₁)`. -/
theorem exact_snakeConnectingL_snakeCokerMapL
    {s : E₂ →L[𝕜] E₁} (hs : Function.RightInverse s p)
    {r : F₁ →L[𝕜] F₀} (hr : Function.LeftInverse r j) :
    Function.Exact (snakeConnectingL T₀ T₁ T₂ s r) (snakeCokerMapL j h₁) :=
  show Function.Exact (snakeConnectingL T₀ T₁ T₂ s r).toLinearMap
      (snakeCokerMapL j h₁).toLinearMap by
    rw [toLinearMap_snakeConnectingL_eq_snakeConnecting hip hj hjq h₁ h₂ hs hr,
      toLinearMap_snakeCokerMapL]
    exact LinearMap.exact_snakeConnecting_snakeCokerMap hip hs.surjective hj hjq
      (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)

/-- When `T₁` is injective, the connecting map `ker T₂ →L[𝕜] (F₀ ⧸ range T₀)` is injective. -/
theorem injective_snakeConnectingL
    {s : E₂ →L[𝕜] E₁} (hs : Function.RightInverse s p)
    {r : F₁ →L[𝕜] F₀} (hr : Function.LeftInverse r j) (hT₁ : Function.Injective T₁) :
    Function.Injective (snakeConnectingL T₀ T₁ T₂ s r) := by
  refine (injective_iff_map_eq_zero _).mpr fun x₂ hx₂ ↦ ?_
  obtain ⟨x₁, rfl⟩ := (exact_snakeKerMapL_snakeConnectingL hip hj hjq h₁ h₂ hs hr x₂).mp hx₂
  have hx₁0 : (x₁ : E₁) = 0 := hT₁ (by rw [map_zero]; exact LinearMap.mem_ker.mp x₁.2)
  exact Subtype.ext (by simp [hx₁0])

/-- When `T₁` is surjective, the connecting map `ker T₂ →L[𝕜] (F₀ ⧸ range T₀)` is surjective. -/
theorem surjective_snakeConnectingL
    {s : E₂ →L[𝕜] E₁} (hs : Function.RightInverse s p)
    {r : F₁ →L[𝕜] F₀} (hr : Function.LeftInverse r j) (hT₁ : Function.Surjective T₁) :
    Function.Surjective (snakeConnectingL T₀ T₁ T₂ s r) := fun c₀ ↦ by
  refine (exact_snakeConnectingL_snakeCokerMapL hip hj hjq h₁ h₂ hs hr c₀).mp ?_
  induction c₀ using Submodule.Quotient.induction_on with | H y₀ =>
  obtain ⟨x₁, hx₁⟩ := hT₁ (j y₀)
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x₁, hx₁⟩

/-- When `T₁` is bijective, the connecting map `ker T₂ →L[𝕜] (F₀ ⧸ range T₀)` is bijective. -/
theorem bijective_snakeConnectingL
    {s : E₂ →L[𝕜] E₁} (hs : Function.RightInverse s p)
    {r : F₁ →L[𝕜] F₀} (hr : Function.LeftInverse r j) (hT₁ : Function.Bijective T₁) :
    Function.Bijective (snakeConnectingL T₀ T₁ T₂ s r) :=
  ⟨injective_snakeConnectingL hip hj hjq h₁ h₂ hs hr hT₁.injective,
    surjective_snakeConnectingL hip hj hjq h₁ h₂ hs hr hT₁.surjective⟩

end SnakeExact

section SameUniverse

universe v

/-- When all six spaces live in universe `v`, `snakeConnectingL` agrees with the categorical
connecting morphism `δ` of `CategoryTheory.ShortComplex.moduleCatSnakeInput`. -/
theorem toLinearMap_snakeConnectingL_eq_moduleCatSnakeInput_δ
    {E₀ E₁ E₂ F₀ F₁ F₂ : Type v}
    [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀] [AddCommGroup E₁] [Module 𝕜 E₁]
    [TopologicalSpace E₁] [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
    [AddCommGroup F₀] [Module 𝕜 F₀] [TopologicalSpace F₀] [AddCommGroup F₁] [Module 𝕜 F₁]
    [TopologicalSpace F₁] [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂]
    {i : E₀ →L[𝕜] E₁} {p : E₁ →L[𝕜] E₂} {j : F₀ →L[𝕜] F₁} {q : F₁ →L[𝕜] F₂}
    {T₀ : E₀ →L[𝕜] F₀} {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂}
    (hip : Function.Exact i p) (hj : Function.Injective j) (hjq : Function.Exact j q)
    (h₁ : j ∘L T₀ = T₁ ∘L i) (h₂ : q ∘L T₁ = T₂ ∘L p)
    {s : E₂ →L[𝕜] E₁} (hs : Function.RightInverse s p)
    {r : F₁ →L[𝕜] F₀} (hr : Function.LeftInverse r j) :
    (snakeConnectingL T₀ T₁ T₂ s r : T₂.ker →ₗ[𝕜] (F₀ ⧸ T₀.range)) =
      (ShortComplex.moduleCatSnakeInput (i := (i : E₀ →ₗ[𝕜] E₁)) (p := (p : E₁ →ₗ[𝕜] E₂))
        (j := (j : F₀ →ₗ[𝕜] F₁)) (q := (q : F₁ →ₗ[𝕜] F₂))
        (T₀ := (T₀ : E₀ →ₗ[𝕜] F₀)) (T₁ := (T₁ : E₁ →ₗ[𝕜] F₁)) (T₂ := (T₂ : E₂ →ₗ[𝕜] F₂))
        hip hs.surjective hj hjq (by simpa only [toLinearMap_comp] using congrArg toLinearMap h₁)
        (by simpa only [toLinearMap_comp] using congrArg toLinearMap h₂)).δ.hom := by
  ext x₂
  have hx₂0 : T₂ x₂ = 0 := LinearMap.mem_ker.mp x₂.2
  have hqs : q (T₁ (s x₂)) = 0 := by rw [← comp_apply, h₂, comp_apply, hs x₂, hx₂0]
  obtain ⟨y₀, hy₀⟩ := (hjq (T₁ (s x₂))).mp hqs
  rw [coe_coe, snakeConnectingL_apply_eq_mk hip hj hjq h₁ h₂ hs hr x₂ (hs x₂) hy₀]
  exact (ShortComplex.moduleCatSnakeInput_δ_apply hip hs.surjective hj hjq
    (by simpa only [toLinearMap_comp] using congrArg toLinearMap h₁)
    (by simpa only [toLinearMap_comp] using congrArg toLinearMap h₂) x₂ (hs x₂) hy₀).symm

end SameUniverse

/-- Exactness of the continuous kernel row `ker T₀ →L[𝕜] ker T₁ →L[𝕜] ker T₂`. -/
theorem exact_snakeKerMapL (hip : Function.Exact i p) (hj : Function.Injective j)
    (h₁ : j ∘L T₀ = T₁ ∘L i) (h₂ : q ∘L T₁ = T₂ ∘L p) :
    Function.Exact (snakeKerMapL i h₁) (snakeKerMapL p h₂) :=
  show Function.Exact (snakeKerMapL i h₁).toLinearMap (snakeKerMapL p h₂).toLinearMap by
    rw [toLinearMap_snakeKerMapL, toLinearMap_snakeKerMapL]
    exact LinearMap.exact_snakeKerMap hip hj (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)

/-- Exactness of the continuous cokernel row `(F₀ ⧸ range T₀) →L[𝕜] (F₁ ⧸ range T₁) →L[𝕜]
(F₂ ⧸ range T₂)`. -/
theorem exact_snakeCokerMapL (hp : Function.Surjective p) (hjq : Function.Exact j q)
    (h₁ : j ∘L T₀ = T₁ ∘L i) (h₂ : q ∘L T₁ = T₂ ∘L p) :
    Function.Exact (snakeCokerMapL j h₁) (snakeCokerMapL q h₂) :=
  show Function.Exact (snakeCokerMapL j h₁).toLinearMap (snakeCokerMapL q h₂).toLinearMap by
    rw [toLinearMap_snakeCokerMapL, toLinearMap_snakeCokerMapL]
    exact LinearMap.exact_snakeCokerMap hp hjq (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)

/-- Injectivity of `ker T₀ →L[𝕜] ker T₁` when `i` is injective. -/
theorem injective_snakeKerMapL (hi : Function.Injective i) (h₁ : j ∘L T₀ = T₁ ∘L i) :
    Function.Injective (snakeKerMapL i h₁) :=
  fun _ _ h ↦ Subtype.ext (hi (congrArg Subtype.val h))

/-- Surjectivity of `(F₁ ⧸ range T₁) →L[𝕜] (F₂ ⧸ range T₂)` when `q` is surjective. -/
theorem surjective_snakeCokerMapL (hq : Function.Surjective q) (h₂ : q ∘L T₁ = T₂ ∘L p) :
    Function.Surjective (snakeCokerMapL q h₂) := fun c₂ ↦ by
  induction c₂ using Submodule.Quotient.induction_on with | H y₂ =>
  obtain ⟨y₁, rfl⟩ := hq y₂; exact ⟨Submodule.Quotient.mk y₁, rfl⟩

end ContinuousSnake

/-! ### Topological splittings of exact sequences of Banach and Hilbert spaces -/

section TopologicalSplitting

/-- In an exact pair `E₀ --i--> E₁ --p--> E₂` into a `T1Space`, `range i = ker p` is closed. -/
theorem isClosed_range_of_exact {𝕜 E₀ E₁ E₂ : Type*} [Ring 𝕜]
    [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
    [AddCommGroup E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂] [T1Space E₂]
    {i : E₀ →L[𝕜] E₁} {p : E₁ →L[𝕜] E₂} (hip : Function.Exact i p) :
    IsClosed (i.range : Set E₁) := by
  rw [← hip.linearMap_ker_eq]; exact p.isClosed_ker

section ExactEquivKer

variable {𝕜 E₀ E₁ E₂ : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂] [T1Space E₂]
  {i : E₀ →L[𝕜] E₁} {p : E₁ →L[𝕜] E₂} (hi : Function.Injective i) (hip : Function.Exact i p)

/-- Between Banach spaces, an injective map `i : E₀ →L[𝕜] E₁` in an exact pair `E₀ → E₁ → E₂`
identifies `E₀` continuously linearly with `p.ker`, by the Banach open mapping theorem. -/
noncomputable def exactEquivKer : E₀ ≃L[𝕜] p.ker :=
  letI : CompleteSpace p.ker := p.isClosed_ker.completeSpace_coe
  ContinuousLinearEquiv.ofBijective
    (i.codRestrict p.ker fun x ↦ LinearMap.mem_ker.mpr (hip.apply_apply_eq_zero x))
    (LinearMap.ker_eq_bot.mpr fun _ _ hxy ↦ hi (congrArg Subtype.val hxy))
    (LinearMap.range_eq_top.mpr fun ⟨y, hy⟩ ↦
      let ⟨x, hx⟩ := (hip y).mp (LinearMap.mem_ker.mp hy); ⟨x, Subtype.ext hx⟩)

/-- `exactEquivKer` acts by the inclusion `i`. -/
@[simp]
lemma coe_exactEquivKer_apply (x : E₀) : (exactEquivKer hi hip x : E₁) = i x := (rfl)

/-- Applying `i` to the inverse of `exactEquivKer` recovers the kernel element. -/
@[simp]
lemma apply_exactEquivKer_symm (y : p.ker) : i ((exactEquivKer hi hip).symm y) = y := by
  rw [← coe_exactEquivKer_apply hi hip, ContinuousLinearEquiv.apply_symm_apply]

end ExactEquivKer

section HilbertLeftInverse

variable {𝕜 E₀ E₁ E₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂] [T1Space E₂]
  {i : E₀ →L[𝕜] E₁} {p : E₁ →L[𝕜] E₂} (hi : Function.Injective i) (hip : Function.Exact i p)

/-- Canonical continuous left inverse `E₁ →L[𝕜] E₀` of `i` in `0 → E₀ --i--> E₁ --p--> E₂` when
`E₀` is Banach and `E₁` is Hilbert, given by orthogonal projection onto `ker p` followed by
`(exactEquivKer)⁻¹`. -/
noncomputable def orthogonalLeftInverse : E₁ →L[𝕜] E₀ :=
  letI : CompleteSpace p.ker := p.isClosed_ker.completeSpace_coe
  (exactEquivKer hi hip).symm.toContinuousLinearMap.comp p.ker.orthogonalProjectionOnto

/-- `orthogonalLeftInverse` is a left inverse of `i`. -/
lemma orthogonalLeftInverse_leftInverse :
    Function.LeftInverse (orthogonalLeftInverse hi hip) i := fun x ↦ by
  let _ : CompleteSpace p.ker := p.isClosed_ker.completeSpace_coe
  apply hi
  change i ((exactEquivKer hi hip).symm (p.ker.orthogonalProjectionOnto (i x))) = i x
  rw [apply_exactEquivKer_symm hi hip, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨i x, LinearMap.mem_ker.mpr (hip.apply_apply_eq_zero x)⟩]

/-- Evaluating `orthogonalLeftInverse` on `i x` recovers `x`. -/
@[simp]
lemma orthogonalLeftInverse_apply_self (x : E₀) : orthogonalLeftInverse hi hip (i x) = x :=
  orthogonalLeftInverse_leftInverse hi hip x

/-- `orthogonalLeftInverse` vanishes on `(ker p)ᗮ`. -/
lemma orthogonalLeftInverse_eq_zero_of_mem_orthogonal {x : E₁} (hx : x ∈ p.kerᗮ) :
    orthogonalLeftInverse hi hip x = 0 := by
  let _ : CompleteSpace p.ker := p.isClosed_ker.completeSpace_coe
  change (exactEquivKer hi hip).symm (p.ker.orthogonalProjectionOnto x) = 0
  rw [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hx, map_zero]

include hi hip in
/-- In an exact pair `0 → E₀ --i--> E₁ --p--> E₂` with `E₀` Banach and `E₁` Hilbert, `i` admits a
continuous left inverse. -/
theorem hasLeftInverse_of_exact_of_innerProductSpace : i.HasLeftInverse :=
  ⟨orthogonalLeftInverse hi hip, orthogonalLeftInverse_leftInverse hi hip⟩

end HilbertLeftInverse

section HilbertRightInverse

variable {𝕜 E₀ E₁ E₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {i : E₀ →L[𝕜] E₁} {p : E₁ →L[𝕜] E₂}

/-- Canonical continuous right inverse `E₂ →L[𝕜] E₁` of a continuous linear surjection `p` from a
Hilbert space onto a Banach space, taking values in `(ker p)ᗮ`. -/
noncomputable def orthogonalRightInverse (hp : Function.Surjective p) : E₂ →L[𝕜] E₁ :=
  have htop : p.range = ⊤ := LinearMap.range_eq_top.mpr hp
  p.kerᗮ.subtypeL.comp <|
    (p.orthogonalKerEquivRange (htop ▸ isClosed_univ)).symm.toContinuousLinearMap.comp <|
      (Submodule.topContEquiv.symm.trans
        (ContinuousLinearEquiv.ofEq (⊤ : Submodule 𝕜 E₂) p.range htop.symm)).toContinuousLinearMap

/-- `orthogonalRightInverse` is a right inverse of `p`. -/
lemma orthogonalRightInverse_rightInverse (hp : Function.Surjective p) :
    Function.RightInverse (orthogonalRightInverse hp) p := fun _ ↦ by
  rw [orthogonalRightInverse, comp_apply, comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearEquiv.coe_coe, orthogonalKerEquivRange_symm_apply]; rfl

/-- Applying `p` to `orthogonalRightInverse hp y` recovers `y`. -/
@[simp]
lemma apply_orthogonalRightInverse (hp : Function.Surjective p) (y : E₂) :
    p (orthogonalRightInverse hp y) = y := orthogonalRightInverse_rightInverse hp y

/-- `orthogonalRightInverse` takes values in `(ker p)ᗮ`. -/
lemma orthogonalRightInverse_mem_orthogonal (hp : Function.Surjective p) (y : E₂) :
    orthogonalRightInverse hp y ∈ p.kerᗮ := Subtype.prop _

/-- Every continuous linear surjection from a Hilbert space onto a Banach space admits a continuous
right inverse. -/
theorem hasRightInverse_of_surjective_of_innerProductSpace (hp : Function.Surjective p) :
    p.HasRightInverse := ⟨orthogonalRightInverse hp, orthogonalRightInverse_rightInverse hp⟩

section Split

variable (hi : Function.Injective i) (hip : Function.Exact i p) (hp : Function.Surjective p)

/-- The orthogonal left inverse of `i` annihilates the orthogonal right inverse of `p`. -/
@[simp]
lemma orthogonalLeftInverse_comp_orthogonalRightInverse :
    (orthogonalLeftInverse hi hip).comp (orthogonalRightInverse hp) = 0 :=
  ext fun y ↦ orthogonalLeftInverse_eq_zero_of_mem_orthogonal hi hip
    (orthogonalRightInverse_mem_orthogonal hp y)

/-- The orthogonal splittings decompose the identity on `E₁` as `i ∘ r + s ∘ p = id`. -/
lemma comp_orthogonalLeftInverse_add_orthogonalRightInverse_comp :
    i.comp (orthogonalLeftInverse hi hip) + (orthogonalRightInverse hp).comp p =
      ContinuousLinearMap.id 𝕜 E₁ := by
  ext x
  let _ : CompleteSpace p.ker := p.isClosed_ker.completeSpace_coe
  have hker : x - orthogonalRightInverse hp (p x) ∈ p.ker := by
    rw [LinearMap.mem_ker, coe_coe, map_sub, apply_orthogonalRightInverse, sub_self]
  have hproj : p.ker.orthogonalProjectionOnto x = ⟨x - orthogonalRightInverse hp (p x), hker⟩ := by
    conv_lhs => rw [← sub_add_cancel x (orthogonalRightInverse hp (p x))]
    rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, hker⟩,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
        (orthogonalRightInverse_mem_orthogonal hp (p x)), add_zero]
  have hi_eq : i (orthogonalLeftInverse hi hip x) = x - orthogonalRightInverse hp (p x) := by
    change i ((exactEquivKer hi hip).symm (p.ker.orthogonalProjectionOnto x)) = _
    rw [hproj, apply_exactEquivKer_symm hi hip]
  simp only [add_apply, comp_apply, id_apply, hi_eq, sub_add_cancel]

/-- A short exact sequence `0 → E₀ --i--> E₁ --p--> E₂ → 0` of Banach spaces with `E₁` Hilbert
splits topologically as `E₁ ≃L[𝕜] E₀ × E₂`. -/
noncomputable def orthogonalSplitEquiv : E₁ ≃L[𝕜] E₀ × E₂ :=
  ContinuousLinearEquiv.equivOfInverse
    ((orthogonalLeftInverse hi hip).prod p) (i.coprod (orthogonalRightInverse hp))
    (fun x ↦ by
      have h := congrArg (fun f : E₁ →L[𝕜] E₁ ↦ f x)
        (comp_orthogonalLeftInverse_add_orthogonalRightInverse_comp hi hip hp)
      simpa [add_apply, comp_apply, id_apply] using h)
    (fun ⟨x₀, x₂⟩ ↦ by
      ext
      · simp [orthogonalLeftInverse_eq_zero_of_mem_orthogonal hi hip
          (orthogonalRightInverse_mem_orthogonal hp x₂)]
      · simp [hip.apply_apply_eq_zero x₀])

/-- Evaluating `orthogonalSplitEquiv` gives `(r x, p x)`. -/
@[simp]
lemma orthogonalSplitEquiv_apply (x : E₁) :
    orthogonalSplitEquiv hi hip hp x = (orthogonalLeftInverse hi hip x, p x) := (rfl)

/-- Evaluating the inverse of `orthogonalSplitEquiv` gives `i x₀ + s x₂`. -/
@[simp]
lemma orthogonalSplitEquiv_symm_apply (z : E₀ × E₂) :
    (orthogonalSplitEquiv hi hip hp).symm z = i z.1 + orthogonalRightInverse hp z.2 := (rfl)

end Split

end HilbertRightInverse

section HilbertSnake

variable {𝕜 E₀ E₁ E₂ F₀ F₁ F₂ : Type*} [RCLike 𝕜]
  [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀] [CompleteSpace F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
  [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂] [T1Space F₂]

/-- Canonical continuous snake connecting map `ker T₂ →L[𝕜] (F₀ ⧸ range T₀)` for a diagram whose
middle spaces `E₁`, `F₁` are Hilbert spaces (with `E₂`, `F₀` Banach). -/
noncomputable def hilbertSnakeConnectingL
    {p : E₁ →L[𝕜] E₂} {j : F₀ →L[𝕜] F₁} {q : F₁ →L[𝕜] F₂}
    (T₀ : E₀ →L[𝕜] F₀) (T₁ : E₁ →L[𝕜] F₁) (T₂ : E₂ →L[𝕜] F₂)
    (hp : Function.Surjective p) (hj : Function.Injective j) (hjq : Function.Exact j q) :
    T₂.ker →L[𝕜] (F₀ ⧸ T₀.range) :=
  snakeConnectingL T₀ T₁ T₂ (orthogonalRightInverse hp) (orthogonalLeftInverse hj hjq)

/-- `hilbertSnakeConnectingL` agrees with `snakeConnectingL` for any continuous splittings. -/
theorem hilbertSnakeConnectingL_eq_snakeConnectingL
    {i : E₀ →L[𝕜] E₁} {p : E₁ →L[𝕜] E₂} {j : F₀ →L[𝕜] F₁} {q : F₁ →L[𝕜] F₂}
    {T₀ : E₀ →L[𝕜] F₀} {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂}
    (hip : Function.Exact i p) (hp : Function.Surjective p)
    (hj : Function.Injective j) (hjq : Function.Exact j q)
    (h₁ : j ∘L T₀ = T₁ ∘L i) (h₂ : q ∘L T₁ = T₂ ∘L p)
    {s : E₂ →L[𝕜] E₁} (hs : Function.RightInverse s p)
    {r : F₁ →L[𝕜] F₀} (hr : Function.LeftInverse r j) :
    hilbertSnakeConnectingL T₀ T₁ T₂ hp hj hjq = snakeConnectingL T₀ T₁ T₂ s r :=
  snakeConnectingL_eq_of_rightInverse_leftInverse hip hj hjq h₁ h₂
    (orthogonalRightInverse_rightInverse hp) hs (orthogonalLeftInverse_leftInverse hj hjq) hr

end HilbertSnake

end TopologicalSplitting

/-! ### Two-out-of-three Fredholm snake theorems and index additivity -/

section FredholmSnake

section IndexAdditivity

variable {𝕜 E₀ E₁ E₂ F₀ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₁] [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
  [AddCommGroup F₀] [Module 𝕜 F₀] [TopologicalSpace F₀] [AddCommGroup F₁] [Module 𝕜 F₁]
  [TopologicalSpace F₁] [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂]
  {i : E₀ →L[𝕜] E₁} {p : E₁ →L[𝕜] E₂} {j : F₀ →L[𝕜] F₁} {q : F₁ →L[𝕜] F₂}
  {T₀ : E₀ →L[𝕜] F₀} {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂}
  (hi : Function.Injective i) (hip : Function.Exact i p) (hp : Function.Surjective p)
  (hj : Function.Injective j) (hjq : Function.Exact j q) (hq : Function.Surjective q)
  (h₁ : j ∘L T₀ = T₁ ∘L i) (h₂ : q ∘L T₁ = T₂ ∘L p)

include hi hip hp hj hjq hq h₁ h₂

/-- **Index additivity along a short exact sequence** when the outer two maps are Fredholm. No
completeness or topological splitting is needed. -/
theorem index_eq_add_of_exact_of_isFredholm_left_right
    (hT₀ : T₀.IsFredholm) (hT₂ : T₂.IsFredholm) : T₁.index = T₀.index + T₂.index := by
  have := hT₀.finite_ker; have := hT₀.finite_coker
  have := hT₂.finite_ker; have := hT₂.finite_coker
  have ⟨_, _⟩ := LinearMap.finiteDimensional_ker_coker_middle_of_left_right
    hip hp hj hjq (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)
  simpa only [index_def] using LinearMap.index_eq_add_of_exact hi hip hp hj hjq hq
    (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)

/-- **Index additivity along a short exact sequence** when the middle and right maps are
Fredholm. -/
theorem index_eq_add_of_exact_of_isFredholm_middle_right
    (hT₁ : T₁.IsFredholm) (hT₂ : T₂.IsFredholm) : T₁.index = T₀.index + T₂.index := by
  have := hT₁.finite_ker; have := hT₁.finite_coker; have := hT₂.finite_ker
  have := (LinearMap.finiteDimensional_ker_coker_left_of_middle_right
    hi hip hp hj hjq (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)).2
  simpa only [index_def] using LinearMap.index_eq_add_of_exact hi hip hp hj hjq hq
    (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)

/-- **Index additivity along a short exact sequence** when the left and middle maps are
Fredholm. -/
theorem index_eq_add_of_exact_of_isFredholm_left_middle
    (hT₀ : T₀.IsFredholm) (hT₁ : T₁.IsFredholm) : T₁.index = T₀.index + T₂.index := by
  have := hT₀.finite_coker; have := hT₁.finite_ker; have := hT₁.finite_coker
  have := (LinearMap.finiteDimensional_ker_coker_right_of_left_middle
    hip hp hj hjq hq (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)).1
  simpa only [index_def] using LinearMap.index_eq_add_of_exact hi hip hp hj hjq hq
    (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)

end IndexAdditivity

section BanachTwoOfThree

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]

/-- **Two-out-of-three for Fredholm operators (middle from outer)**: if `T₀` and `T₂` are Fredholm
and the middle spaces `E₁`, `F₁` are Banach, then `T₁` is Fredholm. -/
theorem isFredholm_middle_of_left_right {E₀ E₁ E₂ F₀ F₁ F₂ : Type*}
    [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
    [AddCommGroup F₀] [Module 𝕜 F₀] [TopologicalSpace F₀]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [CompleteSpace F₁]
    [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂]
    {i : E₀ →L[𝕜] E₁} {p : E₁ →L[𝕜] E₂} {j : F₀ →L[𝕜] F₁} {q : F₁ →L[𝕜] F₂}
    {T₀ : E₀ →L[𝕜] F₀} {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂}
    (hip : Function.Exact i p) (hp : Function.Surjective p)
    (hj : Function.Injective j) (hjq : Function.Exact j q)
    (h₁ : j ∘L T₀ = T₁ ∘L i) (h₂ : q ∘L T₁ = T₂ ∘L p)
    (hT₀ : T₀.IsFredholm) (hT₂ : T₂.IsFredholm) : T₁.IsFredholm := by
  have := hT₀.finite_ker; have := hT₀.finite_coker
  have := hT₂.finite_ker; have := hT₂.finite_coker
  obtain ⟨hker, hcoker⟩ := LinearMap.finiteDimensional_ker_coker_middle_of_left_right
    hip hp hj hjq (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)
  exact IsFredholm.of_finite_ker_coker T₁ hker hcoker

/-- **Two-out-of-three for Fredholm operators (left from middle and right)**: if `i` is injective,
`T₁` and `T₂` are Fredholm, and `E₀`, `F₀` are Banach, then `T₀` is Fredholm. -/
theorem isFredholm_left_of_middle_right {E₀ E₁ E₂ F₀ F₁ F₂ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [CompleteSpace E₀]
    [AddCommGroup E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
    [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀] [CompleteSpace F₀]
    [AddCommGroup F₁] [Module 𝕜 F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂]
    {i : E₀ →L[𝕜] E₁} {p : E₁ →L[𝕜] E₂} {j : F₀ →L[𝕜] F₁} {q : F₁ →L[𝕜] F₂}
    {T₀ : E₀ →L[𝕜] F₀} {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂}
    (hi : Function.Injective i) (hip : Function.Exact i p) (hp : Function.Surjective p)
    (hj : Function.Injective j) (hjq : Function.Exact j q)
    (h₁ : j ∘L T₀ = T₁ ∘L i) (h₂ : q ∘L T₁ = T₂ ∘L p)
    (hT₁ : T₁.IsFredholm) (hT₂ : T₂.IsFredholm) : T₀.IsFredholm := by
  have := hT₁.finite_ker; have := hT₁.finite_coker; have := hT₂.finite_ker
  obtain ⟨hker, hcoker⟩ := LinearMap.finiteDimensional_ker_coker_left_of_middle_right
    hi hip hp hj hjq (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)
  exact IsFredholm.of_finite_ker_coker T₀ hker hcoker

/-- **Two-out-of-three for Fredholm operators (right from left and middle)**: if `q` is surjective,
`T₀` and `T₁` are Fredholm, and `E₂`, `F₂` are Banach, then `T₂` is Fredholm. -/
theorem isFredholm_right_of_left_middle {E₀ E₁ E₂ F₀ F₁ F₂ : Type*}
    [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
    [AddCommGroup E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [AddCommGroup F₀] [Module 𝕜 F₀] [TopologicalSpace F₀]
    [AddCommGroup F₁] [Module 𝕜 F₁] [TopologicalSpace F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
    {i : E₀ →L[𝕜] E₁} {p : E₁ →L[𝕜] E₂} {j : F₀ →L[𝕜] F₁} {q : F₁ →L[𝕜] F₂}
    {T₀ : E₀ →L[𝕜] F₀} {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂}
    (hip : Function.Exact i p) (hp : Function.Surjective p)
    (hj : Function.Injective j) (hjq : Function.Exact j q) (hq : Function.Surjective q)
    (h₁ : j ∘L T₀ = T₁ ∘L i) (h₂ : q ∘L T₁ = T₂ ∘L p)
    (hT₀ : T₀.IsFredholm) (hT₁ : T₁.IsFredholm) : T₂.IsFredholm := by
  have := hT₀.finite_coker; have := hT₁.finite_ker; have := hT₁.finite_coker
  obtain ⟨hker, hcoker⟩ := LinearMap.finiteDimensional_ker_coker_right_of_left_middle
    hip hp hj hjq hq (congrArg toLinearMap h₁) (congrArg toLinearMap h₂)
  exact IsFredholm.of_finite_ker_coker T₂ hker hcoker

end BanachTwoOfThree

end FredholmSnake

end ContinuousLinearMap
