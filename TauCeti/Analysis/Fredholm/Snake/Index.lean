/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Analysis.Fredholm.Snake.Basic

import TauCeti.LinearAlgebra.Exact

/-!
# Index additivity and two-out-of-three for Fredholm snake sequences

From the six-term kernel--cokernel snake sequence of `TauCeti.Analysis.Fredholm.Snake.Basic`,
finiteness of any two of `(ker T₁, coker T₁)`, `(ker T₂, coker T₂)` and `(ker T₃, coker T₃)`
forces finiteness of the third, and the alternating dimension sum yields index additivity
`T₂.index = T₁.index + T₃.index`. Between Banach spaces over an `IsRCLikeNormedField`,
`ContinuousLinearMap.IsFredholm.of_finite_ker_coker` then supplies the two-out-of-three property
for Fredholm operators in a short exact diagram.

## Main results

* `TauCeti.finrank_sub_finrank_eq_add_of_exact_six`: Euler characteristic of a six-term exact
  sequence of vector spaces.
* `TauCeti.finiteDimensional_ker_coker_middle_of_shortExact`, `right_of_shortExact`,
  `left_of_shortExact`: algebraic two-out-of-three for finite-dimensional kernels and cokernels.
* `LinearMap.index_eq_add_of_shortExact`: algebraic index additivity in a short exact diagram.
* `ContinuousLinearMap.index_eq_add_of_shortExact_left_right`, `left_middle`, `middle_right`:
  TVS index additivity `T₂.index = T₁.index + T₃.index`.
* `ContinuousLinearMap.IsFredholm.of_shortExact_middle`, `of_shortExact_right`,
  `of_shortExact_left`: two-out-of-three for Banach Fredholm operators.
-/

public section

open Function Module

/-! ### Exact six-term sequences: two-out-of-three finiteness and index additivity -/

namespace TauCeti

section AlgebraicIndex

variable {𝕜 : Type*} [DivisionRing 𝕜]
variable {K₁ K₂ K₃ C₁ C₂ C₃ : Type*}
variable [AddCommGroup K₁] [Module 𝕜 K₁] [AddCommGroup K₂] [Module 𝕜 K₂]
  [AddCommGroup K₃] [Module 𝕜 K₃]
variable [AddCommGroup C₁] [Module 𝕜 C₁] [AddCommGroup C₂] [Module 𝕜 C₂]
  [AddCommGroup C₃] [Module 𝕜 C₃]

/-- **Euler characteristic of a six-term exact sequence:** for an exact sequence
`0 → K₁ → K₂ → K₃ → C₁ → C₂ → C₃ → 0` of vector spaces with outer terms `K₁, K₃, C₁, C₃`
finite-dimensional, `dim K₂ - dim C₂ = (dim K₁ - dim C₁) + (dim K₃ - dim C₃)`. -/
theorem finrank_sub_finrank_eq_add_of_exact_six
    {a : K₁ →ₗ[𝕜] K₂} {b : K₂ →ₗ[𝕜] K₃} {δ : K₃ →ₗ[𝕜] C₁}
    {c : C₁ →ₗ[𝕜] C₂} {d : C₂ →ₗ[𝕜] C₃}
    (ha : Injective a) (hab : Exact a b) (hbδ : Exact b δ)
    (hδc : Exact δ c) (hcd : Exact c d) (hd : Surjective d)
    [FiniteDimensional 𝕜 K₁] [FiniteDimensional 𝕜 K₃]
    [FiniteDimensional 𝕜 C₁] [FiniteDimensional 𝕜 C₃] :
    (finrank 𝕜 K₂ : ℤ) - finrank 𝕜 C₂ =
      ((finrank 𝕜 K₁ : ℤ) - finrank 𝕜 C₁) + ((finrank 𝕜 K₃ : ℤ) - finrank 𝕜 C₃) := by
  have := finiteDimensional_of_exact hab
  have := finiteDimensional_of_exact hcd
  have h1 : finrank 𝕜 K₁ = finrank 𝕜 a.range := (LinearMap.finrank_range_of_inj ha).symm
  have h2 := a.finrank_eq_finrank_range_add_finrank_range_of_exact b hab
  have h3 := b.finrank_eq_finrank_range_add_finrank_range_of_exact δ hbδ
  have h4 := δ.finrank_eq_finrank_range_add_finrank_range_of_exact c hδc
  have h5 := c.finrank_eq_finrank_range_add_finrank_range_of_exact d hcd
  have h6 : finrank 𝕜 C₃ = finrank 𝕜 d.range := by
    rw [LinearMap.range_eq_top.2 hd, finrank_top]
  omega

section ShortExact

variable {i : K₁ →ₗ[𝕜] K₂} {p : K₂ →ₗ[𝕜] K₃} {j : C₁ →ₗ[𝕜] C₂} {q : C₂ →ₗ[𝕜] C₃}
variable {T₁ : K₁ →ₗ[𝕜] C₁} {T₂ : K₂ →ₗ[𝕜] C₂} {T₃ : K₃ →ₗ[𝕜] C₃}

/-- Algebraic two-out-of-three (left and right imply middle): if `T₁` and `T₃` have
finite-dimensional kernels and cokernels, so does `T₂`. -/
theorem finiteDimensional_ker_coker_middle_of_shortExact
    (hip : Exact i p) (hp : Surjective p) (hj : Injective j) (hjq : Exact j q)
    (hcomm₁ : T₂ ∘ₗ i = j ∘ₗ T₁) (hcomm₂ : T₃ ∘ₗ p = q ∘ₗ T₂)
    [FiniteDimensional 𝕜 T₁.ker] [FiniteDimensional 𝕜 (C₁ ⧸ T₁.range)]
    [FiniteDimensional 𝕜 T₃.ker] [FiniteDimensional 𝕜 (C₃ ⧸ T₃.range)] :
    FiniteDimensional 𝕜 T₂.ker ∧ FiniteDimensional 𝕜 (C₂ ⧸ T₂.range) :=
  ⟨finiteDimensional_of_exact (exact_kerMapOfComm hip hj hcomm₁ hcomm₂),
    finiteDimensional_of_exact (exact_cokerMapOfComm hp hjq hcomm₁ hcomm₂)⟩

/-- Algebraic two-out-of-three (left and middle imply right): if `T₁` and `T₂` have
finite-dimensional kernels and cokernels, so does `T₃`. -/
theorem finiteDimensional_ker_coker_right_of_shortExact
    (hip : Exact i p) (hp : Surjective p) (hj : Injective j) (hjq : Exact j q) (hq : Surjective q)
    (hcomm₁ : T₂ ∘ₗ i = j ∘ₗ T₁) (hcomm₂ : T₃ ∘ₗ p = q ∘ₗ T₂)
    [FiniteDimensional 𝕜 (C₁ ⧸ T₁.range)]
    [FiniteDimensional 𝕜 T₂.ker] [FiniteDimensional 𝕜 (C₂ ⧸ T₂.range)] :
    FiniteDimensional 𝕜 T₃.ker ∧ FiniteDimensional 𝕜 (C₃ ⧸ T₃.range) :=
  ⟨finiteDimensional_of_exact (exact_kerMapOfComm_snakeDelta hip hp hjq hj hcomm₁ hcomm₂),
    Module.Finite.of_surjective _ (surjective_cokerMapOfComm hcomm₂ hq)⟩

/-- Algebraic two-out-of-three (middle and right imply left): if `T₂` and `T₃` have
finite-dimensional kernels and cokernels, so does `T₁`. -/
theorem finiteDimensional_ker_coker_left_of_shortExact
    (hi : Injective i) (hip : Exact i p) (hp : Surjective p) (hj : Injective j) (hjq : Exact j q)
    (hcomm₁ : T₂ ∘ₗ i = j ∘ₗ T₁) (hcomm₂ : T₃ ∘ₗ p = q ∘ₗ T₂)
    [FiniteDimensional 𝕜 T₂.ker] [FiniteDimensional 𝕜 (C₂ ⧸ T₂.range)]
    [FiniteDimensional 𝕜 T₃.ker] :
    FiniteDimensional 𝕜 T₁.ker ∧ FiniteDimensional 𝕜 (C₁ ⧸ T₁.range) :=
  ⟨Module.Finite.of_injective _ (injective_kerMapOfComm hcomm₁ hi),
    finiteDimensional_of_exact (exact_snakeDelta_cokerMapOfComm hip hp hjq hj hcomm₁ hcomm₂)⟩

end ShortExact

/-- **Algebraic index additivity in a short exact diagram:** if `T₁` and `T₃` have
finite-dimensional kernels and cokernels, then `T₂.index = T₁.index + T₃.index`. -/
theorem _root_.LinearMap.index_eq_add_of_shortExact
    (T₂ : K₂ →ₗ[𝕜] C₂) {i : K₁ →ₗ[𝕜] K₂} {p : K₂ →ₗ[𝕜] K₃}
    {j : C₁ →ₗ[𝕜] C₂} {q : C₂ →ₗ[𝕜] C₃} {T₁ : K₁ →ₗ[𝕜] C₁} {T₃ : K₃ →ₗ[𝕜] C₃}
    (hi : Injective i) (hip : Exact i p) (hp : Surjective p)
    (hj : Injective j) (hjq : Exact j q) (hq : Surjective q)
    (hcomm₁ : T₂ ∘ₗ i = j ∘ₗ T₁) (hcomm₂ : T₃ ∘ₗ p = q ∘ₗ T₂)
    [FiniteDimensional 𝕜 T₁.ker] [FiniteDimensional 𝕜 (C₁ ⧸ T₁.range)]
    [FiniteDimensional 𝕜 T₃.ker] [FiniteDimensional 𝕜 (C₃ ⧸ T₃.range)] :
    T₂.index = T₁.index + T₃.index := by
  simpa only [LinearMap.index_eq_finrank_sub] using
    finrank_sub_finrank_eq_add_of_exact_six
      (injective_kerMapOfComm hcomm₁ hi)
      (exact_kerMapOfComm hip hj hcomm₁ hcomm₂)
      (exact_kerMapOfComm_snakeDelta hip hp hjq hj hcomm₁ hcomm₂)
      (exact_snakeDelta_cokerMapOfComm hip hp hjq hj hcomm₁ hcomm₂)
      (exact_cokerMapOfComm hp hjq hcomm₁ hcomm₂)
      (surjective_cokerMapOfComm hcomm₂ hq)

end AlgebraicIndex

end TauCeti

/-! ### Two-out-of-three for Fredholm operators and index additivity -/

namespace ContinuousLinearMap

section FredholmSnakeTVS

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}
variable [AddCommGroup E₁] [AddCommGroup E₂] [AddCommGroup E₃]
variable [AddCommGroup F₁] [AddCommGroup F₂] [AddCommGroup F₃]
variable [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace E₃]
variable [TopologicalSpace F₁] [TopologicalSpace F₂] [TopologicalSpace F₃]
variable [Module 𝕜 E₁] [Module 𝕜 E₂] [Module 𝕜 E₃] [Module 𝕜 F₁] [Module 𝕜 F₂] [Module 𝕜 F₃]
variable {i : E₁ →L[𝕜] E₂} {p : E₂ →L[𝕜] E₃} {j : F₁ →L[𝕜] F₂} {q : F₂ →L[𝕜] F₃}
variable {T₁ : E₁ →L[𝕜] F₁} {T₃ : E₃ →L[𝕜] F₃}

/-- **Index additivity in a short exact diagram (left and right Fredholm):** if `T₁` and `T₃` are
Fredholm, then `T₂.index = T₁.index + T₃.index` (no completeness needed). -/
theorem index_eq_add_of_shortExact_left_right (T₂ : E₂ →L[𝕜] F₂)
    (hi : Injective i) (hip : Exact i p) (hp : Surjective p)
    (hj : Injective j) (hjq : Exact j q) (hq : Surjective q)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂)
    (hT₁ : T₁.IsFredholm) (hT₃ : T₃.IsFredholm) :
    T₂.index = T₁.index + T₃.index := by
  have := hT₁.finite_ker; have := hT₁.finite_coker
  have := hT₃.finite_ker; have := hT₃.finite_coker
  rw [index_def, index_def, index_def]
  exact LinearMap.index_eq_add_of_shortExact T₂.toLinearMap hi hip hp hj hjq hq
    (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
    (congrArg ContinuousLinearMap.toLinearMap hcomm₂)

/-- **Index additivity in a short exact diagram (left and middle Fredholm):** if `T₁` and `T₂` are
Fredholm, then `T₂.index = T₁.index + T₃.index`. -/
theorem index_eq_add_of_shortExact_left_middle (T₂ : E₂ →L[𝕜] F₂)
    (hi : Injective i) (hip : Exact i p) (hp : Surjective p)
    (hj : Injective j) (hjq : Exact j q) (hq : Surjective q)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂)
    (hT₁ : T₁.IsFredholm) (hT₂ : T₂.IsFredholm) :
    T₂.index = T₁.index + T₃.index := by
  have := hT₁.finite_ker; have := hT₁.finite_coker
  have := hT₂.finite_ker; have := hT₂.finite_coker
  have hright := TauCeti.finiteDimensional_ker_coker_right_of_shortExact hip hp hj hjq hq
    (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
    (congrArg ContinuousLinearMap.toLinearMap hcomm₂)
  have := hright.1; have := hright.2
  rw [index_def, index_def, index_def]
  exact LinearMap.index_eq_add_of_shortExact T₂.toLinearMap hi hip hp hj hjq hq
    (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
    (congrArg ContinuousLinearMap.toLinearMap hcomm₂)

/-- **Index additivity in a short exact diagram (middle and right Fredholm):** if `T₂` and `T₃`
are Fredholm, then `T₂.index = T₁.index + T₃.index`. -/
theorem index_eq_add_of_shortExact_middle_right (T₂ : E₂ →L[𝕜] F₂)
    (hi : Injective i) (hip : Exact i p) (hp : Surjective p)
    (hj : Injective j) (hjq : Exact j q) (hq : Surjective q)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂)
    (hT₂ : T₂.IsFredholm) (hT₃ : T₃.IsFredholm) :
    T₂.index = T₁.index + T₃.index := by
  have := hT₂.finite_ker; have := hT₂.finite_coker
  have := hT₃.finite_ker; have := hT₃.finite_coker
  have hleft := TauCeti.finiteDimensional_ker_coker_left_of_shortExact hi hip hp hj hjq
    (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
    (congrArg ContinuousLinearMap.toLinearMap hcomm₂)
  have := hleft.1; have := hleft.2
  rw [index_def, index_def, index_def]
  exact LinearMap.index_eq_add_of_shortExact T₂.toLinearMap hi hip hp hj hjq hq
    (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
    (congrArg ContinuousLinearMap.toLinearMap hcomm₂)

end FredholmSnakeTVS

section FredholmSnakeBanach

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}

/-- **Two-out-of-three for Fredholm operators (middle):** if `T₁` and `T₃` are Fredholm and
`E₂, F₂` are Banach spaces over an `IsRCLikeNormedField`, then `T₂` is Fredholm. -/
theorem IsFredholm.of_shortExact_middle
    [AddCommGroup E₁] [TopologicalSpace E₁] [Module 𝕜 E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [AddCommGroup E₃] [TopologicalSpace E₃] [Module 𝕜 E₃]
    [AddCommGroup F₁] [TopologicalSpace F₁] [Module 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
    [AddCommGroup F₃] [TopologicalSpace F₃] [Module 𝕜 F₃]
    {i : E₁ →L[𝕜] E₂} {p : E₂ →L[𝕜] E₃} {j : F₁ →L[𝕜] F₂} {q : F₂ →L[𝕜] F₃}
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    (hT₁ : T₁.IsFredholm) (hT₃ : T₃.IsFredholm)
    (hip : Exact i p) (hp : Surjective p) (hj : Injective j) (hjq : Exact j q)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂) :
    T₂.IsFredholm := by
  have := hT₁.finite_ker; have := hT₁.finite_coker
  have := hT₃.finite_ker; have := hT₃.finite_coker
  have hmid := TauCeti.finiteDimensional_ker_coker_middle_of_shortExact hip hp hj hjq
    (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
    (congrArg ContinuousLinearMap.toLinearMap hcomm₂)
  exact .of_finite_ker_coker T₂ hmid.1 hmid.2

/-- **Two-out-of-three for Fredholm operators (right):** if `T₁` and `T₂` are Fredholm and
`E₃, F₃` are Banach spaces, then `T₃` is Fredholm. -/
theorem IsFredholm.of_shortExact_right
    [AddCommGroup E₁] [TopologicalSpace E₁] [Module 𝕜 E₁]
    [AddCommGroup E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
    [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [CompleteSpace E₃]
    [AddCommGroup F₁] [TopologicalSpace F₁] [Module 𝕜 F₁]
    [AddCommGroup F₂] [TopologicalSpace F₂] [Module 𝕜 F₂]
    [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [CompleteSpace F₃]
    {i : E₁ →L[𝕜] E₂} {p : E₂ →L[𝕜] E₃} {j : F₁ →L[𝕜] F₂} {q : F₂ →L[𝕜] F₃}
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    (hT₁ : T₁.IsFredholm) (hT₂ : T₂.IsFredholm)
    (hip : Exact i p) (hp : Surjective p)
    (hj : Injective j) (hjq : Exact j q) (hq : Surjective q)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂) :
    T₃.IsFredholm := by
  have := hT₁.finite_coker; have := hT₂.finite_ker; have := hT₂.finite_coker
  have hright := TauCeti.finiteDimensional_ker_coker_right_of_shortExact hip hp hj hjq hq
    (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
    (congrArg ContinuousLinearMap.toLinearMap hcomm₂)
  exact .of_finite_ker_coker T₃ hright.1 hright.2

/-- **Two-out-of-three for Fredholm operators (left):** if `T₂` and `T₃` are Fredholm and
`E₁, F₁` are Banach spaces, then `T₁` is Fredholm. -/
theorem IsFredholm.of_shortExact_left
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    [AddCommGroup E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
    [AddCommGroup E₃] [TopologicalSpace E₃] [Module 𝕜 E₃]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [CompleteSpace F₁]
    [AddCommGroup F₂] [TopologicalSpace F₂] [Module 𝕜 F₂]
    [AddCommGroup F₃] [TopologicalSpace F₃] [Module 𝕜 F₃]
    {i : E₁ →L[𝕜] E₂} {p : E₂ →L[𝕜] E₃} {j : F₁ →L[𝕜] F₂} {q : F₂ →L[𝕜] F₃}
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    (hT₂ : T₂.IsFredholm) (hT₃ : T₃.IsFredholm)
    (hi : Injective i) (hip : Exact i p) (hp : Surjective p)
    (hj : Injective j) (hjq : Exact j q)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂) :
    T₁.IsFredholm := by
  have := hT₂.finite_ker; have := hT₂.finite_coker; have := hT₃.finite_ker
  have hleft := TauCeti.finiteDimensional_ker_coker_left_of_shortExact hi hip hp hj hjq
    (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
    (congrArg ContinuousLinearMap.toLinearMap hcomm₂)
  exact .of_finite_ker_coker T₁ hleft.1 hleft.2

end FredholmSnakeBanach

end ContinuousLinearMap
