/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.LinearAlgebra.Exact

import Mathlib.Algebra.Module.ULift
import Mathlib.Tactic.Abel
import TauCeti.Analysis.Fredholm.Prod
import TauCeti.Topology.Algebra.Module.Complement

/-!
# Snake sequences of Fredholm operators

Given a commuting diagram of continuous linear maps between two short exact sequences of
topological vector spaces,
```text
0 ⟶ E₁ —i→ E₂ —p→ E₃ ⟶ 0
     │      │      │
     T₁     T₂     T₃
     ↓      ↓      ↓
0 ⟶ F₁ —j→ F₂ —q→ F₃ ⟶ 0
```
the categorical snake lemma (`CategoryTheory.ShortComplex.SnakeInput.snake_lemma`) on `ModuleCat`
produces the exact six-term kernel--cokernel sequence
```text
0 ⟶ ker T₁ ⟶ ker T₂ ⟶ ker T₃ —δ→ F₁ ⧸ range T₁ ⟶ F₂ ⧸ range T₂ ⟶ F₃ ⧸ range T₃ ⟶ 0.
```

The four horizontal maps on kernels and cokernels are always continuous. Whenever `p` admits a
continuous linear right inverse `s` and `j` admits a continuous linear left inverse `r`, the
connecting map `δ` equals `mkQL ∘ r ∘ T₂ ∘ s ∘ subtypeL`, hence is continuous and independent of
the chosen splittings. Between Banach spaces, a short exact sequence splits topologically whenever
`ker p` is topologically complemented; between Hilbert spaces every closed subspace is complemented
by its orthogonal complement, so topological splitting and continuity of `δ` are automatic.

From the six-term exact sequence, finiteness of any two of `(ker T₁, coker T₁)`,
`(ker T₂, coker T₂)` and `(ker T₃, coker T₃)` forces finiteness of the third, and the alternating
dimension sum yields `T₂.index = T₁.index + T₃.index`. Between Banach spaces over an
`IsRCLikeNormedField`, `ContinuousLinearMap.IsFredholm.of_finite_ker_coker` then yields the
two-out-of-three property for Fredholm operators in a short exact diagram.

Specializing to `0 → E₁ → E₁ × E₂ → E₂ → 0` treats upper-triangular block operators
`upperTriangular A B D (x, y) = (A x + B y, D y)`. Their connecting map is `y ↦ [B y]`, which is a
bijection whenever the block operator is bijective. Comparing with the explicit block parametrix
`upperTriangular PA (-(PA ∘ B ∘ PD)) PD` gives the `(A, D) ↦ M` direction in general TVSs, while
the snake lemma supplies the converse two-out-of-three directions `(M, D) ↦ A` and `(M, A) ↦ D`.

Finally, for composable operators `T : E →L[𝕜] F` and `S : F →L[𝕜] G`, the block operator
`upperTriangular T (-id) S : E × F →L[𝕜] F × G` is conjugate by triangular coordinate equivalences
to `(S ∘ T).prodMap (-id)`. Its snake sequence matches `LinearMap.kerCompToKer`,
`-LinearMap.kerToCoker` and `LinearMap.cokerToCokerComp`, recovering
`ContinuousLinearMap.IsFredholm.index_comp` and its two-out-of-three index variants.

## Main definitions

* `TauCeti.snakeInput`: a `CategoryTheory.ShortComplex.SnakeInput (ModuleCat 𝕜)` with concrete
  kernel and cokernel rows `L₀` and `L₃`.
* `TauCeti.snakeDelta`: the universe-polymorphic connecting map `T₃.ker →ₗ[𝕜] (F₁ ⧸ T₁.range)`.
* `TauCeti.snakeDeltaL`: the continuous connecting map `T₃.ker →L[𝕜] (F₁ ⧸ T₁.range)`.
* `ContinuousLinearMap.upperTriangular`: the upper-triangular block operator
  `(x, y) ↦ (A x + B y, D y)`.
* `ContinuousLinearMap.kerUpperTriangularNegIdEquiv`,
  `ContinuousLinearMap.cokerUpperTriangularNegIdEquiv`: identifications of the kernel and cokernel
  of `upperTriangular T (-id) S` with those of `S ∘L T`.

## Main results

* `TauCeti.snakeDelta_eq`, `TauCeti.continuous_snakeDelta`, `TauCeti.snakeDeltaL_eq_comp`:
  elementwise formula, continuity and splitting-independence of `δ`.
* `TauCeti.exists_topologicalSplitting_of_shortExact`,
  `TauCeti.exists_topologicalSplitting_of_shortExact_hilbert`: topological splitting of Banach
  (complemented kernel) and Hilbert short exact sequences.
* `ContinuousLinearMap.IsFredholm.of_shortExact_middle`, `of_shortExact_right`,
  `of_shortExact_left`: two-out-of-three for Banach Fredholm operators.
* `ContinuousLinearMap.index_eq_add_of_shortExact_left_right`, `left_middle`, `middle_right`:
  index additivity `T₂.index = T₁.index + T₃.index`.
* `ContinuousLinearMap.isQuasiInverse_upperTriangular`,
  `ContinuousLinearMap.isCompactOperator_upperTriangular_parametrix_left`, `parametrix_right`:
  explicit block quasi-inverse and compact-error parametrices.
* `ContinuousLinearMap.isFredholm_upperTriangular_neg_id_iff`,
  `ContinuousLinearMap.index_upperTriangular_neg_id`,
  `ContinuousLinearMap.IsFredholm.index_comp_of_left`, `index_comp_of_right`: comparison with
  `ContinuousLinearMap.IsFredholm.index_comp`.
-/

public section

open CategoryTheory CategoryTheory.Limits Function Module

noncomputable section

/-! ### Induced maps on kernels and cokernels, and categorical `SnakeInput` on `ModuleCat` -/

namespace TauCeti

section KerCokerMaps

variable {𝕜 : Type*} [Ring 𝕜]
variable {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}
variable [AddCommGroup E₁] [Module 𝕜 E₁] [AddCommGroup E₂] [Module 𝕜 E₂]
  [AddCommGroup E₃] [Module 𝕜 E₃]
variable [AddCommGroup F₁] [Module 𝕜 F₁] [AddCommGroup F₂] [Module 𝕜 F₂]
  [AddCommGroup F₃] [Module 𝕜 F₃]
variable {i : E₁ →ₗ[𝕜] E₂} {p : E₂ →ₗ[𝕜] E₃} {j : F₁ →ₗ[𝕜] F₂} {q : F₂ →ₗ[𝕜] F₃}
variable {T₁ : E₁ →ₗ[𝕜] F₁} {T₂ : E₂ →ₗ[𝕜] F₂} {T₃ : E₃ →ₗ[𝕜] F₃}

/-- The map induced on kernels `ker T₁ →ₗ[𝕜] ker T₂` by a commuting square `T₂ ∘ i = j ∘ T₁`. -/
def kerMapOfComm (hcomm : T₂ ∘ₗ i = j ∘ₗ T₁) : T₁.ker →ₗ[𝕜] T₂.ker :=
  i.restrict fun x hx ↦ by
    rw [LinearMap.mem_ker] at hx ⊢
    calc
      T₂ (i x) = (T₂ ∘ₗ i) x := rfl
      _ = j (T₁ x) := LinearMap.congr_fun hcomm x
      _ = 0 := by rw [hx, map_zero]

@[simp]
theorem coe_kerMapOfComm_apply (hcomm : T₂ ∘ₗ i = j ∘ₗ T₁) (x : T₁.ker) :
    (kerMapOfComm hcomm x : E₂) = i x := (rfl)

/-- If `i` is injective, the induced map `ker T₁ → ker T₂` is injective. -/
theorem injective_kerMapOfComm (hcomm : T₂ ∘ₗ i = j ∘ₗ T₁) (hi : Injective i) :
    Injective (kerMapOfComm hcomm) := fun _ _ hxy ↦
  Subtype.ext (hi (congrArg Subtype.val hxy))

/-- Exactness of `ker T₁ → ker T₂ → ker T₃` when `E₁ —i→ E₂ —p→ E₃` is exact and `j` is
injective. -/
theorem exact_kerMapOfComm (hip : Exact i p) (hj : Injective j)
    (hcomm₁ : T₂ ∘ₗ i = j ∘ₗ T₁) (hcomm₂ : T₃ ∘ₗ p = q ∘ₗ T₂) :
    Exact (kerMapOfComm hcomm₁) (kerMapOfComm hcomm₂) := by
  intro x
  refine ⟨fun hx ↦ ?_, fun ⟨a, ha⟩ ↦ ha ▸ Subtype.ext (hip.apply_apply_eq_zero a.1)⟩
  obtain ⟨a, ha⟩ := (hip x.1).1 (congrArg Subtype.val hx)
  refine ⟨⟨a, LinearMap.mem_ker.2 <| hj ?_⟩, Subtype.ext ha⟩
  calc
    j (T₁ a) = (T₂ ∘ₗ i) a := (LinearMap.congr_fun hcomm₁ a).symm
    _ = T₂ x.1 := congrArg T₂ ha
    _ = 0 := x.2
    _ = j 0 := (map_zero j).symm

/-- The map induced on cokernels `(F₁ ⧸ range T₁) →ₗ[𝕜] (F₂ ⧸ range T₂)` by a commuting square
`T₂ ∘ i = j ∘ T₁`. -/
def cokerMapOfComm (hcomm : T₂ ∘ₗ i = j ∘ₗ T₁) : (F₁ ⧸ T₁.range) →ₗ[𝕜] (F₂ ⧸ T₂.range) :=
  T₁.range.mapQ T₂.range j fun _ ⟨x, hx⟩ ↦
    ⟨i x, (LinearMap.congr_fun hcomm x).trans (congrArg j hx)⟩

@[simp]
theorem cokerMapOfComm_mk (hcomm : T₂ ∘ₗ i = j ∘ₗ T₁) (y : F₁) :
    cokerMapOfComm hcomm (Submodule.Quotient.mk y) = Submodule.Quotient.mk (j y) := (rfl)

/-- If `j` is surjective, the induced map `F₁ ⧸ range T₁ → F₂ ⧸ range T₂` is surjective. -/
theorem surjective_cokerMapOfComm (hcomm : T₂ ∘ₗ i = j ∘ₗ T₁) (hj : Surjective j) :
    Surjective (cokerMapOfComm hcomm) := by
  intro c
  induction c using Submodule.Quotient.induction_on with | H z =>
  obtain ⟨y, rfl⟩ := hj z
  exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- Exactness of `F₁ ⧸ range T₁ → F₂ ⧸ range T₂ → F₃ ⧸ range T₃` when `F₁ —j→ F₂ —q→ F₃` is exact
and `p` is surjective. -/
theorem exact_cokerMapOfComm (hp : Surjective p) (hjq : Exact j q)
    (hcomm₁ : T₂ ∘ₗ i = j ∘ₗ T₁) (hcomm₂ : T₃ ∘ₗ p = q ∘ₗ T₂) :
    Exact (cokerMapOfComm hcomm₁) (cokerMapOfComm hcomm₂) := by
  intro c
  induction c using Submodule.Quotient.induction_on with | H y =>
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).1 hy
    obtain ⟨w, rfl⟩ := hp z
    have hq0 : q (y - T₂ w) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hz.symm.trans (LinearMap.congr_fun hcomm₂ w)
    obtain ⟨v, hv⟩ := (hjq (y - T₂ w)).1 hq0
    refine ⟨Submodule.Quotient.mk v, ?_⟩
    rw [cokerMapOfComm_mk, Submodule.Quotient.eq]
    exact ⟨-w, by rw [map_neg, hv]; abel⟩
  · rintro ⟨c₁, hc₁⟩
    induction c₁ using Submodule.Quotient.induction_on with | H v =>
    rw [← hc₁, cokerMapOfComm_mk, cokerMapOfComm_mk, hjq.apply_apply_eq_zero v]
    rfl

end KerCokerMaps

section SnakeInput

universe u v

variable {𝕜 : Type u} [Ring 𝕜]
variable {E₁ E₂ E₃ F₁ F₂ F₃ : Type v}
variable [AddCommGroup E₁] [Module 𝕜 E₁] [AddCommGroup E₂] [Module 𝕜 E₂]
  [AddCommGroup E₃] [Module 𝕜 E₃]
variable [AddCommGroup F₁] [Module 𝕜 F₁] [AddCommGroup F₂] [Module 𝕜 F₂]
  [AddCommGroup F₃] [Module 𝕜 F₃]

-- Exposing the `SnakeInput` fields keeps `L₀.X₃` definitionally `T₃.ker` and `L₃.X₁`
-- definitionally `F₁ ⧸ T₁.range`, so consumers can apply `SnakeInput.δ` and
-- `SnakeInput.snake_lemma` directly without casts.
/-- The `CategoryTheory.ShortComplex.SnakeInput` in `ModuleCat.{v} 𝕜` attached to a commuting
diagram of linear maps between two exact rows, with `L₀` given concretely by the kernel submodules
and `L₃` given concretely by the cokernel quotients. -/
@[expose] def snakeInput {i : E₁ →ₗ[𝕜] E₂} {p : E₂ →ₗ[𝕜] E₃}
    {j : F₁ →ₗ[𝕜] F₂} {q : F₂ →ₗ[𝕜] F₃}
    {T₁ : E₁ →ₗ[𝕜] F₁} {T₂ : E₂ →ₗ[𝕜] F₂} {T₃ : E₃ →ₗ[𝕜] F₃}
    (hip : Exact i p) (hp : Surjective p) (hjq : Exact j q) (hj : Injective j)
    (hcomm₁ : T₂ ∘ₗ i = j ∘ₗ T₁) (hcomm₂ : T₃ ∘ₗ p = q ∘ₗ T₂) :
    ShortComplex.SnakeInput (ModuleCat.{v} 𝕜) where
  L₀ := ShortComplex.moduleCatMk (kerMapOfComm hcomm₁) (kerMapOfComm hcomm₂) <| by
    ext x
    exact hip.apply_apply_eq_zero x.1
  L₁ := ShortComplex.moduleCatMk i p hip.linearMap_comp_eq_zero
  L₂ := ShortComplex.moduleCatMk j q hjq.linearMap_comp_eq_zero
  L₃ := ShortComplex.moduleCatMk (cokerMapOfComm hcomm₁) (cokerMapOfComm hcomm₂) <|
    Submodule.linearMap_qext _ <| LinearMap.ext fun y ↦ by
      simp [hjq.apply_apply_eq_zero y]
  v₀₁ :=
    { τ₁ := ModuleCat.ofHom T₁.ker.subtype
      τ₂ := ModuleCat.ofHom T₂.ker.subtype
      τ₃ := ModuleCat.ofHom T₃.ker.subtype
      comm₁₂ := by ext _; rfl
      comm₂₃ := by ext _; rfl }
  v₁₂ :=
    { τ₁ := ModuleCat.ofHom T₁
      τ₂ := ModuleCat.ofHom T₂
      τ₃ := ModuleCat.ofHom T₃
      comm₁₂ := ModuleCat.hom_ext hcomm₁.symm
      comm₂₃ := ModuleCat.hom_ext hcomm₂.symm }
  v₂₃ :=
    { τ₁ := ModuleCat.ofHom T₁.range.mkQ
      τ₂ := ModuleCat.ofHom T₂.range.mkQ
      τ₃ := ModuleCat.ofHom T₃.range.mkQ
      comm₁₂ := by ext _; rfl
      comm₂₃ := by ext _; rfl }
  w₀₂ := by ext x <;> exact x.2
  w₁₃ := by ext x <;> exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  h₀ := ShortComplex.isLimitOfIsLimitπ _
    ((KernelFork.isLimitMapConeEquiv _ _).symm (ModuleCat.kernelIsLimit (ModuleCat.ofHom T₁)))
    ((KernelFork.isLimitMapConeEquiv _ _).symm (ModuleCat.kernelIsLimit (ModuleCat.ofHom T₂)))
    ((KernelFork.isLimitMapConeEquiv _ _).symm (ModuleCat.kernelIsLimit (ModuleCat.ofHom T₃)))
  h₃ := ShortComplex.isColimitOfIsColimitπ _
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
      (ModuleCat.cokernelIsColimit (ModuleCat.ofHom T₁)))
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
      (ModuleCat.cokernelIsColimit (ModuleCat.ofHom T₂)))
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
      (ModuleCat.cokernelIsColimit (ModuleCat.ofHom T₃)))
  L₁_exact := ModuleCat.shortComplex_exact _ hip
  epi_L₁_g := (ModuleCat.epi_iff_surjective _).2 hp
  L₂_exact := ModuleCat.shortComplex_exact _ hjq
  mono_L₂_f := (ModuleCat.mono_iff_injective _).2 hj

/-- The six-term kernel--cokernel complex built by `snakeInput` is exact via
`CategoryTheory.ShortComplex.SnakeInput.snake_lemma`. -/
theorem snakeInput_composableArrows_exact {i : E₁ →ₗ[𝕜] E₂} {p : E₂ →ₗ[𝕜] E₃}
    {j : F₁ →ₗ[𝕜] F₂} {q : F₂ →ₗ[𝕜] F₃}
    {T₁ : E₁ →ₗ[𝕜] F₁} {T₂ : E₂ →ₗ[𝕜] F₂} {T₃ : E₃ →ₗ[𝕜] F₃}
    (hip : Exact i p) (hp : Surjective p) (hjq : Exact j q) (hj : Injective j)
    (hcomm₁ : T₂ ∘ₗ i = j ∘ₗ T₁) (hcomm₂ : T₃ ∘ₗ p = q ∘ₗ T₂) :
    (snakeInput hip hp hjq hj hcomm₁ hcomm₂).composableArrows.Exact :=
  (snakeInput hip hp hjq hj hcomm₁ hcomm₂).snake_lemma

end SnakeInput

/-! ### Universe-polymorphic connecting map `snakeDelta` and exactness -/

section SnakeDelta

universe u u₁ u₂ u₃ v₁ v₂ v₃

variable {𝕜 : Type u} [Ring 𝕜]
variable {E₁ : Type u₁} {E₂ : Type u₂} {E₃ : Type u₃}
variable {F₁ : Type v₁} {F₂ : Type v₂} {F₃ : Type v₃}
variable [AddCommGroup E₁] [Module 𝕜 E₁] [AddCommGroup E₂] [Module 𝕜 E₂]
  [AddCommGroup E₃] [Module 𝕜 E₃]
variable [AddCommGroup F₁] [Module 𝕜 F₁] [AddCommGroup F₂] [Module 𝕜 F₂]
  [AddCommGroup F₃] [Module 𝕜 F₃]
variable {i : E₁ →ₗ[𝕜] E₂} {p : E₂ →ₗ[𝕜] E₃} {j : F₁ →ₗ[𝕜] F₂} {q : F₂ →ₗ[𝕜] F₃}
variable {T₁ : E₁ →ₗ[𝕜] F₁} {T₂ : E₂ →ₗ[𝕜] F₂} {T₃ : E₃ →ₗ[𝕜] F₃}
variable (hip : Exact i p) (hp : Surjective p) (hjq : Exact j q) (hj : Injective j)
variable (hcomm₁ : T₂ ∘ₗ i = j ∘ₗ T₁) (hcomm₂ : T₃ ∘ₗ p = q ∘ₗ T₂)

private abbrev snakeInputULift :
    ShortComplex.SnakeInput (ModuleCat.{max u₁ u₂ u₃ v₁ v₂ v₃} 𝕜) :=
  let eE₁ : ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} E₁ ≃ₗ[𝕜] E₁ := ULift.moduleEquiv
  let eE₂ : ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} E₂ ≃ₗ[𝕜] E₂ := ULift.moduleEquiv
  let eE₃ : ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} E₃ ≃ₗ[𝕜] E₃ := ULift.moduleEquiv
  let eF₁ : ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} F₁ ≃ₗ[𝕜] F₁ := ULift.moduleEquiv
  let eF₂ : ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} F₂ ≃ₗ[𝕜] F₂ := ULift.moduleEquiv
  let eF₃ : ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} F₃ ≃ₗ[𝕜] F₃ := ULift.moduleEquiv
  snakeInput
    (i := eE₂.symm.toLinearMap ∘ₗ i ∘ₗ eE₁.toLinearMap)
    (p := eE₃.symm.toLinearMap ∘ₗ p ∘ₗ eE₂.toLinearMap)
    (j := eF₂.symm.toLinearMap ∘ₗ j ∘ₗ eF₁.toLinearMap)
    (q := eF₃.symm.toLinearMap ∘ₗ q ∘ₗ eF₂.toLinearMap)
    (T₁ := eF₁.symm.toLinearMap ∘ₗ T₁ ∘ₗ eE₁.toLinearMap)
    (T₂ := eF₂.symm.toLinearMap ∘ₗ T₂ ∘ₗ eE₂.toLinearMap)
    (T₃ := eF₃.symm.toLinearMap ∘ₗ T₃ ∘ₗ eE₃.toLinearMap)
    (fun ⟨x⟩ ↦ ⟨fun hx ↦ let ⟨a, ha⟩ := (hip x).1 (congrArg ULift.down hx)
        ⟨⟨a⟩, congrArg ULift.up ha⟩,
      fun ⟨⟨a⟩, ha⟩ ↦ congrArg ULift.up ((hip x).2 ⟨a, congrArg ULift.down ha⟩)⟩)
    (fun ⟨x⟩ ↦ let ⟨y, hy⟩ := hp x; ⟨⟨y⟩, congrArg ULift.up hy⟩)
    (fun ⟨y⟩ ↦ ⟨fun hy ↦ let ⟨a, ha⟩ := (hjq y).1 (congrArg ULift.down hy)
        ⟨⟨a⟩, congrArg ULift.up ha⟩,
      fun ⟨⟨a⟩, ha⟩ ↦ congrArg ULift.up ((hjq y).2 ⟨a, congrArg ULift.down ha⟩)⟩)
    (fun ⟨_⟩ ⟨_⟩ h ↦ congrArg ULift.up (hj (congrArg ULift.down h)))
    (LinearMap.ext fun ⟨x⟩ ↦ congrArg ULift.up (LinearMap.congr_fun hcomm₁ x))
    (LinearMap.ext fun ⟨x⟩ ↦ congrArg ULift.up (LinearMap.congr_fun hcomm₂ x))

/-- The categorical snake connecting homomorphism as a universe-polymorphic `𝕜`-linear map
`ker T₃ →ₗ[𝕜] (F₁ ⧸ range T₁)`, constructed from `CategoryTheory.ShortComplex.SnakeInput.δ`
on `ModuleCat 𝕜`. -/
def snakeDelta : T₃.ker →ₗ[𝕜] (F₁ ⧸ T₁.range) :=
  let eE₁ : ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} E₁ ≃ₗ[𝕜] E₁ := ULift.moduleEquiv
  let eE₃ : ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} E₃ ≃ₗ[𝕜] E₃ := ULift.moduleEquiv
  let eF₁ : ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} F₁ ≃ₗ[𝕜] F₁ := ULift.moduleEquiv
  let eF₃ : ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} F₃ ≃ₗ[𝕜] F₃ := ULift.moduleEquiv
  let toKer : T₃.ker →ₗ[𝕜] (eF₃.symm.toLinearMap ∘ₗ T₃ ∘ₗ eE₃.toLinearMap).ker :=
    eE₃.symm.toLinearMap.restrict fun _ hx ↦ LinearMap.mem_ker.2 (congrArg ULift.up hx)
  let fromCoker : (ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} F₁ ⧸
      (eF₁.symm.toLinearMap ∘ₗ T₁ ∘ₗ eE₁.toLinearMap).range) →ₗ[𝕜] (F₁ ⧸ T₁.range) :=
    Submodule.mapQ _ T₁.range eF₁.toLinearMap fun _ ⟨⟨x⟩, hx⟩ ↦ ⟨x, congrArg ULift.down hx⟩
  fromCoker ∘ₗ (snakeInputULift hip hp hjq hj hcomm₁ hcomm₂).δ.hom ∘ₗ toKer

/-- **Elementwise characterization of the snake connecting map:** if `p y = x` for `x ∈ ker T₃`
and `j z = T₂ y`, then `δ x` is the class of `z` in `F₁ ⧸ range T₁`. -/
theorem snakeDelta_eq (x : T₃.ker) (y : E₂) (hy : p y = x) (z : F₁) (hz : j z = T₂ y) :
    snakeDelta hip hp hjq hj hcomm₁ hcomm₂ x = Submodule.Quotient.mk z := by
  let S := snakeInputULift hip hp hjq hj hcomm₁ hcomm₂
  let x' : S.L₀.X₃ :=
    ⟨ULift.up x.1, LinearMap.mem_ker.2 (congrArg ULift.up (LinearMap.mem_ker.1 x.2))⟩
  let fromCoker : S.L₃.X₁ →ₗ[𝕜] (F₁ ⧸ T₁.range) :=
    Submodule.mapQ _ T₁.range ULift.moduleEquiv.toLinearMap fun _ ⟨⟨a⟩, ha⟩ ↦
      ⟨a, congrArg ULift.down ha⟩
  exact congrArg fromCoker
    (S.δ_apply x' (ULift.up y) (ULift.up z) (congrArg ULift.up hy) (congrArg ULift.up hz))

/-- **Splitting formula for the connecting map:** for any (not necessarily linear) right inverse `s`
of `p` and left inverse `r` of `j`, `δ x = [r (T₂ (s x))]` for all `x ∈ ker T₃`. -/
theorem snakeDelta_eq_mk_retract_section {s : E₃ → E₂} (hs : RightInverse s p)
    {r : F₂ → F₁} (hr : LeftInverse r j) (x : T₃.ker) :
    snakeDelta hip hp hjq hj hcomm₁ hcomm₂ x = Submodule.Quotient.mk (r (T₂ (s x))) := by
  have hmem : T₂ (s x) ∈ Set.range j := (hjq _).1 <| by
    calc
      q (T₂ (s x)) = T₃ (p (s x)) := (LinearMap.congr_fun hcomm₂ (s x)).symm
      _ = T₃ x := by rw [hs]
      _ = 0 := x.2
  obtain ⟨z, hz⟩ := hmem
  exact snakeDelta_eq hip hp hjq hj hcomm₁ hcomm₂ x (s x) (hs x) (r (T₂ (s x)))
    (by rw [← hz, hr z])

/-- Exactness of `ker T₂ → ker T₃ → F₁ ⧸ range T₁`, deduced from `SnakeInput.L₁'_exact`. -/
theorem exact_kerMapOfComm_snakeDelta :
    Exact (kerMapOfComm hcomm₂) (snakeDelta hip hp hjq hj hcomm₁ hcomm₂) := by
  let S := snakeInputULift hip hp hjq hj hcomm₁ hcomm₂
  let fromCoker : S.L₃.X₁ →ₗ[𝕜] (F₁ ⧸ T₁.range) :=
    Submodule.mapQ _ T₁.range ULift.moduleEquiv.toLinearMap fun _ ⟨⟨a⟩, ha⟩ ↦
      ⟨a, congrArg ULift.down ha⟩
  have hfrom : Injective fromCoker := by
    intro a b hab
    induction a using Submodule.Quotient.induction_on with | H u =>
    induction b using Submodule.Quotient.induction_on with | H v =>
    obtain ⟨w, hw⟩ := (Submodule.Quotient.eq _).1 hab
    exact (Submodule.Quotient.eq _).2 ⟨⟨w⟩, ULift.ext hw⟩
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 S.L₁'_exact
  intro x
  let x' : S.L₀.X₃ :=
    ⟨ULift.up x.1, LinearMap.mem_ker.2 (congrArg ULift.up (LinearMap.mem_ker.1 x.2))⟩
  have hzero : snakeDelta hip hp hjq hj hcomm₁ hcomm₂ x = 0 ↔ S.L₁'.g x' = 0 :=
    map_eq_zero_iff fromCoker hfrom
  refine (hzero.trans (hex x')).trans ?_
  refine ⟨fun ⟨⟨⟨y⟩, hy⟩, hyx⟩ ↦ ⟨⟨y, congrArg ULift.down hy⟩,
      Subtype.ext (congrArg (fun v : S.L₀.X₃ ↦ v.1.down) hyx)⟩,
    fun ⟨⟨y, hy⟩, hyx⟩ ↦ ⟨⟨⟨y⟩, congrArg ULift.up hy⟩,
      Subtype.ext (congrArg (fun v : T₃.ker ↦ ULift.up v.1) hyx)⟩⟩

/-- Exactness of `ker T₃ → F₁ ⧸ range T₁ → F₂ ⧸ range T₂`, deduced from `SnakeInput.L₂'_exact`. -/
theorem exact_snakeDelta_cokerMapOfComm :
    Exact (snakeDelta hip hp hjq hj hcomm₁ hcomm₂) (cokerMapOfComm hcomm₁) := by
  let S := snakeInputULift hip hp hjq hj hcomm₁ hcomm₂
  let fromCoker : S.L₃.X₁ →ₗ[𝕜] (F₁ ⧸ T₁.range) :=
    Submodule.mapQ _ T₁.range ULift.moduleEquiv.toLinearMap fun _ ⟨⟨a⟩, ha⟩ ↦
      ⟨a, congrArg ULift.down ha⟩
  have hfrom : Injective fromCoker := by
    intro a b hab
    induction a using Submodule.Quotient.induction_on with | H u =>
    induction b using Submodule.Quotient.induction_on with | H v =>
    obtain ⟨w, hw⟩ := (Submodule.Quotient.eq _).1 hab
    exact (Submodule.Quotient.eq _).2 ⟨⟨w⟩, ULift.ext hw⟩
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 S.L₂'_exact
  intro c
  induction c using Submodule.Quotient.induction_on with | H y =>
  let y' : S.L₃.X₁ := Submodule.Quotient.mk (ULift.up y)
  have hzero : cokerMapOfComm hcomm₁ (Submodule.Quotient.mk y) = 0 ↔ S.L₂'.g y' = 0 := by
    rw [cokerMapOfComm_mk, Submodule.Quotient.mk_eq_zero]
    refine ⟨fun ⟨w, hw⟩ ↦ (Submodule.Quotient.mk_eq_zero _).2 ⟨⟨w⟩, congrArg ULift.up hw⟩,
      fun h ↦ ?_⟩
    obtain ⟨⟨w⟩, hw⟩ := (Submodule.Quotient.mk_eq_zero _).1 h
    exact ⟨w, congrArg ULift.down hw⟩
  refine (hzero.trans (hex y')).trans ?_
  refine ⟨fun ⟨⟨⟨x⟩, hx⟩, hxy⟩ ↦ ⟨⟨x, congrArg ULift.down hx⟩, congrArg fromCoker hxy⟩,
    fun ⟨⟨x, hx⟩, hxy⟩ ↦ ⟨⟨⟨x⟩, congrArg ULift.up hx⟩, hfrom hxy⟩⟩

/-- If the middle map `T₂` is injective, then `δ : ker T₃ → coker T₁` is injective. -/
theorem injective_snakeDelta_of_injective (hT₂ : Injective T₂) :
    Injective (snakeDelta hip hp hjq hj hcomm₁ hcomm₂) := by
  rw [← LinearMap.ker_eq_bot,
    (exact_kerMapOfComm_snakeDelta hip hp hjq hj hcomm₁ hcomm₂).linearMap_ker_eq, eq_bot_iff]
  rintro x ⟨y, rfl⟩
  have hy : y = 0 := Subtype.ext (hT₂ (by simp))
  simp [hy]

/-- If the middle map `T₂` is surjective, then `δ : ker T₃ → coker T₁` is surjective. -/
theorem surjective_snakeDelta_of_surjective (hT₂ : Surjective T₂) :
    Surjective (snakeDelta hip hp hjq hj hcomm₁ hcomm₂) := fun c ↦
  (exact_snakeDelta_cokerMapOfComm hip hp hjq hj hcomm₁ hcomm₂ c).1 <| by
    induction c using Submodule.Quotient.induction_on with | H y =>
    exact (Submodule.Quotient.mk_eq_zero _).2 (hT₂ (j y))

/-- If the middle map `T₂` is bijective, then `δ : ker T₃ → coker T₁` is a bijection (even when
`ker T₃` and `coker T₁` are infinite-dimensional). -/
theorem bijective_snakeDelta_of_bijective (hT₂ : Bijective T₂) :
    Bijective (snakeDelta hip hp hjq hj hcomm₁ hcomm₂) :=
  ⟨injective_snakeDelta_of_injective hip hp hjq hj hcomm₁ hcomm₂ hT₂.1,
    surjective_snakeDelta_of_surjective hip hp hjq hj hcomm₁ hcomm₂ hT₂.2⟩

end SnakeDelta

/-! ### Continuous snake maps, topological splittings and Hilbert spaces -/

section ContinuousSnake

variable {𝕜 : Type*} [Ring 𝕜]
variable {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}
variable [AddCommGroup E₁] [TopologicalSpace E₁] [Module 𝕜 E₁]
variable [AddCommGroup E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
variable [AddCommGroup F₁] [TopologicalSpace F₁] [Module 𝕜 F₁]
variable [AddCommGroup F₂] [TopologicalSpace F₂] [Module 𝕜 F₂]
variable {i : E₁ →L[𝕜] E₂} {j : F₁ →L[𝕜] F₂} {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂}

/-- The continuous linear map `ker T₁ →L[𝕜] ker T₂` induced by a commuting square
`T₂ ∘L i = j ∘L T₁`. -/
def kerMapLOfComm (hcomm : T₂.comp i = j.comp T₁) : T₁.ker →L[𝕜] T₂.ker :=
  i.restrict fun x hx ↦ by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [ContinuousLinearMap.coe_coe] at hx ⊢
    calc
      T₂ (i x) = j (T₁ x) := DFunLike.congr_fun hcomm x
      _ = 0 := by rw [hx, map_zero]

@[simp]
theorem coe_kerMapLOfComm_apply (hcomm : T₂.comp i = j.comp T₁) (x : T₁.ker) :
    (kerMapLOfComm hcomm x : E₂) = i x := (rfl)

@[simp]
theorem toLinearMap_kerMapLOfComm (hcomm : T₂.comp i = j.comp T₁) :
    (kerMapLOfComm hcomm).toLinearMap =
      kerMapOfComm (congrArg ContinuousLinearMap.toLinearMap hcomm) := by
  ext x
  rfl

/-- The continuous linear map `(F₁ ⧸ range T₁) →L[𝕜] (F₂ ⧸ range T₂)` induced by a commuting
square `T₂ ∘L i = j ∘L T₁`, with the quotient topology on both cokernels. -/
def cokerMapLOfComm (hcomm : T₂.comp i = j.comp T₁) : (F₁ ⧸ T₁.range) →L[𝕜] (F₂ ⧸ T₂.range) :=
  T₁.range.liftQL (T₂.range.mkQL.comp j) fun _ ⟨x, hx⟩ ↦
    LinearMap.mem_ker.2 <| (Submodule.Quotient.mk_eq_zero _).2
      ⟨i x, (DFunLike.congr_fun hcomm x).trans (congrArg j hx)⟩

@[simp]
theorem cokerMapLOfComm_mk (hcomm : T₂.comp i = j.comp T₁) (y : F₁) :
    cokerMapLOfComm hcomm (Submodule.Quotient.mk y) = Submodule.Quotient.mk (j y) := (rfl)

@[simp]
theorem toLinearMap_cokerMapLOfComm (hcomm : T₂.comp i = j.comp T₁) :
    (cokerMapLOfComm hcomm).toLinearMap =
      cokerMapOfComm (congrArg ContinuousLinearMap.toLinearMap hcomm) :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun _ ↦ rfl

variable [AddCommGroup E₃] [TopologicalSpace E₃] [Module 𝕜 E₃]
variable [AddCommGroup F₃] [TopologicalSpace F₃] [Module 𝕜 F₃]
variable {p : E₂ →L[𝕜] E₃} {q : F₂ →L[𝕜] F₃} {T₃ : E₃ →L[𝕜] F₃}

/-- **Continuity of the snake connecting map:** when `p` has a continuous linear right inverse and
`j` has a continuous linear left inverse, `δ : ker T₃ → F₁ ⧸ range T₁` is continuous. -/
theorem continuous_snakeDelta (hip : Exact i p) (hjq : Exact j q)
    (hp_split : p.HasRightInverse) (hj_split : j.HasLeftInverse)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂) :
    Continuous (snakeDelta hip hp_split.surjective hjq hj_split.injective
      (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
      (congrArg ContinuousLinearMap.toLinearMap hcomm₂)) := by
  obtain ⟨s, hs⟩ := hp_split
  obtain ⟨r, hr⟩ := hj_split
  have hfun :
      ⇑(snakeDelta hip hs.surjective hjq hr.injective
        (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
        (congrArg ContinuousLinearMap.toLinearMap hcomm₂)) =
      ⇑(T₁.range.mkQL.comp (r.comp (T₂.comp (s.comp T₃.ker.subtypeL)))) :=
    funext fun x ↦
      snakeDelta_eq_mk_retract_section hip hs.surjective hjq hr.injective _ _ hs hr x
  rw [hfun]
  exact ContinuousLinearMap.continuous _

/-- The snake connecting map bundled as a continuous linear map `ker T₃ →L[𝕜] (F₁ ⧸ range T₁)`,
defined from the intrinsic categorical connecting homomorphism `snakeDelta`. -/
def snakeDeltaL (hip : Exact i p) (hjq : Exact j q)
    (hp_split : p.HasRightInverse) (hj_split : j.HasLeftInverse)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂) :
    T₃.ker →L[𝕜] (F₁ ⧸ T₁.range) where
  toLinearMap := snakeDelta hip hp_split.surjective hjq hj_split.injective
    (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
    (congrArg ContinuousLinearMap.toLinearMap hcomm₂)
  cont := continuous_snakeDelta hip hjq hp_split hj_split hcomm₁ hcomm₂

@[simp]
theorem toLinearMap_snakeDeltaL (hip : Exact i p) (hjq : Exact j q)
    (hp_split : p.HasRightInverse) (hj_split : j.HasLeftInverse)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂) :
    (snakeDeltaL hip hjq hp_split hj_split hcomm₁ hcomm₂).toLinearMap =
      snakeDelta hip hp_split.surjective hjq hj_split.injective
        (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
        (congrArg ContinuousLinearMap.toLinearMap hcomm₂) := (rfl)

/-- **Independence of splittings:** for any continuous linear right inverse `s` of `p` and left
inverse `r` of `j`, `snakeDeltaL` equals `mkQL ∘L r ∘L T₂ ∘L s ∘L subtypeL`. -/
theorem snakeDeltaL_eq_comp (hip : Exact i p) (hjq : Exact j q)
    (hp_split : p.HasRightInverse) (hj_split : j.HasLeftInverse)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂)
    {s : E₃ →L[𝕜] E₂} (hs : RightInverse s p) {r : F₂ →L[𝕜] F₁} (hr : LeftInverse r j) :
    snakeDeltaL hip hjq hp_split hj_split hcomm₁ hcomm₂ =
      T₁.range.mkQL.comp (r.comp (T₂.comp (s.comp T₃.ker.subtypeL))) :=
  ContinuousLinearMap.ext fun x ↦
    snakeDelta_eq_mk_retract_section hip hp_split.surjective hjq hj_split.injective _ _ hs hr x

/-- Any two pairs `(s, r)` and `(s', r')` of continuous linear splittings of `p` and `j` produce
the same continuous linear connecting map `ker T₃ →L[𝕜] (F₁ ⧸ range T₁)`. -/
theorem mkQL_comp_retract_comp_section_eq (hip : Exact i p) (hjq : Exact j q)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂)
    {s s' : E₃ →L[𝕜] E₂} (hs : RightInverse s p) (hs' : RightInverse s' p)
    {r r' : F₂ →L[𝕜] F₁} (hr : LeftInverse r j) (hr' : LeftInverse r' j) :
    T₁.range.mkQL.comp (r.comp (T₂.comp (s.comp T₃.ker.subtypeL))) =
      T₁.range.mkQL.comp (r'.comp (T₂.comp (s'.comp T₃.ker.subtypeL))) := by
  have hp_split : p.HasRightInverse := ⟨s, hs⟩
  have hj_split : j.HasLeftInverse := ⟨r, hr⟩
  rw [← snakeDeltaL_eq_comp hip hjq hp_split hj_split hcomm₁ hcomm₂ hs hr,
    ← snakeDeltaL_eq_comp hip hjq hp_split hj_split hcomm₁ hcomm₂ hs' hr']

/-- Exactness at `ker T₃` for `snakeDeltaL`. -/
theorem exact_kerMapLOfComm_snakeDeltaL (hip : Exact i p) (hjq : Exact j q)
    (hp_split : p.HasRightInverse) (hj_split : j.HasLeftInverse)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂) :
    Exact (kerMapLOfComm hcomm₂) (snakeDeltaL hip hjq hp_split hj_split hcomm₁ hcomm₂) :=
  exact_kerMapOfComm_snakeDelta hip hp_split.surjective hjq hj_split.injective
    (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
    (congrArg ContinuousLinearMap.toLinearMap hcomm₂)

/-- Exactness at `F₁ ⧸ range T₁` for `snakeDeltaL`. -/
theorem exact_snakeDeltaL_cokerMapLOfComm (hip : Exact i p) (hjq : Exact j q)
    (hp_split : p.HasRightInverse) (hj_split : j.HasLeftInverse)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂) :
    Exact (snakeDeltaL hip hjq hp_split hj_split hcomm₁ hcomm₂) (cokerMapLOfComm hcomm₁) :=
  exact_snakeDelta_cokerMapOfComm hip hp_split.surjective hjq hj_split.injective
    (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
    (congrArg ContinuousLinearMap.toLinearMap hcomm₂)

end ContinuousSnake

section TopologicalSplitting

/-- In an algebraically exact pair `E₁ —i→ E₂ —p→ E₃` where `p` is continuous into a `T₁` space,
`range i = ker p` is closed. -/
theorem _root_.Function.Exact.isClosed_range {𝕜 E₁ E₂ E₃ : Type*} [Semiring 𝕜]
    [AddCommMonoid E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
    [AddCommMonoid E₃] [TopologicalSpace E₃] [Module 𝕜 E₃] [T1Space E₃]
    {i : E₁ → E₂} {p : E₂ →L[𝕜] E₃} (hip : Exact i p) :
    IsClosed (Set.range i) := by
  have h : Set.range i = (p.ker : Set E₂) := Set.ext fun x ↦ (hip x).symm
  rw [h]
  exact p.isClosed_ker

section Banach

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E₁ E₂ E₃ : Type*}

/-- In a surjective map `p : E₂ →L[𝕜] E₃` between Banach spaces, if `ker p` is topologically
complemented then `p` has a continuous linear right inverse. -/
theorem _root_.ContinuousLinearMap.hasRightInverse_of_surjective
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [CompleteSpace E₃]
    (p : E₂ →L[𝕜] E₃) (hp : Surjective p) (hcompl : p.ker.ClosedComplemented) :
    p.HasRightInverse :=
  (p.exists_rightInverse_iff_closedComplemented_ker (p.isQuotientMap hp)).2 hcompl

/-- In an exact pair `E₁ —i→ E₂ —p→ E₃` with `E₁, E₂` Banach, `E₃` `T₁` and `i` injective, if
`ker p` is topologically complemented then `i` has a continuous linear left inverse. -/
theorem _root_.ContinuousLinearMap.hasLeftInverse_of_exact
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [AddCommGroup E₃] [TopologicalSpace E₃] [Module 𝕜 E₃] [T1Space E₃]
    (i : E₁ →L[𝕜] E₂) {p : E₂ →L[𝕜] E₃}
    (hi : Injective i) (hip : Exact i p) (hcompl : p.ker.ClosedComplemented) :
    i.HasLeftInverse :=
  ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range
    hi hip.isClosed_range (hip.linearMap_ker_eq.symm ▸ hcompl)

/-- **Topological splitting of a Banach short exact sequence:** if `0 → E₁ —i→ E₂ —p→ E₃ → 0` is
algebraically exact between Banach spaces and `ker p` is topologically complemented, then there
exist compatible continuous linear splitting maps `r : E₂ →L[𝕜] E₁` and `s : E₃ →L[𝕜] E₂` with
`r ∘L i = id`, `p ∘L s = id`, `r ∘L s = 0` and `i ∘L r + s ∘L p = id`. -/
theorem exists_topologicalSplitting_of_shortExact
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [CompleteSpace E₃]
    {i : E₁ →L[𝕜] E₂} {p : E₂ →L[𝕜] E₃}
    (hi : Injective i) (hip : Exact i p) (hp : Surjective p)
    (hcompl : p.ker.ClosedComplemented) :
    ∃ (r : E₂ →L[𝕜] E₁) (s : E₃ →L[𝕜] E₂),
      r.comp i = ContinuousLinearMap.id 𝕜 E₁ ∧
      p.comp s = ContinuousLinearMap.id 𝕜 E₃ ∧
      r.comp s = 0 ∧
      i.comp r + s.comp p = ContinuousLinearMap.id 𝕜 E₂ := by
  obtain ⟨s, hs⟩ := p.hasRightInverse_of_surjective hp hcompl
  let _ : CompleteSpace i.range := hip.isClosed_range.completeSpace_coe
  have hbij : Bijective i.rangeRestrict :=
    ⟨fun _ _ hxy ↦ hi (congrArg Subtype.val hxy), Set.rangeFactorization_surjective⟩
  let e : E₁ ≃L[𝕜] i.range := ContinuousLinearEquiv.ofBijective i.rangeRestrict
    (LinearMap.ker_eq_bot.2 hbij.1) (LinearMap.range_eq_top.2 hbij.2)
  have hmem (x : E₂) : x - s (p x) ∈ i.range := by
    rw [hip.linearMap_ker_eq.symm, LinearMap.mem_ker]
    simp [hs (p x)]
  let r : E₂ →L[𝕜] E₁ := e.symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id 𝕜 E₂) - s.comp p).codRestrict i.range hmem)
  have hir (x : E₂) : i (r x) = x - s (p x) :=
    congrArg Subtype.val (e.apply_symm_apply ⟨x - s (p x), hmem x⟩)
  refine ⟨r, s, ?_, ContinuousLinearMap.ext hs, ?_, ContinuousLinearMap.ext fun x ↦ by simp [hir x]⟩
  · ext x
    apply hi
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hir,
      hip.apply_apply_eq_zero x, map_zero, sub_zero]
  · ext z
    apply hi
    rw [ContinuousLinearMap.comp_apply, zero_apply, map_zero, hir, hs z, sub_self]

end Banach

section Hilbert

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ H₂ H₃ G₁ G₂ G₃ : Type*}

/-- Every surjective bounded linear map from a Hilbert space onto a Banach space admits a
continuous linear right inverse, obtained from the orthogonal complement of its kernel and the
open mapping theorem. -/
theorem _root_.ContinuousLinearMap.hasRightInverse_of_surjective_hilbert
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    [NormedAddCommGroup H₃] [NormedSpace 𝕜 H₃] [CompleteSpace H₃]
    (p : H₂ →L[𝕜] H₃) (hp : Surjective p) : p.HasRightInverse := by
  let _ : CompleteSpace p.ker := p.isClosed_ker.completeSpace_coe
  exact p.hasRightInverse_of_surjective hp p.ker.isTopCompl_orthogonal.closedComplemented

/-- In an algebraically exact sequence `0 → H₁ —i→ H₂ —p→ H₃` with `H₁` Banach, `H₂` Hilbert and
`H₃` `T₁`, `i` admits a continuous linear left inverse. -/
theorem _root_.ContinuousLinearMap.hasLeftInverse_of_exact_hilbert
    [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    [AddCommGroup H₃] [TopologicalSpace H₃] [Module 𝕜 H₃] [T1Space H₃]
    (i : H₁ →L[𝕜] H₂) {p : H₂ →L[𝕜] H₃} (hi : Injective i) (hip : Exact i p) :
    i.HasLeftInverse := by
  let _ : CompleteSpace p.ker := p.isClosed_ker.completeSpace_coe
  exact i.hasLeftInverse_of_exact hi hip p.ker.isTopCompl_orthogonal.closedComplemented

/-- **Automatic topological splitting in Hilbert spaces:** every algebraically short exact sequence
`0 → H₁ —i→ H₂ —p→ H₃ → 0` with `H₂` Hilbert and `H₁, H₃` Banach splits topologically. -/
theorem exists_topologicalSplitting_of_shortExact_hilbert
    [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    [NormedAddCommGroup H₃] [NormedSpace 𝕜 H₃] [CompleteSpace H₃]
    {i : H₁ →L[𝕜] H₂} {p : H₂ →L[𝕜] H₃}
    (hi : Injective i) (hip : Exact i p) (hp : Surjective p) :
    ∃ (r : H₂ →L[𝕜] H₁) (s : H₃ →L[𝕜] H₂),
      r.comp i = ContinuousLinearMap.id 𝕜 H₁ ∧
      p.comp s = ContinuousLinearMap.id 𝕜 H₃ ∧
      r.comp s = 0 ∧
      i.comp r + s.comp p = ContinuousLinearMap.id 𝕜 H₂ := by
  let _ : CompleteSpace p.ker := p.isClosed_ker.completeSpace_coe
  exact exists_topologicalSplitting_of_shortExact hi hip hp
    p.ker.isTopCompl_orthogonal.closedComplemented

/-- **Automatic continuity of the connecting map for Hilbert spaces:** in any commuting diagram of
continuous linear maps between algebraically exact sequences (`p` surjective, `j` injective) where
`H₂, G₂` are Hilbert, `H₃, G₁` are Banach and `G₃` is `T₁`, `δ : ker T₃ → G₁ ⧸ range T₁` is
automatically continuous. -/
theorem continuous_snakeDelta_hilbert
    [AddCommGroup H₁] [TopologicalSpace H₁] [Module 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    [NormedAddCommGroup H₃] [NormedSpace 𝕜 H₃] [CompleteSpace H₃]
    [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [CompleteSpace G₁]
    [NormedAddCommGroup G₂] [InnerProductSpace 𝕜 G₂] [CompleteSpace G₂]
    [AddCommGroup G₃] [TopologicalSpace G₃] [Module 𝕜 G₃] [T1Space G₃]
    {i : H₁ →L[𝕜] H₂} {p : H₂ →L[𝕜] H₃} {j : G₁ →L[𝕜] G₂} {q : G₂ →L[𝕜] G₃}
    {T₁ : H₁ →L[𝕜] G₁} {T₂ : H₂ →L[𝕜] G₂} {T₃ : H₃ →L[𝕜] G₃}
    (hip : Exact i p) (hp : Surjective p) (hjq : Exact j q) (hj : Injective j)
    (hcomm₁ : T₂.comp i = j.comp T₁) (hcomm₂ : T₃.comp p = q.comp T₂) :
    Continuous (snakeDelta hip hp hjq hj
      (congrArg ContinuousLinearMap.toLinearMap hcomm₁)
      (congrArg ContinuousLinearMap.toLinearMap hcomm₂)) :=
  continuous_snakeDelta hip hjq (p.hasRightInverse_of_surjective_hilbert hp)
    (j.hasLeftInverse_of_exact_hilbert hj hjq) hcomm₁ hcomm₂

end Hilbert

end TopologicalSplitting

/-! ### Exact six-term sequences: two-out-of-three finiteness and index additivity -/

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

/-! ### Upper-triangular block operators and block parametrices -/

section UpperTriangularDefs

variable {𝕜 : Type*} [Semiring 𝕜]
variable {E₁ E₂ F₁ F₂ G₁ G₂ : Type*}
variable [AddCommMonoid E₁] [TopologicalSpace E₁] [Module 𝕜 E₁]
variable [AddCommMonoid E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
variable [AddCommMonoid F₁] [TopologicalSpace F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
variable [AddCommMonoid F₂] [TopologicalSpace F₂] [Module 𝕜 F₂]

/-- The product sequence `E₁ —inl→ E₁ × E₂ —snd→ E₂` of continuous linear maps is exact. -/
theorem exact_inl_snd : Exact (inl 𝕜 E₁ E₂) (snd 𝕜 E₁ E₂) :=
  Function.Exact.inl_snd

/-- The **upper-triangular block operator** `E₁ × E₂ →L[𝕜] F₁ × F₂` sending `(x, y)` to
`(A x + B y, D y)`. -/
def upperTriangular (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂) :
    E₁ × E₂ →L[𝕜] F₁ × F₂ :=
  (A.coprod B).prod (D.comp (snd 𝕜 E₁ E₂))

@[simp]
theorem upperTriangular_apply (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (x : E₁) (y : E₂) :
    upperTriangular A B D (x, y) = (A x + B y, D y) := (rfl)

@[simp]
theorem upperTriangular_zero (A : E₁ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂) :
    upperTriangular A 0 D = A.prodMap D :=
  ContinuousLinearMap.ext fun ⟨_, _⟩ ↦ by simp

@[simp]
theorem upperTriangular_comp_inl (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂) :
    (upperTriangular A B D).comp (inl 𝕜 E₁ E₂) = (inl 𝕜 F₁ F₂).comp A :=
  ContinuousLinearMap.ext fun _ ↦ by simp

@[simp]
theorem snd_comp_upperTriangular (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂) :
    (snd 𝕜 F₁ F₂).comp (upperTriangular A B D) = D.comp (snd 𝕜 E₁ E₂) :=
  ContinuousLinearMap.ext fun ⟨_, _⟩ ↦ by simp

theorem upperTriangular_comp [AddCommMonoid G₁] [TopologicalSpace G₁] [Module 𝕜 G₁]
    [ContinuousAdd G₁] [AddCommMonoid G₂] [TopologicalSpace G₂] [Module 𝕜 G₂]
    (A₂ : F₁ →L[𝕜] G₁) (B₂ : F₂ →L[𝕜] G₁) (D₂ : F₂ →L[𝕜] G₂)
    (A₁ : E₁ →L[𝕜] F₁) (B₁ : E₂ →L[𝕜] F₁) (D₁ : E₂ →L[𝕜] F₂) :
    (upperTriangular A₂ B₂ D₂).comp (upperTriangular A₁ B₁ D₁) =
      upperTriangular (A₂.comp A₁) (A₂.comp B₁ + B₂.comp D₁) (D₂.comp D₁) :=
  ContinuousLinearMap.ext fun ⟨_, _⟩ ↦ by simp [map_add, add_assoc]

end UpperTriangularDefs

section UpperTriangularSnake

variable {𝕜 : Type*} [Ring 𝕜]
variable {E₁ E₂ F₁ F₂ : Type*}
variable [AddCommGroup E₁] [TopologicalSpace E₁] [Module 𝕜 E₁]
variable [AddCommGroup E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
variable [AddCommGroup F₁] [TopologicalSpace F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
variable [AddCommGroup F₂] [TopologicalSpace F₂] [Module 𝕜 F₂]

/-- **Connecting map of an upper-triangular block operator:** for `M = upperTriangular A B D`,
the snake connecting map `δ : ker D →L[𝕜] (F₁ ⧸ range A)` sends `y ∈ ker D` to `[B y]`. -/
theorem snakeDeltaL_upperTriangular (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂) :
    TauCeti.snakeDeltaL (i := inl 𝕜 E₁ E₂) (p := snd 𝕜 E₁ E₂)
      (j := inl 𝕜 F₁ F₂) (q := snd 𝕜 F₁ F₂)
      (T₁ := A) (T₂ := upperTriangular A B D) (T₃ := D)
      exact_inl_snd exact_inl_snd
      ⟨inr 𝕜 E₁ E₂, by intro _; simp⟩ ⟨fst 𝕜 F₁ F₂, by intro _; simp⟩
      (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm =
      A.range.mkQL.comp (B.comp D.ker.subtypeL) :=
  (TauCeti.snakeDeltaL_eq_comp _ _ _ _ _ _ (s := inr 𝕜 E₁ E₂) (fun _ ↦ rfl)
    (r := fst 𝕜 F₁ F₂) (fun _ ↦ rfl)).trans <| ContinuousLinearMap.ext fun y ↦ by simp

/-- When `upperTriangular A B D` is bijective, `y ↦ [B y]` is a bijection `ker D → F₁ ⧸ range A`
(even if both spaces are infinite-dimensional). In particular, invertibility of the middle
operator alone places no Fredholm restriction on `A` or `D`. -/
theorem bijective_mkQL_comp_of_bijective_upperTriangular
    (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (hbij : Bijective (upperTriangular A B D)) :
    Bijective (A.range.mkQL.comp (B.comp D.ker.subtypeL)) := by
  rw [← snakeDeltaL_upperTriangular A B D]
  exact TauCeti.bijective_snakeDelta_of_bijective exact_inl_snd LinearMap.snd_surjective
    exact_inl_snd LinearMap.inl_injective
    (congrArg ContinuousLinearMap.toLinearMap (upperTriangular_comp_inl A B D))
    (congrArg ContinuousLinearMap.toLinearMap (snd_comp_upperTriangular A B D).symm) hbij

end UpperTriangularSnake

section UpperTriangularParametrix

variable {E₁ E₂ F₁ F₂ : Type*}
variable [AddCommGroup E₁] [AddCommGroup E₂] [AddCommGroup F₁] [AddCommGroup F₂]
variable [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace F₁] [TopologicalSpace F₂]

/-- **Block quasi-inverse:** if `PA` is a quasi-inverse of `A` and `PD` is a quasi-inverse of `D`,
then `upperTriangular PA (-(PA ∘L B ∘L PD)) PD` is a quasi-inverse of `upperTriangular A B D`. -/
theorem isQuasiInverse_upperTriangular {𝕜 : Type*} [CommRing 𝕜] [IsNoetherianRing 𝕜]
    [Module 𝕜 E₁] [Module 𝕜 E₂] [Module 𝕜 F₁] [Module 𝕜 F₂]
    [IsTopologicalAddGroup E₁] [ContinuousAdd F₁]
    (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    {PA : F₁ →L[𝕜] E₁} {PD : F₂ →L[𝕜] E₂}
    (hA : PA.toLinearMap.IsQuasiInverse A.toLinearMap)
    (hD : PD.toLinearMap.IsQuasiInverse D.toLinearMap) :
    (upperTriangular PA (-(PA.comp (B.comp PD))) PD).toLinearMap.IsQuasiInverse
      (upperTriangular A B D).toLinearMap := by
  have hPA_l : (PA.toLinearMap ∘ₗ A.toLinearMap - LinearMap.id).HasFiniteRange :=
    LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.1 hA.1
  have hPA_r : (A.toLinearMap ∘ₗ PA.toLinearMap - LinearMap.id).HasFiniteRange :=
    LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.1 hA.2
  have hPD_l : (PD.toLinearMap ∘ₗ D.toLinearMap - LinearMap.id).HasFiniteRange :=
    LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.1 hD.1
  have hPD_r : (D.toLinearMap ∘ₗ PD.toLinearMap - LinearMap.id).HasFiniteRange :=
    LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.1 hD.2
  constructor
  · rw [LinearMap.IsLeftQuasiInverse, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    have hdecomp :
        (upperTriangular PA (-(PA.comp (B.comp PD))) PD).toLinearMap ∘ₗ
          (upperTriangular A B D).toLinearMap - LinearMap.id =
        (LinearMap.inl 𝕜 E₁ E₂ ∘ₗ ((PA.toLinearMap ∘ₗ A.toLinearMap - LinearMap.id) ∘ₗ
            LinearMap.fst 𝕜 E₁ E₂)) +
        (LinearMap.inl 𝕜 E₁ E₂ ∘ₗ ((-(PA.toLinearMap ∘ₗ B.toLinearMap)) ∘ₗ
            ((PD.toLinearMap ∘ₗ D.toLinearMap - LinearMap.id) ∘ₗ LinearMap.snd 𝕜 E₁ E₂))) +
        (LinearMap.inr 𝕜 E₁ E₂ ∘ₗ ((PD.toLinearMap ∘ₗ D.toLinearMap - LinearMap.id) ∘ₗ
            LinearMap.snd 𝕜 E₁ E₂)) :=
      LinearMap.ext fun ⟨_, _⟩ ↦ by simp [map_add]; abel
    rw [hdecomp]
    exact (((hPA_l.comp_right _).comp_left _).add
      (((hPD_l.comp_right _).comp_left _).comp_left _)).add
      ((hPD_l.comp_right _).comp_left _)
  · rw [LinearMap.IsRightQuasiInverse, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    have hdecomp :
        (upperTriangular A B D).toLinearMap ∘ₗ
          (upperTriangular PA (-(PA.comp (B.comp PD))) PD).toLinearMap - LinearMap.id =
        (LinearMap.inl 𝕜 F₁ F₂ ∘ₗ ((A.toLinearMap ∘ₗ PA.toLinearMap - LinearMap.id) ∘ₗ
            LinearMap.fst 𝕜 F₁ F₂)) +
        (LinearMap.inl 𝕜 F₁ F₂ ∘ₗ ((-(A.toLinearMap ∘ₗ PA.toLinearMap - LinearMap.id)) ∘ₗ
            ((B.toLinearMap ∘ₗ PD.toLinearMap) ∘ₗ LinearMap.snd 𝕜 F₁ F₂))) +
        (LinearMap.inr 𝕜 F₁ F₂ ∘ₗ ((D.toLinearMap ∘ₗ PD.toLinearMap - LinearMap.id) ∘ₗ
            LinearMap.snd 𝕜 F₁ F₂)) :=
      LinearMap.ext fun ⟨_, _⟩ ↦ by simp [map_add]; abel
    rw [hdecomp]
    exact (((hPA_r.comp_right _).comp_left _).add
      ((hPA_r.neg.comp_right _).comp_left _)).add
      ((hPD_r.comp_right _).comp_left _)

/-- **Upper-triangular Fredholmness via the block quasi-inverse (general TVSs):**
over a complete nontrivially normed field, if `A` and `D` are Fredholm between Hausdorff
topological vector spaces, then `upperTriangular A B D` is Fredholm for any bounded `B`. -/
theorem IsFredholm.upperTriangular {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [Module 𝕜 E₁] [Module 𝕜 E₂] [Module 𝕜 F₁] [Module 𝕜 F₂]
    [IsTopologicalAddGroup E₁] [IsTopologicalAddGroup E₂]
    [IsTopologicalAddGroup F₁] [IsTopologicalAddGroup F₂]
    [ContinuousSMul 𝕜 E₁] [ContinuousSMul 𝕜 E₂] [ContinuousSMul 𝕜 F₁] [ContinuousSMul 𝕜 F₂]
    [T2Space E₁] [T2Space E₂] [T2Space F₁] [T2Space F₂]
    {A : E₁ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hA : A.IsFredholm) (hD : D.IsFredholm) (B : E₂ →L[𝕜] F₁) :
    (A.upperTriangular B D).IsFredholm := by
  obtain ⟨PA, hPA⟩ := hA.exists_isQuasiInverse
  obtain ⟨PD, hPD⟩ := hD.exists_isQuasiInverse
  exact .of_isQuasiInverse (isQuasiInverse_upperTriangular A B D hPA hPD)

/-- **Left compact-error parametrix** for `upperTriangular A B D`. -/
theorem isCompactOperator_upperTriangular_parametrix_left {𝕜 : Type*} [Ring 𝕜]
    [Module 𝕜 E₁] [Module 𝕜 E₂] [Module 𝕜 F₁] [Module 𝕜 F₂]
    [IsTopologicalAddGroup E₁] [IsTopologicalAddGroup E₂] [ContinuousAdd F₁]
    (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    {PA : F₁ →L[𝕜] E₁} {PD : F₂ →L[𝕜] E₂}
    (hA : IsCompactOperator (PA.comp A - 1 : E₁ →L[𝕜] E₁))
    (hD : IsCompactOperator (PD.comp D - 1 : E₂ →L[𝕜] E₂)) :
    IsCompactOperator
      ((upperTriangular PA (-(PA.comp (B.comp PD))) PD).comp (upperTriangular A B D) - 1 :
        E₁ × E₂ →L[𝕜] E₁ × E₂) := by
  have h1 := (hA.comp_clm (fst 𝕜 E₁ E₂)).clm_comp (inl 𝕜 E₁ E₂)
  have h2 := (hD.comp_clm (snd 𝕜 E₁ E₂)).clm_comp ((inl 𝕜 E₁ E₂).comp (-(PA.comp B)))
  have h3 := (hD.comp_clm (snd 𝕜 E₁ E₂)).clm_comp (inr 𝕜 E₁ E₂)
  convert (h1.add h2).add h3 using 1
  exact funext fun ⟨_, _⟩ ↦ by simp [map_add]; abel

/-- **Right compact-error parametrix** for `upperTriangular A B D`. -/
theorem isCompactOperator_upperTriangular_parametrix_right {𝕜 : Type*} [Ring 𝕜]
    [Module 𝕜 E₁] [Module 𝕜 E₂] [Module 𝕜 F₁] [Module 𝕜 F₂]
    [IsTopologicalAddGroup E₁] [IsTopologicalAddGroup F₁] [IsTopologicalAddGroup F₂]
    (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    {PA : F₁ →L[𝕜] E₁} {PD : F₂ →L[𝕜] E₂}
    (hA : IsCompactOperator (A.comp PA - 1 : F₁ →L[𝕜] F₁))
    (hD : IsCompactOperator (D.comp PD - 1 : F₂ →L[𝕜] F₂)) :
    IsCompactOperator
      ((upperTriangular A B D).comp (upperTriangular PA (-(PA.comp (B.comp PD))) PD) - 1 :
        F₁ × F₂ →L[𝕜] F₁ × F₂) := by
  have h1 := (hA.comp_clm (fst 𝕜 F₁ F₂)).clm_comp (inl 𝕜 F₁ F₂)
  have h2 := (hA.comp_clm ((B.comp PD).comp (snd 𝕜 F₁ F₂))).clm_comp (-(inl 𝕜 F₁ F₂))
  have h3 := (hD.comp_clm (snd 𝕜 F₁ F₂)).clm_comp (inr 𝕜 F₁ F₂)
  convert (h1.add h2).add h3 using 1
  exact funext fun ⟨_, _⟩ ↦ by simp [map_add]; abel

end UpperTriangularParametrix

section UpperTriangularFredholm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E₁ E₂ F₁ F₂ : Type*}

/-- **Converse two-out-of-three for upper-triangular operators (left block):**
if `upperTriangular A B D` and `D` are Fredholm and `E₁, F₁` are Banach spaces, then `A` is
Fredholm. -/
theorem IsFredholm.of_upperTriangular_left [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    [AddCommGroup E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [CompleteSpace F₁]
    [AddCommGroup F₂] [TopologicalSpace F₂] [Module 𝕜 F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hM : (A.upperTriangular B D).IsFredholm) (hD : D.IsFredholm) :
    A.IsFredholm :=
  hM.of_shortExact_left hD LinearMap.inl_injective exact_inl_snd
    LinearMap.snd_surjective LinearMap.inl_injective exact_inl_snd
    (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm

/-- **Converse two-out-of-three for upper-triangular operators (right block):**
if `upperTriangular A B D` and `A` are Fredholm and `E₂, F₂` are Banach spaces, then `D` is
Fredholm. -/
theorem IsFredholm.of_upperTriangular_right [IsRCLikeNormedField 𝕜]
    [AddCommGroup E₁] [TopologicalSpace E₁] [Module 𝕜 E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [AddCommGroup F₁] [TopologicalSpace F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hM : (A.upperTriangular B D).IsFredholm) (hA : A.IsFredholm) :
    D.IsFredholm :=
  hA.of_shortExact_right hM exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm

section Index

variable [AddCommGroup E₁] [TopologicalSpace E₁] [Module 𝕜 E₁]
variable [AddCommGroup E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
variable [AddCommGroup F₁] [TopologicalSpace F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
variable [AddCommGroup F₂] [TopologicalSpace F₂] [Module 𝕜 F₂]

/-- **Index of an upper-triangular block operator** when `A` and `D` are Fredholm. -/
theorem index_upperTriangular_of_diag (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (hA : A.IsFredholm) (hD : D.IsFredholm) :
    (upperTriangular A B D).index = A.index + D.index :=
  index_eq_add_of_shortExact_left_right (upperTriangular A B D)
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm hA hD

/-- **Index of an upper-triangular block operator** when `A` and the block operator are Fredholm. -/
theorem index_upperTriangular_of_left (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (hA : A.IsFredholm) (hM : (upperTriangular A B D).IsFredholm) :
    (upperTriangular A B D).index = A.index + D.index :=
  index_eq_add_of_shortExact_left_middle (upperTriangular A B D)
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm hA hM

/-- **Index of an upper-triangular block operator** when the block operator and `D` are Fredholm. -/
theorem index_upperTriangular_of_right (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (hM : (upperTriangular A B D).IsFredholm) (hD : D.IsFredholm) :
    (upperTriangular A B D).index = A.index + D.index :=
  index_eq_add_of_shortExact_middle_right (upperTriangular A B D)
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm hM hD

end Index

end UpperTriangularFredholm

/-! ### Composition snake diagram and comparison with `IsFredholm.index_comp` -/

section CompositionSnake

section Ring

variable {𝕜 : Type*} [Ring 𝕜]
variable {E F G : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
variable [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

/-- Target change of coordinates `(y, z) ↦ (z + S y, y)` from `F × G` to `G × F`. -/
def upperTriangularNegIdCodEquiv [IsTopologicalAddGroup G] (S : F →L[𝕜] G) :
    (F × G) ≃L[𝕜] (G × F) :=
  ContinuousLinearEquiv.equivOfInverse
    ((snd 𝕜 F G + S.comp (fst 𝕜 F G)).prod (fst 𝕜 F G))
    ((snd 𝕜 G F).prod (fst 𝕜 G F - S.comp (snd 𝕜 G F)))
    (fun ⟨_, _⟩ ↦ by simp) (fun ⟨_, _⟩ ↦ by simp)

@[simp]
theorem upperTriangularNegIdCodEquiv_apply [IsTopologicalAddGroup G] (S : F →L[𝕜] G)
    (y : F) (z : G) :
    upperTriangularNegIdCodEquiv S (y, z) = (z + S y, y) := (rfl)

@[simp]
theorem upperTriangularNegIdCodEquiv_symm_apply [IsTopologicalAddGroup G] (S : F →L[𝕜] G)
    (z : G) (y : F) :
    (upperTriangularNegIdCodEquiv S).symm (z, y) = (y, z - S y) := (rfl)

variable [IsTopologicalAddGroup F]

/-- Source change of coordinates `(x, y) ↦ (x, y + T x)` on `E × F`. -/
def upperTriangularNegIdDomEquiv (T : E →L[𝕜] F) : (E × F) ≃L[𝕜] (E × F) :=
  ContinuousLinearEquiv.equivOfInverse
    ((fst 𝕜 E F).prod (snd 𝕜 E F + T.comp (fst 𝕜 E F)))
    ((fst 𝕜 E F).prod (snd 𝕜 E F - T.comp (fst 𝕜 E F)))
    (fun ⟨_, _⟩ ↦ by simp) (fun ⟨_, _⟩ ↦ by simp)

@[simp]
theorem upperTriangularNegIdDomEquiv_apply (T : E →L[𝕜] F) (x : E) (y : F) :
    upperTriangularNegIdDomEquiv T (x, y) = (x, y + T x) := (rfl)

@[simp]
theorem upperTriangularNegIdDomEquiv_symm_apply (T : E →L[𝕜] F) (x : E) (y : F) :
    (upperTriangularNegIdDomEquiv T).symm (x, y) = (x, y - T x) := (rfl)

/-- **Diagonalization of the composition snake operator:** conjugating
`upperTriangular T (-id 𝕜 F) S` by the triangular coordinate equivalences yields
`(S ∘L T).prodMap (-id 𝕜 F)`. -/
theorem upperTriangularNegIdCodEquiv_comp_upperTriangular_comp_domEquiv [IsTopologicalAddGroup G]
    (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    ((upperTriangularNegIdCodEquiv S : F × G →L[𝕜] G × F).comp
      (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S)).comp
      (upperTriangularNegIdDomEquiv T : E × F →L[𝕜] E × F) =
      (S.comp T).prodMap (-ContinuousLinearMap.id 𝕜 F) :=
  ContinuousLinearMap.ext fun ⟨_, _⟩ ↦ by simp [map_add]

/-- Identification of the kernel of `upperTriangular T (-id 𝕜 F) S` with `ker (S ∘L T)`,
sending `(x, y)` to `x` with inverse `x ↦ (x, T x)`. -/
def kerUpperTriangularNegIdEquiv (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).ker ≃L[𝕜]
      (S.toLinearMap ∘ₗ T.toLinearMap).ker :=
  ContinuousLinearEquiv.equivOfInverse
    (((fst 𝕜 E F).comp (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).ker.subtypeL).codRestrict
      (S.toLinearMap ∘ₗ T.toLinearMap).ker fun ⟨⟨x, y⟩, h⟩ ↦ by
        rw [LinearMap.mem_ker] at h ⊢
        have h1 : T x - y = 0 := by simpa [sub_eq_add_neg] using congrArg Prod.fst h
        have hy : y = T x := (sub_eq_zero.1 h1).symm
        simpa [hy] using congrArg Prod.snd h)
    ((((ContinuousLinearMap.id 𝕜 E).prod T).comp
        (S.toLinearMap ∘ₗ T.toLinearMap).ker.subtypeL).codRestrict
      (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).ker fun ⟨x, hx⟩ ↦ by
        rw [LinearMap.mem_ker] at hx ⊢
        refine Prod.ext ?_ hx
        simp only [coe_coe, comp_apply, Submodule.subtypeL_apply, prod_apply, id_apply,
          upperTriangular_apply, neg_apply, add_neg_cancel, Prod.fst_zero])
    (fun ⟨⟨x, y⟩, h⟩ ↦ by
      apply Subtype.ext
      have h1 : T x - y = 0 := by simpa [sub_eq_add_neg] using congrArg Prod.fst h
      exact Prod.ext rfl (sub_eq_zero.1 h1))
    (fun ⟨_, _⟩ ↦ rfl)

@[simp]
theorem coe_kerUpperTriangularNegIdEquiv_apply (T : E →L[𝕜] F) (S : F →L[𝕜] G)
    (v : (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).ker) :
    (kerUpperTriangularNegIdEquiv T S v : E) = v.1.1 := (rfl)

@[simp]
theorem coe_kerUpperTriangularNegIdEquiv_symm_apply (T : E →L[𝕜] F) (S : F →L[𝕜] G)
    (x : (S.toLinearMap ∘ₗ T.toLinearMap).ker) :
    ((kerUpperTriangularNegIdEquiv T S).symm x : E × F) = (x.1, T x.1) := (rfl)

/-- Identification of the cokernel of `upperTriangular T (-id 𝕜 F) S` with `G ⧸ range (S ∘L T)`,
sending `[(y, z)]` to `[z + S y]` with inverse `[z] ↦ [(0, z)]`. -/
def cokerUpperTriangularNegIdEquiv (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    ((F × G) ⧸ (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).range) ≃ₗ[𝕜]
      (G ⧸ (S.toLinearMap ∘ₗ T.toLinearMap).range) :=
  LinearEquiv.ofLinearMap
    ((upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).range.liftQ
      ((S.toLinearMap ∘ₗ T.toLinearMap).range.mkQ ∘ₗ
        (LinearMap.snd 𝕜 F G + S.toLinearMap ∘ₗ LinearMap.fst 𝕜 F G)) <| by
        rintro _ ⟨⟨x, y⟩, rfl⟩
        rw [LinearMap.mem_ker]
        refine (Submodule.Quotient.mk_eq_zero _).2 ⟨x, ?_⟩
        simp [map_add])
    ((S.toLinearMap ∘ₗ T.toLinearMap).range.liftQ
      ((upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).range.mkQ ∘ₗ LinearMap.inr 𝕜 F G) <| by
        rintro _ ⟨x, rfl⟩
        rw [LinearMap.mem_ker]
        refine (Submodule.Quotient.mk_eq_zero _).2 ⟨(x, T x), ?_⟩
        refine Prod.ext ?_ ?_ <;> simp)
    (Submodule.linearMap_qext _ <| LinearMap.ext fun z ↦ by
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
        LinearMap.inr_apply, LinearMap.add_apply, LinearMap.snd_apply, LinearMap.fst_apply,
        map_zero, add_zero, LinearMap.id_apply])
    (Submodule.linearMap_qext _ <| LinearMap.ext fun ⟨y, z⟩ ↦ by
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
        LinearMap.add_apply, LinearMap.snd_apply, LinearMap.fst_apply, LinearMap.inr_apply,
        LinearMap.id_apply]
      rw [Submodule.Quotient.eq]
      exact ⟨(0, y), Prod.ext (by simp) (by simp)⟩)

@[simp]
theorem cokerUpperTriangularNegIdEquiv_mk (T : E →L[𝕜] F) (S : F →L[𝕜] G) (y : F) (z : G) :
    cokerUpperTriangularNegIdEquiv T S (Submodule.Quotient.mk (y, z)) =
      Submodule.Quotient.mk (z + S y) := (rfl)

@[simp]
theorem cokerUpperTriangularNegIdEquiv_symm_mk (T : E →L[𝕜] F) (S : F →L[𝕜] G) (z : G) :
    (cokerUpperTriangularNegIdEquiv T S).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (0, z) := (rfl)

/-- Under `kerUpperTriangularNegIdEquiv`, the first map of the composition snake sequence is the
inclusion `ker T → ker (S ∘L T)`. -/
theorem kerUpperTriangularNegIdEquiv_comp_kerMapOfComm (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (kerUpperTriangularNegIdEquiv T S).toLinearMap ∘ₗ
      TauCeti.kerMapOfComm (congrArg ContinuousLinearMap.toLinearMap
        (upperTriangular_comp_inl T (-ContinuousLinearMap.id 𝕜 F) S)) =
      Submodule.inclusion (LinearMap.ker_le_ker_comp T.toLinearMap S.toLinearMap) :=
  LinearMap.ext fun _ ↦ Subtype.ext rfl

/-- Under `kerUpperTriangularNegIdEquiv`, the second map of the composition snake sequence is
`LinearMap.kerCompToKer T S`. -/
theorem kerMapOfComm_comp_kerUpperTriangularNegIdEquiv_symm (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    TauCeti.kerMapOfComm (congrArg ContinuousLinearMap.toLinearMap
      (snd_comp_upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).symm) ∘ₗ
      (kerUpperTriangularNegIdEquiv T S).symm.toLinearMap =
      T.toLinearMap.kerCompToKer S.toLinearMap :=
  LinearMap.ext fun x ↦ Subtype.ext
    (LinearMap.coe_kerCompToKer_apply T.toLinearMap S.toLinearMap x).symm

/-- The connecting map of the composition snake diagram `upperTriangular T (-id 𝕜 F) S` equals
`-T.toLinearMap.kerToCoker S.toLinearMap`. -/
theorem toLinearMap_snakeDeltaL_upperTriangular_neg_id (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (TauCeti.snakeDeltaL (i := inl 𝕜 E F) (p := snd 𝕜 E F)
      (j := inl 𝕜 F G) (q := snd 𝕜 F G)
      (T₁ := T) (T₂ := upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S) (T₃ := S)
      exact_inl_snd exact_inl_snd
      ⟨inr 𝕜 E F, by intro _; simp⟩ ⟨fst 𝕜 F G, by intro _; simp⟩
      (upperTriangular_comp_inl T (-ContinuousLinearMap.id 𝕜 F) S)
      (snd_comp_upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).symm).toLinearMap =
      -(T.toLinearMap.kerToCoker S.toLinearMap) := by
  rw [snakeDeltaL_upperTriangular]
  ext y
  simp

/-- Under `cokerUpperTriangularNegIdEquiv`, the fourth map of the composition snake sequence is
`LinearMap.cokerToCokerComp T S`. -/
theorem cokerUpperTriangularNegIdEquiv_comp_cokerMapOfComm (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (cokerUpperTriangularNegIdEquiv T S).toLinearMap ∘ₗ
      TauCeti.cokerMapOfComm (congrArg ContinuousLinearMap.toLinearMap
        (upperTriangular_comp_inl T (-ContinuousLinearMap.id 𝕜 F) S)) =
      T.toLinearMap.cokerToCokerComp S.toLinearMap :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun y ↦
    (congrArg (Submodule.Quotient.mk (p := (S.toLinearMap ∘ₗ T.toLinearMap).range))
      (zero_add (S y))).trans
      (LinearMap.cokerToCokerComp_mk T.toLinearMap S.toLinearMap y).symm

/-- Under `cokerUpperTriangularNegIdEquiv`, the fifth map of the composition snake sequence is
`Submodule.factor (range_comp_le_range T S)`. -/
theorem cokerMapOfComm_comp_cokerUpperTriangularNegIdEquiv_symm (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    TauCeti.cokerMapOfComm (congrArg ContinuousLinearMap.toLinearMap
      (snd_comp_upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).symm) ∘ₗ
      (cokerUpperTriangularNegIdEquiv T S).symm.toLinearMap =
      Submodule.factor (LinearMap.range_comp_le_range T.toLinearMap S.toLinearMap) :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun _ ↦ rfl

/-- The index of `upperTriangular T (-id 𝕜 F) S` unconditionally equals `(S ∘L T).index`. -/
theorem index_upperTriangular_neg_id (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).index = (S.comp T).index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub, toLinearMap_comp,
    (kerUpperTriangularNegIdEquiv T S).toLinearEquiv.finrank_eq,
    (cokerUpperTriangularNegIdEquiv T S).finrank_eq]

end Ring

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
variable [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

/-- The composition snake operator `upperTriangular T (-id 𝕜 F) S` is Fredholm if and only if
`S ∘L T` is Fredholm. -/
theorem isFredholm_upperTriangular_neg_id_iff [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    [IsTopologicalAddGroup G] (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).IsFredholm ↔ (S.comp T).IsFredholm := by
  have hconj := isFredholm_iff_of_comp_eq
    (T := upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S)
    (S := (S.comp T).prodMap (-ContinuousLinearMap.id 𝕜 F))
    (upperTriangularNegIdDomEquiv T).symm (upperTriangularNegIdCodEquiv S) (by
      rw [← upperTriangularNegIdCodEquiv_comp_upperTriangular_comp_domEquiv T S]
      exact ContinuousLinearMap.ext fun ⟨_, _⟩ ↦ by simp)
  rw [hconj, isFredholm_prodMap_iff]
  have hneg : (-ContinuousLinearMap.id 𝕜 F).IsFredholm :=
    (ContinuousLinearEquiv.refl 𝕜 F).isFredholm.neg
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hneg⟩⟩

/-- **Composition index additivity (composite and left factor Fredholm):**
if `S ∘L T` and `S` are Fredholm, then `(S ∘L T).index = S.index + T.index`. Compare with
`ContinuousLinearMap.IsFredholm.index_comp`, which assumes `S` and `T` are Fredholm. -/
theorem IsFredholm.index_comp_of_left {T : E →L[𝕜] F} {S : F →L[𝕜] G}
    (hST : (S.comp T).IsFredholm) (hS : S.IsFredholm) :
    (S.comp T).index = S.index + T.index := by
  have : FiniteDimensional 𝕜 (S.toLinearMap ∘ₗ T.toLinearMap).ker := hST.finite_ker
  have : FiniteDimensional 𝕜 (G ⧸ (S.toLinearMap ∘ₗ T.toLinearMap).range) := hST.finite_coker
  have := hS.finite_ker; have := hS.finite_coker
  have : FiniteDimensional 𝕜 T.ker :=
    Module.Finite.of_injective _ (Submodule.inclusion_injective
      (LinearMap.ker_le_ker_comp T.toLinearMap S.toLinearMap))
  have : FiniteDimensional 𝕜 (F ⧸ T.range) :=
    TauCeti.finiteDimensional_of_exact (LinearMap.exact_kerToCoker_cokerToCokerComp T.toLinearMap
      S.toLinearMap)
  rw [index_def, index_def, index_def]
  exact LinearMap.index_comp S.toLinearMap T.toLinearMap

/-- **Composition index additivity (composite and right factor Fredholm):**
if `S ∘L T` and `T` are Fredholm, then `(S ∘L T).index = S.index + T.index`. -/
theorem IsFredholm.index_comp_of_right {T : E →L[𝕜] F} {S : F →L[𝕜] G}
    (hST : (S.comp T).IsFredholm) (hT : T.IsFredholm) :
    (S.comp T).index = S.index + T.index := by
  have : FiniteDimensional 𝕜 (S.toLinearMap ∘ₗ T.toLinearMap).ker := hST.finite_ker
  have : FiniteDimensional 𝕜 (G ⧸ (S.toLinearMap ∘ₗ T.toLinearMap).range) := hST.finite_coker
  have := hT.finite_ker; have := hT.finite_coker
  have : FiniteDimensional 𝕜 S.ker :=
    TauCeti.finiteDimensional_of_exact (LinearMap.exact_kerCompToKer_kerToCoker T.toLinearMap
      S.toLinearMap)
  have : FiniteDimensional 𝕜 (G ⧸ S.range) :=
    Module.Finite.of_surjective _ (Submodule.factor_surjective
      (LinearMap.range_comp_le_range T.toLinearMap S.toLinearMap))
  rw [index_def, index_def, index_def]
  exact LinearMap.index_comp S.toLinearMap T.toLinearMap

end NormedField

end CompositionSnake

end ContinuousLinearMap
