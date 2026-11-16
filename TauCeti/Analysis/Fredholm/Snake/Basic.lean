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
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

import Mathlib.Algebra.Module.ULift
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Abel
import TauCeti.Topology.Algebra.Module.Complement

/-!
# Categorical and topological snake sequences

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

## Main definitions

* `TauCeti.kerMapOfComm`, `TauCeti.cokerMapOfComm`: algebraic maps induced on kernels and cokernels
  by a commuting square.
* `TauCeti.snakeInput`: a `CategoryTheory.ShortComplex.SnakeInput (ModuleCat 𝕜)` with concrete
  kernel and cokernel rows `L₀` and `L₃`.
* `TauCeti.snakeDelta`: the universe-polymorphic connecting map `T₃.ker →ₗ[𝕜] (F₁ ⧸ T₁.range)`.
* `TauCeti.kerMapLOfComm`, `TauCeti.cokerMapLOfComm`, `TauCeti.snakeDeltaL`: the continuous linear
  maps in the six-term snake sequence.

## Main results

* `TauCeti.snakeInput_composableArrows_exact`, `TauCeti.exact_kerMapOfComm_snakeDelta`,
  `TauCeti.exact_snakeDelta_cokerMapOfComm`, `TauCeti.bijective_snakeDelta_of_bijective`: exactness
  of the six-term snake sequence and bijectivity of `δ` when `T₂` is bijective.
* `TauCeti.snakeDelta_eq`, `TauCeti.continuous_snakeDelta`, `TauCeti.snakeDeltaL_eq_comp`,
  `TauCeti.mkQL_comp_retract_comp_section_eq`: elementwise formula, continuity and
  splitting-independence of `δ`.
* `TauCeti.exists_topologicalSplitting_of_shortExact`,
  `TauCeti.exists_topologicalSplitting_of_shortExact_hilbert`,
  `TauCeti.continuous_snakeDelta_hilbert`: topological splitting of Banach (complemented kernel)
  and Hilbert short exact sequences, and automatic continuity of `δ` for Hilbert spaces.
-/

public section

open CategoryTheory CategoryTheory.Limits Function

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

end TauCeti
