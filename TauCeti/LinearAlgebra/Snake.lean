/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.Algebra.Module.SnakeLemma
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.LinearAlgebra.Exact

import Mathlib.Algebra.Module.ULift

/-!
# Algebraic snake sequence and index additivity for linear maps

Given a commuting morphism `(T₀, T₁, T₂)` between exact sequences `E₀ --i--> E₁ --p--> E₂ → 0`
and `0 → F₀ --j--> F₁ --q--> F₂` of modules over an arbitrary ring `R`, this file constructs the
six-term kernel–cokernel exact sequence across arbitrary universes via
`CategoryTheory.ShortComplex.moduleCatSnakeInput` and `ULift`. Working through `ModuleCat` avoids
commutativity of `R`, yielding two-out-of-three finiteness and index additivity
`T₁.index = T₀.index + T₂.index` over any division ring; over a commutative ring,
`LinearMap.snakeConnecting_eq_snakeLemma_δ'` identifies `LinearMap.snakeConnecting` with
`SnakeLemma.δ'`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 1.3.
-/

public section

open CategoryTheory Module

namespace LinearMap

section Maps

variable {R E E' F F' : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']
  [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
  {T : E →ₗ[R] F} {T' : E' →ₗ[R] F'}

/-- Canonical kernel restriction `ker T → ker T'` induced by `g ∘ T = T' ∘ f`. -/
def snakeKerMap (f : E →ₗ[R] E') {g : F →ₗ[R] F'} (h : g ∘ₗ T = T' ∘ₗ f) : T.ker →ₗ[R] T'.ker :=
  f.restrict fun x hx ↦ mem_ker.mpr <| by
    rw [← comp_apply, ← h, comp_apply, mem_ker.mp hx, map_zero]

/-- Evaluating `snakeKerMap` in the ambient module applies the horizontal map. -/
@[simp]
lemma coe_snakeKerMap_apply (f : E →ₗ[R] E') {g : F →ₗ[R] F'} (h : g ∘ₗ T = T' ∘ₗ f)
    (x : T.ker) : (snakeKerMap f h x : E') = f x := (rfl)

/-- Canonical cokernel map `F ⧸ range T → F' ⧸ range T'` induced by `g ∘ T = T' ∘ f`. -/
def snakeCokerMap {f : E →ₗ[R] E'} (g : F →ₗ[R] F') (h : g ∘ₗ T = T' ∘ₗ f) :
    (F ⧸ T.range) →ₗ[R] (F' ⧸ T'.range) :=
  T.range.mapQ T'.range g fun _ ⟨x, hx⟩ ↦ ⟨f x, by rw [← hx, ← comp_apply, ← h, comp_apply]⟩

/-- Evaluating `snakeCokerMap` on a quotient class applies the horizontal map. -/
@[simp]
lemma snakeCokerMap_mk {f : E →ₗ[R] E'} (g : F →ₗ[R] F') (h : g ∘ₗ T = T' ∘ₗ f) (y : F) :
    snakeCokerMap g h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (g y) := (rfl)

end Maps

section AlgebraicSnake

universe u₀ u₁ u₂ u₃ u₄ u₅ u₆ w

private def uliftMap {R : Type u₀} [Ring R] {M : Type u₁} {N : Type u₂}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    ULift.{w} M →ₗ[R] ULift.{w} N :=
  (ULift.moduleEquiv.{u₀, u₂, w} (R := R) (M := N)).symm.toLinearMap ∘ₗ f ∘ₗ
    (ULift.moduleEquiv.{u₀, u₁, w} (R := R) (M := M)).toLinearMap

private lemma uliftMap_exact {R : Type u₀} [Ring R] {M : Type u₁} {N : Type u₂} {P : Type u₃}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P} (h : Function.Exact f g) :
    Function.Exact (uliftMap.{u₀, u₁, u₂, w} f) (uliftMap.{u₀, u₂, u₃, w} g) := fun x ↦ by
  simp only [uliftMap, comp_apply, LinearEquiv.coe_coe, EmbeddingLike.map_eq_zero_iff,
    Set.mem_range, ULift.moduleEquiv_apply]
  rw [h x.down]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨ULift.up a, congrArg ULift.up ha⟩,
    fun ⟨a, ha⟩ ↦ ⟨a.down, congrArg ULift.down ha⟩⟩

private lemma uliftMap_surjective {R : Type u₀} [Ring R] {M : Type u₁} {N : Type u₂}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Surjective (uliftMap.{u₀, u₁, u₂, w} f) := fun z ↦
  let ⟨y, hy⟩ := hf z.down; ⟨ULift.up y, congrArg ULift.up hy⟩

private lemma uliftMap_injective {R : Type u₀} [Ring R] {M : Type u₁} {N : Type u₂}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N} (hf : Function.Injective f) :
    Function.Injective (uliftMap.{u₀, u₁, u₂, w} f) :=
  fun _ _ hab ↦ ULift.ext (hf (congrArg ULift.down hab))

private lemma uliftMap_comp_eq {R : Type u₀} [Ring R]
    {M : Type u₁} {N : Type u₂} {P : Type u₃} {Q : Type u₄}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {f₁ : M →ₗ[R] N} {g₁ : N →ₗ[R] Q} {f₂ : M →ₗ[R] P} {g₂ : P →ₗ[R] Q}
    (h : g₁ ∘ₗ f₁ = g₂ ∘ₗ f₂) :
    uliftMap.{u₀, u₂, u₄, w} g₁ ∘ₗ uliftMap.{u₀, u₁, u₂, w} f₁ =
      uliftMap.{u₀, u₃, u₄, w} g₂ ∘ₗ uliftMap.{u₀, u₁, u₃, w} f₂ :=
  LinearMap.ext fun x ↦ ULift.ext (LinearMap.congr_fun h x.down)

variable {R : Type u₀} [Ring R]
  {E₀ : Type u₁} {E₁ : Type u₂} {E₂ : Type u₃} {F₀ : Type u₄} {F₁ : Type u₅} {F₂ : Type u₆}
  [AddCommGroup E₀] [Module R E₀] [AddCommGroup E₁] [Module R E₁] [AddCommGroup E₂] [Module R E₂]
  [AddCommGroup F₀] [Module R F₀] [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₂] [Module R F₂]
  {i : E₀ →ₗ[R] E₁} {p : E₁ →ₗ[R] E₂} {j : F₀ →ₗ[R] F₁} {q : F₁ →ₗ[R] F₂}
  {T₀ : E₀ →ₗ[R] F₀} {T₁ : E₁ →ₗ[R] F₁} {T₂ : E₂ →ₗ[R] F₂}

private def uliftFromCoker (T₀ : E₀ →ₗ[R] F₀) :
    (ULift.{w} F₀ ⧸ (uliftMap.{u₀, u₁, u₄, w} T₀).range) →ₗ[R] (F₀ ⧸ T₀.range) :=
  Submodule.mapQ _ T₀.range (ULift.moduleEquiv.{u₀, u₄, w} (R := R) (M := F₀)).toLinearMap
    fun _ ⟨x, hx⟩ ↦ ⟨x.down, congrArg ULift.down hx⟩

section Connecting

variable (hip : Function.Exact i p) (hp : Function.Surjective p)
  (hj : Function.Injective j) (hjq : Function.Exact j q)
  (h₁ : j ∘ₗ T₀ = T₁ ∘ₗ i) (h₂ : q ∘ₗ T₁ = T₂ ∘ₗ p)

include hip hp hj hjq h₁ h₂

private noncomputable def uliftSnakeInput :
    ShortComplex.SnakeInput (ModuleCat.{max u₁ u₂ u₃ u₄ u₅ u₆} R) :=
  ShortComplex.moduleCatSnakeInput
    (uliftMap_exact.{u₀, u₁, u₂, u₃, max u₁ u₂ u₃ u₄ u₅ u₆} hip)
    (uliftMap_surjective.{u₀, u₂, u₃, max u₁ u₂ u₃ u₄ u₅ u₆} hp)
    (uliftMap_injective.{u₀, u₄, u₅, max u₁ u₂ u₃ u₄ u₅ u₆} hj)
    (uliftMap_exact.{u₀, u₄, u₅, u₆, max u₁ u₂ u₃ u₄ u₅ u₆} hjq)
    (uliftMap_comp_eq.{u₀, u₁, u₄, u₂, u₅, max u₁ u₂ u₃ u₄ u₅ u₆} h₁)
    (uliftMap_comp_eq.{u₀, u₂, u₅, u₃, u₆, max u₁ u₂ u₃ u₄ u₅ u₆} h₂)

/-- Canonical algebraic connecting homomorphism `ker T₂ →ₗ[R] F₀ ⧸ range T₀` of the snake lemma,
constructed from Mathlib's `ShortComplex.SnakeInput.δ` via `ULift`. -/
noncomputable def snakeConnecting : T₂.ker →ₗ[R] (F₀ ⧸ T₀.range) :=
  let S := uliftSnakeInput hip hp hj hjq h₁ h₂
  let toKer : T₂.ker →ₗ[R] S.L₀.X₃ :=
    (ULift.moduleEquiv (R := R) (M := E₂)).symm.toLinearMap.restrict fun _ hx ↦
      mem_ker.mpr (congrArg ULift.up (mem_ker.mp hx))
  uliftFromCoker.{u₀, u₁, u₄, max u₁ u₂ u₃ u₄ u₅ u₆} T₀ ∘ₗ S.δ.hom ∘ₗ toKer

/-- **Zigzag characterization of `LinearMap.snakeConnecting`**: if `p x₁ = x₂` and
`j y₀ = T₁ x₁`, then `snakeConnecting` maps `x₂` to `[y₀]` in `F₀ ⧸ range T₀`. -/
theorem snakeConnecting_apply_eq_mk
    (x₂ : T₂.ker) {x₁ : E₁} (hx₁ : p x₁ = x₂) {y₀ : F₀} (hy₀ : j y₀ = T₁ x₁) :
    snakeConnecting hip hp hj hjq h₁ h₂ x₂ = Submodule.Quotient.mk y₀ :=
  congrArg (uliftFromCoker.{u₀, u₁, u₄, max u₁ u₂ u₃ u₄ u₅ u₆} T₀) <|
    ShortComplex.moduleCatSnakeInput_δ_apply
      (uliftMap_exact.{u₀, u₁, u₂, u₃, max u₁ u₂ u₃ u₄ u₅ u₆} hip)
      (uliftMap_surjective.{u₀, u₂, u₃, max u₁ u₂ u₃ u₄ u₅ u₆} hp)
      (uliftMap_injective.{u₀, u₄, u₅, max u₁ u₂ u₃ u₄ u₅ u₆} hj)
      (uliftMap_exact.{u₀, u₄, u₅, u₆, max u₁ u₂ u₃ u₄ u₅ u₆} hjq)
      (uliftMap_comp_eq.{u₀, u₁, u₄, u₂, u₅, max u₁ u₂ u₃ u₄ u₅ u₆} h₁)
      (uliftMap_comp_eq.{u₀, u₂, u₅, u₃, u₆, max u₁ u₂ u₃ u₄ u₅ u₆} h₂)
      ⟨ULift.up x₂.1, congrArg ULift.up x₂.2⟩ (x₁ := ULift.up x₁) (congrArg ULift.up hx₁)
      (y₀ := ULift.up y₀) (congrArg ULift.up hy₀)

/-- Uniqueness of `snakeConnecting`: any linear map satisfying the zigzag formula equals it. -/
theorem eq_snakeConnecting_of_zigzag (δ : T₂.ker →ₗ[R] (F₀ ⧸ T₀.range))
    (hδ : ∀ (x₂ : T₂.ker) (x₁ : E₁) (y₀ : F₀),
      p x₁ = x₂ → j y₀ = T₁ x₁ → δ x₂ = Submodule.Quotient.mk y₀) :
    δ = snakeConnecting hip hp hj hjq h₁ h₂ := by
  ext x₂
  obtain ⟨x₁, hx₁⟩ := hp x₂.1
  obtain ⟨y₀, hy₀⟩ := (hjq (T₁ x₁)).mp (by rw [← comp_apply, h₂, comp_apply, hx₁, mem_ker.mp x₂.2])
  rw [hδ x₂ x₁ y₀ hx₁ hy₀, snakeConnecting_apply_eq_mk hip hp hj hjq h₁ h₂ x₂ hx₁ hy₀]

/-- Exactness at `ker T₂`: `ker T₁ → ker T₂ → F₀ ⧸ range T₀`, transported from
`ShortComplex.SnakeInput.L₁'_exact`. -/
theorem exact_snakeKerMap_snakeConnecting :
    Function.Exact (snakeKerMap p h₂) (snakeConnecting hip hp hj hjq h₁ h₂) := fun x₂ ↦ by
  let S := uliftSnakeInput hip hp hj hjq h₁ h₂
  have hmem := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp S.L₁'_exact
    ⟨ULift.up x₂.1, congrArg ULift.up x₂.2⟩
  refine ⟨fun hδ ↦ ?_, fun ⟨x₁, hx₁⟩ ↦
    hx₁ ▸ snakeConnecting_apply_eq_mk hip hp hj hjq h₁ h₂ _ rfl (y₀ := 0)
      (by simp [mem_ker.mp x₁.2])⟩
  have h0 : S.δ.hom ⟨ULift.up x₂.1, congrArg ULift.up x₂.2⟩ = 0 := by
    have hδ' : uliftFromCoker.{u₀, u₁, u₄, max u₁ u₂ u₃ u₄ u₅ u₆} T₀
        (S.δ.hom ⟨ULift.up x₂.1, congrArg ULift.up x₂.2⟩) = 0 := hδ
    induction hz : S.δ.hom ⟨ULift.up x₂.1, congrArg ULift.up x₂.2⟩ using
      Submodule.Quotient.induction_on with | H y =>
    rw [hz] at hδ'
    obtain ⟨x₀, hx₀⟩ :=
      (Submodule.Quotient.mk_eq_zero _).mp (hδ' : Submodule.Quotient.mk y.down = 0)
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨ULift.up x₀, congrArg ULift.up hx₀⟩
  obtain ⟨⟨⟨x₁⟩, hx₁⟩, hx₁eq⟩ := hmem.mp h0
  exact ⟨⟨x₁, congrArg ULift.down hx₁⟩, Subtype.ext (congrArg (fun z ↦ z.1.down) hx₁eq)⟩

/-- Exactness at `F₀ ⧸ range T₀`: `ker T₂ → F₀ ⧸ range T₀ → F₁ ⧸ range T₁`, transported from
`ShortComplex.SnakeInput.L₂'_exact`. -/
theorem exact_snakeConnecting_snakeCokerMap :
    Function.Exact (snakeConnecting hip hp hj hjq h₁ h₂) (snakeCokerMap j h₁) := fun c₀ ↦ by
  let S := uliftSnakeInput hip hp hj hjq h₁ h₂
  induction c₀ using Submodule.Quotient.induction_on with | H y₀ =>
  have hmem := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp S.L₂'_exact
    (Submodule.Quotient.mk (ULift.up y₀))
  constructor
  · intro hc
    obtain ⟨x₁, hx₁⟩ := (Submodule.Quotient.mk_eq_zero _).mp hc
    obtain ⟨⟨⟨x₂⟩, hx₂⟩, hx₂eq⟩ := hmem.mp <|
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨ULift.up x₁, congrArg ULift.up hx₁⟩
    exact ⟨⟨x₂, congrArg ULift.down hx₂⟩,
      congrArg (uliftFromCoker.{u₀, u₁, u₄, max u₁ u₂ u₃ u₄ u₅ u₆} T₀) hx₂eq⟩
  · rintro ⟨x₂, hx₂⟩
    obtain ⟨x₁, hx₁⟩ := hp x₂.1
    obtain ⟨y₀', hy₀'⟩ :=
      (hjq (T₁ x₁)).mp (by rw [← comp_apply, h₂, comp_apply, hx₁, mem_ker.mp x₂.2])
    rw [← hx₂, snakeConnecting_apply_eq_mk hip hp hj hjq h₁ h₂ x₂ hx₁ hy₀', snakeCokerMap_mk, hy₀']
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x₁, rfl⟩

end Connecting

/-- Exactness of the kernel row `ker T₀ → ker T₁ → ker T₂`. -/
theorem exact_snakeKerMap (hip : Function.Exact i p) (hj : Function.Injective j)
    (h₁ : j ∘ₗ T₀ = T₁ ∘ₗ i) (h₂ : q ∘ₗ T₁ = T₂ ∘ₗ p) :
    Function.Exact (snakeKerMap i h₁) (snakeKerMap p h₂) := fun x₁ ↦ by
  refine ⟨fun hx ↦ ?_, fun ⟨x₀, hx₀⟩ ↦ hx₀ ▸ Subtype.ext (hip.apply_apply_eq_zero x₀.1)⟩
  obtain ⟨x₀, hx₀⟩ := (hip x₁.1).mp (congrArg Subtype.val hx)
  exact ⟨⟨x₀, hj <| by rw [← comp_apply, h₁, comp_apply, hx₀, mem_ker.mp x₁.2, map_zero]⟩,
    Subtype.ext hx₀⟩

/-- Exactness of the cokernel row `F₀ ⧸ range T₀ → F₁ ⧸ range T₁ → F₂ ⧸ range T₂`. -/
theorem exact_snakeCokerMap (hp : Function.Surjective p) (hjq : Function.Exact j q)
    (h₁ : j ∘ₗ T₀ = T₁ ∘ₗ i) (h₂ : q ∘ₗ T₁ = T₂ ∘ₗ p) :
    Function.Exact (snakeCokerMap j h₁) (snakeCokerMap q h₂) := fun c₁ ↦ by
  induction c₁ using Submodule.Quotient.induction_on with | H y₁ =>
  constructor
  · intro hc
    obtain ⟨x₂, hx₂⟩ := (Submodule.Quotient.mk_eq_zero _).mp hc
    obtain ⟨x₁, rfl⟩ := hp x₂
    obtain ⟨y₀, hy₀⟩ := (hjq (y₁ - T₁ x₁)).mp
      (by rw [map_sub, ← comp_apply, h₂, comp_apply, hx₂, sub_self])
    exact ⟨Submodule.Quotient.mk y₀,
      (Submodule.Quotient.eq _).mpr ⟨-x₁, by rw [map_neg, hy₀]; abel⟩⟩
  · rintro ⟨c₀, hc₀⟩; rw [← hc₀]
    induction c₀ using Submodule.Quotient.induction_on with | H y₀ =>
    rw [snakeCokerMap_mk, snakeCokerMap_mk, hjq.apply_apply_eq_zero y₀,
      Submodule.Quotient.mk_zero]

/-- Injectivity of `ker T₀ → ker T₁` when `i` is injective. -/
theorem injective_snakeKerMap (hi : Function.Injective i) (h₁ : j ∘ₗ T₀ = T₁ ∘ₗ i) :
    Function.Injective (snakeKerMap i h₁) := fun _ _ h ↦ Subtype.ext (hi (congrArg Subtype.val h))

/-- Surjectivity of `F₁ ⧸ range T₁ → F₂ ⧸ range T₂` when `q` is surjective. -/
theorem surjective_snakeCokerMap (hq : Function.Surjective q) (h₂ : q ∘ₗ T₁ = T₂ ∘ₗ p) :
    Function.Surjective (snakeCokerMap q h₂) := fun c₂ ↦ by
  induction c₂ using Submodule.Quotient.induction_on with | H y₂ =>
  obtain ⟨y₁, rfl⟩ := hq y₂; exact ⟨Submodule.Quotient.mk y₁, rfl⟩

end AlgebraicSnake

section CommRingComparison

variable {R E₀ E₁ E₂ F₀ F₁ F₂ : Type*} [CommRing R]
  [AddCommGroup E₀] [Module R E₀] [AddCommGroup E₁] [Module R E₁] [AddCommGroup E₂] [Module R E₂]
  [AddCommGroup F₀] [Module R F₀] [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₂] [Module R F₂]
  {i : E₀ →ₗ[R] E₁} {p : E₁ →ₗ[R] E₂} {j : F₀ →ₗ[R] F₁} {q : F₁ →ₗ[R] F₂}
  {T₀ : E₀ →ₗ[R] F₀} {T₁ : E₁ →ₗ[R] F₁} {T₂ : E₂ →ₗ[R] F₂}

/-- Over a commutative ring, `LinearMap.snakeConnecting` coincides with `SnakeLemma.δ'`. -/
theorem snakeConnecting_eq_snakeLemma_δ'
    (hip : Function.Exact i p) (hp : Function.Surjective p)
    (hj : Function.Injective j) (hjq : Function.Exact j q)
    (h₁ : j ∘ₗ T₀ = T₁ ∘ₗ i) (h₂ : q ∘ₗ T₁ = T₂ ∘ₗ p) :
    snakeConnecting hip hp hj hjq h₁ h₂ =
      SnakeLemma.δ' T₀ T₁ T₂ i p hip j q hjq h₁ h₂
        T₂.ker.subtype (fun x ↦ ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.2⟩)
        T₀.range.mkQ (fun _ ↦ Submodule.Quotient.mk_eq_zero T₀.range) hp hj :=
  (eq_snakeConnecting_of_zigzag hip hp hj hjq h₁ h₂ _ fun x₂ x₁ y₀ hx₁ hy₀ ↦
    SnakeLemma.δ'_eq T₀ T₁ T₂ i p hip j q hjq h₁ h₂ T₂.ker.subtype _ T₀.range.mkQ _
      hp hj x₂ x₁ hx₁ y₀ hy₀).symm

end CommRingComparison

/-! ### Algebraic two-out-of-three finiteness and index additivity -/

section AlgebraicIndex

variable {𝕜 E₀ E₁ E₂ F₀ F₁ F₂ : Type*} [DivisionRing 𝕜]
  [AddCommGroup E₀] [Module 𝕜 E₀] [AddCommGroup E₁] [Module 𝕜 E₁] [AddCommGroup E₂] [Module 𝕜 E₂]
  [AddCommGroup F₀] [Module 𝕜 F₀] [AddCommGroup F₁] [Module 𝕜 F₁] [AddCommGroup F₂] [Module 𝕜 F₂]
  {i : E₀ →ₗ[𝕜] E₁} {p : E₁ →ₗ[𝕜] E₂} {j : F₀ →ₗ[𝕜] F₁} {q : F₁ →ₗ[𝕜] F₂}
  {T₀ : E₀ →ₗ[𝕜] F₀} {T₁ : E₁ →ₗ[𝕜] F₁} {T₂ : E₂ →ₗ[𝕜] F₂}
  (hi : Function.Injective i) (hip : Function.Exact i p) (hp : Function.Surjective p)
  (hj : Function.Injective j) (hjq : Function.Exact j q) (hq : Function.Surjective q)
  (h₁ : j ∘ₗ T₀ = T₁ ∘ₗ i) (h₂ : q ∘ₗ T₁ = T₂ ∘ₗ p)

include hip hp hj hjq h₁ h₂ in
/-- If `T₀` and `T₂` have finite-dimensional kernels and cokernels, so does `T₁`. -/
theorem finiteDimensional_ker_coker_middle_of_left_right
    [FiniteDimensional 𝕜 T₀.ker] [FiniteDimensional 𝕜 (F₀ ⧸ T₀.range)]
    [FiniteDimensional 𝕜 T₂.ker] [FiniteDimensional 𝕜 (F₂ ⧸ T₂.range)] :
    FiniteDimensional 𝕜 T₁.ker ∧ FiniteDimensional 𝕜 (F₁ ⧸ T₁.range) :=
  ⟨TauCeti.finiteDimensional_of_exact (exact_snakeKerMap hip hj h₁ h₂),
    TauCeti.finiteDimensional_of_exact (exact_snakeCokerMap hp hjq h₁ h₂)⟩

include hi hip hp hj hjq h₁ h₂ in
/-- If `i` is injective, `T₁` has finite-dimensional kernel and cokernel, and `T₂` has
finite-dimensional kernel, then `T₀` has finite-dimensional kernel and cokernel. -/
theorem finiteDimensional_ker_coker_left_of_middle_right
    [FiniteDimensional 𝕜 T₁.ker] [FiniteDimensional 𝕜 (F₁ ⧸ T₁.range)]
    [FiniteDimensional 𝕜 T₂.ker] :
    FiniteDimensional 𝕜 T₀.ker ∧ FiniteDimensional 𝕜 (F₀ ⧸ T₀.range) :=
  ⟨Module.Finite.of_injective (snakeKerMap i h₁) (injective_snakeKerMap hi h₁),
    TauCeti.finiteDimensional_of_exact
      (exact_snakeConnecting_snakeCokerMap hip hp hj hjq h₁ h₂)⟩

include hip hp hj hjq hq h₁ h₂ in
/-- If `q` is surjective, `T₁` has finite-dimensional kernel and cokernel, and `T₀` has
finite-dimensional cokernel, then `T₂` has finite-dimensional kernel and cokernel. -/
theorem finiteDimensional_ker_coker_right_of_left_middle
    [FiniteDimensional 𝕜 (F₀ ⧸ T₀.range)]
    [FiniteDimensional 𝕜 T₁.ker] [FiniteDimensional 𝕜 (F₁ ⧸ T₁.range)] :
    FiniteDimensional 𝕜 T₂.ker ∧ FiniteDimensional 𝕜 (F₂ ⧸ T₂.range) :=
  ⟨TauCeti.finiteDimensional_of_exact
      (exact_snakeKerMap_snakeConnecting hip hp hj hjq h₁ h₂),
    Module.Finite.of_surjective (snakeCokerMap q h₂) (surjective_snakeCokerMap hq h₂)⟩

include hi hip hp hj hjq hq h₁ h₂ in
/-- **Algebraic index additivity along a short exact sequence**: over any division ring, if
`(T₀, T₁, T₂)` is a morphism of short exact sequences with finite-dimensional `ker T₁`, `ker T₂`,
`F₀ ⧸ range T₀`, and `F₁ ⧸ range T₁` (which automatically forces `ker T₀` and `F₂ ⧸ range T₂` to
be finite-dimensional), then `T₁.index = T₀.index + T₂.index`. -/
theorem index_eq_add_of_exact
    [FiniteDimensional 𝕜 (F₀ ⧸ T₀.range)]
    [FiniteDimensional 𝕜 T₁.ker] [FiniteDimensional 𝕜 (F₁ ⧸ T₁.range)]
    [FiniteDimensional 𝕜 T₂.ker] :
    T₁.index = T₀.index + T₂.index := by
  let f₀ := snakeKerMap i h₁; let g₀ := snakeKerMap p h₂
  let δ := snakeConnecting hip hp hj hjq h₁ h₂
  let f₃ := snakeCokerMap j h₁; let g₃ := snakeCokerMap q h₂
  have h0 : finrank 𝕜 T₀.ker = finrank 𝕜 f₀.range :=
    (LinearMap.finrank_range_of_inj (injective_snakeKerMap hi h₁)).symm
  have h1 := f₀.finrank_eq_finrank_range_add_finrank_range_of_exact g₀
    (exact_snakeKerMap hip hj h₁ h₂)
  have h2 := g₀.finrank_eq_finrank_range_add_finrank_range_of_exact δ
    (exact_snakeKerMap_snakeConnecting hip hp hj hjq h₁ h₂)
  have h3 := δ.finrank_eq_finrank_range_add_finrank_range_of_exact f₃
    (exact_snakeConnecting_snakeCokerMap hip hp hj hjq h₁ h₂)
  have h4 := f₃.finrank_eq_finrank_range_add_finrank_range_of_exact g₃
    (exact_snakeCokerMap hp hjq h₁ h₂)
  have h5 : finrank 𝕜 (F₂ ⧸ T₂.range) = finrank 𝕜 g₃.range := by
    rw [LinearMap.range_eq_top.mpr (surjective_snakeCokerMap hq h₂), finrank_top]
  rw [index_eq_finrank_sub, index_eq_finrank_sub, index_eq_finrank_sub]; omega

end AlgebraicIndex

end LinearMap
