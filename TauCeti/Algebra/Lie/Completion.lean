/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Quotient
public import TauCeti.Algebra.Lie.Quotient

/-!
# Completions along decreasing Lie ideals

The module limit of the quotients by a decreasing sequence of Lie ideals carries
its quotient-wise Lie bracket. Its projections are Lie homomorphisms and satisfy
the universal property for compatible families of Lie homomorphisms. The canonical
map sends an element to its quotient classes. No separatedness or nilpotence is
required.

The carrier is the existing `TauCeti.ModuleTower.lim`, retaining its module and
topological structures. The quotient terms are accessed through their universal
property, so the construction does not depend on the implementation of the tower.

Adapted from `Mei/Algebra/Lie/Completion/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

namespace LieIdeal

open TauCeti

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (I : ℕ → LieIdeal R L) (hI : Antitone I)

local notation "Js" => (fun k : ℕ => LieSubmodule.toSubmodule (I k))
local notation "hs" => (fun a b h =>
  Iff.mpr (LieSubmodule.toSubmodule_le_toSubmodule _ _) (hI h))

/-- The completion along a decreasing sequence of Lie ideals, on the module limit carrier. -/
abbrev completion := (ModuleTower.quotients Js hs).lim

/-- The module quotient term is canonically the corresponding Lie quotient. -/
private noncomputable def quotientEquiv (k : ℕ) :
    (ModuleTower.quotients Js hs).obj (Opposite.op k) ≃ₗ[R] L ⧸ I k :=
  ModuleTower.quotientsLiftEquiv Js hs k (I k).toSubmodule.mkQ
    (Submodule.ker_mkQ _) (Submodule.mkQ_surjective _)

private theorem quotientEquiv_π (k : ℕ) (x : L) :
    quotientEquiv I hI k (ModuleTower.quotientsπ Js hs k x) = LieSubmodule.Quotient.mk x := by
  exact ModuleTower.quotientsLiftEquiv_quotientsπ _ _ _ _ _ _ x

private theorem quotientEquiv_transition {k l : ℕ} (h : k ≤ l)
    (x : (ModuleTower.quotients Js hs).obj (Opposite.op l)) :
    quotientEquiv I hI k ((ModuleTower.quotients Js hs).transitionOfLE h x) =
      LieIdeal.factor (hI h) (quotientEquiv I hI l x) := by
  obtain ⟨x, rfl⟩ := ModuleTower.quotientsπ_surjective Js hs l x
  have ht := ModuleTower.transitionOfLE_quotientsπ Js hs h x
  calc
    _ = quotientEquiv I hI k (ModuleTower.quotientsπ _ _ k x) := congrArg _ ht
    _ = LieSubmodule.Quotient.mk x := quotientEquiv_π I hI k x
    _ = _ := by rw [quotientEquiv_π, LieIdeal.factor_apply]

private noncomputable def projectionLinear (k : ℕ) : completion I hI →ₗ[R] L ⧸ I k :=
  (quotientEquiv I hI k).toLinearMap.comp ((ModuleTower.quotients Js hs).limπ k)

private theorem factor_projectionLinear {k l : ℕ} (h : k ≤ l) (x : completion I hI) :
    LieIdeal.factor (hI h) (projectionLinear I hI l x) = projectionLinear I hI k x := by
  simpa only [projectionLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ModuleTower.limπ_apply, ModuleTower.transitionOfLE_coe_lim] using
    (quotientEquiv_transition I hI h
      (((ModuleTower.quotients _ hs).limπ l) x)).symm

private theorem completion_ext_aux {x y : completion I hI}
    (h : ∀ k, projectionLinear I hI k x = projectionLinear I hI k y) : x = y :=
  ModuleTower.lim_ext _ fun k => (quotientEquiv I hI k).injective (h k)

/-- The bracket of two compatible families is their quotient-wise bracket. -/
noncomputable instance completionBracket : Bracket (completion I hI) (completion I hI) := by
  let q (k : ℕ) :
      (ModuleTower.quotients Js hs).obj (Opposite.op k) ≃ₗ[R] L ⧸ I k :=
    ModuleTower.quotientsLiftEquiv Js hs k (I k).toSubmodule.mkQ
      (Submodule.ker_mkQ _) (Submodule.mkQ_surjective _)
  exact ⟨fun x y => ⟨fun k => (q k).symm
    ⁅q k ((ModuleTower.quotients _ _).limπ k x),
     q k ((ModuleTower.quotients _ _).limπ k y)⁆,
    (ModuleTower.mem_lim _).mpr (by
      intro k
      apply (q k).injective
      rw [← ModuleTower.transitionOfLE_succ]
      have ht (z) : q k ((ModuleTower.quotients _ _).transitionOfLE
          (Nat.le_succ k) z) = LieIdeal.factor (hI (Nat.le_succ k)) (q (k + 1) z) :=
        quotientEquiv_transition I hI (Nat.le_succ k) z
      simp only [LinearEquiv.apply_symm_apply]
      rw [ht, LinearEquiv.apply_symm_apply, LieHom.map_lie]
      have hx := factor_projectionLinear I hI (Nat.le_succ k) x
      have hy := factor_projectionLinear I hI (Nat.le_succ k) y
      exact congrArg₂ Bracket.bracket hx hy)⟩⟩

private theorem projectionLinear_bracket (k : ℕ) (x y : completion I hI) :
    projectionLinear I hI k ⁅x, y⁆ =
      ⁅projectionLinear I hI k x, projectionLinear I hI k y⁆ := by
  simp only [projectionLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ModuleTower.limπ_apply]
  -- The bracket instance stores the quotient-wise family as a subtype value.
  change quotientEquiv I hI k ((quotientEquiv I hI k).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  simp only [quotientEquiv, ModuleTower.limπ_apply]

noncomputable instance completionLieRing : LieRing (completion I hI) where
  add_lie x y z := by
    apply completion_ext_aux I hI
    intro k
    simp only [map_add, projectionLinear_bracket, add_lie]
  lie_add x y z := by
    apply completion_ext_aux I hI
    intro k
    simp only [map_add, projectionLinear_bracket, lie_add]
  lie_self x := by
    apply completion_ext_aux I hI
    intro k
    simp only [map_zero, projectionLinear_bracket, lie_self]
  leibniz_lie x y z := by
    apply completion_ext_aux I hI
    intro k
    simp only [map_add, projectionLinear_bracket]
    exact leibniz_lie _ _ _

noncomputable instance completionLieAlgebra : LieAlgebra R (completion I hI) where
  lie_smul r x y := by
    apply completion_ext_aux I hI
    intro k
    simp only [map_smul, projectionLinear_bracket, lie_smul]

/-- Projection of the completion to a Lie quotient. -/
noncomputable def completionProjection (k : ℕ) : completion I hI →ₗ⁅R⁆ L ⧸ I k where
  __ := projectionLinear I hI k
  map_lie' := projectionLinear_bracket I hI k _ _

/-- Completed Lie elements are determined by their quotient projections. -/
@[ext]
theorem completion_ext {x y : completion I hI}
    (h : ∀ k, completionProjection I hI k x = completionProjection I hI k y) : x = y :=
  completion_ext_aux I hI h

/-- Quotient representatives compute the module projection of a completed bracket. -/
theorem limπ_bracket_of_representatives (k : ℕ) (x y : completion I hI) (a b : L)
    (ha : ModuleTower.quotientsπ Js hs k a = (ModuleTower.quotients Js hs).limπ k x)
    (hb : ModuleTower.quotientsπ Js hs k b = (ModuleTower.quotients Js hs).limπ k y) :
    (ModuleTower.quotients Js hs).limπ k ⁅x, y⁆ = ModuleTower.quotientsπ Js hs k ⁅a, b⁆ := by
  apply (quotientEquiv I hI k).injective
  rw [quotientEquiv_π, LieSubmodule.Quotient.mk_bracket]
  have hx : projectionLinear I hI k x = LieSubmodule.Quotient.mk a := by
    simp only [projectionLinear, LinearMap.comp_apply, LinearEquiv.coe_coe, ← ha,
      quotientEquiv_π]
  have hy : projectionLinear I hI k y = LieSubmodule.Quotient.mk b := by
    simp only [projectionLinear, LinearMap.comp_apply, LinearEquiv.coe_coe, ← hb,
      quotientEquiv_π]
  exact (projectionLinear_bracket I hI k x y).trans (congrArg₂ Bracket.bracket hx hy)

/-- Completed Lie projections commute with all quotient transitions. -/
@[simp]
theorem factor_completionProjection {k l : ℕ} (h : k ≤ l) (x : completion I hI) :
    LieIdeal.factor (hI h) (completionProjection I hI l x) =
      completionProjection I hI k x :=
  factor_projectionLinear I hI h x

variable {M : Type*} [LieRing M] [LieAlgebra R M]

/-- Lift a compatible family of Lie homomorphisms into the Lie completion. -/
noncomputable def completionLift (f : ∀ k, M →ₗ⁅R⁆ L ⧸ I k)
    (hf : ∀ k, (LieIdeal.factor (hI (Nat.le_succ k))).comp (f (k + 1)) = f k) :
    M →ₗ⁅R⁆ completion I hI where
  toLinearMap := (ModuleTower.quotients Js hs).limLift
    (fun k => (quotientEquiv I hI k).symm.toLinearMap.comp (f k).toLinearMap) (by
      intro k
      apply LinearMap.ext
      intro x
      apply (quotientEquiv I hI k).injective
      rw [LinearMap.comp_apply, ← ModuleTower.transitionOfLE_succ,
        quotientEquiv_transition]
      simpa using LieHom.congr_fun (hf k) x)
  map_lie' := by
    intro x y
    apply completion_ext_aux I hI
    intro k
    rw [projectionLinear_bracket]
    simp only [projectionLinear, LinearMap.comp_apply,
      ModuleTower.limπ_apply, ModuleTower.coe_limLift_apply, LinearMap.toFun_eq_coe,
      LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LieHom.coe_toLinearMap, LieHom.map_lie]

/-- The universal lift has the prescribed quotient coordinates. -/
@[simp]
theorem completionProjection_lift (f : ∀ k, M →ₗ⁅R⁆ L ⧸ I k) (hf)
    (k : ℕ) (x : M) :
    completionProjection I hI k (completionLift I hI f hf x) = f k x := by
  -- Lie homomorphisms store a linear map; expose that projection before computing the limit lift.
  change projectionLinear I hI k
    ((ModuleTower.quotients _ _).limLift
      (fun k => (quotientEquiv I hI k).symm.toLinearMap.comp (f k).toLinearMap) _ x) = _
  simp [projectionLinear, ModuleTower.limπ_apply]

/-- A compatible lift is uniquely determined by its projections. -/
theorem completionLift_unique (f : ∀ k, M →ₗ⁅R⁆ L ⧸ I k) (hf)
    (g : M →ₗ⁅R⁆ completion I hI)
    (hg : ∀ k, (completionProjection I hI k).comp g = f k) :
    g = completionLift I hI f hf := by
  apply LieHom.ext
  intro x
  apply completion_ext_aux I hI
  intro k
  exact (LieHom.congr_fun (hg k) x).trans (completionProjection_lift I hI f hf k x).symm

/-- The canonical map to the completion sends an element to its quotient classes. -/
noncomputable def toCompletion : L →ₗ⁅R⁆ completion I hI :=
  completionLift I hI (fun k => (I k).mkQ) (by
    intro k
    ext x
    simp)

/-- Canonical elements have the usual quotient classes as their coordinates. -/
@[simp]
theorem completionProjection_toCompletion (k : ℕ) (x : L) :
    completionProjection I hI k (toCompletion I hI x) = (I k).mkQ x := by
  simp [toCompletion]

/-- The canonical Lie map has the existing module completion map as its linear map. -/
@[simp]
theorem toCompletion_toLinearMap :
    (toCompletion I hI).toLinearMap = ModuleTower.toLimQuotients Js hs := by
  apply LinearMap.ext
  intro x
  apply completion_ext I hI
  intro k
  have hx := completionProjection_toCompletion I hI k x
  refine hx.trans ?_
  -- The Lie homomorphism stores the linear projection to the quotient.
  change (I k).mkQ x = projectionLinear I hI k (ModuleTower.toLimQuotients Js hs x)
  simp only [projectionLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ModuleTower.limπ_apply, LieIdeal.mkQ_apply]
  rw [ModuleTower.coe_toLimQuotients_apply Js hs x k, quotientEquiv_π]

end LieIdeal
