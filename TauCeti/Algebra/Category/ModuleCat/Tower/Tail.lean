/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Removing finite initial segments of module towers

Deleting the first `k` terms of a tower changes neither its limit nor its first derived limit.
The comparison maps restrict product families to the tail; their inverses are induced by the
composite transition maps from the tail back to the original tower. Both comparisons are natural
in tower morphisms. No surjectivity or Mittag-Leffler hypothesis is needed.

The proof uses the shift presentation of `lim` and `lim¹` from `ModuleTower.Basic`: a finite
telescoping sum makes the composite of restriction and transition equal to the identity modulo
the shift. These comparisons allow finite changes of starting index in inverse-limit sequences.

## References

* C. A. Weibel, *An introduction to homological algebra*, §3.5.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite
open scoped BigOperators

universe v u

variable {R : Type u} [Ring R]

/-- The tail of a tower starting at its `k`-th term. -/
abbrev tail (F : ModuleTower.{v} R) (k : ℕ) : ModuleTower.{v} R :=
  (show Monotone (fun n : ℕ ↦ k + n) from fun _ _ h ↦ Nat.add_le_add_left h k).functor.op ⋙ F

variable (F : ModuleTower.{v} R) (k : ℕ)

@[simp]
theorem tail_transitionOfLE {n m : ℕ} (h : n ≤ m) :
    (F.tail k).transitionOfLE h = F.transitionOfLE (Nat.add_le_add_left h k) := by
  rw [transitionOfLE_def, transitionOfLE_def]
  rfl

@[simp]
theorem tail_transition (n : ℕ) : (F.tail k).transition n = F.transition (k + n) := by
  rw [transition_def, transition_def]
  rfl

/-- Restriction of a product family to a tail. -/
def tailRestriction : F.Product →ₗ[R] (F.tail k).Product :=
  LinearMap.pi fun n ↦ LinearMap.proj (k + n)

@[simp]
theorem tailRestriction_apply (x : F.Product) (n : ℕ) :
    F.tailRestriction k x n = x (k + n) :=
  (rfl)

/-- Restriction commutes with the difference maps defining `lim` and `lim¹`. -/
theorem tailRestriction_shift :
    F.tailRestriction k ∘ₗ F.shift = (F.tail k).shift ∘ₗ F.tailRestriction k := by
  ext x n
  simp only [LinearMap.comp_apply, tailRestriction_apply, shift_apply, tail_transition]
  rfl

/-- Composite transition maps give a morphism from a tail to the original tower. -/
def tailToSelf : F.tail k ⟶ F where
  app n := F.map (homOfLE (Nat.le_add_left n.unop k)).op
  naturality _ _ _ := by simp only [Functor.comp_map, ← F.map_comp]; congr 1

@[simp]
theorem tailToSelf_app (n : ℕ) :
    ((F.tailToSelf k).app (op n)).hom = F.transitionOfLE (Nat.le_add_left n k) := by
  rw [transitionOfLE_def]
  rfl

/-- Restriction of compatible families to a tail. -/
private def limTailMap : F.lim →ₗ[R] (F.tail k).lim :=
  (F.tailRestriction k).restrict fun x hx ↦ by
    rw [lim_eq_ker, LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, ← tailRestriction_shift, LinearMap.comp_apply, hx, map_zero]

@[simp]
private theorem coe_limTailMap_apply (x : F.lim) :
    (F.limTailMap k x : (F.tail k).Product) = F.tailRestriction k x :=
  (rfl)

/-- Restriction on the cokernels of the difference maps. -/
private def limOneTailMap : F.limOne →ₗ[R] (F.tail k).limOne :=
  (LinearMap.range F.shift).mapQ (LinearMap.range (F.tail k).shift) (F.tailRestriction k) <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨F.tailRestriction k x, (LinearMap.congr_fun (F.tailRestriction_shift k) x).symm⟩

@[simp]
private theorem limOneTailMap_mk (x : F.Product) :
    F.limOneTailMap k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.tailRestriction k x) :=
  (rfl)

private def tailCorrection (x : F.Product) : F.Product :=
  fun n ↦ ∑ i ∈ Finset.range k, F.transitionOfLE (Nat.le_add_right n i) (x (n + i))

private theorem shift_tailCorrection (x : F.Product) :
    F.shift (F.tailCorrection k x) = x - productMap (F.tailToSelf k) (F.tailRestriction k x) := by
  funext n
  simp only [shift_apply, tailCorrection, map_sum, transition_transitionOfLE,
    Pi.sub_apply, productMap_apply, tailToSelf_app, tailRestriction_apply]
  rw [← Finset.sum_sub_distrib]
  have key := Finset.sum_range_sub' (fun i ↦ F.transitionOfLE (Nat.le_add_right n i) (x (n + i))) k
  simp only [Nat.add_zero, transitionOfLE_refl, LinearMap.id_apply] at key
  -- The summands have dependent source modules, so transport both the transition and its input.
  have congr_index {i j : ℕ} (hi : n ≤ i) (hj : n ≤ j) (h : i = j) :
      F.transitionOfLE hi (x i) = F.transitionOfLE hj (x j) := by subst j; rfl
  convert! key using 1 <;> congr! 3
  all_goals exact congr_index _ _ (by omega)

/-- Deleting finitely many initial terms preserves the inverse limit. The forward map is
restriction, and the inverse is induced by the composite transition maps. -/
def limTailEquiv : F.lim ≃ₗ[R] (F.tail k).lim :=
  LinearEquiv.ofLinearMap (F.limTailMap k) (limMap (F.tailToSelf k))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      funext n
      simpa only [LinearMap.comp_apply, coe_limTailMap_apply, tailRestriction_apply,
        coe_limMap_apply, productMap_apply, tailToSelf_app, tail_transitionOfLE,
        LinearMap.id_apply] using
        (F.tail k).transitionOfLE_coe_lim x (Nat.le_add_left n k))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      funext n
      simpa only [LinearMap.comp_apply, coe_limMap_apply, productMap_apply, tailToSelf_app,
        coe_limTailMap_apply, tailRestriction_apply, LinearMap.id_apply] using
        F.transitionOfLE_coe_lim x (Nat.le_add_left n k))

@[simp]
theorem coe_limTailEquiv_apply (x : F.lim) (n : ℕ) :
    (F.limTailEquiv k x : (F.tail k).Product) n = (x : F.Product) (k + n) :=
  (rfl)

@[simp]
theorem coe_limTailEquiv_symm_apply (x : (F.tail k).lim) (n : ℕ) :
    ((F.limTailEquiv k).symm x : F.Product) n =
      F.transitionOfLE (Nat.le_add_left n k) ((x : (F.tail k).Product) n) := by
  simp only [limTailEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    coe_limMap_apply, productMap_apply, tailToSelf_app]

private theorem limOne_tailToSelf_restriction (x : F.Product) :
    (Submodule.Quotient.mk (productMap (F.tailToSelf k) (F.tailRestriction k x)) : F.limOne) =
      Submodule.Quotient.mk x := by
  apply (Submodule.Quotient.eq _).2
  exact ⟨-F.tailCorrection k x, by simp [shift_tailCorrection]⟩

/-- Deleting finitely many initial terms preserves `lim¹`, without any condition on the
transition maps. The inverse is induced by the composite transitions from the tail. -/
def limOneTailEquiv : F.limOne ≃ₗ[R] (F.tail k).limOne :=
  LinearEquiv.ofLinearMap (F.limOneTailMap k) (limOneMap (F.tailToSelf k))
    (by
      apply Submodule.linearMap_qext
      ext x
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, limOneMap_mk, limOneTailMap_mk,
        LinearMap.id_apply]
      have h : F.tailRestriction k (productMap (F.tailToSelf k) x) =
          productMap ((F.tail k).tailToSelf k) ((F.tail k).tailRestriction k x) := by
        ext n
        simp only [tailRestriction_apply, productMap_apply, tailToSelf_app, tail_transitionOfLE]
      rw [h]
      exact (F.tail k).limOne_tailToSelf_restriction k x)
    (by
      apply Submodule.linearMap_qext
      ext x
      simpa only [LinearMap.comp_apply, Submodule.mkQ_apply, limOneTailMap_mk, limOneMap_mk,
        LinearMap.id_apply] using F.limOne_tailToSelf_restriction k x)

@[simp]
theorem limOneTailEquiv_mk (x : F.Product) :
    F.limOneTailEquiv k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.tailRestriction k x) :=
  (rfl)

@[simp]
theorem limOneTailEquiv_symm_mk (x : (F.tail k).Product) :
    (F.limOneTailEquiv k).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (productMap (F.tailToSelf k) x) := by
  simp only [limOneTailEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    limOneMap_mk]

variable {F} {G : ModuleTower.{v} R}

/-- The inverse-limit tail comparison is natural in morphisms of towers. -/
theorem limTailEquiv_naturality (f : F ⟶ G) :
    (G.limTailEquiv k).toLinearMap ∘ₗ limMap f =
      limMap (Functor.whiskerLeft _ f) ∘ₗ (F.limTailEquiv k).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  simp

/-- The `lim¹` tail comparison is natural in morphisms of towers. -/
theorem limOneTailEquiv_naturality (f : F ⟶ G) :
    (G.limOneTailEquiv k).toLinearMap ∘ₗ limOneMap f =
      limOneMap (Functor.whiskerLeft _ f) ∘ₗ (F.limOneTailEquiv k).toLinearMap := by
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Submodule.mkQ_apply, limOneMap_mk, limOneTailEquiv_mk]
  congr 1
  funext n
  simp

end TauCeti.ModuleTower
