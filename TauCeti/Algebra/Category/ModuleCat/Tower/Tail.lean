/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Subsequence
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Removing finite initial segments of module towers

The tail is a subsequence of a tower, so `ModuleTower.limSubsequenceEquiv` compares its
limit with the original limit. Deleting the first `k` terms also preserves the first derived
limit. Its comparison restricts product families to the tail; the inverse is induced by the
composite transition maps from the tail back to the original tower. This comparison is natural
in tower morphisms. No surjectivity or Mittag-Leffler hypothesis is needed. Consequently, a tower
whose transitions are surjective from some index on has vanishing `lim¹`.

The proof uses the shift presentation of `lim¹` from `ModuleTower.Basic`: a finite
telescoping sum makes the composite of restriction and transition equal to the identity modulo
the shift. This comparison allows finite changes of starting index in inverse-limit sequences.

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
  F.subsequence ⟨(k + ·), fun _ _ h ↦ Nat.add_le_add_left h k⟩

variable (F : ModuleTower.{v} R) (k : ℕ)

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
  simp only [LinearMap.comp_apply, tailRestriction_apply, shift_apply,
    ← transitionOfLE_succ, subsequence_transitionOfLE]
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
        simp only [tailRestriction_apply, productMap_apply, tailToSelf_app,
          subsequence_transitionOfLE]
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

/-- **Eventually surjective towers have vanishing `lim¹`.** If the transition maps `Aₙ₊₁ → Aₙ`
are surjective for all `n ≥ k`, then `lim¹ A` vanishes. -/
theorem subsingleton_limOne_of_surjective_of_le
    (h : ∀ n, k ≤ n → Function.Surjective (F.transition n)) : Subsingleton F.limOne :=
  (F.limOneTailEquiv k).toEquiv.subsingleton_congr.2 <|
    (F.tail k).subsingleton_limOne_of_surjective fun n ↦ by
      erw [subsequence_transition, transitionOfLE_succ]
      exact h _ (Nat.le_add_right k n)

variable {F} {G : ModuleTower.{v} R}

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
  simp only [tailRestriction_apply, productMap_apply]
  -- Evaluating the shift order hom sends n to k + n, including in the dependent source module.
  rfl

end TauCeti.ModuleTower
