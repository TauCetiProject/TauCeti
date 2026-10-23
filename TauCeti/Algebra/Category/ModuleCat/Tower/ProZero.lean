/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.MittagLeffler
public import TauCeti.CategoryTheory.Functor.ProZero

/-!
# Pro-zero towers of modules

A tower of modules `A₀ ← A₁ ← A₂ ← ⋯` is pro-zero (`CategoryTheory.Functor.IsProZero`) when every
term `Aₙ` is killed by some composite transition `Aₘ → Aₙ`. This file shows that a pro-zero tower
has `lim A = 0` and `lim¹ A = 0`, so pro-zero error terms are invisible to `lim` and `lim¹`.

The basic family of examples is the tower `R ← R ← ⋯` whose transitions are right multiplication
by an element `a`: it is pro-zero exactly when `a` is nilpotent. In particular, for a prime `p` the
tower `ℤ ← ℤ ← ⋯` with transitions multiplication by `p` is not pro-zero.

## Main declarations

* `TauCeti.ModuleTower.isProZero_iff_exists_transitionOfLE_eq_zero`: a tower of modules is pro-zero
  exactly when every term is killed by some composite transition `transitionOfLE`.
* `TauCeti.ModuleTower.lim_eq_bot_of_isProZero`,
  `TauCeti.ModuleTower.subsingleton_limOne_of_isProZero`: pro-zero towers have vanishing `lim` and
  `lim¹`; `TauCeti.ModuleTower.isMittagLeffler_of_isProZero`: they are Mittag-Leffler.
* `TauCeti.ModuleTower.multiplicationTower`: the tower `R ← R ← ⋯` with transitions right
  multiplication by `a`.
* `TauCeti.ModuleTower.isProZero_multiplicationTower_iff`: it is pro-zero exactly when `a` is
  nilpotent; `TauCeti.ModuleTower.isProZero_multiplicationTower_iff_eq_zero` is the case of a
  reduced ring.

## References

* B. Bhatt, *On the direct summand conjecture and its derived variant*, Invent. Math. 212 (2018),
  §3 (pro-zero towers, in their almost form).
-/

public section

noncomputable section

namespace TauCeti

namespace ModuleTower

open CategoryTheory Opposite

universe v u

variable {R : Type u} [Ring R]

section IsProZero

variable (F : ModuleTower.{v} R)

/-- A tower of modules is pro-zero exactly when every term `Aₙ` is killed by some composite
transition `Aₘ → Aₙ`. -/
theorem isProZero_iff_exists_transitionOfLE_eq_zero :
    F.IsProZero ↔ ∀ n, ∃ (m : ℕ) (h : n ≤ m), F.transitionOfLE h = 0 := by
  rw [Functor.isProZero_iff_forall_exists_le]
  simp only [ModuleCat.hom_ext_iff, ModuleCat.hom_zero, transitionOfLE_def]

variable {F}

/-- A pro-zero tower has `lim A = 0`. -/
theorem lim_eq_bot_of_isProZero (hF : F.IsProZero) : F.lim = ⊥ := by
  have h := hF.isZero_of_isLimit F.isLimitLimCone
  rw [limCone_pt, ModuleCat.isZero_of_iff_subsingleton] at h
  exact Submodule.subsingleton_iff_eq_bot.1 h

/-- A pro-zero tower is Mittag-Leffler: the images of the composite transitions into each term
are eventually zero. -/
theorem isMittagLeffler_of_isProZero (hF : F.IsProZero) : F.IsMittagLeffler := by
  refine (F.isMittagLeffler_iff_ranges).2 fun n ↦ ?_
  obtain ⟨m, h, hm⟩ := (F.isProZero_iff_exists_transitionOfLE_eq_zero).1 hF n
  exact ⟨m, h, fun k hmk ↦ by simp [← F.transitionOfLE_comp_transitionOfLE h hmk, hm]⟩

/-- A pro-zero tower has `lim¹ A = 0`. -/
theorem subsingleton_limOne_of_isProZero (hF : F.IsProZero) : Subsingleton F.limOne :=
  F.subsingleton_limOne_of_isMittagLeffler (isMittagLeffler_of_isProZero hF)

end IsProZero

section MultiplicationTower

/-- The tower `R ← R ← R ← ⋯` of left `R`-modules whose transition maps are right multiplication
`x ↦ x * a` by an element `a`. -/
@[expose] def multiplicationTower (a : R) : ModuleTower.{u} R :=
  Functor.ofOpSequence (X := fun _ ↦ ModuleCat.of R R) fun _ ↦
    ModuleCat.ofHom (LinearMap.toSpanSingleton R R a)

@[simp]
theorem multiplicationTower_obj (a : R) (n : ℕ) :
    (multiplicationTower a).obj (op n) = ModuleCat.of R R :=
  (rfl)

@[simp]
theorem multiplicationTower_transition (a : R) (n : ℕ) :
    (multiplicationTower a).transition n = LinearMap.toSpanSingleton R R a := by
  simp only [multiplicationTower, transition_def, Functor.ofOpSequence_map_homOfLE_succ]
  -- `ModuleCat.hom_ofHom`, stated for the carrier `R` rather than `ModuleCat.of R R`
  rfl

/-- The composite transition `Aₖ → Aₙ` of `multiplicationTower a` is right multiplication by
`a ^ (k - n)`. -/
@[simp]
theorem multiplicationTower_transitionOfLE (a : R) {n k : ℕ} (h : n ≤ k) :
    (multiplicationTower a).transitionOfLE h = LinearMap.toSpanSingleton R R (a ^ (k - n)) := by
  -- The `have`s are stated for `R →ₗ[R] R`; the goals are about the defeq carrier of
  -- `ModuleCat.of R R`, on which the `toSpanSingleton` lemmas do not fire syntactically.
  induction k, h using Nat.le_induction with
  | base =>
    have key : (LinearMap.id : R →ₗ[R] R) = LinearMap.toSpanSingleton R R (a ^ (n - n)) := by
      ext; simp
    rw [transitionOfLE_refl]
    exact key
  | succ k h ih =>
    have key : LinearMap.toSpanSingleton R R (a ^ (k - n)) ∘ₗ LinearMap.toSpanSingleton R R a =
        LinearMap.toSpanSingleton R R (a ^ (k + 1 - n)) := by
      rw [LinearMap.toSpanSingleton_comp_toSpanSingleton, smul_eq_mul, Nat.succ_sub h, pow_succ']
    rw [← transitionOfLE_comp_transitionOfLE _ h (Nat.le_succ k), ih, transitionOfLE_succ,
      multiplicationTower_transition]
    exact key

/-- **The multiplication tower is pro-zero exactly for nilpotent elements.** -/
theorem isProZero_multiplicationTower_iff (a : R) :
    (multiplicationTower a).IsProZero ↔ IsNilpotent a := by
  rw [isProZero_iff_exists_transitionOfLE_eq_zero]
  constructor
  · intro h
    obtain ⟨m, _, hm⟩ := h 0
    rw [multiplicationTower_transitionOfLE] at hm
    exact ⟨m - 0, (LinearMap.toSpanSingleton_eq_zero_iff R R).1 hm⟩
  · rintro ⟨k, hk⟩ n
    refine ⟨n + k, by lia, ?_⟩
    rw [multiplicationTower_transitionOfLE, Nat.add_sub_cancel_left, hk]
    exact LinearMap.toSpanSingleton_zero R R

/-- Over a reduced ring the multiplication tower by `a` is pro-zero only for `a = 0`. For instance,
for a prime `p` the tower `ℤ ← ℤ ← ⋯` with transitions multiplication by `p` is not pro-zero. -/
theorem isProZero_multiplicationTower_iff_eq_zero [IsReduced R] (a : R) :
    (multiplicationTower a).IsProZero ↔ a = 0 := by
  rw [isProZero_multiplicationTower_iff, isNilpotent_iff_eq_zero]

end MultiplicationTower

end ModuleTower

end TauCeti
