/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.MittagLeffler
public import TauCeti.CategoryTheory.Functor.ProZero
import Mathlib.RingTheory.Multiplicity

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
* `TauCeti.ModuleTower.multiplicationTowerProductEquiv`: the product of its terms is the module of
  sequences `ℕ → R`, on which the shift is `δ(x)ₙ = xₙ - xₙ₊₁ * a`
  (`TauCeti.ModuleTower.multiplicationTowerProductEquiv_shift`).
* `TauCeti.ModuleTower.lim_multiplicationTower_eq_bot`: for an integer `p` that is not a unit, the
  multiplication-by-`p` tower of integers has `lim = 0`.
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

/-- The terms of `multiplicationTower a` are `R` itself, so the product of its terms is the module
of sequences `ℕ → R`. -/
def multiplicationTowerProductEquiv (a : R) : (multiplicationTower a).Product ≃ₗ[R] (ℕ → R) :=
  -- `(multiplicationTower a).obj (op n)` is `ModuleCat.of R R` by definition
  LinearEquiv.refl R (ℕ → R)

/-- The shift map of `multiplicationTower a`, as a map of sequences:
`δ(x)ₙ = xₙ - xₙ₊₁ * a`. -/
@[simp]
theorem multiplicationTowerProductEquiv_shift (a : R) (x : (multiplicationTower a).Product)
    (n : ℕ) :
    multiplicationTowerProductEquiv a ((multiplicationTower a).shift x) n =
      multiplicationTowerProductEquiv a x n - multiplicationTowerProductEquiv a x (n + 1) * a := by
  rw [← smul_eq_mul, ← LinearMap.toSpanSingleton_apply, ← multiplicationTower_transition]
  exact shift_apply _ x n

/-- A sequence lies in `lim` of `multiplicationTower a` exactly when `xₙ₊₁ * a = xₙ` for all
`n`. -/
theorem mem_lim_multiplicationTower_iff {a : R} {x : (multiplicationTower a).Product} :
    x ∈ (multiplicationTower a).lim ↔ ∀ n,
      multiplicationTowerProductEquiv a x (n + 1) * a = multiplicationTowerProductEquiv a x n := by
  rw [lim_eq_ker, LinearMap.mem_ker, ← (multiplicationTowerProductEquiv a).map_eq_zero_iff,
    funext_iff]
  simp only [multiplicationTowerProductEquiv_shift, Pi.zero_apply, sub_eq_zero]
  exact forall_congr' fun n ↦ eq_comm

/-- **The multiplication-by-`p` tower has vanishing limit** for every integer `p` that is not a
unit: every term of a compatible family is divisible by every power of `p`. -/
theorem lim_multiplicationTower_eq_bot {p : ℤ} (hp : ¬IsUnit p) :
    (multiplicationTower p).lim = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ (Submodule.mem_bot ℤ).2 <|
    (multiplicationTowerProductEquiv p).map_eq_zero_iff.1 (funext fun n ↦ ?_)
  set e := multiplicationTowerProductEquiv p
  have hx' := mem_lim_multiplicationTower_iff.1 hx
  have key (k : ℕ) : e x n = e x (n + k) * p ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [ih, ← hx' (n + k), pow_succ', ← mul_assoc, add_assoc]
  have hdvd (k : ℕ) : p ^ k ∣ e x n := ⟨e x (n + k), by rw [key k, mul_comm]⟩
  by_contra h0
  obtain ⟨k, hk⟩ := Int.finiteMultiplicity_iff.2 ⟨mt Int.isUnit_iff_natAbs_eq.2 hp, h0⟩
  exact hk (hdvd (k + 1))

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
