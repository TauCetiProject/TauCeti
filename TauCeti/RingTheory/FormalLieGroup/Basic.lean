/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Commutative formal Lie groups in coordinates

A law of dimension `n` over `R` has one power series per output coordinate and two blocks
of `n` input variables. The unit, symmetry and associativity identities are identities in
the universal variables. They can therefore be used after any admissible formal substitution,
including substitutions with nilpotent constant coefficients.

We use the coordinate description of Stix, *A course on finite flat group schemes*, §10.2.2.
-/

public section

noncomputable section

namespace TauCeti

open MvPowerSeries

variable {R : Type*} [CommRing R] {n : ℕ} {σ τ : Type*}

namespace FormalLieGroup

/-- Substitute two blocks of coordinates into a tuple of binary law series. -/
def substLaw (φ : Fin n → MvPowerSeries (Fin 2 × Fin n) R)
    (x y : Fin n → MvPowerSeries σ R) (i : Fin n) : MvPowerSeries σ R :=
  (φ i).subst (Function.uncurry ![x, y])

/-- The coordinate formula for substituting two tuples into a binary law. -/
theorem substLaw_def (φ : Fin n → MvPowerSeries (Fin 2 × Fin n) R)
    (x y : Fin n → MvPowerSeries σ R) (i : Fin n) :
    substLaw φ x y i = (φ i).subst (Function.uncurry ![x, y]) := (rfl)

/-- Substituting after applying a law substitutes into each of its arguments. -/
theorem subst_substLaw (φ : Fin n → MvPowerSeries (Fin 2 × Fin n) R)
    {x y : Fin n → MvPowerSeries σ R} (hx : HasSubst x) (hy : HasSubst y)
    {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (i : Fin n) :
    (substLaw φ x y i).subst a =
      substLaw φ (fun j ↦ (x j).subst a) (fun j ↦ (y j).subst a) i := by
  unfold substLaw
  rw [subst_comp_subst_apply (hx.pair hy) ha]
  congr 1
  funext ⟨k, j⟩
  fin_cases k <;> rfl

end FormalLieGroup

open FormalLieGroup in
/-- A commutative formal Lie group of dimension `n` in a chosen system of parameters.
The first variable index chooses the input block and the second chooses a coordinate. -/
structure FormalLieGroup (R : Type*) [CommRing R] (n : ℕ) where
  /-- The coordinate series of the group law. -/
  law : Fin n → MvPowerSeries (Fin 2 × Fin n) R
  /-- The origin is a right unit. -/
  right_unit : substLaw law X 0 = X
  /-- The two input blocks can be exchanged. -/
  comm : substLaw law (fun i ↦ X ((0 : Fin 2), i)) (fun i ↦ X (1, i)) =
    substLaw law (fun i ↦ X (1, i)) (fun i ↦ X (0, i))
  /-- The two bracketings agree in three blocks of independent variables. -/
  assoc :
    let x := fun i : Fin n ↦ X (R := R) ((0 : Fin 3), i)
    let y := fun i : Fin n ↦ X (R := R) ((1 : Fin 3), i)
    let z := fun i : Fin n ↦ X (R := R) ((2 : Fin 3), i)
    substLaw law (substLaw law x y) z = substLaw law x (substLaw law y z)

namespace FormalLieGroup

@[ext]
theorem ext {F G : FormalLieGroup R n} (h : F.law = G.law) : F = G := by
  cases F
  cases G
  cases h
  rfl

variable (F : FormalLieGroup R n)

/-- Every coordinate of a formal Lie group law vanishes at the origin. -/
@[simp]
theorem constantCoeff_law (i : Fin n) : constantCoeff (F.law i) = 0 := by
  have h := congrArg constantCoeff (congrFun F.right_unit i)
  have hz : HasSubst (0 : Fin n → MvPowerSeries (Fin n) R) := HasSubst.zero
  rw [substLaw, constantCoeff_subst_of_constantCoeff_zero (HasSubst.X.pair hz)] at h
  · simpa using h
  · rintro ⟨k, j⟩
    fin_cases k <;> simp [Function.uncurry]

/-- A formal sum of admissible tuples is admissible. -/
theorem hasSubst_substLaw {x y : Fin n → MvPowerSeries σ R} (hx : HasSubst x)
    (hy : HasSubst y) : HasSubst (substLaw F.law x y) :=
  hasSubst_of_constantCoeff_nilpotent fun i ↦
    IsNilpotent_subst (hx.pair hy) (F.constantCoeff_law i ▸ IsNilpotent.zero)

/-- The right unit identity after substitution. -/
@[simp]
theorem substLaw_zero_right {x : Fin n → MvPowerSeries σ R} (hx : HasSubst x) :
    substLaw F.law x 0 = x := by
  funext i
  have h := congrArg (subst x) (congrFun F.right_unit i)
  have hz : HasSubst (0 : Fin n → MvPowerSeries (Fin n) R) := HasSubst.zero
  have h0 : subst x (0 : MvPowerSeries (Fin n) R) = 0 := by
    rw [← substAlgHom_apply hx, map_zero]
  -- The transport produces a lambda-valued zero tuple. Expose the target's zero tuple too,
  -- since Pi.zero_apply simplifies applied zeros, not a zero tuple passed to substLaw.
  change substLaw F.law x (fun _ ↦ 0) i = x i
  simpa only [subst_substLaw _ HasSubst.X hz hx, subst_X hx, Pi.zero_apply, h0] using h

/-- Symmetry of the formal sum on admissible tuples. -/
theorem substLaw_comm {x y : Fin n → MvPowerSeries σ R} (hx : HasSubst x) (hy : HasSubst y) :
    substLaw F.law x y = substLaw F.law y x := by
  funext i
  have h := congrArg (subst (Function.uncurry ![x, y])) (congrFun F.comm i)
  simpa only [subst_substLaw _ (hasSubst_block _) (hasSubst_block _) (hx.pair hy),
    subst_block _ (hx.pair hy), Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using h

/-- The left unit identity after substitution. -/
@[simp]
theorem substLaw_zero_left {x : Fin n → MvPowerSeries σ R} (hx : HasSubst x) :
    substLaw F.law 0 x = x := by
  exact (F.substLaw_comm (x := 0) HasSubst.zero hx).trans (F.substLaw_zero_right hx)

/-- Associativity of the formal sum on admissible tuples. -/
theorem substLaw_assoc {x y z : Fin n → MvPowerSeries σ R}
    (hx : HasSubst x) (hy : HasSubst y) (hz : HasSubst z) :
    substLaw F.law (substLaw F.law x y) z = substLaw F.law x (substLaw F.law y z) := by
  let a := ![x, y, z]
  have ha : HasSubst (Function.uncurry a) :=
    .uncurry (by intro j; fin_cases j <;> assumption)
  funext i
  have h := congrArg (subst (Function.uncurry a)) (congrFun F.assoc i)
  simpa only [subst_substLaw _ (F.hasSubst_substLaw (hasSubst_block _) (hasSubst_block _))
      (hasSubst_block _) ha,
    subst_substLaw _ (hasSubst_block _) (F.hasSubst_substLaw (hasSubst_block _)
      (hasSubst_block _)) ha, subst_substLaw _ (hasSubst_block _) (hasSubst_block _) ha,
    subst_block _ ha, a, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Function.comp_apply, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail,
    Matrix.cons_val_fin_one] using h

private theorem substLaw_X_add_X {x y : Fin n → MvPowerSeries σ R}
    (hx : HasSubst x) (hy : HasSubst y) :
    substLaw (fun i ↦ X ((0 : Fin 2), i) + X (1, i)) x y = x + y := by
  funext i
  simp [substLaw, subst_add (hx.pair hy), subst_X (hx.pair hy), Function.uncurry]

/-- The additive formal Lie group in `n` coordinates, with coordinatewise addition. -/
def additive (R : Type*) [CommRing R] (n : ℕ) : FormalLieGroup R n where
  law i := X ((0 : Fin 2), i) + X (1, i)
  right_unit := (substLaw_X_add_X (x := X) (y := 0) HasSubst.X HasSubst.zero).trans (add_zero _)
  comm := by simp only [substLaw_X_add_X (hasSubst_block _) (hasSubst_block _), add_comm]
  assoc := by
    dsimp only
    simp only [substLaw_X_add_X (hasSubst_block _) (hasSubst_block _),
      substLaw_X_add_X ((hasSubst_block _).add (hasSubst_block _)) (hasSubst_block _),
      substLaw_X_add_X (hasSubst_block _) ((hasSubst_block _).add (hasSubst_block _)), add_assoc]

@[simp]
theorem additive_law (i : Fin n) :
    (additive R n).law i = X ((0 : Fin 2), i) + X (1, i) := (rfl)

/-- The additive formal Lie group sums admissible tuples coordinatewise. -/
@[simp]
theorem substLaw_additive {x y : Fin n → MvPowerSeries σ R}
    (hx : HasSubst x) (hy : HasSubst y) :
    substLaw (additive R n).law x y = x + y :=
  substLaw_X_add_X hx hy

end FormalLieGroup

end TauCeti
