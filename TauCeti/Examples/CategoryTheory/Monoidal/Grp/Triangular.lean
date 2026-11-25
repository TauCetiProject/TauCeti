/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grp.Triangular
public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Checks for the triangular change of coordinates

Checks for `TauCeti.GrpObj.triangularIso` with head index `0` on the power
`∏ᶜ (fun _ : Fin (n + 1) => G)` of a group object `G`.

For points of an arbitrary group object: a single factor gives the identity; the inverse sends
`(f, g / f)` to `(f, g)`; the small diagonal `(f, …, f)` goes to `(f, 1, …, 1)`; the inverse sends
`(a, b)` to `(a, b a)`, which differs from `(a, a b)` for noncommuting `a, b`; on the diagonal
`(a, a)` the inverse gives `(a, a²)` and the forward map `(a, 1)`.

For group schemes, both coordinate changes commute with base change along any `S' ⟶ S` through
the canonical comparison `PreservesProduct.iso` of fibre powers, nonreduced bases included.

For groups viewed as group objects in `Type`: in `GL₂(𝔽₂)` the two elementary matrices do not
commute, so the head must stand on the right; in the cyclic group of order three the tails `a²` and
`1` differ; in the unit group `ℚ[ε]ˣ` of the dual numbers, the forward map sends `(1 + ε, 1)` to
`(1 + ε, 1 - ε)`, and the inverse restores `(1 + ε, 1)`.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TauCeti.GrpObj

namespace TauCeti.Examples.GrpObjTriangular

section General

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] (G : C) [GrpObj G] {T : C}

-- For a single factor the triangular change of coordinates is the identity.
example : triangularIso G (0 : Fin 1) = Iso.refl _ :=
  triangularIso_eq_refl G 0

/-- On a pair of points, the inverse triangular change of coordinates sends `(a, b)` to
`(a, b a)`. -/
theorem lift_pair_comp_triangularIso_inv (a b : T ⟶ G) :
    Pi.lift ![a, b] ≫ (triangularIso G (0 : Fin 2)).inv = Pi.lift ![a, b * a] := by
  rw [lift_comp_triangularIso_inv]
  congr 1
  ext j
  fin_cases j <;> simp

/-- On a pair of points, the triangular change of coordinates sends `(a, b)` to `(a, b / a)`. -/
theorem lift_pair_comp_triangularIso_hom (a b : T ⟶ G) :
    Pi.lift ![a, b] ≫ (triangularIso G (0 : Fin 2)).hom = Pi.lift ![a, b / a] := by
  rw [lift_comp_triangularIso_hom]
  congr 1
  ext j
  fin_cases j <;> simp

-- The inverse sends the pair `(f, g / f)` to `(f, g)`.
example (f g : T ⟶ G) :
    Pi.lift ![f, g / f] ≫ (triangularIso G 0).inv = Pi.lift ![f, g] := by
  rw [lift_pair_comp_triangularIso_inv, div_mul_cancel]

-- The small diagonal `(f, …, f)` goes to `(f, 1, …, 1)`.
example (n : ℕ) (f : T ⟶ G) :
    Pi.lift (fun _ : Fin (n + 1) ↦ f) ≫ (triangularIso G 0).hom =
      Pi.lift fun i ↦ if i = 0 then f else 1 := by
  rw [lift_comp_triangularIso_hom]
  congr 1
  ext i
  split_ifs <;> simp

-- The head stands on the right: the inverse sends `(a, b)` to `(a, b a)`, which differs from
-- `(a, a b)` when `a` and `b` do not commute.
example (a b : T ⟶ G) (h : a * b ≠ b * a) :
    Pi.lift ![a, b] ≫ (triangularIso G 0).inv = Pi.lift ![a, b * a] ∧
      Pi.lift ![a, b] ≫ (triangularIso G 0).inv ≠ Pi.lift ![a, a * b] := by
  have e := lift_pair_comp_triangularIso_inv G a b
  refine ⟨e, fun h' ↦ h ?_⟩
  simpa using (congrArg (· ≫ Pi.π _ 1) (e.symm.trans h')).symm

-- On the diagonal `(a, a)` the inverse gives `(a, a²)` and the forward map `(a, 1)`.
example (a : T ⟶ G) :
    Pi.lift ![a, a] ≫ (triangularIso G 0).inv = Pi.lift ![a, a * a] ∧
      Pi.lift ![a, a] ≫ (triangularIso G 0).hom = Pi.lift ![a, 1] := by
  rw [lift_pair_comp_triangularIso_inv, lift_pair_comp_triangularIso_hom, div_self']
  exact ⟨rfl, rfl⟩

end General

section Scheme

open AlgebraicGeometry

open scoped CategoryTheory.Obj

variable {S S' : Scheme} (f : S' ⟶ S) (A : Over S) [GrpObj A] (n : ℕ)

-- Base change along `f` commutes with the triangular change of coordinates of a group scheme,
-- through the canonical comparison of fibre powers.
example :
    (Over.pullback f).map (triangularIso A (0 : Fin (n + 1))).hom ≫
        (PreservesProduct.iso (Over.pullback f) fun _ : Fin (n + 1) ↦ A).hom =
      (PreservesProduct.iso (Over.pullback f) fun _ : Fin (n + 1) ↦ A).hom ≫
        (triangularIso ((Over.pullback f).obj A) 0).hom := by
  simpa using map_triangularIso_hom_comp_piComparison A (0 : Fin (n + 1)) (Over.pullback f)

-- Base change along `f` commutes with the inverse triangular change of coordinates.
example :
    (Over.pullback f).map (triangularIso A (0 : Fin (n + 1))).inv ≫
        (PreservesProduct.iso (Over.pullback f) fun _ : Fin (n + 1) ↦ A).hom =
      (PreservesProduct.iso (Over.pullback f) fun _ : Fin (n + 1) ↦ A).hom ≫
        (triangularIso ((Over.pullback f).obj A) 0).inv := by
  simpa using map_triangularIso_inv_comp_piComparison A (0 : Fin (n + 1)) (Over.pullback f)

-- Read through the inverse comparison: `C⁻¹ ≫ F (R⁻¹) = R'⁻¹ ≫ C⁻¹`.
example :
    (PreservesProduct.iso (Over.pullback f) fun _ : Fin (n + 1) ↦ A).inv ≫
        (Over.pullback f).map (triangularIso A (0 : Fin (n + 1))).inv =
      (triangularIso ((Over.pullback f).obj A) 0).inv ≫
        (PreservesProduct.iso (Over.pullback f) fun _ : Fin (n + 1) ↦ A).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  simpa using map_triangularIso_inv_comp_piComparison A (0 : Fin (n + 1)) (Over.pullback f)

end Scheme

section Concrete

/-- A group `H` as a group object in `Type`. -/
noncomputable abbrev grpObjOf (H : Type) [Group H] : Type :=
  (GrpTypeEquivalenceGrp.inverse.obj (GrpCat.of H)).X

/-- The constant point `a` of `H`, with values in `PUnit`. -/
abbrev pt {H : Type} [Group H] (a : H) : PUnit ⟶ grpObjOf H :=
  TypeCat.ofHom fun _ ↦ a

/-- The group law on points of `grpObjOf H` is that of `H`, by construction of
`GrpTypeEquivalenceGrp.inverse`. -/
theorem pt_mul {H : Type} [Group H] (a b : H) : pt a * pt b = pt (a * b) := rfl

/-- The unit point of `grpObjOf H` is the constant point `1`. -/
theorem pt_one {H : Type} [Group H] : pt (1 : H) = 1 := rfl

/-- Inverses of points of `grpObjOf H` are computed in `H`. -/
theorem pt_inv {H : Type} [Group H] (a : H) : (pt a)⁻¹ = pt a⁻¹ := rfl

/-- Quotients of points of `grpObjOf H` are computed in `H`. -/
theorem pt_div {H : Type} [Group H] (a b : H) : pt a / pt b = pt (a / b) := by
  rw [div_eq_mul_inv, pt_inv, pt_mul, div_eq_mul_inv]

/-- Distinct elements of `H` give distinct points. -/
theorem pt_injective {H : Type} [Group H] : Function.Injective (pt (H := H)) :=
  fun _ _ h ↦ ConcreteCategory.congr_hom h PUnit.unit

/-- The upper elementary matrix `((1, 1), (0, 1))` in `GL₂(𝔽₂)`. -/
abbrev upperElementary : GL (Fin 2) (ZMod 2) :=
  ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩

/-- The lower elementary matrix `((1, 0), (1, 1))` in `GL₂(𝔽₂)`. -/
abbrev lowerElementary : GL (Fin 2) (ZMod 2) :=
  ⟨!![1, 0; 1, 1], !![1, 0; 1, 1], by decide, by decide⟩

-- In `GL₂(𝔽₂)`, the inverse sends `(a, b)` to `(a, b a)`, and `b a = ((1, 1), (1, 0))` differs
-- from `a b = ((0, 1), (1, 1))`, so the second projection detects the order.
example :
    Pi.lift ![pt upperElementary, pt lowerElementary] ≫
        (triangularIso (grpObjOf (GL (Fin 2) (ZMod 2))) 0).inv =
      Pi.lift ![pt upperElementary, pt (lowerElementary * upperElementary)] ∧
    ((lowerElementary * upperElementary : GL (Fin 2) (ZMod 2)) :
        Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![1, 1; 1, 0] ∧
    ((upperElementary * lowerElementary : GL (Fin 2) (ZMod 2)) :
        Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![0, 1; 1, 1] ∧
    pt (lowerElementary * upperElementary) ≠ pt (upperElementary * lowerElementary) := by
  refine ⟨?_, by decide, by decide,
    fun h ↦ absurd (congrArg Units.val (pt_injective h)) (by decide)⟩
  rw [lift_pair_comp_triangularIso_inv, pt_mul]

-- On the diagonal `(a, a)` of the cyclic group of order three, with `a` a generator, the inverse
-- gives `(a, a²)` and the forward map `(a, 1)`; the tails differ.
example :
    let a : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1
    Pi.lift ![pt a, pt a] ≫ (triangularIso (grpObjOf (Multiplicative (ZMod 3))) 0).inv =
        Pi.lift ![pt a, pt (a * a)] ∧
      Pi.lift ![pt a, pt a] ≫ (triangularIso (grpObjOf (Multiplicative (ZMod 3))) 0).hom =
        Pi.lift ![pt a, pt 1] ∧
      a * a ≠ 1 := by
  refine ⟨?_, ?_, by decide⟩
  · rw [lift_pair_comp_triangularIso_inv, pt_mul]
  · rw [lift_pair_comp_triangularIso_hom, div_self', pt_one]

/-- The unit `1 + ε` of the dual numbers `ℚ[ε]`, with inverse `1 - ε`. -/
abbrev onePlusEps : (DualNumber ℚ)ˣ where
  val := 1 + DualNumber.eps
  inv := 1 - DualNumber.eps
  val_inv := by linear_combination (-1 : DualNumber ℚ) * DualNumber.eps_mul_eps (R := ℚ)
  inv_val := by linear_combination (-1 : DualNumber ℚ) * DualNumber.eps_mul_eps (R := ℚ)

-- In the unit group `ℚ[ε]ˣ`, viewed as a group object in `Type`, the forward map sends
-- `(1 + ε, 1)` to `(1 + ε, 1 - ε)`, and the inverse restores `(1 + ε, 1)`.
example :
    Pi.lift ![pt onePlusEps, pt 1] ≫ (triangularIso (grpObjOf (DualNumber ℚ)ˣ) 0).hom =
        Pi.lift ![pt onePlusEps, pt onePlusEps⁻¹] ∧
      ((onePlusEps⁻¹ : (DualNumber ℚ)ˣ) : DualNumber ℚ) = 1 - DualNumber.eps ∧
      Pi.lift ![pt onePlusEps, pt 1] ≫ (triangularIso (grpObjOf (DualNumber ℚ)ˣ) 0).hom ≫
        (triangularIso (grpObjOf (DualNumber ℚ)ˣ) 0).inv = Pi.lift ![pt onePlusEps, pt 1] := by
  refine ⟨?_, by simp [Units.inv_mk], by simp⟩
  rw [lift_pair_comp_triangularIso_hom, pt_div, one_div]

end Concrete

end TauCeti.Examples.GrpObjTriangular
