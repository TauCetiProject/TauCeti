/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Naive
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveExactOrder.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.FiniteSubgroup
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.Data.ZMod.FinEquiv

/-!
# Comparison of naive and Drinfeld exact order

Where the level is invertible, a point has Drinfeld exact order precisely when it has exact
order in every geometric fibre. This comparison holds over arbitrary, possibly nonreduced base
schemes and identifies the Drinfeld and naive moduli problems for points of exact order.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.4 and §3.7.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}

variable {N : ℕ}

/-- Over an empty base every object of `Over S` is terminal, so every such object is a group
object and every morphism to a group object is a monoid homomorphism. -/
private theorem isOfExactOrder_of_isEmpty [IsEmpty S]
    {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} : E.IsOfExactOrder P N := by
  have ht (X : Over S) : IsTerminal X := by
    refine IsTerminal.ofUniqueHom (fun Y ↦ ?_) fun Y m ↦ ?_
    · have : IsEmpty Y.left := ⟨fun y ↦ isEmptyElim (Y.hom y)⟩
      exact Over.homMk (isInitialOfIsEmpty.to X.left) (isInitialOfIsEmpty.hom_ext _ _)
    · exact Over.OverMorphism.ext (by
        have : IsEmpty Y.left := ⟨fun y ↦ isEmptyElim (Y.hom y)⟩
        exact isInitialOfIsEmpty.hom_ext _ _)
  rw [isOfExactOrder_def]
  let X := Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap)
  let _ : MonObj X :=
    { one := (ht _).from _, mul := (ht _).from _, one_mul := (ht _).hom_ext _ _,
      mul_one := (ht _).hom_ext _ _, mul_assoc := (ht _).hom_ext _ _ }
  let _ : GrpObj X :=
    { inv := (ht _).from _, left_inv := (ht _).hom_ext _ _, right_inv := (ht _).hom_ext _ _ }
  exact ⟨inferInstance, { one_hom := (ht _).hom_ext _ _, mul_hom := (ht _).hom_ext _ _ }⟩

/-- A naive point of exact order is a Drinfeld point of exact order where the level is invertible.
This implication is valid over arbitrary, possibly nonreduced base schemes. -/
theorem IsOfNaiveExactOrder.isOfExactOrder
    {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (hP : E.IsOfNaiveExactOrder P N)
    (hN : ∀ s : S, (N : S.residueField s) ≠ 0) : E.IsOfExactOrder P N := by
  rcases eq_or_ne N 0 with rfl | hN0
  · have : IsEmpty S := ⟨fun s ↦ hN s (by simp)⟩
    exact isOfExactOrder_of_isEmpty
  have : NeZero N := ⟨hN0⟩
  let φ := (zmodMonoidHomEquiv N _).symm ⟨P, hP.pow_eq_one⟩
  have hφ1 : φ (.ofAdd 1) = P := zmodMonoidHomEquiv_symm_apply_ofAdd_one _
  have hφ : E.IsFiberwiseInjective φ :=
    isFiberwiseInjective_iff_isOfNaiveExactOrder.mpr (by rwa [hφ1])
  have hkill (a : Multiplicative (ZMod N)) : φ a ^ N = 1 := by
    rw [← map_pow]
    have : a ^ N = 1 := Multiplicative.toAdd.injective (by simp [nsmul_eq_mul])
    rw [this, map_one]
  have hgrp := hφ.exists_grpObj_isMonHom_pointsDivisor hN hkill
  have hI : E.multiplesDivisor P N = E.pointsDivisor φ := by
    rw [multiplesDivisor_eq_pointsDivisor]
    let e : Fin N ≃ Multiplicative (ZMod N) :=
      ((ZMod.finEquiv N).toEquiv.trans (Equiv.addRight 1)).trans Multiplicative.ofAdd
    have he (a : Fin N) : P ^ (a.val + 1) = φ (e a) := by
      rw [← hφ1, ← map_pow]
      congr 1
      apply Multiplicative.toAdd.injective
      simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
        _root_.mul_one, e, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe,
        RingEquiv.coe_toEquiv, Equiv.coe_addRight, ZMod.finEquiv_apply]
    simp_rw [he]
    exact E.pointsDivisor_comp_equiv φ e
  -- Transport the subgroup predicate as a whole; rewriting its dependent structure fields
  -- separately would retain the old inclusion's proof argument.
  let H (I : E.carrier.IdealSheafData) : Prop :=
    ∃ _ : GrpObj (Over.mk (I.subschemeι ≫ E.structureMap)),
      IsMonHom (Over.homMk I.subschemeι : Over.mk (I.subschemeι ≫ E.structureMap) ⟶
        Over.mk E.structureMap)
  exact isOfExactOrder_def.mpr ((congrArg H hI).mpr hgrp)

variable [NeZero N]

/-- Drinfeld and naive exact order agree where the level is invertible. -/
@[simp]
theorem isOfExactOrder_iff_isOfNaiveExactOrder
    {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    (hN : ∀ s : S, (N : S.residueField s) ≠ 0) :
    E.IsOfExactOrder P N ↔ E.IsOfNaiveExactOrder P N := by
  refine ⟨fun hP ↦ ?_, fun hP ↦ hP.isOfExactOrder hN⟩
  let φ := (zmodMonoidHomEquiv N _).symm ⟨P, hP.pow_eq_one⟩
  have hφ1 : φ (.ofAdd 1) = P := zmodMonoidHomEquiv_symm_apply_ofAdd_one _
  rw [← hφ1, ← isFiberwiseInjective_iff_isOfNaiveExactOrder]
  exact IsOfExactOrder.isFiberwiseInjective (by rwa [hφ1]) hN

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
