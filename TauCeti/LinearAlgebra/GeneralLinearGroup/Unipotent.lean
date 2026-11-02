/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
import TauCeti.LinearAlgebra.Charpoly.Nilpotent
import TauCeti.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Unipotent linear automorphisms

A linear automorphism is unipotent when its underlying endomorphism minus the identity is
nilpotent. This file records the elementary group-theoretic closure properties needed to use
unipotent elements in algebraic groups: inverses, products of commuting elements, powers, and
conjugates are unipotent.

It also records the rank-one rigidity statement: over a reduced base, a unipotent automorphism
of a free rank-one module is the identity.

Products require commutativity. Indeed, `gh - 1 = (g - 1)h + (h - 1)`; when `g` and `h` commute,
the first summand is nilpotent and commutes with the second.

## Main declarations

* `LinearMap.GeneralLinearGroup.IsUnipotent`: a linear automorphism is unipotent when its
  difference from the identity is nilpotent.
* `LinearMap.GeneralLinearGroup.isUnipotent_def`: the defining nilpotence criterion.
* `LinearMap.GeneralLinearGroup.isUnipotent_of_charpoly_eq`: the characteristic-polynomial
  sufficient condition over a commutative ring.
* `LinearMap.GeneralLinearGroup.isUnipotent_iff_charpoly`: the characteristic-polynomial
  criterion over a reduced commutative ring.
* `LinearMap.GeneralLinearGroup.isUnipotent_one`: the identity automorphism is unipotent.
* `LinearMap.GeneralLinearGroup.IsUnipotent.inv`: the inverse of a unipotent automorphism is
  unipotent.
* `LinearMap.GeneralLinearGroup.isUnipotent_ofLinearEquiv_iff`: unipotence after converting a
  linear equivalence to a general-linear-group element.
* `LinearMap.GeneralLinearGroup.isUnipotent_congrLinearEquiv_iff`: unipotence is invariant under
  transport by a semilinear equivalence.
* `LinearMap.GeneralLinearGroup.isUnipotent_inv_iff`: an automorphism is unipotent exactly when
  its inverse is.
* `LinearMap.GeneralLinearGroup.IsUnipotent.mul_of_commute`: commuting unipotent automorphisms have
  unipotent product.
* `LinearMap.GeneralLinearGroup.IsUnipotent.pow` and `.zpow`: every natural or integer power of a
  unipotent automorphism is unipotent.
* `LinearMap.GeneralLinearGroup.isUnipotent_conj_iff`: unipotence is invariant under
  conjugation.
* `LinearMap.GeneralLinearGroup.IsUnipotent.eq_one_of_finrank_eq_one`: a unipotent automorphism
  of a free rank-one module over a reduced commutative ring is the identity.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace LinearMap.GeneralLinearGroup

open _root_.Module

universe u v w

variable {K : Type u} {V : Type v} [Semiring K] [AddCommGroup V] [Module K V]

/-- A linear automorphism is unipotent if its difference from the identity is nilpotent. -/
def IsUnipotent (g : GeneralLinearGroup K V) : Prop :=
  _root_.IsNilpotent ((g : End K V) - 1)

/-- Unipotence of a linear automorphism means that its underlying endomorphism minus the
identity is nilpotent. -/
theorem isUnipotent_def (g : GeneralLinearGroup K V) :
    IsUnipotent g ↔ _root_.IsNilpotent ((g : End K V) - 1) :=
  Iff.rfl

/-- An automorphism of a finite free module over a commutative ring is unipotent if its
characteristic polynomial is a power of `X - 1`. -/
theorem isUnipotent_of_charpoly_eq
    {F : Type u} {W : Type v} [CommRing F] [AddCommGroup W] [Module F W]
    [Module.Free F W] [Module.Finite F W] (g : GeneralLinearGroup F W) {n : ℕ}
    (h : (g : End F W).charpoly = (Polynomial.X - 1) ^ n) :
    IsUnipotent g := by
  have hnil : ((g : End F W) - 1).charpoly = Polynomial.X ^ n := by
    simpa [h] using LinearMap.charpoly_sub_smul (g : End F W) 1
  exact ⟨n, by rw [← @Polynomial.aeval_X_pow F, ← hnil, LinearMap.aeval_self_charpoly]⟩

/-- Over a reduced commutative ring, an automorphism of a finite free module is unipotent exactly
when its characteristic polynomial is a power of `X - 1`. -/
theorem isUnipotent_iff_charpoly
    {F : Type u} {W : Type v} [CommRing F] [IsReduced F] [AddCommGroup W] [Module F W]
    [Module.Free F W] [Module.Finite F W] (g : GeneralLinearGroup F W) :
    IsUnipotent g ↔
      (g : End F W).charpoly = (Polynomial.X - 1) ^ Module.finrank F W := by
  refine ⟨fun h ↦ ?_, isUnipotent_of_charpoly_eq g⟩
  simpa using LinearMap.charpoly_eq_pow_of_isNilpotent_sub_smul (g : End F W) 1
    (by simpa using (isUnipotent_def g).mp h)

/-- The identity automorphism is unipotent. -/
@[simp]
theorem isUnipotent_one : IsUnipotent (1 : GeneralLinearGroup K V) := by
  simp [isUnipotent_def]

/-- A linear equivalence is unipotent after conversion to the general linear group exactly when
its underlying endomorphism minus the identity is nilpotent. -/
@[simp]
theorem isUnipotent_ofLinearEquiv_iff (f : V ≃ₗ[K] V) :
    IsUnipotent (LinearMap.GeneralLinearGroup.ofLinearEquiv f) ↔
      _root_.IsNilpotent (f.toLinearMap - 1) := by
  rw [isUnipotent_def, val_ofLinearEquiv]

/-- Unipotence of a linear automorphism is invariant under transport by a semilinear
equivalence. -/
theorem isUnipotent_congrLinearEquiv_iff
    {L : Type*} {W : Type w} [Semiring L] [AddCommGroup W] [Module L W]
    {σ : K →+* L} {σ' : L →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : V ≃ₛₗ[σ] W) (g : GeneralLinearGroup K V) :
    IsUnipotent (congrLinearEquiv e g) ↔ IsUnipotent g := by
  have h : LinearEquiv.conjRingEquiv e (g : End K V) =
      (e.symm.trans (g.toLinearEquiv.trans e)).toLinearMap := by
    ext x
    simp
  rw [congrLinearEquiv_apply, isUnipotent_ofLinearEquiv_iff, isUnipotent_def, ← h,
    ← map_one (LinearEquiv.conjRingEquiv e), ← map_sub]
  exact IsNilpotent.map_iff (LinearEquiv.conjRingEquiv e).injective

/-- The inverse of a unipotent linear automorphism is unipotent. -/
theorem IsUnipotent.inv {g : GeneralLinearGroup K V} (hg : IsUnipotent g) :
    IsUnipotent g⁻¹ := by
  have hc : Commute ((g⁻¹ : GeneralLinearGroup K V) : End K V) ((g : End K V) - 1) :=
    (Commute.units_val (Commute.refl g).inv_left).sub_right (Commute.one_right _)
  have heq : ((g⁻¹ : GeneralLinearGroup K V) : End K V) - 1 =
      -(((g⁻¹ : GeneralLinearGroup K V) : End K V) * ((g : End K V) - 1)) := by
    simp [mul_sub]
  rw [isUnipotent_def, heq]
  exact (hc.isNilpotent_mul_left hg).neg

/-- A linear automorphism is unipotent if and only if its inverse is unipotent. -/
@[simp]
theorem isUnipotent_inv_iff (g : GeneralLinearGroup K V) :
    IsUnipotent g⁻¹ ↔ IsUnipotent g :=
  ⟨fun hg ↦ inv_inv g ▸ hg.inv, IsUnipotent.inv⟩

/-- The product of two commuting unipotent linear automorphisms is unipotent. -/
theorem IsUnipotent.mul_of_commute {g h : GeneralLinearGroup K V}
    (hg : IsUnipotent g) (hh : IsUnipotent h) (hcomm : Commute g h) :
    IsUnipotent (g * h) := by
  rw [isUnipotent_def] at hg hh ⊢
  have hgh : Commute ((g : End K V) - 1) (h : End K V) :=
    hcomm.units_val.sub_left (Commute.one_left _)
  have hc : Commute (((g : End K V) - 1) * h) ((h : End K V) - 1) :=
    (hgh.sub_right (Commute.one_right _)).mul_left
      ((Commute.refl _).sub_right (Commute.one_right _))
  have heq : ((g * h : GeneralLinearGroup K V) : End K V) - 1 =
      ((g : End K V) - 1) * h + ((h : End K V) - 1) := by
    simp [sub_mul]
  rw [heq]
  exact hc.isNilpotent_add (hgh.isNilpotent_mul_right hg) hh

/-- Every natural power of a unipotent linear automorphism is unipotent. -/
theorem IsUnipotent.pow {g : GeneralLinearGroup K V} (hg : IsUnipotent g) (n : ℕ) :
    IsUnipotent (g ^ n) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ]
      exact hn.mul_of_commute hg (Commute.self_pow g n).symm

/-- Every integer power of a unipotent linear automorphism is unipotent. -/
theorem IsUnipotent.zpow {g : GeneralLinearGroup K V} (hg : IsUnipotent g) (n : ℤ) :
    IsUnipotent (g ^ n) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hg.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hg.pow n.succ).inv

/-- Unipotence is invariant under conjugation by a linear automorphism. -/
@[simp]
theorem isUnipotent_conj_iff (g h : GeneralLinearGroup K V) :
    IsUnipotent (h * g * h⁻¹) ↔ IsUnipotent g := by
  have heq : ((h * g * h⁻¹ : GeneralLinearGroup K V) : End K V) - 1 =
      h * ((g : End K V) - 1) * ↑h⁻¹ := by
    simp [mul_sub, sub_mul]
  rw [isUnipotent_def, isUnipotent_def, heq]
  simp [IsNilpotent, Units.conj_pow]

/-- A unipotent automorphism of a free rank-one module over a reduced commutative ring is the
identity. -/
theorem IsUnipotent.eq_one_of_finrank_eq_one
    {F : Type u} {W : Type v} [CommRing F] [IsReduced F]
    [AddCommGroup W] [Module F W] [Module.Free F W]
    {g : GeneralLinearGroup F W} (hg : IsUnipotent g) (hdim : finrank F W = 1) :
    g = 1 := by
  cases subsingleton_or_nontrivial F
  · have := Module.subsingleton F W
    exact Subsingleton.elim _ _
  -- Every endomorphism of `W` is a homothety `c • id`, and `algebraMap` is injective.
  let e := LinearEquiv.smul_id_of_finrank_eq_one (M := W) hdim
  obtain ⟨c, hc⟩ := e.surjective g
  have hinj : Function.Injective (algebraMap F (End F W)) :=
    fun a b hab ↦ e.injective (by simpa [e, Module.algebraMap_end_eq_smul_id] using hab)
  have hEnd : (g : End F W) - 1 = algebraMap F (End F W) (c - 1) := by
    simp [← hc, e, Module.algebraMap_end_eq_smul_id, sub_smul, Module.End.one_eq_id]
  rw [isUnipotent_def, hEnd, IsNilpotent.map_iff hinj] at hg
  refine Units.ext (sub_eq_zero.mp ?_)
  rw [Units.val_one, hEnd, hg.eq_zero, map_zero]

end LinearMap.GeneralLinearGroup
