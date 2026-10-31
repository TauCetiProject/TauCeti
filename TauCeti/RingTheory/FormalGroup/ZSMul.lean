/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange

/-!
# Integer multiplication on formal groups

`FormalGroup.zsmulSeries` extends the native natural-number multiplication series to all
integers, using the group of substitutable power-series points. Negative indices use the
formal inverse, not coefficientwise negation. Substitution into a point with nilpotent
constant term computes integer multiplication on that point.

The addition and composition identities hold without commutativity of the formal group.
For a commutative formal group, integer multiplication is bundled as an endomorphism.
Multiplication series commute with coefficient base change and with every homomorphism;
in particular an isomorphism identifies them by conjugation of coordinates.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.2 and IV.4.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R)

/-- Multiplication by an integer on a formal group, evaluated at its tautological point. -/
noncomputable def zsmulSeries (n : ℤ) : PowerSeries R :=
  (n • F.tautologicalPoint).val

/-- Integer multiplication extends the existing natural-number multiplication series. -/
@[simp]
theorem zsmulSeries_natCast (n : ℕ) : F.zsmulSeries n = F.nsmulSeries n := by
  rw [zsmulSeries, natCast_zsmul, ← F.subst_nsmulSeries F.tautologicalPoint n,
    val_tautologicalPoint, PowerSeries.X_subst]

@[simp]
theorem zsmulSeries_zero : F.zsmulSeries 0 = 0 := by
  simpa using F.zsmulSeries_natCast 0

@[simp]
theorem zsmulSeries_one : F.zsmulSeries 1 = PowerSeries.X := by
  simpa using F.zsmulSeries_natCast 1

/-- Negating an index composes with the formal inverse. -/
theorem zsmulSeries_neg (n : ℤ) :
    F.zsmulSeries (-n) = PowerSeries.subst (F.zsmulSeries n) F.addInvX := by
  simp only [zsmulSeries, neg_zsmul, neg_apply]

/-- Multiplication by minus one is the formal inverse. -/
@[simp]
theorem zsmulSeries_neg_one : F.zsmulSeries (-1) = F.addInvX := by
  rw [zsmulSeries_neg, zsmulSeries_one, PowerSeries.X_subst]

/-- Every integer multiplication series has zero constant coefficient. -/
@[simp]
theorem constantCoeff_zsmulSeries (n : ℤ) : (F.zsmulSeries n).constantCoeff = 0 := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simp
  · rw [zsmulSeries_neg, zsmulSeries_natCast]
    exact PowerSeries.constantCoeff_subst_eq_zero (F.constantCoeff_nsmulSeries k) _
      F.constantCoeff_addInvX

/-- Integer multiplication series admit formal substitution. -/
theorem hasSubst_zsmulSeries (n : ℤ) : PowerSeries.HasSubst (F.zsmulSeries n) :=
  .of_constantCoeff_zero (F.constantCoeff_zsmulSeries n)

/-- Integer multiplication has linear coefficient equal to its index. -/
@[simp]
theorem coeff_one_zsmulSeries (n : ℤ) : PowerSeries.coeff 1 (F.zsmulSeries n) = n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simp
  · simp [zsmulSeries_neg, PowerSeries.coeff_one_subst (F.constantCoeff_nsmulSeries k)]

/-- Evaluating the integer multiplication series at a substitutable point computes its
integer multiple, including points with nonzero nilpotent constant coefficient. -/
theorem subst_zsmulSeries {σ : Type*} (x : F.Point σ) (n : ℤ) :
    PowerSeries.subst x.val (F.zsmulSeries n) = (n • x).val := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simpa using F.subst_nsmulSeries x k
  · rw [zsmulSeries_neg, zsmulSeries_natCast,
      PowerSeries.subst_comp_subst_apply
        (.of_constantCoeff_zero (F.constantCoeff_nsmulSeries k)) x.prop,
      F.subst_nsmulSeries, neg_zsmul, natCast_zsmul, neg_apply]

/-- The series of a sum of indices is the formal-group sum of their series. -/
theorem zsmulSeries_add (m n : ℤ) :
    F.zsmulSeries (m + n) = subst ![F.zsmulSeries m, F.zsmulSeries n] F.toPowerSeries := by
  simp only [zsmulSeries, add_zsmul, add_apply]

/-- The series of a product of indices is the composite of their series. -/
theorem zsmulSeries_mul (m n : ℤ) :
    F.zsmulSeries (m * n) = PowerSeries.subst (F.zsmulSeries n) (F.zsmulSeries m) := by
  rw [zsmulSeries, mul_zsmul, ← F.subst_zsmulSeries (n • F.tautologicalPoint) m]
  rfl

/-- The formal inverse commutes with every integer multiplication series. -/
theorem subst_addInvX_zsmulSeries (n : ℤ) :
    PowerSeries.subst F.addInvX (F.zsmulSeries n) = F.zsmulSeries (-n) := by
  simpa using (F.zsmulSeries_mul n (-1)).symm

/-- Integer multiplication commutes with base change of the coefficient ring. -/
@[simp]
theorem map_zsmulSeries (f : R →+* S) (n : ℤ) :
    PowerSeries.map f (F.zsmulSeries n) = (F.map f).zsmulSeries n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simp
  · rw [zsmulSeries_neg, zsmulSeries_neg, zsmulSeries_natCast, zsmulSeries_natCast]
    calc
      _ = PowerSeries.subst (PowerSeries.map f (F.nsmulSeries k))
          (PowerSeries.map f F.addInvX) :=
        PowerSeries.map_subst (.of_constantCoeff_zero (F.constantCoeff_nsmulSeries k)) _
      _ = _ := by rw [F.map_nsmulSeries, F.map_addInvX]

/-- Integer multiplication is an endomorphism when the formal group is commutative. -/
theorem subst_toPowerSeries_zsmulSeries [F.IsComm] (n : ℤ) :
    PowerSeries.subst F.toPowerSeries (F.zsmulSeries n) =
      subst (fun i ↦ (F.zsmulSeries n).toMvPowerSeries i) F.toPowerSeries := by
  let x : F.Point (Fin 2) := ⟨X 0, PowerSeries.HasSubst.X 0⟩
  let y : F.Point (Fin 2) := ⟨X 1, PowerSeries.HasSubst.X 1⟩
  have hxy : (x + y).val = F.toPowerSeries := by
    rw [add_apply]
    trans subst X F.toPowerSeries
    · congr 1
      funext i
      fin_cases i <;> rfl
    · rw [subst_self, id]
  conv_lhs => rw [← hxy]
  rw [F.subst_zsmulSeries, zsmul_add, add_apply]
  congr 1
  funext i
  rw [PowerSeries.toMvPowerSeries_eq_subst,
    F.subst_zsmulSeries ⟨X i, PowerSeries.HasSubst.X i⟩]
  fin_cases i <;> rfl

/-- Integer multiplication as a bundled endomorphism of a commutative formal group. -/
noncomputable def zsmulHom [F.IsComm] (n : ℤ) : TauCeti.FormalGroupHom F F where
  toPowerSeries := F.zsmulSeries n
  zero_constantCoeff := F.constantCoeff_zsmulSeries n
  hom := F.subst_toPowerSeries_zsmulSeries n

@[simp]
theorem zsmulHom_toPowerSeries [F.IsComm] (n : ℤ) :
    (F.zsmulHom n).toPowerSeries = F.zsmulSeries n := (rfl)

/-- The bundled integer endomorphism acts by integer multiplication on points. -/
@[simp]
theorem zsmulHom_applyPoint [F.IsComm] {σ : Type*} (x : F.Point σ) (n : ℤ) :
    (F.zsmulHom n).applyPoint x = n • x := by
  apply Subtype.ext
  simp [F.subst_zsmulSeries]

/-- On the additive formal group, integer multiplication is ordinary scalar multiplication. -/
@[simp]
theorem zsmulSeries_𝔾ₐ (n : ℤ) :
    (𝔾ₐ (R := R)).zsmulSeries n = (n : PowerSeries R) * PowerSeries.X := by
  have subst_neg_X {a : PowerSeries R} (ha : PowerSeries.HasSubst a) :
      PowerSeries.subst a (-PowerSeries.X : PowerSeries R) = -a := by
    rw [← PowerSeries.coe_substAlgHom ha, map_neg, PowerSeries.substAlgHom_X]
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simp
  · rw [zsmulSeries_neg, addInvX_𝔾ₐ,
      subst_neg_X ((𝔾ₐ (R := R)).hasSubst_zsmulSeries k)]
    simp

end FormalGroup

namespace TauCeti.FormalGroupHom

variable {R : Type*} [CommRing R] {F G : FormalGroup R}

/-- Every formal-group homomorphism commutes with integer multiplication, without any
commutativity assumption on its source or target. -/
theorem subst_zsmulSeries (f : FormalGroupHom F G) (n : ℤ) :
    PowerSeries.subst (F.zsmulSeries n) f.toPowerSeries =
      PowerSeries.subst f.toPowerSeries (G.zsmulSeries n) := by
  rw [FormalGroup.zsmulSeries]
  simpa only [toAddMonoidHom_apply, applyPoint_val, ← G.subst_zsmulSeries,
    FormalGroup.val_tautologicalPoint, PowerSeries.X_subst]
    using congrArg Subtype.val (map_zsmul (f.toAddMonoidHom Unit) n F.tautologicalPoint)

end TauCeti.FormalGroupHom

namespace TauCeti.FormalGroupIso

variable {R : Type*} [CommRing R] {F G : FormalGroup R}

/-- An isomorphism transports integer multiplication by conjugation with its forward
and inverse coordinates. -/
theorem zsmulSeries_eq_subst (f : FormalGroupIso F G) (n : ℤ) :
    G.zsmulSeries n = PowerSeries.subst f.invHom.toPowerSeries
      (PowerSeries.subst (F.zsmulSeries n) f.toHom.toPowerSeries) := by
  rw [f.toHom.subst_zsmulSeries,
    PowerSeries.subst_comp_subst_apply f.toHom.hasSubst f.invHom.hasSubst,
    f.subst_invHom_toHom, PowerSeries.X_subst]

end TauCeti.FormalGroupIso
