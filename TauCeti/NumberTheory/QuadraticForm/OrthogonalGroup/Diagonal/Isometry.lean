/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Diagonal.Finite
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Diagonal.Full
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic

/-!
# Isometric transport of rational adelic diagonals

A rational isometry induces compatible equivalences of the rational point groups and their local
scalar extensions. Whenever the local equivalences carry the reference subgroups onto one another
at almost every prime, they identify the finite adelic groups and carry the rational diagonal
subgroups onto one another. This is the left-subgroup compatibility needed to transport adelic
double-coset spaces. Adding the real place, the full adelic transports built from the scalar
extensions of the rational isometry carry the full adelic diagonal subgroups onto one another in
the same way. The assertions hold for orthogonal, special orthogonal and Spin points, without
nondegeneracy assumptions on the quadratic forms.

The proofs use the naturality of scalar extension, `restrictedProductCongrRight`, the full adelic
transports such as `TauCeti.QuadraticMap.OrthogonalCompactOpens.fullAdelicOrthogonalCongr`, and the
coordinate formulas for `rationalDiagonal`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
* A. Weil, *Adeles and Algebraic Groups* (1982), Chapter I.
-/

public section

namespace TauCeti.QuadraticMap.OrthogonalCompactOpens

open Filter
open _root_.QuadraticMap

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {Q : QuadraticForm ℚ V} {Q' : QuadraticForm ℚ W}
  (U : OrthogonalCompactOpens Q) (U' : OrthogonalCompactOpens Q')
  (e : Q.IsometryEquiv Q')

/-- Local transport by a rational isometry commutes with the orthogonal diagonal. -/
@[simp]
theorem restrictedProductCongrRight_finiteAdelicOrthogonalDiagonal
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) (g : orthogonalGroup Q) :
    restrictedProductCongrRight U.orthogonal U'.orthogonal
        (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).orthogonalGroupCongr) he
        (U.finiteAdelicOrthogonalDiagonal g) =
      U'.finiteAdelicOrthogonalDiagonal (e.orthogonalGroupCongr g) := by
  ext p : 1
  simp only [restrictedProductCongrRight_apply, finiteAdelicOrthogonalDiagonal_apply]
  exact (e.orthogonalGroupBaseChange_congr (A := ℚ_[p]) g).symm

/-- Isometric transport carries the rational orthogonal diagonal subgroup onto the target
rational diagonal subgroup. -/
theorem map_range_finiteAdelicOrthogonalDiagonal_of_isometry
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) :
    U.finiteAdelicOrthogonalDiagonal.range.map
        (restrictedProductCongrRight U.orthogonal U'.orthogonal
          (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).orthogonalGroupCongr) he :
          U.finiteAdelicOrthogonal →* U'.finiteAdelicOrthogonal) =
      U'.finiteAdelicOrthogonalDiagonal.range := by
  have hcomp :
      (restrictedProductCongrRight U.orthogonal U'.orthogonal
        (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).orthogonalGroupCongr) he :
          U.finiteAdelicOrthogonal →* U'.finiteAdelicOrthogonal).comp
          U.finiteAdelicOrthogonalDiagonal =
        U'.finiteAdelicOrthogonalDiagonal.comp
          (e.orthogonalGroupCongr : _ →* _) :=
    MonoidHom.ext (U.restrictedProductCongrRight_finiteAdelicOrthogonalDiagonal U' e he)
  rw [MonoidHom.map_range, hcomp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr e.orthogonalGroupCongr.surjective, ← MonoidHom.range_eq_map]

/-- Local transport by a rational isometry commutes with the Spin diagonal. -/
@[simp]
theorem restrictedProductCongrRight_finiteAdelicSpinDiagonal
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).spinGroupEquiv
      (U.spin p) (U'.spin p)) (g : spinGroup Q) :
    restrictedProductCongrRight U.spin U'.spin
        (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).spinGroupEquiv) he
        (U.finiteAdelicSpinDiagonal g) =
      U'.finiteAdelicSpinDiagonal (e.spinGroupEquiv g) := by
  ext p : 1
  simp only [restrictedProductCongrRight_apply, finiteAdelicSpinDiagonal_apply]
  exact (e.spinGroupBaseChange_spinGroupEquiv (A := ℚ_[p]) g).symm

/-- Isometric transport carries the rational Spin diagonal subgroup onto the target
rational diagonal subgroup. -/
theorem map_range_finiteAdelicSpinDiagonal_of_isometry
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).spinGroupEquiv
      (U.spin p) (U'.spin p)) :
    U.finiteAdelicSpinDiagonal.range.map
        (restrictedProductCongrRight U.spin U'.spin
          (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).spinGroupEquiv) he :
          U.finiteAdelicSpin →* U'.finiteAdelicSpin) =
      U'.finiteAdelicSpinDiagonal.range := by
  have hcomp :
      (restrictedProductCongrRight U.spin U'.spin
        (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).spinGroupEquiv) he :
          U.finiteAdelicSpin →* U'.finiteAdelicSpin).comp
          U.finiteAdelicSpinDiagonal =
        U'.finiteAdelicSpinDiagonal.comp
          (e.spinGroupEquiv : _ →* _) :=
    MonoidHom.ext (U.restrictedProductCongrRight_finiteAdelicSpinDiagonal U' e he)
  rw [MonoidHom.map_range, hcomp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr e.spinGroupEquiv.surjective, ← MonoidHom.range_eq_map]

section

variable [FiniteDimensional ℚ V] [FiniteDimensional ℚ W]

/-- Local transport by a rational isometry commutes with the special orthogonal diagonal. -/
@[simp]
theorem restrictedProductCongrRight_finiteAdelicSpecialOrthogonalDiagonal
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) (g : specialOrthogonalGroup Q) :
    restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
        (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr) he
        (U.finiteAdelicSpecialOrthogonalDiagonal g) =
      U'.finiteAdelicSpecialOrthogonalDiagonal (e.specialOrthogonalGroupCongr g) := by
  ext p : 1
  simp only [restrictedProductCongrRight_apply, finiteAdelicSpecialOrthogonalDiagonal_apply]
  exact (e.specialOrthogonalGroupBaseChange_congr (A := ℚ_[p]) g).symm

/-- Isometric transport carries the rational special orthogonal diagonal subgroup onto the target
rational diagonal subgroup. -/
theorem map_range_finiteAdelicSpecialOrthogonalDiagonal_of_isometry
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) :
    U.finiteAdelicSpecialOrthogonalDiagonal.range.map
        (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
          (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr) he :
          U.finiteAdelicSpecialOrthogonal →* U'.finiteAdelicSpecialOrthogonal) =
      U'.finiteAdelicSpecialOrthogonalDiagonal.range := by
  have hcomp :
      (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
        (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr) he :
          U.finiteAdelicSpecialOrthogonal →* U'.finiteAdelicSpecialOrthogonal).comp
          U.finiteAdelicSpecialOrthogonalDiagonal =
        U'.finiteAdelicSpecialOrthogonalDiagonal.comp
          (e.specialOrthogonalGroupCongr : _ →* _) :=
    MonoidHom.ext (U.restrictedProductCongrRight_finiteAdelicSpecialOrthogonalDiagonal U' e he)
  rw [MonoidHom.map_range, hcomp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr e.specialOrthogonalGroupCongr.surjective, ← MonoidHom.range_eq_map]

end

/-! ### Full adelic diagonals -/

section Full

/-- Full adelic transport by a rational isometry commutes with the orthogonal diagonal. -/
theorem fullAdelicOrthogonalCongr_comp_fullAdelicOrthogonalDiagonal
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) :
    (U.fullAdelicOrthogonalCongr U' (e.baseChange ℝ) (fun p ↦ e.baseChange ℚ_[p]) he :
        U.fullAdelicOrthogonal →* U'.fullAdelicOrthogonal).comp U.fullAdelicOrthogonalDiagonal =
      U'.fullAdelicOrthogonalDiagonal.comp (e.orthogonalGroupCongr : _ →* _) := by
  ext g : 1
  simp

/-- Full adelic transport by a rational isometry carries the rational orthogonal diagonal subgroup
onto the target rational diagonal subgroup. -/
theorem map_range_fullAdelicOrthogonalDiagonal_of_isometry
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) :
    U.fullAdelicOrthogonalDiagonal.range.map
        (U.fullAdelicOrthogonalCongr U' (e.baseChange ℝ) (fun p ↦ e.baseChange ℚ_[p]) he :
          U.fullAdelicOrthogonal →* U'.fullAdelicOrthogonal) =
      U'.fullAdelicOrthogonalDiagonal.range := by
  rw [MonoidHom.map_range, U.fullAdelicOrthogonalCongr_comp_fullAdelicOrthogonalDiagonal U' e he,
    MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.orthogonalGroupCongr.surjective,
    ← MonoidHom.range_eq_map]

/-- Full adelic transport by a rational isometry commutes with the Spin diagonal. -/
theorem fullAdelicSpinCongr_comp_fullAdelicSpinDiagonal
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).spinGroupEquiv
      (U.spin p) (U'.spin p)) :
    (U.fullAdelicSpinCongr U' (e.baseChange ℝ) (fun p ↦ e.baseChange ℚ_[p]) he :
        U.fullAdelicSpin →* U'.fullAdelicSpin).comp U.fullAdelicSpinDiagonal =
      U'.fullAdelicSpinDiagonal.comp (e.spinGroupEquiv : _ →* _) := by
  ext x : 1
  simp only [MonoidHom.comp_apply, MonoidHom.coe_ofClass,
    fullAdelicSpinCongr_apply, fullAdelicSpinDiagonal_apply,
    restrictedProductCongrRight_finiteAdelicSpinDiagonal, e.spinGroupBaseChange_spinGroupEquiv]

/-- Full adelic transport by a rational isometry carries the rational Spin diagonal subgroup
onto the target rational diagonal subgroup. -/
theorem map_range_fullAdelicSpinDiagonal_of_isometry
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).spinGroupEquiv
      (U.spin p) (U'.spin p)) :
    U.fullAdelicSpinDiagonal.range.map
        (U.fullAdelicSpinCongr U' (e.baseChange ℝ) (fun p ↦ e.baseChange ℚ_[p]) he :
          U.fullAdelicSpin →* U'.fullAdelicSpin) =
      U'.fullAdelicSpinDiagonal.range := by
  rw [MonoidHom.map_range, U.fullAdelicSpinCongr_comp_fullAdelicSpinDiagonal U' e he,
    MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.spinGroupEquiv.surjective,
    ← MonoidHom.range_eq_map]

variable [FiniteDimensional ℚ V] [FiniteDimensional ℚ W]

/-- Full adelic transport by a rational isometry commutes with the special orthogonal diagonal. -/
theorem fullAdelicSpecialOrthogonalCongr_comp_fullAdelicSpecialOrthogonalDiagonal
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) :
    (U.fullAdelicSpecialOrthogonalCongr U' (e.baseChange ℝ) (fun p ↦ e.baseChange ℚ_[p]) he :
        U.fullAdelicSpecialOrthogonal →* U'.fullAdelicSpecialOrthogonal).comp
        U.fullAdelicSpecialOrthogonalDiagonal =
      U'.fullAdelicSpecialOrthogonalDiagonal.comp (e.specialOrthogonalGroupCongr : _ →* _) := by
  ext g : 1
  simp

/-- Full adelic transport by a rational isometry carries the rational special orthogonal diagonal
subgroup onto the target rational diagonal subgroup. -/
theorem map_range_fullAdelicSpecialOrthogonalDiagonal_of_isometry
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) :
    U.fullAdelicSpecialOrthogonalDiagonal.range.map
        (U.fullAdelicSpecialOrthogonalCongr U' (e.baseChange ℝ) (fun p ↦ e.baseChange ℚ_[p]) he :
          U.fullAdelicSpecialOrthogonal →* U'.fullAdelicSpecialOrthogonal) =
      U'.fullAdelicSpecialOrthogonalDiagonal.range := by
  rw [MonoidHom.map_range,
    U.fullAdelicSpecialOrthogonalCongr_comp_fullAdelicSpecialOrthogonalDiagonal U' e he,
    MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.specialOrthogonalGroupCongr.surjective,
    ← MonoidHom.range_eq_map]

end Full

end TauCeti.QuadraticMap.OrthogonalCompactOpens
