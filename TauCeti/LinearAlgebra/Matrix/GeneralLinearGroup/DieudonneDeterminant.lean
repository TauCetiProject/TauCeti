/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stability

/-!
# The Dieudonné determinant and `K₁` of a division ring

For a division ring `D` the determinant of a matrix cannot take values in `D`, but it does take
values in the abelianization `Dˣ/[Dˣ, Dˣ]` of the unit group. This file constructs this
**Dieudonné determinant** `GLₙ(D) → Dˣ/[Dˣ, Dˣ]` on invertible `n × n` matrices, together with
its extension to all `2 × 2` matrices by a zero adjoined for singular ones, and computes algebraic
`K₁` of `D`.

For `2 × 2` matrices the determinant is given by an explicit formula. Writing a matrix as
`!![a, b; c, d]` and `[x]` for the class of a nonzero `x`, it is `[a d]` when `c = 0`, and
`[c (a c⁻¹ d - b)]` when `c ≠ 0`; it is multiplicative, vanishes exactly on singular matrices, and
is one on elementary matrices.

Division rings have Bass stable range one, so by the stability theorems `K₁(D)` is the quotient of
`GL₂(D)` by its elementary subgroup, and also the quotient of `GL₁(D) = Dˣ`. The `2 × 2`
determinant thus descends to `K₁(D)`, where it inverts the map induced by the class of the
`1 × 1` matrix `(u)`. Hence `K₁(D) ≃* Dˣ/[Dˣ, Dˣ]`, which for a field `F` is `K₁(F) = Fˣ`.

Composing with the class map gives the Dieudonné determinant on `GLₙ(D)` for every finite index
type: a homomorphism to `Dˣ/[Dˣ, Dˣ]` that sends a diagonal matrix to the product of the classes
of its entries, is surjective as soon as there is an index, and whose kernel is the elementary
subgroup `Eₙ(D)` as soon as there are at least two indices. With a single index `E₁(D)` is
trivial, while the determinant of `(u)` is the class of `u`, trivial for every commutator `u`.

## Main definitions

* `TauCeti.abelianizationClass`: the class of an element of a group with zero in the
  abelianization of its unit group, with a zero adjoined.
* `TauCeti.dieudonneDetFinTwo`: the Dieudonné determinant of `2 × 2` matrices, a monoid with zero
  homomorphism to `WithZero (Group.Abelianization Dˣ)`.
* `TauCeti.AlgebraicK1.divisionRingEquiv`: the isomorphism `K₁(D) ≃* Dˣ/[Dˣ, Dˣ]`.
* `TauCeti.dieudonneDet`: the Dieudonné determinant `GL n D →* Dˣ/[Dˣ, Dˣ]`.

## Main results

* `TauCeti.dieudonneDetFinTwo_eq_zero_iff`: the `2 × 2` determinant vanishes exactly on
  non-invertible matrices.
* `TauCeti.AlgebraicK1.divisionRingEquiv_ofUnits`: the isomorphism sends the class of `(u)` to the
  class of `u`; `TauCeti.kOne_divisionRing` restates this as an existence statement.
* `TauCeti.dieudonneDet_diagGL`: the determinant of a diagonal matrix is the product of the classes
  of its entries.
* `TauCeti.ker_dieudonneDet`: with at least two indices the kernel is the elementary subgroup.
* `TauCeti.dieudonne_determinant`: the Dieudonné determinant theorem, as an existence statement.

## Implementation notes

Multiplicativity of the `2 × 2` formula is checked on left multiplication by upper triangular
matrices and by the rotation `!![0, -1; 1, 0]`; this suffices because every matrix whose lower
left entry is nonzero is a product of an upper triangular matrix, the rotation and a unipotent upper
triangular matrix.

## References

* J. Dieudonné, *Les déterminants sur un corps non commutatif*, Bull. Soc. Math. France 71
  (1943), 27–45.
* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter IV, §1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, 1.2.4, Example 1.3.5 and Exercise 1.2.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

/-! ## Classes of elements of a group with zero -/

section GroupWithZero

variable (G₀ : Type*) [GroupWithZero G₀]

open Classical in
/-- The class of an element of a group with zero `G₀` in the abelianization of its unit group,
with a zero adjoined: `0` goes to `0`, and a unit `u` to its abelianization class. This is the
Dieudonné determinant of a `1 × 1` matrix. -/
def abelianizationClass : G₀ →*₀ WithZero (Group.Abelianization G₀ˣ) :=
  (WithZero.map' Group.Abelianization.of).comp (WithZero.withZeroUnitsEquiv (G := G₀)).symm

variable {G₀}

/-- `abelianizationClass` sends a unit to its abelianization class. -/
@[simp]
theorem abelianizationClass_units (u : G₀ˣ) :
    abelianizationClass G₀ u = Group.Abelianization.of u := by
  classical
  simp [abelianizationClass]

end GroupWithZero

/-! ## The Dieudonné determinant of `2 × 2` matrices -/

section FinTwo

variable {D : Type*} [DivisionRing D]

local notation "ν" => abelianizationClass D

open Classical in
/-- The formula underlying `TauCeti.dieudonneDetFinTwo`. -/
private def detTwo (M : Matrix (Fin 2) (Fin 2) D) : WithZero (Group.Abelianization Dˣ) :=
  if M 1 0 = 0 then ν (M 0 0 * M 1 1) else ν (M 1 0 * (M 0 0 * (M 1 0)⁻¹ * M 1 1 - M 0 1))

private theorem detTwo_of_eq_zero {M : Matrix (Fin 2) (Fin 2) D} (h : M 1 0 = 0) :
    detTwo M = ν (M 0 0 * M 1 1) := by
  simp [detTwo, h]

private theorem detTwo_of_ne_zero {M : Matrix (Fin 2) (Fin 2) D} (h : M 1 0 ≠ 0) :
    detTwo M = ν (M 1 0 * (M 0 0 * (M 1 0)⁻¹ * M 1 1 - M 0 1)) := by
  simp [detTwo, h]

/-- The formula on a matrix literal with vanishing lower left entry. -/
private theorem detTwo_of_mk_zero (a b d : D) : detTwo !![a, b; 0, d] = ν (a * d) :=
  detTwo_of_eq_zero (by simp)

/-- The formula on a matrix literal with nonzero lower left entry. -/
private theorem detTwo_of_mk_ne_zero {a b c d : D} (hc : c ≠ 0) :
    detTwo !![a, b; c, d] = ν (c * (a * c⁻¹ * d - b)) :=
  detTwo_of_ne_zero (by simpa using hc)

private theorem detTwo_one : detTwo (1 : Matrix (Fin 2) (Fin 2) D) = 1 := by
  simp [detTwo_of_eq_zero]

/-- The formula is multiplicative on left multiplication by an upper triangular matrix. -/
private theorem detTwo_upper_mul (p q r : D) (M : Matrix (Fin 2) (Fin 2) D) :
    detTwo (!![p, q; 0, r] * M) = detTwo !![p, q; 0, r] * detTwo M := by
  have hpM : !![p, q; 0, r] * M =
      !![p * M 0 0 + q * M 1 0, p * M 0 1 + q * M 1 1; r * M 1 0, r * M 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  rw [hpM, detTwo_of_mk_zero]
  by_cases hc : M 1 0 = 0
  · simp only [hc, mul_zero, add_zero, detTwo_of_mk_zero, detTwo_of_eq_zero hc, map_mul]
    ac_rfl
  by_cases hr : r = 0
  · simp [hr, detTwo_of_mk_zero]
  have key : (p * M 0 0 + q * M 1 0) * (r * M 1 0)⁻¹ * (r * M 1 1) - (p * M 0 1 + q * M 1 1) =
      p * (M 0 0 * (M 1 0)⁻¹ * M 1 1 - M 0 1) := by
    simp only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ hr, add_mul,
      mul_inv_cancel_left₀ hc]
    noncomm_ring
  rw [detTwo_of_mk_ne_zero (mul_ne_zero hr hc), detTwo_of_ne_zero hc, key]
  simp only [map_mul]
  ac_rfl

/-- The formula is unchanged by left multiplication by the rotation `!![0, -1; 1, 0]`. -/
private theorem detTwo_w_mul (M : Matrix (Fin 2) (Fin 2) D) :
    detTwo (!![0, -1; 1, 0] * M) = detTwo M := by
  have hwM : !![0, -1; 1, 0] * M = !![-M 1 0, -M 1 1; M 0 0, M 0 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  rw [hwM]
  by_cases ha : M 0 0 = 0
  · rw [ha, detTwo_of_mk_zero]
    by_cases hc : M 1 0 = 0
    · simp [detTwo_of_eq_zero hc, ha, hc]
    · simp [detTwo_of_ne_zero hc, ha]
  by_cases hc : M 1 0 = 0
  · simp [detTwo_of_mk_ne_zero ha, detTwo_of_eq_zero hc, hc]
  have key : M 0 0 * (-M 1 0 * (M 0 0)⁻¹ * M 0 1 - -M 1 1) =
      M 0 0 * M 1 0 * (M 0 0)⁻¹ * (M 0 0 * (M 1 0)⁻¹ * M 1 1 - M 0 1) := by
    have e : M 0 0 * M 1 0 * (M 0 0)⁻¹ * (M 0 0 * (M 1 0)⁻¹ * M 1 1) = M 0 0 * M 1 1 := by
      simp [mul_assoc, inv_mul_cancel_left₀ ha, mul_inv_cancel_left₀ hc]
    rw [mul_sub (M 0 0 * M 1 0 * (M 0 0)⁻¹), e]
    noncomm_ring
  have hνa : ν (M 0 0) ≠ 0 := (map_ne_zero _).mpr ha
  rw [detTwo_of_mk_ne_zero ha, detTwo_of_ne_zero hc, key]
  simp only [map_mul, map_inv₀]
  field_simp

/-- A `2 × 2` matrix with nonzero lower left entry is an upper triangular matrix times the rotation
`!![0, -1; 1, 0]` times a unipotent upper triangular matrix. -/
private theorem eq_upper_mul_w_mul_upper (M : Matrix (Fin 2) (Fin 2) D) (hc : M 1 0 ≠ 0) :
    M = !![M 0 0 * (M 1 0)⁻¹ * M 1 1 - M 0 1, M 0 0; 0, M 1 0] * !![0, -1; 1, 0] *
      !![1, (M 1 0)⁻¹ * M 1 1; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, mul_assoc, mul_inv_cancel_left₀ hc]

private theorem detTwo_mul (N M : Matrix (Fin 2) (Fin 2) D) :
    detTwo (N * M) = detTwo N * detTwo M := by
  by_cases hc : N 1 0 = 0
  · rw [Matrix.eta_fin_two N, hc]
    exact detTwo_upper_mul _ _ _ M
  have h : ∀ M, detTwo (N * M) = detTwo !![N 0 0 * (N 1 0)⁻¹ * N 1 1 - N 0 1, N 0 0; 0, N 1 0] *
      detTwo !![1, (N 1 0)⁻¹ * N 1 1; 0, 1] * detTwo M := by
    intro M
    conv_lhs => rw [eq_upper_mul_w_mul_upper N hc]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, detTwo_upper_mul, detTwo_w_mul, detTwo_upper_mul]
    exact (mul_assoc ..).symm
  have h1 := h 1
  rw [Matrix.mul_one, detTwo_one, mul_one] at h1
  rw [h, h1]

variable (D) in
/-- The **Dieudonné determinant** of `2 × 2` matrices over a division ring `D`, with values in the
abelianization of `Dˣ` with a zero adjoined. Writing `[x]` for `abelianizationClass D x`, the
matrix `!![a, b; c, d]` goes to `[a d]` when `c = 0` and to `[c (a c⁻¹ d - b)]` when `c ≠ 0`. -/
def dieudonneDetFinTwo : Matrix (Fin 2) (Fin 2) D →*₀ WithZero (Group.Abelianization Dˣ) where
  toFun := detTwo
  map_zero' := by rw [detTwo_of_eq_zero (by simp)]; simp
  map_one' := detTwo_one
  map_mul' := detTwo_mul

/-- The Dieudonné determinant of a `2 × 2` matrix whose lower left entry vanishes is the class of
the product of its diagonal entries. -/
theorem dieudonneDetFinTwo_apply_of_eq_zero {M : Matrix (Fin 2) (Fin 2) D} (h : M 1 0 = 0) :
    dieudonneDetFinTwo D M = abelianizationClass D (M 0 0 * M 1 1) :=
  detTwo_of_eq_zero h

/-- The Dieudonné determinant of a `2 × 2` matrix `!![a, b; c, d]` with `c ≠ 0` is the class of
`c (a c⁻¹ d - b)`. -/
theorem dieudonneDetFinTwo_apply_of_ne_zero {M : Matrix (Fin 2) (Fin 2) D} (h : M 1 0 ≠ 0) :
    dieudonneDetFinTwo D M = abelianizationClass D (M 1 0 * (M 0 0 * (M 1 0)⁻¹ * M 1 1 - M 0 1)) :=
  detTwo_of_ne_zero h

/-- The Dieudonné determinant of an upper triangular `2 × 2` matrix is the class of the product of
its diagonal entries. -/
@[simp]
theorem dieudonneDetFinTwo_upperTriangular (a b d : D) :
    dieudonneDetFinTwo D !![a, b; 0, d] = abelianizationClass D (a * d) :=
  dieudonneDetFinTwo_apply_of_eq_zero (by simp)

/-- Elementary `2 × 2` matrices `1 + a Eᵢⱼ`, `i ≠ j`, have Dieudonné determinant one. -/
@[simp]
theorem dieudonneDetFinTwo_one_add_single {i j : Fin 2} (hij : i ≠ j) (a : D) :
    dieudonneDetFinTwo D (1 + single i j a) = 1 := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · rw [dieudonneDetFinTwo_apply_of_eq_zero (by simp)]
    simp
  · by_cases ha : a = 0
    · simp [ha]
    rw [dieudonneDetFinTwo_apply_of_ne_zero (by simpa using ha)]
    simp [ha]
  · exact absurd rfl hij

private theorem isUnit_upperTriangular {a d : D} (b : D) (ha : a ≠ 0) (hd : d ≠ 0) :
    IsUnit !![a, b; 0, d] := by
  refine ⟨⟨!![a, b; 0, d], !![a⁻¹, -(a⁻¹ * b * d⁻¹); 0, d⁻¹], ?_, ?_⟩, rfl⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, ha, hd, mul_assoc]

private theorem isUnit_rotation : IsUnit (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) D) := by
  refine ⟨⟨!![0, -1; 1, 0], !![0, 1; -1, 0], ?_, ?_⟩, rfl⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- The Dieudonné determinant of a `2 × 2` matrix vanishes exactly when the matrix is not
invertible. -/
theorem dieudonneDetFinTwo_eq_zero_iff {M : Matrix (Fin 2) (Fin 2) D} :
    dieudonneDetFinTwo D M = 0 ↔ ¬IsUnit M := by
  refine ⟨fun h ⟨u, hu⟩ ↦ ?_, fun h ↦ by_contra fun h0 ↦ h ?_⟩
  · have := congrArg (dieudonneDetFinTwo D) u.mul_inv
    rw [map_mul, hu, h, zero_mul, map_one] at this
    exact zero_ne_one this
  by_cases hc : M 1 0 = 0
  · rw [dieudonneDetFinTwo_apply_of_eq_zero hc, map_eq_zero] at h0
    rw [Matrix.eta_fin_two M, hc]
    exact isUnit_upperTriangular _ (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0)
  rw [dieudonneDetFinTwo_apply_of_ne_zero hc, map_eq_zero] at h0
  rw [eq_upper_mul_w_mul_upper M hc]
  exact ((isUnit_upperTriangular _ (right_ne_zero_of_mul h0) hc).mul isUnit_rotation).mul
    (isUnit_upperTriangular _ one_ne_zero one_ne_zero)

end FinTwo

/-! ## `K₁` of a division ring -/

section KOne

variable {D : Type*} [DivisionRing D]

namespace AlgebraicK1

/-- The Dieudonné determinant of invertible `2 × 2` matrices, with values in the abelianization of
`Dˣ`. -/
private def dieudonneDetGLFinTwo : GL (Fin 2) D →* Group.Abelianization Dˣ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp (Units.map (dieudonneDetFinTwo D))

private theorem coe_dieudonneDetGLFinTwo (g : GL (Fin 2) D) :
    (dieudonneDetGLFinTwo g : WithZero (Group.Abelianization Dˣ)) = dieudonneDetFinTwo D g := by
  simp [dieudonneDetGLFinTwo]

private theorem ker_mk_two_le : (mk D 2).ker ≤ dieudonneDetGLFinTwo.ker := by
  rw [ker_mk_eq_elementarySubgroup (hasStableRangeLE_one_of_isLocalRing D) le_rfl,
    elementarySubgroup_le_iff]
  intro i j hij a
  rw [MonoidHom.mem_ker, ← WithZero.coe_inj, coe_dieudonneDetGLFinTwo,
    coe_transvectionUnit_eq_one_add_single, dieudonneDetFinTwo_one_add_single hij, WithZero.coe_one]

/-- The homomorphism `K₁(D) →* Dˣ/[Dˣ, Dˣ]` induced by the `2 × 2` Dieudonné determinant, through
the identification of `K₁(D)` with a quotient of `GL₂(D)`. -/
private def toAbelianization : AlgebraicK1 D →* Group.Abelianization Dˣ :=
  (QuotientGroup.lift _ dieudonneDetGLFinTwo ker_mk_two_le).comp
    (quotientKerMkEquiv (hasStableRangeLE_one_of_isLocalRing D)
      (by norm_num : 1 ≤ 2)).symm.toMonoidHom

private theorem toAbelianization_mk_two (g : GL (Fin 2) D) :
    toAbelianization (mk D 2 g) = dieudonneDetGLFinTwo g := by
  rw [toAbelianization, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← quotientKerMkEquiv_mk (hasStableRangeLE_one_of_isLocalRing D) (by norm_num : 1 ≤ 2) g,
    MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]

private theorem toAbelianization_ofUnits (d : Dˣ) :
    toAbelianization (ofUnits D d) = Group.Abelianization.of d := by
  rw [ofUnits_apply, ← mk_stabilizeGL (by norm_num : 1 ≤ 2), toAbelianization_mk_two,
    ← WithZero.coe_inj, coe_dieudonneDetGLFinTwo,
    dieudonneDetFinTwo_apply_of_eq_zero (by simp [coe_stabilizeGL_apply])]
  simp [coe_stabilizeGL_apply]

variable (D) in
/-- **`K₁` of a division ring**: algebraic `K₁(D)` is the abelianization `Dˣ/[Dˣ, Dˣ]` of the unit
group, the class of the `1 × 1` matrix `(u)` corresponding to the class of `u`. For a field `F`
this is `K₁(F) = Fˣ`. -/
def divisionRingEquiv : AlgebraicK1 D ≃* Group.Abelianization Dˣ :=
  toAbelianization.toMulEquiv (Group.Abelianization.lift (ofUnits D))
    (MonoidHom.ext fun x ↦ by
      obtain ⟨d, rfl⟩ := ofUnits_surjective (hasStableRangeLE_one_of_isLocalRing D) x
      simp [toAbelianization_ofUnits])
    (Group.Abelianization.hom_ext _ _ (MonoidHom.ext fun d ↦ by simp [toAbelianization_ofUnits]))

/-- The isomorphism `K₁(D) ≃* Dˣ/[Dˣ, Dˣ]` sends the class of the `1 × 1` matrix `(u)` to the class
of `u`. -/
@[simp]
theorem divisionRingEquiv_ofUnits (u : Dˣ) :
    divisionRingEquiv D (ofUnits D u) = Group.Abelianization.of u :=
  toAbelianization_ofUnits u

/-- The inverse of `K₁(D) ≃* Dˣ/[Dˣ, Dˣ]` sends the class of `u` to the class of the `1 × 1`
matrix `(u)`. -/
@[simp]
theorem divisionRingEquiv_symm_of (u : Dˣ) :
    (divisionRingEquiv D).symm (Group.Abelianization.of u) = ofUnits D u := by
  rw [MulEquiv.symm_apply_eq, divisionRingEquiv_ofUnits]

/-- On the class of an invertible `2 × 2` matrix, the isomorphism `K₁(D) ≃* Dˣ/[Dˣ, Dˣ]` is the
`2 × 2` Dieudonné determinant. -/
theorem coe_divisionRingEquiv_mk_two (g : GL (Fin 2) D) :
    (divisionRingEquiv D (mk D 2 g) : WithZero (Group.Abelianization Dˣ)) =
      dieudonneDetFinTwo D g :=
  (congrArg _ (toAbelianization_mk_two g)).trans (coe_dieudonneDetGLFinTwo g)

end AlgebraicK1

/-- **`K₁` of a division ring** (Weibel, *The K-book*, III.1.3.5): `K₁(D) ≅ Dˣ/[Dˣ, Dˣ]`, sending
the class of the `1 × 1` matrix `(d)` to the class of `d`. -/
theorem kOne_divisionRing (D : Type*) [DivisionRing D] :
    ∃ e : AlgebraicK1 D ≃* Group.Abelianization Dˣ, ∀ d : Dˣ,
      e (AlgebraicK1.mk D 1
        (Units.map (Matrix.scalar (Fin 1) : D →+* Matrix (Fin 1) (Fin 1) D).toMonoidHom d)) =
        Group.Abelianization.of d :=
  ⟨AlgebraicK1.divisionRingEquiv D, fun d ↦ by
    have h : Units.map (Matrix.scalar (Fin 1) : D →+* Matrix (Fin 1) (Fin 1) D).toMonoidHom d =
        GeneralLinearGroup.scalar (Fin 1) d :=
      Units.ext (by simp)
    rw [h, ← AlgebraicK1.ofUnits_apply, AlgebraicK1.divisionRingEquiv_ofUnits]⟩

end KOne

/-! ## The Dieudonné determinant of invertible matrices -/

section DieudonneDet

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] {D : Type*}
  [DivisionRing D]

variable (n D) in
/-- The **Dieudonné determinant** `GL n D →* Dˣ/[Dˣ, Dˣ]` of a division ring `D`: the class in
`K₁(D) ≃* Dˣ/[Dˣ, Dˣ]` of an invertible matrix, after enumerating the indices. It does not depend
on the enumeration (`TauCeti.dieudonneDet_reindexGL`). -/
def dieudonneDet : GL n D →* Group.Abelianization Dˣ :=
  (AlgebraicK1.divisionRingEquiv D).toMonoidHom.comp
    ((AlgebraicK1.mk D (Fintype.card n)).comp ((Fintype.equivFin n).reindexGL D).toMonoidHom)

/-- The Dieudonné determinant does not change when the indices are relabelled. -/
@[simp]
theorem dieudonneDet_reindexGL (e : n ≃ m) (g : GL n D) :
    dieudonneDet m D (e.reindexGL D g) = dieudonneDet n D g := by
  have h : (Fintype.equivFin m).reindexGL D (e.reindexGL D g) =
      ((Fintype.equivFin n).symm.trans (e.trans (Fintype.equivFin m))).reindexGL D
        ((Fintype.equivFin n).reindexGL D g) := by
    ext i j
    simp
  simp only [dieudonneDet, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [h, AlgebraicK1.mk_reindexGL]

/-- On `Fin k`, the Dieudonné determinant of an invertible matrix is the image of its class in
`K₁(D)`. -/
theorem dieudonneDet_fin_apply {k : ℕ} (g : GL (Fin k) D) :
    dieudonneDet (Fin k) D g = AlgebraicK1.divisionRingEquiv D (AlgebraicK1.mk D k g) := by
  simp [dieudonneDet]

/-- On invertible `2 × 2` matrices the Dieudonné determinant is `TauCeti.dieudonneDetFinTwo`. -/
theorem coe_dieudonneDet_fin_two (g : GL (Fin 2) D) :
    (dieudonneDet (Fin 2) D g : WithZero (Group.Abelianization Dˣ)) = dieudonneDetFinTwo D g := by
  rw [dieudonneDet_fin_apply, AlgebraicK1.coe_divisionRingEquiv_mk_two]

/-- Elementary matrices have Dieudonné determinant one. -/
@[simp]
theorem dieudonneDet_transvectionUnit {i j : n} (hij : i ≠ j) (a : D) :
    dieudonneDet n D (transvectionUnit hij a) = 1 := by
  rw [← dieudonneDet_reindexGL (Fintype.equivFin n), Equiv.reindexGL_transvectionUnit,
    dieudonneDet_fin_apply, AlgebraicK1.elementarySubgroup_le_ker_mk _
      (transvectionUnit_mem_elementarySubgroup _ _), map_one]

/-- The Dieudonné determinant of the diagonal matrix with one diagonal entry `d` and all others `1`
is the class of `d`. -/
@[simp]
theorem dieudonneDet_diagGL_mulSingle (i : n) (d : Dˣ) :
    dieudonneDet n D (diagGL (Pi.mulSingle i d)) = Group.Abelianization.of d := by
  have hk : 1 ≤ Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
  let e : n ≃ Fin (Fintype.card n) :=
    (Fintype.equivFin n).trans (Equiv.swap (Fintype.equivFin n i) ⟨0, hk⟩)
  have he : e i = ⟨0, hk⟩ := by simp [e]
  have hdiag : e.reindexGL D (diagGL (Pi.mulSingle i d)) =
      stabilizeGL D hk (Matrix.GeneralLinearGroup.scalar (Fin 1) d) := by
    ext a b
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    have key : ∀ c : n, (e c : ℕ) < 1 ↔ c = i := fun c ↦ by
      rw [Nat.lt_one_iff, ← e.injective.eq_iff, he, Fin.ext_iff]
    simp only [Equiv.coe_reindexGL, submatrix_apply, Equiv.symm_apply_apply, diagGL_coe,
      diagonal_apply, coe_stabilizeGL_apply, key, e.apply_eq_iff_eq, Matrix.one_apply]
    by_cases ha : a = i <;> by_cases hb : b = i <;> simp [ha, hb, Ne.symm]
  rw [← dieudonneDet_reindexGL e, hdiag, dieudonneDet_fin_apply, AlgebraicK1.mk_stabilizeGL,
    ← AlgebraicK1.ofUnits_apply, AlgebraicK1.divisionRingEquiv_ofUnits]

/-- The Dieudonné determinant of an invertible diagonal matrix is the product of the classes of its
diagonal entries. -/
theorem dieudonneDet_diagGL (t : n → Dˣ) :
    dieudonneDet n D (diagGL t) = ∏ i, Group.Abelianization.of (t i) := by
  -- the diagonal matrix with entries `t i` for `i ∈ s` and `1` elsewhere
  have key : ∀ s : Finset n, dieudonneDet n D (diagGL fun i ↦ if i ∈ s then t i else 1) =
      ∏ i ∈ s, Group.Abelianization.of (t i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [← Pi.one_def]
    | insert a s ha ih =>
      have hsplit : (fun i ↦ if i ∈ insert a s then t i else 1) =
          (fun i ↦ if i ∈ s then t i else 1) * Pi.mulSingle a (t a) := by
        funext i
        by_cases hi : i = a
        · subst hi
          simp [ha]
        · simp [hi, Finset.mem_insert]
      rw [hsplit, map_mul, map_mul, ih, dieudonneDet_diagGL_mulSingle, Finset.prod_insert ha,
        mul_comm]
  simpa using key Finset.univ

/-- The Dieudonné determinant is surjective as soon as there is an index. -/
theorem dieudonneDet_surjective [Nonempty n] : Function.Surjective (dieudonneDet n D) := by
  intro x
  obtain ⟨d, rfl⟩ := Group.Abelianization.surjective_of _ x
  exact ⟨_, dieudonneDet_diagGL_mulSingle (Classical.arbitrary n) d⟩

/-- **Dieudonné**: with at least two indices, the kernel of the Dieudonné determinant is the
elementary subgroup. -/
theorem ker_dieudonneDet (hn : 2 ≤ Fintype.card n) :
    (dieudonneDet n D).ker = elementarySubgroup n D := by
  ext g
  simp only [MonoidHom.mem_ker, dieudonneDet, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  rw [← MonoidHom.mem_ker,
    AlgebraicK1.ker_mk_eq_elementarySubgroup (hasStableRangeLE_one_of_isLocalRing D) hn,
    Equiv.reindexGL_mem_elementarySubgroup_iff]

/-- **The Dieudonné determinant** (Weibel, *The K-book*, III.1.2.4 and Exercise III.1.2): for a
division ring `D` and at least two indices there is a surjective homomorphism
`GLₙ(D) → Dˣ/[Dˣ, Dˣ]` with kernel the elementary subgroup `Eₙ(D)`, sending the diagonal matrix with
one entry `d` and all others `1` to the class of `d`. -/
theorem dieudonne_determinant (D : Type*) [DivisionRing D] (n : Type*) [Fintype n]
    [DecidableEq n] (hn : 2 ≤ Fintype.card n) :
    ∃ φ : GL n D →* Group.Abelianization Dˣ,
      Function.Surjective φ ∧ φ.ker = elementarySubgroup n D ∧
      ∀ (g : GL n D) (i : n) (d : Dˣ),
        (g : Matrix n n D) = diagonal (Function.update (1 : n → D) i (d : D)) →
          φ g = Group.Abelianization.of d := by
  have : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  refine ⟨dieudonneDet n D, dieudonneDet_surjective, ker_dieudonneDet hn, fun g i d hg ↦ ?_⟩
  obtain rfl : g = diagGL (Pi.mulSingle i d) := Units.ext <| by
    rw [hg, diagGL_coe]
    congr 1
    funext j
    by_cases h : j = i <;> simp [h]
  exact dieudonneDet_diagGL_mulSingle i d

end DieudonneDet

end TauCeti
