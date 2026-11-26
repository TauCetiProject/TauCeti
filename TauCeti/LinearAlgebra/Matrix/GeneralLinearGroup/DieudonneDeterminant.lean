/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Abelianization.WithZero
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stability

-- Non-public: the factorization through the Weyl element is used to prove multiplicativity and the
-- singularity criterion of the `2 × 2` determinant; invertible upper triangular matrices only for
-- the latter; relabelling indices preserves the class in `K₁` (`AlgebraicK1.mk_reindexGL`); the
-- signed Weyl word is elementary, which computes the determinant of a permutation matrix.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary.Permutation
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable.BlockSum
import TauCeti.LinearAlgebra.Matrix.WeylElementFinTwo

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

Every invertible matrix over `D` is an elementary matrix times a diagonal matrix with a single
entry `d` different from `1`. With at least two indices the commutator subgroup of `GLₙ(D)` is
the elementary subgroup, except for `GL₂(𝔽₂)`; when `D` has an element other than `0` and `1`,
the elementary subgroup lies in the commutator subgroup in every size. Hence the Dieudonné
determinant is the **only** homomorphism `GLₙ(D) → Dˣ/[Dˣ, Dˣ]`, for `n ≥ 1`, that sends such a
diagonal matrix to the class of `d`. Through `K₁(D)` the determinant inherits the rules of
computation of classes in `K₁`: it is multiplicative on block diagonal matrices, and an invertible
block matrix `fromBlocks X Y Z W` with invertible `X` has determinant `Δ(X) Δ(W - Z X⁻¹ Y)`, the
Schur complement formula, in this order of the factors. It is natural in ring homomorphisms, it
sends a permutation matrix to the class of the sign, and over a field it is the class of the usual
determinant.

## Main definitions

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
* `TauCeti.elementarySubgroup_le_ker_dieudonneDet`: elementary matrices have determinant one.
* `TauCeti.exists_mem_elementarySubgroup_eq_mul_diagGL_mulSingle`: every invertible matrix is an
  elementary matrix times a diagonal matrix with a single entry different from `1`.
* `TauCeti.hom_ext_of_elementarySubgroup_le_ker`, `TauCeti.eq_dieudonneDet`: uniqueness of the
  Dieudonné determinant.
* `TauCeti.commutator_eq_elementarySubgroup`: the commutator subgroup of `GLₙ(D)` is `Eₙ(D)` for
  `n ≥ 2`, except for `GL₂(𝔽₂)`; `TauCeti.elementarySubgroup_le_commutator_of_ne` gives the
  inclusion `Eₙ(D) ≤ [GLₙ(D), GLₙ(D)]` in every size when `D ≠ 𝔽₂`.
* `TauCeti.dieudonneDet_fromBlocksGL`, `TauCeti.dieudonneDet_eq_mul_of_coe_eq_fromBlocks`: the block
  diagonal and the Schur complement formulas, with the block triangular special cases
  `TauCeti.dieudonneDet_eq_mul_of_coe_eq_fromBlocks_zero₂₁` and
  `TauCeti.dieudonneDet_eq_mul_of_coe_eq_fromBlocks_zero₁₂`.
* `TauCeti.dieudonneDet_permutationGL`: a permutation matrix has the class of its sign.
* `TauCeti.dieudonneDet_unitsMap_mapMatrix`, `TauCeti.AlgebraicK1.divisionRingEquiv_map`:
  naturality in ring homomorphisms of division rings.
* `TauCeti.dieudonneDet_eq_of_det`, `TauCeti.AlgebraicK1.divisionRingEquiv_eq_of_det`: over a field
  the Dieudonné determinant is the class of the usual determinant.

## Implementation notes

Multiplicativity of the `2 × 2` formula is checked on left multiplication by upper triangular
matrices and by the Weyl element `!![0, -1; 1, 0]`; this suffices because every matrix whose
lower left entry is nonzero is a product of an upper triangular matrix, the Weyl element and a
unipotent upper triangular matrix.

## References

* J. Dieudonné, *Les déterminants sur un corps non commutatif*, Bull. Soc. Math. France 71
  (1943), 27–45.
* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter IV, §1, where the determinant is
  characterized by its behaviour under elementary row operations and on diagonal matrices.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, 1.2.4, Example 1.3.5 and Exercise 1.2.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

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

/-- The formula is unchanged by left multiplication by the Weyl element `!![0, -1; 1, 0]`. -/
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

private theorem detTwo_mul (N M : Matrix (Fin 2) (Fin 2) D) :
    detTwo (N * M) = detTwo N * detTwo M := by
  by_cases hc : N 1 0 = 0
  · rw [Matrix.eta_fin_two N, hc]
    exact detTwo_upper_mul _ _ _ M
  have h : ∀ M, detTwo (N * M) = detTwo !![N 0 0 * (N 1 0)⁻¹ * N 1 1 - N 0 1, N 0 0; 0, N 1 0] *
      detTwo !![1, (N 1 0)⁻¹ * N 1 1; 0, 1] * detTwo M := by
    intro M
    conv_lhs => rw [eq_upper_mul_weylElement_mul_upper_fin_two N hc]
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

/-- The Dieudonné determinant of a `2 × 2` matrix vanishes exactly when the matrix is not
invertible. -/
theorem dieudonneDetFinTwo_eq_zero_iff {M : Matrix (Fin 2) (Fin 2) D} :
    dieudonneDetFinTwo D M = 0 ↔ ¬IsUnit M := by
  refine ⟨fun h ⟨u, hu⟩ ↦ ?_, fun h ↦ by_contra fun h0 ↦ h ?_⟩
  · have := congrArg (dieudonneDetFinTwo D) u.mul_inv
    rw [map_mul, hu, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hB (a d : Dˣ) (b : D) : IsUnit !![(a : D), b; 0, d] :=
    GL2Borel.coe_mk a d b ▸ (GL2Borel.mk a d b).isUnit
  by_cases hc : M 1 0 = 0
  · rw [dieudonneDetFinTwo_apply_of_eq_zero hc, map_eq_zero] at h0
    rw [Matrix.eta_fin_two M, hc]
    exact hB (.mk0 _ (left_ne_zero_of_mul h0)) (.mk0 _ (right_ne_zero_of_mul h0)) _
  rw [dieudonneDetFinTwo_apply_of_ne_zero hc, map_eq_zero] at h0
  rw [eq_upper_mul_weylElement_mul_upper_fin_two M hc]
  exact ((hB (.mk0 _ (right_ne_zero_of_mul h0)) (.mk0 _ hc) _).mul
    (isUnit_weylElement_fin_two D)).mul (hB 1 1 _)

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
  rw [MonoidHom.mem_ker, ← WithZero.coe_inj]
  simp [coe_dieudonneDetGLFinTwo, coe_transvectionUnit_eq_one_add_single hij,
    dieudonneDetFinTwo_one_add_single hij]

/-- The homomorphism `K₁(D) →* Dˣ/[Dˣ, Dˣ]` induced by the `2 × 2` Dieudonné determinant, through
the identification of `K₁(D)` with a quotient of `GL₂(D)`. -/
private def toAbelianization : AlgebraicK1 D →* Group.Abelianization Dˣ :=
  (QuotientGroup.lift _ dieudonneDetGLFinTwo ker_mk_two_le).comp
    (quotientKerMkEquiv (hasStableRangeLE_one_of_isLocalRing D)
      (by norm_num : 1 ≤ 2)).symm.toMonoidHom

private theorem toAbelianization_mk_two (g : GL (Fin 2) D) :
    toAbelianization (mk D 2 g) = dieudonneDetGLFinTwo g := by
  rw [← quotientKerMkEquiv_mk (hasStableRangeLE_one_of_isLocalRing D) (by norm_num : 1 ≤ 2) g]
  simp [toAbelianization, -quotientKerMkEquiv_mk]

private theorem toAbelianization_ofUnits (d : Dˣ) :
    toAbelianization (ofUnits D d) = Group.Abelianization.of d := by
  rw [ofUnits_apply, ← mk_stabilizeGL (by norm_num : 1 ≤ 2), toAbelianization_mk_two,
    ← WithZero.coe_inj]
  simp [coe_dieudonneDetGLFinTwo, dieudonneDetFinTwo_apply_of_eq_zero, coe_stabilizeGL_apply]

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
  -- `Dˣ` need not be commutative, so decompose `t` with a noncommutative product
  have h := Finset.univ.map_noncommProd (fun i ↦ Pi.mulSingle i (t i))
    (fun i _ j _ _ ↦ Pi.mulSingle_apply_commute t i j) ((dieudonneDet n D).comp diagGL)
  rw [Finset.noncommProd_mulSingle, Finset.noncommProd_eq_prod] at h
  simpa using h

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

/-! ## Elementary invariance, uniqueness and the class in `K₁` -/

section Uniqueness

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] {D : Type*}
  [DivisionRing D]

/-- Elementary matrices lie in the kernel of the Dieudonné determinant. -/
theorem elementarySubgroup_le_ker_dieudonneDet :
    elementarySubgroup n D ≤ (dieudonneDet n D).ker :=
  elementarySubgroup_le_iff.2 fun _ _ hij a ↦ dieudonneDet_transvectionUnit hij a

/-- Over a division ring, every invertible matrix is an elementary matrix times the diagonal
matrix with a chosen diagonal entry `d` and all others `1`. -/
theorem exists_mem_elementarySubgroup_eq_mul_diagGL_mulSingle (i : n) (g : GL n D) :
    ∃ e ∈ elementarySubgroup n D, ∃ d : Dˣ, g = e * diagGL (Pi.mulSingle i d) := by
  rcases le_or_gt 2 (Fintype.card n) with hn | hn
  · -- with two indices, divide by a diagonal matrix of the same determinant
    obtain ⟨d, hd⟩ := Group.Abelianization.surjective_of _ (dieudonneDet n D g)
    refine ⟨g * (diagGL (Pi.mulSingle i d))⁻¹, ?_, d, by rw [inv_mul_cancel_right]⟩
    rw [← ker_dieudonneDet hn, MonoidHom.mem_ker, map_mul, map_inv, dieudonneDet_diagGL_mulSingle,
      hd, mul_inv_cancel]
  · -- with a single index, `g` is the diagonal matrix of its only entry
    have : Subsingleton n := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    have hmul (M N : Matrix n n D) : (M * N) i i = M i i * N i i := by
      rw [Matrix.mul_apply, Fintype.sum_subsingleton _ i]
    refine ⟨1, one_mem _, ⟨(g : Matrix n n D) i i, (↑g⁻¹ : Matrix n n D) i i, ?_, ?_⟩, ?_⟩
    · rw [← hmul, Units.mul_inv, Matrix.one_apply_eq]
    · rw [← hmul, Units.inv_mul, Matrix.one_apply_eq]
    ext a b
    rw [Subsingleton.elim a i, Subsingleton.elim b i]
    simp

/-- Two homomorphisms out of `GL n D` that are trivial on elementary matrices are equal as soon as
they agree on the diagonal matrices with a chosen diagonal entry `d` and all others `1`. -/
theorem hom_ext_of_elementarySubgroup_le_ker {G : Type*} [MulOneClass G] {φ ψ : GL n D →* G} (i : n)
    (hφ : elementarySubgroup n D ≤ φ.ker) (hψ : elementarySubgroup n D ≤ ψ.ker)
    (h : ∀ d : Dˣ, φ (diagGL (Pi.mulSingle i d)) = ψ (diagGL (Pi.mulSingle i d))) : φ = ψ := by
  ext1 g
  obtain ⟨e, he, d, rfl⟩ := exists_mem_elementarySubgroup_eq_mul_diagGL_mulSingle i g
  rw [map_mul, map_mul, MonoidHom.mem_ker.1 (hφ he), MonoidHom.mem_ker.1 (hψ he), h]

/-- Over a division ring with an element other than `0` and `1`, the elementary subgroup lies in
the commutator subgroup of `GL n D`, in every size. -/
theorem elementarySubgroup_le_commutator_of_ne {a : D} (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) :
    elementarySubgroup n D ≤ commutator (GL n D) :=
  elementarySubgroup_le_commutator_of_isUnit_sub_one (Units.mk0 a ha₀)
    (isUnit_iff_ne_zero.2 (sub_ne_zero.2 ha₁))

/-- **The commutator subgroup of `GLₙ(D)`** is the elementary subgroup, as soon as there are at
least two indices, except for `2 × 2` matrices over `𝔽₂`: the group `GL₂(𝔽₂) = E₂(𝔽₂)` is the
symmetric group on three letters, whose commutator subgroup has index two. The hypothesis `hD`
excludes this case. -/
theorem commutator_eq_elementarySubgroup (hn : 2 ≤ Fintype.card n)
    (hD : 3 ≤ Fintype.card n ∨ ∃ a : D, a ≠ 0 ∧ a ≠ 1) :
    commutator (GL n D) = elementarySubgroup n D := by
  refine le_antisymm ((Group.Abelianization.commutator_le_ker (dieudonneDet n D)).trans
    (ker_dieudonneDet hn).le) ?_
  rcases hD with h₃ | ⟨a, ha₀, ha₁⟩
  · exact elementarySubgroup_le_commutator h₃
  · exact elementarySubgroup_le_commutator_of_ne ha₀ ha₁

/-- **Uniqueness of the Dieudonné determinant**: a homomorphism `GL n D →* Dˣ/[Dˣ, Dˣ]` that sends
the diagonal matrix with a chosen diagonal entry `d` and all others `1` to the class of `d` is the
Dieudonné determinant. It is automatically trivial on elementary matrices, since its target is
commutative. -/
theorem eq_dieudonneDet {φ : GL n D →* Group.Abelianization Dˣ} (i : n)
    (h : ∀ d : Dˣ, φ (diagGL (Pi.mulSingle i d)) = Group.Abelianization.of d) :
    φ = dieudonneDet n D := by
  refine hom_ext_of_elementarySubgroup_le_ker i ?_ elementarySubgroup_le_ker_dieudonneDet
    fun d ↦ by rw [h, dieudonneDet_diagGL_mulSingle]
  by_cases hD : ∃ a : D, a ≠ 0 ∧ a ≠ 1
  · obtain ⟨a, ha₀, ha₁⟩ := hD
    exact (elementarySubgroup_le_commutator_of_ne ha₀ ha₁).trans
      (Group.Abelianization.commutator_le_ker φ)
  · -- every unit of `D` is `1`, so the target of `φ` is trivial
    push Not at hD
    intro g _
    obtain ⟨d, hd⟩ := Group.Abelianization.surjective_of _ (φ g)
    rw [MonoidHom.mem_ker, ← hd, Units.val_eq_one.1 (hD _ d.ne_zero), map_one]

/-- The isomorphism `K₁(D) ≃* Dˣ/[Dˣ, Dˣ]` sends the class of an invertible matrix to its
Dieudonné determinant. -/
@[simp]
theorem AlgebraicK1.divisionRingEquiv_mkOfFintype (g : GL n D) :
    AlgebraicK1.divisionRingEquiv D (AlgebraicK1.mkOfFintype D n g) = dieudonneDet n D g := by
  rw [AlgebraicK1.mkOfFintype_apply, dieudonneDet, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom]

/-! ## Block matrices -/

/-- The Dieudonné determinant of a block diagonal matrix is the product of the Dieudonné
determinants of its blocks. -/
@[simp]
theorem dieudonneDet_fromBlocksGL (u : GL m D) (v : GL n D) :
    dieudonneDet (m ⊕ n) D (fromBlocksGL (u, v)) = dieudonneDet m D u * dieudonneDet n D v := by
  rw [← AlgebraicK1.divisionRingEquiv_mkOfFintype, AlgebraicK1.mkOfFintype_fromBlocksGL, map_mul,
    AlgebraicK1.divisionRingEquiv_mkOfFintype, AlgebraicK1.divisionRingEquiv_mkOfFintype]

/-- **The Schur complement formula** for the Dieudonné determinant: if the upper-left block `u` of
an invertible block matrix `fromBlocks u Y Z W` is invertible, its Dieudonné determinant is
`Δ(u) Δ(W - Z u⁻¹ Y)`, the Schur complement being invertible by
`Matrix.GeneralLinearGroup.isUnit_sub_mul_mul_of_coe_eq_fromBlocks`. The order of the factors in
the Schur complement matters, since `D` need not be commutative. -/
theorem dieudonneDet_eq_mul_of_coe_eq_fromBlocks {g : GL (m ⊕ n) D} {u : GL m D} {v : GL n D}
    {Y : Matrix m n D} {Z : Matrix n m D} {W : Matrix n n D}
    (hg : (g : Matrix (m ⊕ n) (m ⊕ n) D) = fromBlocks u Y Z W)
    (hv : (v : Matrix n n D) = W - Z * (↑u⁻¹ : Matrix m m D) * Y) :
    dieudonneDet (m ⊕ n) D g = dieudonneDet m D u * dieudonneDet n D v := by
  rw [← AlgebraicK1.divisionRingEquiv_mkOfFintype,
    AlgebraicK1.mkOfFintype_eq_mul_of_coe_eq_fromBlocks hg hv, map_mul,
    AlgebraicK1.divisionRingEquiv_mkOfFintype, AlgebraicK1.divisionRingEquiv_mkOfFintype]

/-- The Dieudonné determinant of a block upper triangular matrix with invertible diagonal blocks
`u` and `v` is `Δ(u) Δ(v)`, whatever its off-diagonal block. -/
theorem dieudonneDet_eq_mul_of_coe_eq_fromBlocks_zero₂₁ {g : GL (m ⊕ n) D} {u : GL m D}
    {v : GL n D} {X : Matrix m n D} (hg : (g : Matrix (m ⊕ n) (m ⊕ n) D) = fromBlocks u X 0 v) :
    dieudonneDet (m ⊕ n) D g = dieudonneDet m D u * dieudonneDet n D v :=
  dieudonneDet_eq_mul_of_coe_eq_fromBlocks hg (by simp)

/-- The Dieudonné determinant of a block lower triangular matrix with invertible diagonal blocks
`u` and `v` is `Δ(u) Δ(v)`, whatever its off-diagonal block. -/
theorem dieudonneDet_eq_mul_of_coe_eq_fromBlocks_zero₁₂ {g : GL (m ⊕ n) D} {u : GL m D}
    {v : GL n D} {Y : Matrix n m D} (hg : (g : Matrix (m ⊕ n) (m ⊕ n) D) = fromBlocks u 0 Y v) :
    dieudonneDet (m ⊕ n) D g = dieudonneDet m D u * dieudonneDet n D v :=
  dieudonneDet_eq_mul_of_coe_eq_fromBlocks hg (by simp)

/-! ## Permutation matrices -/

/-- The Dieudonné determinant of a permutation matrix is the class of the sign of the
permutation. -/
@[simp]
theorem dieudonneDet_permutationGL (σ : Equiv.Perm n) :
    dieudonneDet n D (permutationGL σ) =
      Group.Abelianization.of (Units.map (Int.castRingHom D : ℤ →* D) (Equiv.Perm.sign σ)) := by
  -- both sides are homomorphisms on `Equiv.Perm n`, so it suffices to compare them on swaps
  suffices h : (dieudonneDet n D).comp permutationGL = Group.Abelianization.of.comp
      ((Units.map (Int.castRingHom D : ℤ →* D)).comp Equiv.Perm.sign) from
    DFunLike.congr_fun h σ
  refine MonoidHom.eq_of_eqOn_denseM Equiv.Perm.mclosure_isSwap ?_
  rintro _ ⟨i, j, hij, rfl⟩
  -- the signed Weyl word `diag(1, …, -1, …, 1) · (i j)` is elementary
  have hW := elementarySubgroup_le_ker_dieudonneDet
    (transvectionWeylElement_mem_elementarySubgroup (A := D) hij)
  rw [MonoidHom.mem_ker, transvectionWeylElement_eq_diagGL_mul_permutationGL, map_mul,
    dieudonneDet_diagGL_mulSingle] at hW
  simp [Equiv.Perm.sign_swap hij, eq_inv_of_mul_eq_one_right hW, ← map_inv]

end Uniqueness

/-! ## Naturality and commutative division rings -/

namespace AlgebraicK1

/-- The isomorphism `K₁(D) ≃* Dˣ/[Dˣ, Dˣ]` is natural in ring homomorphisms of division rings. -/
@[simp]
theorem divisionRingEquiv_map {D D' : Type*} [DivisionRing D] [DivisionRing D'] (f : D →+* D')
    (x : AlgebraicK1 D) :
    divisionRingEquiv D' (map f x) =
      Group.Abelianization.map (Units.map (f : D →* D')) (divisionRingEquiv D x) := by
  obtain ⟨u, rfl⟩ := ofUnits_surjective (hasStableRangeLE_one_of_isLocalRing D) x
  simp [Group.Abelianization.map_of]

/-- Over a field `F`, the isomorphism `K₁(F) ≃* Fˣ/[Fˣ, Fˣ]` is the determinant
`K₁(F) →* Fˣ` followed by the class map, the abelianization of the commutative group `Fˣ` being
`Fˣ` itself. -/
theorem divisionRingEquiv_eq_of_det {F : Type*} [Field F] (x : AlgebraicK1 F) :
    divisionRingEquiv F x = Group.Abelianization.of (det F x) := by
  obtain ⟨u, rfl⟩ := ofUnits_surjective (hasStableRangeLE_one_of_isLocalRing F) x
  simp

end AlgebraicK1

section Naturality

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Dieudonné determinant is natural in ring homomorphisms of division rings: applying `f` to
the entries of an invertible matrix applies `f` to the classes of the units. -/
@[simp]
theorem dieudonneDet_unitsMap_mapMatrix {D D' : Type*} [DivisionRing D] [DivisionRing D']
    (f : D →+* D') (g : GL n D) :
    dieudonneDet n D' (Units.map (f.mapMatrix (m := n) : Matrix n n D →* Matrix n n D') g) =
      Group.Abelianization.map (Units.map (f : D →* D')) (dieudonneDet n D g) := by
  rw [← AlgebraicK1.divisionRingEquiv_mkOfFintype, ← RingHom.toMonoidHom_eq_coe,
    ← AlgebraicK1.map_mkOfFintype,
    AlgebraicK1.divisionRingEquiv_map, AlgebraicK1.divisionRingEquiv_mkOfFintype]

/-- Over a field the Dieudonné determinant is the class of the usual determinant. -/
theorem dieudonneDet_eq_of_det {F : Type*} [Field F] (g : GL n F) :
    dieudonneDet n F g = Group.Abelianization.of (GeneralLinearGroup.det g) := by
  rw [← AlgebraicK1.divisionRingEquiv_mkOfFintype, AlgebraicK1.divisionRingEquiv_eq_of_det,
    AlgebraicK1.det_mkOfFintype]

end Naturality

end TauCeti
