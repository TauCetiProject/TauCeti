/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Matrix
public import TauCeti.Algebra.Lie.Unitary.Special
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Projective
import TauCeti.Analysis.Matrix.UnitaryGroup.Torus

/-!
# Metric, orientation and kernel of the adjoint representations of `U(n)`

The unitary group `U(n)` acts on its Lie algebra `𝔲(n)` and on `𝔰𝔲(n)` by conjugation,
`Ad_U X = U X Uᴴ` (`TauCeti.unitaryAdjointRepresentation`,
`TauCeti.specialUnitaryAdjointRepresentation`). This file shows that these are representations by
orientation-preserving isometries of the invariant metric, and computes their kernel. These are
the data that make the bundle `P ×_Ad 𝔰𝔲(r)` associated with a principal bundle `P` with
structure group `PU(r) = U(r) ⧸ U(1)` (which is `PSU(r)`) an oriented Euclidean vector bundle of
rank `r² - 1`.

* **The metric.** `Ad_U` preserves the real trace form `⟪X, Y⟫ = Re tr(X Yᴴ)`
  (`LieSubalgebra.reTraceForm`), which is positive definite and on skew-Hermitian matrices equals
  `-Re tr(X Y)` (`TauCeti.isIsometry_reTraceForm_unitaryAdjointRepresentation`,
  `TauCeti.isIsometry_reTraceForm_specialUnitaryAdjointRepresentation`). Its positive multiples,
  such as `-tr(X Y) / (4π²)`, are invariant as well.
* **The orientation.** `det Ad_U = 1` on `𝔲(n)` and on `𝔰𝔲(n)`
  (`TauCeti.det_unitaryAdjointRepresentation`, `TauCeti.det_specialUnitaryAdjointRepresentation`),
  so by `Orientation.map_eq_iff_det_pos` the adjoint action preserves every orientation. The
  determinant of an isometry is `±1`, and every `U ∈ U(n)` is a square `V²` in `U(n)`
  (`Matrix.UnitaryGroup.isSquare`), so `det Ad_U = (det Ad_V)² ≥ 0`
  (`TauCeti.BilinForm.IsIsometry.det_eq_one_of_isSquare`); this square root replaces the usual
  appeal to the connectedness of `U(n)`. On `𝔰𝔲(n)` this makes `Ad` a homomorphism
  `U(n) →* SO(𝔰𝔲(n))` into the determinant-one isometries of the metric
  (`TauCeti.specialUnitaryAdjointHom`).
* **The kernel.** `Ad_U` is the identity on `𝔰𝔲(n)`, or on `𝔲(n)`, exactly when `U` is a unit
  scalar `c • 1` (`TauCeti.ker_specialUnitaryAdjointRepresentation`,
  `TauCeti.ker_unitaryAdjointRepresentation`), because a matrix commuting with `𝔰𝔲(n)` is scalar
  (`TauCeti.mem_range_scalar_of_forall_mem_specialUnitaryLieAlgebra_commute`). So the rotation
  representation descends to a faithful representation `PU(n) →* SO(𝔰𝔲(n))` of the projective
  unitary group (`TauCeti.projectiveUnitaryAdjointHom`,
  `TauCeti.projectiveUnitaryAdjointHom_injective`).

## Main definitions

* `TauCeti.specialUnitaryAdjointHom`: `Ad : U(n) →* SO(𝔰𝔲(n))`.
* `TauCeti.projectiveUnitaryAdjointHom`: `Ad : PU(n) →* SO(𝔰𝔲(n))`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition,
  Springer GTM 222, 2015, Chapter 3 (the adjoint representation of a matrix Lie group).
-/

public section

open Matrix Module

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The invariant metric -/

/-- **The adjoint action of `U(n)` on `𝔲(n)` is by isometries** of the invariant metric
`⟪X, Y⟫ = Re tr(X Yᴴ) = -Re tr(X Y)`. -/
theorem isIsometry_reTraceForm_unitaryAdjointRepresentation (U : unitaryGroup ι ℂ) :
    BilinForm.IsIsometry (unitaryLieAlgebra ι).reTraceForm (unitaryAdjointRepresentation ι U) :=
  BilinForm.isIsometry_iff.mpr fun X Y ↦ by
    simp only [LieSubalgebra.reTraceForm_apply, coe_unitaryAdjointRepresentation_apply,
      reTraceForm_eq_frobenius_real_inner, star_eq_conjTranspose,
      UnitaryGroup.frobenius_real_inner_conj]

/-- **The adjoint action of `U(n)` on `𝔰𝔲(n)` is by isometries** of the invariant metric
`⟪X, Y⟫ = Re tr(X Yᴴ) = -Re tr(X Y)`. -/
theorem isIsometry_reTraceForm_specialUnitaryAdjointRepresentation (U : unitaryGroup ι ℂ) :
    BilinForm.IsIsometry (specialUnitaryLieAlgebra ι).reTraceForm
      (specialUnitaryAdjointRepresentation ι U) :=
  BilinForm.isIsometry_iff.mpr fun X Y ↦ by
    simp only [LieSubalgebra.reTraceForm_apply, coe_specialUnitaryAdjointRepresentation_apply,
      reTraceForm_eq_frobenius_real_inner, star_eq_conjTranspose,
      UnitaryGroup.frobenius_real_inner_conj]

/-! ### The orientation -/

/-- **The adjoint action of `U(n)` on `𝔲(n)` has determinant `1`**, so it preserves every
orientation of `𝔲(n)` (`Orientation.map_eq_iff_det_pos`). -/
theorem det_unitaryAdjointRepresentation (U : unitaryGroup ι ℂ) :
    LinearMap.det (unitaryAdjointRepresentation ι U) = 1 := by
  obtain ⟨V, rfl⟩ := UnitaryGroup.isSquare U
  exact (isIsometry_reTraceForm_unitaryAdjointRepresentation (V * V)).det_eq_one_of_isSquare
    (LinearMap.BilinForm.separatingLeft_of_anisotropic
      (unitaryLieAlgebra ι).posDef_reTraceForm.anisotropic) ⟨_, map_mul _ V V⟩

/-- **The adjoint action of `U(n)` on `𝔰𝔲(n)` has determinant `1`**, so it preserves every
orientation of `𝔰𝔲(n)` (`Orientation.map_eq_iff_det_pos`). -/
theorem det_specialUnitaryAdjointRepresentation (U : unitaryGroup ι ℂ) :
    LinearMap.det (specialUnitaryAdjointRepresentation ι U) = 1 := by
  obtain ⟨V, rfl⟩ := UnitaryGroup.isSquare U
  exact (isIsometry_reTraceForm_specialUnitaryAdjointRepresentation (V * V)).det_eq_one_of_isSquare
    (LinearMap.BilinForm.separatingLeft_of_anisotropic
      (specialUnitaryLieAlgebra ι).posDef_reTraceForm.anisotropic) ⟨_, map_mul _ V V⟩

variable (ι) in
/-- The **adjoint representation of `U(n)` on `𝔰𝔲(n)` by rotations**: `Ad_U` as an element of the
special orthogonal group `SO(𝔰𝔲(n))` of the invariant metric `⟪X, Y⟫ = Re tr(X Yᴴ)`, the group of
its isometries of determinant `1`. An associated bundle `P ×_Ad 𝔰𝔲(n)` thus carries a metric and an
orientation from those of `𝔰𝔲(n)`. -/
noncomputable def specialUnitaryAdjointHom :
    unitaryGroup ι ℂ →*
      LinearMap.BilinForm.specialIsometryGroup (specialUnitaryLieAlgebra ι).reTraceForm :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ _).toMonoidHom.comp
    (specialUnitaryAdjointRepresentation ι).asGroupHom).codRestrict _ fun U ↦
    LinearMap.BilinForm.mem_specialIsometryGroup_iff.mpr
      ⟨LinearMap.BilinForm.mem_isometryGroup.mpr
        (isIsometry_reTraceForm_specialUnitaryAdjointRepresentation U),
        Units.ext <| (LinearEquiv.coe_det _).trans (det_specialUnitaryAdjointRepresentation U)⟩

/-- The rotation `specialUnitaryAdjointHom ι U` acts as `Ad_U`. -/
@[simp]
theorem specialUnitaryAdjointHom_apply (U : unitaryGroup ι ℂ) (X : specialUnitaryLieAlgebra ι) :
    (specialUnitaryAdjointHom ι U : specialUnitaryLieAlgebra ι ≃ₗ[ℝ] specialUnitaryLieAlgebra ι) X =
      specialUnitaryAdjointRepresentation ι U X :=
  (rfl)

/-! ### The kernel -/

/-- A unitary matrix commuting with every element of `𝔰𝔲(n)` is a unit scalar. -/
private theorem mem_range_scalarHom_of_forall_mul_mul_star_eq_self {U : unitaryGroup ι ℂ}
    (h : ∀ X ∈ specialUnitaryLieAlgebra ι, U * X * star (U : Matrix ι ι ℂ) = X) :
    U ∈ (UnitaryGroup.scalarHom ι ℂ).range := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, Subtype.ext (Subsingleton.elim _ _)⟩
  obtain ⟨c, hc⟩ := mem_range_scalar_of_forall_mem_specialUnitaryLieAlgebra_commute fun X hX ↦
    ((commute_unitary_iff_star_right_conjugate U.property).mpr (h X hX)).symm
  exact UnitaryGroup.mem_range_scalarHom_iff.mpr ⟨c, hc.symm⟩

/-- **The kernel of the adjoint action on `𝔰𝔲(n)`** is the subgroup of unit scalars `c • 1`:
`Ad_U` is the identity of `𝔰𝔲(n)` exactly when `U` is a scalar matrix. -/
theorem ker_specialUnitaryAdjointRepresentation :
    (specialUnitaryAdjointRepresentation ι).ker = (UnitaryGroup.scalarHom ι ℂ).range := by
  ext U
  refine ⟨fun h ↦ mem_range_scalarHom_of_forall_mul_mul_star_eq_self fun X hX ↦ ?_,
    fun h ↦ LinearMap.ext fun X ↦ Subtype.ext ?_⟩
  · simpa using congrArg Subtype.val (LinearMap.congr_fun (MonoidHom.mem_ker.mp h) ⟨X, hX⟩)
  · simpa using UnitaryGroup.mul_mul_star_eq_self_of_mem_range_scalarHom h X

/-- **The kernel of the adjoint action on `𝔲(n)`** is the subgroup of unit scalars `c • 1`. -/
theorem ker_unitaryAdjointRepresentation :
    (unitaryAdjointRepresentation ι).ker = (UnitaryGroup.scalarHom ι ℂ).range := by
  ext U
  refine ⟨fun h ↦ mem_range_scalarHom_of_forall_mul_mul_star_eq_self fun X hX ↦ ?_,
    fun h ↦ LinearMap.ext fun X ↦ Subtype.ext ?_⟩
  · simpa using congrArg Subtype.val
      (LinearMap.congr_fun (MonoidHom.mem_ker.mp h)
        ⟨X, specialUnitaryLieAlgebra_le_unitaryLieAlgebra ι hX⟩)
  · simpa using UnitaryGroup.mul_mul_star_eq_self_of_mem_range_scalarHom h X

/-- The kernel of the rotation representation `U(n) →* SO(𝔰𝔲(n))` is the subgroup of unit
scalars. -/
theorem ker_specialUnitaryAdjointHom :
    (specialUnitaryAdjointHom ι).ker = (UnitaryGroup.scalarHom ι ℂ).range := by
  rw [← ker_specialUnitaryAdjointRepresentation]
  ext U
  simp only [MonoidHom.mem_ker, Subtype.ext_iff, LinearEquiv.ext_iff, LinearMap.ext_iff,
    specialUnitaryAdjointHom_apply, OneMemClass.coe_one, one_apply_eq_self]

/-! ### The projective unitary group -/

variable (ι) in
/-- The **adjoint representation of the projective unitary group** `PU(n) = U(n) ⧸ U(1)` on
`𝔰𝔲(n)`, by rotations: the rotation representation `TauCeti.specialUnitaryAdjointHom` descends to
the quotient by the unit scalars, its kernel. It is faithful
(`TauCeti.projectiveUnitaryAdjointHom_injective`). -/
noncomputable def projectiveUnitaryAdjointHom :
    ProjectiveUnitaryGroup ι ℂ →*
      LinearMap.BilinForm.specialIsometryGroup (specialUnitaryLieAlgebra ι).reTraceForm :=
  QuotientGroup.lift _ (specialUnitaryAdjointHom ι) ker_specialUnitaryAdjointHom.ge

/-- The class of `U` in `PU(n)` acts on `𝔰𝔲(n)` as `Ad_U`. -/
@[simp]
theorem projectiveUnitaryAdjointHom_mk (U : unitaryGroup ι ℂ) :
    projectiveUnitaryAdjointHom ι U = specialUnitaryAdjointHom ι U :=
  (rfl)

/-- **The adjoint action of `PU(n)` on `𝔰𝔲(n)` is faithful.** -/
theorem projectiveUnitaryAdjointHom_injective :
    Function.Injective (projectiveUnitaryAdjointHom ι) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr ker_specialUnitaryAdjointHom.symm

end TauCeti
