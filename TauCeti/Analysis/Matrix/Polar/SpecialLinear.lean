/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary

/-!
# `SL(n, 𝕜)` and `PSL(n, 𝕜)` deformation retract onto `SU(n)` and `PSU(n)`

Over `𝕜 = ℝ` or `ℂ`, the polar deformation `A ↦ P ^ (1 - t) * U` of an invertible matrix
`A = P * U` (`Matrix.GeneralLinearGroup.polarDeformation`) preserves determinant one, and the
unitary factor of a matrix of determinant one again has determinant one. So the polar deformation
restricts to a strong deformation retraction of `SL(n, 𝕜)` onto `SU(n)` (`SO(n)` when `𝕜 = ℝ`)
(`Matrix.SpecialLinearGroup.polarHomotopy`), ending at the polar unitary factor
(`Matrix.SpecialLinearGroup.polarRetraction`), and the inclusion `SU(n) → SL(n, 𝕜)` is a homotopy
equivalence (`Matrix.SpecialLinearGroup.polarHomotopyEquiv`).

The polar deformation commutes with left multiplication by unitary matrices, and every central
element of `SL(n, 𝕜)` is a unitary scalar matrix. So the deformation descends to the projective
special linear group `PSL(n, 𝕜) = SL(n, 𝕜) ⧸ Z`, with its quotient topology: it is a strong
deformation retraction of `PSL(n, 𝕜)` onto the projective special unitary group `PSU(n)`, the image
of `SU(n)` (`Matrix.ProjectiveSpecialLinearGroup.polarHomotopy`), and the inclusion
`PSU(n) → PSL(n, 𝕜)` is a homotopy equivalence
(`Matrix.ProjectiveSpecialLinearGroup.polarHomotopyEquiv`). Continuity of the descended deformation
holds because `SL(n, 𝕜) → PSL(n, 𝕜)` is an open quotient map, so that its product with the unit
interval is again a quotient map.

For `n = 2` and `𝕜 = ℂ` this deforms the Möbius group of the Riemann sphere onto its rotation group
`PSU(2)`.

## Main definitions

* `Matrix.SpecialLinearGroup.polarRetraction`: the retraction `SL(n, 𝕜) → SU(n)` onto the polar
  unitary factor.
* `Matrix.SpecialLinearGroup.polarHomotopy`: the strong deformation retraction of `SL(n, 𝕜)` onto
  `SU(n)`, as a homotopy relative to `SU(n)` from the identity to the retraction.
* `Matrix.SpecialLinearGroup.polarHomotopyEquiv`: the homotopy equivalence `SU(n) ≃ₕ SL(n, 𝕜)`.
* `Matrix.ProjectiveSpecialLinearGroup.polarRetraction`,
  `Matrix.ProjectiveSpecialLinearGroup.polarHomotopy`,
  `Matrix.ProjectiveSpecialLinearGroup.polarHomotopyEquiv`: the same for `PSL(n, 𝕜)` and `PSU(n)`.

## Main results

* `Matrix.SpecialLinearGroup.polarRetraction_toSL_mul`,
  `Matrix.SpecialLinearGroup.polarHomotopy_toSL_mul`: the retraction and the deformation of
  `SL(n, 𝕜)` commute with left multiplication by `SU(n)`.
* `Matrix.ProjectiveSpecialLinearGroup.polarHomotopy_mk`: the deformation of `PSL(n, 𝕜)` is induced
  by that of `SL(n, 𝕜)`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter VI, Section 1.
-/

public section

noncomputable section

open scoped unitInterval ContinuousMap MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix.SpecialLinearGroup

open Matrix.specialUnitaryGroup GeneralLinearGroup

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

attribute [local instance] Matrix.l2OpNormedAlgebraReal

variable (n 𝕜) in
/-- **The polar retraction** `SL(n, 𝕜) → SU(n)`, for `𝕜 = ℝ` or `ℂ`: the unitary factor `U` of the
polar decomposition `g = P * U`, which has determinant one. -/
def polarRetraction : C(SpecialLinearGroup n 𝕜, specialUnitaryGroup n 𝕜) where
  toFun g := ⟨(toGL g).polarUnitary, mem_specialUnitaryGroup_iff.mpr
    ⟨((toGL g).polarUnitary).2, det_polarUnitary_of_det_eq_one _ (coe_GL_coe_matrix g ▸ g.2)⟩⟩
  continuous_toFun :=
    ((contMDiff_coe_polarUnitary (n := n) (𝕜 := 𝕜) (k := 0)).continuous.comp
      continuous_toGL).subtype_mk _

/-- The polar retraction of `g` is the polar unitary factor of `g`. -/
@[simp]
theorem coe_polarRetraction_apply (g : SpecialLinearGroup n 𝕜) :
    (polarRetraction n 𝕜 g : Matrix n n 𝕜) = (toGL g).polarUnitary :=
  (rfl)

/-- The polar retraction fixes the special unitary matrices. -/
@[simp]
theorem polarRetraction_toSL (k : specialUnitaryGroup n 𝕜) :
    polarRetraction n 𝕜 (toSL k) = k := by
  ext : 1
  rw [coe_polarRetraction_apply, toGL_toSL, Units.polarUnitary_toUnits, Submonoid.coe_inclusion]

/-- The polar retraction commutes with left multiplication by `SU(n)`. -/
@[simp]
theorem polarRetraction_toSL_mul (k : specialUnitaryGroup n 𝕜) (g : SpecialLinearGroup n 𝕜) :
    polarRetraction n 𝕜 (toSL k * g) = k * polarRetraction n 𝕜 g := by
  ext : 1
  have h := Units.polarUnitary_unitary_mul_mul_unitary (toGL g)
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup k) 1
  rw [map_one, mul_one, mul_one, ← toGL_toSL, ← map_mul] at h
  rw [coe_polarRetraction_apply, h, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_inclusion,
    coe_polarRetraction_apply]

variable (n 𝕜) in
/-- **`SL(n, 𝕜)` deformation retracts onto `SU(n)`**, for `𝕜 = ℝ` or `ℂ`. The polar deformation
`P * U ↦ P ^ (1 - t) * U` runs from the identity to the polar retraction followed by the inclusion
`SU(n) → SL(n, 𝕜)`, and fixes `SU(n)` throughout. -/
def polarHomotopy :
    (ContinuousMap.id (SpecialLinearGroup n 𝕜)).HomotopyRel
      ((⟨toSL, continuous_toSL⟩ : C(specialUnitaryGroup n 𝕜, SpecialLinearGroup n 𝕜)).comp
        (polarRetraction n 𝕜))
      (Set.range toSL) where
  toFun p := ⟨polarDeformation (toGL p.2) p.1,
    det_polarDeformation_of_det_eq_one (coe_GL_coe_matrix p.2 ▸ p.2.2) _⟩
  continuous_toFun := by
    have h := (GeneralLinearGroup.polarHomotopy n 𝕜).continuous.comp
      (continuous_fst.prodMk (continuous_toGL.comp continuous_snd) :
        Continuous fun p : I × SpecialLinearGroup n 𝕜 ↦ (p.1, toGL p.2))
    simp only [Function.comp_def, polarHomotopy_apply] at h
    exact (Units.continuous_val.comp h).subtype_mk _
  map_zero_left g := Subtype.ext (by simp)
  map_one_left g := Subtype.ext (by simp)
  prop' t := by
    rintro _ ⟨k, rfl⟩
    have h : polarDeformation (toGL (toSL k)) t = toGL (toSL k) := by
      rw [toGL_toSL, polarDeformation_toUnits]
    exact Subtype.ext ((congrArg Units.val h).trans (coe_GL_coe_matrix _))

/-- The polar homotopy of `SL(n, 𝕜)` is the polar deformation of `GL(n, 𝕜)`. -/
@[simp]
theorem toGL_polarHomotopy_apply (t : I) (g : SpecialLinearGroup n 𝕜) :
    toGL (polarHomotopy n 𝕜 (t, g)) = polarDeformation (toGL g) t :=
  Units.ext (rfl)

/-- The polar homotopy commutes with left multiplication by `SU(n)`. -/
theorem polarHomotopy_toSL_mul (t : I) (k : specialUnitaryGroup n 𝕜)
    (g : SpecialLinearGroup n 𝕜) :
    polarHomotopy n 𝕜 (t, toSL k * g) = toSL k * polarHomotopy n 𝕜 (t, g) := by
  apply toGL_injective
  have h := polarDeformation_unitary_mul_mul_unitary t (toGL g)
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup k) 1
  rw [map_one, mul_one, mul_one, ← toGL_toSL] at h
  rw [map_mul, toGL_polarHomotopy_apply, toGL_polarHomotopy_apply, map_mul, h]

variable (n 𝕜) in
/-- **`SU(n)` is homotopy equivalent to `SL(n, 𝕜)`**, for `𝕜 = ℝ` or `ℂ`, through the inclusion,
with homotopy inverse the polar retraction. -/
def polarHomotopyEquiv : specialUnitaryGroup n 𝕜 ≃ₕ SpecialLinearGroup n 𝕜 where
  toFun := ⟨toSL, continuous_toSL⟩
  invFun := polarRetraction n 𝕜
  left_inv := by
    rw [show (polarRetraction n 𝕜).comp ⟨toSL, continuous_toSL⟩ = ContinuousMap.id _ from
      ContinuousMap.ext polarRetraction_toSL]
  right_inv := ⟨(polarHomotopy n 𝕜).toHomotopy.symm⟩

@[simp]
theorem polarHomotopyEquiv_apply (k : specialUnitaryGroup n 𝕜) :
    polarHomotopyEquiv n 𝕜 k = toSL k :=
  (rfl)

@[simp]
theorem polarHomotopyEquiv_symm_apply (g : SpecialLinearGroup n 𝕜) :
    (polarHomotopyEquiv n 𝕜).symm g = polarRetraction n 𝕜 g :=
  (rfl)

end Matrix.SpecialLinearGroup

namespace Matrix.ProjectiveSpecialLinearGroup

open Matrix.specialUnitaryGroup

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Two matrices of `SL(n, 𝕜)` with the same class in `PSL(n, 𝕜)` differ by left multiplication
by a special unitary matrix which is central in `SL(n, 𝕜)`. -/
private theorem exists_toSL_mul_eq {g g' : SpecialLinearGroup n 𝕜}
    (h : (g : ProjectiveSpecialLinearGroup n 𝕜) = g') :
    ∃ k : specialUnitaryGroup n 𝕜, toSL k ∈ Subgroup.center (SpecialLinearGroup n 𝕜) ∧
      g' = toSL k * g := by
  have hc := QuotientGroup.eq.mp h
  obtain ⟨k, hk⟩ := center_le_range_toSL hc
  refine ⟨k, hk ▸ hc, ?_⟩
  rw [hk, ← Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_left]

variable (n 𝕜) in
/-- **The polar retraction** `PSL(n, 𝕜) → PSU(n)`, for `𝕜 = ℝ` or `ℂ`, induced by the polar
retraction `SL(n, 𝕜) → SU(n)`: the class of `g` goes to the class of its polar unitary factor. -/
def polarRetraction :
    C(ProjectiveSpecialLinearGroup n 𝕜, (toPSL : specialUnitaryGroup n 𝕜 →* _).range) where
  toFun := Quotient.lift (fun g => toPSL.rangeRestrict (SpecialLinearGroup.polarRetraction n 𝕜 g))
    fun g g' h => by
      obtain ⟨k, hk, rfl⟩ := exists_toSL_mul_eq (Quotient.sound h)
      have hk' : toPSL.rangeRestrict k = 1 := Subtype.ext <| by
        rw [MonoidHom.coe_rangeRestrict, OneMemClass.coe_one, ← MonoidHom.mem_ker, ker_toPSL]
        exact hk
      rw [SpecialLinearGroup.polarRetraction_toSL_mul, map_mul, hk', one_mul]
  continuous_toFun := Continuous.quotient_lift
    ((continuous_toPSL.comp (SpecialLinearGroup.polarRetraction n 𝕜).continuous).subtype_mk _) _

/-- The polar retraction sends the class of `g` to the class of its polar unitary factor. -/
@[simp]
theorem polarRetraction_mk (g : SpecialLinearGroup n 𝕜) :
    polarRetraction n 𝕜 (g : ProjectiveSpecialLinearGroup n 𝕜) =
      toPSL.rangeRestrict (SpecialLinearGroup.polarRetraction n 𝕜 g) :=
  (rfl)

/-- The polar retraction fixes `PSU(n)`. -/
theorem polarRetraction_toPSL (k : specialUnitaryGroup n 𝕜) :
    polarRetraction n 𝕜 (toPSL k) = toPSL.rangeRestrict k := by
  rw [toPSL_apply, polarRetraction_mk, SpecialLinearGroup.polarRetraction_toSL]

/-- The deformation of `PSL(n, 𝕜)` induced by the polar homotopy of `SL(n, 𝕜)`; it is well
defined because the latter commutes with the center, which consists of unitary scalars. -/
private def polarHomotopyAux :
    C(I × ProjectiveSpecialLinearGroup n 𝕜, ProjectiveSpecialLinearGroup n 𝕜) where
  toFun p := Quotient.lift
    (fun g => ((SpecialLinearGroup.polarHomotopy n 𝕜 (p.1, g) : SpecialLinearGroup n 𝕜) :
      ProjectiveSpecialLinearGroup n 𝕜))
    (fun g g' h => by
      obtain ⟨k, hk, rfl⟩ := exists_toSL_mul_eq (Quotient.sound h)
      rw [SpecialLinearGroup.polarHomotopy_toSL_mul, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff _).mpr hk, one_mul])
    p.2
  -- `I × SL(n, 𝕜) → I × PSL(n, 𝕜)` is an open quotient map, and composed with it this map is the
  -- class of the polar homotopy of `SL(n, 𝕜)`.
  continuous_toFun :=
    (IsOpenQuotientMap.id.prodMap QuotientGroup.isOpenQuotientMap_mk).continuous_comp_iff.mp
      (QuotientGroup.continuous_mk.comp (SpecialLinearGroup.polarHomotopy n 𝕜).continuous)

private theorem polarHomotopyAux_mk (t : I) (g : SpecialLinearGroup n 𝕜) :
    polarHomotopyAux (t, (g : ProjectiveSpecialLinearGroup n 𝕜)) =
      (SpecialLinearGroup.polarHomotopy n 𝕜 (t, g) : SpecialLinearGroup n 𝕜) :=
  (rfl)

variable (n 𝕜) in
/-- **`PSL(n, 𝕜)` deformation retracts onto `PSU(n)`**, for `𝕜 = ℝ` or `ℂ`: the homotopy
induced by the polar homotopy of `SL(n, 𝕜)` runs from the identity to the polar retraction
followed by the inclusion `PSU(n) → PSL(n, 𝕜)`, and fixes `PSU(n)` throughout. -/
def polarHomotopy :
    (ContinuousMap.id (ProjectiveSpecialLinearGroup n 𝕜)).HomotopyRel
      ((⟨Subtype.val, continuous_subtype_val⟩ :
        C((toPSL : specialUnitaryGroup n 𝕜 →* _).range, ProjectiveSpecialLinearGroup n 𝕜)).comp
          (polarRetraction n 𝕜))
      ((toPSL : specialUnitaryGroup n 𝕜 →* ProjectiveSpecialLinearGroup n 𝕜).range) where
  toFun := polarHomotopyAux
  continuous_toFun := polarHomotopyAux.continuous
  map_zero_left x := by
    induction x using QuotientGroup.induction_on with | H g => _
    rw [polarHomotopyAux_mk, (SpecialLinearGroup.polarHomotopy n 𝕜).apply_zero,
      ContinuousMap.id_apply, ContinuousMap.id_apply]
  map_one_left x := by
    induction x using QuotientGroup.induction_on with | H g => _
    rw [polarHomotopyAux_mk, (SpecialLinearGroup.polarHomotopy n 𝕜).apply_one]
    simp
  prop' t := by
    rintro _ ⟨k, rfl⟩
    simp only [ContinuousMap.coe_mk, ContinuousMap.id_apply, toPSL_apply]
    rw [polarHomotopyAux_mk,
      (SpecialLinearGroup.polarHomotopy n 𝕜).eq_fst t (Set.mem_range_self k),
      ContinuousMap.id_apply]

/-- The polar homotopy of `PSL(n, 𝕜)` is induced by that of `SL(n, 𝕜)`. -/
@[simp]
theorem polarHomotopy_mk (t : I) (g : SpecialLinearGroup n 𝕜) :
    polarHomotopy n 𝕜 (t, (g : ProjectiveSpecialLinearGroup n 𝕜)) =
      (SpecialLinearGroup.polarHomotopy n 𝕜 (t, g) : SpecialLinearGroup n 𝕜) :=
  polarHomotopyAux_mk t g

variable (n 𝕜) in
/-- **`PSU(n)` is homotopy equivalent to `PSL(n, 𝕜)`**, for `𝕜 = ℝ` or `ℂ`, through the
inclusion, with homotopy inverse the polar retraction. -/
def polarHomotopyEquiv :
    (toPSL : specialUnitaryGroup n 𝕜 →* ProjectiveSpecialLinearGroup n 𝕜).range ≃ₕ
      ProjectiveSpecialLinearGroup n 𝕜 where
  toFun := ⟨Subtype.val, continuous_subtype_val⟩
  invFun := polarRetraction n 𝕜
  left_inv := by
    rw [show (polarRetraction n 𝕜).comp ⟨Subtype.val, continuous_subtype_val⟩ =
        ContinuousMap.id _ from ContinuousMap.ext ?_]
    rintro ⟨_, k, rfl⟩
    exact polarRetraction_toPSL k
  right_inv := ⟨(polarHomotopy n 𝕜).toHomotopy.symm⟩

@[simp]
theorem polarHomotopyEquiv_apply
    (x : (toPSL : specialUnitaryGroup n 𝕜 →* ProjectiveSpecialLinearGroup n 𝕜).range) :
    polarHomotopyEquiv n 𝕜 x = x :=
  (rfl)

@[simp]
theorem polarHomotopyEquiv_symm_apply (x : ProjectiveSpecialLinearGroup n 𝕜) :
    (polarHomotopyEquiv n 𝕜).symm x = polarRetraction n 𝕜 x :=
  (rfl)

end Matrix.ProjectiveSpecialLinearGroup
