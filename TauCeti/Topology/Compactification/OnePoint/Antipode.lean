/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine
import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.UnitaryGroup
import TauCeti.Topology.Compactification.OnePoint.Map

/-!
# The antipodal map of the projective line and the rotation group `PSU(2)`

On the projective line `OnePoint 𝕜` over `𝕜 = ℝ` or `ℂ`, the *antipodal map*
`OnePoint.antipode` is `z ↦ -1 / conj z`, exchanging `0` and `∞`. It is an involution without fixed
points (`OnePoint.antipode_antipode`, `OnePoint.antipode_ne_self`). Classically, in homogeneous
coordinates it sends the line through `(v₀, v₁)` to the line through `(-conj v₁, conj v₀)`, its
orthogonal complement in `𝕜²`; and for `𝕜 = ℂ`, under stereographic projection of the unit sphere
of `ℝ³`, it is the antipodal map `x ↦ -x` of the round sphere. These descriptions motivate the
name and are not used below.

The main result characterizes the projective special unitary group `PSU(2)`, the range of
`Matrix.specialUnitaryGroup.toPSL`, inside `PSL(2, 𝕜)`: a Möbius transformation lies in `PSU(2)`
exactly when it commutes with the antipodal map
(`Matrix.ProjectiveSpecialLinearGroup.mem_range_toPSL_iff_forall_smul_antipode`). For instance
the rotation `z ↦ e^{iθ} z`, the class of `diag (e^{iθ/2}, e^{-iθ/2})`, lies in `PSU(2)`. The
dilation `z ↦ 2 z` fixes `0` and `∞` but does not: it sends `-1 = antipode 1` to `-2`, while
`antipode 2 = -1 / 2`.

The proof writes the antipodal map as the Möbius transformation `z ↦ -1 / z` of the matrix
`S = !![0, -1; 1, 0]` composed with complex conjugation, which conjugates the Möbius action by
conjugating matrix entries (`OnePoint.map_smul`). If the class of `A ∈ SL(2, 𝕜)` commutes with
the antipodal map, then `(A S)⁻¹ S conj(A)` fixes every point of the projective line, so it is a
scalar matrix (`TauCeti.mem_center_of_smul_zero_one_infty_eq_self`). Comparing entries, `Aᴴ A`
is then a scalar matrix, and `A` is unitary because its determinant is one
(`Matrix.mem_unitaryGroup_of_star_mul_self_eq_scalar`).

## Main declarations

* `OnePoint.antipode`: the antipodal map `z ↦ -1 / conj z` of the projective line.
* `OnePoint.antipode_antipode`, `OnePoint.antipode_ne_self`: it is a fixed-point-free involution.
* `Matrix.specialUnitaryGroup.toPSL_smul_antipode`: special unitary Möbius transformations
  commute with it.
* `Matrix.ProjectiveSpecialLinearGroup.mem_range_toPSL_iff_forall_smul_antipode`: the elements of
  `PSL(2, 𝕜)` commuting with it are exactly those of `PSU(2)`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, Chapter 4 (complex Möbius transformations and the unitary subgroup).
-/

public section

open scoped MatrixGroups

open Matrix

namespace OnePoint

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq 𝕜]

/-- The antipodal map `z ↦ -1 / conj z` of the projective line over `ℝ` or `ℂ`, exchanging `0`
and `∞`. Classically it sends a line of `𝕜²` to its orthogonal complement, and for the Riemann
sphere it is the antipodal map of the round sphere. -/
noncomputable def antipode (x : OnePoint 𝕜) : OnePoint 𝕜 :=
  x.elim ((0 : 𝕜) : OnePoint 𝕜) fun z => if z = 0 then ∞ else ((-(starRingEnd 𝕜 z)⁻¹ : 𝕜))

@[simp]
theorem antipode_infty : antipode (∞ : OnePoint 𝕜) = ((0 : 𝕜) : OnePoint 𝕜) := by
  simp [antipode]

@[simp]
theorem antipode_zero : antipode ((0 : 𝕜) : OnePoint 𝕜) = ∞ := by
  simp [antipode]

theorem antipode_coe {z : 𝕜} (hz : z ≠ 0) :
    antipode (z : OnePoint 𝕜) = ((-(starRingEnd 𝕜 z)⁻¹ : 𝕜) : OnePoint 𝕜) := by
  simp [antipode, hz]

/-- The antipodal map is an involution. -/
@[simp]
theorem antipode_antipode (x : OnePoint 𝕜) : antipode (antipode x) = x := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · simp [hz]
    · rw [antipode_coe hz, antipode_coe (by simpa using hz)]
      simp

theorem antipode_involutive : Function.Involutive (antipode (𝕜 := 𝕜)) :=
  antipode_antipode

/-- The antipodal map has no fixed points: `-1 / conj z = z` would give `‖z‖ ^ 2 = -1`. -/
theorem antipode_ne_self (x : OnePoint 𝕜) : antipode x ≠ x := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · simp [hz]
    · rw [antipode_coe hz, Ne, coe_eq_coe]
      intro h
      have hc : starRingEnd 𝕜 z ≠ 0 := by simpa using hz
      have hmul : z * starRingEnd 𝕜 z = -1 := by
        nth_rewrite 1 [← h]
        field_simp
      rw [RCLike.mul_conj] at hmul
      have hre := congrArg RCLike.re hmul
      norm_num at hre
      nlinarith [norm_nonneg z]

/-- The matrix `!![0, -1; 1, 0]` of the Möbius transformation `z ↦ -1 / z`. -/
private noncomputable def antipodeGL : GL (Fin 2) 𝕜 :=
  SpecialLinearGroup.toGL ⟨!![0, -1; 1, 0], by simp [det_fin_two]⟩

omit [DecidableEq 𝕜] in
private theorem antipodeGL_apply (i j : Fin 2) :
    (antipodeGL : GL (Fin 2) 𝕜) i j = !![0, -1; 1, 0] i j :=
  rfl

/-- The antipodal map is complex conjugation followed by the Möbius transformation
`z ↦ -1 / z`. -/
private theorem antipode_eq_smul (x : OnePoint 𝕜) :
    antipode x = (antipodeGL : GL (Fin 2) 𝕜) • OnePoint.map (starRingEnd 𝕜) x := by
  induction x using OnePoint.rec with
  | infty => simp [smul_infty_eq_ite, antipodeGL_apply]
  | coe z =>
    by_cases hz : z = 0
    · simp [hz, smul_some_eq_ite, antipodeGL_apply]
    · simp [antipode_coe hz, smul_some_eq_ite, antipodeGL_apply, hz, neg_div]

end OnePoint

open OnePoint

namespace Matrix.specialUnitaryGroup

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq 𝕜]

/-- **Rotations commute with the antipodal map.** A special unitary matrix acts on the projective
line by a Möbius transformation commuting with `z ↦ -1 / conj z`. -/
theorem toPSL_smul_antipode (A : specialUnitaryGroup (Fin 2) 𝕜) (x : OnePoint 𝕜) :
    toPSL A • antipode x = antipode (toPSL A • x) := by
  rw [toPSL_apply, pslMk_smul, pslMk_smul, antipode_eq_smul,
    antipode_eq_smul, OnePoint.map_smul, smul_smul, smul_smul]
  congr 1
  -- For a special unitary `A`, `conj A` is the adjugate transpose of `A`.
  have hstar := fun i j => congrFun (congrFun (specialUnitaryGroup.star_eq_adjugate A) i) j
  simp only [star_apply, RCLike.star_def, adjugate_fin_two] at hstar
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, antipodeGL_apply, hstar]

end Matrix.specialUnitaryGroup

namespace Matrix.ProjectiveSpecialLinearGroup

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq 𝕜]

/-- **`PSU(2)` is the group of Möbius transformations commuting with the antipodal map.** Over
`ℝ` or `ℂ`, an element of `PSL(2, 𝕜)` lies in the range of `SU(2)` exactly when it commutes with
`z ↦ -1 / conj z`. Classically, for the Riemann sphere these are the rotations of the round
sphere; that identification is not proved here. -/
theorem mem_range_toPSL_iff_forall_smul_antipode (g : PSL(2, 𝕜)) :
    g ∈ (specialUnitaryGroup.toPSL : specialUnitaryGroup (Fin 2) 𝕜 →* _).range ↔
      ∀ x : OnePoint 𝕜, g • antipode x = antipode (g • x) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨A, rfl⟩ x
    exact specialUnitaryGroup.toPSL_smul_antipode A x
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  -- The two composites `A S` and `S conj(A)` agree on the projective line.
  have hfix : ∀ y : OnePoint 𝕜, ((SpecialLinearGroup.toGL A * antipodeGL)⁻¹ * (antipodeGL *
      GeneralLinearGroup.map (starRingEnd 𝕜) (SpecialLinearGroup.toGL A))) • y = y := by
    intro y
    have hy := h (OnePoint.map (starRingEnd 𝕜) y)
    rw [pslMk_smul, pslMk_smul, antipode_eq_smul, antipode_eq_smul, OnePoint.map_smul,
      TauCeti.onePointMap_involutive (f := starRingEnd 𝕜) starRingEnd_self_apply, smul_smul,
      smul_smul] at hy
    rw [mul_smul, ← hy, inv_smul_smul]
  -- Hence they differ by a scalar matrix.
  have hcen := TauCeti.mem_center_of_smul_zero_one_infty_eq_self (hfix _) (hfix _) (hfix _)
  rw [GeneralLinearGroup.center_eq_range_scalar] at hcen
  obtain ⟨u, hu⟩ := hcen
  have hc : antipodeGL * GeneralLinearGroup.map (starRingEnd 𝕜) (SpecialLinearGroup.toGL A) =
      SpecialLinearGroup.toGL A * antipodeGL * GeneralLinearGroup.scalar (Fin 2) u := by
    rw [hu, mul_inv_cancel_left]
  have e := fun i j => congrArg (fun M : GL (Fin 2) 𝕜 => (M : Matrix (Fin 2) (Fin 2) 𝕜) i j) hc
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two,
    antipodeGL_apply, GeneralLinearGroup.map_apply, scalar_apply,
    SpecialLinearGroup.coe_GL_coe_matrix] at e
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h1 := A.2
    rwa [det_fin_two] at h1
  -- Comparing entries, `Aᴴ A` is the scalar matrix `u`.
  have hAA : star (A : Matrix (Fin 2) (Fin 2) 𝕜) * A = scalar (Fin 2) (u : 𝕜) := by
    have e00 := e 0 0
    have e01 := e 0 1
    have e10 := e 1 0
    have e11 := e 1 1
    simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, zero_mul,
      cons_val_one, neg_mul, one_mul, zero_add, mul_zero, mul_one, diagonal_apply_eq, mul_neg,
      add_zero, ne_eq, one_ne_zero, not_false_eq_true, diagonal_apply_ne, zero_ne_one, neg_inj]
      at e00 e01 e10 e11
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.mul_apply, star_apply,
        RCLike.star_def, Fin.sum_univ_two, scalar_apply, diagonal_apply_eq, ne_eq, zero_ne_one,
        one_ne_zero, not_false_eq_true, diagonal_apply_ne]
    · linear_combination A 0 0 * e10 - A 1 0 * e00 + (u : 𝕜) * hdet
    · linear_combination A 0 1 * e10 - A 1 1 * e00
    · linear_combination A 0 0 * e11 + A 1 0 * e01
    · linear_combination A 0 1 * e11 + A 1 1 * e01 + (u : 𝕜) * hdet
  rw [specialUnitaryGroup.mk_mem_range_toPSL_iff]
  exact mem_unitaryGroup_of_star_mul_self_eq_scalar (by simp [A.2]) hAA

end Matrix.ProjectiveSpecialLinearGroup
