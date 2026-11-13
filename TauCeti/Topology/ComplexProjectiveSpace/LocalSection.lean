/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
public import TauCeti.Topology.ComplexProjectiveSpace.Charts
public import TauCeti.Topology.ComplexProjectiveSpace.Homogeneous
public import TauCeti.Topology.Homotopy.HurewiczFibration.LocallyTrivial
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Householder

/-!
# Local sections of the unitary group over complex projective space

The orbit map `A ↦ A • [e₀]` of `U(n + 1)` on `CPⁿ`, through the base point
`TauCeti.ComplexProjectiveSpace.basePoint`, has a continuous section over each standard affine
chart `{X_k ≠ 0}` (`TauCeti.ComplexProjectiveSpace.affineOpen`). A point of the chart with affine
coordinates `z` has the unit representative `y = w / ‖w‖`, where `w = (z₀, …, 1, …, z_{n-1})` has
the entry `1` in position `k`, so that `y_k = 1 / ‖w‖` is real and positive. Two Householder
reflections compose to a unitary matrix sending `e_k` to `y`:

* the reflection `1 - 2 e_k e_kᴴ` in `e_k` sends `e_k` to `-e_k`;
* the reflection `1 - (1 + y_k)⁻¹ u uᴴ` in `u = e_k + y` sends `-e_k` to `y`. Its coefficient
  involves only `1 + y_k ≥ 1`, so it depends continuously on the point of the chart, including
  its centre `y = e_k`.

Composing them with the permutation matrix exchanging `e₀` and `e_k` gives the section
`TauCeti.ComplexProjectiveSpace.unitaryLocalSection k`, whose first column is `y`.

By the passage from local sections of an orbit map to bundle charts
(`TauCeti.orbitMapTrivialization`), each section trivializes `A ↦ A • [e₀]` over its chart, with
fibre the stabilizer of `[e₀]`, which is the block subgroup `U(1) × U(n)`
(`TauCeti.ComplexProjectiveSpace.range_prodBlockSucc_eq_stabilizer`). The chart intertwines right
multiplication by the stabilizer on `U(n + 1)` with right multiplication on the fibre, so
`U(n + 1) → CPⁿ` is a principal bundle with structure group `U(1) × U(n)`. As `CPⁿ` is compact
Hausdorff, the orbit map is a Hurewicz fibration.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.unitaryLocalSection`: the section over the chart `X_k ≠ 0`.
* `TauCeti.ComplexProjectiveSpace.continuousOn_unitaryLocalSection` and
  `TauCeti.ComplexProjectiveSpace.unitaryLocalSection_smul_basePoint`: it is a continuous section
  of the orbit map over the chart.
* `TauCeti.ComplexProjectiveSpace.unitaryTrivialization`: the chart of the orbit map over
  `X_k ≠ 0` determined by the section, with
  `TauCeti.ComplexProjectiveSpace.unitaryTrivialization_apply_mul` for its equivariance.
* `TauCeti.ComplexProjectiveSpace.isHurewiczFibration_smul_basePoint`: the orbit map
  `U(n + 1) → CPⁿ` is a Hurewicz fibration.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7 (local
  cross-sections of the coset spaces of the classical groups).
-/

public section

noncomputable section

open Matrix Metric

universe w

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

/-! ### A unitary matrix with prescribed first column -/

/-- The axis `e_k + y` of the second reflection, for the unit representative
`y = affineUnitVector k z`. -/
private def reflectionAxis (k : Fin (n + 1)) (z : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Pi.single k 1 + (affineUnitVector k z : EuclideanSpace ℂ (Fin (n + 1))).ofLp

/-- The unitary matrix with first column the unit representative `y = affineUnitVector k z`: the
permutation matrix exchanging `e₀` and `e_k`, followed by the reflection in `e_k` and the
reflection in `e_k + y`. -/
private def sectionMatrix (k : Fin (n + 1)) (z : Fin n → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (1 - (1 + ‖affineVector k z‖⁻¹)⁻¹ •
      vecMulVec (reflectionAxis k z) (star (reflectionAxis k z))) *
    (1 - (2 : ℝ) • vecMulVec (Pi.single k (1 : ℂ)) (star (Pi.single k 1))) *
    (Equiv.swap 0 k).permMatrix ℂ

/-- The Hermitian square of `e_k + y`, for the unit representative `y`, is `2 + 2 y_k`. -/
private theorem star_reflectionAxis_dotProduct_self (k : Fin (n + 1)) (z : Fin n → ℂ) :
    star (reflectionAxis k z) ⬝ᵥ reflectionAxis k z =
      algebraMap ℝ ℂ (2 + 2 * ‖affineVector k z‖⁻¹) := by
  -- The unit representative `y` has Hermitian square `⟪y, y⟫ = ‖y‖² = 1`.
  have hy : star (affineUnitVector k z : EuclideanSpace ℂ (Fin (n + 1))).ofLp ⬝ᵥ
      (affineUnitVector k z : EuclideanSpace ℂ (Fin (n + 1))).ofLp = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      mem_sphere_zero_iff_norm.1 (affineUnitVector k z).2]
    simp
  simp only [reflectionAxis, star_add, add_dotProduct, dotProduct_add, hy, Pi.star_single, star_one,
    single_dotProduct, dotProduct_single, Pi.add_apply, Pi.star_apply, Pi.single_eq_same,
    affineUnitVector_apply_self, Complex.star_def, Complex.conj_ofReal, one_mul, mul_one,
    Complex.coe_algebraMap]
  push_cast
  ring

private theorem sectionMatrix_mem_unitaryGroup (k : Fin (n + 1)) (z : Fin n → ℂ) :
    sectionMatrix k z ∈ unitaryGroup (Fin (n + 1)) ℂ := by
  have hc : (1 + ‖affineVector k z‖⁻¹)⁻¹ * (1 + ‖affineVector k z‖⁻¹)⁻¹ *
      (2 + 2 * ‖affineVector k z‖⁻¹) = 2 * (1 + ‖affineVector k z‖⁻¹)⁻¹ := by
    field_simp
  have he : star (Pi.single k (1 : ℂ)) ⬝ᵥ Pi.single k 1 = algebraMap ℝ ℂ 1 := by
    simp [Pi.star_single]
  rw [sectionMatrix]
  exact mul_mem (mul_mem
    (one_sub_smul_vecMulVec_mem_unitary (star_reflectionAxis_dotProduct_self k z) hc)
    (one_sub_smul_vecMulVec_mem_unitary he (by norm_num)))
    (permMatrix_mem_unitary _)

/-- The first column of `sectionMatrix k z` is the unit representative `affineUnitVector k z`. -/
private theorem sectionMatrix_mulVec_single_zero (k : Fin (n + 1)) (z : Fin n → ℂ) :
    sectionMatrix k z *ᵥ Pi.single 0 1 =
      (affineUnitVector k z : EuclideanSpace ℂ (Fin (n + 1))).ofLp := by
  set y := (affineUnitVector k z : EuclideanSpace ℂ (Fin (n + 1))).ofLp with hy
  set r := ‖affineVector k z‖⁻¹
  have hr : 0 ≤ r := inv_nonneg.2 (norm_nonneg _)
  have hyk : y k = (r : ℂ) := affineUnitVector_apply_self k z
  -- The permutation matrix sends `e₀` to `e_k`.
  have hP : (Equiv.swap 0 k).permMatrix ℂ *ᵥ Pi.single 0 1 = Pi.single k 1 := by
    rw [permMatrix_mulVec]
    ext i
    simp only [Function.comp_apply, Pi.single_apply, Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_left]
  -- The reflection in `e_k` sends `e_k` to `-e_k`.
  have hE : (1 - (2 : ℝ) • vecMulVec (Pi.single k (1 : ℂ)) (star (Pi.single k 1))) *ᵥ
      Pi.single k 1 = -Pi.single k 1 := by
    rw [one_sub_smul_vecMulVec_mulVec]
    simp only [Pi.star_single, star_one, single_dotProduct, Pi.single_eq_same, one_mul,
      MulOpposite.op_one, one_smul]
    module
  -- The reflection in `e_k + y` sends `e_k` to `-y`, since the Hermitian product of `e_k + y`
  -- with `e_k` is `1 + r`.
  have hU : (1 - (1 + r)⁻¹ • vecMulVec (reflectionAxis k z) (star (reflectionAxis k z))) *ᵥ
      Pi.single k 1 = -y := by
    -- The only computation: `(1 + r)⁻¹ (1 + r) = 1`.
    have hc : (1 + r)⁻¹ • (1 + (r : ℂ)) = 1 := by
      have : (1 + (r : ℂ)) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < 1 + r).ne'
      rw [Complex.real_smul]
      push_cast
      field_simp
    rw [reflectionAxis, ← hy, one_sub_smul_vecMulVec_mulVec, dotProduct_single, op_smul_eq_smul,
      mul_one]
    simp only [Pi.star_apply, Pi.add_apply, Pi.single_eq_same, hyk, star_add, star_one,
      Complex.star_def, Complex.conj_ofReal]
    rw [← smul_assoc, hc, one_smul]
    abel
  rw [sectionMatrix, ← mulVec_mulVec, ← mulVec_mulVec, hP, hE, mulVec_neg, hU, neg_neg]

/-- The unitary matrix with first column `affineUnitVector k z`, as an element of `U(n + 1)`. -/
private def sectionUnitary (k : Fin (n + 1)) (z : Fin n → ℂ) : unitaryGroup (Fin (n + 1)) ℂ :=
  ⟨sectionMatrix k z, sectionMatrix_mem_unitaryGroup k z⟩

private theorem continuous_sectionUnitary (k : Fin (n + 1)) :
    Continuous (sectionUnitary (n := n) k) := by
  have hn : Continuous fun z ↦ ‖affineVector (n := n) k z‖⁻¹ :=
    (continuous_affineVector k).norm.inv₀ fun z ↦ norm_ne_zero_iff.2 (affineVector_ne_zero k z)
  have hc : Continuous fun z ↦ (1 + ‖affineVector (n := n) k z‖⁻¹)⁻¹ :=
    (continuous_const.add hn).inv₀ fun z ↦
      (add_pos_of_pos_of_nonneg one_pos (inv_nonneg.2 (norm_nonneg _))).ne'
  have hu : Continuous (reflectionAxis (n := n) k) :=
    continuous_const.add ((PiLp.continuous_ofLp 2 _).comp
      (continuous_subtype_val.comp (affineUnitVector k).continuous))
  refine Continuous.subtype_mk ?_ _
  unfold sectionMatrix
  exact ((continuous_const.sub (hc.smul (hu.matrix_vecMulVec hu.star))).matrix_mul
    continuous_const).matrix_mul continuous_const

/-! ### The local sections and the induced charts -/

/-- **A local section of `U(n + 1) → CPⁿ`** over the affine chart `X_k ≠ 0`: a unitary matrix
whose first column is the unit representative `w / ‖w‖` of the point, where `w` is its vector of
homogeneous coordinates normalized by `w_k = 1`. It is continuous on the chart
(`TauCeti.ComplexProjectiveSpace.continuousOn_unitaryLocalSection`) and sends the base point
`[e₀]` to the given point there
(`TauCeti.ComplexProjectiveSpace.unitaryLocalSection_smul_basePoint`); outside the chart its
values carry no meaning. -/
def unitaryLocalSection (k : Fin (n + 1)) (p : ComplexProjectiveSpace n) :
    unitaryGroup (Fin (n + 1)) ℂ :=
  sectionUnitary k (affineChart k p)

/-- The local section over the chart `X_k ≠ 0` is continuous on that chart. -/
theorem continuousOn_unitaryLocalSection (k : Fin (n + 1)) :
    ContinuousOn (unitaryLocalSection (n := n) k) (affineOpen k) := by
  rw [← affineChart_source]
  exact (continuous_sectionUnitary k).comp_continuousOn (affineChart k).continuousOn

/-- The first column of the local section over `X_k ≠ 0` is the unit representative `w / ‖w‖` of
the point, for its homogeneous coordinate vector `w` normalized by `w_k = 1`. -/
theorem col_zero_unitaryLocalSection (k : Fin (n + 1)) (p : ComplexProjectiveSpace n) :
    (unitaryLocalSection k p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).col 0 =
      (affineUnitVector k (affineChart k p) : EuclideanSpace ℂ (Fin (n + 1))).ofLp := by
  rw [← mulVec_single_one]
  exact sectionMatrix_mulVec_single_zero k _

/-- **The local section is a section of the orbit map** over its chart: on `X_k ≠ 0` it carries
the base point `[e₀]` to the given point. -/
theorem unitaryLocalSection_smul_basePoint {k : Fin (n + 1)} {p : ComplexProjectiveSpace n}
    (hp : p ∈ affineOpen k) : unitaryLocalSection k p • basePoint n = p := by
  have hp' : p ∈ (affineChart k).source := by rwa [affineChart_source]
  rw [basePoint_def, smul_mk]
  conv_rhs => rw [← (affineChart k).left_inv hp', affineChart_symm_apply, affineParam_def]
  congr 1
  ext1
  rw [LinearIsometryEquiv.coe_smul_unitSphere, UnitaryGroup.toLinearIsometryEquiv_single,
    col_zero_unitaryLocalSection, WithLp.toLp_ofLp]

variable (n) in
/-- **The chart of `U(n + 1) → CPⁿ` over `X_k ≠ 0`** determined by the local section `s`: it sends
`A` to `(A • [e₀], s(A • [e₀])⁻¹ A)`, with fibre the stabilizer `U(1) × U(n)` of `[e₀]`
(`TauCeti.ComplexProjectiveSpace.range_prodBlockSucc_eq_stabilizer`), and its inverse sends
`(p, h)` to `s(p) h`. -/
def unitaryTrivialization (k : Fin (n + 1)) :
    Bundle.Trivialization (MulAction.stabilizer (unitaryGroup (Fin (n + 1)) ℂ) (basePoint n))
      fun A : unitaryGroup (Fin (n + 1)) ℂ ↦ A • basePoint n :=
  orbitMapTrivialization (basePoint n) (continuous_id.smul continuous_const) (affineOpen k)
    (isOpen_affineOpen k) (unitaryLocalSection k) (continuousOn_unitaryLocalSection k)
    fun _ hp ↦ unitaryLocalSection_smul_basePoint hp

/-- The base of the chart over `X_k ≠ 0` is that affine chart. -/
@[simp]
theorem unitaryTrivialization_baseSet (k : Fin (n + 1)) :
    (unitaryTrivialization n k).baseSet = affineOpen k :=
  orbitMapTrivialization_baseSet

/-- Over `X_k ≠ 0`, the fibre coordinate of `A` is `s(A • [e₀])⁻¹ A` for the local section
`s`. -/
@[simp]
theorem unitaryTrivialization_fiberCoordinate {k : Fin (n + 1)}
    {A : unitaryGroup (Fin (n + 1)) ℂ} (hA : A • basePoint n ∈ affineOpen k) :
    ((unitaryTrivialization n k A).2 : unitaryGroup (Fin (n + 1)) ℂ) =
      (unitaryLocalSection k (A • basePoint n))⁻¹ * A :=
  orbitMapTrivialization_fiberCoordinate hA

/-- The inverse of the chart over `X_k ≠ 0` multiplies the local section by the fibre
coordinate. -/
@[simp]
theorem unitaryTrivialization_symm_apply (k : Fin (n + 1))
    (p : ComplexProjectiveSpace n ×
      MulAction.stabilizer (unitaryGroup (Fin (n + 1)) ℂ) (basePoint n)) :
    (unitaryTrivialization n k).toOpenPartialHomeomorph.symm p = unitaryLocalSection k p.1 * p.2 :=
  orbitMapTrivialization_symm_apply p

/-- **The charts are principal**: they intertwine right multiplication by the stabilizer
`U(1) × U(n)` of `[e₀]` on `U(n + 1)` with right multiplication on the fibre. -/
theorem unitaryTrivialization_apply_mul {k : Fin (n + 1)} {A : unitaryGroup (Fin (n + 1)) ℂ}
    (hA : A • basePoint n ∈ affineOpen k)
    (h : MulAction.stabilizer (unitaryGroup (Fin (n + 1)) ℂ) (basePoint n)) :
    unitaryTrivialization n k (A * h) =
      ((unitaryTrivialization n k A).1, (unitaryTrivialization n k A).2 * h) :=
  orbitMapTrivialization_apply_mul hA h

/-- **`U(n + 1) → CPⁿ` is a Hurewicz fibration**: the orbit map `A ↦ A • [e₀]` is locally
trivial over the affine charts, and `CPⁿ` is compact Hausdorff, hence normal and paracompact. -/
theorem isHurewiczFibration_smul_basePoint :
    IsHurewiczFibration.{w} fun A : unitaryGroup (Fin (n + 1)) ℂ ↦ A • basePoint n :=
  isHurewiczFibration_of_exists_trivialization fun p ↦
    let ⟨k, hk⟩ := exists_mem_affineOpen p
    ⟨unitaryTrivialization n k, by rwa [unitaryTrivialization_baseSet]⟩

end TauCeti.ComplexProjectiveSpace
