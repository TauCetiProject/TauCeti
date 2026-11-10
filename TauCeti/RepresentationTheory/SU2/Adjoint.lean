/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Quotient

public import TauCeti.LinearAlgebra.Matrix.Pauli
public import TauCeti.RepresentationTheory.SU2.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv
import TauCeti.LinearAlgebra.Matrix.CrossProduct
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Three
import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.WeightedSumSquares
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# The double cover `SU(2) → SO(3)`

A unitary `2 × 2` matrix `U` acts on the traceless Hermitian matrices by conjugation,
`A ↦ U A U*`. Through the Pauli map `TauCeti.pauli : ℝ³ ≃ {traceless Hermitian}` this is a linear
map of `ℝ³`, the matrix `TauCeti.pauliRotation U`, characterized by

`pauli (pauliRotation U *ᵥ x) = U * pauli x * U*`

(`TauCeti.pauli_pauliRotation_mulVec`). Conjugation preserves the trace form and the commutator,
which the Pauli map turns into the dot product and the cross product of `ℝ³`
(`TauCeti.trace_pauli_mul_pauli`, `TauCeti.pauli_mul_sub_mul_pauli`). So `pauliRotation U` is
orthogonal and preserves the cross product, hence has determinant one: it is a rotation, and
`U ↦ pauliRotation U` is a group homomorphism `U(2) → SO(3)` (`TauCeti.pauliRotationHom`). Its
kernel consists of the scalar unitary matrices (`TauCeti.pauliRotation_eq_one_iff`).

The rotation `pauliRotation U` moves the north pole `e₂ = (0, 0, 1)` to the point of the unit
sphere attached to the first column `u` of `U` by the Pauli map: `U σ₃ U*` is `2 u u* - 1`, the
reflection fixing the complex line `ℂ u`, so

`pauliRotation U *ᵥ e₂ = (2 Re (u₁ conj u₀), 2 Im (u₁ conj u₀), 2 |u₀|² - 1)`

(`TauCeti.pauliRotation_mulVec_single_two`). This is the point `√2 (P - 1 / 2)` of the round
sphere of traceless Hermitian matrices, where `P = u u*` is the orthogonal projection onto the
line `ℂ u`, read in the orthonormal basis `σᵢ / √2`.

Restricted to `SU(2)` the homomorphism is the **double cover** `TauCeti.SU2.toSO3`. Up to the
factor `-i` and a fixed rotation of coordinates, the Pauli map is the matrix of the pure quaternion
attached to a vector by `TauCeti.realCliffordThreeZeroPureQuaternionEquiv`, so `toSO3` is the
vector action of `Spin(3) ≅ SU(2)` (`TauCeti.realSpinThreeEquivSpecialUnitary_action`); it is
therefore surjective (`TauCeti.SU2.toSO3_surjective`). Its kernel is `{1, -1}`
(`TauCeti.SU2.toSO3_eq_one_iff`), the center of `SU(2)` (`TauCeti.SU2.ker_toSO3`), and since
`SU(2)` is compact and `SO(3)` is Hausdorff, it induces an isomorphism of topological groups
`SU(2) ⧸ {±1} ≃ₜ* SO(3)` (`TauCeti.SU2.quotientKerToSO3`).
The Pauli map is a covering map (`TauCeti.SU2.isCoveringMap_toSO3`).

## Main definitions

* `TauCeti.pauliRotation`: the matrix of the action of a unitary matrix on `ℝ³` through the Pauli
  map.
* `TauCeti.pauliRotationHom`: the homomorphism `U(2) →* SO(3)`.
* `TauCeti.SU2.toSO3`: its restriction `SU(2) →* SO(3)`, the double cover.
* `TauCeti.SU2.quotientKerToSO3`: the induced isomorphism `SU(2) ⧸ {±1} ≃ₜ* SO(3)`.

## Main results

* `TauCeti.pauliRotation_eq_iff`: `pauliRotation U` is the only matrix `R` with
  `pauli (R *ᵥ x) = U * pauli x * U*` for all `x`.
* `TauCeti.dotProduct_pauliRotation_mulVec` and `TauCeti.pauliRotation_mulVec_cross`: the action
  preserves the dot product and the cross product.
* `TauCeti.pauliRotation_mem_specialOrthogonalGroup`: `pauliRotation U` is a rotation.
* `TauCeti.pauliRotation_mulVec_single_two`: the image of the north pole.
* `TauCeti.pauliRotation_eq_one_iff`: the kernel of `U(2) → SO(3)` is the scalar matrices.
* `TauCeti.SU2.toSO3_eq_one_iff`: the kernel of `SU(2) → SO(3)` is `{1, -1}`.
* `TauCeti.SU2.ker_toSO3`: the kernel of `SU(2) → SO(3)` is the center of `SU(2)`.
* `TauCeti.SU2.coe_toSO3_torusHom`: the maximal torus `diag (z, z⁻¹)` maps to the rotations about
  the axis `(0, 0, 1)`.
* `TauCeti.SU2.toSO3_surjective`: `SU(2) → SO(3)` is surjective.
* `TauCeti.SU2.isCoveringMap_toSO3`: the Pauli map is a covering map.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Example 2.5(5) and Exercises 2.8–2.11.

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics
  129, Springer, 1991, §7.3 and §10.1.
* J. Stillwell, *Naive Lie Theory*, Undergraduate Texts in Mathematics, Springer, 2008, §1.5
  and §2.3.
-/

public section

open Matrix Complex
open scoped ComplexConjugate Quaternion

namespace TauCeti

variable (U V : Matrix.unitaryGroup (Fin 2) ℂ)

/-! ### Conjugation of traceless Hermitian matrices -/

/-- Conjugating `pauli x` by a unitary matrix gives a Hermitian matrix. -/
private theorem isHermitian_mul_pauli_mul_star (x : Fin 3 → ℝ) :
    ((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli x * star (U : Matrix (Fin 2) (Fin 2) ℂ)).IsHermitian :=
  isHermitian_mul_mul_conjTranspose _ (isHermitian_pauli x)

/-- Conjugation by a unitary matrix preserves the trace. -/
private theorem trace_mul_mul_star (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ((U : Matrix (Fin 2) (Fin 2) ℂ) * A * star (U : Matrix (Fin 2) (Fin 2) ℂ)).trace = A.trace := by
  rw [trace_mul_cycle, mem_unitaryGroup_iff'.mp U.2, one_mul]

/-- Conjugating `pauli x` by a unitary matrix gives a traceless matrix. -/
private theorem trace_mul_pauli_mul_star (x : Fin 3 → ℝ) :
    ((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli x * star (U : Matrix (Fin 2) (Fin 2) ℂ)).trace = 0 := by
  rw [trace_mul_mul_star, trace_pauli]

/-! ### The rotation attached to a unitary matrix -/

/-- The matrix of the action of a unitary `2 × 2` matrix `U` on `ℝ³` by conjugation through the
Pauli map: the unique matrix `R` with `pauli (R *ᵥ x) = U * pauli x * U*` for all `x`
(`TauCeti.pauliRotation_eq_iff`). It is a rotation
(`TauCeti.pauliRotation_mem_specialOrthogonalGroup`). -/
noncomputable def pauliRotation : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix' (pauliCoord ∘ₗ LinearMap.mulLeft ℝ (U : Matrix (Fin 2) (Fin 2) ℂ) ∘ₗ
    LinearMap.mulRight ℝ (star (U : Matrix (Fin 2) (Fin 2) ℂ)) ∘ₗ pauli)

/-- `pauliRotation U` sends `x` to the Pauli coordinates of `U * pauli x * U*`. -/
theorem pauliRotation_mulVec (x : Fin 3 → ℝ) :
    pauliRotation U *ᵥ x = pauliCoord
      ((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli x * star (U : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [pauliRotation, LinearMap.toMatrix'_mulVec]
  simp [mul_assoc]

/-- The defining property of `pauliRotation U`: the Pauli map intertwines it with conjugation
by `U`. -/
theorem pauli_pauliRotation_mulVec (x : Fin 3 → ℝ) :
    pauli (pauliRotation U *ᵥ x) =
      (U : Matrix (Fin 2) (Fin 2) ℂ) * pauli x * star (U : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pauliRotation_mulVec]
  exact pauli_pauliCoord (isHermitian_mul_pauli_mul_star U x) (trace_mul_pauli_mul_star U x)

/-- `pauliRotation U` is the only matrix intertwined by the Pauli map with conjugation by `U`. -/
theorem pauliRotation_eq_iff {R : Matrix (Fin 3) (Fin 3) ℝ} :
    pauliRotation U = R ↔ ∀ x, pauli (R *ᵥ x) =
      (U : Matrix (Fin 2) (Fin 2) ℂ) * pauli x * star (U : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨fun h x => h ▸ pauli_pauliRotation_mulVec U x, fun h => ?_⟩
  refine ext_iff_mulVec.mpr fun x => pauli_injective ?_
  rw [pauli_pauliRotation_mulVec, h]

/-- The identity matrix acts on `ℝ³` by the identity. -/
@[simp]
theorem pauliRotation_one : pauliRotation 1 = 1 :=
  (pauliRotation_eq_iff 1).mpr fun x => by simp

/-- The action on `ℝ³` is multiplicative. -/
@[simp]
theorem pauliRotation_mul : pauliRotation (U * V) = pauliRotation U * pauliRotation V := by
  refine (pauliRotation_eq_iff _).mpr fun x => ?_
  rw [← mulVec_mulVec, pauli_pauliRotation_mulVec, pauli_pauliRotation_mulVec]
  simp [Submonoid.coe_mul, star_mul, mul_assoc]

/-- Conjugation by a unitary matrix is multiplicative. -/
private theorem mul_mul_mul_star (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (U : Matrix (Fin 2) (Fin 2) ℂ) * (A * B) * star (U : Matrix (Fin 2) (Fin 2) ℂ) =
      (U : Matrix (Fin 2) (Fin 2) ℂ) * A * star (U : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U : Matrix (Fin 2) (Fin 2) ℂ) * B * star (U : Matrix (Fin 2) (Fin 2) ℂ)) := by
  simpa using map_mul (Unitary.conjStarAlgAut ℝ (Matrix (Fin 2) (Fin 2) ℂ) U) A B

/-- Conjugation by a unitary matrix preserves the dot product of Pauli coordinates. -/
theorem dotProduct_pauliRotation_mulVec (x y : Fin 3 → ℝ) :
    (pauliRotation U *ᵥ x) ⬝ᵥ (pauliRotation U *ᵥ y) = x ⬝ᵥ y := by
  have h := trace_pauli_mul_pauli (pauliRotation U *ᵥ x) (pauliRotation U *ᵥ y)
  rw [pauli_pauliRotation_mulVec, pauli_pauliRotation_mulVec, ← mul_mul_mul_star,
    trace_mul_mul_star, trace_pauli_mul_pauli] at h
  simpa using h.symm

/-- Conjugation by a unitary matrix preserves the cross product of Pauli coordinates. -/
theorem pauliRotation_mulVec_cross (x y : Fin 3 → ℝ) :
    pauliRotation U *ᵥ (x ⨯₃ y) = (pauliRotation U *ᵥ x) ⨯₃ (pauliRotation U *ᵥ y) := by
  refine pauli_injective (smul_right_injective _ (mul_ne_zero two_ne_zero I_ne_zero) ?_)
  simp only [← pauli_mul_sub_mul_pauli, pauli_pauliRotation_mulVec]
  rw [← mul_mul_mul_star, ← mul_mul_mul_star, ← sub_mul, ← mul_sub, pauli_mul_sub_mul_pauli]
  simp

/-- `pauliRotation U` is an orthogonal matrix. -/
theorem pauliRotation_mem_orthogonalGroup : pauliRotation U ∈ orthogonalGroup (Fin 3) ℝ :=
  mem_orthogonalGroup_iff_dotProduct_mulVec.mpr (dotProduct_pauliRotation_mulVec U)

/-- `pauliRotation U` has determinant one, since it is orthogonal and preserves the cross
product. -/
theorem det_pauliRotation : (pauliRotation U).det = 1 :=
  Matrix.det_eq_one_of_mulVec_cross
    (UnitaryGroup.det_isUnit ⟨_, pauliRotation_mem_orthogonalGroup U⟩)
    (pauliRotation_mulVec_cross U)

/-- `pauliRotation U` is a rotation. -/
theorem pauliRotation_mem_specialOrthogonalGroup :
    pauliRotation U ∈ specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨pauliRotation_mem_orthogonalGroup U, det_pauliRotation U⟩

/-- The group homomorphism `U(2) →* SO(3)` through which a unitary `2 × 2` matrix acts on `ℝ³` by
conjugation of traceless Hermitian matrices. -/
noncomputable def pauliRotationHom :
    Matrix.unitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ where
  toFun U := ⟨pauliRotation U, pauliRotation_mem_specialOrthogonalGroup U⟩
  map_one' := Subtype.ext pauliRotation_one
  map_mul' U V := Subtype.ext (pauliRotation_mul U V)

/-- The matrix of `pauliRotationHom U` is `pauliRotation U`. -/
@[simp]
theorem coe_pauliRotationHom :
    (pauliRotationHom U : Matrix (Fin 3) (Fin 3) ℝ) = pauliRotation U :=
  (rfl)

/-! ### The image of the north pole -/

/-- For a unitary matrix `A`, conjugating `σ₃` by `A` gives `2 u u* - 1`, where `u` is the first
column of `A`. -/
private theorem mul_pauli_single_two_mul_star {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A * star A = 1) :
    (A * pauli (Pi.single 2 1) * star A) 1 0 = 2 * (A 1 0 * conj (A 0 0)) ∧
      (A * pauli (Pi.single 2 1) * star A) 0 0 = 2 * (A 0 0 * conj (A 0 0)) - 1 := by
  have h00 := Matrix.ext_iff.mpr hA 0 0
  have h10 := Matrix.ext_iff.mpr hA 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h10
  simp only [Matrix.mul_apply, Fin.sum_univ_two, pauli_apply]
  simp only [star_apply, RCLike.star_def, one_apply_eq, one_apply_ne one_ne_zero] at h00 h10
  constructor
  · simp
    linear_combination -h10
  · simp
    linear_combination -h00

/-- The rotation `pauliRotation U` moves the north pole `(0, 0, 1)` to the point of the unit
sphere attached by the Pauli map to the first column `u` of `U`, namely
`(2 Re (u₁ conj u₀), 2 Im (u₁ conj u₀), 2 |u₀|² - 1)`. -/
theorem pauliRotation_mulVec_single_two :
    pauliRotation U *ᵥ Pi.single 2 1 =
      ![2 * ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * conj ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0)).re,
        2 * ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * conj ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0)).im,
        2 * normSq ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) - 1] := by
  obtain ⟨h10, h00⟩ := mul_pauli_single_two_mul_star (mem_unitaryGroup_iff.mp U.2)
  rw [pauliRotation_mulVec, pauliCoord_apply, h10, h00, mul_conj]
  ext i
  fin_cases i <;> simp

/-! ### The kernel -/

/-- A `2 × 2` matrix commuting with `σ₃` and `σ₁` is scalar. -/
private theorem eq_smul_one_of_commute_pauli {A : Matrix (Fin 2) (Fin 2) ℂ}
    (h3 : A * pauli (Pi.single 2 1) = pauli (Pi.single 2 1) * A)
    (h1 : A * pauli (Pi.single 0 1) = pauli (Pi.single 0 1) * A) : A = A 0 0 • 1 := by
  have h01 : -A 0 1 = A 0 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, pauli_apply] using Matrix.ext_iff.mpr h3 0 1
  have h10 : A 1 0 = -A 1 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, pauli_apply] using Matrix.ext_iff.mpr h3 1 0
  have h11 : A 0 0 = A 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, pauli_apply] using Matrix.ext_iff.mpr h1 0 1
  have h01' : A 0 1 = 0 := by linear_combination -h01 / 2
  have h10' : A 1 0 = 0 := by linear_combination h10 / 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01', h10', h11]

/-- `pauliRotation U` is the identity exactly when `U` is a scalar matrix: the kernel of
`U(2) → SO(3)` is the center of `U(2)`. -/
theorem pauliRotation_eq_one_iff :
    pauliRotation U = 1 ↔ ∃ c : ℂ, (U : Matrix (Fin 2) (Fin 2) ℂ) = c • 1 := by
  have hU := mem_unitaryGroup_iff'.mp U.2
  constructor
  · intro h
    -- `U` commutes with every `pauli x`.
    have hcomm : ∀ x, (U : Matrix (Fin 2) (Fin 2) ℂ) * pauli x =
        pauli x * (U : Matrix (Fin 2) (Fin 2) ℂ) := fun x => by
      have hx := (pauliRotation_eq_iff U).mp h x
      rw [one_mulVec] at hx
      conv_rhs => rw [hx]
      rw [mul_assoc, hU, mul_one]
    exact ⟨_, eq_smul_one_of_commute_pauli (hcomm _) (hcomm _)⟩
  · rintro ⟨c, hc⟩
    refine (pauliRotation_eq_iff U).mpr fun x => ?_
    have hcc : conj c * c = 1 := by
      have := Matrix.ext_iff.mpr (mem_unitaryGroup_iff.mp U.2) 0 0
      rw [hc] at this
      simpa [mul_comm] using this
    simp [hc, smul_smul, hcc]

/-! ### The double cover `SU(2) → SO(3)` -/

namespace SU2

/-- The **double cover** `SU(2) →* SO(3)`: an element of `SU(2)` acts on `ℝ³` by conjugation of
traceless Hermitian matrices through the Pauli map. It is surjective
(`TauCeti.SU2.toSO3_surjective`) with kernel `{1, -1}` (`TauCeti.SU2.toSO3_eq_one_iff`). -/
noncomputable def toSO3 : SU2 →* specialOrthogonalGroup (Fin 3) ℝ :=
  pauliRotationHom.comp (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

/-- The matrix of `toSO3 g` is `pauliRotation g`. -/
@[simp]
theorem coe_toSO3 (g : SU2) :
    (toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) =
      pauliRotation (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup g) :=
  (rfl)

/-- The kernel of `SU(2) → SO(3)` is `{1, -1}`. -/
theorem toSO3_eq_one_iff (g : SU2) :
    toSO3 g = 1 ↔ (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (g : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  rw [← Subtype.coe_inj, coe_toSO3, OneMemClass.coe_one, pauliRotation_eq_one_iff]
  simp only [Submonoid.coe_inclusion]
  constructor
  · rintro ⟨c, hc⟩
    have hdet := (mem_specialUnitaryGroup_iff.mp g.2).2
    rw [hc, det_smul, Fintype.card_fin, det_one, mul_one] at hdet
    rcases sq_eq_one_iff.mp hdet with rfl | rfl
    · exact Or.inl (by rw [hc, one_smul])
    · exact Or.inr (by rw [hc, neg_one_smul])
  · rintro (h | h)
    · exact ⟨1, by rw [h, one_smul]⟩
    · exact ⟨-1, by rw [h, neg_one_smul]⟩

/-- `i σ(x)` lies in `SU(2)` for a unit vector `x`. -/
private theorem smul_pauli_mem_specialUnitaryGroup {x : Fin 3 → ℝ} (hx : x ⬝ᵥ x = 1) :
    I • pauli x ∈ specialUnitaryGroup (Fin 2) ℂ := by
  refine mem_specialUnitaryGroup_iff.mpr ⟨mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · rw [star_smul, star_eq_conjTranspose, (isHermitian_pauli x).eq, smul_mul_smul_comm,
      pauli_mul_self, hx]
    simp
  · simp [det_pauli, hx]

/-- The kernel of `SU(2) → SO(3)` is the center of `SU(2)`. -/
theorem ker_toSO3 : toSO3.ker = Subgroup.center SU2 := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hg h
    rcases (toSO3_eq_one_iff g).mp hg with hg | hg <;> exact Subtype.ext (by simp [hg])
  · intro hg
    rw [← Subtype.coe_inj, coe_toSO3, OneMemClass.coe_one, pauliRotation_eq_one_iff,
      Submonoid.coe_inclusion]
    -- `g` commutes with `i σ₃` and `i σ₁`, hence with `σ₃` and `σ₁`.
    have hcomm (k : Fin 3) : (g : Matrix (Fin 2) (Fin 2) ℂ) * pauli (Pi.single k 1) =
        pauli (Pi.single k 1) * g := by
      have h := congrArg Subtype.val
        (hg ⟨_, smul_pauli_mem_specialUnitaryGroup (x := Pi.single k 1) (by simp)⟩)
      rw [Submonoid.coe_mul, Submonoid.coe_mul, smul_mul_assoc, mul_smul_comm] at h
      exact (smul_right_injective _ I_ne_zero h).symm
    exact ⟨_, eq_smul_one_of_commute_pauli (hcomm 2) (hcomm 0)⟩

/-- Conjugation by the torus element `diag (z, z⁻¹)` acts on `ℝ³` by the rotation about the axis
`(0, 0, 1)` by the angle `-2 arg z`. -/
private theorem pauliCoord_torusMatrix_mul_pauli_mul_star (z : Circle) (x : Fin 3 → ℝ) :
    pauliCoord (torusMatrix z * pauli x * star (torusMatrix z)) =
      !![((z : ℂ) ^ 2).re, ((z : ℂ) ^ 2).im, 0; -((z : ℂ) ^ 2).im, ((z : ℂ) ^ 2).re, 0;
        0, 0, 1] *ᵥ x := by
  have hre : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa [normSq_apply, sq] using Circle.normSq_coe z
  simp only [pauliCoord_apply, Matrix.mul_apply, Fin.sum_univ_two, star_apply, pauli_apply]
  ext i
  fin_cases i
  · simp [mulVec, dotProduct, Fin.sum_univ_three, sq]
    ring
  · simp [mulVec, dotProduct, Fin.sum_univ_three, sq]
    ring
  · simp [mulVec, dotProduct, Fin.sum_univ_three, sq]
    linear_combination x 2 * hre

/-- The rotation attached to the torus element `diag (z, z⁻¹)`: the rotation about the axis
`(0, 0, 1)` by the angle `-2 arg z`. -/
theorem coe_toSO3_torusHom (z : Circle) :
    (toSO3 (torusHom z) : Matrix (Fin 3) (Fin 3) ℝ) =
      !![((z : ℂ) ^ 2).re, ((z : ℂ) ^ 2).im, 0; -((z : ℂ) ^ 2).im, ((z : ℂ) ^ 2).re, 0;
        0, 0, 1] := by
  refine ext_iff_mulVec.mpr fun x => ?_
  rw [coe_toSO3, pauliRotation_mulVec, Submonoid.coe_inclusion, coe_torusHom,
    pauliCoord_torusMatrix_mul_pauli_mul_star]

/-- The fixed rotation of coordinates `x ↦ (x₁, -x₂, -x₀)` carrying the Pauli coordinates to the
coordinates of `TauCeti.realCliffordThreeZeroPureQuaternionEquiv`. -/
private def pauliQuaternionFrame : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 0, 0, -1; -1, 0, 0]

private theorem pauliQuaternionFrame_mem_specialOrthogonalGroup :
    pauliQuaternionFrame ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  refine ⟨(mem_orthogonalGroup_iff' _ _).mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliQuaternionFrame, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [pauliQuaternionFrame, det_fin_three]

/-- Up to the factor `-i` and the rotation of coordinates `pauliQuaternionFrame`, the Pauli map is
the matrix of the pure quaternion attached to a vector by
`TauCeti.realCliffordThreeZeroPureQuaternionEquiv`. -/
private theorem pauli_eq_smul_toComplexMatrix (x : Fin 3 → ℝ) :
    pauli x = (-I) • Quaternion.toComplexMatrix
      (realCliffordThreeZeroPureQuaternionEquiv (pauliQuaternionFrame *ᵥ x) : ℍ[ℝ]) := by
  rw [coe_realCliffordThreeZeroPureQuaternionEquiv_apply, Quaternion.toComplexMatrix_apply,
    pauli_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [pauliQuaternionFrame, mulVec, dotProduct, Fin.sum_univ_three]

/-- The double cover `SU(2) → SO(3)` is surjective. Through `pauli_eq_smul_toComplexMatrix` it is
the vector action of `Spin(3) ≅ SU(2)` (`TauCeti.realSpinThreeEquivSpecialUnitary_action`), which
is onto `SO(3)` (`CliffordAlgebra.spinToSpecialOrthogonal_surjective_of_posDef`). -/
theorem toSO3_surjective : Function.Surjective toSO3 := by
  intro S
  let F : specialOrthogonalGroup (Fin 3) ℝ :=
    ⟨pauliQuaternionFrame, pauliQuaternionFrame_mem_specialOrthogonalGroup⟩
  -- The rotation `F S F⁻¹` of the pure-quaternion coordinates is the action of a Spin element.
  let T := QuadraticMap.matrixSpecialOrthogonalEquivWeightedSumSquaresOne (Fin 3) (F * S * F⁻¹)
  have hT : (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) ∈
      QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0) := by
    rw [realCliffordForm_zero_eq_weightedSumSquares_one]
    exact T.2
  obtain ⟨s, hs⟩ := CliffordAlgebra.spinToSpecialOrthogonal_surjective_of_posDef _
    (posDef_realCliffordForm_zero 3) ⟨_, hT⟩
  have hsx (x : Fin 3 → ℝ) :
      s • (pauliQuaternionFrame *ᵥ x) = pauliQuaternionFrame *ᵥ (S *ᵥ x) := by
    rw [CliffordAlgebra.spinGroup_smul_apply,
      ← CliffordAlgebra.coe_spinToSpecialOrthogonal_apply, hs]
    -- By definition `⟨_, hT⟩` coerces to `T`, and the matrix of the `let`-bound `F` is
    -- `pauliQuaternionFrame`.
    change (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) ((F : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) = _
    rw [QuadraticMap.matrixSpecialOrthogonalEquivWeightedSumSquaresOne_apply, toLin'_apply,
      mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel_right, Submonoid.coe_mul, ← mulVec_mulVec]
  refine ⟨realSpinThreeEquivSpecialUnitary s,
    Subtype.ext ((pauliRotation_eq_iff _).mpr fun x => ?_)⟩
  rw [Submonoid.coe_inclusion, pauli_eq_smul_toComplexMatrix, pauli_eq_smul_toComplexMatrix,
    ← hsx, realSpinThreeEquivSpecialUnitary_action, mul_smul_comm, smul_mul_assoc]

/-- The double cover `SU(2) → SO(3)` is continuous. -/
theorem continuous_toSO3 : Continuous toSO3 := by
  refine continuous_induced_rng.mpr (continuous_pi fun i => continuous_pi fun j => ?_)
  have h (g : SU2) : (toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) i j = pauliCoord
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * pauli (Pi.single j 1) *
        star (g : Matrix (Fin 2) (Fin 2) ℂ)) i := by
    rw [coe_toSO3]
    exact congrFun ((mulVec_single_one _ j).symm.trans (pauliRotation_mulVec _ _)) i
  have hc : Continuous fun g : SU2 => (g : Matrix (Fin 2) (Fin 2) ℂ) * pauli (Pi.single j 1) *
      star (g : Matrix (Fin 2) (Fin 2) ℂ) :=
    (continuous_subtype_val.mul continuous_const).mul continuous_subtype_val.star
  simp only [Function.comp_def, h]
  exact (continuous_apply i).comp ((LinearMap.continuous_of_finiteDimensional pauliCoord).comp hc)

/-- The double cover induces an isomorphism of topological groups `SU(2) ⧸ {±1} ≃ₜ* SO(3)`:
`SU(2)` is compact and `SO(3)` is Hausdorff. The kernel `toSO3.ker` is `{1, -1}`
(`TauCeti.SU2.toSO3_eq_one_iff`), the center of `SU(2)` (`TauCeti.SU2.ker_toSO3`). -/
noncomputable def quotientKerToSO3 : SU2 ⧸ toSO3.ker ≃ₜ* specialOrthogonalGroup (Fin 3) ℝ :=
  ContinuousMonoidHom.quotientKerEquivOfSurjective ⟨toSO3, continuous_toSO3⟩ toSO3_surjective

/-- The isomorphism `SU(2) ⧸ {±1} ≃ₜ* SO(3)` sends the class of `g` to `toSO3 g`. -/
@[simp]
theorem quotientKerToSO3_mk (g : SU2) : quotientKerToSO3 (g : SU2 ⧸ toSO3.ker) = toSO3 g :=
  ContinuousMonoidHom.quotientKerEquivOfSurjective_apply_mk ⟨toSO3, continuous_toSO3⟩
    toSO3_surjective g

/-- The Pauli-map homomorphism from `SU(2)` onto `SO(3)` is a covering map. -/
theorem isCoveringMap_toSO3 : IsCoveringMap toSO3 := by
  have hfinite : (toSO3.ker : Set SU2).Finite := by
    have h := (Set.toFinite ({1, -1} : Set (Matrix (Fin 2) (Fin 2) ℂ))).preimage
      (f := fun g : SU2 ↦ (g : Matrix (Fin 2) (Fin 2) ℂ)) Subtype.val_injective.injOn
    refine h.subset fun g hg ↦ ?_
    simpa only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] using
      (toSO3_eq_one_iff g).mp (MonoidHom.mem_ker.mp hg)
  have hquot : Topology.IsQuotientMap toSO3 :=
    Topology.IsQuotientMap.of_surjective_continuous toSO3_surjective continuous_toSO3
  exact (hquot.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom hfinite.isDiscrete).isCoveringMap

end SU2

end TauCeti
