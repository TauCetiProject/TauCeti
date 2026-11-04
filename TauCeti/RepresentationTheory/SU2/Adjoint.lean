/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Pauli
public import TauCeti.RepresentationTheory.SU2.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
import TauCeti.LinearAlgebra.Matrix.CrossProduct
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

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

Restricted to `SU(2)` the homomorphism is the **double cover** `TauCeti.SU2.toSO3`. It is
surjective (`TauCeti.SU2.toSO3_surjective`): the formula above reaches every point of the sphere,
and a rotation fixing the north pole is the image of a diagonal element `diag (z, z⁻¹)` of the
maximal torus. Its kernel is `{1, -1}` (`TauCeti.SU2.toSO3_eq_one_iff`), and since `SU(2)` is
compact and `SO(3)` is Hausdorff, it induces an isomorphism of topological groups
`SU(2) ⧸ {±1} ≃ₜ* SO(3)` (`TauCeti.SU2.quotientKerToSO3`).

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
* `TauCeti.SU2.coe_toSO3_torusHom`: the maximal torus `diag (z, z⁻¹)` maps to the rotations about
  the axis `(0, 0, 1)`.
* `TauCeti.SU2.toSO3_surjective`: `SU(2) → SO(3)` is surjective.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics
  129, Springer, 1991, §7.3 and §10.1.
* J. Stillwell, *Naive Lie Theory*, Undergraduate Texts in Mathematics, Springer, 2008, §1.5
  and §2.3.
-/

public section

open Matrix Complex
open scoped ComplexConjugate

namespace TauCeti

variable (U V : Matrix.unitaryGroup (Fin 2) ℂ)

/-! ### Conjugation of traceless Hermitian matrices -/

/-- Conjugating `pauli x` by a unitary matrix gives a Hermitian matrix. -/
private theorem isHermitian_mul_pauli_mul_star (x : Fin 3 → ℝ) :
    ((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli x * star (U : Matrix (Fin 2) (Fin 2) ℂ)).IsHermitian :=
  isHermitian_mul_mul_conjTranspose _ (isHermitian_pauli x)

/-- Conjugating `pauli x` by a unitary matrix gives a traceless matrix. -/
private theorem trace_mul_pauli_mul_star (x : Fin 3 → ℝ) :
    ((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli x * star (U : Matrix (Fin 2) (Fin 2) ℂ)).trace = 0 := by
  rw [trace_mul_cycle, mem_unitaryGroup_iff'.mp U.2, one_mul, trace_pauli]

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

/-- Conjugation by a unitary matrix preserves the dot product of Pauli coordinates. -/
theorem dotProduct_pauliRotation_mulVec (x y : Fin 3 → ℝ) :
    (pauliRotation U *ᵥ x) ⬝ᵥ (pauliRotation U *ᵥ y) = x ⬝ᵥ y := by
  have h := trace_pauli_mul_pauli (pauliRotation U *ᵥ x) (pauliRotation U *ᵥ y)
  rw [pauli_pauliRotation_mulVec, pauli_pauliRotation_mulVec] at h
  have hU := mem_unitaryGroup_iff'.mp U.2
  rw [show (U : Matrix (Fin 2) (Fin 2) ℂ) * pauli x * star (U : Matrix (Fin 2) (Fin 2) ℂ) *
      ((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli y * star (U : Matrix (Fin 2) (Fin 2) ℂ)) =
      (U : Matrix (Fin 2) (Fin 2) ℂ) * (pauli x * pauli y) *
        star (U : Matrix (Fin 2) (Fin 2) ℂ) by
      simp only [mul_assoc, ← mul_assoc (star _) (U : Matrix (Fin 2) (Fin 2) ℂ), hU, one_mul],
    trace_mul_cycle, hU, one_mul, trace_pauli_mul_pauli] at h
  exact_mod_cast (mul_left_cancel₀ two_ne_zero h).symm

/-- Conjugation by a unitary matrix preserves the cross product of Pauli coordinates. -/
theorem pauliRotation_mulVec_cross (x y : Fin 3 → ℝ) :
    pauliRotation U *ᵥ (x ⨯₃ y) = (pauliRotation U *ᵥ x) ⨯₃ (pauliRotation U *ᵥ y) := by
  refine pauli_injective (smul_right_injective _ (mul_ne_zero two_ne_zero I_ne_zero) ?_)
  have hU := mem_unitaryGroup_iff'.mp U.2
  dsimp only
  rw [← pauli_mul_sub_mul_pauli, pauli_pauliRotation_mulVec, pauli_pauliRotation_mulVec,
    pauli_pauliRotation_mulVec, ← smul_mul_assoc, ← mul_smul_comm, ← pauli_mul_sub_mul_pauli,
    mul_sub, sub_mul]
  simp only [mul_assoc, ← mul_assoc (star _) (U : Matrix (Fin 2) (Fin 2) ℂ), hU, one_mul]

/-- `pauliRotation U` is an orthogonal matrix. -/
theorem pauliRotation_mem_orthogonalGroup : pauliRotation U ∈ orthogonalGroup (Fin 3) ℝ :=
  mem_orthogonalGroup_iff_dotProduct_mulVec.mpr (dotProduct_pauliRotation_mulVec U)

/-- `pauliRotation U` has determinant one, since it preserves the cross product. -/
theorem det_pauliRotation : (pauliRotation U).det = 1 :=
  Matrix.det_eq_one_of_mulVec_cross (dotProduct_pauliRotation_mulVec U)
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
  refine ⟨?_, ?_⟩
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
  have h01 := Matrix.ext_iff.mpr h3 0 1
  have h10 := Matrix.ext_iff.mpr h3 1 0
  have h11 := Matrix.ext_iff.mpr h1 0 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, pauli_apply] at h01 h10 h11
  simp at h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination -h01 / 2
  · linear_combination h10 / 2
  · linear_combination -h11

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
    have hcc : star c * c = 1 := by
      have := Matrix.ext_iff.mpr (mem_unitaryGroup_iff.mp U.2) 0 0
      rw [hc] at this
      simpa [mul_comm] using this
    rw [one_mulVec, hc, star_smul, star_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
      smul_smul, hcc, one_smul]

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

/-- The element of `SU(2)` with first column `(a, b)`, for `|a|² + |b|² = 1`. -/
private noncomputable def ofColumn (a b : ℂ) (h : normSq a + normSq b = 1) : SU2 :=
  ⟨!![a, -conj b; b, conj a], by
    have h' : a * conj a + b * conj b = 1 := by
      rw [mul_conj, mul_conj]
      exact_mod_cast h
    refine mem_specialUnitaryGroup_iff.mpr ⟨mem_unitaryGroup_iff.mpr ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination h'
      · ring
      · ring
      · linear_combination h'
    · rw [det_fin_two_of]
      linear_combination h'⟩

private theorem coe_ofColumn_apply_zero_zero (a b : ℂ) (h : normSq a + normSq b = 1) :
    (ofColumn a b h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = a :=
  (rfl)

private theorem coe_ofColumn_apply_one_zero (a b : ℂ) (h : normSq a + normSq b = 1) :
    (ofColumn a b h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = b :=
  (rfl)

/-- Every point of the unit sphere is the image of the north pole under some rotation coming
from `SU(2)`. -/
private theorem exists_toSO3_mulVec_single_two (n : Fin 3 → ℝ) (hn : n ⬝ᵥ n = 1) :
    ∃ g : SU2, (toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ Pi.single 2 1 = n := by
  simp only [dotProduct, Fin.sum_univ_three] at hn
  have hn2 : -1 ≤ n 2 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
  rcases hn2.eq_or_lt with h2 | h2
  · -- The south pole is the image of `!![0, -1; 1, 0]`.
    have h0 : n 0 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
    have h1 : n 1 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
    refine ⟨ofColumn 0 1 (by simp), ?_⟩
    rw [coe_toSO3, pauliRotation_mulVec_single_two]
    ext i
    fin_cases i <;> simp [Submonoid.coe_inclusion, coe_ofColumn_apply_zero_zero,
      coe_ofColumn_apply_one_zero, h0, h1, ← h2]
  · -- Otherwise take `a = √((1 + n₂) / 2) > 0` and `b = (n₀ + i n₁) / (2 a)`.
    set a : ℝ := √((1 + n 2) / 2)
    have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have ha2 : a ^ 2 = (1 + n 2) / 2 := Real.sq_sqrt (by linarith)
    set b : ℂ := (n 0 + n 1 * I) / (2 * a)
    have hb : normSq b = (n 0 ^ 2 + n 1 ^ 2) / (4 * a ^ 2) := by
      simp only [b, normSq_div, normSq_add_mul_I]
      rw [show (2 * (a : ℂ)) = ((2 * a : ℝ) : ℂ) by push_cast; ring, normSq_ofReal]
      ring
    have hab : normSq (a : ℂ) + normSq b = 1 := by
      rw [normSq_ofReal, hb]
      field_simp
      nlinarith
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hba : b * a = (n 0 + n 1 * I) / 2 := by
      simp only [b]
      field_simp
    refine ⟨ofColumn a b hab, ?_⟩
    rw [coe_toSO3, pauliRotation_mulVec_single_two]
    simp only [Submonoid.coe_inclusion, coe_ofColumn_apply_zero_zero, coe_ofColumn_apply_one_zero,
      conj_ofReal, normSq_ofReal, hba]
    ext i
    fin_cases i
    · simp
      ring
    · simp
      ring
    · simp
      nlinarith

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

/-- An orthogonal matrix of determinant one fixing `(0, 0, 1)` is a rotation about that axis. -/
private theorem eq_of_mulVec_single_two {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * T = 1)
    (hdet : T.det = 1) (hS : T *ᵥ Pi.single 2 1 = Pi.single 2 1) :
    T = !![T 0 0, -T 1 0, 0; T 1 0, T 0 0, 0; 0, 0, 1] ∧ T 0 0 ^ 2 + T 1 0 ^ 2 = 1 := by
  have hcol := congrFun hS
  simp only [mulVec_single_one] at hcol
  have h02 : T 0 2 = 0 := by simpa using hcol 0
  have h12 : T 1 2 = 0 := by simpa using hcol 1
  have h22 : T 2 2 = 1 := by simpa using hcol 2
  have hTT := Matrix.ext_iff.mpr hT
  have e20 := hTT 2 0
  have e21 := hTT 2 1
  have e00 := hTT 0 0
  have e11 := hTT 1 1
  have e01 := hTT 0 1
  simp only [Matrix.mul_apply, Fin.sum_univ_three, transpose_apply, h02, h12, h22, one_apply_eq,
    one_apply_ne, ne_eq, Fin.reduceEq, not_false_eq_true, zero_mul, one_mul, zero_add,
    Fin.isValue] at e20 e21 e00 e11 e01
  rw [det_fin_three, h02, h12, h22, e20, e21] at hdet
  simp only [mul_one, mul_zero, sub_zero, zero_mul, add_zero] at hdet
  -- The upper-left block is a rotation of the plane: `(T₀₀ - T₁₁)² + (T₀₁ + T₁₀)² = 0`.
  have h11 : T 1 1 = T 0 0 := by
    nlinarith [sq_nonneg (T 0 0 - T 1 1), sq_nonneg (T 0 1 + T 1 0)]
  have h01 : T 0 1 = -T 1 0 := by
    nlinarith [sq_nonneg (T 0 0 - T 1 1), sq_nonneg (T 0 1 + T 1 0)]
  refine ⟨Matrix.ext fun i j => ?_, by nlinarith⟩
  fin_cases i <;> fin_cases j <;> simp [h02, h12, h22, e20, e21, h11, h01]

/-- The rotation attached to the torus element `diag (z, z⁻¹)`: the rotation about the axis
`(0, 0, 1)` by the angle `-2 arg z`. -/
theorem coe_toSO3_torusHom (z : Circle) :
    (toSO3 (torusHom z) : Matrix (Fin 3) (Fin 3) ℝ) =
      !![((z : ℂ) ^ 2).re, ((z : ℂ) ^ 2).im, 0; -((z : ℂ) ^ 2).im, ((z : ℂ) ^ 2).re, 0;
        0, 0, 1] := by
  refine ext_iff_mulVec.mpr fun x => ?_
  rw [coe_toSO3, pauliRotation_mulVec, Submonoid.coe_inclusion, coe_torusHom,
    pauliCoord_torusMatrix_mul_pauli_mul_star]

/-- A rotation fixing `(0, 0, 1)` is the image of an element of the maximal torus. -/
private theorem exists_coe_toSO3_torusHom_eq {T : Matrix (Fin 3) (Fin 3) ℝ} (hTo : Tᵀ * T = 1)
    (hTd : T.det = 1) (hS : T *ᵥ Pi.single 2 1 = Pi.single 2 1) :
    ∃ z : Circle, (toSO3 (torusHom z) : Matrix (Fin 3) (Fin 3) ℝ) = T := by
  obtain ⟨hT, hT2⟩ := eq_of_mulVec_single_two hTo hTd hS
  -- Choose `z` on the circle with `z² = T₀₀ - i T₁₀`.
  set w : ℂ := T 0 0 - T 1 0 * I with hw_def
  have hw : ‖w‖ = 1 := by
    have hn : normSq w = 1 := by
      rw [hw_def, show (T 0 0 : ℂ) - T 1 0 * I = (T 0 0 : ℂ) + ((-T 1 0 : ℝ) : ℂ) * I by
        push_cast; ring, normSq_add_mul_I, neg_sq, hT2]
    rw [Complex.norm_def, hn, Real.sqrt_one]
  -- Take `z = exp (i arg w / 2)`.
  have hz : ((Circle.exp (arg w / 2) : ℂ)) ^ 2 = w := by
    rw [Circle.coe_exp, ← Complex.exp_nat_mul]
    have h := norm_mul_exp_arg_mul_I w
    rw [hw, ofReal_one, one_mul] at h
    convert h using 2
    push_cast
    ring
  refine ⟨Circle.exp (arg w / 2), ?_⟩
  rw [coe_toSO3_torusHom, hz]
  conv_rhs => rw [hT]
  simp [w]

/-- The double cover `SU(2) → SO(3)` is surjective. -/
theorem toSO3_surjective : Function.Surjective toSO3 := by
  intro S
  set n := (S : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ Pi.single 2 1 with hn_def
  have hn : n ⬝ᵥ n = 1 := by
    have := Matrix.ext_iff.mpr ((mem_orthogonalGroup_iff' _ _).mp S.2.1) 2 2
    simpa [n, mulVec_single_one, dotProduct, Matrix.mul_apply, Fin.sum_univ_three, sq] using this
  obtain ⟨g, hg⟩ := exists_toSO3_mulVec_single_two n hn
  obtain ⟨z, hz⟩ := exists_coe_toSO3_torusHom_eq
    ((mem_orthogonalGroup_iff' _ _).mp ((toSO3 g)⁻¹ * S).2.1) ((toSO3 g)⁻¹ * S).2.2 (by
    rw [← map_inv, Submonoid.coe_mul, ← mulVec_mulVec,
      ← hn_def, ← hg, mulVec_mulVec,
      ← Submonoid.coe_mul, ← map_mul, inv_mul_cancel, map_one, OneMemClass.coe_one, one_mulVec])
  exact ⟨g * torusHom z, by rw [map_mul, Subtype.ext hz, mul_inv_cancel_left]⟩

/-- The double cover `SU(2) → SO(3)` is continuous. -/
theorem continuous_toSO3 : Continuous toSO3 := by
  refine continuous_induced_rng.mpr (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [Function.comp_def, coe_toSO3, pauliRotation, LinearMap.toMatrix'_apply,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    Submonoid.coe_inclusion]
  have hc : Continuous fun g : SU2 => (g : Matrix (Fin 2) (Fin 2) ℂ) *
      (pauli (Pi.single j 1) * star (g : Matrix (Fin 2) (Fin 2) ℂ)) :=
    continuous_subtype_val.mul (continuous_const.mul continuous_subtype_val.star)
  exact (continuous_apply i).comp ((LinearMap.continuous_of_finiteDimensional pauliCoord).comp hc)

/-- The double cover induces an isomorphism of topological groups `SU(2) ⧸ {±1} ≃ₜ* SO(3)`:
`SU(2)` is compact and `SO(3)` is Hausdorff. -/
noncomputable def quotientKerToSO3 : SU2 ⧸ toSO3.ker ≃ₜ* specialOrthogonalGroup (Fin 3) ℝ :=
  let e := QuotientGroup.quotientKerEquivOfSurjective toSO3 toSO3_surjective
  have hc : Continuous e :=
    (QuotientGroup.isQuotientMap_mk toSO3.ker).continuous_iff.mpr continuous_toSO3
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

/-- The isomorphism `SU(2) ⧸ {±1} ≃ₜ* SO(3)` sends the class of `g` to `toSO3 g`. -/
@[simp]
theorem quotientKerToSO3_mk (g : SU2) : quotientKerToSO3 (g : SU2 ⧸ toSO3.ker) = toSO3 g :=
  (rfl)

end SU2

end TauCeti
