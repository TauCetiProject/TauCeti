/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Mathlib.Algebra.QuaternionBasis` is imported publicly for `QuaternionAlgebra.Basis` and its
-- `liftHom`, the universal property used to build the embedding below, and it re-exports
-- `Mathlib.Algebra.Quaternion`, hence `ℍ[ℝ]`, `Quaternion.normSq` and quaternion conjugation.
public import Mathlib.Algebra.QuaternionBasis
-- `Mathlib.Analysis.Quaternion` is imported publicly for the `DivisionRing ℍ[ℝ]` structure and
-- `Quaternion.normSq_eq_zero`, which occur in the statements and proofs below.
public import Mathlib.Analysis.Quaternion
public import Mathlib.Algebra.Star.StarAlgHom
-- `Mathlib.LinearAlgebra.UnitaryGroup` is imported publicly for `Matrix.unitaryGroup`,
-- `Matrix.specialUnitaryGroup` and the `StarRing (Matrix n n ℂ)` instance.
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import TauCeti.Algebra.Quaternion.NormForm
-- `TauCeti.LinearAlgebra.UnitaryGroup` supplies `Matrix.specialUnitaryGroup.star_eq_adjugate`,
-- which turns the unitarity of a special unitary matrix into four entry identities.
public import TauCeti.LinearAlgebra.UnitaryGroup
-- `TauCeti.Analysis.Matrix.UnitaryGroup.Basic` supplies `Circle.coe_mem_unitary` and the
-- decomposition `U(n) = Circle · SU(n)` used for `U(2)` below.
public import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
import TauCeti.Analysis.Complex.Circle

/-!
# The real quaternions as two-by-two complex matrices, `SU(2)` and `U(2)`

The real quaternion algebra `ℍ[ℝ]` is a four-dimensional real form of the eight-dimensional real
algebra `M₂(ℂ)`. This file builds the embedding realizing it, as a homomorphism of `ℝ`-algebras
compatible with the two conjugations:

```text
Quaternion.toComplexMatrix : ℍ[ℝ] →⋆ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ
```

sending the quaternion units to

```text
i ↦ !![I, 0; 0, -I],    j ↦ !![0, 1; -1, 0],    k ↦ !![0, I; I, 0],
```

so that a general quaternion goes to

```text
a + b i + c j + d k  ↦  !![a + b I, c + d I; -c + d I, a - b I].
```

Three facts make the embedding useful. Its determinant is the reduced norm
(`Quaternion.det_toComplexMatrix`); it carries quaternion conjugation to the conjugate transpose,
which is what makes it a `StarAlgHom` at all; and its image is cut out by two entry identities
(`Quaternion.mem_range_toComplexMatrix_iff`), so the real form is explicit. Together they identify
the unit quaternions with the special unitary group of degree two:

```text
Quaternion.unitaryEquivSpecialUnitaryGroup :
  unitary ℍ[ℝ] ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ.
```

Both inclusions are entry computations. A unit quaternion has determinant one and conjugate
transpose its own inverse, so it lands in `SU(2)`; conversely, for a special unitary matrix the
conjugate transpose *is* the adjugate (`Matrix.specialUnitaryGroup.star_eq_adjugate`), and in
degree two the adjugate swaps the diagonal and negates the off-diagonal, which is exactly the pair
of identities carving out the real form.

Multiplying by scalars of modulus one then presents the whole unitary group: the homomorphism
`Quaternion.unitaryProdCircleToUnitaryGroup : Sp(1) × U(1) → U(2)`, `(q, w) ↦ w • q`, is onto
(`U(2) = Circle · SU(2)`) with kernel `{(1, 1), (-1, -1)}`, so
`U(2) ≅ (Sp(1) × U(1)) / {±1}`.

## Main definitions

* `Quaternion.toComplexMatrix`: the `ℝ`-algebra embedding `ℍ[ℝ] →⋆ₐ[ℝ] M₂(ℂ)`.
* `Quaternion.unitaryEquivSpecialUnitaryGroup`: the unit quaternions are `SU(2)`.
* `Quaternion.ofFirstColumn`: the quaternion whose matrix has a given first column.
* `Quaternion.circleToUnitary`: the circle as the unit quaternions of the complex line.
* `Quaternion.unitaryProdCircleToUnitaryGroup`: the homomorphism `Sp(1) × U(1) → U(2)`,
  `(q, w) ↦ w • q`.

## Main results

* `Quaternion.toComplexMatrix_apply`: the entries of the embedding.
* `Quaternion.det_toComplexMatrix` and `Quaternion.trace_toComplexMatrix`: the determinant is the
  reduced norm and the trace is the reduced trace.
* `Quaternion.toComplexMatrix_injective`: the embedding is injective.
* `Quaternion.mem_range_toComplexMatrix_iff`: the image is the set of matrices whose lower row is
  determined by the upper one by `M 1 1 = star (M 0 0)` and `M 1 0 = -star (M 0 1)`.
* `Quaternion.mem_specialUnitaryGroup_toComplexMatrix` and
  `Quaternion.exists_eq_toComplexMatrix_of_mem_specialUnitaryGroup`: the two inclusions behind the
  equivalence, packaged as `Quaternion.mem_specialUnitaryGroup_iff_exists_toComplexMatrix`.
* `Quaternion.unitaryProdCircleToUnitaryGroup_surjective` and
  `Quaternion.mem_ker_unitaryProdCircleToUnitaryGroup_iff`: `Sp(1) × U(1) → U(2)` is onto with
  kernel `{1, -1}`.

## Implementation notes

This is **not** a splitting of a quaternion algebra, and it is not an instance of the splittings in
`TauCeti/Algebra/Quaternion/Split.lean` or `TauCeti/Algebra/Quaternion/SquareSplit.lean`. Those
produce algebra *equivalences* `ℍ[R,a,b] ≃ₐ[R] M₂(R)` when the symbol is split; `ℍ[ℝ]` is a
division algebra, so no such equivalence exists over `ℝ`, and the base change
`ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℂ] M₂(ℂ)` that those files do supply is a homomorphism of `ℂ`-algebras out of a
larger algebra. What is needed here is the `ℝ`-algebra embedding of `ℍ[ℝ]` itself, together with
the information that it matches quaternion conjugation with the conjugate transpose: it is the
compatibility of the two involutions, not the algebra structure alone, that sends unit quaternions
to unitary matrices. That compatibility also pins the generators down to unitary conjugacy:
conjugating the basis below by any invertible `P` leaves an algebra embedding, but the result is
a `StarAlgHom` only when `Pᴴ * P` commutes with the whole image, hence — the image spanning
`M₂(ℂ)` over `ℂ` — only when `Pᴴ * P` is a positive scalar matrix, which is to say when `P` is a
positive multiple of a unitary matrix. Such a `P` conjugates exactly as its unitary part does, so
the generators below are canonical only up to unitary conjugation, and a general conjugation need
not respect `star` at all.

`Quaternion.unitaryEquivSpecialUnitaryGroup` is stated against Mathlib's
`Matrix.specialUnitaryGroup (Fin 2) ℂ`; `TauCeti.SU2` is a reducible abbreviation for that type, so
the equivalence applies to it with no transport.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, Lecture 20, §20.1.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§3-4.
-/

public section

open scoped Matrix Quaternion

namespace Quaternion

/-! ### The embedding -/

/-- The standard quaternion basis of `M₂(ℂ)`: the complex matrices `!![I, 0; 0, -I]` and
`!![0, 1; -1, 0]`, whose product is `!![0, I; I, 0]`. -/
private noncomputable def complexMatrixBasis :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℂ) (-1 : ℝ) 0 (-1) where
  i := !![Complex.I, 0; 0, -Complex.I]
  j := !![0, 1; -1, 0]
  k := !![0, Complex.I; Complex.I, 0]
  i_mul_i := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_j := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  i_mul_j := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem complexMatrixBasis_liftHom_apply (q : ℍ[ℝ]) :
    complexMatrixBasis.liftHom q =
      !![(q.re : ℂ) + q.imI * Complex.I, (q.imJ : ℂ) + q.imK * Complex.I;
        -(q.imJ : ℂ) + q.imK * Complex.I, (q.re : ℂ) - q.imI * Complex.I] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [complexMatrixBasis, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift,
      Algebra.algebraMap_eq_smul_one, Complex.ext_iff]

private theorem complexMatrixBasis_liftHom_star (q : ℍ[ℝ]) :
    complexMatrixBasis.liftHom (star q) = star (complexMatrixBasis.liftHom q) := by
  rw [complexMatrixBasis_liftHom_apply, complexMatrixBasis_liftHom_apply]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.star_apply]

/-- **The real quaternions as two-by-two complex matrices.** The embedding of `ℝ`-algebras with
star sending the quaternion units `i`, `j`, `k` to `!![I, 0; 0, -I]`, `!![0, 1; -1, 0]` and
`!![0, I; I, 0]`. Quaternion conjugation becomes the conjugate transpose. -/
noncomputable def toComplexMatrix : ℍ[ℝ] →⋆ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  { complexMatrixBasis.liftHom with map_star' := complexMatrixBasis_liftHom_star }

/-- The entries of `Quaternion.toComplexMatrix`.

This is deliberately not a `simp` lemma: expanding a bundled algebra map into a matrix literal is
not a normal form, and it would hide the left-hand sides of `Quaternion.det_toComplexMatrix` and
`Quaternion.trace_toComplexMatrix`, which are the intended simp-normal readings of the embedding. -/
theorem toComplexMatrix_apply (q : ℍ[ℝ]) :
    toComplexMatrix q =
      !![(q.re : ℂ) + q.imI * Complex.I, (q.imJ : ℂ) + q.imK * Complex.I;
        -(q.imJ : ℂ) + q.imK * Complex.I, (q.re : ℂ) - q.imI * Complex.I] :=
  complexMatrixBasis_liftHom_apply q

/-- **The determinant of the matrix of a quaternion is its reduced norm.** -/
@[simp]
theorem det_toComplexMatrix (q : ℍ[ℝ]) :
    (toComplexMatrix q).det = ((normSq q : ℝ) : ℂ) := by
  rw [toComplexMatrix_apply, Matrix.det_fin_two_of, normSq_def']
  push_cast
  linear_combination (-((q.imI : ℂ) ^ 2 + (q.imK : ℂ) ^ 2)) * Complex.I_sq

/-- **The trace of the matrix of a quaternion is its reduced trace.** -/
@[simp]
theorem trace_toComplexMatrix (q : ℍ[ℝ]) :
    (toComplexMatrix q).trace = ((2 * q.re : ℝ) : ℂ) := by
  rw [toComplexMatrix_apply, Matrix.trace_fin_two_of]
  push_cast
  ring

/-- `Quaternion.toComplexMatrix` is injective: a quaternion whose matrix vanishes has vanishing
reduced norm. -/
theorem toComplexMatrix_injective : Function.Injective toComplexMatrix := by
  intro p q hpq
  have hdet : ((normSq (p - q) : ℝ) : ℂ) = 0 := by
    rw [← det_toComplexMatrix, map_sub, hpq, sub_self]
    simp
  rw [Complex.ofReal_eq_zero, normSq_eq_zero, sub_eq_zero] at hdet
  exact hdet

/-! ### The image is the real form -/

/-- **The image of `Quaternion.toComplexMatrix` is an explicit real form of `M₂(ℂ)`**: a complex
two-by-two matrix is the matrix of a quaternion exactly when its lower row is read off its upper
row by conjugation. -/
theorem mem_range_toComplexMatrix_iff {M : Matrix (Fin 2) (Fin 2) ℂ} :
    M ∈ Set.range toComplexMatrix ↔ M 1 1 = star (M 0 0) ∧ M 1 0 = -star (M 0 1) := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [toComplexMatrix_apply]
    refine ⟨?_, ?_⟩ <;> simp [Complex.ext_iff]
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩, ?_⟩
    rw [toComplexMatrix_apply]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [h₁, h₂, Complex.ext_iff]

/-! ### The unit quaternions are `SU(2)` -/

/-- A unit quaternion has special unitary matrix. -/
theorem mem_specialUnitaryGroup_toComplexMatrix {q : ℍ[ℝ]} (hq : q ∈ unitary ℍ[ℝ]) :
    toComplexMatrix q ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Unitary.map_mem toComplexMatrix hq, ?_⟩
  rw [det_toComplexMatrix, (mem_unitary_iff_normSq_eq_one q).mp hq, Complex.ofReal_one]

/-- **Every special unitary matrix of degree two is the matrix of a unit quaternion.** -/
theorem exists_eq_toComplexMatrix_of_mem_specialUnitaryGroup
    {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ q ∈ unitary ℍ[ℝ], toComplexMatrix q = M := by
  have hstar : star M = M.adjugate := Matrix.specialUnitaryGroup.star_eq_adjugate ⟨M, hM⟩
  rw [Matrix.adjugate_fin_two] at hstar
  have h₁ : M 1 1 = star (M 0 0) := by
    simpa using (congrFun (congrFun hstar 0) 0).symm
  have h₂ : M 1 0 = -star (M 0 1) :=
    neg_eq_iff_eq_neg.mp (by simpa using (congrFun (congrFun hstar 1) 0).symm)
  obtain ⟨q, hq⟩ := mem_range_toComplexMatrix_iff.mpr ⟨h₁, h₂⟩
  refine ⟨q, ?_, hq⟩
  rw [mem_unitary_iff_normSq_eq_one, ← Complex.ofReal_inj, Complex.ofReal_one,
    ← det_toComplexMatrix, hq]
  exact (Matrix.mem_specialUnitaryGroup_iff.mp hM).2

/-- **A complex matrix of degree two is special unitary exactly when it is the matrix of a unit
quaternion.** -/
theorem mem_specialUnitaryGroup_iff_exists_toComplexMatrix
    {M : Matrix (Fin 2) (Fin 2) ℂ} :
    M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔ ∃ q ∈ unitary ℍ[ℝ], toComplexMatrix q = M := by
  refine ⟨exists_eq_toComplexMatrix_of_mem_specialUnitaryGroup, ?_⟩
  rintro ⟨q, hq, rfl⟩
  exact mem_specialUnitaryGroup_toComplexMatrix hq

private noncomputable def unitaryToSpecialUnitaryGroup :
    unitary ℍ[ℝ] →* Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun q := ⟨toComplexMatrix (q : ℍ[ℝ]), mem_specialUnitaryGroup_toComplexMatrix q.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)

/-- **The unit quaternions are the special unitary group of degree two**: the group `Sp(1)` of unit
Hamilton quaternions is `SU(2)`, by `Quaternion.toComplexMatrix`. -/
noncomputable def unitaryEquivSpecialUnitaryGroup :
    unitary ℍ[ℝ] ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  MulEquiv.ofBijective unitaryToSpecialUnitaryGroup
    ⟨fun p q hpq => Subtype.ext (toComplexMatrix_injective (congrArg Subtype.val hpq)),
      fun M => by
        obtain ⟨q, hq, hqM⟩ := exists_eq_toComplexMatrix_of_mem_specialUnitaryGroup M.2
        exact ⟨⟨q, hq⟩, Subtype.ext hqM⟩⟩

/-- The special unitary matrix attached to a unit quaternion is its matrix under
`Quaternion.toComplexMatrix`. -/
@[simp]
theorem coe_unitaryEquivSpecialUnitaryGroup_apply (q : unitary ℍ[ℝ]) :
    (unitaryEquivSpecialUnitaryGroup q : Matrix (Fin 2) (Fin 2) ℂ) =
      toComplexMatrix (q : ℍ[ℝ]) := (rfl)

/-- The unit quaternion attached to a special unitary matrix has that matrix. -/
theorem coe_unitaryEquivSpecialUnitaryGroup_symm_apply
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    toComplexMatrix ((unitaryEquivSpecialUnitaryGroup.symm M : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      (M : Matrix (Fin 2) (Fin 2) ℂ) :=
  congrArg Subtype.val (unitaryEquivSpecialUnitaryGroup.apply_symm_apply M)

/-! ### First columns and the complex line -/

/-- The quaternion whose matrix under `Quaternion.toComplexMatrix` has first column `z`
(`toComplexMatrix_ofFirstColumn_apply_zero`), and every quaternion is recovered from the first
column of its matrix (`ofFirstColumn_toComplexMatrix_apply_zero`). Through it, matrices of
quaternions act on `ℂ²` by left multiplication (`ofFirstColumn_toComplexMatrix_mulVec`) and complex
scalars by right multiplication (`ofFirstColumn_smul`). -/
def ofFirstColumn (z : Fin 2 → ℂ) : ℍ[ℝ] :=
  ⟨(z 0).re, (z 0).im, -(z 1).re, (z 1).im⟩

/-- The real part of `ofFirstColumn z` is the real part of `z 0`. -/
@[simp]
theorem re_ofFirstColumn (z : Fin 2 → ℂ) : (ofFirstColumn z).re = (z 0).re := (rfl)

/-- The `i`-part of `ofFirstColumn z` is the imaginary part of `z 0`. -/
@[simp]
theorem imI_ofFirstColumn (z : Fin 2 → ℂ) : (ofFirstColumn z).imI = (z 0).im := (rfl)

/-- The `j`-part of `ofFirstColumn z` is minus the real part of `z 1`. -/
@[simp]
theorem imJ_ofFirstColumn (z : Fin 2 → ℂ) : (ofFirstColumn z).imJ = -(z 1).re := (rfl)

/-- The `k`-part of `ofFirstColumn z` is the imaginary part of `z 1`. -/
@[simp]
theorem imK_ofFirstColumn (z : Fin 2 → ℂ) : (ofFirstColumn z).imK = (z 1).im := (rfl)

/-- A quaternion is recovered from the first column of its matrix. -/
@[simp]
theorem ofFirstColumn_toComplexMatrix_apply_zero (q : ℍ[ℝ]) :
    ofFirstColumn (fun i => toComplexMatrix q i 0) = q := by
  rw [toComplexMatrix_apply]
  ext <;> simp

/-- The first column of the matrix of `ofFirstColumn z` is `z`. -/
@[simp]
theorem toComplexMatrix_ofFirstColumn_apply_zero (z : Fin 2 → ℂ) (i : Fin 2) :
    toComplexMatrix (ofFirstColumn z) i 0 = z i := by
  rw [toComplexMatrix_apply]
  fin_cases i <;> apply Complex.ext <;> simp [ofFirstColumn]

/-- Left multiplication by `q` is the matrix `toComplexMatrix q` on first columns. -/
theorem ofFirstColumn_toComplexMatrix_mulVec (q : ℍ[ℝ]) (z : Fin 2 → ℂ) :
    ofFirstColumn (toComplexMatrix q *ᵥ z) = q * ofFirstColumn z := by
  rw [toComplexMatrix_apply]
  ext <;> simp [ofFirstColumn, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Complex scalars act on first columns by right multiplication. -/
theorem ofFirstColumn_smul (c : ℂ) (z : Fin 2 → ℂ) :
    ofFirstColumn (c • z) = ofFirstColumn z * (c : ℍ[ℝ]) := by
  ext <;> simp [ofFirstColumn] <;> ring

/-- The circle as the unit quaternions of the complex line `ℝ ⊕ ℝ i`. -/
noncomputable def circleToUnitary : Circle →* unitary ℍ[ℝ] where
  toFun w := ⟨((w : ℂ) : ℍ[ℝ]), by
    rw [mem_unitary_iff_normSq_eq_one, normSq_def']
    simpa [sq] using Circle.re_sq_add_im_sq w⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)

/-- The unit quaternion `circleToUnitary w` is the complex number `w`. -/
@[simp]
theorem coe_circleToUnitary (w : Circle) :
    (circleToUnitary w : ℍ[ℝ]) = ((w : ℂ) : ℍ[ℝ]) :=
  (rfl)

/-! ### `U(2)` as a quotient of `Sp(1) × U(1)` -/

/-- **`U(2)` from unit quaternions and the circle.** The homomorphism `Sp(1) × U(1) → U(2)`,
`(q, w) ↦ w • toComplexMatrix q`. It is onto (`unitaryProdCircleToUnitaryGroup_surjective`) with
kernel `{1, -1}` (`mem_ker_unitaryProdCircleToUnitaryGroup_iff`). -/
noncomputable def unitaryProdCircleToUnitaryGroup :
    unitary ℍ[ℝ] × Circle →* Matrix.unitaryGroup (Fin 2) ℂ where
  toFun p := ⟨(p.2 : ℂ) • toComplexMatrix (p.1 : ℍ[ℝ]),
    Unitary.smul_mem_of_mem p.2.coe_mem_unitary
      (Matrix.specialUnitaryGroup_le_unitaryGroup (mem_specialUnitaryGroup_toComplexMatrix p.1.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' p q := Subtype.ext (by
    simp only [Prod.fst_mul, Prod.snd_mul, Submonoid.coe_mul, Circle.coe_mul, map_mul]
    rw [smul_mul_smul_comm])

/-- The matrix of `unitaryProdCircleToUnitaryGroup (q, w)` is `w • toComplexMatrix q`. -/
@[simp]
theorem coe_unitaryProdCircleToUnitaryGroup_apply (p : unitary ℍ[ℝ] × Circle) :
    (unitaryProdCircleToUnitaryGroup p : Matrix (Fin 2) (Fin 2) ℂ) =
      (p.2 : ℂ) • toComplexMatrix (p.1 : ℍ[ℝ]) :=
  (rfl)

/-- **`U(2) = U(1) · Sp(1)`.** Every unitary matrix of degree two is a scalar of modulus one times
the matrix of a unit quaternion. -/
theorem unitaryProdCircleToUnitaryGroup_surjective :
    Function.Surjective unitaryProdCircleToUnitaryGroup := by
  intro g
  obtain ⟨c, hc⟩ := Matrix.exists_circle_smul_mem_specialUnitaryGroup g
  refine ⟨(unitaryEquivSpecialUnitaryGroup.symm ⟨_, hc⟩, c⁻¹), Subtype.ext ?_⟩
  rw [coe_unitaryProdCircleToUnitaryGroup_apply, coe_unitaryEquivSpecialUnitaryGroup_symm_apply,
    smul_smul, Circle.coe_inv, inv_mul_cancel₀ (Circle.coe_ne_zero _), one_smul]

/-- **The kernel of `Sp(1) × U(1) → U(2)` is `{1, -1}`**: `w • q = 1` forces `q = w⁻¹` to be a real
unit quaternion. -/
theorem mem_ker_unitaryProdCircleToUnitaryGroup_iff {p : unitary ℍ[ℝ] × Circle} :
    p ∈ unitaryProdCircleToUnitaryGroup.ker ↔ p = 1 ∨ p = -1 := by
  refine ⟨fun hp => ?_, ?_⟩
  · obtain ⟨⟨a, ha⟩, w⟩ := p
    have hm := congrArg (fun g : Matrix.unitaryGroup (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ))
      (MonoidHom.mem_ker.mp hp)
    simp only [coe_unitaryProdCircleToUnitaryGroup_apply, OneMemClass.coe_one,
      toComplexMatrix_apply] at hm
    -- Compare the entries `(0, 0)`, `(0, 1)` and `(1, 1)` of `w • toComplexMatrix a = 1`.
    have h00 := congrFun (congrFun hm 0) 0
    have h01 := congrFun (congrFun hm 0) 1
    have h11 := congrFun (congrFun hm 1) 1
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul,
      Matrix.one_apply_eq, Matrix.one_apply_ne zero_ne_one] at h00 h01 h11
    have hw := Circle.coe_ne_zero w
    have hJK : (a.imJ : ℂ) + a.imK * Complex.I = 0 := (mul_eq_zero.mp h01).resolve_left hw
    have hJ : a.imJ = 0 := by simpa using congrArg Complex.re hJK
    have hK : a.imK = 0 := by simpa using congrArg Complex.im hJK
    have hI : a.imI = 0 := by
      have := congrArg Complex.im (mul_left_cancel₀ hw (h00.trans h11.symm))
      simp at this
      linarith
    have hre : (a.re - 1) * (a.re + 1) = 0 := by
      have := (mem_unitary_iff_normSq_eq_one a).mp ha
      rw [normSq_def'] at this
      linear_combination (by simpa [hI, hJ, hK, sq] using this : a.re ^ 2 = 1)
    have hwre : (w : ℂ) * a.re = 1 := by simpa [hI] using h00
    rcases mul_eq_zero.mp hre with h | h
    · have h1 : a.re = 1 := by linarith
      refine Or.inl (Prod.ext (Subtype.ext ?_) (Circle.ext (by simpa [h1] using hwre)))
      ext <;> simp [h1, hI, hJ, hK]
    · have h1 : a.re = -1 := by linarith
      refine Or.inr (Prod.ext (Subtype.ext ?_)
        (Circle.ext (by simpa [h1, neg_eq_iff_eq_neg] using hwre)))
      ext <;> simp [h1, hI, hJ, hK, Unitary.coe_neg]
  · rintro (rfl | rfl)
    · exact one_mem _
    · refine MonoidHom.mem_ker.mpr (Subtype.ext ?_)
      simp [Unitary.coe_neg]

end Quaternion

end
