/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Algebra.Lie.Orthogonal.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.UnitaryTransvection
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.DotProduct
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The indefinite unitary group `U(p, q)`

Let `R` be a commutative ring with an involution `star`. For a square matrix `A` over `R`, the
**unitary group of `A`**, `Matrix.unitaryGroupOf A` (defined, with its basic API, in
`TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Form`), is the subgroup of `GL n R` of the
matrices `g` with `star g * A * g = A`: the invertible matrices preserving the sesquilinear form
`⟨z, w⟩ = star z ⬝ᵥ A *ᵥ w` of Gram matrix `A`, conjugate-linear in the first slot.

For `J = LieAlgebra.Orthogonal.indefiniteDiagonal p q R = diag(1, …, 1, -1, …, -1)`, the Gram
matrix of the Hermitian form
`⟨z, w⟩ = star z ⬝ᵥ J *ᵥ w = Σ_{i ∈ p} star zᵢ wᵢ - Σ_{j ∈ q} star zⱼ wⱼ` on `p ⊕ q → R`, this is
the **indefinite unitary group** `TauCeti.Matrix.indefiniteUnitaryGroup p q R`. Over `ℂ` this is
`U(p, q)`, and `U(1, n)`, for `p = Fin 1` and `q = Fin n`, is the group acting on complex
hyperbolic `n`-space. Over `ℝ`, where the star is trivial, it is the indefinite orthogonal group
`O(p, q)`.

The basic structure of these groups is recorded here.

* Its determinant-one elements form the special isometry group
  `Matrix.specialIsometryGroup A (starRingEnd R)` of the same form, whose defining equation is
  written `(g.map σ)ᵀ * A * g = A`.
* Membership in `unitaryGroupOf A` is equivalent to the preservation `⟨g z, g w⟩ = ⟨z, w⟩` of the
  form and, for invertible `A`, to `g * A⁻¹ * star g = A⁻¹`, that is to `star g` lying in
  `unitaryGroupOf A⁻¹`. For `J`, which is its own inverse, `U(p, q)` is stable under `star`.
  (Over `ℝ` or `ℂ` and for Hermitian `A`, membership is also equivalent, by polarization, to the
  preservation of the values `⟨z, z⟩` alone; that statement, with the topological facts, is in
  `TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup`.)
* For invertible `A`, the determinant of an element of `unitaryGroupOf A` is a unitary scalar.
  For `U(p, q)` the inverse `A⁻¹ * star g * A` of `g` is `J * star g * J`.
* The block-diagonal matrices `diag(A, D)` with `A ∈ U(p)` and `D ∈ U(q)` form a subgroup of
  `U(p, q)` isomorphic to `U(p) × U(q)` (`TauCeti.Matrix.indefiniteUnitaryGroup.fromBlocksHom`). It
  is the stabilizer of the coordinate subspace `p → R` spanned by the positive basis vectors: an
  element of `U(p, q)` preserves that subspace, that is has vanishing lower-left block, exactly
  when it is block diagonal. For `U(1, n)` this is the stabilizer `U(1) × U(n)` of the positive
  line spanned by the first basis vector.
* Over a field of characteristic zero, the centre of `U(p, q)` is the group of unit scalars
  `λ • 1` with `star λ * λ = 1`. The proof uses the reflections
  `1 - (2 / ⟨v, v⟩) • vecMulVec v (star v ᵥ* A)` in the non-isotropic vectors `v`, which lie in
  `unitaryGroupOf A` for every Hermitian `A` (`Matrix.unitaryGroupOf.reflection`, defined in
  `TauCeti.LinearAlgebra.Matrix.UnitaryGroup.UnitaryTransvection` for every vector, as the
  identity at isotropic vectors): a
  central element commutes with the rank-one matrices `vecMulVec v (star v ᵥ* A)`, and for `A = J`
  testing this on the vectors `eₖ` and `eᵢ + 2 eₖ` forces it to be scalar.

## Main definitions

* `Matrix.unitaryGroupOf.scalarHom`: the embedding `λ ↦ λ • 1` of the unitary scalars.
* `Matrix.unitaryGroupOf.conjEquiv`: for `bᴴ (t A) b = A'` with `t ≠ 0`, the isomorphism
  `g ↦ b⁻¹ g b` from `unitaryGroupOf A` onto `unitaryGroupOf A'`.
* `Matrix.unitaryGroupOf.transport`: for such `b` and `a b ∈ unitaryGroupOf A'`, the bijection
  `g ↦ a g b` from `unitaryGroupOf A` onto `unitaryGroupOf A'`.
* `TauCeti.Matrix.indefiniteUnitaryGroup p q R`: the group `U(p, q)` of invertible matrices
  preserving the Hermitian form of Gram matrix `diag(1, …, 1, -1, …, -1)`.
* `TauCeti.Matrix.indefiniteUnitaryGroup.fromBlocksHom`: the block-diagonal embedding of
  `U(p) × U(q)`.

## Main results

* `Matrix.mem_unitaryGroupOf_iff_forall_dotProduct`: membership as preservation of the
  form.
* `Matrix.specialIsometryGroup_starRingEnd_eq_comap_unitaryGroupOf`: the determinant-one elements
  of `unitaryGroupOf A` are the special isometry group of the form.
* `Matrix.mem_unitaryGroupOf_iff'`: membership as the equation `g * A⁻¹ * star g = A⁻¹`.
* `Matrix.star_mem_unitaryGroupOf_iff_of_mul_self_eq_one`: for an involution `A` (`A * A = 1`),
  `unitaryGroupOf A` is stable under conjugate transposition.
* `Matrix.det_mem_unitary_of_mem_unitaryGroupOf`: `star (det g) * det g = 1`.
* `Matrix.unitaryGroupOf.scalarHom_injective`: the embedding of the unitary scalars is
  injective.
* `TauCeti.Matrix.mem_indefiniteUnitaryGroup_iff'`: membership in `U(p, q)` as the equation
  `g * J * star g = J`.
* `TauCeti.Matrix.val_inv_of_mem_indefiniteUnitaryGroup`: the inverse of `g ∈ U(p, q)` is
  `J * star g * J`.
* `TauCeti.Matrix.star_diagonal_mul_indefiniteDiagonal_mul_diagonal_eq_iff`: a diagonal matrix
  preserves the form of `J` exactly when its diagonal entries are unitary.
* `TauCeti.Matrix.star_mem_indefiniteUnitaryGroup_iff`: `U(p, q)` is stable under conjugate
  transposition.
* `TauCeti.Matrix.indefiniteUnitaryGroup.mem_range_fromBlocksHom_iff`: the image of
  `U(p) × U(q)` is the subgroup of elements with vanishing lower-left block.
* `TauCeti.Matrix.indefiniteUnitaryGroup.mem_range_fromBlocksHom_iff_mem_unitaryGroup`: when `2`
  is left-regular in `R`, the image of `U(p) × U(q)` is `U(p, q) ∩ U(p ⊕ q)`.
* `TauCeti.Matrix.indefiniteUnitaryGroup.center_eq_range_scalarHom`: over a field of
  characteristic zero, the centre of `U(p, q)` is the group of unit scalars.
* `TauCeti.Matrix.indefiniteUnitaryGroup.center_eq_comap_center`: over a field of
  characteristic zero, an element of `U(p, q)` is central in `U(p, q)` exactly when it is central
  in the general linear group.

## References

* W. M. Goldman, *Complex Hyperbolic Geometry*, Oxford Mathematical Monographs, Oxford University
  Press (1999), Chapter 3.
* G. Baldi and E. Ullmo, *Special subvarieties of non-arithmetic ball quotients and Hodge theory*,
  Ann. of Math. 197 (2023), Section 2, for the matrix description of `U(1, n)`.
-/

public section

open LieAlgebra.Orthogonal Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R] [StarRing R] {A : Matrix n n R}

/-- **`unitaryGroupOf A` is the group of isometries of the form**: `g ∈ unitaryGroupOf A` exactly
when `⟨g x, g y⟩ = ⟨x, y⟩` for all `x` and `y`, where `⟨x, y⟩ = star x ⬝ᵥ A *ᵥ y`. -/
theorem mem_unitaryGroupOf_iff_forall_dotProduct {g : GL n R} :
    g ∈ unitaryGroupOf A ↔ ∀ x y : n → R,
      star ((g : Matrix n n R) *ᵥ x) ⬝ᵥ A *ᵥ (g *ᵥ y) = star x ⬝ᵥ A *ᵥ y := by
  refine ⟨fun h => comp_mulVec_dotProduct_mulVec_mulVec (σ := starRingEnd R)
    (mem_unitaryGroupOf_iff.1 h), fun h => mem_unitaryGroupOf_iff.2 ?_⟩
  simp only [← star_dotProduct_conjTranspose_mul_mul_mulVec, ← star_eq_conjTranspose] at h
  ext i j
  simpa [mulVec_single_one, Pi.star_single] using h (Pi.single i 1) (Pi.single j 1)

/-- The determinant-one elements of `unitaryGroupOf A` form Tau Ceti's special isometry group
`Matrix.specialIsometryGroup A (starRingEnd R)` of the `star`-sesquilinear form: the two defining
equations agree, since `star g = (g.map star)ᵀ`. -/
theorem specialIsometryGroup_starRingEnd_eq_comap_unitaryGroupOf :
    A.specialIsometryGroup (starRingEnd R) =
      (unitaryGroupOf A).comap SpecialLinearGroup.toGL :=
  Subgroup.ext fun g => by
    rw [mem_specialIsometryGroup_iff, Subgroup.mem_comap, mem_unitaryGroupOf_iff,
      SpecialLinearGroup.coe_GL_coe_matrix, transpose_map_starRingEnd, ← star_eq_conjTranspose]

/-- For invertible `A`, membership in `unitaryGroupOf A` is equivalent to the equation
`g * A⁻¹ * star g = A⁻¹`. -/
theorem mem_unitaryGroupOf_iff' (hA : IsUnit A) {g : GL n R} :
    g ∈ unitaryGroupOf A ↔ (g : Matrix n n R) * A⁻¹ * star (g : Matrix n n R) = A⁻¹ := by
  -- Both equations say that `A⁻¹ * star g * A` is an inverse of `g`, on the left and on the right.
  set M : Matrix n n R := (g : Matrix n n R)
  have hd : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA
  have hA' : IsUnit A⁻¹ := (isUnit_nonsing_inv_iff).mpr hA
  calc g ∈ unitaryGroupOf A ↔ A⁻¹ * (star M * A * M) = A⁻¹ * A :=
        mem_unitaryGroupOf_iff.trans hA'.mul_right_inj.symm
    _ ↔ A⁻¹ * star M * A * M = 1 := by simp only [nonsing_inv_mul _ hd, Matrix.mul_assoc]
    _ ↔ M * (A⁻¹ * star M * A) = 1 := mul_eq_one_comm
    _ ↔ M * A⁻¹ * star M * A = A⁻¹ * A := by simp only [nonsing_inv_mul _ hd, Matrix.mul_assoc]
    _ ↔ _ := hA.mul_left_inj

/-- For invertible `A`, conjugate transposition maps `unitaryGroupOf A` onto
`unitaryGroupOf A⁻¹`. -/
theorem star_mem_unitaryGroupOf_inv_iff (hA : IsUnit A) {g : GL n R} :
    star g ∈ unitaryGroupOf A⁻¹ ↔ g ∈ unitaryGroupOf A := by
  rw [mem_unitaryGroupOf_iff, mem_unitaryGroupOf_iff' hA, Units.coe_star, star_star]

/-- For an involution `A` (`A * A = 1`), `unitaryGroupOf A` is stable under conjugate
transposition (`star`). -/
theorem star_mem_unitaryGroupOf_iff_of_mul_self_eq_one (hA : A * A = 1) {g : GL n R} :
    star g ∈ unitaryGroupOf A ↔ g ∈ unitaryGroupOf A := by
  have hA_unit : IsUnit A := isUnit_iff_exists_inv.2 ⟨A, hA⟩
  have hA_inv : A⁻¹ = A := inv_eq_left_inv hA
  simpa only [hA_inv] using star_mem_unitaryGroupOf_inv_iff hA_unit

/-- **The determinant of an element of `unitaryGroupOf A` is a unitary scalar**, for invertible
`A`: `star (det g) * det g = 1`. Over `ℂ` this says `|det g| = 1`. -/
theorem det_mem_unitary_of_mem_unitaryGroupOf (hA : IsUnit A) {g : GL n R}
    (hg : g ∈ unitaryGroupOf A) : (g : Matrix n n R).det ∈ unitary R := by
  have h := congrArg det (mem_unitaryGroupOf_iff.mp hg)
  rw [det_mul, det_mul, star_eq_conjTranspose, det_conjTranspose, mul_right_comm] at h
  rw [Unitary.mem_iff_star_mul_self]
  exact ((isUnit_iff_isUnit_det A).mp hA).mul_eq_right.mp h

section Congruence

variable {A' : Matrix n n R} {b : GL n R} {K : Type*} [Semifield K] [Algebra K R] {t : K}

/-- If `bᴴ (t A) b = A'` with `A` invertible and `t ≠ 0`, then `A'` is invertible. -/
theorem isUnit_of_star_mul_smul_mul_eq (hA : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n R) * (t • A) * b = A') : IsUnit A' := by
  rw [← hb]
  have htA : IsUnit (t • A) := by simpa [Units.smul_def] using hA.smul (Units.mk0 t ht)
  exact ((b.isUnit.star).mul htA).mul b.isUnit

/-- The congruence `bᴴ (t A) b = A'` inverted: `(b⁻¹)ᴴ (t⁻¹ A') b⁻¹ = A`. -/
theorem star_inv_mul_smul_mul_inv (ht : t ≠ 0) (hb : star (b : Matrix n n R) * (t • A) * b = A') :
    star ((b⁻¹ : GL n R) : Matrix n n R) * (t⁻¹ • A') * (b⁻¹ : GL n R) = A := by
  have h1 : star ((b⁻¹ : GL n R) : Matrix n n R) * star (b : Matrix n n R) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  have h2 : (b : Matrix n n R) * ((b⁻¹ : GL n R) : Matrix n n R) = 1 := Units.mul_inv b
  rw [← hb]
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h2, Matrix.mul_one, smul_smul, inv_mul_cancel₀ ht, one_smul]

end Congruence

namespace unitaryGroupOf

variable (A) in
/-- The embedding `λ ↦ λ • 1` of the unitary scalars in `unitaryGroupOf A`. For the indefinite
unitary group over a field of characteristic zero its image is the centre
(`TauCeti.Matrix.indefiniteUnitaryGroup.center_eq_range_scalarHom`). -/
def scalarHom : unitary R →* unitaryGroupOf A :=
  ((GeneralLinearGroup.scalar n).comp Unitary.toUnits).codRestrict _ fun u => by
    rw [mem_unitaryGroupOf_iff]
    ext i j
    simp [star_eq_conjTranspose, mul_diagonal, diagonal_mul, mul_right_comm,
      Unitary.star_mul_self_of_mem u.property]

@[simp]
theorem val_scalarHom (u : unitary R) :
    ((scalarHom A u : GL n R) : Matrix n n R) = scalar n (u : R) :=
  GeneralLinearGroup.coe_scalar _

/-- The embedding of the unitary scalars in `unitaryGroupOf A` is injective for nonempty `n`. -/
theorem scalarHom_injective [Nonempty n] : Function.Injective (scalarHom A) := fun u v h => by
  rw [unitaryGroupOf.ext_iff, val_scalarHom, val_scalarHom] at h
  exact Subtype.ext (scalar_inj.mp h)

section Congruence

variable {A' : Matrix n n R} {b : GL n R}

section CommSemiring

variable {K : Type*} [CommSemiring K] [Algebra K R] {t : K}

/-- If `bᴴ (t A) b = A'`, conjugation `g ↦ b⁻¹ g b` maps the unitary group of `A` into that of
`A'`. -/
theorem inv_mul_mul_mem (hb : star (b : Matrix n n R) * (t • A) * b = A') {g : GL n R}
    (hg : g ∈ unitaryGroupOf A) : b⁻¹ * g * b ∈ unitaryGroupOf A' := by
  rw [mem_unitaryGroupOf_iff] at hg ⊢
  rw [← hb]
  have h1 : star ((b⁻¹ : GL n R) : Matrix n n R) * star (b : Matrix n n R) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  have h2 : (b : Matrix n n R) * ((b⁻¹ : GL n R) : Matrix n n R) = 1 := Units.mul_inv b
  calc star (((b⁻¹ * g * b : GL n R)) : Matrix n n R) * (star (b : Matrix n n R) * (t • A) * b) *
        ((b⁻¹ * g * b : GL n R) : Matrix n n R)
      = star (b : Matrix n n R) * star (g : Matrix n n R) *
          (star ((b⁻¹ : GL n R) : Matrix n n R) * star (b : Matrix n n R)) * (t • A) *
          ((b : Matrix n n R) * ((b⁻¹ : GL n R) : Matrix n n R)) * g * b := by
        simp only [Units.val_mul, star_mul, Matrix.mul_assoc]
    _ = star (b : Matrix n n R) * (t • (star (g : Matrix n n R) * A * g)) * b := by
        rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = star (b : Matrix n n R) * (t • A) * b := by rw [hg]

end CommSemiring

variable {K : Type*} [Semifield K] [Algebra K R] {t : K}

/-- The **conjugation isomorphism** `g ↦ b⁻¹ g b` from the unitary group of `A` to that of
`A' = bᴴ (t A) b`, for a nonzero scalar `t`. Its inverse is `g ↦ b g b⁻¹`. -/
noncomputable def conjEquiv (ht : t ≠ 0) (hb : star (b : Matrix n n R) * (t • A) * b = A') :
    unitaryGroupOf A ≃* unitaryGroupOf A' where
  toFun g := ⟨b⁻¹ * g * b, inv_mul_mul_mem hb g.property⟩
  invFun g := ⟨b * g * b⁻¹, by
    simpa using inv_mul_mul_mem (star_inv_mul_smul_mul_inv ht hb) g.property⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  map_mul' g h := Subtype.ext (by simp [mul_assoc])

theorem conjEquiv_apply (ht : t ≠ 0) (hb : star (b : Matrix n n R) * (t • A) * b = A')
    (g : unitaryGroupOf A) :
    conjEquiv ht hb g = ⟨b⁻¹ * g * b, inv_mul_mul_mem hb g.property⟩ :=
  (rfl)

@[simp]
theorem coe_conjEquiv_apply (ht : t ≠ 0) (hb : star (b : Matrix n n R) * (t • A) * b = A')
    (g : unitaryGroupOf A) :
    (((conjEquiv ht hb g : unitaryGroupOf A') : GL n R) : Matrix n n R) =
      (b : Matrix n n R)⁻¹ * ((g : GL n R) : Matrix n n R) * b := by
  simp [conjEquiv, coe_units_inv]

@[simp]
theorem coe_conjEquiv_symm_apply (ht : t ≠ 0) (hb : star (b : Matrix n n R) * (t • A) * b = A')
    (g : unitaryGroupOf A') :
    ((((conjEquiv ht hb).symm g : unitaryGroupOf A) : GL n R) : Matrix n n R) =
      (b : Matrix n n R) * ((g : GL n R) : Matrix n n R) * (b : Matrix n n R)⁻¹ := by
  simp [conjEquiv, coe_units_inv]

/-- For `a b ∈ U(A')`, the bijection `g ↦ a g b` from the unitary group of `A` to that of
`A' = bᴴ (t A) b`: the conjugation isomorphism `g ↦ b⁻¹ g b` followed by the left translation by
`a b`. -/
noncomputable def transport (ht : t ≠ 0) (hb : star (b : Matrix n n R) * (t • A) * b = A')
    {a : GL n R} (hab : a * b ∈ unitaryGroupOf A') : unitaryGroupOf A ≃ unitaryGroupOf A' :=
  (conjEquiv ht hb).toEquiv.trans (Equiv.mulLeft ⟨a * b, hab⟩)

theorem transport_apply (ht : t ≠ 0) (hb : star (b : Matrix n n R) * (t • A) * b = A')
    {a : GL n R} (hab : a * b ∈ unitaryGroupOf A') (g : unitaryGroupOf A) :
    transport ht hb hab g = ⟨a * b, hab⟩ * conjEquiv ht hb g :=
  (rfl)

/-- `Matrix.unitaryGroupOf.transport` is `g ↦ a g b`. -/
@[simp]
theorem coe_transport_apply (ht : t ≠ 0) (hb : star (b : Matrix n n R) * (t • A) * b = A')
    {a : GL n R} (hab : a * b ∈ unitaryGroupOf A') (g : unitaryGroupOf A) :
    (((transport ht hb hab g : unitaryGroupOf A') : GL n R) : Matrix n n R) =
      (a : Matrix n n R) * ((g : GL n R) : Matrix n n R) * b := by
  simp [transport_apply, Matrix.mul_assoc]

/-- The inverse of `Matrix.unitaryGroupOf.transport` is `g ↦ a⁻¹ g b⁻¹`. -/
@[simp]
theorem coe_transport_symm_apply (ht : t ≠ 0) (hb : star (b : Matrix n n R) * (t • A) * b = A')
    {a : GL n R} (hab : a * b ∈ unitaryGroupOf A') (g : unitaryGroupOf A') :
    ((((transport ht hb hab).symm g : unitaryGroupOf A) : GL n R) : Matrix n n R) =
      (a : Matrix n n R)⁻¹ * ((g : GL n R) : Matrix n n R) * (b : Matrix n n R)⁻¹ := by
  obtain ⟨h, rfl⟩ := (transport ht hb hab).surjective g
  rw [Equiv.symm_apply_apply, coe_transport_apply]
  simp [Matrix.mul_assoc]

end Congruence

end unitaryGroupOf

end CommRing

section Field

variable {K : Type*} [Field K] [StarRing K] {A : Matrix n n K}

namespace unitaryGroupOf

/-- For a Hermitian Gram matrix `A`, an element of the centre of `unitaryGroupOf A`
commutes with the rank-one matrix `v (star v ᵥ* A)` of every non-isotropic vector `v`, since it
commutes with the reflection in `v`. -/
private theorem mul_vecMulVec_eq_of_mem_center [NeZero (2 : K)] (hA : A.IsHermitian)
    {g : unitaryGroupOf A} (hg : g ∈ Subgroup.center (unitaryGroupOf A))
    {v : n → K} (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) :
    ((g : GL n K) : Matrix n n K) * vecMulVec v (star v ᵥ* A) =
      vecMulVec v (star v ᵥ* A) * (g : GL n K) := by
  have h := congrArg (fun x : unitaryGroupOf A => ((x : GL n K) : Matrix n n K))
    (Subgroup.mem_center_iff.mp hg (reflection hA v))
  simp only [Subgroup.coe_mul, Units.val_mul, val_reflection, sub_mul, mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, sub_right_inj] at h
  exact (smul_right_injective _ (div_ne_zero two_ne_zero hv) h).symm

/-- The entry `(i, k)` of `g * v (star v ᵥ* A) = v (star v ᵥ* A) * g`. -/
private theorem mulVec_apply_mul_eq_of_mem_center [NeZero (2 : K)] (hA : A.IsHermitian)
    {g : unitaryGroupOf A} (hg : g ∈ Subgroup.center (unitaryGroupOf A))
    {v : n → K} (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) (i k : n) :
    (((g : GL n K) : Matrix n n K) *ᵥ v) i * (star v ᵥ* A) k =
      v i * (star v ᵥ* A ᵥ* ((g : GL n K) : Matrix n n K)) k := by
  simpa [mul_vecMulVec, vecMulVec_mul, vecMulVec_apply] using
    congrFun (congrFun (mul_vecMulVec_eq_of_mem_center hA hg hv) i) k

end unitaryGroupOf

end Field

end Matrix

namespace TauCeti

namespace Matrix

variable (p q R : Type*) [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

section CommRing

variable [CommRing R] [StarRing R]

/-- The **indefinite unitary group** `U(p, q)`: the invertible matrices `g` on `p ⊕ q → R` with
`star g * J * g = J`, where `J = diag(1, …, 1, -1, …, -1)` is
`LieAlgebra.Orthogonal.indefiniteDiagonal p q R`, the Gram matrix of the Hermitian form
`⟨z, w⟩ = star z ⬝ᵥ J *ᵥ w` of signature `(p, q)`. It is `unitaryGroupOf J`, whose general API
applies to it. -/
abbrev indefiniteUnitaryGroup : Subgroup (GL (p ⊕ q) R) :=
  unitaryGroupOf (indefiniteDiagonal p q R)

variable {p q R}

/-- **The inverse of an element of `U(p, q)`** is `J * star g * J`. -/
theorem val_inv_of_mem_indefiniteUnitaryGroup {g : GL (p ⊕ q) R}
    (hg : g ∈ indefiniteUnitaryGroup p q R) :
    (↑g⁻¹ : Matrix (p ⊕ q) (p ⊕ q) R) =
      indefiniteDiagonal p q R * star (g : Matrix (p ⊕ q) (p ⊕ q) R) *
        indefiniteDiagonal p q R := by
  rw [val_inv_of_mem_unitaryGroupOf isUnit_indefiniteDiagonal hg, inv_indefiniteDiagonal]

/-- Membership in `U(p, q)` is equivalent to the equation `g * J * star g = J`. -/
theorem mem_indefiniteUnitaryGroup_iff' {g : GL (p ⊕ q) R} :
    g ∈ indefiniteUnitaryGroup p q R ↔
      (g : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R * star (g : Matrix _ _ R) =
        indefiniteDiagonal p q R := by
  rw [mem_unitaryGroupOf_iff' isUnit_indefiniteDiagonal, inv_indefiniteDiagonal]

/-- **`U(p, q)` is stable under conjugate transposition.** -/
@[simp]
theorem star_mem_indefiniteUnitaryGroup_iff {g : GL (p ⊕ q) R} :
    star g ∈ indefiniteUnitaryGroup p q R ↔ g ∈ indefiniteUnitaryGroup p q R := by
  simpa only [inv_indefiniteDiagonal] using
    star_mem_unitaryGroupOf_inv_iff (A := indefiniteDiagonal p q R) isUnit_indefiniteDiagonal

/-- A diagonal matrix `diag(d)` satisfies `star (diag d) * J * diag d = J` exactly when every
diagonal entry is unitary. -/
theorem star_diagonal_mul_indefiniteDiagonal_mul_diagonal_eq_iff {d : p ⊕ q → R} :
    star (diagonal d) * indefiniteDiagonal p q R * diagonal d = indefiniteDiagonal p q R ↔
      ∀ i, star (d i) * d i = 1 := by
  rw [indefiniteDiagonal, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    diagonal_mul_diagonal, diagonal_eq_diagonal_iff]
  refine forall_congr' fun i => ?_
  rcases i with i | i <;> simp [neg_eq_iff_eq_neg]

namespace indefiniteUnitaryGroup

variable (p q R) in
/-- The **block-diagonal embedding** `(A, D) ↦ diag(A, D)` of `U(p) × U(q)` in `U(p, q)`. Its
image is the stabilizer of the positive coordinate subspace (`mem_range_fromBlocksHom_iff`); for
`U(1, n)` it is the stabilizer `U(1) × U(n)` of the positive line spanned by the first basis
vector. -/
def fromBlocksHom : unitaryGroup p R × unitaryGroup q R →* indefiniteUnitaryGroup p q R :=
  (Unitary.toUnits.comp UnitaryGroup.sum).codRestrict _ fun x => by
    rw [mem_unitaryGroupOf_iff, MonoidHom.comp_apply, Unitary.val_toUnits_apply,
      UnitaryGroup.coe_sum, indefiniteDiagonal_eq_fromBlocks, star_eq_conjTranspose,
      fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [← star_eq_conjTranspose]

@[simp]
theorem val_fromBlocksHom (x : unitaryGroup p R × unitaryGroup q R) :
    ((fromBlocksHom p q R x : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) =
      fromBlocks (x.1 : Matrix p p R) 0 0 (x.2 : Matrix q q R) := by
  simp [fromBlocksHom]

/-- The block-diagonal embedding of `U(p) × U(q)` in `U(p, q)` is injective. -/
theorem fromBlocksHom_injective : Function.Injective (fromBlocksHom p q R) := fun x y h =>
  UnitaryGroup.sum_injective <| Subtype.ext <| by
    simpa using congrArg (fun g : indefiniteUnitaryGroup p q R =>
      ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R)) h

/-- **The stabilizer of the positive coordinate subspace.** An element of `U(p, q)` lies in the
image of `U(p) × U(q)` exactly when its lower-left block vanishes, that is when it maps the
subspace spanned by the positive basis vectors `eᵢ`, `i ∈ p`, into itself. -/
theorem mem_range_fromBlocksHom_iff {g : indefiniteUnitaryGroup p q R} :
    g ∈ (fromBlocksHom p q R).range ↔
      ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R).toBlocks₂₁ = 0 := by
  refine ⟨fun ⟨x, hx⟩ => by rw [← hx, val_fromBlocksHom, toBlocks_fromBlocks₂₁], fun hC => ?_⟩
  set M : Matrix (p ⊕ q) (p ⊕ q) R := ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R)
  have hM : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← hC, fromBlocks_toBlocks]
  have h : star M * indefiniteDiagonal p q R * M = indefiniteDiagonal p q R :=
    mem_unitaryGroupOf_iff.mp g.property
  rw [hM, indefiniteDiagonal_eq_fromBlocks, star_eq_conjTranspose, fromBlocks_conjTranspose,
    fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  simp only [conjTranspose_zero, Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul,
    Matrix.mul_neg, Matrix.neg_mul, zero_add, neg_zero] at h
  obtain ⟨hA, hB, -, hD⟩ := h
  have hAu : M.toBlocks₁₁ ∈ unitaryGroup p R := by
    rwa [mem_unitaryGroup_iff', star_eq_conjTranspose]
  have hB0 : M.toBlocks₁₂ = 0 := by
    rw [← Matrix.one_mul M.toBlocks₁₂, ← mem_unitaryGroup_iff.mp hAu, Matrix.mul_assoc,
      star_eq_conjTranspose, hB, Matrix.mul_zero]
  have hDu : M.toBlocks₂₂ ∈ unitaryGroup q R := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
    simpa [hB0] using hD
  refine ⟨(⟨_, hAu⟩, ⟨_, hDu⟩), unitaryGroupOf.ext ?_⟩
  rw [val_fromBlocksHom]
  exact (hB0 ▸ hM).symm

/-- An element of `U(p, q)` (or `O(p, q)`) is unitary in the ambient space if and only if it lies
in the block-diagonal subgroup `U(p) × U(q)` (the range of `fromBlocksHom`), provided `2` is
left-regular in `R`. -/
theorem mem_range_fromBlocksHom_iff_mem_unitaryGroup (h2 : IsLeftRegular (2 : R))
    (g : indefiniteUnitaryGroup p q R) :
    g ∈ (fromBlocksHom p q R).range ↔
      ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) ∈ unitaryGroup (p ⊕ q) R := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [val_fromBlocksHom, ← UnitaryGroup.coe_sum]
    exact (UnitaryGroup.sum x).property
  · intro hU
    rw [mem_range_fromBlocksHom_iff]
    set M : Matrix (p ⊕ q) (p ⊕ q) R := ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R)
    set J : Matrix (p ⊕ q) (p ⊕ q) R := indefiniteDiagonal p q R
    have hJM : Mᴴ * J * M = J := by
      simpa only [star_eq_conjTranspose] using mem_unitaryGroupOf_iff.1 g.property
    have hcomm : J * M = M * J := by
      have h1 : M * Mᴴ = 1 := (mem_unitaryGroup_iff).1 hU
      calc J * M = (M * Mᴴ) * J * M := by rw [h1, Matrix.one_mul]
        _ = M * (Mᴴ * J * M) := by simp only [Matrix.mul_assoc]
        _ = M * J := by rw [hJM]
    have h21 : (J * M).toBlocks₂₁ = (M * J).toBlocks₂₁ := congrArg Matrix.toBlocks₂₁ hcomm
    have hJblock : J = fromBlocks 1 0 0 (-1) := indefiniteDiagonal_eq_fromBlocks
    rw [← fromBlocks_toBlocks M, hJblock] at h21
    simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, toBlocks_fromBlocks₂₁] at h21
    ext i j
    have h2ij : (2 : R) * M.toBlocks₂₁ i j = (2 : R) * 0 := by
      rw [two_mul, mul_zero]
      exact eq_neg_iff_add_eq_zero.1 (congrFun (congrFun h21.symm i) j)
    exact h2 h2ij

end indefiniteUnitaryGroup

end CommRing

section Field

variable {p q} {K : Type*} [Field K] [StarRing K]

namespace indefiniteUnitaryGroup

variable [CharZero K]

/-- The off-diagonal entries of a central element of `U(p, q)` vanish: test its commutation with
the rank-one matrix of the basis vector `eₖ`. -/
private theorem apply_eq_zero_of_mem_center {g : indefiniteUnitaryGroup p q K}
    (hg : g ∈ Subgroup.center (indefiniteUnitaryGroup p q K)) {i k : p ⊕ q} (hik : i ≠ k) :
    ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) i k = 0 := by
  have hv :
      star (Pi.single k 1 : p ⊕ q → K) ⬝ᵥ indefiniteDiagonal p q K *ᵥ Pi.single k 1 ≠ 0 := by
    simpa [Pi.single_star, mulVec_single_one, single_one_dotProduct] using
      indefiniteDiagonal_apply_self_ne_zero k
  have h := unitaryGroupOf.mulVec_apply_mul_eq_of_mem_center isHermitian_indefiniteDiagonal
    hg hv i k
  simp only [mulVec_single, MulOpposite.op_one, Pi.smul_apply, col_apply, one_smul,
    Pi.star_single, star_one, single_vecMul, row_apply, smul_eq_mul, one_mul, ne_eq, hik,
    not_false_eq_true, Pi.single_eq_of_ne, zero_mul, mul_eq_zero] at h
  exact h.resolve_right (indefiniteDiagonal_apply_self_ne_zero k)

/-- The matrix of a central element of `U(p, q)` is diagonal. -/
private theorem eq_diagonal_of_mem_center {g : indefiniteUnitaryGroup p q K}
    (hg : g ∈ Subgroup.center (indefiniteUnitaryGroup p q K)) :
    ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) =
      diagonal fun i => ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) i i := by
  ext a b
  rcases eq_or_ne a b with rfl | hab
  · simp
  · simp [apply_eq_zero_of_mem_center hg hab, hab]

/-- The diagonal entries of a central element of `U(p, q)` agree: test its commutation with the
rank-one matrix of the non-isotropic vector `eᵢ + 2 eₖ`, whose value `J i i + 4 J k k` is one of
`±3`, `±5`. -/
private theorem apply_self_eq_of_mem_center {g : indefiniteUnitaryGroup p q K}
    (hg : g ∈ Subgroup.center (indefiniteUnitaryGroup p q K)) (i k : p ⊕ q) :
    ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) i i =
      ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) k k := by
  rcases eq_or_ne i k with rfl | hik
  · rfl
  set v : p ⊕ q → K := Pi.single i 1 + Pi.single k 2 with hv_def
  have hvi : v i = 1 := by simp [v, hik]
  have hvk : v k = 2 := by simp [v, hik.symm]
  have hsv : star v = v := by simp [v]
  have hv : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v ≠ 0 := by
    have hc : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v =
        indefiniteDiagonal p q K i i + 4 * indefiniteDiagonal p q K k k := by
      nth_rw 1 [hsv, hv_def]
      rw [add_dotProduct, single_dotProduct, single_dotProduct, indefiniteDiagonal_mulVec_apply,
        indefiniteDiagonal_mulVec_apply, hvi, hvk]
      ring
    rw [hc]
    rcases indefiniteDiagonal_apply_self_eq_one_or_eq_neg_one (p := p) (q := q) (R := K) i
      with h1 | h1 <;>
    rcases indefiniteDiagonal_apply_self_eq_one_or_eq_neg_one (p := p) (q := q) (R := K) k
      with h2 | h2 <;> rw [h1, h2] <;> norm_num
  have h := unitaryGroupOf.mulVec_apply_mul_eq_of_mem_center isHermitian_indefiniteDiagonal
    hg hv i k
  rw [eq_diagonal_of_mem_center hg, mulVec_diagonal, vecMul_diagonal, hsv,
    vecMul_indefiniteDiagonal_apply, hvi, hvk] at h
  apply mul_right_cancel₀ (mul_ne_zero two_ne_zero (indefiniteDiagonal_apply_self_ne_zero k))
  linear_combination h

/-- **The centre of `U(p, q)`**: over a field of characteristic zero, the elements of `U(p, q)`
commuting with all of `U(p, q)` are the unit scalars `λ • 1` with `star λ * λ = 1`. Over `ℂ`
these are the scalars of modulus one, and `PU(p, q)` is the quotient by them. -/
theorem center_eq_range_scalarHom :
    Subgroup.center (indefiniteUnitaryGroup p q K) =
      (unitaryGroupOf.scalarHom (indefiniteDiagonal p q K)).range := by
  refine le_antisymm (fun g hg => ?_) fun _ ⟨u, hu⟩ => hu ▸ Subgroup.mem_center_iff.mpr fun h =>
    unitaryGroupOf.ext <| by
      simp only [Subgroup.coe_mul, Units.val_mul, unitaryGroupOf.val_scalarHom]
      exact (scalar_commute _ (fun _ => Commute.all _ _) _).eq.symm
  rcases isEmpty_or_nonempty (p ⊕ q) with hn | ⟨⟨i₀⟩⟩
  · exact ⟨1, unitaryGroupOf.ext <| Subsingleton.elim _ _⟩
  set M : Matrix (p ⊕ q) (p ⊕ q) K := ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) with hMdef
  -- `M` is the scalar matrix of its corner entry `λ = M i₀ i₀`, and `star λ * λ = 1`.
  have hMs : M = scalar (p ⊕ q) (M i₀ i₀) := by
    rw [hMdef, eq_diagonal_of_mem_center hg, scalar_apply]
    exact congrArg diagonal (funext fun a => by simp [apply_self_eq_of_mem_center hg a i₀])
  have hu : M i₀ i₀ ∈ unitary K := by
    have h := congrFun (congrFun (mem_unitaryGroupOf_iff.mp g.property) i₀) i₀
    rw [← hMdef, hMs] at h
    simp only [scalar_apply, star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal,
      diagonal_mul, Pi.star_apply] at h
    rw [Unitary.mem_iff_star_mul_self]
    exact mul_right_cancel₀ (indefiniteDiagonal_apply_self_ne_zero i₀) (by linear_combination h)
  exact ⟨⟨_, hu⟩, unitaryGroupOf.ext <| by rw [unitaryGroupOf.val_scalarHom]; exact hMs.symm⟩

/-- **The centre of `U(p, q)` is cut out by the centre of the general linear group.** Over a field
of characteristic zero, an element of `U(p, q)` commutes with every element of `U(p, q)` exactly
when it commutes with every invertible matrix: both say that it is a scalar matrix. -/
theorem center_eq_comap_center :
    Subgroup.center (indefiniteUnitaryGroup p q K) =
      (Subgroup.center (GL (p ⊕ q) K)).comap (indefiniteUnitaryGroup p q K).subtype := by
  refine le_antisymm (fun g hg => ?_) fun g hg => Subgroup.mem_center_iff.mpr fun h =>
    Subtype.ext (Subgroup.mem_center_iff.mp hg h)
  rw [center_eq_range_scalarHom] at hg
  obtain ⟨u, rfl⟩ := hg
  exact Subgroup.mem_comap.mpr <| GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    ⟨u, (unitaryGroupOf.val_scalarHom (A := indefiniteDiagonal p q K) u).symm⟩

end indefiniteUnitaryGroup

end Field

end Matrix

end TauCeti
