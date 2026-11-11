/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialUnitary
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary

/-!
# The orthogonal subgroup of the general linear group

For a commutative ring `R`, the **orthogonal group** of the standard symmetric bilinear form
`(x, y) ↦ ∑ i, x i * y i` on `n → R` consists of the invertible matrices `A` with `Aᵀ A = 1`.
This file defines it as a subgroup `TauCeti.GLOrthogonal n R` of `GL n R`: the fixed points of the
inverse-transpose automorphism `Matrix.GeneralLinearGroup.inverseTranspose`, `A ↦ (A⁻¹)ᵀ`.
Its subgroup of determinant one is the **special orthogonal group**
`TauCeti.GLSpecialOrthogonal n R`.

Over `ℂ` these are the complex orthogonal groups `O(n, ℂ)` and `SO(n, ℂ)`, and over `ℝ` the real
orthogonal groups `O(n)` and `SO(n)`. They are Mathlib's `Matrix.orthogonalGroup n R` and
`Matrix.specialOrthogonalGroup n R` read on units
(`TauCeti.GLOrthogonal.mem_iff_mem_orthogonalGroup` and
`TauCeti.GLSpecialOrthogonal.mem_iff_mem_specialOrthogonalGroup`). Mathlib defines those as
submonoids of matrices through the trivial star structure `starRingOfComm`, which differs from the
star structure of `ℂ`. The constructions that see a matrix group as a group of units, such as its
compact subgroups and the polar decomposition, need a subgroup of `GL n R` instead. Over a ring
whose own star is trivial, such as `ℝ`, the orthogonal group is the unitary subgroup
`unitarySubgroup (GL n R)` (`TauCeti.GLOrthogonal.eq_unitarySubgroup`), and the special
orthogonal group is `TauCeti.GLSpecialUnitary n R`. Over a Hausdorff topological ring both groups
are closed in `GL n R` (`TauCeti.GLOrthogonal.isClosed`).

This mirrors `TauCeti.GLSymplectic`, the units-level avatar of `Matrix.symplecticGroup`.

## Main definitions

* `TauCeti.GLOrthogonal`: the orthogonal group `{A | Aᵀ A = 1}` as a subgroup of `GL n R`.
* `TauCeti.GLSpecialOrthogonal`: its elements of determinant one.

## Main results

* `TauCeti.GLOrthogonal.mem_iff` and `TauCeti.GLOrthogonal.mem_iff'`: `A` is orthogonal exactly
  when `Aᵀ A = 1`, equivalently `A Aᵀ = 1`.
* `TauCeti.GLOrthogonal.mem_iff_mem_orthogonalGroup` and
  `TauCeti.GLSpecialOrthogonal.mem_iff_mem_specialOrthogonalGroup`: the two groups are Mathlib's
  matrix groups read on units.
* `TauCeti.GLOrthogonal.coe_inv`: an orthogonal matrix is inverted by its transpose.
* `TauCeti.GLOrthogonal.map_mem` and `TauCeti.GLSpecialOrthogonal.map_mem`: a ring homomorphism
  maps orthogonal and special orthogonal matrices to orthogonal and special orthogonal matrices.
* `TauCeti.GLOrthogonal.eq_unitarySubgroup` and `TauCeti.GLSpecialOrthogonal.eq_GLSpecialUnitary`:
  over a ring with trivial star, the orthogonal groups are the unitary ones.
* `TauCeti.GLOrthogonal.mem_unitarySubgroup_iff_map_star_eq`: an orthogonal matrix is unitary
  exactly when its entries are fixed by the star.
* `TauCeti.GLOrthogonal.isClosed` and `TauCeti.GLSpecialOrthogonal.isClosed`: both groups are
  closed.
-/

public section

open Matrix Matrix.GeneralLinearGroup

namespace TauCeti

variable (n : Type*) [Fintype n] [DecidableEq n] (R : Type*)

section CommSemiring

variable [CommSemiring R]

/-- **The orthogonal subgroup of the general linear group**: the invertible matrices `A` with
`Aᵀ A = 1`, the isometries of the standard symmetric bilinear form on `n → R`. It is defined as the
fixed locus of the inverse-transpose automorphism `A ↦ (A⁻¹)ᵀ`. -/
def GLOrthogonal : Subgroup (GL n R) :=
  MonoidHom.eqLocus (inverseTranspose : GL n R ≃* GL n R).toMonoidHom (MonoidHom.id _)

namespace GLOrthogonal

variable {n R}

/-- A matrix is orthogonal exactly when it is fixed by inverse transpose. -/
theorem mem_iff_inverseTranspose_eq {A : GL n R} :
    A ∈ GLOrthogonal n R ↔ inverseTranspose A = A :=
  Iff.rfl

/-- An orthogonal matrix is fixed by inverse transpose. -/
@[simp]
theorem inverseTranspose_eq {A : GL n R} (hA : A ∈ GLOrthogonal n R) : inverseTranspose A = A :=
  hA

/-- A matrix is orthogonal exactly when its transpose is its inverse. -/
theorem mem_iff_transpose_eq_inv {A : GL n R} :
    A ∈ GLOrthogonal n R ↔ (A : Matrix n n R)ᵀ = ((A⁻¹ : GL n R) : Matrix n n R) := by
  rw [mem_iff_inverseTranspose_eq, Units.ext_iff, coe_inverseTranspose]
  constructor
  · intro h
    rw [← h, transpose_transpose]
  · intro h
    rw [← h, transpose_transpose]

/-- **The orthogonality condition**: `A` is orthogonal exactly when `Aᵀ A = 1`. -/
theorem mem_iff {A : GL n R} : A ∈ GLOrthogonal n R ↔ (A : Matrix n n R)ᵀ * A = 1 := by
  rw [mem_iff_transpose_eq_inv]
  exact ⟨fun h ↦ h ▸ Units.inv_mul A, Units.eq_inv_of_mul_eq_one_right⟩

/-- The orthogonality condition from the other side: `A` is orthogonal exactly when `A Aᵀ = 1`. -/
theorem mem_iff' {A : GL n R} :
    A ∈ GLOrthogonal n R ↔ (A : Matrix n n R) * (A : Matrix n n R)ᵀ = 1 := by
  rw [mem_iff_transpose_eq_inv]
  exact ⟨fun h ↦ h ▸ Units.mul_inv A, Units.eq_inv_of_mul_eq_one_left⟩

/-- An orthogonal matrix is inverted by its transpose. -/
theorem coe_inv {A : GL n R} (hA : A ∈ GLOrthogonal n R) :
    ((A⁻¹ : GL n R) : Matrix n n R) = (A : Matrix n n R)ᵀ :=
  (mem_iff_transpose_eq_inv.mp hA).symm

/-- The carrier of the orthogonal group is the preimage, under the coercion of units, of the
matrices whose transpose is a left inverse. This is the form its closedness is read from. -/
theorem coe_eq_preimage :
    (GLOrthogonal n R : Set (GL n R)) =
      Units.val ⁻¹' {M : Matrix n n R | Mᵀ * M = 1} :=
  Set.ext fun _ ↦ mem_iff

/-- **The orthogonal group is closed** in `GL n R` over a Hausdorff topological semiring. -/
theorem isClosed [TopologicalSpace R] [IsTopologicalSemiring R] [T2Space R] :
    IsClosed (GLOrthogonal n R : Set (GL n R)) := by
  rw [coe_eq_preimage]
  exact (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id)
    continuous_const).preimage Units.continuous_val

end GLOrthogonal

end CommSemiring

section CommRing

variable [CommRing R]

namespace GLOrthogonal

variable {n R}

/-- An invertible matrix lies in the orthogonal subgroup exactly when its underlying matrix lies in
Mathlib's `Matrix.orthogonalGroup`. -/
@[simp]
theorem mem_iff_mem_orthogonalGroup {A : GL n R} :
    A ∈ GLOrthogonal n R ↔ (A : Matrix n n R) ∈ Matrix.orthogonalGroup n R := by
  rw [mem_iff, Matrix.mem_orthogonalGroup_iff']

variable {S : Type*} [CommRing S]

/-- **Change of scalars preserves orthogonality**: applying a ring homomorphism entrywise maps
orthogonal matrices to orthogonal matrices. -/
theorem map_mem (f : R →+* S) {A : GL n R} (hA : A ∈ GLOrthogonal n R) :
    Matrix.GeneralLinearGroup.map f A ∈ GLOrthogonal n S := by
  rw [mem_iff] at hA ⊢
  have hmap : ((Matrix.GeneralLinearGroup.map f A : GL n S) : Matrix n n S) =
      (A : Matrix n n R).map f := by
    simp
  rw [hmap, ← transpose_map, ← Matrix.map_mul, hA, Matrix.map_one _ f.map_zero f.map_one]

/-- Change of scalars maps the orthogonal group into the orthogonal group. -/
theorem map_le (f : R →+* S) :
    (GLOrthogonal n R).map (Matrix.GeneralLinearGroup.map f) ≤ GLOrthogonal n S := by
  rintro _ ⟨A, hA, rfl⟩
  exact map_mem f hA

/-- **Over a ring with trivial star, the orthogonal group is the unitary subgroup**: there the
star of a matrix is its transpose. -/
theorem eq_unitarySubgroup [StarRing R] [TrivialStar R] :
    GLOrthogonal n R = unitarySubgroup (GL n R) := by
  ext A
  rw [mem_iff', mem_unitarySubgroup_GL_iff]

/-- **An orthogonal matrix is unitary exactly when its entries are fixed by the star.** For
`Aᵀ A = 1`, the inverse of `A` is `Aᵀ`, so `A` is unitary exactly when `Aᴴ = Aᵀ`. Over `ℂ` this
says that `O(n, ℂ) ∩ U(n)` consists of the real orthogonal matrices. -/
theorem mem_unitarySubgroup_iff_map_star_eq [StarRing R] {A : GL n R}
    (hA : A ∈ GLOrthogonal n R) :
    A ∈ unitarySubgroup (GL n R) ↔ (A : Matrix n n R).map star = A := by
  have key : (A : Matrix n n R)ᴴ = (A : Matrix n n R)ᵀ ↔ (A : Matrix n n R).map star = A := by
    rw [← transpose_inj, conjTranspose_transpose, transpose_transpose]
  rw [mem_unitarySubgroup_GL_iff_mem_unitaryGroup, mem_unitaryGroup_iff', star_eq_conjTranspose,
    ← key]
  constructor
  · intro h
    calc (A : Matrix n n R)ᴴ = (A : Matrix n n R)ᴴ * (A * (A : Matrix n n R)ᵀ) := by
          rw [mem_iff'.mp hA, mul_one]
      _ = (A : Matrix n n R)ᵀ := by rw [← mul_assoc, h, one_mul]
  · intro h
    rw [h, mem_iff.mp hA]

end GLOrthogonal

/-- **The special orthogonal subgroup of the general linear group**: the orthogonal matrices of
determinant one. -/
def GLSpecialOrthogonal : Subgroup (GL n R) :=
  GLOrthogonal n R ⊓ MonoidHom.ker Matrix.GeneralLinearGroup.det

namespace GLSpecialOrthogonal

variable {n R}

/-- The special orthogonal group is cut out by two independent conditions: being orthogonal, and
having determinant one. -/
theorem eq_inf_ker_det :
    GLSpecialOrthogonal n R = GLOrthogonal n R ⊓ MonoidHom.ker Matrix.GeneralLinearGroup.det :=
  (rfl)

/-- An invertible matrix is special orthogonal exactly when it is orthogonal and has determinant
one. -/
theorem mem_iff {A : GL n R} :
    A ∈ GLSpecialOrthogonal n R ↔ A ∈ GLOrthogonal n R ∧ (A : Matrix n n R).det = 1 := by
  simp [eq_inf_ker_det, Units.ext_iff]

/-- An invertible matrix lies in the special orthogonal subgroup exactly when its underlying matrix
lies in Mathlib's `Matrix.specialOrthogonalGroup`. -/
@[simp]
theorem mem_iff_mem_specialOrthogonalGroup {A : GL n R} :
    A ∈ GLSpecialOrthogonal n R ↔ (A : Matrix n n R) ∈ Matrix.specialOrthogonalGroup n R := by
  rw [mem_iff, Matrix.mem_specialOrthogonalGroup_iff, GLOrthogonal.mem_iff_mem_orthogonalGroup]

/-- The special orthogonal group is contained in the orthogonal group. -/
theorem le_GLOrthogonal : GLSpecialOrthogonal n R ≤ GLOrthogonal n R :=
  inf_le_left

section map

variable {S : Type*} [CommRing S]

/-- **Change of scalars preserves special orthogonality**: applying a ring homomorphism entrywise
maps special orthogonal matrices to special orthogonal matrices. -/
theorem map_mem (f : R →+* S) {A : GL n R} (hA : A ∈ GLSpecialOrthogonal n R) :
    Matrix.GeneralLinearGroup.map f A ∈ GLSpecialOrthogonal n S := by
  rw [mem_iff] at hA ⊢
  refine ⟨GLOrthogonal.map_mem f hA.1, ?_⟩
  have hdet : ((Matrix.GeneralLinearGroup.map f A : GL n S) : Matrix n n S).det =
      f (A : Matrix n n R).det := by
    rw [RingHom.map_det]
    congr 1
  rw [hdet, hA.2, map_one]

/-- Change of scalars maps the special orthogonal group into the special orthogonal group. -/
theorem map_le (f : R →+* S) :
    (GLSpecialOrthogonal n R).map (Matrix.GeneralLinearGroup.map f) ≤ GLSpecialOrthogonal n S := by
  rintro _ ⟨A, hA, rfl⟩
  exact map_mem f hA

end map

/-- **Over a ring with trivial star, the special orthogonal group is the special unitary
group.** -/
theorem eq_GLSpecialUnitary [StarRing R] [TrivialStar R] :
    GLSpecialOrthogonal n R = GLSpecialUnitary n R := by
  rw [eq_inf_ker_det, GLOrthogonal.eq_unitarySubgroup,
    GLSpecialUnitary.eq_unitarySubgroup_inf_ker_det]

/-- **The special orthogonal group is closed** in `GL n R` over a Hausdorff topological ring. -/
theorem isClosed [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    IsClosed (GLSpecialOrthogonal n R : Set (GL n R)) := by
  have hdet : ((MonoidHom.ker Matrix.GeneralLinearGroup.det : Subgroup (GL n R)) : Set (GL n R)) =
      Units.val ⁻¹' {M : Matrix n n R | M.det = 1} := by
    ext A
    simp [Units.ext_iff]
  rw [eq_inf_ker_det, Subgroup.coe_inf, hdet]
  exact GLOrthogonal.isClosed.inter
    ((isClosed_eq continuous_id.matrix_det continuous_const).preimage Units.continuous_val)

end GLSpecialOrthogonal

end CommRing

end TauCeti
