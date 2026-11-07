/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.UnitaryGroup
import TauCeti.Analysis.Matrix.UnitaryGroup.Basic

/-!
# The projective special unitary group inside `PSL(n, 𝕜)`

A special unitary matrix has determinant one, so the special unitary group
`Matrix.specialUnitaryGroup n α` is a subgroup of the special linear group `SL(n, α)`
(`Matrix.specialUnitaryGroup.toSL`). Composing with the quotient map gives a homomorphism
`Matrix.specialUnitaryGroup.toPSL` to the projective special linear group
`PSL(n, α) = SL(n, α) ⧸ Z(SL(n, α))`. Its range is the projective special unitary group
`PSU(n)`, and its kernel consists of the special unitary matrices that are central in `SL(n, α)`.

Over `𝕜 = ℝ` or `ℂ` every central element of `SL(n, 𝕜)` is a scalar root of unity and hence
unitary, so a class in `PSL(n, 𝕜)` lies in `PSU(n)` exactly when one, equivalently every, matrix
representing it is unitary (`Matrix.specialUnitaryGroup.mk_mem_range_toPSL_iff`). For `n = 2` the
kernel of `toPSL` is `{1, -1}` (`Matrix.specialUnitaryGroup.mem_ker_toPSL_iff`), so
`PSU(2) = SU(2) ⧸ {±1}`. For `𝕜 = ℂ`, `PSU(2)` acts on the Riemann sphere by the Möbius
transformations commuting with its antipodal map (see
`TauCeti.Topology.Compactification.OnePoint.Antipode`), classically the rotations of the round
sphere.

## Main declarations

* `Matrix.specialUnitaryGroup.toSL`: the inclusion `SU(n) → SL(n)`.
* `Matrix.specialUnitaryGroup.toGL_toSL`: in `GL(n)`, it agrees with the unitary units.
* `Matrix.specialUnitaryGroup.toPSL`: the homomorphism `SU(n) → PSL(n)`, whose range is `PSU(n)`.
* `Matrix.specialUnitaryGroup.ker_toPSL`: its kernel is the preimage of the center of `SL(n)`.
* `Matrix.specialUnitaryGroup.mk_mem_range_toPSL_iff`: over `ℝ` or `ℂ`, the class of a matrix of
  `SL(n)` lies in `PSU(n)` exactly when the matrix is unitary.
* `Matrix.specialUnitaryGroup.mem_ker_toPSL_iff`: over a ring without zero divisors, such as
  `ℝ` or `ℂ`, the kernel of `SU(2) → PSL(2)` is `{1, -1}`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, Chapters 2 and 4 (unitary matrices and complex Möbius transformations).
-/

public section

open scoped MatrixGroups

namespace Matrix

namespace specialUnitaryGroup

variable {n : Type*} [DecidableEq n] [Fintype n] {α : Type*} [CommRing α] [StarRing α]

/-- The inclusion of the special unitary group into the special linear group: a special unitary
matrix has determinant one. -/
def toSL : specialUnitaryGroup n α →* SpecialLinearGroup n α where
  toFun A := ⟨A, (mem_specialUnitaryGroup_iff.mp A.2).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem coe_toSL (A : specialUnitaryGroup n α) :
    ((toSL A : SpecialLinearGroup n α) : Matrix n n α) = A :=
  (rfl)

/-- A special unitary matrix, viewed in `GL(n, α)`, is the unit of the corresponding unitary
matrix. -/
theorem toGL_toSL (A : specialUnitaryGroup n α) :
    SpecialLinearGroup.toGL (toSL A) =
      Unitary.toUnits (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A) :=
  Units.ext (rfl)

theorem toSL_injective : Function.Injective (toSL : specialUnitaryGroup n α →* _) :=
  fun A B h => Subtype.ext <| by
    simpa using congrArg (fun M : SpecialLinearGroup n α => (M : Matrix n n α)) h

/-- A matrix of the special linear group comes from the special unitary group exactly when it is
unitary. -/
theorem mem_range_toSL_iff {A : SpecialLinearGroup n α} :
    A ∈ (toSL : specialUnitaryGroup n α →* _).range ↔ (A : Matrix n n α) ∈ unitaryGroup n α := by
  refine ⟨?_, fun hA => ⟨⟨A, hA, A.2⟩, rfl⟩⟩
  rintro ⟨B, rfl⟩
  exact (mem_specialUnitaryGroup_iff.mp B.2).1

/-- The homomorphism from the special unitary group to the projective special linear group,
the inclusion into `SL(n, α)` followed by the quotient by its center. Its range is the projective
special unitary group `PSU(n)`. -/
def toPSL : specialUnitaryGroup n α →* ProjectiveSpecialLinearGroup n α :=
  (QuotientGroup.mk' _).comp toSL

@[simp]
theorem toPSL_apply (A : specialUnitaryGroup n α) :
    toPSL A = (toSL A : ProjectiveSpecialLinearGroup n α) :=
  (rfl)

/-- The kernel of `SU(n) → PSL(n)` consists of the special unitary matrices that are central in
the special linear group. -/
theorem ker_toPSL :
    (toPSL : specialUnitaryGroup n α →* _).ker =
      (Subgroup.center (SpecialLinearGroup n α)).comap toSL := by
  rw [toPSL, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']

/-- Over a ring without zero divisors, such as `ℝ` or `ℂ`, the kernel of `SU(2) → PSL(2)` is
`{1, -1}`, so that `PSU(2) = SU(2) ⧸ {±1}`. -/
theorem mem_ker_toPSL_iff [NoZeroDivisors α] {A : specialUnitaryGroup (Fin 2) α} :
    A ∈ (toPSL : specialUnitaryGroup (Fin 2) α →* _).ker ↔
      (A : Matrix (Fin 2) (Fin 2) α) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) α) = -1 := by
  rw [ker_toPSL, Subgroup.mem_comap, SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr' : r * r = 1 := by simpa [sq] using hr
    rcases mul_self_eq_one_iff.mp hr' with rfl | rfl
    · exact Or.inl (by rw [← coe_toSL A, ← hA, map_one])
    · exact Or.inr (by rw [← coe_toSL A, ← hA, map_neg, map_one])
  · rintro (hA | hA)
    · exact ⟨1, by simp, by rw [map_one, coe_toSL, hA]⟩
    · exact ⟨-1, by norm_num, by rw [map_neg, map_one, coe_toSL, hA]⟩

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Over `ℝ` or `ℂ` every central element of `SL(n, 𝕜)` is unitary: it is a scalar matrix whose
scalar is a root of unity, hence of norm one. -/
theorem center_le_range_toSL :
    Subgroup.center (SpecialLinearGroup n 𝕜) ≤ (toSL : specialUnitaryGroup n 𝕜 →* _).range := by
  intro A hA
  rw [mem_range_toSL_iff]
  obtain ⟨r, hr, hrA⟩ := SpecialLinearGroup.mem_center_iff.mp hA
  rw [← hrA]
  rcases isEmpty_or_nonempty n with hn | hn
  · exact mem_unitaryGroup_iff'.mpr (Subsingleton.elim _ _)
  have hnorm : ‖r‖ = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg r) (Fintype.card_ne_zero (α := n)), ← norm_pow,
      hr, norm_one]
  rw [scalar_apply, diagonal_mem_unitaryGroup_iff]
  exact fun _ => Unitary.mem_iff_star_mul_self.mpr <| by
    rw [RCLike.star_def, RCLike.conj_mul, hnorm]
    simp

/-- **The projective special unitary group.** Over `ℝ` or `ℂ`, the class in `PSL(n, 𝕜)` of a
matrix of `SL(n, 𝕜)` lies in the range `PSU(n)` of `SU(n)` exactly when the matrix is unitary. -/
theorem mk_mem_range_toPSL_iff {A : SpecialLinearGroup n 𝕜} :
    (A : ProjectiveSpecialLinearGroup n 𝕜) ∈ (toPSL : specialUnitaryGroup n 𝕜 →* _).range ↔
      (A : Matrix n n 𝕜) ∈ unitaryGroup n 𝕜 := by
  refine ⟨?_, fun hA => ⟨⟨A, hA, A.2⟩, rfl⟩⟩
  rintro ⟨B, hB⟩
  have hcen : (toSL B)⁻¹ * A ∈ (toSL : specialUnitaryGroup n 𝕜 →* _).range :=
    center_le_range_toSL (QuotientGroup.eq.mp hB)
  rw [← mem_range_toSL_iff, show A = toSL B * ((toSL B)⁻¹ * A) by group]
  exact mul_mem ⟨B, rfl⟩ hcen

end RCLike

end specialUnitaryGroup

end Matrix
