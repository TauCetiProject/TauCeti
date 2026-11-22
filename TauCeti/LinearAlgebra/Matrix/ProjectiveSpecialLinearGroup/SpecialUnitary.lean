/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.UnitaryGroup
import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

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
representing it is unitary (`Matrix.specialUnitaryGroup.mk_mem_range_toPSL_iff`). Over `ℂ`, the
kernel of `toPSL` coincides with the center of `SU(n)`
(`Matrix.specialUnitaryGroup.ker_toPSL_eq_center`), which consists of the scalar matrices whose
scalar is a `card n`-th root of unity (`Matrix.specialUnitaryGroup.mem_center_iff`). (Over `ℝ`
this fails in dimension two, where `SO(2)` is abelian.) For `n = 2` the kernel of `toPSL` is
`{1, -1}` (`Matrix.specialUnitaryGroup.mem_ker_toPSL_iff`), so `PSU(2) = SU(2) ⧸ {±1}`. For
`𝕜 = ℂ`, `PSU(2)` acts on the Riemann sphere by the Möbius transformations commuting with its
antipodal map (see `TauCeti.Topology.Compactification.OnePoint.Antipode`), classically the
rotations of the round sphere.

## Main declarations

* `Matrix.specialUnitaryGroup.toSL`: the inclusion `SU(n) → SL(n)`.
* `Matrix.specialUnitaryGroup.toGL_toSL`: in `GL(n)`, it agrees with the unitary units.
* `Matrix.specialUnitaryGroup.toPSL`: the homomorphism `SU(n) → PSL(n)`, whose range is `PSU(n)`.
* `Matrix.specialUnitaryGroup.ker_toPSL`: its kernel is the preimage of the center of `SL(n)`.
* `Matrix.specialUnitaryGroup.scalarCenter` and `Matrix.specialUnitaryGroup.coe_scalarCenter`:
  over `ℝ` or `ℂ`, construct a central element of `SU(n)` from a `card n`-th root of unity.
* `Matrix.specialUnitaryGroup.mk_mem_range_toPSL_iff`: over `ℝ` or `ℂ`, the class of a matrix of
  `SL(n)` lies in `PSU(n)` exactly when the matrix is unitary.
* `Matrix.specialUnitaryGroup.mem_ker_toPSL_iff`: over a ring without zero divisors, such as
  `ℝ` or `ℂ`, the kernel of `SU(2) → PSL(2)` is `{1, -1}`.
* `Matrix.specialUnitaryGroup.ker_toPSL_eq_center` and `Matrix.specialUnitaryGroup.mem_center_iff`:
  over `ℂ`, the kernel of `SU(n) → PSL(n)` equals the center of `SU(n)`, consisting of the scalar
  matrices whose scalar is a `card n`-th root of unity.

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
  toFun A := ⟨A, (mem_specialUnitaryGroup_iff.mp A.property).2⟩
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
  refine ⟨?_, fun hA => ⟨⟨A, hA, A.property⟩, rfl⟩⟩
  rintro ⟨B, rfl⟩
  exact (mem_specialUnitaryGroup_iff.mp B.property).1

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

/-- The kernel of `SU(n) → PSL(n)` is always contained in the center of `SU(n)`. -/
theorem ker_toPSL_le_center :
    (toPSL : specialUnitaryGroup n α →* _).ker ≤ Subgroup.center (specialUnitaryGroup n α) := by
  rw [ker_toPSL]
  exact Subgroup.comap_center_le_center toSL_injective

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

/-- Construct a central special unitary matrix over `ℝ` or `ℂ` from a `card n`-th root of
unity `c`. -/
def scalarCenter {c : 𝕜} (hc : c ^ Fintype.card n = 1) :
    Subgroup.center (specialUnitaryGroup n 𝕜) :=
  ⟨⟨scalar n c, mem_specialUnitaryGroup_iff.mpr ⟨by
      rcases isEmpty_or_nonempty n with hn | hn
      · exact mem_unitaryGroup_iff'.mpr (Subsingleton.elim _ _)
      · have hnorm : ‖c‖ = 1 := by
          rw [← pow_eq_one_iff_of_nonneg (norm_nonneg c) (Fintype.card_ne_zero (α := n)),
            ← norm_pow, hc, norm_one]
        rw [scalar_apply, diagonal_mem_unitary, Pi.mem_unitary_iff]
        exact fun _ => Unitary.mem_iff_star_mul_self.mpr <| by
          rw [RCLike.star_def, RCLike.conj_mul, hnorm]
          simp,
      by simpa [scalar_apply, det_diagonal] using hc⟩⟩,
    Subgroup.mem_center_iff.mpr fun B => Subtype.ext <| by
      simpa [Submonoid.coe_mul, scalar_apply] using
        (scalar_commute c (Commute.all c) (B : Matrix n n 𝕜)).symm.eq⟩

/-- Coercing `scalarCenter hc` to a matrix yields the scalar matrix `scalar n c`. -/
@[simp]
theorem coe_scalarCenter {c : 𝕜} (hc : c ^ Fintype.card n = 1) :
    ((scalarCenter hc : specialUnitaryGroup n 𝕜) : Matrix n n 𝕜) = scalar n c :=
  (rfl)

/-- Over `ℝ` or `ℂ` every central element of `SL(n, 𝕜)` is unitary: it is a scalar matrix whose
scalar is a root of unity, hence of norm one. -/
theorem center_le_range_toSL :
    Subgroup.center (SpecialLinearGroup n 𝕜) ≤ (toSL : specialUnitaryGroup n 𝕜 →* _).range := by
  intro A hA
  obtain ⟨r, hr, hrA⟩ := SpecialLinearGroup.mem_center_iff.mp hA
  exact ⟨(scalarCenter hr : specialUnitaryGroup n 𝕜),
    Subtype.ext (by rw [coe_toSL, coe_scalarCenter, hrA])⟩

/-- **The projective special unitary group.** Over `ℝ` or `ℂ`, the class in `PSL(n, 𝕜)` of a
matrix of `SL(n, 𝕜)` lies in the range `PSU(n)` of `SU(n)` exactly when the matrix is unitary. -/
theorem mk_mem_range_toPSL_iff {A : SpecialLinearGroup n 𝕜} :
    (A : ProjectiveSpecialLinearGroup n 𝕜) ∈ (toPSL : specialUnitaryGroup n 𝕜 →* _).range ↔
      (A : Matrix n n 𝕜) ∈ unitaryGroup n 𝕜 := by
  refine ⟨?_, fun hA => ⟨⟨A, hA, A.property⟩, rfl⟩⟩
  rintro ⟨B, hB⟩
  have hcen : (toSL B)⁻¹ * A ∈ (toSL : specialUnitaryGroup n 𝕜 →* _).range :=
    center_le_range_toSL (QuotientGroup.eq.mp hB)
  rw [← mem_range_toSL_iff, show A = toSL B * ((toSL B)⁻¹ * A) by group]
  exact mul_mem ⟨B, rfl⟩ hcen

end RCLike

section Complex

/-- A diagonal test matrix in `SU(n, ℂ)` with `I` at `i`, `-I` at `j`, and `1` elsewhere. -/
private def diagITest {i j : n} (hij : i ≠ j) : specialUnitaryGroup n ℂ :=
  let d : n → ℂ := Function.update (Function.update (1 : n → ℂ) i Complex.I) j (-Complex.I)
  ⟨diagonal d, mem_specialUnitaryGroup_iff.mpr ⟨by
    rw [diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro k
    by_cases hkj : k = j
    · subst hkj; simp [d, Unitary.mem_iff]
    · by_cases hki : k = i
      · subst hki; simp [d, hkj, Unitary.mem_iff]
      · simp [d, hkj, hki], by
    rw [det_diagonal]
    have h1 := Finset.prod_update_of_mem (Finset.mem_univ j)
      (Function.update (1 : n → ℂ) i Complex.I) (-Complex.I)
    have h2 := Finset.prod_update_of_mem
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, Finset.notMem_singleton.mpr hij⟩)
      (1 : n → ℂ) Complex.I
    simp [d, h1, h2]⟩⟩

/-- A signed-swap test matrix in `SU(n, ℂ)` swapping `i` and `j` with a sign at `j`. -/
private def signedSwapTest {i j : n} (hij : i ≠ j) : specialUnitaryGroup n ℂ :=
  let Rmat : Matrix n n ℂ :=
    (Equiv.swap i j).permMatrix ℂ * diagonal (Function.update (1 : n → ℂ) j (-1))
  ⟨Rmat, mem_specialUnitaryGroup_iff.mpr ⟨
    Submonoid.mul_mem _ (permMatrix_mem_unitary _)
      (diagonal_update_one_mem_unitary_iff.mpr (by simp [Unitary.mem_iff])), by
    rw [det_mul, det_permutation, Equiv.Perm.sign_swap hij, det_diagonal,
      Finset.prod_update_of_mem (Finset.mem_univ j)]
    simp⟩⟩

/-- Over `ℂ`, the kernel of `SU(n) → PSL(n)` coincides with the center of `SU(n)`. -/
theorem ker_toPSL_eq_center :
    (toPSL : specialUnitaryGroup n ℂ →* _).ker = Subgroup.center (specialUnitaryGroup n ℂ) := by
  refine le_antisymm ker_toPSL_le_center fun A hA => ?_
  rw [ker_toPSL, Subgroup.mem_comap, SpecialLinearGroup.mem_center_iff]
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · exact ⟨1, by simp, Subsingleton.elim _ _⟩
  have hdiag : (A : Matrix n n ℂ).IsDiag := fun i j hij => by
    have hcomm : Commute ((diagITest hij : specialUnitaryGroup n ℂ) : Matrix n n ℂ) A :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hA (diagITest hij))
    refine TauCeti.apply_eq_zero_of_commute_diagonal hcomm ?_
    simp [hij, Complex.ext_iff]
    norm_num
  have hconst : ∀ i : n, (A : Matrix n n ℂ) i i = (A : Matrix n n ℂ) i₀ i₀ := fun i => by
    by_cases hi : i = i₀
    · rw [hi]
    have hcomm : ((signedSwapTest hi : specialUnitaryGroup n ℂ) : Matrix n n ℂ) * A =
        A * ((signedSwapTest hi : specialUnitaryGroup n ℂ) : Matrix n n ℂ) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hA (signedSwapTest hi))
    have hentry := congr_fun₂ hcomm i i₀
    rw [← hdiag.diagonal_diag] at hentry
    have hR : ((signedSwapTest hi : specialUnitaryGroup n ℂ) : Matrix n n ℂ) i i₀ = -1 := by
      simp [signedSwapTest, mul_diagonal, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
        Equiv.toPEquiv_apply]
    simpa [mul_diagonal, diagonal_mul, hR] using hentry.symm
  have hscalar : scalar n ((A : Matrix n n ℂ) i₀ i₀) = (A : Matrix n n ℂ) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [scalar_apply, hconst a]
    · simp [scalar_apply, hab, hdiag hab]
  refine ⟨(A : Matrix n n ℂ) i₀ i₀, ?_, by rw [coe_toSL, hscalar]⟩
  have hdet := congrArg Matrix.det hscalar
  simpa [scalar_apply, det_diagonal, (mem_specialUnitaryGroup_iff.mp A.property).2] using hdet

/-- **The center of `SU(n, ℂ)`.** A special unitary matrix over `ℂ` is central in `SU(n)` exactly
when it is a scalar matrix whose scalar is a `card n`-th root of unity. -/
theorem mem_center_iff {A : specialUnitaryGroup n ℂ} :
    A ∈ Subgroup.center (specialUnitaryGroup n ℂ) ↔
      ∃ c : ℂ, c ^ Fintype.card n = 1 ∧ scalar n c = (A : Matrix n n ℂ) := by
  rw [← ker_toPSL_eq_center, ker_toPSL, Subgroup.mem_comap, SpecialLinearGroup.mem_center_iff,
    coe_toSL]

end Complex

end specialUnitaryGroup

end Matrix
