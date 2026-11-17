/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Algebra.Star.Unitary
import TauCeti.Analysis.Matrix.UnitaryGroup.Weyl
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.Logic.Equiv.Fin.Basic
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Center, diagonalization, and clock-and-shift matrices in `SU(n)`

Over `ℂ`, the center of the special unitary group `SU(n) = Matrix.specialUnitaryGroup n ℂ`
consists of the scalar matrices `scalar n c` with `c ^ card n = 1`
(`Matrix.specialUnitaryGroup.mem_center_iff`), matching the center of `SL(n, ℂ)`. Consequently an
element of `SU(n)` is central in `SU(n)` precisely when its image in `SL(n, ℂ)` is central
(`Matrix.specialUnitaryGroup.toSL_mem_center_iff`), the kernel of `SU(n) → PSL(n, ℂ)` is the
center of `SU(n)` (`Matrix.specialUnitaryGroup.ker_toPSL_eq_center`), and for `0 < r` the center of
`SU(r)` is canonically isomorphic to `rootsOfUnity r ℂ`
(`Matrix.specialUnitaryGroup.centerMulEquivRootsOfUnityFin`). Complex scalars are essential here:
over `ℝ`, `specialUnitaryGroup (Fin 2) ℝ` is `SO(2)`, which is commutative, so the quarter turn
`!![0, -1; 1, 0]` is central without being scalar.

Every element of `SU(n)` is also diagonalized by conjugation inside `SU(n)`
(`Matrix.specialUnitaryGroup.exists_conj_eq_diagonal`): conjugating into the diagonal torus of
`U(n)` (`TauCeti.exists_conj_mem_unitaryTorus`) and rescaling the conjugating unitary matrix by a
point of the unit circle (`Matrix.exists_circle_smul_mem_specialUnitaryGroup`) gives a conjugator
of determinant one without changing the conjugate.

For any `r`-th root of unity `ζ`, rescaling the diagonal clock matrix `diag(1, ζ, …, ζ^(r - 1))`
and the cyclic-shift permutation matrix into `SU(r)` yields the Weyl clock-and-shift pair
(`Matrix.specialUnitaryGroup.clock`, `Matrix.specialUnitaryGroup.shift`) satisfying the twisted
commutator relation `⁅clock hζ, shift r⁆ = ζ • 1`
(`Matrix.specialUnitaryGroup.commutator_clock_shift`). When `ζ` is a primitive `r`-th root of
unity, every pair `A, B ∈ SU(r)` with `⁅A, B⁆ = ζ • 1` is simultaneously conjugate in `SU(r)` to
`(clock hζ.pow_eq_one, shift r)` (`Matrix.specialUnitaryGroup.exists_conj_eq_clock_shift`).

## Main definitions

* `Matrix.specialUnitaryGroup.centerMulEquivCenterSL`: the isomorphism between the centers of
  `SU(n)` and `SL(n, ℂ)` induced by `toSL`.
* `Matrix.specialUnitaryGroup.centerMulEquivRootsOfUnityFin`: for `0 < r`, the isomorphism
  `Subgroup.center (specialUnitaryGroup (Fin r) ℂ) ≃* rootsOfUnity r ℂ`.
* `Matrix.specialUnitaryGroup.clock`, `Matrix.specialUnitaryGroup.shift`: the rescaled Weyl clock
  and cyclic-shift matrices in `SU(r)`.

## Main results

* `Matrix.specialUnitaryGroup.mem_center_iff`: over `ℂ`, `g` lies in the center of `SU(n)` iff
  `g = scalar n c` for some `c` with `c ^ card n = 1`.
* `Matrix.specialUnitaryGroup.toSL_mem_center_iff`,
  `Matrix.specialUnitaryGroup.comap_toSL_center`,
  `Matrix.specialUnitaryGroup.ker_toPSL_eq_center`: the center of `SU(n)` is the preimage of the
  center of `SL(n, ℂ)` and equals the kernel of `toPSL`.
* `Matrix.specialUnitaryGroup.exists_conj_eq_diagonal`: every element of `SU(n)` is conjugate in
  `SU(n)` to a diagonal matrix with entries on the unit circle.
* `Matrix.specialUnitaryGroup.exists_coe_clock`, `Matrix.specialUnitaryGroup.exists_coe_shift`,
  `Matrix.specialUnitaryGroup.commutator_clock_shift`: matrix descriptions of `clock` and `shift`
  and their Weyl commutation relation `⁅clock hζ, shift r⁆ = ζ • 1`.
* `Matrix.specialUnitaryGroup.exists_conj_eq_clock_shift`: when `IsPrimitiveRoot ζ r`, every pair
  `A, B ∈ SU(r)` with `⁅A, B⁆ = ζ • 1` is simultaneously conjugate in `SU(r)` to
  `(clock hζ.pow_eq_one, shift r)`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222
  (2015), Chapter 1.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, §1.
-/

public section

namespace Matrix.specialUnitaryGroup

section Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A central element of `SU(n)` over `ℂ` is diagonal: for any `i ≠ j`, the diagonal matrix with
`I` at `i`, `-I` at `j`, and `1` elsewhere lies in `SU(n)` and separates `i` from `j`. -/
private theorem isDiag_of_mem_center {g : specialUnitaryGroup n ℂ}
    (hg : g ∈ Subgroup.center (specialUnitaryGroup n ℂ)) :
    (g : Matrix n n ℂ).IsDiag := by
  intro i j hij
  let cI : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩
  let z : n → Circle := Pi.mulSingle i cI * Pi.mulSingle j cI⁻¹
  have hprod : ∏ k, z k = 1 := by
    simp only [z, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', mul_inv_cancel]
  have hdet : (TauCeti.unitaryTorusHom n z : Matrix n n ℂ).det = 1 := by
    rw [TauCeti.det_unitaryTorusHom, hprod, Circle.coe_one]
  let u : specialUnitaryGroup n ℂ :=
    ⟨TauCeti.unitaryTorusHom n z,
      mem_specialUnitaryGroup_iff.mpr ⟨(TauCeti.unitaryTorusHom n z).2, hdet⟩⟩
  have hcomm : Commute (diagonal fun k => (z k : ℂ)) (g : Matrix n n ℂ) := by
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hg u)
    rw [Submonoid.coe_mul, Submonoid.coe_mul] at h
    dsimp only [u] at h
    rwa [TauCeti.coe_unitaryTorusHom] at h
  have hzi : z i = cI := by
    simp [z, Pi.mulSingle_eq_of_ne hij]
  have hzj : z j = cI⁻¹ := by
    simp [z, Pi.mulSingle_eq_of_ne hij.symm]
  refine TauCeti.apply_eq_zero_of_commute_diagonal hcomm ?_
  rw [hzi, hzj, Circle.coe_inv]
  dsimp only [cI]
  rw [Complex.inv_I]
  intro hI
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination hI
  exact mul_ne_zero two_ne_zero Complex.I_ne_zero h2

/-- Any two diagonal entries of a central element of `SU(n)` over `ℂ` coincide: for `i ≠ j`,
multiplying the transposition matrix of `swap i j` by `diag(-1, 1, …)` at `i` gives an element of
`SU(n)` that conjugates one entry to the other. -/
private theorem diag_eq_of_mem_center {g : specialUnitaryGroup n ℂ}
    (hg : g ∈ Subgroup.center (specialUnitaryGroup n ℂ)) (i j : n) :
    (g : Matrix n n ℂ) i i = (g : Matrix n n ℂ) j j := by
  by_cases hij : i = j
  · rw [hij]
  let z : n → Circle := Pi.mulSingle i (-1)
  let U : unitaryGroup n ℂ := TauCeti.unitaryTorusHom n z * permutationUnitary (Equiv.swap i j)
  have hprod : ∏ k, z k = -1 := by
    simp only [z, Fintype.prod_pi_mulSingle']
  have hdet : (U : Matrix n n ℂ).det = 1 := by
    rw [Submonoid.coe_mul, det_mul, TauCeti.det_unitaryTorusHom, hprod,
      coe_permutationUnitary, Equiv.swap_inv, det_permutation, Equiv.Perm.sign_swap hij]
    norm_num
  let u : specialUnitaryGroup n ℂ := ⟨U, mem_specialUnitaryGroup_iff.mpr ⟨U.2, hdet⟩⟩
  have hdiag := (isDiag_of_mem_center hg).diagonal_diag
  have hmat :
      (U : Matrix n n ℂ) * (g : Matrix n n ℂ) = (g : Matrix n n ℂ) * (U : Matrix n n ℂ) := by
    simpa only [Submonoid.coe_mul] using congrArg Subtype.val (Subgroup.mem_center_iff.mp hg u)
  rw [← hdiag] at hmat
  have hcomm := congr_fun₂ hmat i j
  rw [mul_diagonal, diagonal_mul] at hcomm
  have huij : (U : Matrix n n ℂ) i j = -1 := by
    rw [Submonoid.coe_mul, TauCeti.coe_unitaryTorusHom, coe_permutationUnitary, Equiv.swap_inv,
      diagonal_mul]
    simp [z, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  rw [huij, diag_apply, diag_apply] at hcomm
  linear_combination hcomm

/-- **Center of `SU(n)` over `ℂ`.** A special unitary matrix lies in the center of `SU(n)`
precisely when it is a scalar matrix whose scalar is a `card n`-th root of unity. -/
theorem mem_center_iff {g : specialUnitaryGroup n ℂ} :
    g ∈ Subgroup.center (specialUnitaryGroup n ℂ) ↔
      ∃ c : ℂ, c ^ Fintype.card n = 1 ∧ scalar n c = (g : Matrix n n ℂ) := by
  refine ⟨fun hg => ?_, fun ⟨c, _, hc⟩ => mem_center_of_coe_eq_scalar hc.symm⟩
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · exact ⟨1, by simp, Subsingleton.elim _ _⟩
  have hscal : scalar n ((g : Matrix n n ℂ) i₀ i₀) = (g : Matrix n n ℂ) := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simpa using (diag_eq_of_mem_center hg i i₀).symm
    · simp [scalar_apply, diagonal_apply_ne _ hij, isDiag_of_mem_center hg hij]
  refine ⟨(g : Matrix n n ℂ) i₀ i₀, ?_, hscal⟩
  have hdet := (mem_specialUnitaryGroup_iff.mp g.2).2
  rwa [← hscal, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ] at hdet

/-- Over `ℂ`, an element of `SU(n)` maps into the center of `SL(n, ℂ)` precisely when it lies in
the center of `SU(n)`. -/
@[simp]
theorem toSL_mem_center_iff {g : specialUnitaryGroup n ℂ} :
    toSL g ∈ Subgroup.center (SpecialLinearGroup n ℂ) ↔
      g ∈ Subgroup.center (specialUnitaryGroup n ℂ) := by
  rw [SpecialLinearGroup.mem_center_iff, mem_center_iff, coe_toSL]

/-- Over `ℂ`, the preimage of the center of `SL(n, ℂ)` in `SU(n)` is the center of `SU(n)`. -/
@[simp]
theorem comap_toSL_center :
    (Subgroup.center (SpecialLinearGroup n ℂ)).comap (toSL (n := n) (α := ℂ)) =
      Subgroup.center (specialUnitaryGroup n ℂ) := by
  ext g
  exact toSL_mem_center_iff

/-- Over `ℂ`, the kernel of `toPSL : SU(n) →* PSL(n, ℂ)` is the center of `SU(n)`. -/
@[simp]
theorem ker_toPSL_eq_center :
    (toPSL : specialUnitaryGroup n ℂ →* ProjectiveSpecialLinearGroup n ℂ).ker =
      Subgroup.center (specialUnitaryGroup n ℂ) := by
  rw [ker_toPSL, comap_toSL_center]

/-- The inclusion `toSL : SU(n) →* SL(n, ℂ)` restricts to an isomorphism between the centers of
`SU(n)` and `SL(n, ℂ)`. -/
noncomputable def centerMulEquivCenterSL :
    Subgroup.center (specialUnitaryGroup n ℂ) ≃* Subgroup.center (SpecialLinearGroup n ℂ) :=
  MulEquiv.ofBijective
    ((toSL.comp (Subgroup.center (specialUnitaryGroup n ℂ)).subtype).codRestrict
      (Subgroup.center (SpecialLinearGroup n ℂ)) fun g => toSL_mem_center_iff.mpr g.2)
    ⟨fun a b h => Subtype.ext <| toSL_injective (congrArg Subtype.val h), fun z => by
      obtain ⟨g, hg⟩ := center_le_range_toSL z.2
      exact ⟨⟨g, toSL_mem_center_iff.mp (hg.symm ▸ z.2)⟩, Subtype.ext hg⟩⟩

/-- `centerMulEquivCenterSL` acts on elements by applying `toSL`. -/
@[simp]
theorem coe_centerMulEquivCenterSL_apply (z : Subgroup.center (specialUnitaryGroup n ℂ)) :
    (centerMulEquivCenterSL z : SpecialLinearGroup n ℂ) = toSL z.1 :=
  (rfl)

/-- Applying `toSL` after `centerMulEquivCenterSL.symm` recovers the underlying element of
`SL(n, ℂ)`. -/
@[simp]
theorem toSL_coe_centerMulEquivCenterSL_symm (z : Subgroup.center (SpecialLinearGroup n ℂ)) :
    toSL ((centerMulEquivCenterSL.symm z : Subgroup.center (specialUnitaryGroup n ℂ)) :
      specialUnitaryGroup n ℂ) = z.1 :=
  congrArg Subtype.val (centerMulEquivCenterSL.apply_symm_apply z)

/-- For `0 < r`, the center of `SU(r)` is canonically isomorphic to the group of `r`-th roots of
unity in `ℂ`. -/
noncomputable def centerMulEquivRootsOfUnityFin (r : ℕ) (hr : 0 < r) :
    Subgroup.center (specialUnitaryGroup (Fin r) ℂ) ≃* rootsOfUnity r ℂ :=
  centerMulEquivCenterSL.trans (SpecialLinearGroup.centerMulEquivRootsOfUnityFin r hr ℂ)

/-- `centerMulEquivRootsOfUnityFin` reads off the `(0, 0)` matrix entry of a central element of
`SU(r)`. -/
@[simp]
theorem coe_centerMulEquivRootsOfUnityFin_apply (r : ℕ) (hr : 0 < r)
    (z : Subgroup.center (specialUnitaryGroup (Fin r) ℂ)) :
    (((centerMulEquivRootsOfUnityFin r hr z : rootsOfUnity r ℂ) : ℂˣ) : ℂ) =
      (z.1 : Matrix (Fin r) (Fin r) ℂ) ⟨0, hr⟩ ⟨0, hr⟩ := by
  simp [centerMulEquivRootsOfUnityFin]

/-- The inverse of `centerMulEquivRootsOfUnityFin` sends an `r`-th root of unity `ζ` to the scalar
matrix `scalar (Fin r) ζ`. -/
@[simp]
theorem coe_centerMulEquivRootsOfUnityFin_symm_apply (r : ℕ) (hr : 0 < r)
    (ζ : rootsOfUnity r ℂ) :
    (((centerMulEquivRootsOfUnityFin r hr).symm ζ :
        Subgroup.center (specialUnitaryGroup (Fin r) ℂ)) : Matrix (Fin r) (Fin r) ℂ) =
      scalar (Fin r) ((ζ : ℂˣ) : ℂ) := by
  rw [← coe_toSL, centerMulEquivRootsOfUnityFin, MulEquiv.symm_trans_apply,
    toSL_coe_centerMulEquivCenterSL_symm]
  exact SpecialLinearGroup.coe_centerMulEquivRootsOfUnityFin_symm_apply r hr ℂ ζ

/-- **Diagonalization in `SU(n)`.** Every element of `SU(n)` is conjugate inside `SU(n)` to a
diagonal matrix with entries on the unit circle: conjugating into the diagonal torus of `U(n)` and
rescaling the conjugator by a circle scalar gives a conjugator in `SU(n)` with the same
conjugate. -/
theorem exists_conj_eq_diagonal (g : specialUnitaryGroup n ℂ) :
    ∃ (u : specialUnitaryGroup n ℂ) (z : n → Circle),
      ((u * g * u⁻¹ : specialUnitaryGroup n ℂ) : Matrix n n ℂ) =
        diagonal fun i => (z i : ℂ) := by
  let gU : unitaryGroup n ℂ := ⟨g, specialUnitaryGroup_le_unitaryGroup g.2⟩
  obtain ⟨U, hU⟩ := TauCeti.exists_conj_mem_unitaryTorus gU
  obtain ⟨z, hz⟩ := TauCeti.mem_unitaryTorus_iff_exists_unitaryTorusHom.mp hU
  obtain ⟨c, hc⟩ := exists_circle_smul_mem_specialUnitaryGroup U
  refine ⟨⟨(c : ℂ) • (U : Matrix n n ℂ), hc⟩, z, ?_⟩
  have hcoe : (((⟨(c : ℂ) • (U : Matrix n n ℂ), hc⟩ * g *
      (⟨(c : ℂ) • (U : Matrix n n ℂ), hc⟩)⁻¹ : specialUnitaryGroup n ℂ)) : Matrix n n ℂ) =
      ((U * gU * U⁻¹ : unitaryGroup n ℂ) : Matrix n n ℂ) := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_inv, Submonoid.coe_mul, Submonoid.coe_mul,
      ← Unitary.star_eq_inv, Unitary.coe_star]
    exact Unitary.smul_mul_mul_star_smul c.coe_mem_unitary (U : Matrix n n ℂ) (g : Matrix n n ℂ)
  rw [hcoe, ← hz, TauCeti.coe_unitaryTorusHom]

/-! ### Clock-and-shift matrices in `SU(r)` -/

/-- The diagonal unitary clock matrix `diag(1, ζ, …, ζ^(r - 1))` in `U(r)` for an `r`-th root of
unity `ζ`. -/
private noncomputable def clockUnitary {r : ℕ} {ζ : ℂ} (hζ : ζ ^ r = 1) :
    unitaryGroup (Fin r) ℂ :=
  TauCeti.unitaryTorusHom (Fin r) fun k =>
    ⟨ζ ^ (k : ℕ), mem_sphere_zero_iff_norm.mpr <| by
      rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hζ (Nat.ne_zero_of_lt k.isLt), one_pow]⟩

/-- A special unitary clock matrix in `SU(r)` associated to an `r`-th root of unity `ζ`: a
unit-circle rescaling of `diag(1, ζ, …, ζ^(r - 1))` into `SU(r)`. Together with
`Matrix.specialUnitaryGroup.shift`, it satisfies `⁅clock hζ, shift r⁆ = ζ • 1`
(`Matrix.specialUnitaryGroup.commutator_clock_shift`). -/
noncomputable def clock {r : ℕ} {ζ : ℂ} (hζ : ζ ^ r = 1) : specialUnitaryGroup (Fin r) ℂ :=
  ⟨((exists_circle_smul_mem_specialUnitaryGroup (clockUnitary hζ)).choose : ℂ) •
      (clockUnitary hζ : Matrix (Fin r) (Fin r) ℂ),
    (exists_circle_smul_mem_specialUnitaryGroup (clockUnitary hζ)).choose_spec⟩

/-- A special unitary cyclic-shift matrix in `SU(r)`: a unit-circle rescaling of the permutation
matrix `permutationUnitary (finRotate r)` into `SU(r)`. Together with
`Matrix.specialUnitaryGroup.clock`, it satisfies `⁅clock hζ, shift r⁆ = ζ • 1`
(`Matrix.specialUnitaryGroup.commutator_clock_shift`). -/
noncomputable def shift (r : ℕ) : specialUnitaryGroup (Fin r) ℂ :=
  ⟨((exists_circle_smul_mem_specialUnitaryGroup
        (permutationUnitary (R := ℂ) (finRotate r))).choose : ℂ) •
      ((permutationUnitary (R := ℂ) (finRotate r) : unitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ),
    (exists_circle_smul_mem_specialUnitaryGroup
      (permutationUnitary (R := ℂ) (finRotate r))).choose_spec⟩

/-- As a matrix, `clock hζ` is a unit-circle scalar multiple of `diag(1, ζ, …, ζ^(r - 1))`. -/
theorem exists_coe_clock {r : ℕ} {ζ : ℂ} (hζ : ζ ^ r = 1) :
    ∃ c : Circle,
      (clock hζ : Matrix (Fin r) (Fin r) ℂ) =
        (c : ℂ) • diagonal (fun k : Fin r => ζ ^ (k : ℕ)) :=
  ⟨(exists_circle_smul_mem_specialUnitaryGroup (clockUnitary hζ)).choose,
    congrArg (((exists_circle_smul_mem_specialUnitaryGroup (clockUnitary hζ)).choose : ℂ) • ·)
      (TauCeti.coe_unitaryTorusHom _)⟩

/-- As a matrix, `shift r` is a unit-circle scalar multiple of the cyclic-shift permutation matrix
`permutationUnitary (finRotate r)`. -/
theorem exists_coe_shift (r : ℕ) :
    ∃ c : Circle,
      (shift r : Matrix (Fin r) (Fin r) ℂ) =
        (c : ℂ) • ((permutationUnitary (R := ℂ) (finRotate r) : unitaryGroup (Fin r) ℂ) :
          Matrix (Fin r) (Fin r) ℂ) :=
  ⟨(exists_circle_smul_mem_specialUnitaryGroup
    (permutationUnitary (R := ℂ) (finRotate r))).choose, rfl⟩

open scoped commutatorElement in
/-- **Weyl clock-and-shift commutation relation in `SU(r)`.** For any `r`-th root of unity `ζ`,
the special unitary clock and shift matrices satisfy `⁅clock hζ, shift r⁆ = ζ • 1`. -/
theorem commutator_clock_shift {r : ℕ} {ζ : ℂ} (hζ : ζ ^ r = 1) :
    (↑⁅clock hζ, shift r⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
  let DU : unitaryGroup (Fin r) ℂ := clockUnitary hζ
  let QU : unitaryGroup (Fin r) ℂ := permutationUnitary (finRotate r)
  have hrel : (DU : Matrix (Fin r) (Fin r) ℂ) * QU =
      ζ • ((QU : Matrix (Fin r) (Fin r) ℂ) * DU) := by
    have hDU : (DU : Matrix (Fin r) (Fin r) ℂ) = diagonal fun k : Fin r => ζ ^ (k : ℕ) :=
      TauCeti.coe_unitaryTorusHom _
    rw [hDU, coe_permutationUnitary]
    ext i j
    simp only [diagonal_mul, Matrix.smul_apply, mul_diagonal, smul_eq_mul,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq]
    by_cases h : (finRotate r)⁻¹ i = j
    · have hi : i = finRotate r j := by rw [← h, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      simp only [h, ↓reduceIte, mul_one, one_mul]
      rw [hi, TauCeti.pow_val_finRotate hζ]
    · simp only [h, ↓reduceIte, mul_zero, zero_mul]
  have hDU_mul : (DU : Matrix (Fin r) (Fin r) ℂ) * star (DU : Matrix (Fin r) (Fin r) ℂ) = 1 :=
    (Unitary.mem_iff.mp DU.2).2
  have hQU_mul : (QU : Matrix (Fin r) (Fin r) ℂ) * star (QU : Matrix (Fin r) (Fin r) ℂ) = 1 :=
    (Unitary.mem_iff.mp QU.2).2
  calc (↑⁅clock hζ, shift r⁆ : Matrix (Fin r) (Fin r) ℂ)
      = (DU : Matrix (Fin r) (Fin r) ℂ) * (QU : Matrix (Fin r) (Fin r) ℂ) *
          star (DU : Matrix (Fin r) (Fin r) ℂ) * star (QU : Matrix (Fin r) (Fin r) ℂ) :=
        coe_commutatorElement_of_eq_smul
          (exists_circle_smul_mem_specialUnitaryGroup DU).choose.coe_mem_unitary
          (exists_circle_smul_mem_specialUnitaryGroup QU).choose.coe_mem_unitary
          (A := clock hζ) (B := shift r) rfl rfl
    _ = ζ • ((QU : Matrix (Fin r) (Fin r) ℂ) *
          ((DU : Matrix (Fin r) (Fin r) ℂ) * star (DU : Matrix (Fin r) (Fin r) ℂ)) *
          star (QU : Matrix (Fin r) (Fin r) ℂ)) := by
        rw [hrel, smul_mul_assoc, smul_mul_assoc, Matrix.mul_assoc (QU : Matrix (Fin r) (Fin r) ℂ)]
    _ = ζ • 1 := by rw [hDU_mul, Matrix.mul_one, hQU_mul]

/-- If `diagonal z * B₁ = ζ • (B₁ * diagonal z)` with `B₁ ∈ SU(r)`, `1 ≤ r`, and
`IsPrimitiveRoot ζ r`, the diagonal entries `z` are a permutation of `ζ ^ k * μ` (`μ ≠ 0`). -/
private theorem exists_perm_pow_eq_of_mul_eq_smul_mul {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) (z : Fin r → Circle) (B₁ : specialUnitaryGroup (Fin r) ℂ)
    (hrel : diagonal (fun i => (z i : ℂ)) * (B₁ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * diagonal (fun i => (z i : ℂ)))) :
    ∃ (σ : Equiv.Perm (Fin r)) (μ : ℂ), μ ≠ 0 ∧ ∀ k : Fin r, (z (σ k) : ℂ) = ζ ^ (k : ℕ) * μ := by
  have hstep : ∀ j : Fin r, ∃ i : Fin r, (z i : ℂ) = ζ * (z j : ℂ) := fun j => by
    have hcol : ∃ i : Fin r, (B₁ : Matrix (Fin r) (Fin r) ℂ) i j ≠ 0 := by
      by_contra! hall
      have hB₁U : (B₁ : Matrix (Fin r) (Fin r) ℂ) ∈ unitary (Matrix (Fin r) (Fin r) ℂ) :=
        (mem_specialUnitaryGroup_iff.mp B₁.2).1
      have hunit := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M j j)
        (Unitary.mem_iff.mp hB₁U).1
      simp [Matrix.mul_apply, hall] at hunit
    obtain ⟨i, hij⟩ := hcol
    have hent := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M i j) hrel
    rw [diagonal_mul, Matrix.smul_apply, mul_diagonal, smul_eq_mul] at hent
    refine ⟨i, sub_eq_zero.mp ((mul_eq_zero.mp ?_).resolve_right hij)⟩
    linear_combination hent
  let i₀ : Fin r := ⟨0, hr⟩
  let μ : ℂ := (z i₀ : ℂ)
  have hμ : μ ≠ 0 := Circle.coe_ne_zero (z i₀)
  have hpow : ∀ m : ℕ, ∃ i : Fin r, (z i : ℂ) = ζ ^ m * μ := fun m => by
    induction m with
    | zero => exact ⟨i₀, by simp [μ]⟩
    | succ m ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨i, hi⟩ := hstep j
      exact ⟨i, by rw [hi, hj, pow_succ', mul_assoc]⟩
  choose g hg using fun k : Fin r => hpow (k : ℕ)
  have hg_inj : Function.Injective g := fun k₁ k₂ hk =>
    hζ.injective_fin_pow_mul hμ (by dsimp only; rw [← hg k₁, hk, hg k₂])
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg_inj), μ, hμ, hg⟩

open scoped commutatorElement in
/-- Any pair `(A, B)` in `SU(r)` with `⁅A, B⁆ = ζ • 1` (`1 ≤ r`, `IsPrimitiveRoot ζ r`) can be
conjugated in `SU(r)` so that `A = diagonal (fun k => ζ ^ (k : ℕ) * μ)` for some `μ ≠ 0`. -/
private theorem exists_conj_first_eq_clock {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (A B : specialUnitaryGroup (Fin r) ℂ)
    (hAB : (↑⁅A, B⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1) :
    ∃ (u : specialUnitaryGroup (Fin r) ℂ) (μ : ℂ), μ ≠ 0 ∧
      ((u * A * u⁻¹ : specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        diagonal (fun k : Fin r => ζ ^ (k : ℕ) * μ) := by
  obtain ⟨u₁, z, hu₁⟩ := exists_conj_eq_diagonal A
  let A₁ := u₁ * A * u₁⁻¹
  let B₁ := u₁ * B * u₁⁻¹
  have hrel₁ : diagonal (fun i => (z i : ℂ)) * (B₁ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * diagonal (fun i => (z i : ℂ))) := by
    rw [← hu₁]
    exact coe_commutatorElement_eq_smul_one_iff.mp (commutator_conj_eq_smul_one hAB u₁)
  obtain ⟨σ, μ, hμ, hσ⟩ := exists_perm_pow_eq_of_mul_eq_smul_mul hr hζ z B₁ hrel₁
  let PU : unitaryGroup (Fin r) ℂ := permutationUnitary σ⁻¹
  obtain ⟨c, hc⟩ := exists_circle_smul_mem_specialUnitaryGroup PU
  let u₂ : specialUnitaryGroup (Fin r) ℂ := ⟨(c : ℂ) • (PU : Matrix (Fin r) (Fin r) ℂ), hc⟩
  refine ⟨u₂ * u₁, μ, hμ, ?_⟩
  have hconjU : (PU * TauCeti.unitaryTorusHom (Fin r) z * PU⁻¹ : unitaryGroup (Fin r) ℂ) =
      TauCeti.unitaryTorusHom (Fin r) (fun k => z (σ k)) := by
    have h := TauCeti.unitaryTorusNormalizer_mul_unitaryTorusHom_mul_inv
      ⟨permutationUnitary σ⁻¹, TauCeti.permutationUnitary_mem_normalizer σ⁻¹⟩ z
    rw [TauCeti.unitaryTorusNormalizerPerm_permutationUnitary] at h
    exact h.trans (congrArg (TauCeti.unitaryTorusHom (Fin r))
      (funext fun i => by rw [Equiv.Perm.inv_def, Equiv.symm_symm]))
  calc (((u₂ * u₁) * A * (u₂ * u₁)⁻¹ : specialUnitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ)
      = (u₂ : Matrix (Fin r) (Fin r) ℂ) * A₁ * star (u₂ : Matrix (Fin r) (Fin r) ℂ) := by
        simp only [A₁, _root_.mul_inv_rev, Submonoid.coe_mul, coe_inv, Matrix.mul_assoc]
    _ = (PU : Matrix (Fin r) (Fin r) ℂ) * diagonal (fun i => (z i : ℂ)) *
          star (PU : Matrix (Fin r) (Fin r) ℂ) := by
        rw [hu₁]
        exact Unitary.smul_mul_mul_star_smul c.coe_mem_unitary
          (PU : Matrix (Fin r) (Fin r) ℂ) _
    _ = diagonal (fun k : Fin r => ζ ^ (k : ℕ) * μ) := by
        rw [← TauCeti.coe_unitaryTorusHom, ← Unitary.coe_star, Unitary.star_eq_inv,
          ← Submonoid.coe_mul, ← Submonoid.coe_mul, hconjU, TauCeti.coe_unitaryTorusHom]
        exact congrArg diagonal (funext hσ)

open scoped commutatorElement in
/-- If `A₀` has distinct diagonal entries `ζ ^ k * c₁` and both `B₀` and `B` satisfy
`⁅A₀, -⁆ = ζ • 1`, then `(B * B₀⁻¹)⁻¹` is diagonal of determinant `1`. -/
private theorem exists_torus_of_commutator_eq {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    {A₀ B₀ B : specialUnitaryGroup (Fin r) ℂ} {c₁ : Circle}
    (hA₀ : (A₀ : Matrix (Fin r) (Fin r) ℂ) = diagonal (fun k : Fin r => ζ ^ (k : ℕ) * (c₁ : ℂ)))
    (hrel₀ : (↑⁅A₀, B₀⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1)
    (hrel : (↑⁅A₀, B⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1) :
    ∃ η : Fin r → Circle, (∏ j : Fin r, η j = 1) ∧
      (((B * B₀⁻¹)⁻¹ : specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        diagonal (fun j => (η j : ℂ)) := by
  let C : specialUnitaryGroup (Fin r) ℂ := B * B₀⁻¹
  have hcommC : Commute (diagonal (fun k : Fin r => ζ ^ (k : ℕ) * (c₁ : ℂ)))
      (C : Matrix (Fin r) (Fin r) ℂ) := by
    rw [← hA₀]
    exact (commute_mul_inv_of_commutator_eq_smul_one hrel₀ hrel).map
      (specialUnitaryGroup (Fin r) ℂ).subtype
  have hCdiag : (⟨(C⁻¹ : specialUnitaryGroup (Fin r) ℂ),
      specialUnitaryGroup_le_unitaryGroup (C⁻¹).2⟩ : unitaryGroup (Fin r) ℂ) ∈
      TauCeti.unitaryTorus (Fin r) := by
    rw [TauCeti.mem_unitaryTorus_iff, coe_inv]
    exact (TauCeti.isDiag_of_commute_diagonal
      (hζ.injective_fin_pow_mul (Circle.coe_ne_zero c₁)) hcommC).conjTranspose
  obtain ⟨η, hη⟩ := TauCeti.mem_unitaryTorus_iff_exists_unitaryTorusHom.mp hCdiag
  have hη_mat : ((C⁻¹ : specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      diagonal (fun j => (η j : ℂ)) := by
    simpa [TauCeti.coe_unitaryTorusHom] using (congrArg Subtype.val hη).symm
  have hprod_coe : Circle.coeHom (∏ j : Fin r, η j) = 1 := by
    rw [map_prod]
    simpa only [Circle.coeHom_apply] using
      det_diagonal.symm.trans (hη_mat ▸ (mem_specialUnitaryGroup_iff.mp (C⁻¹).2).2)
  exact ⟨η, (map_eq_one_iff Circle.coeHom Circle.coe_injective).mp hprod_coe, hη_mat⟩

open scoped commutatorElement in
/-- Conjugating the rescaled cyclic shift `B₀ = c₂ • permutationUnitary (finRotate r)` by a
rescaled diagonal matrix `D = α • unitaryTorusHom δ` multiplies `B₀` on the left by
`diagonal (fun k => δ k * (δ ((finRotate r).symm k))⁻¹)`. -/
private theorem conj_shift_eq_torus_mul {r : ℕ} {B₀ C : specialUnitaryGroup (Fin r) ℂ}
    {c₂ α : Circle} {δ η : Fin r → Circle}
    (hB₀ : (B₀ : Matrix (Fin r) (Fin r) ℂ) =
      (c₂ : ℂ) • ((permutationUnitary (finRotate r) : unitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ))
    (hδ : ∀ k : Fin r, δ k * (δ ((finRotate r).symm k))⁻¹ = η k)
    (hη_mat : ((C⁻¹ : specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      diagonal (fun j => (η j : ℂ)))
    (hα : (α : ℂ) • (TauCeti.unitaryTorusHom (Fin r) δ : Matrix (Fin r) (Fin r) ℂ) ∈
      specialUnitaryGroup (Fin r) ℂ) :
    (⟨(α : ℂ) • (TauCeti.unitaryTorusHom (Fin r) δ : Matrix (Fin r) (Fin r) ℂ), hα⟩ :
        specialUnitaryGroup (Fin r) ℂ) * B₀ *
      (⟨(α : ℂ) • (TauCeti.unitaryTorusHom (Fin r) δ : Matrix (Fin r) (Fin r) ℂ), hα⟩)⁻¹ =
      C⁻¹ * B₀ := by
  let DU : unitaryGroup (Fin r) ℂ := TauCeti.unitaryTorusHom (Fin r) δ
  let QU : unitaryGroup (Fin r) ℂ := permutationUnitary (finRotate r)
  let D : specialUnitaryGroup (Fin r) ℂ := ⟨(α : ℂ) • (DU : Matrix _ _ ℂ), hα⟩
  have hconjQ : (QU * DU⁻¹ * QU⁻¹ : unitaryGroup (Fin r) ℂ) =
      TauCeti.unitaryTorusHom (Fin r) (fun k => (δ ((finRotate r).symm k))⁻¹) := by
    have hinv : DU⁻¹ = TauCeti.unitaryTorusHom (Fin r) (fun k => (δ k)⁻¹) := (map_inv _ _).symm
    have h := TauCeti.unitaryTorusNormalizer_mul_unitaryTorusHom_mul_inv
      ⟨permutationUnitary (finRotate r), TauCeti.permutationUnitary_mem_normalizer (finRotate r)⟩
      (fun k => (δ k)⁻¹)
    rw [TauCeti.unitaryTorusNormalizerPerm_permutationUnitary, ← hinv] at h
    exact h
  have hηU : TauCeti.unitaryTorusHom (Fin r) η = DU * (QU * DU⁻¹ * QU⁻¹) := by
    rw [← funext hδ, ← Pi.mul_def, map_mul, ← hconjQ]
  have hcomm_mat : (↑⁅D, B₀⁆ : Matrix (Fin r) (Fin r) ℂ) =
      ((C⁻¹ : specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
    have hD_inv : ((DU⁻¹ : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        star (DU : Matrix (Fin r) (Fin r) ℂ) := by rw [← Unitary.star_eq_inv, Unitary.coe_star]
    have hQ_inv : ((QU⁻¹ : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        star (QU : Matrix (Fin r) (Fin r) ℂ) := by rw [← Unitary.star_eq_inv, Unitary.coe_star]
    calc (↑⁅D, B₀⁆ : Matrix (Fin r) (Fin r) ℂ)
        = (DU : Matrix (Fin r) (Fin r) ℂ) * (QU : Matrix (Fin r) (Fin r) ℂ) *
            star (DU : Matrix (Fin r) (Fin r) ℂ) * star (QU : Matrix (Fin r) (Fin r) ℂ) :=
          coe_commutatorElement_of_eq_smul α.coe_mem_unitary c₂.coe_mem_unitary
            (U := (DU : Matrix (Fin r) (Fin r) ℂ)) (V := (QU : Matrix (Fin r) (Fin r) ℂ)) rfl hB₀
      _ = ((DU * (QU * DU⁻¹ * QU⁻¹) : unitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
          simp only [Submonoid.coe_mul, hD_inv, hQ_inv, Matrix.mul_assoc]
      _ = ((C⁻¹ : specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
          rw [← hηU, TauCeti.coe_unitaryTorusHom, ← hη_mat]
  have hcomm : ⁅D, B₀⁆ = C⁻¹ := Subtype.ext hcomm_mat
  calc D * B₀ * D⁻¹ = ⁅D, B₀⁆ * B₀ := by group
    _ = C⁻¹ * B₀ := by rw [hcomm]

open scoped commutatorElement in
/-- If `(A₀, B)` and `(A₀, B₀)` both solve `⁅A₀, -⁆ = ζ • 1` with the standard clock matrix `A₀`
and shift matrix `B₀`, some diagonal element of `SU(r)` conjugates `(A₀, B)` to `(A₀, B₀)`. -/
private theorem exists_diag_conj_second_eq {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {A₀ B₀ B : specialUnitaryGroup (Fin r) ℂ} {c₁ c₂ : Circle}
    (hA₀ : (A₀ : Matrix (Fin r) (Fin r) ℂ) = diagonal (fun k : Fin r => ζ ^ (k : ℕ) * (c₁ : ℂ)))
    (hB₀ : (B₀ : Matrix (Fin r) (Fin r) ℂ) =
      (c₂ : ℂ) • ((permutationUnitary (finRotate r) : unitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ))
    (hrel₀ : (↑⁅A₀, B₀⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1)
    (hrel : (↑⁅A₀, B⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1) :
    ∃ D : specialUnitaryGroup (Fin r) ℂ,
      D * A₀ * D⁻¹ = A₀ ∧ D * B * D⁻¹ = B₀ := by
  let C : specialUnitaryGroup (Fin r) ℂ := B * B₀⁻¹
  obtain ⟨η, hη_prod, hη_mat⟩ := exists_torus_of_commutator_eq hζ hA₀ hrel₀ hrel
  obtain ⟨δ, hδ⟩ := TauCeti.exists_mul_inv_finRotate_symm_eq_iff.mpr hη_prod
  obtain ⟨α, hα⟩ := exists_circle_smul_mem_specialUnitaryGroup (TauCeti.unitaryTorusHom (Fin r) δ)
  let D : specialUnitaryGroup (Fin r) ℂ :=
    ⟨(α : ℂ) • (TauCeti.unitaryTorusHom (Fin r) δ : Matrix (Fin r) (Fin r) ℂ), hα⟩
  have hdiag_comm : ∀ {X : specialUnitaryGroup (Fin r) ℂ} (f : Fin r → ℂ),
      (X : Matrix (Fin r) (Fin r) ℂ) = diagonal f → D * X = X * D := fun f hX => Subtype.ext <| by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, hX]
    dsimp only [D]
    rw [TauCeti.coe_unitaryTorusHom, smul_mul_assoc, mul_smul_comm, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    exact congrArg (α.1 • ·) (congrArg diagonal (funext fun _ => mul_comm _ _))
  have hDA : D * A₀ * D⁻¹ = A₀ := mul_inv_eq_iff_eq_mul.mpr (hdiag_comm _ hA₀)
  have hDC : D * C = C * D := Commute.inv_right_iff.mp (hdiag_comm _ hη_mat)
  have hDB₀ : D * B₀ * D⁻¹ = C⁻¹ * B₀ := conj_shift_eq_torus_mul hB₀ hδ hη_mat hα
  refine ⟨D, hDA, ?_⟩
  calc D * B * D⁻¹ = D * (C * B₀) * D⁻¹ := by simp [C]
    _ = C * (D * B₀ * D⁻¹) := by simp only [← mul_assoc, hDC]
    _ = B₀ := by rw [hDB₀, mul_inv_cancel_left]

/-- If two elements of `SU(r)` are diagonal with entries `ζ ^ k * μ` and `ζ ^ k * c₁`
(`ζ ≠ 0`, `c₁ ≠ 0`), then their scalar ratio satisfies `(μ / c₁) ^ r = 1`. -/
private theorem pow_div_eq_one_of_diagonal_eq {r : ℕ} {ζ μ c₁ : ℂ} (hζ0 : ζ ≠ 0) (hc₁ : c₁ ≠ 0)
    {A₁ A₀ : specialUnitaryGroup (Fin r) ℂ}
    (hA₁ : (A₁ : Matrix (Fin r) (Fin r) ℂ) = diagonal fun k : Fin r => ζ ^ (k : ℕ) * μ)
    (hA₀ : (A₀ : Matrix (Fin r) (Fin r) ℂ) = diagonal fun k : Fin r => ζ ^ (k : ℕ) * c₁) :
    (μ / c₁) ^ r = 1 := by
  have hdetA₁ := (mem_specialUnitaryGroup_iff.mp A₁.2).2
  have hdetA₀ := (mem_specialUnitaryGroup_iff.mp A₀.2).2
  rw [hA₁, det_diagonal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdetA₁
  rw [hA₀, det_diagonal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdetA₀
  have hprod_ne : (∏ k : Fin r, ζ ^ (k : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ hζ0
  rw [div_pow, mul_left_cancel₀ hprod_ne (hdetA₁.trans hdetA₀.symm),
    div_self (pow_ne_zero _ hc₁)]

open scoped commutatorElement in
/-- **Classification of twisted commuting pairs in `SU(r)`.** When `ζ` is a primitive `r`-th root
of unity, every pair `A, B ∈ SU(r)` satisfying `⁅A, B⁆ = ζ • 1` is simultaneously conjugate in
`SU(r)` to the clock-and-shift pair `(clock hζ.pow_eq_one, shift r)`. No positivity assumption on
`r` is needed: for `r = 0`, `SU(0)` is a subsingleton. -/
theorem exists_conj_eq_clock_shift {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    {A B : specialUnitaryGroup (Fin r) ℂ}
    (hAB : (↑⁅A, B⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1) :
    ∃ w : specialUnitaryGroup (Fin r) ℂ,
      w * A * w⁻¹ = clock hζ.pow_eq_one ∧ w * B * w⁻¹ = shift r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have : NeZero r := ⟨by omega⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  let A₀ := clock hζ.pow_eq_one
  let B₀ := shift r
  obtain ⟨c₁, hA₀'⟩ := exists_coe_clock hζ.pow_eq_one
  obtain ⟨c₂, hB₀⟩ := exists_coe_shift r
  have hA₀ : (A₀ : Matrix (Fin r) (Fin r) ℂ) =
      diagonal (fun k : Fin r => ζ ^ (k : ℕ) * (c₁ : ℂ)) := by
    rw [hA₀', ← diagonal_smul]
    exact congrArg diagonal (funext fun _ => mul_comm _ _)
  have hrel₀ : (↑⁅A₀, B₀⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 :=
    commutator_clock_shift hζ.pow_eq_one
  -- Conjugate `A` to `diagonal (ζ ^ k * μ)` for some scalar `μ ≠ 0`.
  obtain ⟨u₁, μ, _, hu₁⟩ := exists_conj_first_eq_clock hr hζ A B hAB
  let A₁ := u₁ * A * u₁⁻¹
  let B₁ := u₁ * B * u₁⁻¹
  have hrel₁ : (↑⁅A₁, B₁⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 :=
    commutator_conj_eq_smul_one hAB u₁
  -- Conjugate by a power of `B₁` to match the scalar factor `c₁` of `clock`.
  have hratio : (μ / (c₁ : ℂ)) ^ r = 1 :=
    pow_div_eq_one_of_diagonal_eq hζ0 (Circle.coe_ne_zero c₁) hu₁ hA₀
  obtain ⟨m, _, hm⟩ := hζ.eq_pow_of_pow_eq_one hratio
  have hA₂ : B₁ ^ m * A₁ * (B₁ ^ m)⁻¹ = A₀ := Subtype.ext <| by
    rw [conj_pow_eq_inv_pow_smul hrel₁ m, hu₁, hA₀, ← diagonal_smul]
    refine congrArg diagonal (funext fun k => ?_)
    have hμ_eq : μ = ζ ^ m * (c₁ : ℂ) := by rw [hm, div_mul_cancel₀ _ (Circle.coe_ne_zero c₁)]
    rw [Pi.smul_apply, smul_eq_mul, hμ_eq, inv_pow]
    linear_combination (ζ ^ (k : ℕ) * (c₁ : ℂ)) * inv_mul_cancel₀ (pow_ne_zero m hζ0)
  have hB₁_self : B₁ ^ m * B₁ * (B₁ ^ m)⁻¹ = B₁ := by group
  have hrel₂ : (↑⁅A₀, B₁⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
    simpa only [hA₂, hB₁_self] using commutator_conj_eq_smul_one hrel₁ (B₁ ^ m)
  -- Conjugate by a diagonal matrix `D` fixing `A₀` and taking `B₁` to `shift r`.
  obtain ⟨D, hDA₀, hDB₁⟩ := exists_diag_conj_second_eq hζ hA₀ hB₀ hrel₀ hrel₂
  refine ⟨D * B₁ ^ m * u₁, ?_, ?_⟩
  · calc (D * B₁ ^ m * u₁) * A * (D * B₁ ^ m * u₁)⁻¹
        = D * (B₁ ^ m * A₁ * (B₁ ^ m)⁻¹) * D⁻¹ := by simp only [A₁, _root_.mul_inv_rev, mul_assoc]
      _ = A₀ := by rw [hA₂, hDA₀]
  · calc (D * B₁ ^ m * u₁) * B * (D * B₁ ^ m * u₁)⁻¹
        = D * (B₁ ^ m * B₁ * (B₁ ^ m)⁻¹) * D⁻¹ := by simp only [B₁, _root_.mul_inv_rev, mul_assoc]
      _ = B₀ := by rw [hB₁_self, hDB₁]

end Complex

end Matrix.specialUnitaryGroup
