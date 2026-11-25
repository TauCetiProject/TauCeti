/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import TauCeti.Algebra.Star.Unitary
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Center and diagonalization of `SU(n)`

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

## Main definitions

* `Matrix.specialUnitaryGroup.mulSingleInvTorus`: the diagonal element of `SU(n)` with circle entry
  `c` at `i`, `c⁻¹` at `j` (or `1` if `i = j`), and `1` elsewhere.
* `Matrix.specialUnitaryGroup.centerMulEquivCenterSL`: the isomorphism between the centers of
  `SU(n)` and `SL(n, ℂ)` induced by `toSL`.
* `Matrix.specialUnitaryGroup.centerMulEquivRootsOfUnityFin`: for `0 < r`, the isomorphism
  `Subgroup.center (specialUnitaryGroup (Fin r) ℂ) ≃* rootsOfUnity r ℂ`.

## Main results

* `Matrix.specialUnitaryGroup.mem_center_iff`: over `ℂ`, `g` lies in the center of `SU(n)` iff
  `g = scalar n c` for some `c` with `c ^ card n = 1`.
* `Matrix.specialUnitaryGroup.mulSingleInvTorus_notMem_center` and
  `Matrix.specialUnitaryGroup.exists_notMem_center`: for `[Nontrivial n]`, `SU(n)` has non-central
  elements.
* `Matrix.specialUnitaryGroup.toSL_mem_center_iff`,
  `Matrix.specialUnitaryGroup.comap_toSL_center`,
  `Matrix.specialUnitaryGroup.ker_toPSL_eq_center`: the center of `SU(n)` is the preimage of the
  center of `SL(n, ℂ)` and equals the kernel of `toPSL`.
* `Matrix.specialUnitaryGroup.exists_conj_eq_diagonal`: every element of `SU(n)` is conjugate in
  `SU(n)` to a diagonal matrix with entries on the unit circle.

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

/-- For indices `i, j : n` and `c : Circle`, the diagonal element of `SU(n)` with entry `c` at `i`,
`c⁻¹` at `j` (or `1` when `i = j`), and `1` elsewhere. -/
noncomputable def mulSingleInvTorus (i j : n) (c : Circle) : specialUnitaryGroup n ℂ :=
  let z : n → Circle := Pi.mulSingle i c * Pi.mulSingle j c⁻¹
  ⟨TauCeti.unitaryTorusHom n z,
    mem_specialUnitaryGroup_iff.mpr
      ⟨(TauCeti.unitaryTorusHom n z).property, by
        have hprod : ∏ k, z k = 1 := by
          simp only [z, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle',
            mul_inv_cancel]
        rw [TauCeti.det_unitaryTorusHom, hprod, Circle.coe_one]⟩⟩

/-- The underlying matrix of `mulSingleInvTorus i j c` is the diagonal matrix of
`Pi.mulSingle i c * Pi.mulSingle j c⁻¹`. -/
@[simp]
theorem coe_mulSingleInvTorus (i j : n) (c : Circle) :
    (mulSingleInvTorus i j c : Matrix n n ℂ) =
      diagonal fun k => (((Pi.mulSingle i c * Pi.mulSingle j c⁻¹ : n → Circle) k : Circle) : ℂ) :=
  TauCeti.coe_unitaryTorusHom _

/-- For distinct indices `i ≠ j`, some `mulSingleInvTorus i j c ∈ SU(n)` has distinct `(i, i)` and
`(j, j)` entries (witnessed by `c = I`, giving `I` at `i` and `-I` at `j`). -/
private theorem exists_mulSingleInvTorus_apply_ne {i j : n} (hij : i ≠ j) :
    ∃ c : Circle,
      (mulSingleInvTorus i j c : Matrix n n ℂ) i i ≠
        (mulSingleInvTorus i j c : Matrix n n ℂ) j j := by
  let cI : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩
  have hcI : (cI : ℂ) = Complex.I := rfl
  exact ⟨cI, by simp [hcI, hij, hij.symm, Complex.inv_I, self_eq_neg, Complex.I_ne_zero]⟩

/-- A central element of `SU(n)` over `ℂ` is diagonal: for any `i ≠ j`, some
`mulSingleInvTorus i j c ∈ SU(n)` separates `i` from `j`. -/
private theorem isDiag_of_mem_center {g : specialUnitaryGroup n ℂ}
    (hg : g ∈ Subgroup.center (specialUnitaryGroup n ℂ)) :
    (g : Matrix n n ℂ).IsDiag := by
  intro i j hij
  obtain ⟨c, hc⟩ := exists_mulSingleInvTorus_apply_ne hij
  have hcomm : Commute (mulSingleInvTorus i j c : Matrix n n ℂ) (g : Matrix n n ℂ) := by
    rw [commute_iff_eq]
    simpa only [Submonoid.coe_mul] using
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hg (mulSingleInvTorus i j c))
  rw [coe_mulSingleInvTorus] at hcomm
  exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm
    (by simpa only [coe_mulSingleInvTorus, diagonal_apply_eq] using hc)

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
    simp [U, -TauCeti.coe_unitaryTorusHom, TauCeti.det_unitaryTorusHom, hprod,
      Equiv.Perm.sign_swap hij]
  let u : specialUnitaryGroup n ℂ := ⟨U, mem_specialUnitaryGroup_iff.mpr ⟨U.property, hdet⟩⟩
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
  refine ⟨fun hg => ?_, fun ⟨c, _, hc⟩ => Subgroup.mem_center_iff.mpr fun h => Subtype.ext <| by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ← hc,
      (scalar_commute c (Commute.all c) (h : Matrix n n ℂ)).symm.eq]⟩
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · exact ⟨1, by simp, Subsingleton.elim _ _⟩
  have hscal : scalar n ((g : Matrix n n ℂ) i₀ i₀) = (g : Matrix n n ℂ) := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simpa using (diag_eq_of_mem_center hg i i₀).symm
    · simp [scalar_apply, diagonal_apply_ne _ hij, isDiag_of_mem_center hg hij]
  refine ⟨(g : Matrix n n ℂ) i₀ i₀, ?_, hscal⟩
  have hdet := (mem_specialUnitaryGroup_iff.mp g.property).2
  rwa [← hscal, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ] at hdet

/-- For distinct indices `i ≠ j` and a circle element `c` with `c ≠ c⁻¹`,
`mulSingleInvTorus i j c` does not lie in the center of `SU(n)`. -/
theorem mulSingleInvTorus_notMem_center {i j : n} (hij : i ≠ j) {c : Circle} (hc : c ≠ c⁻¹) :
    mulSingleInvTorus i j c ∉ Subgroup.center (specialUnitaryGroup n ℂ) := fun h => by
  obtain ⟨z, _, hz⟩ := mem_center_iff.mp h
  have hi : z = c := by simpa [hij] using congr_fun₂ hz i i
  have hj : z = (c⁻¹ : Circle) := by simpa [hij.symm] using congr_fun₂ hz j j
  exact hc (Circle.coe_inj.mp (hi.symm.trans hj))

/-- Over `ℂ`, whenever `n` has at least two elements, `SU(n)` has a non-central element (so its
center is a proper subgroup). -/
theorem exists_notMem_center [Nontrivial n] :
    ∃ u : specialUnitaryGroup n ℂ, u ∉ Subgroup.center (specialUnitaryGroup n ℂ) := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  obtain ⟨c, hc⟩ := exists_mulSingleInvTorus_apply_ne hij
  refine ⟨mulSingleInvTorus i j c, mulSingleInvTorus_notMem_center hij fun h => hc ?_⟩
  simp [hij, hij.symm, ← h]

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
      (Subgroup.center (SpecialLinearGroup n ℂ)) fun g => toSL_mem_center_iff.mpr g.property)
    ⟨fun a b h => Subtype.ext <| toSL_injective (congrArg Subtype.val h), fun z => by
      obtain ⟨g, hg⟩ := center_le_range_toSL z.property
      exact ⟨⟨g, toSL_mem_center_iff.mp (hg.symm ▸ z.property)⟩, Subtype.ext hg⟩⟩

/-- `centerMulEquivCenterSL` acts on elements by applying `toSL`. -/
@[simp]
theorem coe_centerMulEquivCenterSL_apply (z : Subgroup.center (specialUnitaryGroup n ℂ)) :
    (centerMulEquivCenterSL z : SpecialLinearGroup n ℂ) = toSL z.val :=
  (rfl)

/-- Applying `toSL` after `centerMulEquivCenterSL.symm` recovers the underlying element of
`SL(n, ℂ)`. -/
@[simp]
theorem toSL_coe_centerMulEquivCenterSL_symm (z : Subgroup.center (SpecialLinearGroup n ℂ)) :
    toSL ((centerMulEquivCenterSL.symm z : Subgroup.center (specialUnitaryGroup n ℂ)) :
      specialUnitaryGroup n ℂ) = z.val :=
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
      (z.val : Matrix (Fin r) (Fin r) ℂ) ⟨0, hr⟩ ⟨0, hr⟩ := by
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
  let gU : unitaryGroup n ℂ := ⟨g, specialUnitaryGroup_le_unitaryGroup g.property⟩
  obtain ⟨U, hU⟩ := TauCeti.exists_conj_mem_unitaryTorus gU
  obtain ⟨z, hz⟩ := TauCeti.mem_unitaryTorus_iff_exists_unitaryTorusHom.mp hU
  obtain ⟨c, hc⟩ := exists_circle_smul_mem_specialUnitaryGroup U
  refine ⟨⟨(c : ℂ) • (U : Matrix n n ℂ), hc⟩, z, ?_⟩
  have hcoe : (((⟨(c : ℂ) • (U : Matrix n n ℂ), hc⟩ * g *
      (⟨(c : ℂ) • (U : Matrix n n ℂ), hc⟩)⁻¹ : specialUnitaryGroup n ℂ)) : Matrix n n ℂ) =
      ((U * gU * U⁻¹ : unitaryGroup n ℂ) : Matrix n n ℂ) := by
    simp only [Submonoid.coe_mul, coe_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
    exact Unitary.smul_mul_mul_star_smul c.coe_mem_unitary (U : Matrix n n ℂ) (g : Matrix n n ℂ)
  rw [hcoe, ← hz, TauCeti.coe_unitaryTorusHom]

end Complex

end Matrix.specialUnitaryGroup
