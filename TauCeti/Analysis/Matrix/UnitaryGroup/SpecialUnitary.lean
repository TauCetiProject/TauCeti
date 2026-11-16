/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Center and diagonalization in the complex special unitary group

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

* `Matrix.specialUnitaryGroup.centerMulEquivCenterSL`: the isomorphism between the centers of
  `SU(n)` and `SL(n, ℂ)` induced by `toSL`.
* `Matrix.specialUnitaryGroup.centerMulEquivRootsOfUnityFin`: for `0 < r`, the isomorphism
  `Subgroup.center (specialUnitaryGroup (Fin r) ℂ) ≃* rootsOfUnity r ℂ`.

## Main results

* `Matrix.specialUnitaryGroup.scalar_mem`: over `ℝ` or `ℂ`, `scalar n c` lies in
  `specialUnitaryGroup n 𝕜` whenever `c ^ card n = 1`.
* `Matrix.specialUnitaryGroup.mem_center_iff`: over `ℂ`, `g` lies in the center of `SU(n)` iff
  `g = scalar n c` for some `c` with `c ^ card n = 1`.
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

section CommRing

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [CommRing α] [StarRing α]

/-- Any special unitary matrix equal to a scalar matrix lies in the center of the special unitary
group. -/
theorem mem_center_of_coe_eq_scalar {g : specialUnitaryGroup n α} {c : α}
    (hg : (g : Matrix n n α) = scalar n c) :
    g ∈ Subgroup.center (specialUnitaryGroup n α) :=
  Subgroup.mem_center_iff.mpr fun h => Subtype.ext <| by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, hg,
      (scalar_commute c (Commute.all c) (h : Matrix n n α)).eq]

/-- An element of `SU(n, α)` whose image in `SL(n, α)` is central lies in the center of
`SU(n, α)`. -/
theorem comap_toSL_center_le :
    (Subgroup.center (SpecialLinearGroup n α)).comap (toSL (n := n) (α := α)) ≤
      Subgroup.center (specialUnitaryGroup n α) := fun g hg =>
  Subgroup.mem_center_iff.mpr fun h => toSL_injective <| by
    rw [map_mul, map_mul, Subgroup.mem_center_iff.mp hg (toSL h)]

end CommRing

section RCLike

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

/-- Over `ℝ` or `ℂ`, a scalar matrix whose scalar is a `card n`-th root of unity lies in
`specialUnitaryGroup n 𝕜`. No nonemptiness assumption on `n` is needed. -/
theorem scalar_mem {c : 𝕜} (hc : c ^ Fintype.card n = 1) :
    scalar n c ∈ specialUnitaryGroup n 𝕜 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Subsingleton.elim (scalar n c) 1 ▸ one_mem _
  have hnorm : ‖c‖ = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg c) (Fintype.card_ne_zero (α := n)),
      ← norm_pow, hc, norm_one]
  refine mem_specialUnitaryGroup_iff.mpr ⟨?_, by simp [det_diagonal, hc]⟩
  rw [scalar_apply, diagonal_mem_unitary, Pi.mem_unitary_iff]
  intro _
  refine Unitary.mem_iff_star_mul_self.mpr ?_
  rw [RCLike.star_def, RCLike.conj_mul, hnorm]
  simp

end RCLike

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
    have hcoe_prod : ∏ k, (z k : ℂ) = ((∏ k, z k : Circle) : ℂ) :=
      (map_prod (Submonoid.unitSphere ℂ).subtype z Finset.univ).symm
    rw [TauCeti.coe_unitaryTorusHom, det_diagonal, hcoe_prod, hprod, Circle.coe_one]
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
    have hcoe_prod : ∏ k, (z k : ℂ) = ((∏ k, z k : Circle) : ℂ) :=
      (map_prod (Submonoid.unitSphere ℂ).subtype z Finset.univ).symm
    rw [Submonoid.coe_mul, det_mul, TauCeti.coe_unitaryTorusHom, det_diagonal, hcoe_prod,
      hprod, coe_permutationUnitary, Equiv.swap_inv, det_permutation, Equiv.Perm.sign_swap hij]
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
  have hcmul : (c : ℂ) * star (c : ℂ) = 1 :=
    Unitary.mem_iff_self_mul_star.mp c.coe_mem_unitary
  have hcoe : (((⟨(c : ℂ) • (U : Matrix n n ℂ), hc⟩ * g *
      (⟨(c : ℂ) • (U : Matrix n n ℂ), hc⟩)⁻¹ : specialUnitaryGroup n ℂ)) : Matrix n n ℂ) =
      ((U * gU * U⁻¹ : unitaryGroup n ℂ) : Matrix n n ℂ) := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
      ← star_eq_inv, coe_star, ← Unitary.star_eq_inv, Unitary.coe_star]
    dsimp only [gU]
    rw [star_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hcmul, one_smul]
  rw [hcoe, ← hz, TauCeti.coe_unitaryTorusHom]

end Complex

end Matrix.specialUnitaryGroup
