/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.RepresentationTheory.SU2.Basic
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.RankOne

/-!
# The ambient groups of Sato–Tate theory: `U(d)` and `USp(d)`

A Sato–Tate group is a closed subgroup `G` of the unitary group `U(d)` of `d × d` complex
matrices, weighted by its normalized Haar measure; for an abelian variety of dimension `g` it lies
in the unitary symplectic group `USp(2g)`. This file sets up these ambient groups.

## Closed subgroups of `U(d)` and their Haar measure

`U(d) = Matrix.unitaryGroup (Fin d) ℂ` is a compact Hausdorff topological group
(`TauCeti.Matrix.isCompact_unitaryGroup`). It inherits Mathlib's measurable structure on
`Matrix (Fin d) (Fin d) ℂ`, which is the Borel structure, so every subgroup of `U(d)` is a Borel
space through the subtype instances, and no further measurable structure is declared here. For
`G : ClosedSubgroup (U d)` the subgroup `↥G.toSubgroup` is a compact topological group
(`ClosedSubgroup.instCompactSpaceToSubgroup`), and its Haar probability measure is
`TauCeti.haarProb G.toSubgroup`. That measure is invariant under left and right translation and
inversion, it is the unique Haar probability measure
(`MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure`), and restricted to a closed
subgroup of finite index `n` it is `n⁻¹` times the Haar probability measure of that subgroup
(`TauCeti.comap_inclusion_haarProb_eq_inv_relIndex_smul`).

## The unitary symplectic group

The symplectic form is `Ω_d = [[0, I], [−I, 0]]` in block form, with `I` of size `d / 2`, and
`USp(d) = {g ∈ U(d) | gᵀ Ω_d g = Ω_d}`; this is the convention of Fité–Kedlaya–Rotger–Sutherland
(§3.4, Remark 3.6). For `d = g + g`, reindexing along `finSumFinEquiv : Fin g ⊕ Fin g ≃ Fin (g + g)`
carries Mathlib's form `Matrix.J (Fin g) ℂ = [[0, −I], [I, 0]]` to `−Ω_d`, that is
`Ω_{g+g} = −TauCeti.JFin g ℂ` (`TauCeti.SatoTate.symplecticForm_eq_neg_JFin`), so a unitary
matrix lies in `USp(d)` exactly when its reindexing lies in Mathlib's `Matrix.symplecticGroup`.
This gives `det g = 1` on `USp(d)` for even `d` (`Matrix.SymplecticGroup.det_eq_one`) and closure
under transposition. For `d = 2` the condition `gᵀ Ω g = Ω` is `det g = 1`, so `USp(2)` is
`SU(2)`, and the resulting isomorphism of topological groups carries Haar measure to Haar measure;
statements about `SU(2)` transfer to `USp(2)` along it.

The same compact group appears in `TauCeti/Geometry/Lie/Subgroup/CompactSymplectic.lean` as
`TauCeti.GLSymplectic l ℂ ⊓ unitarySubgroup (GL (l ⊕ l) ℂ)`, a subgroup of the general linear
group in Mathlib's coordinates. Here it is a subgroup of `U(d)` in the coordinates of
Fité–Kedlaya–Rotger–Sutherland, because Sato–Tate groups are closed subgroups of `U(d)` written in
those coordinates.

## Main definitions

* `TauCeti.SatoTate.U`: the unitary group `U(d)`.
* `TauCeti.SatoTate.symplecticForm`: the symplectic form `Ω_d`.
* `TauCeti.SatoTate.USp`: the unitary symplectic group `USp(d)`, a subgroup of `U(d)`, and
  `TauCeti.SatoTate.uSpClosed`, the same group as a closed subgroup.
* `TauCeti.SatoTate.uSpTwoEquivSU2`: the isomorphism of topological groups `USp(2) ≃ₜ* SU(2)`.

## Main results

* `TauCeti.SatoTate.isClosed_USp`: `USp(d)` is closed in `U(d)`.
* `TauCeti.SatoTate.mem_USp_iff_reindex_mem_symplecticGroup`: for `d = g + g`, membership in
  `USp(d)` is membership of the reindexed matrix in Mathlib's symplectic group.
* `TauCeti.SatoTate.det_eq_one_of_mem_USp`: elements of `USp(d)` have determinant one for even `d`.
* `TauCeti.SatoTate.transpose_mem_USp_iff`, `TauCeti.SatoTate.map_star_mem_USp_iff`: `USp(d)` is
  closed under transposition (for even `d`) and entrywise complex conjugation.
* `TauCeti.SatoTate.transpose_mul_symplecticForm_two_mul_eq_det_smul`: `Mᵀ Ω_2 M = det M • Ω_2`
  for every `2 × 2` matrix `M`.
* `TauCeti.SatoTate.mem_USp_two_iff`: `USp(2)` is the determinant-one subgroup of `U(2)`.
* `TauCeti.SatoTate.map_haarProb_uSpTwoEquivSU2`: `USp(2) ≃ₜ* SU(2)` carries Haar measure to Haar
  measure.

## References

* F. Fité, K. S. Kedlaya, V. Rotger, A. V. Sutherland, *Sato–Tate distributions and Galois
  endomorphism modules in genus 2*, Compositio Math. 148 (2012), §3.
-/

public section

open Matrix MeasureTheory

namespace TauCeti.SatoTate

/-- The unitary group `U(d)` of `d × d` complex matrices, the compact group whose closed subgroups
are the candidate Sato–Tate groups of degree `d`. -/
abbrev U (d : ℕ) : Type := Matrix.unitaryGroup (Fin d) ℂ

variable {d : ℕ}

/-! ### The symplectic form -/

/-- The symplectic form `Ω_d = [[0, I], [−I, 0]]`: the entry at `(i, i + d / 2)` is `1`, the entry
at `(j + d / 2, j)` is `−1`, and all other entries vanish. It is a symplectic form only for even
`d`. -/
def symplecticForm (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j ↦ if (j : ℕ) = i + d / 2 then 1 else if (i : ℕ) = j + d / 2 then -1 else 0

theorem symplecticForm_apply (i j : Fin d) :
    symplecticForm d i j =
      if (j : ℕ) = i + d / 2 then 1 else if (i : ℕ) = j + d / 2 then -1 else 0 :=
  (rfl)

/-- `Ω_{g+g}` is the negative of Tau Ceti's `TauCeti.JFin g ℂ`, Mathlib's symplectic form
`Matrix.J (Fin g) ℂ = [[0, −I], [I, 0]]` reindexed along
`finSumFinEquiv : Fin g ⊕ Fin g ≃ Fin (g + g)`. -/
theorem symplecticForm_eq_neg_JFin (g : ℕ) : symplecticForm (g + g) = -JFin g ℂ := by
  have hg : (g + g) / 2 = g := by omega
  rw [JFin_eq_submatrix]
  ext i j
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;>
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    rw [symplecticForm_apply, hg] <;>
    split_ifs <;>
    -- `Fin.natAdd_eq_addNat` would turn `Fin.natAdd g j` into `j.addNat g` before
    -- `finSumFinEquiv.symm` cancels against it.
    simp [J, Matrix.one_apply, -Fin.natAdd_eq_addNat, Fin.ext_iff] at * <;> omega

/-- `Ω_d` is antisymmetric for even `d`. -/
@[simp]
theorem transpose_symplecticForm (hd : Even d) :
    (symplecticForm d)ᵀ = -symplecticForm d := by
  obtain ⟨g, rfl⟩ := hd
  rw [symplecticForm_eq_neg_JFin, transpose_neg, JFin_transpose]

/-- `Ω_d² = −1` for even `d`. -/
theorem symplecticForm_mul_self (hd : Even d) :
    symplecticForm d * symplecticForm d = -1 := by
  obtain ⟨g, rfl⟩ := hd
  rw [symplecticForm_eq_neg_JFin, neg_mul_neg, JFin_mul_self]

/-- `Ω_d` has entries in `{0, 1, −1}`, so every additive map `ℂ → ℂ` preserving `1` fixes it
entrywise; in particular complex conjugation `starRingEnd ℂ` does. This is the analogue of
`Matrix.map_J`. -/
@[simp]
theorem map_symplecticForm {F : Type*} [FunLike F ℂ ℂ] [AddMonoidHomClass F ℂ ℂ]
    [OneHomClass F ℂ ℂ] (f : F) : (symplecticForm d).map f = symplecticForm d := by
  ext i j
  simp only [map_apply, symplecticForm_apply]
  split_ifs <;> simp

/-! ### The unitary symplectic group -/

/-- The unitary symplectic group `USp(d) = {g ∈ U(d) | gᵀ Ω_d g = Ω_d}`. It is the compact form of
the symplectic group for even `d`; for odd `d` the matrix `Ω_d` is not a symplectic form, and the
results below about `USp(d)` as a symplectic group assume `d` even. -/
def USp (d : ℕ) : Subgroup (U d) where
  carrier := {g | (g : Matrix (Fin d) (Fin d) ℂ)ᵀ * symplecticForm d * g = symplecticForm d}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Submonoid.coe_mul, transpose_mul] at hg hh ⊢
    calc (h : Matrix (Fin d) (Fin d) ℂ)ᵀ * (g : Matrix (Fin d) (Fin d) ℂ)ᵀ * symplecticForm d *
          ((g : Matrix (Fin d) (Fin d) ℂ) * h)
        = (h : Matrix (Fin d) (Fin d) ℂ)ᵀ *
            ((g : Matrix (Fin d) (Fin d) ℂ)ᵀ * symplecticForm d * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = symplecticForm d := by rw [hg, hh]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h1 : (g : Matrix (Fin d) (Fin d) ℂ) * ((g⁻¹ : U d) : Matrix (Fin d) (Fin d) ℂ) = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
    generalize ((g⁻¹ : U d) : Matrix (Fin d) (Fin d) ℂ) = B at h1 ⊢
    generalize (g : Matrix (Fin d) (Fin d) ℂ) = A at h1 hg
    calc Bᵀ * symplecticForm d * B = Bᵀ * (Aᵀ * symplecticForm d * A) * B := by rw [hg]
      _ = (A * B)ᵀ * symplecticForm d * (A * B) := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = symplecticForm d := by rw [h1, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_USp_iff {g : U d} :
    g ∈ USp d ↔ (g : Matrix (Fin d) (Fin d) ℂ)ᵀ * symplecticForm d * g = symplecticForm d :=
  Iff.rfl

/-- `USp(d)` is closed in `U(d)`: it is cut out by the continuous equation `gᵀ Ω_d g = Ω_d`. -/
theorem isClosed_USp (d : ℕ) : IsClosed (USp d : Set (U d)) :=
  isClosed_eq ((continuous_subtypeVal.matrix_transpose.matrix_mul continuous_const).matrix_mul
    continuous_subtypeVal) continuous_const

/-- `USp(d)` as a closed subgroup of `U(d)`. -/
def uSpClosed (d : ℕ) : ClosedSubgroup (U d) where
  toSubgroup := USp d
  isClosed' := isClosed_USp d

@[simp]
theorem toSubgroup_uSpClosed (d : ℕ) : (uSpClosed d).toSubgroup = USp d :=
  (rfl)

instance (d : ℕ) : CompactSpace (USp d) :=
  isCompact_iff_compactSpace.mp (isClosed_USp d).isCompact

/-- For `d = g + g`, a unitary matrix lies in `USp(d)` exactly when its reindexing along
`finSumFinEquiv` lies in Mathlib's symplectic group `Matrix.symplecticGroup (Fin g) ℂ`. -/
theorem mem_USp_iff_reindex_mem_symplecticGroup {g : ℕ} (x : U (g + g)) :
    x ∈ USp (g + g) ↔ reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (x : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) ∈ symplecticGroup (Fin g) ℂ := by
  have hJ : J (Fin g) ℂ =
      reindex finSumFinEquiv.symm finSumFinEquiv.symm (-symplecticForm (g + g)) := by
    rw [symplecticForm_eq_neg_JFin, neg_neg, reindex_apply, Equiv.symm_symm, JFin_submatrix]
  rw [SymplecticGroup.mem_iff', hJ, transpose_reindex, ← coe_reindexAlgEquiv ℂ ℂ, ← map_mul,
    ← map_mul, (reindexAlgEquiv ℂ ℂ _).injective.eq_iff, Matrix.mul_neg, Matrix.neg_mul, neg_inj,
    mem_USp_iff]

/-- Elements of `USp(d)` have determinant one when `d` is even. -/
theorem det_eq_one_of_mem_USp (hd : Even d) {x : U d} (hx : x ∈ USp d) :
    (x : Matrix (Fin d) (Fin d) ℂ).det = 1 := by
  obtain ⟨g, rfl⟩ := hd
  rw [← det_reindex_self finSumFinEquiv.symm]
  exact SymplecticGroup.det_eq_one ((mem_USp_iff_reindex_mem_symplecticGroup x).mp hx)

/-- For even `d`, `USp(d)` is closed under transposition. -/
@[simp]
theorem transpose_mem_USp_iff (hd : Even d) {x : U d} :
    UnitaryGroup.transpose x ∈ USp d ↔ x ∈ USp d := by
  obtain ⟨g, rfl⟩ := hd
  simp only [mem_USp_iff_reindex_mem_symplecticGroup, UnitaryGroup.transpose_coe,
    ← transpose_reindex, SymplecticGroup.transpose_mem_iff]

/-- `USp(d)` is closed under entrywise complex conjugation. -/
@[simp]
theorem map_star_mem_USp_iff {x : U d} : UnitaryGroup.map_star x ∈ USp d ↔ x ∈ USp d := by
  have hs : (star : ℂ → ℂ) = starRingEnd ℂ := (funext starRingEnd_apply).symm
  have hΩ : (symplecticForm d).map (starRingEnd ℂ) = symplecticForm d :=
    map_symplecticForm _
  have hinv (M : Matrix (Fin d) (Fin d) ℂ) : (M.map (starRingEnd ℂ)).map (starRingEnd ℂ) = M := by
    ext
    simp
  have key (M : Matrix (Fin d) (Fin d) ℂ) :
      (M.map (starRingEnd ℂ))ᵀ * symplecticForm d * M.map (starRingEnd ℂ) =
        (Mᵀ * symplecticForm d * M).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map, hΩ]
  rw [mem_USp_iff, mem_USp_iff, UnitaryGroup.map_star_coe, hs, key]
  constructor
  · intro h
    simpa only [hinv, hΩ] using congrArg (Matrix.map · (starRingEnd ℂ)) h
  · intro h
    rw [h, hΩ]

/-- For every `2 × 2` matrix `M`, `Mᵀ Ω_2 M = det M • Ω_2`. This is
`TauCeti.mul_JFin_one_mul_transpose_eq_det_smul` applied to `Mᵀ`, read through
`Ω_{1+1} = −JFin 1 ℂ`. -/
theorem transpose_mul_symplecticForm_two_mul_eq_det_smul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Mᵀ * symplecticForm 2 * M = M.det • symplecticForm 2 := by
  have h := mul_JFin_one_mul_transpose_eq_det_smul Mᵀ
  rw [transpose_transpose, det_transpose] at h
  -- The `JFin` API is stated on `Fin (1 + 1)`; restate the goal there, using that the
  -- numerals `2` and `1 + 1` are definitionally equal, so its lemmas rewrite the goal.
  change Mᵀ * symplecticForm (1 + 1) * M = M.det • symplecticForm (1 + 1)
  rw [symplecticForm_eq_neg_JFin, Matrix.mul_neg, Matrix.neg_mul, h, smul_neg]

/-- `USp(2)` is the determinant-one subgroup of `U(2)`, since `gᵀ Ω_2 g = det g • Ω_2`
(`transpose_mul_symplecticForm_two_mul_eq_det_smul`). -/
theorem mem_USp_two_iff {x : U 2} : x ∈ USp 2 ↔ (x : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  rw [mem_USp_iff, transpose_mul_symplecticForm_two_mul_eq_det_smul]
  constructor
  · intro h
    simpa [symplecticForm_apply] using congrFun (congrFun h 0) 1
  · intro h
    rw [h, one_smul]

/-- The isomorphism of topological groups `USp(2) ≃ₜ* SU(2)`, the identity on matrices. It is
stated on `(uSpClosed 2).toSubgroup`, the form in which Haar measure of a closed subgroup of `U(d)`
is taken. -/
def uSpTwoEquivSU2 : (uSpClosed 2).toSubgroup ≃ₜ* SU2 where
  toFun x := ⟨((x : U 2) : Matrix (Fin 2) (Fin 2) ℂ),
    mem_specialUnitaryGroup_iff.mpr ⟨(x : U 2).property, mem_USp_two_iff.mp x.property⟩⟩
  invFun y := ⟨⟨y, (mem_specialUnitaryGroup_iff.mp y.property).1⟩,
    mem_USp_two_iff.mpr (mem_specialUnitaryGroup_iff.mp y.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _

@[simp]
theorem coe_uSpTwoEquivSU2 (x : (uSpClosed 2).toSubgroup) :
    ((uSpTwoEquivSU2 x : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((x : U 2) : Matrix (Fin 2) (Fin 2) ℂ) :=
  (rfl)

@[simp]
theorem coe_uSpTwoEquivSU2_symm (y : SU2) :
    (((uSpTwoEquivSU2.symm y : (uSpClosed 2).toSubgroup) : U 2) : Matrix (Fin 2) (Fin 2) ℂ) =
      y :=
  (rfl)

/-- The isomorphism `USp(2) ≃ₜ* SU(2)` carries the Haar probability measure of `USp(2)` to that
of `SU(2)`. -/
theorem map_haarProb_uSpTwoEquivSU2 :
    (haarProb (uSpClosed 2).toSubgroup).map uSpTwoEquivSU2 = haarProb SU2 :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end TauCeti.SatoTate
