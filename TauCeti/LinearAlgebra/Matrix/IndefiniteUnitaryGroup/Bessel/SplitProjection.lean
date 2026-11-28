/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Exchange
import TauCeti.LinearAlgebra.Matrix.Permutation

/-!
# The Bessel unipotent group over an exchange ring

Projection to one component of an exchange ring identifies the Bessel unipotent group with the
block upper unitriangular matrices in the split basis. Inverse transpose reverses the triangular
condition, and the hyperbolic pairing reverses it back. This identifies the local matrix group
that occurs at a split residue place.

The local projection is the split matrix step in `New.Filling.mem_reducedImage_besselU` of
`grh-lean`, `grh/src/New/Spanning/Unfolding/ReducedGroups.lean` (revision `72fead1`).
-/

public section

open Matrix

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [StarRing S]
variable {ϱ : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The permutation pairing each hyperbolic basis vector with its dual and fixing the middle
block. -/
private def splitSwap (ϱ : ℕ) (κ : Type*) : Equiv.Perm (BesselIndex ϱ κ) where
  toFun := Sum.elim (fun i ↦ .inr (.inr i)) (Sum.elim (fun i ↦ .inr (.inl i)) Sum.inl)
  invFun := Sum.elim (fun i ↦ .inr (.inr i)) (Sum.elim (fun i ↦ .inr (.inl i)) Sum.inl)
  left_inv := by rintro (i | i | i) <;> rfl
  right_inv := by rintro (i | i | i) <;> rfl

omit [Fintype κ] [DecidableEq κ] in
private theorem splitLevel_splitSwap (i : BesselIndex ϱ κ) :
    splitLevel (splitSwap ϱ κ i) + splitLevel i = 2 * ϱ := by
  rcases i with (i | i | i) <;> simp [splitSwap] <;> omega

/-- The unit diagonal weights in the split Gram matrix, before permuting the hyperbolic indices. -/
private def splitWeight (N : Sˣ) : BesselIndex ϱ κ → Sˣ
  | .inr (.inl (.inr _)) => -N
  | _ => 1

omit [StarRing S] in
private theorem coe_splitGramUnit (N : Sˣ) :
    ((permutationGL (splitSwap ϱ κ) * diagGL (splitWeight N) : GL (BesselIndex ϱ κ) S) :
      Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) S) = splitGram ϱ (middleGram (N : S)) := by
  ext (i | i | i) (j | j | j)
  case' inr.inl.inr.inl =>
    rcases i with i | u <;> rcases j with j | v
  all_goals simp [Units.val_mul, diagGL_coe, permutationGL_coe, mul_diagonal,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, splitWeight, splitSwap, Matrix.one_apply]

private theorem inverseTranspose_mem_unitriangular_splitSwap
    {g : GL (BesselIndex ϱ κ) R} (hg : g ∈ unitriangularSubgroup splitLevel R) :
    (permutationGL (splitSwap ϱ κ) : GL (BesselIndex ϱ κ) R)⁻¹ *
        GeneralLinearGroup.inverseTranspose g * permutationGL (splitSwap ϱ κ) ∈
      unitriangularSubgroup splitLevel R := by
  have h := (mem_unitriangularSubgroup (lev := splitLevel)).mp
    ((unitriangularSubgroup splitLevel R).inv_mem hg)
  apply (mem_unitriangularSubgroup (lev := splitLevel)).mpr
  apply blockUnitriangular_of_apply_eq_one_apply_of_not_lt
  intro i j hij
  have hrev : ¬ splitLevel (splitSwap ϱ κ j) < splitLevel (splitSwap ϱ κ i) := by
    have hi := splitLevel_splitSwap i
    have hj := splitLevel_splitSwap j
    omega
  have hentry : ((g⁻¹ : GL (BesselIndex ϱ κ) R) : Matrix _ _ R)
      (splitSwap ϱ κ j) (splitSwap ϱ κ i) = (1 : Matrix (BesselIndex ϱ κ) _ R) i j := by
    rcases lt_or_eq_of_le (le_of_not_gt hrev) with hlt | heq
    · have hji : j ≠ i := fun e ↦ (e ▸ hlt).false
      simp [h.blockTriangular hlt, Ne.symm hji]
    · rw [h.apply_of_eq heq.symm]
      simp [Matrix.one_apply, eq_comm]
  simp only [Units.val_mul, ← map_inv permutationGL, permutationGL_coe,
    ← Matrix.permMatrixHom_apply, Matrix.permMatrixHom_mul_apply, Matrix.mul_permMatrixHom_apply,
    GeneralLinearGroup.coe_inverseTranspose, transpose_apply]
  exact hentry

private theorem blockUnitriangular_iff_exchangeFst (e : S ≃+* R × R)
    (he : ∀ x, e (star x) = (e x).swap) (N : Sˣ)
    {J : GL (BesselIndex ϱ κ) S} (hJ : J = permutationGL (splitSwap ϱ κ) * diagGL (splitWeight N))
    (hHerm : J.val.IsHermitian) (g : unitaryGroupOf J.val) :
    g.val.val.BlockUnitriangular splitLevel ↔
      Matrix.unitaryGroupOf.exchangeFstEquiv e he J hHerm g ∈
        unitriangularSubgroup splitLevel R := by
  let f := (RingHom.fst R R).comp e.toRingHom
  let s := (RingHom.snd R R).comp e.toRingHom
  have mapOne (p : S →+* R) (i j : BesselIndex ϱ κ) :
      p ((1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) S) i j) =
        (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j :=
    congrFun₂ (map_one (p.mapMatrix (m := BesselIndex ϱ κ))) i j
  rw [Matrix.unitaryGroupOf.exchangeFstEquiv_apply]
  refine ⟨fun hg ↦ (mem_unitriangularSubgroup (lev := splitLevel)).mpr ?_, fun hg ↦ ?_⟩
  · refine blockUnitriangular_iff.mpr ⟨fun i j hij ↦ ?_, fun i j hij ↦ ?_⟩
    · simp [GeneralLinearGroup.map_apply, hg.blockTriangular hij]
    · rw [GeneralLinearGroup.map_apply, hg.apply_of_eq hij]
      exact mapOne f i j
  have hs : GeneralLinearGroup.map s g.val ∈ unitriangularSubgroup splitLevel R := by
    have heq := (mem_unitaryGroupOf_iff_snd_eq_inverseTranspose e he J hHerm g.val).mp g.property
    rw [heq]
    let D := diagGL (fun i : BesselIndex ϱ κ ↦ Units.map (s : S →* R) (splitWeight N i))
    let P : GL (BesselIndex ϱ κ) R := permutationGL (splitSwap ϱ κ)
    have hJD : GeneralLinearGroup.map s J = P * D := by
      simp only [hJ, map_mul, map_permutationGL, map_diagGL, P, D]
    rw [hJD, _root_.mul_inv_rev]
    have hD : D ∈ blockTriangularGroup R splitLevel := mem_blockTriangularGroup_iff.mpr (by
      simp only [D, diagGL_coe]
      exact blockTriangular_diagonal _)
    simpa only [mul_assoc] using
      conj_mem_unitriangularSubgroup hD (inverseTranspose_mem_unitriangular_splitSwap hg)
  have h₁ := (mem_unitriangularSubgroup (lev := splitLevel)).mp hg
  have h₂ := (mem_unitriangularSubgroup (lev := splitLevel)).mp hs
  apply blockUnitriangular_of_apply_eq_one_apply_of_not_lt
  intro i j hij
  have entry (M : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
      (hM : M.BlockUnitriangular splitLevel) : M i j = (1 : Matrix _ _ R) i j := by
    rcases lt_or_eq_of_le (le_of_not_gt hij) with hlt | heq
    · have hne : i ≠ j := fun e ↦ (congrArg splitLevel e).symm.not_lt hlt
      simp [hM.blockTriangular hlt, one_apply_ne hne]
    · exact hM.apply_of_eq heq.symm
  apply e.injective
  exact Prod.ext ((entry _ h₁).trans (mapOne f i j).symm)
    ((entry _ h₂).trans (mapOne s i j).symm)

/-- The Bessel unipotent group for `diag(1, −N)` over a split coefficient ring, with `N` a
self-adjoint unit, is identified by the first projection with the block unitriangular group. -/
def besselUExchangeFstEquiv (e : S ≃+* R × R) (he : ∀ x, e (star x) = (e x).swap)
    (ϱ : ℕ) (κ : Type*) [Fintype κ] [DecidableEq κ] (N : Sˣ) (hN : star (N : S) = N) :
    besselU ϱ (middleGram (κ := κ) (N : S)) ≃*
      unitriangularSubgroup (splitLevel (ϱ := ϱ) (μ := κ ⊕ Unit)) R := by
  let J : GL (BesselIndex ϱ κ) S := permutationGL (splitSwap ϱ κ) * diagGL (splitWeight N)
  have hJ : (J : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) S) =
      splitGram ϱ (middleGram (N : S)) := coe_splitGramUnit N
  have hHerm : (J : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) S).IsHermitian := by
    rw [hJ]
    exact isHermitian_splitGram (isHermitian_middleGram hN)
  let F := Matrix.unitaryGroupOf.exchangeFstEquiv e he J hHerm
  let T := MulEquiv.subgroupCongr (congrArg unitaryGroupOf hJ.symm)
  let E := T.trans F
  have hE (g : unitaryGroupOf (splitGram ϱ (middleGram (κ := κ) (N : S)))) :
      g ∈ besselU ϱ (middleGram (N : S)) ↔ E g ∈ unitriangularSubgroup splitLevel R := by
    simpa only [E, T, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, mem_besselU] using
      blockUnitriangular_iff_exchangeFst e he N rfl hHerm (T g)
  apply (E.subgroupMap (besselU ϱ (middleGram (N : S)))).trans
  apply MulEquiv.subgroupCongr
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (hE g).mp hg
  · intro hy
    exact ⟨E.symm y, (hE _).mpr (by simpa using hy), E.apply_symm_apply y⟩

/-- On the underlying invertible matrix, the split Bessel equivalence is entrywise projection. -/
@[simp] theorem coe_besselUExchangeFstEquiv_apply (e : S ≃+* R × R)
    (he : ∀ x, e (star x) = (e x).swap) (ϱ : ℕ) (κ : Type*) [Fintype κ] [DecidableEq κ]
    (N : Sˣ) (hN : star (N : S) = N) (g : besselU ϱ (middleGram (κ := κ) (N : S))) :
    (besselUExchangeFstEquiv e he ϱ κ N hN g).val =
      GeneralLinearGroup.map ((RingHom.fst R R).comp e.toRingHom) g.val.val := by
  simp only [besselUExchangeFstEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply, Matrix.unitaryGroupOf.exchangeFstEquiv_apply]

end TauCeti
