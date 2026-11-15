/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Induced
public import TauCeti.Algebra.TypeAHeckeAlgebra.GroupAlgebra
public import TauCeti.Algebra.TypeAHeckeAlgebra.Shuffle.Coset
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
public import TauCeti.RepresentationTheory.Tensor.External
import TauCeti.RepresentationTheory.Induction.Basic
import TauCeti.RepresentationTheory.Induction.Transitivity

/-!
# Group-algebra specializations of the shuffle module

When `q = q⁻¹` (`q ^ 2 = 1`), the quadratic defect `q - q⁻¹` vanishes, so every inverse generator
`(unitT q i)⁻¹` agrees with `T q i`, the inverse shuffle word of a mask `S` becomes the standard
basis element `Tw q (permCoxeterSystem (k + l)) S.toPerm`, and the PBW coset isomorphism
`TauCeti.TypeAHeckeAlgebra.shuffleCosetEquiv` collapses to the mask-length sign gauge
`TauCeti.TypeAHeckeAlgebra.shuffleSignEquiv`.

Via `TauCeti.TypeAHeckeAlgebra.groupRepresentationEquiv`, any `H_l`-module `U` at `q = q⁻¹` is a
representation of `S_l = Equiv.Perm (Fin l)`, and both `shuffleRep k ρ` and `unsignedShuffleRep k ρ`
become representations of `S_(k+l) = Equiv.Perm (Fin (k + l))`. This file identifies both with
symmetric-group parabolic induction along the block embedding
`Equiv.Perm.finSumPermHom k l : S_k × S_l →* S_(k+l)` from the external tensor product
`χ_q ⊠ U`, where `χ_q` is the Coxeter length-power character `σ ↦ q ^ ℓ(σ)` of `S_k`
(`CoxeterSystem.lengthPowHom`):

* `TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraEquiv` sends `Pi.single S u` to
  `(-1) ^ S.length • IndV.mk _ _ S.toPerm⁻¹ (1 ⊗ₜ u)`.
* `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraEquiv` removes the mask-length signs via
  `shuffleSignEquiv`, sending `Pi.single S u` directly to `IndV.mk _ _ S.toPerm⁻¹ (1 ⊗ₜ u)`.
* Specializing to `q = 1` (`TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraOneEquiv`,
  `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraOneEquiv`) yields parabolic induction of
  `triv_k ⊠ U`; specializing to `q = -1`
  (`TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraNegOneEquiv`,
  `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraNegOneEquiv`) yields parabolic induction of
  `sgn_k ⊠ U`.

All equivalences hold over an arbitrary commutative ring `R`, in independent universes for `R` and
`U`, and for all `k l : ℕ` including `k = 0` and `l = 0`.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.shuffleSignRepEquiv`: `shuffleSignEquiv` as a `Representation.Equiv`
  between `shuffleRep` and `unsignedShuffleRep` at `q = q⁻¹`.
* `TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraEquiv` and
  `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraEquiv`: equivalences with parabolic
  induction of `χ_q ⊠ U` at any `q = q⁻¹`.
* `TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraOneEquiv` and
  `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraOneEquiv`: specializations at `q = 1` to
  `Ind_(S_k × S_l)^(S_(k+l)) (triv_k ⊠ U)`.
* `TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraNegOneEquiv` and
  `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraNegOneEquiv`: specializations at `q = -1`
  to `Ind_(S_k × S_l)^(S_(k+l)) (sgn_k ⊠ U)`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.shuffleInvWord_eq_Tw_toPerm`: at `q = q⁻¹`, `shuffleInvWord q S` is
  `Tw q (permCoxeterSystem (k + l)) S.toPerm`.
* `TauCeti.TypeAHeckeAlgebra.shuffleCosetEquiv_eq_shuffleSignEquiv_of_eq_inv`: at `q = q⁻¹`,
  `shuffleCosetEquiv k ρ = shuffleSignEquiv R k l U`.

## Implementation notes

To avoid forcing the ring `R` and module `U` into a common `max` universe as `Rep.indResHomEquiv`
does, the forward map is constructed directly from `TauCeti.TypeAHeckeAlgebra.shuffleLift` and the
inverse map directly from `Representation.Coinvariants.lift`. As in
`TauCeti.RepresentationTheory.Induction.Basic`, generator lemmas with the reducible abbreviation
`Representation.IndV.mk` on the left-hand side are not marked `@[simp]`.

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52.
* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 4.4 and Section 9.1.
-/

public section

open Representation TensorProduct

namespace TauCeti.TypeAHeckeAlgebra

section EqInv

variable {R : Type*} [CommRing R] {q : Rˣ} {k l : ℕ}
variable {U : Type*} [AddCommGroup U] [Module R U]

private theorem inv_unitT_eq_T_of_eq_inv {n : ℕ} (hq : q = q⁻¹) (i : Fin (n - 1)) :
    (↑(unitT q i)⁻¹ : TypeAHeckeAlgebra R q n) = T q i := by
  rw [val_inv_unitT, ← hq, sub_self, map_zero, sub_zero]

/-- At `q = q⁻¹`, the inverse shuffle word of a mask `S` equals the standard basis element
`Tw q (permCoxeterSystem (k + l)) S.toPerm`. -/
theorem shuffleInvWord_eq_Tw_toPerm (hq : q = q⁻¹) (S : ShuffleMask k l) :
    shuffleInvWord q S = Tw q (permCoxeterSystem (k + l)) S.toPerm := by
  obtain ⟨w, hw⟩ := ShuffleMask.exists_isShufflePath S
  rw [← hw.prod_map_inv_unitT, ← hw.prod_map_T_eq_Tw_toPerm]
  congr 1
  exact List.map_congr_left fun i _ ↦ inv_unitT_eq_T_of_eq_inv hq i

/-- At `q = q⁻¹`, `T_(S.toPerm)` acts monomially on the initial mask of `shuffleRep`, sending
`Pi.single initial u` to `(-1) ^ S.length • Pi.single S u` with no lower-length terms. -/
theorem shuffleRep_Tw_toPerm_single_initial_of_eq_inv
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (hq : q = q⁻¹) (S : ShuffleMask k l)
    (u : U) :
    shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) S.toPerm)
        (Pi.single ShuffleMask.initial u) =
      (-1 : R) ^ S.length • Pi.single S u := by
  rw [← shuffleInvWord_eq_Tw_toPerm hq, shuffleRep_shuffleInvWord_single_initial]

/-- At `q = q⁻¹`, `T_(S.toPerm)` sends `Pi.single initial u` directly to `Pi.single S u` in
`unsignedShuffleRep`. -/
theorem unsignedShuffleRep_Tw_toPerm_single_initial_of_eq_inv
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (hq : q = q⁻¹) (S : ShuffleMask k l)
    (u : U) :
    unsignedShuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) S.toPerm)
        (Pi.single ShuffleMask.initial u) =
      Pi.single S u := by
  rw [← shuffleInvWord_eq_Tw_toPerm hq, unsignedShuffleRep_shuffleInvWord_single_initial]

/-- At `q = q⁻¹`, the PBW coset isomorphism `shuffleCosetEquiv` collapses to the mask-length sign
gauge `shuffleSignEquiv`. -/
theorem shuffleCosetEquiv_eq_shuffleSignEquiv_of_eq_inv
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (hq : q = q⁻¹) :
    shuffleCosetEquiv k ρ = shuffleSignEquiv R k l U := by
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.pi_ext fun S u ↦ ?_
  simp [shuffleRep_Tw_toPerm_single_initial_of_eq_inv ρ hq]

variable (k) in
/-- At `q = q⁻¹`, the mask-length sign gauge `TauCeti.TypeAHeckeAlgebra.shuffleSignEquiv` as an
equivalence of `S_(k+l)`-representations from `shuffleRep` to `unsignedShuffleRep`. -/
noncomputable def shuffleSignRepEquiv
    (hq : q = q⁻¹) (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) :
    (groupRepresentationEquiv (permCoxeterSystem (k + l)) hq (shuffleRep k ρ)).Equiv
      (groupRepresentationEquiv (permCoxeterSystem (k + l)) hq (unsignedShuffleRep k ρ)) :=
  .mk (shuffleSignEquiv R k l U)
    ((forall_comp_groupRepresentationEquiv_iff (permCoxeterSystem (k + l)) hq
      (shuffleRep k ρ) (unsignedShuffleRep k ρ) (shuffleSignEquiv R k l U).toLinearMap).mpr
      (shuffleSignEquiv_comp_shuffleRep ρ))

/-- `TauCeti.TypeAHeckeAlgebra.shuffleSignRepEquiv` acts by `shuffleSignEquiv`. -/
@[simp]
theorem shuffleSignRepEquiv_apply (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (f : ShuffleMask k l → U) :
    shuffleSignRepEquiv k hq ρ f = shuffleSignEquiv R k l U f :=
  (rfl)

/-- The inverse of `TauCeti.TypeAHeckeAlgebra.shuffleSignRepEquiv` also acts by
`shuffleSignEquiv`. -/
@[simp]
theorem shuffleSignRepEquiv_symm_apply (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (f : ShuffleMask k l → U) :
    (shuffleSignRepEquiv k hq ρ).symm f = shuffleSignEquiv R k l U f := by
  rw [shuffleSignRepEquiv, Representation.Equiv.mk_symm, Representation.Equiv.mk_apply,
    shuffleSignEquiv_symm]

/-! ### Equivalence with symmetric-group parabolic induction at `q = q⁻¹` -/

private noncomputable abbrev blockFactorRep (k : ℕ) (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) :
    Representation R (Equiv.Perm (Fin k) × Equiv.Perm (Fin l)) (R ⊗[R] U) :=
  (Representation.ofLinearCharacter
    ((permCoxeterSystem k).lengthPowHom q (by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr hq)))
    |>.externalTensor (groupRepresentationEquiv (permCoxeterSystem l) hq ρ)

private noncomputable def shuffleToInd (k : ℕ) (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) :
    (ShuffleMask k l → U) →ₗ[R]
      IndV (Equiv.Perm.finSumPermHom k l) (blockFactorRep k hq ρ) :=
  shuffleLift
    ((groupRepresentationEquiv (permCoxeterSystem (k + l)) hq).symm
      (Representation.ind (Equiv.Perm.finSumPermHom k l) (blockFactorRep k hq ρ)))
    (IndV.mk (Equiv.Perm.finSumPermHom k l) (blockFactorRep k hq ρ) 1 ∘ₗ
      TensorProduct.mk R R U 1)

private theorem shuffleToInd_single (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U) :
    shuffleToInd k hq ρ (Pi.single S u) =
      (-1 : R) ^ S.length •
        IndV.mk (Equiv.Perm.finSumPermHom k l) (blockFactorRep k hq ρ) S.toPerm⁻¹ (1 ⊗ₜ[R] u) := by
  rw [shuffleToInd, shuffleLift_single, shuffleInvWord_eq_Tw_toPerm hq,
    groupRepresentationEquiv_symm_apply_Tw, LinearMap.comp_apply, TensorProduct.mk_apply,
    Representation.ind_mk, one_mul]

private theorem shuffleToInd_intertwining (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U)
    (π : Equiv.Perm (Fin (k + l))) :
    shuffleToInd k hq ρ ∘ₗ groupRepresentationEquiv (permCoxeterSystem (k + l)) hq
        (shuffleRep k ρ) π =
      Representation.ind (Equiv.Perm.finSumPermHom k l) (blockFactorRep k hq ρ) π ∘ₗ
        shuffleToInd k hq ρ := by
  let φ := Equiv.Perm.finSumPermHom k l
  let W₀ := blockFactorRep k hq ρ
  let σ_H := (groupRepresentationEquiv (permCoxeterSystem (k + l)) hq).symm
    (Representation.ind φ W₀)
  have hcomp : ∀ x : TypeAHeckeAlgebra R q (k + l),
      shuffleToInd k hq ρ ∘ₗ shuffleRep k ρ x = σ_H x ∘ₗ shuffleToInd k hq ρ := by
    refine shuffleLift_comp_shuffleRep ρ ?_ ?_
    · intro i hi
      refine LinearMap.ext fun u ↦ ?_
      let i₀ : Fin (k - 1) := ⟨i, by omega⟩
      have hi₀ : (⟨i₀, by omega⟩ : Fin (k + l - 1)) = i := Fin.ext rfl
      rw [LinearMap.comp_apply, LinearMap.comp_apply (IndV.mk φ W₀ 1), TensorProduct.mk_apply,
        LinearMap.smul_apply, LinearMap.comp_apply (IndV.mk φ W₀ 1), TensorProduct.mk_apply,
        groupRepresentationEquiv_symm_apply_T, permCoxeterSystem_simple, ← hi₀,
        ← Equiv.Perm.finSumPerm_transposition_one i₀,
        ← Equiv.Perm.finSumPermHom_apply (BraidGroup.transposition i₀, 1),
        Representation.ind_mk, one_mul, ← map_inv,
        ← mul_one (φ (BraidGroup.transposition i₀, 1)⁻¹),
        ← TauCeti.indV_mk_apply_inv φ W₀ (BraidGroup.transposition i₀, 1)⁻¹ 1, inv_inv,
        externalTensor_apply_tmul, ofLinearCharacter_apply,
        ← permCoxeterSystem_simple, CoxeterSystem.lengthPowHom_apply,
        (permCoxeterSystem k).length_simple, pow_one, mul_one, map_one, one_apply_eq_self,
        ← map_smul, smul_tmul', smul_eq_mul, mul_one]
    · intro j
      refine LinearMap.ext fun u ↦ ?_
      rw [LinearMap.comp_apply (σ_H _), LinearMap.comp_apply (IndV.mk φ W₀ 1),
        LinearMap.comp_apply (IndV.mk φ W₀ 1 ∘ₗ TensorProduct.mk R R U 1),
        LinearMap.comp_apply (IndV.mk φ W₀ 1), TensorProduct.mk_apply, TensorProduct.mk_apply,
        groupRepresentationEquiv_symm_apply_T, permCoxeterSystem_simple,
        ← Equiv.Perm.finSumPerm_one_transposition j,
        ← Equiv.Perm.finSumPermHom_apply (1, BraidGroup.transposition j),
        Representation.ind_mk, one_mul, ← map_inv,
        ← mul_one (φ (1, BraidGroup.transposition j)⁻¹),
        ← TauCeti.indV_mk_apply_inv φ W₀ (1, BraidGroup.transposition j)⁻¹ 1, inv_inv,
        externalTensor_apply_tmul, ofLinearCharacter_apply, map_one, Units.val_one,
        one_mul, groupRepresentationEquiv_apply, ← permCoxeterSystem_simple, Tw_simple]
  have hG := (forall_comp_groupRepresentationEquiv_iff (permCoxeterSystem (k + l)) hq
    (shuffleRep k ρ) σ_H (shuffleToInd k hq ρ)).mpr hcomp π
  rwa [Equiv.apply_symm_apply] at hG

private theorem shuffleRep_Tw_finSumPerm_one (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U)
    (hq2 : q ^ 2 = 1) (σ : Equiv.Perm (Fin k)) (u : U) :
    shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) (Equiv.Perm.finSumPerm σ 1))
        (Pi.single ShuffleMask.initial u) =
      (((permCoxeterSystem k).lengthPowHom q hq2 σ : Rˣ) : R) •
        Pi.single ShuffleMask.initial u := by
  obtain ⟨w, hw⟩ := (permCoxeterSystem k).exists_isReduced σ
  rw [hw.2]
  clear hw
  induction w with
  | nil => simp
  | cons i w ih =>
    have hmul : Equiv.Perm.finSumPerm ((permCoxeterSystem k).simple i *
          (permCoxeterSystem k).wordProd w) (1 : Equiv.Perm (Fin l)) =
        BraidGroup.transposition ⟨i, by omega⟩ *
          Equiv.Perm.finSumPerm ((permCoxeterSystem k).wordProd w) 1 := by
      rw [← Equiv.Perm.finSumPerm_transposition_one i, ← permCoxeterSystem_simple,
        Equiv.Perm.finSumPerm_mul, one_mul]
    have hχ : (((permCoxeterSystem k).lengthPowHom q hq2
          ((permCoxeterSystem k).simple i * (permCoxeterSystem k).wordProd w) : Rˣ) : R) =
        (q : R) * ((permCoxeterSystem k).lengthPowHom q hq2
          ((permCoxeterSystem k).wordProd w) : Rˣ) := by
      rw [map_mul, Units.val_mul, CoxeterSystem.lengthPowHom_apply,
        (permCoxeterSystem k).length_simple, pow_one]
    rw [CoxeterSystem.wordProd_cons, hmul, ← permCoxeterSystem_simple,
      ← Tw_mul_Tw_of_eq_inv (permCoxeterSystem (k + l)) hq, map_mul, mul_apply_eq_comp,
      Tw_simple, ih, map_smul, shuffleRep_T_single_initial_of_lt ρ (by simp; omega),
      hχ, mul_smul, smul_comm (q : R)]

private theorem shuffleRep_Tw_one_finSumPerm (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (τ : Equiv.Perm (Fin l)) (u : U) :
    shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) (Equiv.Perm.finSumPerm 1 τ))
        (Pi.single ShuffleMask.initial u) =
      Pi.single ShuffleMask.initial (ρ (Tw q (permCoxeterSystem l) τ) u) := by
  obtain ⟨w, hw⟩ := (permCoxeterSystem l).exists_isReduced τ
  rw [hw.2]
  clear hw
  induction w with
  | nil => simp
  | cons j w ih =>
    have hmul : Equiv.Perm.finSumPerm (1 : Equiv.Perm (Fin k))
          ((permCoxeterSystem l).simple j * (permCoxeterSystem l).wordProd w) =
        BraidGroup.transposition ⟨k + j, by omega⟩ *
          Equiv.Perm.finSumPerm 1 ((permCoxeterSystem l).wordProd w) := by
      rw [← Equiv.Perm.finSumPerm_one_transposition j, ← permCoxeterSystem_simple,
        Equiv.Perm.finSumPerm_mul, one_mul]
    rw [CoxeterSystem.wordProd_cons, hmul, ← permCoxeterSystem_simple,
      ← Tw_mul_Tw_of_eq_inv (permCoxeterSystem (k + l)) hq,
      ← Tw_mul_Tw_of_eq_inv (permCoxeterSystem l) hq, map_mul, map_mul, mul_apply_eq_comp,
      mul_apply_eq_comp, Tw_simple, Tw_simple, ih, shuffleRep_T_add_single_initial]

private theorem blockFactorRep_intertwining (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U)
    (g : Equiv.Perm (Fin k) × Equiv.Perm (Fin l)) :
    (LinearMap.single R (fun _ : ShuffleMask k l ↦ U) ShuffleMask.initial ∘ₗ
        (TensorProduct.lid R U).toLinearMap) ∘ₗ blockFactorRep k hq ρ g =
      groupRepresentationEquiv (permCoxeterSystem (k + l)) hq (shuffleRep k ρ)
          (Equiv.Perm.finSumPermHom k l g) ∘ₗ
        (LinearMap.single R (fun _ : ShuffleMask k l ↦ U) ShuffleMask.initial ∘ₗ
          (TensorProduct.lid R U).toLinearMap) := by
  rcases g with ⟨σ, τ⟩
  refine TensorProduct.ext' fun c u ↦ ?_
  have hστ : Equiv.Perm.finSumPermHom k l (σ, τ) =
      Equiv.Perm.finSumPerm σ 1 * Equiv.Perm.finSumPerm 1 τ := by
    rw [Equiv.Perm.finSumPermHom_apply, Equiv.Perm.finSumPerm_mul, mul_one, one_mul]
  have hq2 : q ^ 2 = 1 := by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr hq
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    externalTensor_apply_tmul, ofLinearCharacter_apply, TensorProduct.lid_tmul,
    LinearMap.single_apply, groupRepresentationEquiv_apply]
  rw [hστ, ← Tw_mul_Tw_of_eq_inv (permCoxeterSystem (k + l)) hq, map_mul, mul_apply_eq_comp,
    Pi.single_smul', Pi.single_smul', map_smul, map_smul, shuffleRep_Tw_one_finSumPerm hq ρ τ u,
    shuffleRep_Tw_finSumPerm_one hq ρ hq2 σ, mul_smul, smul_comm (_ : R) c]

private noncomputable def indToShuffle (k : ℕ) (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) :
    IndV (Equiv.Perm.finSumPermHom k l) (blockFactorRep k hq ρ) →ₗ[R]
      (ShuffleMask k l → U) :=
  let τ_G := groupRepresentationEquiv (permCoxeterSystem (k + l)) hq (shuffleRep k ρ)
  let f₀ : R ⊗[R] U →ₗ[R] (ShuffleMask k l → U) :=
    LinearMap.single R (fun _ : ShuffleMask k l ↦ U) ShuffleMask.initial ∘ₗ
      (TensorProduct.lid R U).toLinearMap
  Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ R _ fun h ↦ τ_G h⁻¹ ∘ₗ f₀) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv R).toLinearMap)
    fun g ↦ TensorProduct.ext <| MonoidAlgebra.lhom_ext' fun h ↦ LinearMap.ext_ring <|
      TensorProduct.ext' fun c u ↦ by
        have hg : f₀ (blockFactorRep k hq ρ g (c ⊗ₜ[R] u)) =
            τ_G (Equiv.Perm.finSumPermHom k l g) (f₀ (c ⊗ₜ[R] u)) :=
          LinearMap.congr_fun (blockFactorRep_intertwining hq ρ g) (c ⊗ₜ[R] u)
        simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
        suffices τ_G h⁻¹ (τ_G (Equiv.Perm.finSumPermHom k l g)⁻¹
              (f₀ (blockFactorRep k hq ρ g (c ⊗ₜ[R] u)))) =
            τ_G h⁻¹ (f₀ (c ⊗ₜ[R] u)) by
          simpa -zeta [-Equiv.Perm.finSumPermHom_apply, -externalTensor_apply,
            Representation.ofMulAction_single, mul_inv_rev] using this
        congr 1
        rw [hg, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]

private theorem indToShuffle_mk (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U)
    (π : Equiv.Perm (Fin (k + l))) (c : R) (u : U) :
    indToShuffle k hq ρ
        (IndV.mk (Equiv.Perm.finSumPermHom k l) (blockFactorRep k hq ρ) π (c ⊗ₜ[R] u)) =
      c • shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) π⁻¹)
        (Pi.single ShuffleMask.initial u) := by
  simp [indToShuffle, Pi.single_smul']

variable (k) in
/-- **The shuffle module at `q = q⁻¹` is symmetric-group parabolic induction.** Over any
commutative ring `R`, at any unit parameter `q : Rˣ` with `q = q⁻¹`, `shuffleRep k ρ` viewed as a
representation of `S_(k+l)` is canonically isomorphic to the representation induced along
`Equiv.Perm.finSumPermHom k l : S_k × S_l →* S_(k+l)` from `χ_q ⊠ U`, where `χ_q(σ) = q ^ ℓ(σ)` is
`CoxeterSystem.lengthPowHom`. -/
noncomputable def shuffleGroupAlgebraEquiv
    (hq : q = q⁻¹) (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) :
    (groupRepresentationEquiv (permCoxeterSystem (k + l)) hq (shuffleRep k ρ)).Equiv
      (Representation.ind (Equiv.Perm.finSumPermHom k l)
        ((Representation.ofLinearCharacter
            ((permCoxeterSystem k).lengthPowHom q
              (by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr hq))).externalTensor
          (groupRepresentationEquiv (permCoxeterSystem l) hq ρ))) :=
  .mk
    (LinearEquiv.ofLinearMap (shuffleToInd k hq ρ) (indToShuffle k hq ρ)
      (IndV.hom_ext _ _ fun π ↦ TensorProduct.ext' fun c u ↦ by
        have hF := LinearMap.congr_fun (shuffleToInd_intertwining hq ρ π⁻¹)
          (Pi.single ShuffleMask.initial u)
        simp only [LinearMap.comp_apply, groupRepresentationEquiv_apply] at hF
        rw [LinearMap.comp_apply, LinearMap.comp_apply, indToShuffle_mk, map_smul, hF,
          shuffleToInd_single, ShuffleMask.length_initial, pow_zero, one_smul,
          ShuffleMask.toPerm_initial, inv_one, Representation.ind_mk, one_mul, inv_inv,
          ← map_smul, smul_tmul', smul_eq_mul, mul_one, LinearMap.comp_apply LinearMap.id,
          LinearMap.id_apply])
      (LinearMap.pi_ext fun S u ↦ by
        rw [LinearMap.comp_apply, shuffleToInd_single, map_smul, indToShuffle_mk, inv_inv,
          one_smul, shuffleRep_Tw_toPerm_single_initial_of_eq_inv ρ hq, smul_smul, ← mul_pow,
          neg_one_mul, neg_neg, one_pow, one_smul, LinearMap.id_apply]))
    (shuffleToInd_intertwining hq ρ)

/-- `TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraEquiv` sends `Pi.single S u` to
`(-1) ^ S.length • IndV.mk _ _ S.toPerm⁻¹ (1 ⊗ₜ u)`. -/
@[simp]
theorem shuffleGroupAlgebraEquiv_single (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U) :
    shuffleGroupAlgebraEquiv k hq ρ (Pi.single S u) =
      (-1 : R) ^ S.length •
        IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (1 ⊗ₜ[R] u) :=
  shuffleToInd_single hq ρ S u

/-- The inverse of `TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraEquiv` on induced generators:
`⟦π ⊗ₜ (c ⊗ₜ u)⟧ ↦ c • T_(π⁻¹) • Pi.single initial u`. -/
theorem shuffleGroupAlgebraEquiv_symm_mk (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U)
    (π : Equiv.Perm (Fin (k + l))) (c : R) (u : U) :
    (shuffleGroupAlgebraEquiv k hq ρ).symm
        (IndV.mk (Equiv.Perm.finSumPermHom k l) _ π (c ⊗ₜ[R] u)) =
      c • shuffleRep k ρ (Tw q (permCoxeterSystem (k + l)) π⁻¹)
        (Pi.single ShuffleMask.initial u) :=
  indToShuffle_mk hq ρ π c u

/-- On the coset generator at `S.toPerm⁻¹`, the inverse of `shuffleGroupAlgebraEquiv` evaluates to
`(-1) ^ S.length • Pi.single S (c • u)`. -/
theorem shuffleGroupAlgebraEquiv_symm_mk_toPerm_inv (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U)
    (S : ShuffleMask k l) (c : R) (u : U) :
    (shuffleGroupAlgebraEquiv k hq ρ).symm
        (IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (c ⊗ₜ[R] u)) =
      (-1 : R) ^ S.length • Pi.single S (c • u) := by
  rw [shuffleGroupAlgebraEquiv_symm_mk, inv_inv,
    shuffleRep_Tw_toPerm_single_initial_of_eq_inv ρ hq, smul_comm, ← Pi.single_smul']

variable (k) in
/-- **The unsigned shuffle module at `q = q⁻¹` is symmetric-group parabolic induction without
signs.** Composing `TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraEquiv` with the mask-length sign
gauge `TauCeti.TypeAHeckeAlgebra.shuffleSignRepEquiv` cancels the `(-1) ^ S.length` signs on
masks. -/
noncomputable def unsignedShuffleGroupAlgebraEquiv
    (hq : q = q⁻¹) (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) :
    (groupRepresentationEquiv (permCoxeterSystem (k + l)) hq (unsignedShuffleRep k ρ)).Equiv
      (Representation.ind (Equiv.Perm.finSumPermHom k l)
        ((Representation.ofLinearCharacter
            ((permCoxeterSystem k).lengthPowHom q
              (by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr hq))).externalTensor
          (groupRepresentationEquiv (permCoxeterSystem l) hq ρ))) :=
  (shuffleSignRepEquiv k hq ρ).symm.trans (shuffleGroupAlgebraEquiv k hq ρ)

/-- `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraEquiv` sends `Pi.single S u` directly to
`IndV.mk _ _ S.toPerm⁻¹ (1 ⊗ₜ u)`, with no `(-1) ^ S.length` sign. -/
@[simp]
theorem unsignedShuffleGroupAlgebraEquiv_single (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U) :
    unsignedShuffleGroupAlgebraEquiv k hq ρ (Pi.single S u) =
      IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (1 ⊗ₜ[R] u) := by
  rw [unsignedShuffleGroupAlgebraEquiv, Representation.Equiv.trans_apply,
    shuffleSignRepEquiv_symm_apply, shuffleSignEquiv_single, map_smul,
    shuffleGroupAlgebraEquiv_single, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- The inverse of `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraEquiv` on coset generators:
`⟦S.toPerm⁻¹ ⊗ₜ (c ⊗ₜ u)⟧ ↦ Pi.single S (c • u)`. -/
theorem unsignedShuffleGroupAlgebraEquiv_symm_mk_toPerm_inv (hq : q = q⁻¹)
    (ρ : TypeAHeckeAlgebra R q l →ₐ[R] Module.End R U)
    (S : ShuffleMask k l) (c : R) (u : U) :
    (unsignedShuffleGroupAlgebraEquiv k hq ρ).symm
        (IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (c ⊗ₜ[R] u)) =
      Pi.single S (c • u) :=
  EquivLike.injective (unsignedShuffleGroupAlgebraEquiv k hq ρ) <| by
    rw [Representation.Equiv.apply_symm_apply, Pi.single_smul', map_smul,
      unsignedShuffleGroupAlgebraEquiv_single, ← map_smul, smul_tmul', smul_eq_mul, mul_one]

end EqInv

/-! ### Specializations at `q = 1` (`triv_k ⊠ U`) and `q = -1` (`sgn_k ⊠ U`) -/

section Specializations

variable {R : Type*} [CommRing R] {k l : ℕ}
variable {U : Type*} [AddCommGroup U] [Module R U]

variable (k) in
/-- **At `q = 1`, the shuffle module is parabolic induction of `triv_k ⊠ U`.** -/
noncomputable def shuffleGroupAlgebraOneEquiv
    (ρ : TypeAHeckeAlgebra R 1 l →ₐ[R] Module.End R U) :
    (groupRepresentationEquiv (permCoxeterSystem (k + l)) inv_one.symm (shuffleRep k ρ)).Equiv
      (Representation.ind (Equiv.Perm.finSumPermHom k l)
        ((Representation.trivial R (Equiv.Perm (Fin k)) R).externalTensor
          (groupRepresentationEquiv (permCoxeterSystem l) inv_one.symm ρ))) :=
  (shuffleGroupAlgebraEquiv k inv_one.symm ρ).trans <|
    (Representation.Equiv.mk (LinearEquiv.refl R _) fun g ↦ by
      rw [CoxeterSystem.lengthPowHom_one, Representation.ofLinearCharacter_one,
        LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id]).ind
      (Equiv.Perm.finSumPermHom k l)

/-- `TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraOneEquiv` sends `Pi.single S u` to
`(-1) ^ S.length • IndV.mk _ _ S.toPerm⁻¹ (1 ⊗ₜ u)`. -/
@[simp]
theorem shuffleGroupAlgebraOneEquiv_single
    (ρ : TypeAHeckeAlgebra R 1 l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U) :
    shuffleGroupAlgebraOneEquiv k ρ (Pi.single S u) =
      (-1 : R) ^ S.length •
        IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (1 ⊗ₜ[R] u) := by
  rw [shuffleGroupAlgebraOneEquiv, Representation.Equiv.trans_apply,
    shuffleGroupAlgebraEquiv_single, map_smul, Representation.Equiv.ind_mk]
  rfl

/-- The inverse of `TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraOneEquiv` on the coset generator at
`S.toPerm⁻¹` evaluates to `(-1) ^ S.length • Pi.single S (c • u)`. -/
theorem shuffleGroupAlgebraOneEquiv_symm_mk_toPerm_inv
    (ρ : TypeAHeckeAlgebra R 1 l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (c : R) (u : U) :
    (shuffleGroupAlgebraOneEquiv k ρ).symm
        (IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (c ⊗ₜ[R] u)) =
      (-1 : R) ^ S.length • Pi.single S (c • u) :=
  EquivLike.injective (shuffleGroupAlgebraOneEquiv k ρ) <| by
    rw [Representation.Equiv.apply_symm_apply, map_smul, Pi.single_smul', map_smul,
      shuffleGroupAlgebraOneEquiv_single, smul_comm c, smul_smul ((-1 : R) ^ S.length),
      ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, ← map_smul, smul_tmul', smul_eq_mul,
      mul_one]

variable (k) in
/-- **At `q = 1`, the unsigned shuffle module is parabolic induction of `triv_k ⊠ U` without
signs.** -/
noncomputable def unsignedShuffleGroupAlgebraOneEquiv
    (ρ : TypeAHeckeAlgebra R 1 l →ₐ[R] Module.End R U) :
    (groupRepresentationEquiv (permCoxeterSystem (k + l)) inv_one.symm
        (unsignedShuffleRep k ρ)).Equiv
      (Representation.ind (Equiv.Perm.finSumPermHom k l)
        ((Representation.trivial R (Equiv.Perm (Fin k)) R).externalTensor
          (groupRepresentationEquiv (permCoxeterSystem l) inv_one.symm ρ))) :=
  (shuffleSignRepEquiv k inv_one.symm ρ).symm.trans (shuffleGroupAlgebraOneEquiv k ρ)

/-- `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraOneEquiv` sends `Pi.single S u` directly
to `IndV.mk _ _ S.toPerm⁻¹ (1 ⊗ₜ u)`. -/
@[simp]
theorem unsignedShuffleGroupAlgebraOneEquiv_single
    (ρ : TypeAHeckeAlgebra R 1 l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U) :
    unsignedShuffleGroupAlgebraOneEquiv k ρ (Pi.single S u) =
      IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (1 ⊗ₜ[R] u) := by
  rw [unsignedShuffleGroupAlgebraOneEquiv, Representation.Equiv.trans_apply,
    shuffleSignRepEquiv_symm_apply, shuffleSignEquiv_single, map_smul,
    shuffleGroupAlgebraOneEquiv_single, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
    one_smul]

/-- The inverse of `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraOneEquiv` on the coset
generator at `S.toPerm⁻¹` evaluates to `Pi.single S (c • u)`. -/
theorem unsignedShuffleGroupAlgebraOneEquiv_symm_mk_toPerm_inv
    (ρ : TypeAHeckeAlgebra R 1 l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (c : R) (u : U) :
    (unsignedShuffleGroupAlgebraOneEquiv k ρ).symm
        (IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (c ⊗ₜ[R] u)) =
      Pi.single S (c • u) :=
  EquivLike.injective (unsignedShuffleGroupAlgebraOneEquiv k ρ) <| by
    rw [Representation.Equiv.apply_symm_apply, Pi.single_smul', map_smul,
      unsignedShuffleGroupAlgebraOneEquiv_single, ← map_smul, smul_tmul', smul_eq_mul, mul_one]

variable (k) in
/-- **At `q = -1`, the shuffle module is parabolic induction of `sgn_k ⊠ U`.** -/
noncomputable def shuffleGroupAlgebraNegOneEquiv
    (ρ : TypeAHeckeAlgebra R (-1) l →ₐ[R] Module.End R U) :
    (groupRepresentationEquiv (permCoxeterSystem (k + l)) (by ext; simp) (shuffleRep k ρ)).Equiv
      (Representation.ind (Equiv.Perm.finSumPermHom k l)
        ((Representation.ofLinearCharacter (signLinearCharacter R (Fin k))).externalTensor
          (groupRepresentationEquiv (permCoxeterSystem l) (by ext; simp) ρ))) :=
  let hq : (-1 : Rˣ) = (-1 : Rˣ)⁻¹ := by ext; simp
  let hχ : (permCoxeterSystem k).lengthPowHom (-1 : Rˣ)
      (by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr hq) =
        signLinearCharacter R (Fin k) :=
    (permCoxeterSystem k).ext_simple fun i ↦ by
      rw [CoxeterSystem.lengthPowHom_apply, (permCoxeterSystem k).length_simple, pow_one,
        permCoxeterSystem_simple, BraidGroup.transposition_eq_swap,
        signLinearCharacter_swap (BraidGroup.strand_ne_strandSucc i)]
  (shuffleGroupAlgebraEquiv k hq ρ).trans <|
    (Representation.Equiv.mk (LinearEquiv.refl R _) fun g ↦ by
      rw [hχ, LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id]).ind
      (Equiv.Perm.finSumPermHom k l)

/-- `TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraNegOneEquiv` sends `Pi.single S u` to
`(-1) ^ S.length • IndV.mk _ _ S.toPerm⁻¹ (1 ⊗ₜ u)`. -/
@[simp]
theorem shuffleGroupAlgebraNegOneEquiv_single
    (ρ : TypeAHeckeAlgebra R (-1) l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U) :
    shuffleGroupAlgebraNegOneEquiv k ρ (Pi.single S u) =
      (-1 : R) ^ S.length •
        IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (1 ⊗ₜ[R] u) := by
  rw [shuffleGroupAlgebraNegOneEquiv, Representation.Equiv.trans_apply,
    shuffleGroupAlgebraEquiv_single, map_smul, Representation.Equiv.ind_mk]
  rfl

/-- The inverse of `TauCeti.TypeAHeckeAlgebra.shuffleGroupAlgebraNegOneEquiv` on the coset
generator at `S.toPerm⁻¹` evaluates to `(-1) ^ S.length • Pi.single S (c • u)`. -/
theorem shuffleGroupAlgebraNegOneEquiv_symm_mk_toPerm_inv
    (ρ : TypeAHeckeAlgebra R (-1) l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (c : R) (u : U) :
    (shuffleGroupAlgebraNegOneEquiv k ρ).symm
        (IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (c ⊗ₜ[R] u)) =
      (-1 : R) ^ S.length • Pi.single S (c • u) :=
  EquivLike.injective (shuffleGroupAlgebraNegOneEquiv k ρ) <| by
    rw [Representation.Equiv.apply_symm_apply, map_smul, Pi.single_smul', map_smul,
      shuffleGroupAlgebraNegOneEquiv_single, smul_comm c, smul_smul ((-1 : R) ^ S.length),
      ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, ← map_smul, smul_tmul', smul_eq_mul,
      mul_one]

variable (k) in
/-- **At `q = -1`, the unsigned shuffle module is parabolic induction of `sgn_k ⊠ U` without
signs.** -/
noncomputable def unsignedShuffleGroupAlgebraNegOneEquiv
    (ρ : TypeAHeckeAlgebra R (-1) l →ₐ[R] Module.End R U) :
    (groupRepresentationEquiv (permCoxeterSystem (k + l)) (by ext; simp)
        (unsignedShuffleRep k ρ)).Equiv
      (Representation.ind (Equiv.Perm.finSumPermHom k l)
        ((Representation.ofLinearCharacter (signLinearCharacter R (Fin k))).externalTensor
          (groupRepresentationEquiv (permCoxeterSystem l) (by ext; simp) ρ))) :=
  (shuffleSignRepEquiv k (by ext; simp) ρ).symm.trans (shuffleGroupAlgebraNegOneEquiv k ρ)

/-- `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraNegOneEquiv` sends `Pi.single S u`
directly to `IndV.mk _ _ S.toPerm⁻¹ (1 ⊗ₜ u)`. -/
@[simp]
theorem unsignedShuffleGroupAlgebraNegOneEquiv_single
    (ρ : TypeAHeckeAlgebra R (-1) l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (u : U) :
    unsignedShuffleGroupAlgebraNegOneEquiv k ρ (Pi.single S u) =
      IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (1 ⊗ₜ[R] u) := by
  rw [unsignedShuffleGroupAlgebraNegOneEquiv, Representation.Equiv.trans_apply,
    shuffleSignRepEquiv_symm_apply, shuffleSignEquiv_single, map_smul,
    shuffleGroupAlgebraNegOneEquiv_single, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
    one_smul]

/-- The inverse of `TauCeti.TypeAHeckeAlgebra.unsignedShuffleGroupAlgebraNegOneEquiv` on the coset
generator at `S.toPerm⁻¹` evaluates to `Pi.single S (c • u)`. -/
theorem unsignedShuffleGroupAlgebraNegOneEquiv_symm_mk_toPerm_inv
    (ρ : TypeAHeckeAlgebra R (-1) l →ₐ[R] Module.End R U) (S : ShuffleMask k l) (c : R) (u : U) :
    (unsignedShuffleGroupAlgebraNegOneEquiv k ρ).symm
        (IndV.mk (Equiv.Perm.finSumPermHom k l) _ S.toPerm⁻¹ (c ⊗ₜ[R] u)) =
      Pi.single S (c • u) :=
  EquivLike.injective (unsignedShuffleGroupAlgebraNegOneEquiv k ρ) <| by
    rw [Representation.Equiv.apply_symm_apply, Pi.single_smul', map_smul,
      unsignedShuffleGroupAlgebraNegOneEquiv_single, ← map_smul, smul_tmul', smul_eq_mul, mul_one]

end Specializations

end TauCeti.TypeAHeckeAlgebra
