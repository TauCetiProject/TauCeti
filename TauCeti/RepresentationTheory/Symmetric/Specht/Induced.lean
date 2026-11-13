/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.SumCongr
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.Induction.CharTwist
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Symmetric.Specht.SignTranspose
public import TauCeti.RepresentationTheory.Tensor.External

/-!
# Induced Specht modules and their transpose comparison

For partitions `μ ⊢ a` and `ν ⊢ b`, the representation `inducedSpecht μ ν` of `S_(a+b)` is induced
along the block embedding `Equiv.Perm.finSumPermHom a b : S_a × S_b →* S_(a+b)` from the external
tensor product `S^μ ⊠ S^ν` of `S_a × S_b`. For `ξ ⊢ a + b`, the space of intertwining maps
`S^ξ → inducedSpecht μ ν` is the multiplicity space `C_(μ,ν)^ξ` of the Littlewood--Richardson
rule. This file proves that transposing all three shapes preserves it:

`C_(μ,ν)^ξ ≃ C_(μᵗ,νᵗ)^(ξᵗ)`.

The route is the sign twist. Restricted along the block embedding, the sign of `S_(a+b)` is the
product of the signs of the two blocks (`TauCeti.signLinearCharacter_comp_finSumPermHom`), so the
twist of `S^μ ⊠ S^ν` by the restricted sign is `(S^μ ⊗ sgn) ⊠ (S^ν ⊗ sgn) ≅ S^(μᵗ) ⊠ S^(νᵗ)`.
Inducing, and moving the sign out of the induced representation by the projection formula
(`TauCeti.indCharTwistEquiv`, that is `Ind(W ⊗ Res sgn) ≅ Ind(W) ⊗ sgn`), gives
`inducedSpecht μᵗ νᵗ ≅ inducedSpecht μ ν ⊗ sgn` (`TauCeti.inducedSpechtConjugateEquiv`).
Twisting both sides of an intertwining map by the sign does not change it, and `S^ξ ⊗ sgn ≅ S^(ξᵗ)`
identifies the source.

Twists are taken with `Representation.charTwist` rather than by tensoring with the line of the
sign: the carrier stays the same, so twisting both sides of an intertwining map literally keeps the
map (`Representation.IntertwiningMap.charTwistLinearEquiv`), with no unitor to cancel.

## Main definitions

* `TauCeti.inducedSpecht`: `Ind_(S_a × S_b)^(S_(a+b)) (S^μ ⊠ S^ν)`.
* `TauCeti.spechtModuleCharTwistSignEquiv`: the sign twist of `S^μ` is `S^(μᵗ)`.
* `TauCeti.inducedSpechtConjugateEquiv`: `inducedSpecht μᵗ νᵗ ≃ inducedSpecht μ ν ⊗ sgn`.
* `TauCeti.inducedSpechtTranspose`: **the transpose comparison of the induced multiplicity
  spaces**, `Hom(S^ξ, inducedSpecht μ ν) ≃ Hom(S^(ξᵗ), inducedSpecht μᵗ νᵗ)`.

## Main statements

* `TauCeti.spechtModuleCharTwistSignEquiv_apply`, `TauCeti.inducedSpechtConjugateEquiv_mk`: the
  two sign-transpose equivalences on elements and on generators, with their inverses.
* `TauCeti.inducedSpechtTranspose_apply`, `TauCeti.inducedSpechtTranspose_symm_apply`: the
  comparison and its inverse are conjugation by the two sign-transpose equivalences.
* `TauCeti.finrank_intertwiningMap_inducedSpecht_conjugate`: the two multiplicities agree.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Theorem 16.4 and
  §8.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 4.
-/

public section

open CategoryTheory MonoidalCategory Representation

namespace TauCeti

variable {a b : ℕ}

/-- **The induced Specht representation** `Ind_(S_a × S_b)^(S_(a+b)) (S^μ ⊠ S^ν)`: the external
tensor product of the Specht modules of `μ ⊢ a` and `ν ⊢ b`, induced along the block embedding
`Equiv.Perm.finSumPermHom a b`. Its intertwining maps from `S^ξ`, for `ξ ⊢ a + b`, form the
Littlewood--Richardson multiplicity space of `ξ` in the induction product of `μ` and `ν`. -/
noncomputable abbrev inducedSpecht {R : Type*} [CommRing R] (μ : a.Partition) (ν : b.Partition) :
    Representation R (Equiv.Perm (Fin (a + b)))
      (IndV (Equiv.Perm.finSumPermHom a b)
        (externalTensor (spechtModule (R := R) μ).ρ (spechtModule (R := R) ν).ρ)) :=
  ind (Equiv.Perm.finSumPermHom a b)
    (externalTensor (spechtModule (R := R) μ).ρ (spechtModule (R := R) ν).ρ)

section Transpose

variable {n : ℕ}

/-- **The sign twist of a Specht module is the Specht module of the conjugate partition**,
`S^μ ⊗ sgn ≅ S^(μᵗ)`, as an equivalence of representations out of the twist
`Representation.charTwist`: it is `TauCeti.spechtModuleTensorSignIso` with the line of the sign
absorbed. -/
noncomputable def spechtModuleCharTwistSignEquiv (μ : n.Partition) :
    (charTwist (signLinearCharacter ℚ (Fin n)) (spechtModule (R := ℚ) μ).ρ).Equiv
      (spechtModule (R := ℚ) μ.conjugate).ρ :=
  -- the action on `S^μ ⊗ FDRep.of (ofLinearCharacter sgn)` is `tprod` of the two actions by
  -- definition (`FDRep.tensor_ρ` and `FDRep.of_ρ'` are both `rfl`)
  (tprodOfLinearCharacterEquivCharTwist _ _).symm.trans <|
    FDRep.isoToEquiv ((whiskerLeftIso (spechtModule (R := ℚ) μ)
      (eqToIso (FDRep.ofLinearCharacter_def (signLinearCharacter ℚ (Fin n))))).symm ≪≫
        spechtModuleTensorSignIso μ)

/-- `TauCeti.spechtModuleCharTwistSignEquiv` sends `v` to the image of `v ⊗ 1` under the
equivalence `YoungTableau.spechtSubrepresentationTensorSignEquiv` of the row-superstandard tableau
of `μ`, transported along `YoungDiagram.ofPartition_conjugate`, as in
`TauCeti.isoToLinearEquiv_spechtModuleTensorSignIso_apply`. -/
theorem spechtModuleCharTwistSignEquiv_apply (μ : n.Partition) (v : spechtModule (R := ℚ) μ) :
    spechtModuleCharTwistSignEquiv μ v =
      spechtSubrepresentationCongr (YoungDiagram.ofPartition_conjugate μ).symm
        ((YoungDiagram.card_ofPartition μ).symm.trans (YoungDiagram.card_transpose _).symm)
        (YoungDiagram.card_ofPartition μ.conjugate).symm
        (YoungTableau.spechtSubrepresentationTensorSignEquiv
          (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition μ)).toTableau
          (v ⊗ₜ[ℚ] (1 : ℚ))) := by
  refine (Representation.Equiv.trans_apply _ _ v).trans <|
    (DFunLike.congr_fun (FDRep.toLinearEquiv_isoToEquiv _) _).trans ?_
  rw [tprodOfLinearCharacterEquivCharTwist_symm_apply, FDRep.isoToLinearEquiv_trans,
    LinearEquiv.trans_apply,
    isoToLinearEquiv_spechtModuleTensorSignIso_apply, FDRep.isoToLinearEquiv_symm,
    LinearEquiv.apply_symm_apply]

/-- The inverse of `TauCeti.spechtModuleCharTwistSignEquiv`, through the inverse of
`YoungTableau.spechtSubrepresentationTensorSignEquiv`. -/
theorem spechtModuleCharTwistSignEquiv_symm_apply (μ : n.Partition)
    (w : spechtModule (R := ℚ) μ.conjugate) :
    (spechtModuleCharTwistSignEquiv μ).symm w =
      TensorProduct.rid ℚ _ ((YoungTableau.spechtSubrepresentationTensorSignEquiv
          (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition μ)).toTableau).symm
        ((spechtSubrepresentationCongr (YoungDiagram.ofPartition_conjugate μ).symm
          ((YoungDiagram.card_ofPartition μ).symm.trans (YoungDiagram.card_transpose _).symm)
          (YoungDiagram.card_ofPartition μ.conjugate).symm).symm w)) := by
  rw [← (spechtModuleCharTwistSignEquiv μ).symm_apply_apply (TensorProduct.rid ℚ _ _),
    spechtModuleCharTwistSignEquiv_apply, ← TensorProduct.rid_symm_apply,
    LinearEquiv.symm_apply_apply, Representation.Equiv.apply_symm_apply,
    Representation.Equiv.apply_symm_apply]

/-- **Transposing both shapes twists the induced Specht representation by the sign**:
`Ind(S^(μᵗ) ⊠ S^(νᵗ)) ≅ Ind(S^μ ⊠ S^ν) ⊗ sgn_(a+b)`. The factors are the sign twists of `S^μ` and
`S^ν`, the external product of the two signs is the restricted sign
(`TauCeti.signLinearCharacter_comp_finSumPermHom`), and the projection formula moves the sign out
of the induced representation (`TauCeti.indCharTwistEquiv`). -/
noncomputable def inducedSpechtConjugateEquiv (μ : a.Partition) (ν : b.Partition) :
    (inducedSpecht (R := ℚ) μ.conjugate ν.conjugate).Equiv
      (charTwist (signLinearCharacter ℚ (Fin (a + b))) (inducedSpecht (R := ℚ) μ ν)) :=
  ((((spechtModuleCharTwistSignEquiv μ).symm.externalTensor
      (spechtModuleCharTwistSignEquiv ν).symm).trans
    (.mk (LinearEquiv.refl ℚ _) fun g => by
      rw [externalTensor_charTwist, ← signLinearCharacter_comp_finSumPermHom,
        LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id])).ind _).trans
    (indCharTwistEquiv _ _ _)

/-- `TauCeti.inducedSpechtConjugateEquiv` on generators:
`⟦h ⊗ₜ (v ⊗ₜ w)⟧ ↦ sgn(h⁻¹) ⟦h ⊗ₜ (e_μ⁻¹ v ⊗ₜ e_ν⁻¹ w)⟧`, where `e_μ` and `e_ν` are the sign
twist equivalences `TauCeti.spechtModuleCharTwistSignEquiv`. -/
theorem inducedSpechtConjugateEquiv_mk (μ : a.Partition) (ν : b.Partition)
    (h : Equiv.Perm (Fin (a + b))) (v : spechtModule (R := ℚ) μ.conjugate)
    (w : spechtModule (R := ℚ) ν.conjugate) :
    inducedSpechtConjugateEquiv μ ν (IndV.mk _ _ h (v ⊗ₜ[ℚ] w)) =
      ((signLinearCharacter ℚ (Fin (a + b)) h⁻¹ : ℚˣ) : ℚ) •
        IndV.mk _ _ h ((spechtModuleCharTwistSignEquiv μ).symm v ⊗ₜ[ℚ]
          (spechtModuleCharTwistSignEquiv ν).symm w) := by
  rw [inducedSpechtConjugateEquiv, Representation.Equiv.trans_apply, Representation.Equiv.ind_mk,
    Representation.Equiv.trans_apply, Representation.Equiv.externalTensor_tmul]
  exact indCharTwistEquiv_mk _ _ _ h _

/-- The inverse of `TauCeti.inducedSpechtConjugateEquiv` on generators:
`⟦h ⊗ₜ (v ⊗ₜ w)⟧ ↦ sgn(h) ⟦h ⊗ₜ (e_μ v ⊗ₜ e_ν w)⟧`. -/
theorem inducedSpechtConjugateEquiv_symm_mk (μ : a.Partition) (ν : b.Partition)
    (h : Equiv.Perm (Fin (a + b))) (v : spechtModule (R := ℚ) μ)
    (w : spechtModule (R := ℚ) ν) :
    (inducedSpechtConjugateEquiv μ ν).symm (IndV.mk _ _ h (v ⊗ₜ[ℚ] w)) =
      ((signLinearCharacter ℚ (Fin (a + b)) h : ℚˣ) : ℚ) •
        IndV.mk _ _ h (spechtModuleCharTwistSignEquiv μ v ⊗ₜ[ℚ]
          spechtModuleCharTwistSignEquiv ν w) := by
  rw [← (inducedSpechtConjugateEquiv μ ν).symm_apply_apply
      (((signLinearCharacter ℚ (Fin (a + b)) h : ℚˣ) : ℚ) • IndV.mk _ _ h
        (spechtModuleCharTwistSignEquiv μ v ⊗ₜ[ℚ] spechtModuleCharTwistSignEquiv ν w)),
    map_smul, inducedSpechtConjugateEquiv_mk, Representation.Equiv.symm_apply_apply,
    Representation.Equiv.symm_apply_apply, smul_smul, ← Units.val_mul, ← map_mul, mul_inv_cancel,
    map_one, Units.val_one, one_smul]

/-- **The transpose comparison of induced multiplicity spaces**: for `μ ⊢ a`, `ν ⊢ b` and
`ξ ⊢ a + b`, the intertwining maps `S^ξ → Ind(S^μ ⊠ S^ν)` are identified with the intertwining
maps `S^(ξᵗ) → Ind(S^(μᵗ) ⊠ S^(νᵗ))`. An intertwining map is twisted by the sign on both sides,
which keeps the map, and is then conjugated by `S^ξ ⊗ sgn ≅ S^(ξᵗ)` at the source and by
`TauCeti.inducedSpechtConjugateEquiv` at the target. -/
noncomputable def inducedSpechtTranspose (μ : a.Partition) (ν : b.Partition)
    (ξ : (a + b).Partition) :
    IntertwiningMap (spechtModule (R := ℚ) ξ).ρ (inducedSpecht (R := ℚ) μ ν) ≃ₗ[ℚ]
      IntertwiningMap (spechtModule (R := ℚ) ξ.conjugate).ρ
        (inducedSpecht (R := ℚ) μ.conjugate ν.conjugate) :=
  (IntertwiningMap.charTwistLinearEquiv (signLinearCharacter ℚ (Fin (a + b)))).trans
    ((spechtModuleCharTwistSignEquiv ξ).intertwiningMapCongr (inducedSpechtConjugateEquiv μ ν).symm)

/-- `TauCeti.inducedSpechtTranspose` conjugates an intertwining map by the two sign-transpose
equivalences. Not a `simp` lemma: `simp` unfolds the Specht modules in its left-hand side. -/
theorem inducedSpechtTranspose_apply (μ : a.Partition) (ν : b.Partition) (ξ : (a + b).Partition)
    (f : IntertwiningMap (spechtModule (R := ℚ) ξ).ρ (inducedSpecht (R := ℚ) μ ν))
    (v : spechtModule (R := ℚ) ξ.conjugate) :
    inducedSpechtTranspose μ ν ξ f v =
      (inducedSpechtConjugateEquiv μ ν).symm (f ((spechtModuleCharTwistSignEquiv ξ).symm v)) := by
  rw [inducedSpechtTranspose, LinearEquiv.trans_apply, Equiv.intertwiningMapCongr_apply,
    IntertwiningMap.coe_charTwistLinearEquiv]

/-- The inverse of `TauCeti.inducedSpechtTranspose` conjugates back by the two sign-transpose
equivalences. Not a `simp` lemma, for the same reason. -/
theorem inducedSpechtTranspose_symm_apply (μ : a.Partition) (ν : b.Partition)
    (ξ : (a + b).Partition)
    (f : IntertwiningMap (spechtModule (R := ℚ) ξ.conjugate).ρ
      (inducedSpecht (R := ℚ) μ.conjugate ν.conjugate))
    (v : spechtModule (R := ℚ) ξ) :
    (inducedSpechtTranspose μ ν ξ).symm f v =
      inducedSpechtConjugateEquiv μ ν (f (spechtModuleCharTwistSignEquiv ξ v)) := by
  rw [inducedSpechtTranspose, LinearEquiv.symm_trans_apply,
    IntertwiningMap.coe_charTwistLinearEquiv_symm, Equiv.intertwiningMapCongr_symm_apply]
  -- `e.symm.symm` is `e` by definition of `Representation.Equiv.symm`, which has no
  -- `symm_symm` lemma in Mathlib
  rfl

/-- **Transposing all three shapes preserves the induced multiplicity**: the multiplicity of
`S^(ξᵗ)` in `Ind(S^(μᵗ) ⊠ S^(νᵗ))` is that of `S^ξ` in `Ind(S^μ ⊠ S^ν)`. -/
theorem finrank_intertwiningMap_inducedSpecht_conjugate (μ : a.Partition) (ν : b.Partition)
    (ξ : (a + b).Partition) :
    Module.finrank ℚ (IntertwiningMap (spechtModule (R := ℚ) ξ.conjugate).ρ
        (inducedSpecht (R := ℚ) μ.conjugate ν.conjugate)) =
      Module.finrank ℚ (IntertwiningMap (spechtModule (R := ℚ) ξ).ρ
        (inducedSpecht (R := ℚ) μ ν)) :=
  (inducedSpechtTranspose μ ν ξ).finrank_eq.symm

end Transpose

end TauCeti
