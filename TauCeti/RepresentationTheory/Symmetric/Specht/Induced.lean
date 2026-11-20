/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.SumCongr
public import TauCeti.RepresentationTheory.Induction.CharTwist
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Symmetric.Specht.SignTranspose
public import TauCeti.RepresentationTheory.Tensor.External

/-!
# Induced Specht modules and their transpose comparison

For partitions `μ ⊢ a` and `ν ⊢ b`, the representation `inducedSpecht μ ν` of `S_(a+b)` is induced
along the block embedding `Equiv.Perm.finSumPermHom a b : S_a × S_b →* S_(a+b)` from the external
tensor product `S^μ ⊠ S^ν` of `S_a × S_b`. For `ξ ⊢ a + b`, the space of intertwining maps
`S^ξ → inducedSpecht μ ν` over `ℚ` is the multiplicity space `C_(μ,ν)^ξ` of the
Littlewood--Richardson rule. This file proves that, over `ℚ`, transposing all three shapes preserves
it:

`C_(μ,ν)^ξ ≃ C_(μᵗ,νᵗ)^(ξᵗ)`.

The route is the sign twist. Restricted along the block embedding, the sign of `S_(a+b)` is the
product of the signs of the two blocks (`TauCeti.signLinearCharacter_comp_finSumPermHom`), so the
twist of `S^μ ⊠ S^ν` by the restricted sign is `(S^μ ⊗ sgn) ⊠ (S^ν ⊗ sgn) ≅ S^(μᵗ) ⊠ S^(νᵗ)`.
Inducing, and moving the sign out of the induced representation by the projection formula
(`TauCeti.indCharTwistEquiv`, that is `Ind(W ⊗ Res sgn) ≅ Ind(W) ⊗ sgn`), gives
`inducedSpecht μᵗ νᵗ ≅ inducedSpecht μ ν ⊗ sgn` (`TauCeti.inducedSpechtConjugateEquiv`).
Twisting both sides of an intertwining map by the sign does not change it, and `S^ξ ⊗ sgn ≅ S^(ξᵗ)`
(`TauCeti.spechtModuleCharTwistSignEquiv`) identifies the source. Like `S^μ ⊗ sgn ≅ S^(μᵗ)`, these
comparisons are stated over `ℚ`.

Twists are taken with `Representation.charTwist` rather than by tensoring with the line of the
sign: the carrier stays the same, so twisting both sides of an intertwining map literally keeps the
map (`Representation.IntertwiningMap.charTwistLinearEquiv`), with no unitor to cancel.

## Main definitions

* `TauCeti.inducedSpecht`: `Ind_(S_a × S_b)^(S_(a+b)) (S^μ ⊠ S^ν)`.
* `TauCeti.inducedSpechtConjugateEquiv`: `inducedSpecht μᵗ νᵗ ≃ inducedSpecht μ ν ⊗ sgn` over `ℚ`.
* `TauCeti.inducedSpechtTranspose`: **the transpose comparison of the induced multiplicity
  spaces**, `Hom(S^ξ, inducedSpecht μ ν) ≃ Hom(S^(ξᵗ), inducedSpecht μᵗ νᵗ)`.

## Main statements

* `TauCeti.inducedSpechtConjugateEquiv_mk`, `TauCeti.inducedSpechtConjugateEquiv_symm_mk`: the
  sign-transpose equivalence of induced Specht representations on generators.
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
`Equiv.Perm.finSumPermHom a b`. Over `ℚ`, its intertwining maps from `S^ξ`, for `ξ ⊢ a + b`, form
the Littlewood--Richardson multiplicity space of `ξ` in the induction product of `μ` and `ν`. -/
noncomputable abbrev inducedSpecht {R : Type*} [CommRing R] (μ : a.Partition) (ν : b.Partition) :
    Representation R (Equiv.Perm (Fin (a + b)))
      (IndV (Equiv.Perm.finSumPermHom a b)
        (externalTensor (spechtModule (R := R) μ).ρ (spechtModule (R := R) ν).ρ)) :=
  ind (Equiv.Perm.finSumPermHom a b)
    (externalTensor (spechtModule (R := R) μ).ρ (spechtModule (R := R) ν).ρ)

section Transpose

/-- **Transposing both shapes twists the induced Specht representation by the sign**, over `ℚ`:
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
    Representation.Equiv.symm_apply_apply, smul_smul, map_inv, Units.mul_inv, one_smul]

/-- **The transpose comparison of induced multiplicity spaces** over `ℚ`: for `μ ⊢ a`, `ν ⊢ b` and
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

/-- **Transposing all three shapes preserves the induced multiplicity** over `ℚ`: the
multiplicity of `S^(ξᵗ)` in `Ind(S^(μᵗ) ⊠ S^(νᵗ))` is that of `S^ξ` in `Ind(S^μ ⊠ S^ν)`. -/
theorem finrank_intertwiningMap_inducedSpecht_conjugate (μ : a.Partition) (ν : b.Partition)
    (ξ : (a + b).Partition) :
    Module.finrank ℚ (IntertwiningMap (spechtModule (R := ℚ) ξ.conjugate).ρ
        (inducedSpecht (R := ℚ) μ.conjugate ν.conjugate)) =
      Module.finrank ℚ (IntertwiningMap (spechtModule (R := ℚ) ξ).ρ
        (inducedSpecht (R := ℚ) μ ν)) :=
  (inducedSpechtTranspose μ ν ξ).finrank_eq.symm

end Transpose

end TauCeti
