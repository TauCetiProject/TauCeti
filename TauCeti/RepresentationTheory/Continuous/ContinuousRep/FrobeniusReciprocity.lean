/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Induced
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations

/-!
# Frobenius reciprocity for continuous induction

Let `H` be a subgroup of a locally compact group `Γ`, `σ` a jointly continuous representation of
`H` on `U`, and `ρ` one of `Γ` on `M`. This file proves that continuous induction
`TauCeti.ContinuousRep.ind H σ` satisfies both Frobenius reciprocities with restriction
`TauCeti.ContinuousRep.res` along the inclusion `ι : H →ₜ* Γ`.

* **Coinduction form.** `Hom_H(Res M, U) ≃ Hom_Γ(M, Ind U)`, by `f ↦ (m ↦ (x ↦ f (ρ x m)))`,
  with inverse `F ↦ (m ↦ F m 1)`. This holds for every subgroup `H`.
* **Induction form.** For `H` open of finite index, `Hom_Γ(Ind U, M) ≃ Hom_H(U, Res M)`. The
  forward map restricts `F` to the functions `e_u` supported on `H`, `e_u (h) = σ h u`
  (`TauCeti.ContinuousRep.indSingle`); the inverse sends `f` to
  `φ ↦ ∑_{x H ∈ Γ/H} ρ x (f (φ x⁻¹))`, which does not depend on the representatives `x` because
  `f` is `H`-equivariant. The two round trips are the identity `f u = ρ r (f (e_u r⁻¹))` for
  `r ∈ H` and the decomposition `φ = ∑_{x H} x • e_{φ x⁻¹}` of an element of the induced module
  into its pieces on the cosets `H x⁻¹` (`TauCeti.ContinuousRep.finsum_ind_indSingle`).

The names follow Mathlib's `Rep.resCoindHomEquiv` and `Rep.indResHomEquiv`.

## Main definitions

* `TauCeti.ContinuousRep.resIndHomEquiv`: Frobenius reciprocity
  `Hom_H(Res M, U) ≃ Hom_Γ(M, Ind U)`.
* `TauCeti.ContinuousRep.indResHomEquiv`: Frobenius reciprocity
  `Hom_Γ(Ind U, M) ≃ Hom_H(U, Res M)` for `H` open of finite index.
-/

public section

namespace TauCeti

namespace ContinuousRep

variable {Γ A U : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Ring A]
  [TopologicalSpace A] [AddCommGroup U] [Module A U]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul A U] {H : Subgroup Γ}

variable {M : Type*} [AddCommMonoid M] [Module A M] [TopologicalSpace M]

section Coinduction

variable [LocallyCompactSpace Γ] {ρ : ContinuousRep Γ A M} {σ : ContinuousRep H A U}

/-- The morphism `m ↦ (x ↦ f (ρ x m))` from `ρ` to the induced representation attached to a
morphism `f` from the restriction of `ρ` to `σ`: the forward map of `resIndHomEquiv`. -/
private noncomputable def homIndOfHomRes
    (f : Hom (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) σ) : Hom ρ (ind H σ) where
  toFun m := ⟨⟨fun x => f (ρ x m), f.cont.comp (ρ.continuous_orbit m)⟩,
    (mem_indV _).2 fun h x => by simpa using f.isIntertwining h (ρ x m)⟩
  map_add' _ _ := Subtype.ext (ContinuousMap.ext fun _ => by simp)
  map_smul' _ _ := Subtype.ext (ContinuousMap.ext fun _ => by simp)
  isIntertwining' g := LinearMap.ext fun m =>
    Subtype.ext (ContinuousMap.ext fun x => by simp [mul_apply_eq_comp])
  cont := ((ContinuousMap.mk (fun q : M × Γ => f (ρ q.2 q.1))
    (f.cont.comp (ρ.continuous_action.comp continuous_swap))).curry.continuous).subtype_mk _

private theorem homIndOfHomRes_apply_apply
    (f : Hom (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) σ) (m : M) (x : Γ) :
    (homIndOfHomRes f m : C(Γ, U)) x = f (ρ x m) := by
  rw [← Hom.coe_toIntertwiningMap]
  rfl

/-- The morphism `m ↦ F m 1` from the restriction of `ρ` to `σ` attached to a morphism
`F : ρ ⟶ ind H σ`: the inverse map of `resIndHomEquiv`. -/
private noncomputable def homResOfHomInd (F : Hom ρ (ind H σ)) :
    Hom (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) σ where
  toFun m := (F m : C(Γ, U)) 1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  isIntertwining' h := LinearMap.ext fun m => by
    have := (mem_indV _).1 (F m).property h 1
    simp only [mul_one] at this
    simp [F.isIntertwining, ← this]
  cont := ((continuous_eval_const 1).comp continuous_subtypeVal).comp F.cont

private theorem homResOfHomInd_apply (F : Hom ρ (ind H σ)) (m : M) :
    homResOfHomInd F m = (F m : C(Γ, U)) 1 := by
  rw [← Hom.coe_toIntertwiningMap]
  rfl

/-- **Frobenius reciprocity, coinduction form.** Morphisms of continuous representations of `H`
from the restriction of `ρ` to `σ` correspond to morphisms of continuous representations of `Γ`
from `ρ` to the induced representation `ind H σ`: `f` goes to `m ↦ (x ↦ f (ρ x m))`, and `F`
comes from `m ↦ F m 1`. No hypothesis on `H` is needed. -/
noncomputable def resIndHomEquiv :
    Hom (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) σ ≃ Hom ρ (ind H σ) where
  toFun := homIndOfHomRes
  invFun := homResOfHomInd
  left_inv f := Hom.ext fun m => by simp [homResOfHomInd_apply, homIndOfHomRes_apply_apply]
  right_inv F := Hom.ext fun m => Subtype.ext (ContinuousMap.ext fun x => by
    simpa [homResOfHomInd_apply, homIndOfHomRes_apply_apply] using
      congr_arg (fun φ : indV H σ => (φ : C(Γ, U)) 1) (F.isIntertwining x m))

@[simp]
theorem resIndHomEquiv_apply_apply_apply
    (f : Hom (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) σ) (m : M) (x : Γ) :
    (resIndHomEquiv f m : C(Γ, U)) x = f (ρ x m) :=
  homIndOfHomRes_apply_apply f m x

@[simp]
theorem resIndHomEquiv_symm_apply_apply (F : Hom ρ (ind H σ)) (m : M) :
    resIndHomEquiv.symm F m = (F m : C(Γ, U)) 1 :=
  homResOfHomInd_apply F m

end Coinduction

section Induction

variable {ρ : ContinuousRep Γ A M} {σ : ContinuousRep H A U}

/-- The term `ρ x (f (φ x⁻¹))` of the sum defining the inverse map of `indResHomEquiv`. -/
private noncomputable def indHomTerm (f : Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H)))
    (φ : indV H σ) (x : Γ) : M :=
  ρ x (f ((φ : C(Γ, U)) x⁻¹))

omit [IsTopologicalGroup Γ] in
/-- The term `ρ x (f (φ x⁻¹))` depends only on the coset `x H`. -/
private theorem indHomTerm_eq_of_mk_eq
    (f : Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H)))
    (φ : indV H σ) {x y : Γ} (hxy : (x : Γ ⧸ H) = y) :
    indHomTerm f φ x = indHomTerm f φ y := by
  obtain ⟨h, rfl⟩ : ∃ h : H, y = x * h := ⟨⟨_, QuotientGroup.eq.1 hxy⟩, by simp⟩
  have hφ : (φ : C(Γ, U)) (x * h)⁻¹ = σ h⁻¹ ((φ : C(Γ, U)) x⁻¹) := by
    simpa using (mem_indV _).1 φ.property h⁻¹ x⁻¹
  have hf : f (σ h⁻¹ ((φ : C(Γ, U)) x⁻¹)) = ρ (h : Γ)⁻¹ (f ((φ : C(Γ, U)) x⁻¹)) := by
    simpa using f.isIntertwining h⁻¹ ((φ : C(Γ, U)) x⁻¹)
  rw [indHomTerm, indHomTerm, hφ, hf, map_mul, mul_apply_eq_comp]
  simpa using congr_arg (ρ x) (ρ.toRepresentation.self_inv_apply (h : Γ) _).symm

variable [LocallyCompactSpace Γ] (hH : IsOpen (H : Set Γ))

/-- The morphism `u ↦ F e_u` from `σ` to the restriction of `ρ` attached to a morphism
`F : ind H σ ⟶ ρ`, where `e_u` is the element of the induced module supported on `H`
(`TauCeti.ContinuousRep.indSingle`): the forward map of `indResHomEquiv`. -/
private noncomputable def homResOfIndHom (F : Hom (ind H σ) ρ) :
    Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) where
  toFun u := F (indSingle σ hH u)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  isIntertwining' h := LinearMap.ext fun u => by
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, coe_toRepresentation,
      res_apply, ContinuousMonoidHom.subgroupSubtype_apply]
    rw [← ind_apply_indSingle, F.isIntertwining]
  cont := (map_continuous F).comp (indSingle σ hH).continuous

private theorem homResOfIndHom_apply (F : Hom (ind H σ) ρ) (u : U) :
    homResOfIndHom hH F u = F (indSingle σ hH u) := by
  rw [← Hom.coe_toIntertwiningMap]
  rfl

variable [ContinuousAdd M] [H.FiniteIndex]

/-- The morphism `φ ↦ ∑_{x H ∈ Γ / H} ρ x (f (φ x⁻¹))` from the induced representation to `ρ`
attached to a morphism `f` from `σ` to the restriction of `ρ`, for `H` of finite index: the
inverse map of `indResHomEquiv`. The terms do not depend on the representatives `x`
(`indHomTerm_eq_of_mk_eq`). -/
private noncomputable def indHomOfHomRes
    (f : Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H))) : Hom (ind H σ) ρ where
  toFun φ := ∑ᶠ q : Γ ⧸ H, indHomTerm f φ q.out
  map_add' φ ψ := by
    have := Fintype.ofFinite (Γ ⧸ H)
    simp only [finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by simp [indHomTerm]
  map_smul' a φ := by
    have := Fintype.ofFinite (Γ ⧸ H)
    simp only [finsum_eq_sum_of_fintype, Finset.smul_sum]
    exact Finset.sum_congr rfl fun q _ => by simp [indHomTerm]
  isIntertwining' g := LinearMap.ext fun φ => by
    have := Fintype.ofFinite (Γ ⧸ H)
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, finsum_eq_sum_of_fintype,
      map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g⁻¹ : Equiv.Perm (Γ ⧸ H)) _ _ fun q => ?_
    have hq : (((g⁻¹ • q).out : Γ) : Γ ⧸ H) = ((g⁻¹ * q.out : Γ) : Γ ⧸ H) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk,
        QuotientGroup.out_eq']
    rw [MulAction.toPerm_apply, indHomTerm_eq_of_mk_eq f φ hq, indHomTerm, indHomTerm]
    simp only [coe_toRepresentation, ind_apply_apply, mul_inv_rev, inv_inv]
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]
  cont := by
    have := Fintype.ofFinite (Γ ⧸ H)
    simp only [finsum_eq_sum_of_fintype, indHomTerm]
    exact continuous_finsetSum _ fun q _ => (ρ.continuous_apply _).comp ((map_continuous f).comp
      ((continuous_eval_const _).comp continuous_subtypeVal))

private theorem indHomOfHomRes_apply
    (f : Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H))) (φ : indV H σ) :
    indHomOfHomRes f φ = ∑ᶠ q : Γ ⧸ H, ρ q.out (f ((φ : C(Γ, U)) q.out⁻¹)) := by
  rw [← Hom.coe_toIntertwiningMap]
  rfl

/-- **Frobenius reciprocity, induction form.** For an open subgroup `H` of finite index,
morphisms of continuous representations of `Γ` from the induced representation `ind H σ` to `ρ`
correspond to morphisms of continuous representations of `H` from `σ` to the restriction of
`ρ`: `F` goes to `u ↦ F e_u`, and `f` comes from `φ ↦ ∑_{x H ∈ Γ / H} ρ x (f (φ x⁻¹))`. -/
noncomputable def indResHomEquiv :
    Hom (ind H σ) ρ ≃ Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) where
  toFun := homResOfIndHom hH
  invFun := indHomOfHomRes
  left_inv F := Hom.ext fun φ => by
    have := Fintype.ofFinite (Γ ⧸ H)
    rw [indHomOfHomRes_apply]
    conv_rhs => rw [← finsum_ind_indSingle σ hH φ]
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [homResOfIndHom_apply, F.isIntertwining]
  right_inv f := Hom.ext fun u => by
    have := Fintype.ofFinite (Γ ⧸ H)
    rw [homResOfIndHom_apply, indHomOfHomRes_apply, finsum_eq_sum_of_fintype,
      Finset.sum_eq_single_of_mem ((1 : Γ) : Γ ⧸ H) (Finset.mem_univ _)]
    · have hr : Quotient.out ((1 : Γ) : Γ ⧸ H) ∈ H := by
        simp
      have hf := f.isIntertwining ⟨_, H.inv_mem hr⟩ u
      rw [res_apply, ContinuousMonoidHom.subgroupSubtype_apply] at hf
      rw [indSingle_apply_of_mem σ hH u (H.inv_mem hr), hf]
      exact ρ.toRepresentation.self_inv_apply _ _
    · intro q _ hq
      -- the term vanishes unless `q.out⁻¹ ∈ H`, that is unless `q` is the trivial coset
      rw [indSingle_apply_of_notMem σ hH _ fun hm => hq (QuotientGroup.out_mem_iff.1
        (inv_mem_iff.1 hm)), map_zero, map_zero]

@[simp]
theorem indResHomEquiv_apply_apply (F : Hom (ind H σ) ρ) (u : U) :
    indResHomEquiv hH F u = F (indSingle σ hH u) :=
  homResOfIndHom_apply hH F u

@[simp]
theorem indResHomEquiv_symm_apply_apply
    (f : Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H))) (φ : indV H σ) :
    (indResHomEquiv hH).symm f φ = ∑ᶠ q : Γ ⧸ H, ρ q.out (f ((φ : C(Γ, U)) q.out⁻¹)) :=
  indHomOfHomRes_apply f φ

end Induction

end ContinuousRep

end TauCeti
