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
`TauCeti.ContinuousRep.ind H σ` is functorial in `σ` and satisfies both Frobenius reciprocities
with restriction `TauCeti.ContinuousRep.res` along the inclusion `ι : H →ₜ* Γ`.

* **Coinduction form.** `Hom_Γ(M, Ind U) ≃ Hom_H(Res M, U)`, by `F ↦ (m ↦ F m 1)`, with inverse
  `f ↦ (m ↦ (x ↦ f (ρ x m)))`. This holds for every subgroup `H`.
* **Induction form.** For `H` open of finite index, `Hom_Γ(Ind U, M) ≃ Hom_H(U, Res M)`. The
  forward map restricts `F` to the functions `e_u` supported on `H`, `e_u (h) = σ h u`; the
  inverse sends `f` to `φ ↦ ∑_{x H ∈ Γ/H} ρ x (f (φ x⁻¹))`, which does not depend on the
  representatives `x` because `f` is `H`-equivariant. The two round trips are the identity
  `f u = ρ r (f (e_u r⁻¹))` for `r ∈ H` and the decomposition `φ = ∑_{x H} x • e_{φ x⁻¹}` of an
  element of the induced module into its pieces on the cosets `H x⁻¹`.

## Main definitions

* `TauCeti.ContinuousRep.Hom.ind`, `TauCeti.ContinuousRep.Iso.ind`: functoriality of induction.
* `TauCeti.ContinuousRep.indSingle`: the element `e_u` of the induced module supported on `H`.
* `TauCeti.ContinuousRep.homIndEquiv`: Frobenius reciprocity `Hom_Γ(M, Ind U) ≃ Hom_H(Res M, U)`.
* `TauCeti.ContinuousRep.indHomEquiv`: Frobenius reciprocity `Hom_Γ(Ind U, M) ≃ Hom_H(U, Res M)`
  for `H` open of finite index.

## Main results

* `TauCeti.ContinuousRep.ind_apply_indSingle`: `h • e_u = e_{σ h u}` for `h ∈ H`.
* `TauCeti.ContinuousRep.finsum_ind_indSingle`: every element of the induced module is the sum of
  its pieces on the cosets of `H`.
-/

public section

namespace TauCeti

namespace ContinuousRep

variable {Γ A U : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Ring A]
  [TopologicalSpace A] [AddCommGroup U] [Module A U]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul A U] {H : Subgroup Γ}

section Functoriality

variable [LocallyCompactSpace Γ]

variable {V W : Type*} [AddCommGroup V] [Module A V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul A V] [AddCommGroup W] [Module A W]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul A W]
  {σ : ContinuousRep H A U} {τ : ContinuousRep H A V} {υ : ContinuousRep H A W}

/-- **Functoriality of induction.** A morphism `f : σ ⟶ τ` of continuous representations of `H`
induces the morphism `φ ↦ f ∘ φ` of induced representations. -/
noncomputable def Hom.ind (f : Hom σ τ) :
    Hom (ContinuousRep.ind H σ) (ContinuousRep.ind H τ) where
  toFun φ := ⟨(⟨f, f.cont⟩ : C(U, V)).comp φ, (mem_indV _).2 fun h x => by
    simp [(mem_indV _).1 φ.property h x, f.isIntertwining]⟩
  map_add' _ _ := Subtype.ext (ContinuousMap.ext fun _ => map_add f _ _)
  map_smul' _ _ := Subtype.ext (ContinuousMap.ext fun _ => map_smul f _ _)
  isIntertwining' g := LinearMap.ext fun φ => Subtype.ext (ContinuousMap.ext fun x => by
    simp only [LinearMap.comp_apply, coe_toRepresentation, ind_apply_apply]
    change f ((ContinuousRep.ind H σ g φ : C(Γ, U)) x) = f ((φ : C(Γ, U)) (x * g))
    rw [ind_apply_apply])
  cont := ((ContinuousMap.continuous_postcomp _).comp continuous_subtypeVal).subtype_mk _

@[simp]
theorem Hom.ind_apply_apply (f : Hom σ τ) (φ : indV H σ) (x : Γ) :
    (f.ind φ : C(Γ, V)) x = f ((φ : C(Γ, U)) x) := by
  rw [← Hom.coe_toIntertwiningMap]
  rfl

@[simp]
theorem Hom.ind_id : (Hom.id σ).ind = Hom.id (ContinuousRep.ind H σ) :=
  Hom.ext fun _ => Subtype.ext (ContinuousMap.ext fun _ => by simp)

theorem Hom.ind_comp (f : Hom τ υ) (f' : Hom σ τ) : (f.comp f').ind = f.ind.comp f'.ind :=
  Hom.ext fun _ => Subtype.ext (ContinuousMap.ext fun _ => by simp)

/-- **Functoriality of induction** for isomorphisms: an isomorphism `σ ≅ τ` induces an
isomorphism of induced representations. -/
noncomputable def Iso.ind (e : Iso σ τ) :
    Iso (ContinuousRep.ind H σ) (ContinuousRep.ind H τ) where
  toRepresentationEquiv :=
    { e.toHom.ind.toIntertwiningMap with
      invFun := e.symm.toHom.ind
      left_inv φ := Subtype.ext (ContinuousMap.ext fun x => by
        change (e.symm.toHom.ind (e.toHom.ind φ) : C(Γ, U)) x = _
        simp)
      right_inv φ := Subtype.ext (ContinuousMap.ext fun x => by
        change (e.toHom.ind (e.symm.toHom.ind φ) : C(Γ, V)) x = _
        simp) }
  continuous_toFun := e.toHom.ind.cont
  continuous_invFun := e.symm.toHom.ind.cont

@[simp]
theorem Iso.ind_apply_apply (e : Iso σ τ) (φ : indV H σ) (x : Γ) :
    (e.ind φ : C(Γ, V)) x = e ((φ : C(Γ, U)) x) := by
  rw [← Iso.coe_toRepresentationEquiv, ← e.coe_toHom]
  rfl

end Functoriality

section Coinduction

variable [LocallyCompactSpace Γ]

variable {M : Type*} [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  {ρ : ContinuousRep Γ A M} {σ : ContinuousRep H A U}

/-- The morphism `m ↦ F m 1` from the restriction of `ρ` to `σ` attached to a morphism
`F : ρ ⟶ ind H σ`. -/
noncomputable def homResOfHomInd (F : Hom ρ (ind H σ)) :
    Hom (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) σ where
  toFun m := (F m : C(Γ, U)) 1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  isIntertwining' h := LinearMap.ext fun m => by
    have := (mem_indV _).1 (F m).property h 1
    simp only [mul_one] at this
    simp [F.isIntertwining, ← this]
  cont := ((continuous_eval_const 1).comp continuous_subtypeVal).comp F.cont

@[simp]
theorem homResOfHomInd_apply (F : Hom ρ (ind H σ)) (m : M) :
    homResOfHomInd F m = (F m : C(Γ, U)) 1 := by
  rw [← Hom.coe_toIntertwiningMap]
  rfl

/-- The morphism `m ↦ (x ↦ f (ρ x m))` from `ρ` to the induced representation attached to a
morphism `f` from the restriction of `ρ` to `σ`. -/
noncomputable def homIndOfHomRes (f : Hom (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) σ) :
    Hom ρ (ind H σ) where
  toFun m := ⟨⟨fun x => f (ρ x m), f.cont.comp (ρ.continuous_orbit m)⟩,
    (mem_indV _).2 fun h x => by simpa using f.isIntertwining h (ρ x m)⟩
  map_add' _ _ := Subtype.ext (ContinuousMap.ext fun _ => by simp)
  map_smul' _ _ := Subtype.ext (ContinuousMap.ext fun _ => by simp)
  isIntertwining' g := LinearMap.ext fun m =>
    Subtype.ext (ContinuousMap.ext fun x => by
      simp only [LinearMap.comp_apply, coe_toRepresentation, ind_apply_apply]
      change _ = f (ρ (x * g) m)
      rw [map_mul, mul_apply_eq_comp]
      rfl)
  cont := ((ContinuousMap.mk (fun q : M × Γ => f (ρ q.2 q.1))
    (f.cont.comp (ρ.continuous_action.comp continuous_swap))).curry.continuous).subtype_mk _

@[simp]
theorem homIndOfHomRes_apply_apply
    (f : Hom (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) σ) (m : M) (x : Γ) :
    (homIndOfHomRes f m : C(Γ, U)) x = f (ρ x m) := by
  rw [← Hom.coe_toIntertwiningMap]
  rfl

/-- **Frobenius reciprocity, coinduction form.** Morphisms of continuous representations of `Γ`
from `ρ` to the induced representation `ind H σ` correspond to morphisms of continuous
representations of `H` from the restriction of `ρ` to `σ`: `F` goes to `m ↦ F m 1`, and `f` comes
from `m ↦ (x ↦ f (ρ x m))`. No hypothesis on `H` is needed. -/
noncomputable def homIndEquiv :
    Hom ρ (ind H σ) ≃ Hom (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) σ where
  toFun := homResOfHomInd
  invFun := homIndOfHomRes
  left_inv F := Hom.ext fun m => Subtype.ext (ContinuousMap.ext fun x => by
    simpa using congr_arg (fun φ : indV H σ => (φ : C(Γ, U)) 1) (F.isIntertwining x m))
  right_inv f := Hom.ext fun m => by simp

@[simp]
theorem homIndEquiv_apply (F : Hom ρ (ind H σ)) : homIndEquiv F = homResOfHomInd F :=
  (rfl)

@[simp]
theorem homIndEquiv_symm_apply (f : Hom (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) σ) :
    homIndEquiv.symm f = homIndOfHomRes f :=
  (rfl)

end Coinduction

section Single

variable (σ : ContinuousRep H A U) (hH : IsOpen (H : Set Γ))

/-- The equivariant function supported on `H` with value `σ h u` at `h ∈ H`. -/
noncomputable def indSingleFun (u : U) (x : Γ) : U :=
  open Classical in if hx : x ∈ H then σ ⟨x, hx⟩ u else 0

omit [IsTopologicalGroup Γ] [TopologicalSpace A]
  [IsTopologicalAddGroup U] [ContinuousSMul A U] in
theorem indSingleFun_of_mem (u : U) {x : Γ} (hx : x ∈ H) :
    indSingleFun σ u x = σ ⟨x, hx⟩ u := by
  simp [indSingleFun, hx]

omit [IsTopologicalGroup Γ] [TopologicalSpace A]
  [IsTopologicalAddGroup U] [ContinuousSMul A U] in
theorem indSingleFun_of_notMem (u : U) {x : Γ} (hx : x ∉ H) : indSingleFun σ u x = 0 := by
  simp [indSingleFun, hx]

omit [IsTopologicalGroup Γ] [TopologicalSpace A]
  [IsTopologicalAddGroup U] [ContinuousSMul A U] in
theorem indSingleFun_mul (u : U) (h : H) (x : Γ) :
    indSingleFun σ u (h * x) = σ h (indSingleFun σ u x) := by
  by_cases hx : x ∈ H
  · rw [indSingleFun_of_mem σ u (H.mul_mem h.property hx), indSingleFun_of_mem σ u hx,
      ← mul_apply_eq_comp, ← map_mul]
    rfl
  · rw [indSingleFun_of_notMem σ u hx, map_zero,
      indSingleFun_of_notMem σ u fun hm => hx (by simpa using H.mul_mem (inv_mem h.property) hm)]

/-- The element `e_u` of the induced module supported on the open subgroup `H`, with value `σ h u`
at `h ∈ H`. -/
noncomputable def indSingle : U →L[A] indV H σ where
  toFun u := indVMk σ hH (indSingleFun σ u) (indSingleFun_mul σ u)
  map_add' u v := Subtype.ext (ContinuousMap.ext fun x => by
    by_cases hx : x ∈ H <;> simp [indSingleFun, hx])
  map_smul' a u := Subtype.ext (ContinuousMap.ext fun x => by
    by_cases hx : x ∈ H <;> simp [indSingleFun, hx])
  cont := by
    refine Continuous.subtype_mk ?_ _
    refine ((ContinuousMap.mk _ (continuous_uncurry_of_apply_mul σ hH
      (F := fun u => indSingleFun σ u) (fun u => indSingleFun_mul σ u) fun x => ?_)).curry
      |>.continuous).congr fun u => ContinuousMap.ext fun x => (indVMk_apply ..).symm
    by_cases hx : x ∈ H
    · simpa [indSingleFun, hx] using σ.continuous_apply ⟨x, hx⟩
    · simpa [indSingleFun, hx] using continuous_const

theorem indSingle_apply (u : U) (x : Γ) :
    (indSingle σ hH u : C(Γ, U)) x = indSingleFun σ u x :=
  indVMk_apply ..

@[simp]
theorem indSingle_apply_of_mem (u : U) {x : Γ} (hx : x ∈ H) :
    (indSingle σ hH u : C(Γ, U)) x = σ ⟨x, hx⟩ u := by
  rw [indSingle_apply, indSingleFun_of_mem]

@[simp]
theorem indSingle_apply_of_notMem (u : U) {x : Γ} (hx : x ∉ H) :
    (indSingle σ hH u : C(Γ, U)) x = 0 := by
  rw [indSingle_apply, indSingleFun_of_notMem σ u hx]

variable [LocallyCompactSpace Γ]

/-- An element `h ∈ H` acts on `e_u` by acting on `u`: `h • e_u = e_{σ h u}`. -/
theorem ind_apply_indSingle (h : H) (u : U) :
    ind H σ h (indSingle σ hH u) = indSingle σ hH (σ h u) := by
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  rw [ind_apply_apply]
  by_cases hx : x ∈ H
  · rw [indSingle_apply_of_mem σ hH u (H.mul_mem hx h.property), indSingle_apply_of_mem σ hH _ hx,
      ← mul_apply_eq_comp, ← map_mul]
    rfl
  · rw [indSingle_apply_of_notMem σ hH _ hx, indSingle_apply_of_notMem σ hH u fun hm =>
      hx (by simpa using H.mul_mem hm (inv_mem h.property))]

/-- **Decomposition along the cosets.** For `H` open of finite index, every element `φ` of the
induced module is the sum over `x H ∈ Γ / H` of the translates `x • e_{φ x⁻¹}`, the piece of `φ`
supported on the coset `H x⁻¹`. -/
theorem finsum_ind_indSingle [H.FiniteIndex] (φ : indV H σ) :
    ∑ᶠ q : Γ ⧸ H, ind H σ q.out (indSingle σ hH ((φ : C(Γ, U)) q.out⁻¹)) = φ := by
  have := Fintype.ofFinite (Γ ⧸ H)
  rw [finsum_eq_sum_of_fintype]
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  rw [Submodule.coe_sum, ContinuousMap.sum_apply,
    Finset.sum_eq_single_of_mem ((x⁻¹ : Γ) : Γ ⧸ H) (Finset.mem_univ _)]
  · have hmem : x * Quotient.out ((x⁻¹ : Γ) : Γ ⧸ H) ∈ H := by
      simpa using QuotientGroup.eq.1 (QuotientGroup.out_eq' ((x⁻¹ : Γ) : Γ ⧸ H)).symm
    rw [ind_apply_apply, indSingle_apply_of_mem σ hH _ hmem, ← (mem_indV _).1 φ.property]
    simp
  · intro q _ hq
    rw [ind_apply_apply, indSingle_apply_of_notMem σ hH]
    intro hm
    exact hq ((QuotientGroup.out_eq' q).symm.trans
      (QuotientGroup.eq.2 (by simpa using H.inv_mem hm)))

end Single

section Induction

variable {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M]
  {ρ : ContinuousRep Γ A M} {σ : ContinuousRep H A U}

/-- The term `ρ x (f (φ x⁻¹))` of the sum defining `TauCeti.ContinuousRep.indHomOfHomRes`. -/
noncomputable def indHomTerm (f : Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H)))
    (φ : indV H σ) (x : Γ) : M :=
  ρ x (f ((φ : C(Γ, U)) x⁻¹))

omit [IsTopologicalGroup Γ] in
/-- The term `ρ x (f (φ x⁻¹))` depends only on the coset `x H`. -/
theorem indHomTerm_eq_of_mk_eq (f : Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H)))
    (φ : indV H σ) {x y : Γ} (hxy : (x : Γ ⧸ H) = y) :
    indHomTerm f φ x = indHomTerm f φ y := by
  obtain ⟨h, rfl⟩ : ∃ h : H, y = x * h := ⟨⟨_, QuotientGroup.eq.1 hxy⟩, by simp⟩
  have hφ : (φ : C(Γ, U)) (x * h)⁻¹ = σ h⁻¹ ((φ : C(Γ, U)) x⁻¹) := by
    simpa using (mem_indV _).1 φ.property h⁻¹ x⁻¹
  have hf : f (σ h⁻¹ ((φ : C(Γ, U)) x⁻¹)) = ρ (h : Γ)⁻¹ (f ((φ : C(Γ, U)) x⁻¹)) := by
    simpa using f.isIntertwining h⁻¹ ((φ : C(Γ, U)) x⁻¹)
  rw [indHomTerm, indHomTerm, hφ, hf, map_mul, mul_apply_eq_comp,
    ← mul_apply_eq_comp (ρ (h : Γ)), ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]

variable [LocallyCompactSpace Γ] (hH : IsOpen (H : Set Γ))

/-- The morphism `u ↦ F e_u` from `σ` to the restriction of `ρ` attached to a morphism
`F : ind H σ ⟶ ρ`, where `e_u` is the element of the induced module supported on `H`
(`TauCeti.ContinuousRep.indSingle`). -/
noncomputable def homResOfIndHom (F : Hom (ind H σ) ρ) :
    Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H)) where
  toFun u := F (indSingle σ hH u)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  isIntertwining' h := LinearMap.ext fun u => by
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, coe_toRepresentation,
      res_apply, ContinuousMonoidHom.subgroupSubtype_apply]
    rw [← ind_apply_indSingle, F.isIntertwining]
  cont := (map_continuous F).comp (indSingle σ hH).continuous

@[simp]
theorem homResOfIndHom_apply (F : Hom (ind H σ) ρ) (u : U) :
    homResOfIndHom hH F u = F (indSingle σ hH u) := by
  rw [← Hom.coe_toIntertwiningMap]
  rfl

variable [ContinuousAdd M] [H.FiniteIndex]

/-- The morphism `φ ↦ ∑_{x H ∈ Γ / H} ρ x (f (φ x⁻¹))` from the induced representation to `ρ`
attached to a morphism `f` from `σ` to the restriction of `ρ`, for `H` of finite index. The
terms do not depend on the representatives `x` (`indHomTerm_eq_of_mk_eq`). -/
noncomputable def indHomOfHomRes (f : Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H))) :
    Hom (ind H σ) ρ where
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

theorem indHomOfHomRes_apply (f : Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H)))
    (φ : indV H σ) :
    indHomOfHomRes f φ = ∑ᶠ q : Γ ⧸ H, ρ q.out (f ((φ : C(Γ, U)) q.out⁻¹)) := by
  rw [← Hom.coe_toIntertwiningMap]
  rfl

/-- **Frobenius reciprocity, induction form.** For an open subgroup `H` of finite index,
morphisms of continuous representations of `Γ` from the induced representation `ind H σ` to `ρ`
correspond to morphisms of continuous representations of `H` from `σ` to the restriction of
`ρ`: `F` goes to `u ↦ F e_u`, and `f` comes from `φ ↦ ∑_{x H ∈ Γ / H} ρ x (f (φ x⁻¹))`. -/
noncomputable def indHomEquiv :
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
      rw [indSingle_apply_of_mem σ hH u (H.inv_mem hr), hf,
        ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
    · intro q _ hq
      rw [indSingle_apply_of_notMem σ hH, map_zero, map_zero]
      intro hm
      exact hq ((QuotientGroup.out_eq' q).symm.trans
        (QuotientGroup.eq.2 (by simpa using hm)))

@[simp]
theorem indHomEquiv_apply (F : Hom (ind H σ) ρ) : indHomEquiv hH F = homResOfIndHom hH F :=
  (rfl)

@[simp]
theorem indHomEquiv_symm_apply (f : Hom σ (ρ.res (ContinuousMonoidHom.subgroupSubtype H))) :
    (indHomEquiv hH).symm f = indHomOfHomRes f :=
  (rfl)

end Induction

end ContinuousRep

end TauCeti
