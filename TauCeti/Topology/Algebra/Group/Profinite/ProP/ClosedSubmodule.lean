/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Module
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# Closed subgroups and quotient modules of abelian pro-p groups

The canonical `ℤ_[p]`-module on an abelian pro-`p` group identifies its closed subgroups with
closed submodules. The module quotient by the corresponding submodule is continuously linearly
isomorphic to the canonical module on the group quotient. Thus constructions with closed
subgroups can be performed in the module category without changing either the underlying
quotient group or its topology.

The general scalar-stability result and the automatic linearity of continuous additive maps
come from `TauCeti.NumberTheory.Padics.Module`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 4.3.
-/

public section

namespace TauCeti.IsProP

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommGroup A] [TopologicalSpace A]
  [IsTopologicalGroup A] [CompactSpace A] [TotallyDisconnectedSpace A]

/-- Closed subgroups of an abelian pro-`p` group are precisely the closed submodules of its
canonical `ℤ_[p]`-module. -/
noncomputable def closedSubgroupEquivSubmodule (hA : IsProP p A) :
    letI := hA.module
    ClosedSubgroup A ≃o ClosedSubmodule ℤ_[p] (Additive A) := by
  letI := hA.module
  letI := hA.continuousSMul_module
  let e : ClosedSubgroup A ≃o ClosedAddSubgroup (Additive A) :=
    { toFun := fun H ↦
        { toAddSubgroup := H.toSubgroup.toAddSubgroup
          isClosed' := H.isClosed'.preimage continuous_toMul }
      invFun := fun S ↦
        { carrier := {x | Additive.ofMul x ∈ S}
          one_mem' := S.zero_mem
          mul_mem' := fun hx hy ↦ S.add_mem hx hy
          inv_mem' := fun hx ↦ S.toAddSubgroup.neg_mem hx
          isClosed' := S.isClosed'.preimage continuous_ofMul }
      left_inv := fun H ↦ by ext; rfl
      right_inv := fun S ↦ by ext; rfl
      map_rel_iff' := Iff.rfl }
  exact e.trans (closedAddSubgroupEquivPadicIntSubmodule p)

@[simp]
theorem mem_closedSubgroupEquivSubmodule (hA : IsProP p A) (H : ClosedSubgroup A)
    (x : Additive A) :
    letI := hA.module
    x ∈ hA.closedSubgroupEquivSubmodule H ↔ x.toMul ∈ H := by
  simp [closedSubgroupEquivSubmodule]
  rfl

@[simp]
theorem closedSubgroupEquivSubmodule_toAddSubgroup (hA : IsProP p A)
    (H : ClosedSubgroup A) :
    letI := hA.module
    (hA.closedSubgroupEquivSubmodule H).toSubmodule.toAddSubgroup =
      H.toSubgroup.toAddSubgroup := by
  simp [closedSubgroupEquivSubmodule]
  rfl

@[simp]
theorem mem_closedSubgroupEquivSubmodule_symm (hA : IsProP p A)
    (S : letI := hA.module; ClosedSubmodule ℤ_[p] (Additive A)) (x : A) :
    letI := hA.module
    x ∈ hA.closedSubgroupEquivSubmodule.symm S ↔ Additive.ofMul x ∈ S := by
  let _ := hA.module
  let _ := hA.continuousSMul_module
  exact mem_closedAddSubgroupEquivPadicIntSubmodule_symm p S

/-- The canonical module on a closed subgroup is the corresponding submodule of the
canonical module on the ambient group. -/
noncomputable def subgroupEquivModule (hA : IsProP p A) (H : ClosedSubgroup A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.subgroup H.toSubgroup).module
    Additive H.toSubgroup ≃L[ℤ_[p]] (hA.closedSubgroupEquivSubmodule H).toSubmodule := by
  letI := hA.module
  letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  letI := (hA.subgroup H.toSubgroup).module
  letI := hA.continuousSMul_module
  letI := (hA.subgroup H.toSubgroup).continuousSMul_module
  let e : Additive H.toSubgroup ≃+ (hA.closedSubgroupEquivSubmodule H).toSubmodule :=
    { toFun := fun x ↦ ⟨Additive.ofMul x.toMul.val,
        (hA.mem_closedSubgroupEquivSubmodule H _).mpr x.toMul.property⟩
      invFun := fun y ↦ Additive.ofMul ⟨y.val.toMul,
        (hA.mem_closedSubgroupEquivSubmodule H _).mp y.property⟩
      left_inv := fun x ↦ by rfl
      right_inv := fun y ↦ by rfl
      map_add' := fun x y ↦ by rfl }
  exact e.toPadicIntLinearEquiv p
    ((continuous_ofMul.comp (continuous_subtype_val.comp continuous_toMul)).subtype_mk _)
    (continuous_ofMul.comp ((continuous_toMul.comp continuous_subtype_val).subtype_mk _))

@[simp]
theorem subgroupEquivModule_apply (hA : IsProP p A) (H : ClosedSubgroup A)
    (x : Additive H.toSubgroup) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.subgroup H.toSubgroup).module
    (hA.subgroupEquivModule H x : Additive A) = Additive.ofMul x.toMul.val := by
  let _ := hA.module
  let _ : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  let _ := (hA.subgroup H.toSubgroup).module
  let _ := hA.continuousSMul_module
  let _ := (hA.subgroup H.toSubgroup).continuousSMul_module
  dsimp only [subgroupEquivModule]
  exact congrArg
    (fun y : (hA.closedSubgroupEquivSubmodule H).toSubmodule ↦ (y : Additive A))
    (congrFun (AddEquiv.coe_toPadicIntLinearEquiv p _ _ _) x)

/-- The group quotient projection, written additively, is a continuous `ℤ_[p]`-linear map
for the canonical modules on the source and quotient. -/
noncomputable def quotientMkLinear (hA : IsProP p A) (H : ClosedSubgroup A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.quotient H.toSubgroup).module
    Additive A →L[ℤ_[p]] Additive (A ⧸ H.toSubgroup) := by
  letI := hA.module
  letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  letI := (hA.quotient H.toSubgroup).module
  exact
    { toFun := fun x ↦ Additive.ofMul (x.toMul : A ⧸ H.toSubgroup)
      map_add' := fun x y ↦ congrArg Additive.ofMul ((QuotientGroup.mk' H.toSubgroup).map_mul _ _)
      map_smul' := fun c x ↦ by
        simp only [module_smul, toMul_ofMul, mk_padicPow_quotient, RingHom.id_apply]
      cont := continuous_ofMul.comp (QuotientGroup.continuous_mk.comp continuous_toMul) }

@[simp]
theorem quotientMkLinear_apply (hA : IsProP p A) (H : ClosedSubgroup A) (x : Additive A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.quotient H.toSubgroup).module
    hA.quotientMkLinear H x = Additive.ofMul (x.toMul : A ⧸ H.toSubgroup) :=
  (rfl)

/-- The kernel of the linear quotient projection is the submodule corresponding to the
closed subgroup. -/
@[simp]
theorem ker_quotientMkLinear (hA : IsProP p A) (H : ClosedSubgroup A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.quotient H.toSubgroup).module
    (hA.quotientMkLinear H).ker = (hA.closedSubgroupEquivSubmodule H).toSubmodule := by
  let _ := hA.module
  let _ : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  let _ := (hA.quotient H.toSubgroup).module
  ext x
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, quotientMkLinear_apply,
    ofMul_eq_zero, QuotientGroup.eq_one_iff,
    ClosedSubmodule.mem_toSubmodule_iff, mem_closedSubgroupEquivSubmodule]
  rfl

/-- The linear quotient projection is surjective. -/
theorem quotientMkLinear_surjective (hA : IsProP p A) (H : ClosedSubgroup A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.quotient H.toSubgroup).module
    Function.Surjective (hA.quotientMkLinear H) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective y.toMul
  refine ⟨Additive.ofMul x, ?_⟩
  rw [quotientMkLinear_apply]
  exact congrArg Additive.ofMul hx

/-- The module quotient by a closed subgroup agrees, as a topological `ℤ_[p]`-module, with
the canonical module on the group quotient. -/
noncomputable def quotientEquivModule (hA : IsProP p A) (H : ClosedSubgroup A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.quotient H.toSubgroup).module
    (Additive A ⧸ (hA.closedSubgroupEquivSubmodule H).toSubmodule) ≃L[ℤ_[p]]
      Additive (A ⧸ H.toSubgroup) := by
  letI := hA.module
  letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  letI := (hA.quotient H.toSubgroup).module
  let S := (hA.closedSubgroupEquivSubmodule H).toSubmodule
  let f := hA.quotientMkLinear H
  have hf := hA.quotientMkLinear_surjective H
  let e := (Submodule.quotEquivOfEq S f.ker (hA.ker_quotientMkLinear H).symm).trans
    (f.toLinearMap.quotKerEquivOfSurjective hf)
  letI : CompactSpace (Additive A ⧸ S) := Quotient.compactSpace
  have he : Continuous e := by
    apply S.isQuotientMap_mkQ.continuous_iff.mpr
    exact f.continuous
  exact { e with
    continuous_toFun := he
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := e.toEquiv) he }

@[simp]
theorem quotientEquivModule_mk (hA : IsProP p A) (H : ClosedSubgroup A) (x : Additive A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.quotient H.toSubgroup).module
    hA.quotientEquivModule H (Submodule.Quotient.mk x) =
      Additive.ofMul (x.toMul : A ⧸ H.toSubgroup) := by
  simp only [quotientEquivModule]
  exact quotientMkLinear_apply hA H x

end TauCeti.IsProP
