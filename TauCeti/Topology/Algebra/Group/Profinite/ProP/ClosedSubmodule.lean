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
noncomputable def closedSubgroupSubmoduleOrderIso (hA : IsProP p A) :
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
  exact e.trans (closedAddSubgroupPadicIntSubmoduleOrderIso p)

@[simp]
theorem mem_closedSubgroupSubmoduleOrderIso (hA : IsProP p A) (H : ClosedSubgroup A)
    (x : Additive A) :
    letI := hA.module
    x ∈ hA.closedSubgroupSubmoduleOrderIso H ↔ x.toMul ∈ H := by
  simp [closedSubgroupSubmoduleOrderIso]
  rfl

@[simp]
theorem closedSubgroupSubmoduleOrderIso_toAddSubgroup (hA : IsProP p A)
    (H : ClosedSubgroup A) :
    letI := hA.module
    (hA.closedSubgroupSubmoduleOrderIso H).toSubmodule.toAddSubgroup =
      H.toSubgroup.toAddSubgroup := by
  simp [closedSubgroupSubmoduleOrderIso]
  rfl

@[simp]
theorem mem_closedSubgroupSubmoduleOrderIso_symm (hA : IsProP p A)
    (S : letI := hA.module; ClosedSubmodule ℤ_[p] (Additive A)) (x : A) :
    letI := hA.module
    x ∈ hA.closedSubgroupSubmoduleOrderIso.symm S ↔ Additive.ofMul x ∈ S := by
  let _ := hA.module
  let _ := hA.continuousSMul_module
  exact mem_closedAddSubgroupPadicIntSubmoduleOrderIso_symm p S

/-- The canonical module on a closed subgroup is the corresponding submodule of the
canonical module on the ambient group. -/
noncomputable def subgroupContinuousLinearEquivModule (hA : IsProP p A) (H : ClosedSubgroup A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.subgroup H.toSubgroup).module
    Additive H.toSubgroup ≃L[ℤ_[p]] (hA.closedSubgroupSubmoduleOrderIso H).toSubmodule := by
  letI := hA.module
  letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  letI := (hA.subgroup H.toSubgroup).module
  letI := hA.continuousSMul_module
  letI := (hA.subgroup H.toSubgroup).continuousSMul_module
  let e : Additive H.toSubgroup ≃+ (hA.closedSubgroupSubmoduleOrderIso H).toSubmodule :=
    { toFun := fun x ↦ ⟨Additive.ofMul x.toMul.val,
        (hA.mem_closedSubgroupSubmoduleOrderIso H _).mpr x.toMul.property⟩
      invFun := fun y ↦ Additive.ofMul ⟨y.val.toMul,
        (hA.mem_closedSubgroupSubmoduleOrderIso H _).mp y.property⟩
      left_inv := fun x ↦ by rfl
      right_inv := fun y ↦ by rfl
      map_add' := fun x y ↦ by rfl }
  exact e.toPadicIntLinearEquiv p
    ((continuous_ofMul.comp (continuous_subtype_val.comp continuous_toMul)).subtype_mk _)
    (continuous_ofMul.comp ((continuous_toMul.comp continuous_subtype_val).subtype_mk _))

@[simp]
theorem subgroupContinuousLinearEquivModule_apply (hA : IsProP p A) (H : ClosedSubgroup A)
    (x : Additive H.toSubgroup) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.subgroup H.toSubgroup).module
    (hA.subgroupContinuousLinearEquivModule H x : Additive A) = Additive.ofMul x.toMul.val := by
  let _ := hA.module
  let _ : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  let _ := (hA.subgroup H.toSubgroup).module
  let _ := hA.continuousSMul_module
  let _ := (hA.subgroup H.toSubgroup).continuousSMul_module
  dsimp only [subgroupContinuousLinearEquivModule]
  exact congrArg
    (fun y : (hA.closedSubgroupSubmoduleOrderIso H).toSubmodule ↦ (y : Additive A))
    (congrFun (AddEquiv.coe_toPadicIntLinearEquiv p _ _ _) x)

@[simp]
theorem subgroupContinuousLinearEquivModule_symm_apply (hA : IsProP p A) (H : ClosedSubgroup A)
    (y : letI := hA.module; (hA.closedSubgroupSubmoduleOrderIso H).toSubmodule) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.subgroup H.toSubgroup).module
    ((hA.subgroupContinuousLinearEquivModule H).symm y).toMul.val = y.val.toMul := by
  let _ := hA.module
  let _ : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  let _ := (hA.subgroup H.toSubgroup).module
  have h := hA.subgroupContinuousLinearEquivModule_apply H
    ((hA.subgroupContinuousLinearEquivModule H).symm y)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact congrArg Additive.toMul h.symm

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
  letI := hA.continuousSMul_module
  letI := (hA.quotient H.toSubgroup).continuousSMul_module
  exact (QuotientGroup.mk' H.toSubgroup).toAdditive.toPadicIntLinearMap p
    (continuous_ofMul.comp (QuotientGroup.continuous_mk.comp continuous_toMul))

@[simp]
theorem quotientMkLinear_apply (hA : IsProP p A) (H : ClosedSubgroup A) (x : Additive A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.quotient H.toSubgroup).module
    hA.quotientMkLinear H x = Additive.ofMul (x.toMul : A ⧸ H.toSubgroup) := by
  let _ := hA.module
  let _ : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  let _ := (hA.quotient H.toSubgroup).module
  let _ := hA.continuousSMul_module
  let _ := (hA.quotient H.toSubgroup).continuousSMul_module
  dsimp only [quotientMkLinear]
  exact congrFun (AddMonoidHom.coe_toPadicIntLinearMap p _ _) x

/-- The kernel of the linear quotient projection is the submodule corresponding to the
closed subgroup. -/
@[simp]
theorem ker_quotientMkLinear (hA : IsProP p A) (H : ClosedSubgroup A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.quotient H.toSubgroup).module
    (hA.quotientMkLinear H).ker = (hA.closedSubgroupSubmoduleOrderIso H).toSubmodule := by
  let _ := hA.module
  let _ : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  let _ := (hA.quotient H.toSubgroup).module
  ext x
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, quotientMkLinear_apply,
    ofMul_eq_zero, QuotientGroup.eq_one_iff,
    ClosedSubmodule.mem_toSubmodule_iff, mem_closedSubgroupSubmoduleOrderIso]
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
noncomputable def quotientContinuousLinearEquivModule (hA : IsProP p A) (H : ClosedSubgroup A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.quotient H.toSubgroup).module
    (Additive A ⧸ (hA.closedSubgroupSubmoduleOrderIso H).toSubmodule) ≃L[ℤ_[p]]
      Additive (A ⧸ H.toSubgroup) := by
  letI := hA.module
  letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  letI := (hA.quotient H.toSubgroup).module
  let S := (hA.closedSubgroupSubmoduleOrderIso H).toSubmodule
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
theorem quotientContinuousLinearEquivModule_mk (hA : IsProP p A) (H : ClosedSubgroup A)
    (x : Additive A) :
    letI := hA.module
    letI : IsClosed (H.toSubgroup : Set A) := H.isClosed'
    letI := (hA.quotient H.toSubgroup).module
    hA.quotientContinuousLinearEquivModule H (Submodule.Quotient.mk x) =
      Additive.ofMul (x.toMul : A ⧸ H.toSubgroup) := by
  let _ := hA.module
  let _ : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  let _ := (hA.quotient H.toSubgroup).module
  -- Pass from the continuous wrapper to the linear equivalence so its application lemmas apply.
  change ((Submodule.quotEquivOfEq _ _ (hA.ker_quotientMkLinear H).symm).trans
    ((hA.quotientMkLinear H).toLinearMap.quotKerEquivOfSurjective
      (hA.quotientMkLinear_surjective H))) (Submodule.Quotient.mk x) = _
  rw [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact quotientMkLinear_apply hA H x

end TauCeti.IsProP
