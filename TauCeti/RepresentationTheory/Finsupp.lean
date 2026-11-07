/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.AsModule

/-!
# Direct sums of copies of a representation

The native `Representation.finsupp` acts coefficientwise. Passing to the associated
module over the monoid algebra commutes with this direct sum, without a finiteness
assumption on the index set. These comparisons let module decomposition results
apply to direct sums of representations.

The group-algebra comparison follows Mathlib's `Representation.finsuppLEquivFreeAsModule`,
with an arbitrary representation in place of the regular representation.
-/

public section

open scoped MonoidAlgebra

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G]
  [AddCommMonoid V] [Module k V]

/-- The direct sum of copies of a representation acts coefficientwise. -/
@[simp]
theorem finsupp_apply_apply (ρ : Representation k G V) (ι : Type*)
    (g : G) (f : ι →₀ V) (i : ι) : ρ.finsupp ι g f i = ρ g (f i) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f h hf hh => simp [hf, hh]
  | single j x =>
    by_cases h : j = i <;> simp [h]

/-- Passing to the group-algebra module commutes with direct sums of copies of a
representation. The equivalence preserves every coefficient. -/
noncomputable def finsuppAsModuleEquiv (ρ : Representation k G V) (ι : Type*) :
    (ρ.finsupp ι).asModule ≃ₗ[k[G]] (ι →₀ ρ.asModule) := by
  let e := (ρ.finsupp ι).asModuleEquiv ≪≫ₗ
    Finsupp.mapRange.linearEquiv ρ.asModuleEquiv.symm
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro r x
  simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, RingHom.id_apply]
  obtain ⟨x, rfl⟩ := (ρ.finsupp ι).asModuleEquiv.symm.surjective x
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp only [zero_smul, map_zero]
  | add r s hr hs => simp only [add_smul, map_add, hr, hs]
  | single g c =>
    induction x using Finsupp.induction_linear with
    | zero => simp only [map_zero, smul_zero]
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | single i x =>
      have he (y : V) : e ((ρ.finsupp ι).asModuleEquiv.symm (Finsupp.single i y)) =
          Finsupp.single i (ρ.asModuleEquiv.symm y) := by
        simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
          Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_single]
      have hsource := Representation.single_smul (ρ := ρ.finsupp ι) c g
        ((ρ.finsupp ι).asModuleEquiv.symm (Finsupp.single i x))
      have htarget := Representation.single_smul (ρ := ρ) c g
        (ρ.asModuleEquiv.symm x)
      rw [LinearEquiv.apply_symm_apply, Representation.finsupp_single,
        Finsupp.smul_single] at hsource
      calc
        _ = e ((ρ.finsupp ι).asModuleEquiv.symm (Finsupp.single i (c • ρ g x))) :=
          congrArg e hsource
        _ = Finsupp.single i (ρ.asModuleEquiv.symm (c • ρ g x)) := he _
        _ = Finsupp.single i (MonoidAlgebra.single g c • ρ.asModuleEquiv.symm x) := by
          rw [htarget]
          rfl
        _ = _ := by rw [he, Finsupp.smul_single]

/-- The direct-sum comparison is coefficientwise the carrier identification. -/
@[simp]
theorem finsuppAsModuleEquiv_apply
    (ρ : Representation k G V) (ι : Type*) (x : (ρ.finsupp ι).asModule) (i : ι) :
    ρ.finsuppAsModuleEquiv ι x i =
      ρ.asModuleEquiv.symm ((ρ.finsupp ι).asModuleEquiv x i) := (rfl)

/-- The inverse comparison also preserves every coefficient. -/
@[simp]
theorem finsuppAsModuleEquiv_symm_apply
    (ρ : Representation k G V) (ι : Type*) (f : ι →₀ ρ.asModule) (i : ι) :
    DFunLike.coe (F := ι →₀ V) ((ρ.finsuppAsModuleEquiv ι).symm f) i =
      ρ.asModuleEquiv (f i) := (rfl)

end Representation
