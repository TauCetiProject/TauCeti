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
  let f := MonoidAlgebra.equivariantOfLinearOfComm (M := G) e.toLinearMap (fun g x ↦ by
    -- Expose the underlying equivalence of the linear map supplied to the constructor.
    change e (MonoidAlgebra.single g 1 • x) = MonoidAlgebra.single g 1 • e x
    rw [Representation.single_smul, one_smul]
    ext i
    -- The source action now has the representation carrier, not its module synonym.
    change (ρ.finsupp ι g ((ρ.finsupp ι).asModuleEquiv x)) i =
      (MonoidAlgebra.single g 1 • e x) i
    rw [Finsupp.smul_apply, Representation.single_smul, one_smul,
      Representation.finsupp_apply_apply]
    rfl)
  exact { e.toAddEquiv with map_smul' := f.map_smul }

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
