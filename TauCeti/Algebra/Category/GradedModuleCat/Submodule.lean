/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# Homogeneous submodules as graded modules

A homogeneous `A`-submodule `U` of a graded `𝒜`-module `M` inherits an internal grading whose
degree-`p` piece is `U ∩ Mₚ`, together with a compatible graded `A`-action. This file packages `U`
as an object `TauCeti.GradedModuleCat.submoduleObj M U hU` of `GradedModuleCat 𝒜`.

## Main definitions

* `TauCeti.GradedModuleCat.submoduleObj`: a homogeneous `A`-submodule packaged as a graded
  `𝒜`-module.
-/

public section

namespace TauCeti.GradedModuleCat

universe v uk uA

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- A homogeneous `A`-submodule of a graded `𝒜`-module, packaged as a graded `𝒜`-module with the
induced internal grading. -/
noncomputable abbrev submoduleObj (M : GradedModuleCat.{v} 𝒜) (U : Submodule A M)
    (hU : _root_.DirectSum.SetLike.IsHomogeneous M.grading.piece U) : GradedModuleCat.{v} 𝒜 where
  carrier := U
  isAddCommGroup := Submodule.addCommGroup _
  isModule := Submodule.module _
  isModuleBase := Submodule.module' _
  grading := M.grading.submodule U hU
  gradedSMul := ⟨fun {_ _} _ _ ha hx ↦ by
    rw [InternalGrading.mem_submodule_piece] at hx ⊢
    exact SetLike.GradedSMul.smul_mem (B := M.grading.piece) ha hx⟩

end TauCeti.GradedModuleCat
