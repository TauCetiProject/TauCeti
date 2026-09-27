/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Centralizer
public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Action
public import TauCeti.Algebra.Module.Submodule.Quotient

/-!
# The quotient represented by the modular F₄ short-root action

The adjoint action on the twenty-six-dimensional short-root ideal detects the ambient modular
Chevalley Lie algebra modulo the short-root ideal. Consequently, the quotient by that ideal is
linearly equivalent to the represented range modulo the image of the ideal.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra

noncomputable section

/-- The kernel of the adjoint action on the modular short-root ideal is contained in that ideal. -/
theorem ker_f4ShortRootAdjoint_le_f4ShortRootSubspace :
    LinearMap.ker (f4ShortRootAdjoint : f4ModularChevalleyLieAlgebra →ₗ[ZMod 2]
      Module.End (ZMod 2) f4ShortRootLieIdeal) ≤ f4ShortRootSubspace := by
  intro X hX
  apply mem_f4ShortRootSubspace_of_forall_lie_rootVector_eq_zero X
  intro β hβ
  let y : f4ShortRootLieIdeal :=
    ⟨f4ModularRootVector β,
      mem_f4ShortRootLieIdeal_iff.mpr
        (f4ModularRootVector_mem_shortRootSubspace β hβ)⟩
  have happly : f4ShortRootAdjoint X y = 0 :=
    congrArg (fun f : Module.End (ZMod 2) f4ShortRootLieIdeal => f y) hX
  calc
    ⁅X, f4ModularRootVector β⁆ =
        (f4ShortRootAdjoint X y : f4ModularChevalleyLieAlgebra) := by
      rw [coe_f4ShortRootAdjoint_apply]
    _ = 0 := congrArg (fun z : f4ShortRootLieIdeal =>
      (z : f4ModularChevalleyLieAlgebra)) happly

/-- The range of the modular short-root adjoint action. -/
abbrev f4ShortRootRepresentedRange :=
  LinearMap.range (f4ShortRootAdjoint : f4ModularChevalleyLieAlgebra →ₗ[ZMod 2]
    Module.End (ZMod 2) f4ShortRootLieIdeal)

/-- The image of the modular short-root ideal inside the represented range. -/
abbrev f4ShortRootRepresentedIdeal :
    Submodule (ZMod 2) f4ShortRootRepresentedRange :=
  f4ShortRootSubspace.map
    (f4ShortRootAdjoint : f4ModularChevalleyLieAlgebra →ₗ[ZMod 2]
      Module.End (ZMod 2) f4ShortRootLieIdeal).rangeRestrict

end

end TauCeti.DynkinType
