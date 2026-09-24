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

/-- The adjoint action on the modular short-root ideal, viewed as a linear map. -/
noncomputable def f4ShortRootAdjointLinearMap :
    f4ModularChevalleyLieAlgebra →ₗ[ZMod 2]
      Module.End (ZMod 2) f4ShortRootLieIdeal :=
  f4ShortRootAdjoint

@[simp] theorem f4ShortRootAdjointLinearMap_apply
    (X : f4ModularChevalleyLieAlgebra) (y : f4ShortRootLieIdeal) :
    f4ShortRootAdjointLinearMap X y = f4ShortRootAdjoint X y := by
  simp [f4ShortRootAdjointLinearMap]

/-- The kernel of the adjoint action on the modular short-root ideal is contained in that ideal. -/
theorem ker_f4ShortRootAdjoint_le_f4ShortRootSubspace :
    LinearMap.ker f4ShortRootAdjointLinearMap ≤ f4ShortRootSubspace := by
  intro X hX
  apply mem_f4ShortRootSubspace_of_forall_lie_rootVector_eq_zero X
  intro β hβ
  let y : f4ShortRootLieIdeal :=
    ⟨f4ModularRootVector β,
      mem_f4ShortRootLieIdeal_iff.mpr
        (f4ModularRootVector_mem_shortRootSubspace β hβ)⟩
  have happly : f4ShortRootAdjointLinearMap X y = 0 :=
    congrArg (fun f : Module.End (ZMod 2) f4ShortRootLieIdeal => f y) hX
  calc
    ⁅X, f4ModularRootVector β⁆ =
        (f4ShortRootAdjoint X y : f4ModularChevalleyLieAlgebra) := by
      rw [coe_f4ShortRootAdjoint_apply]
    _ = (f4ShortRootAdjointLinearMap X y : f4ModularChevalleyLieAlgebra) :=
      congrArg (fun z : f4ShortRootLieIdeal =>
        (z : f4ModularChevalleyLieAlgebra))
        (f4ShortRootAdjointLinearMap_apply X y).symm
    _ = 0 := congrArg (fun z : f4ShortRootLieIdeal =>
      (z : f4ModularChevalleyLieAlgebra)) happly

/-- The range of the modular short-root adjoint action. -/
abbrev f4ShortRootRepresentedRange :=
  LinearMap.range f4ShortRootAdjointLinearMap

/-- The image of the modular short-root ideal inside the represented range. -/
abbrev f4ShortRootRepresentedIdeal :
    Submodule (ZMod 2) f4ShortRootRepresentedRange :=
  f4ShortRootSubspace.map f4ShortRootAdjointLinearMap.rangeRestrict

/-- The modular Chevalley quotient by the short-root ideal, expressed as the quotient of the
represented range by the image of that ideal. -/
noncomputable def f4ShortRootQuotientEquivRepresentedRange :=
  LinearMap.quotientEquivRangeQuotientMap f4ShortRootAdjointLinearMap f4ShortRootSubspace
    ker_f4ShortRootAdjoint_le_f4ShortRootSubspace

/-- The represented-range equivalence evaluated on a modular Chevalley representative. -/
@[simp] theorem f4ShortRootQuotientEquivRepresentedRange_apply_mk
    (X : f4ModularChevalleyLieAlgebra) :
    f4ShortRootQuotientEquivRepresentedRange (Submodule.Quotient.mk X) =
      Submodule.Quotient.mk (f4ShortRootAdjointLinearMap.rangeRestrict X) :=
  LinearMap.quotientEquivRangeQuotientMap_apply_mk _ _ _ X


end

end TauCeti.DynkinType
