/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Minimal.Basic
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Transfer
public import TauCeti.Algebra.Homology.Contraction.Linear.Homology

/-!
# Minimal models of right A-infinity modules

Let `M` be a right `A∞` module over an `A∞` algebra `A` over a field.  Its unary operation `m₁` is
a square-zero endomorphism of degree one, and the graded vector space `M` contracts onto the
homology `H = ker m₁ ⧸ im m₁` with zero differential
(`TauCeti.InternalGrading.homologyContraction`).  Homological transfer of right `A∞` modules
(`TauCeti.AInfinityRightModule.transfer`) along this contraction puts a right `A∞` module structure
over the same algebra `A` on `H`, the **minimal model** `TauCeti.AInfinityRightModule.minimalModel`,
whose unary operation vanishes.  It comes with two quasi-isomorphisms of right `A∞` modules,
`TauCeti.AInfinityRightModule.minimalModelInclusion` from the minimal model to `M` and
`TauCeti.AInfinityRightModule.minimalModelProjection` from `M` to the minimal model, the second a
left inverse of the first.  The linear part of the inclusion sends each homology class to a cycle
representing it, and the linear part of the projection sends each cycle to its class, so both
induce the identity on cohomology.

This is the module version of Kadeishvili's theorem: over a field, every right `A∞` module is
quasi-isomorphic to a minimal one on its cohomology.  The algebra is not replaced: the minimal
model is a module over `A` itself, with all of its higher operations transferred from those of
`M`.  The minimal model is unique up to isomorphism: composing with the projection onto, or the
inclusion of, the minimal model turns a quasi-isomorphism into `M` from a minimal module, or out of
`M` to a minimal module, into an isomorphism of right `A∞` modules.  The isomorphism depends on
the chosen quasi-isomorphism and is not canonical.  It comes from the fact that a
quasi-isomorphism between minimal modules is an isomorphism
(`TauCeti.AInfinityRightModuleHom.IsQuasiIso.isIso`, in
`TauCeti.Algebra.Homology.AInfinity.Module.Right.Minimal.Basic`).

## Main definitions

* `TauCeti.AInfinityRightModule.minimalModel`: the transferred right `A∞` module structure on the
  homology of the unary operation.
* `TauCeti.AInfinityRightModule.minimalModelInclusion`: the quasi-isomorphism from the minimal
  model to the module.
* `TauCeti.AInfinityRightModule.minimalModelProjection`: the quasi-isomorphism from the module to
  its minimal model.

## Main results

* `TauCeti.AInfinityRightModule.isMinimal_minimalModel`: the minimal model is minimal, that is,
  it has zero unary operation.
* `TauCeti.AInfinityRightModule.isQuasiIso_minimalModelInclusion` and
  `TauCeti.AInfinityRightModule.isQuasiIso_minimalModelProjection`: both morphisms are
  quasi-isomorphisms.
* `TauCeti.AInfinityRightModule.minimalModelProjection_comp_minimalModelInclusion`: the projection
  is a left inverse of the inclusion.
* `TauCeti.AInfinityRightModule.homologyπ_linearPart_minimalModelInclusion` and
  `TauCeti.AInfinityRightModule.linearPart_minimalModelProjection_of_mem_ker`: the inclusion
  chooses representatives of homology classes and the projection takes classes of cycles.
* `TauCeti.AInfinityRightModule.cohomologyEquivHomology_cohomologyMap_minimalModelInclusion` and
  `TauCeti.AInfinityRightModule.cohomologyMap_minimalModelProjection_cohomologyClass`: both
  morphisms induce the identity on cohomology.
* `TauCeti.AInfinityRightModule.isIso_minimalModelProjection_comp` and
  `TauCeti.AInfinityRightModule.isIso_comp_minimalModelInclusion`: **uniqueness of the minimal
  model**; a quasi-isomorphism from or to a minimal module, composed with the projection onto or
  the inclusion of the minimal model, is an isomorphism of right `A∞` modules.

## References

* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 4.
-/

public section

namespace TauCeti

universe uK uA uM uN

/-! ### The minimal model over a field -/

namespace AInfinityRightModule

variable {K : Type uK} {A : Type uA} {M : Type uM} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup M] [Module K M] {AA : AInfinityAlgebra K A} (MM : AInfinityRightModule AA M)

/-- The **minimal model** of a right `A∞` module over a field: the right `A∞` module over the same
algebra on the homology `ker m₁ ⧸ im m₁` of its unary operation, transferred along the contraction
of the module onto this homology.  Its unary operation vanishes (`differential_minimalModel`). -/
noncomputable def minimalModel :
    AInfinityRightModule AA (MM.differential.homology MM.differential_comp_self_eq_zero) :=
  MM.transfer (MM.grading.homologyContraction MM.isHomogeneous_differential
      MM.differential_comp_self_eq_zero)
    (MM.grading.isHomogeneous_homologyContraction_homotopy _ _)
    (MM.grading.isHomogeneous_homologyContraction_incl _ _)
    (MM.grading.isHomogeneous_homologyContraction_proj _ _)

/-- The minimal model is graded by the degrees of homogeneous cycles. -/
@[simp]
theorem minimalModel_grading :
    MM.minimalModel.grading =
      MM.grading.homology MM.isHomogeneous_differential MM.differential_comp_self_eq_zero :=
  transfer_grading ..

/-- The minimal model has zero unary operation. -/
@[simp]
theorem differential_minimalModel : MM.minimalModel.differential = 0 :=
  differential_transfer ..

/-- The minimal model is a minimal module. -/
theorem isMinimal_minimalModel : MM.minimalModel.IsMinimal :=
  (isMinimal_def _).2 MM.differential_minimalModel

/-- Every element of the minimal model is a cycle. -/
theorem mem_cycles_minimalModel
    (y : MM.differential.homology MM.differential_comp_self_eq_zero) :
    y ∈ MM.minimalModel.cycles := by
  rw [mem_cycles, differential_minimalModel, LinearMap.zero_apply]

/-- The quasi-isomorphism from the minimal model to the module, extending the choice of cycle
representatives of homology classes. -/
noncomputable def minimalModelInclusion : AInfinityRightModuleHom MM.minimalModel MM :=
  MM.transferInclusion _ (MM.grading.isHomogeneous_homologyContraction_homotopy _ _)
    (MM.grading.isHomogeneous_homologyContraction_incl _ _)
    (MM.grading.isHomogeneous_homologyContraction_proj _ _)

/-- The linear part of the inclusion of the minimal model is the inclusion of the contraction onto
homology. -/
@[simp]
theorem linearPart_minimalModelInclusion :
    MM.minimalModelInclusion.linearPart =
      (MM.grading.homologyContraction MM.isHomogeneous_differential
        MM.differential_comp_self_eq_zero).incl :=
  linearPart_transferInclusion ..

/-- The linear part of the inclusion of the minimal model takes values in the cycles. -/
theorem linearPart_minimalModelInclusion_mem_ker
    (y : MM.differential.homology MM.differential_comp_self_eq_zero) :
    MM.minimalModelInclusion.linearPart y ∈ LinearMap.ker MM.differential := by
  rw [linearPart_minimalModelInclusion]
  exact InternalGrading.homologyContraction_incl_mem_ker ..

/-- The linear part of the inclusion of the minimal model sends a homology class to a cycle
representing it. -/
theorem homologyπ_linearPart_minimalModelInclusion
    (y : MM.differential.homology MM.differential_comp_self_eq_zero) :
    MM.differential.homologyπ MM.differential_comp_self_eq_zero
        ⟨_, MM.linearPart_minimalModelInclusion_mem_ker y⟩ = y := by
  simp only [linearPart_minimalModelInclusion]
  exact InternalGrading.homologyπ_homologyContraction_incl ..

/-- The inclusion of the minimal model induces the identity on cohomology: under the
identification of module cohomology with the homology of `m₁`, the class of an element `y` of the
minimal model goes to `y`. -/
theorem cohomologyEquivHomology_cohomologyMap_minimalModelInclusion
    (y : MM.differential.homology MM.differential_comp_self_eq_zero) :
    MM.cohomologyEquivHomology (MM.minimalModelInclusion.cohomologyMap
      (MM.minimalModel.cohomologyClass (MM.mem_cycles_minimalModel y))) = y := by
  rw [AInfinityRightModuleHom.cohomologyMap_cohomologyClass,
    cohomologyEquivHomology_cohomologyClass]
  exact MM.homologyπ_linearPart_minimalModelInclusion y

/-- The inclusion of the minimal model is a quasi-isomorphism. -/
theorem isQuasiIso_minimalModelInclusion : MM.minimalModelInclusion.IsQuasiIso :=
  isQuasiIso_transferInclusion ..

/-- The quasi-isomorphism from the module to its minimal model, extending the projection which
sends a cycle to its homology class. -/
noncomputable def minimalModelProjection : AInfinityRightModuleHom MM MM.minimalModel :=
  MM.transferProjection _ (MM.grading.isHomogeneous_homologyContraction_homotopy _ _)
    (MM.grading.isHomogeneous_homologyContraction_incl _ _)
    (MM.grading.isHomogeneous_homologyContraction_proj _ _)

/-- The linear part of the projection onto the minimal model is the projection of the contraction
onto homology. -/
@[simp]
theorem linearPart_minimalModelProjection :
    MM.minimalModelProjection.linearPart =
      (MM.grading.homologyContraction MM.isHomogeneous_differential
        MM.differential_comp_self_eq_zero).proj :=
  linearPart_transferProjection ..

/-- The linear part of the projection onto the minimal model sends a cycle to its homology
class. -/
theorem linearPart_minimalModelProjection_of_mem_ker {x : M}
    (hx : x ∈ LinearMap.ker MM.differential) :
    MM.minimalModelProjection.linearPart x =
      MM.differential.homologyπ MM.differential_comp_self_eq_zero ⟨x, hx⟩ := by
  rw [linearPart_minimalModelProjection, InternalGrading.homologyContraction_proj_of_mem_ker]

/-- The projection onto the minimal model is a left inverse of its inclusion. -/
@[simp]
theorem minimalModelProjection_comp_minimalModelInclusion :
    MM.minimalModelProjection.comp MM.minimalModelInclusion =
      AInfinityRightModuleHom.id MM.minimalModel :=
  transferProjection_comp_transferInclusion ..

/-- The projection onto the minimal model induces the identity on cohomology: the class of a
cycle `x` goes to the class of the homology class of `x`, viewed as an element of the minimal
model. -/
theorem cohomologyMap_minimalModelProjection_cohomologyClass {x : M} (hx : x ∈ MM.cycles) :
    MM.minimalModelProjection.cohomologyMap (MM.cohomologyClass hx) =
      MM.minimalModel.cohomologyClass
        (MM.mem_cycles_minimalModel (MM.cohomologyEquivHomology (MM.cohomologyClass hx))) := by
  rw [AInfinityRightModuleHom.cohomologyMap_cohomologyClass]
  congr 1
  rw [cohomologyEquivHomology_cohomologyClass, linearPart_minimalModelProjection_of_mem_ker]

/-- The projection onto the minimal model is a quasi-isomorphism. -/
theorem isQuasiIso_minimalModelProjection : MM.minimalModelProjection.IsQuasiIso :=
  isQuasiIso_transferProjection ..

/-! ### Uniqueness of the minimal model -/

section Uniqueness

variable {N : Type uN} [AddCommGroup N] [Module K N] {NN : AInfinityRightModule AA N}

/-- **Uniqueness of the minimal model**, for a quasi-isomorphism into `M`: if `f` is a
quasi-isomorphism from a minimal module to `M`, then `f` followed by the projection onto the
minimal model is an isomorphism of right `A∞` modules. -/
theorem isIso_minimalModelProjection_comp (hN : NN.IsMinimal)
    {f : AInfinityRightModuleHom NN MM} (hf : f.IsQuasiIso) :
    (MM.minimalModelProjection.comp f).IsIso :=
  (MM.isQuasiIso_minimalModelProjection.comp hf).isIso hN MM.isMinimal_minimalModel

/-- **Uniqueness of the minimal model**, for a quasi-isomorphism out of `M`: if `g` is a
quasi-isomorphism from `M` to a minimal module, then the inclusion of the minimal model followed
by `g` is an isomorphism of right `A∞` modules. -/
theorem isIso_comp_minimalModelInclusion (hN : NN.IsMinimal)
    {g : AInfinityRightModuleHom MM NN} (hg : g.IsQuasiIso) :
    (g.comp MM.minimalModelInclusion).IsIso :=
  (hg.comp MM.isQuasiIso_minimalModelInclusion).isIso MM.isMinimal_minimalModel hN

end Uniqueness

end AInfinityRightModule

end TauCeti
