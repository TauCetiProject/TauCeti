/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient

/-!
# Local coefficient systems on contractible spaces are constant

Pulling a local coefficient system back along the constant map at `y` gives the constant system
at the fibre over `y` (`TauCeti.LocalCoefficientSystem.pullbackConstIso`). Combined with the
comparison of pullbacks along homotopic maps, a homotopy from the identity of `X` to the constant
map at `x` identifies every local coefficient system on `X` with the constant system at its fibre
over `x` (`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy`). This reduces homology with local
coefficients of a contractible space, such as a disk, and of pairs with contractible ambient space,
to homology with constant coefficients.

## Main definitions

* `TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy`: a null-homotopy of the identity makes a
  local coefficient system constant, by transport along the paths traced by the homotopy
  (`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy_hom_app`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

variable {X : TopCat.{v}} {x : X}

/-- **A local coefficient system on a contractible space is constant**: a homotopy `H` from the
identity of `X` to the constant map at `x` identifies every local coefficient system `L` on `X`
with the constant system at its fibre over `x`. At a point `x'` the comparison is transport by
`L` along the path `t ↦ H (t, x')` from `x'` to `x`
(`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy_hom_app`). -/
def isoConstantOfHomotopy (H : (ContinuousMap.id X).Homotopy (ContinuousMap.const X x))
    (L : LocalCoefficientSystem.{u, v, w} R X) :
    L ≅ (constantFunctor (R := R) X).obj (L.obj (FundamentalGroupoid.mk x)) :=
  ((pullbackIdIso (R := R) X).app L).symm ≪≫ (pullbackHomotopyIso (R := R) H).app L ≪≫
    pullbackConstIso X x L

/-- At a point `x'`, the comparison `TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy` is
transport along the path traced by the homotopy from `x'`. -/
@[simp]
theorem isoConstantOfHomotopy_hom_app
    (H : (ContinuousMap.id X).Homotopy (ContinuousMap.const X x))
    (L : LocalCoefficientSystem.{u, v, w} R X) (x' : FundamentalGroupoid X) :
    (isoConstantOfHomotopy H L).hom.app x' = L.map ⟦H.evalAt x'.as⟧ := by
  simp only [isoConstantOfHomotopy, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.app_inv, Iso.app_hom, pullbackHomotopyIso_hom_app_app, pullbackConstIso_hom_app]
  -- The identity comparison of `pullbackIdIso` and of `pullbackConstIso` sit between objects that
  -- are only definitionally equal, so the unit laws are applied by `exact`.
  exact (congrArg (· ≫ _) (pullbackIdIso_inv_app_app X L x')).trans
    ((Category.id_comp _).trans (Category.comp_id _))

end TauCeti.LocalCoefficientSystem
