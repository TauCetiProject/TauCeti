/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Local coefficient systems on contractible spaces are constant

Pulling a local coefficient system back along the constant map at `y` gives the constant system
at the fibre over `y` (`TauCeti.LocalCoefficientSystem.pullbackConstIso`). Combined with the
comparison of pullbacks along homotopic maps, the pullback along any map homotopic to the constant
map at `y` is the constant system at the fibre over `y`
(`TauCeti.LocalCoefficientSystem.pullbackIsoConstantOfHomotopy`). For the identity of `X`, a
homotopy to the constant map at `x` identifies every local coefficient system on `X` with the
constant system at its fibre over `x` (`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy`).
This reduces homology with local coefficients of a contractible space, such as a disk, and of
pairs with contractible ambient space, to homology with constant coefficients.

## Main definitions

* `TauCeti.LocalCoefficientSystem.pullbackIsoConstantOfHomotopy`: the pullback of a local
  coefficient system along a map homotopic to a constant map is constant, by transport along the
  paths traced by the homotopy
  (`TauCeti.LocalCoefficientSystem.pullbackIsoConstantOfHomotopy_hom_app`).
* `TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy`: a null-homotopy of the identity makes a
  local coefficient system constant, by transport along the paths traced by the homotopy
  (`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy_hom_app`); its inverse is transport along
  any path from `x` (`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy_inv_app`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory

universe u v v₁ v₂ w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section Pullback

variable {X : TopCat.{v₁}} {Y : TopCat.{v₂}} {f : C(X, Y)} {y : Y}

/-- **The pullback along a null-homotopic map is constant**: a homotopy `H` from `f : X → Y` to
the constant map at `y` identifies the pullback along `f` of every local coefficient system `L` on
`Y` with the constant system at the fibre of `L` over `y`. At a point `x` the comparison is
transport by `L` along the path `t ↦ H (t, x)` from `f x` to `y`
(`TauCeti.LocalCoefficientSystem.pullbackIsoConstantOfHomotopy_hom_app`). -/
def pullbackIsoConstantOfHomotopy (H : f.Homotopy (ContinuousMap.const X y))
    (L : LocalCoefficientSystem.{u, v₂, w} R Y) :
    (pullback (R := R) f).obj L ≅
      (constantFunctor (R := R) X).obj (L.obj (FundamentalGroupoid.mk y)) :=
  (pullbackHomotopyIso (R := R) H).app L ≪≫ pullbackConstIso X y L

/-- At a point `x`, the comparison `TauCeti.LocalCoefficientSystem.pullbackIsoConstantOfHomotopy`
is transport along the path traced by the homotopy from `x`. -/
@[simp]
theorem pullbackIsoConstantOfHomotopy_hom_app (H : f.Homotopy (ContinuousMap.const X y))
    (L : LocalCoefficientSystem.{u, v₂, w} R Y) (x : FundamentalGroupoid X) :
    (pullbackIsoConstantOfHomotopy H L).hom.app x = L.map ⟦H.evalAt x.as⟧ := by
  simp only [pullbackIsoConstantOfHomotopy, Iso.trans_hom, NatTrans.comp_app, Iso.app_hom,
    pullbackHomotopyIso_hom_app_app, pullbackConstIso_hom_app]
  -- The component of `pullbackConstIso` is an identity between objects that are only
  -- definitionally equal, so the unit law is applied by `exact`.
  exact Category.comp_id _

end Pullback

variable {X : TopCat.{v}} {x : X}

/-- **A local coefficient system on a contractible space is constant**: a homotopy `H` from the
identity of `X` to the constant map at `x` identifies every local coefficient system `L` on `X`
with the constant system at its fibre over `x`. At a point `x'` the comparison is transport by
`L` along the path `t ↦ H (t, x')` from `x'` to `x`
(`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy_hom_app`). -/
def isoConstantOfHomotopy (H : (ContinuousMap.id X).Homotopy (ContinuousMap.const X x))
    (L : LocalCoefficientSystem.{u, v, w} R X) :
    L ≅ (constantFunctor (R := R) X).obj (L.obj (FundamentalGroupoid.mk x)) :=
  ((pullbackIdIso (R := R) X).app L).symm ≪≫ pullbackIsoConstantOfHomotopy H L

/-- At a point `x'`, the comparison `TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy` is
transport along the path traced by the homotopy from `x'`. -/
@[simp]
theorem isoConstantOfHomotopy_hom_app
    (H : (ContinuousMap.id X).Homotopy (ContinuousMap.const X x))
    (L : LocalCoefficientSystem.{u, v, w} R X) (x' : FundamentalGroupoid X) :
    (isoConstantOfHomotopy H L).hom.app x' = L.map ⟦H.evalAt x'.as⟧ := by
  simp only [isoConstantOfHomotopy, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.app_inv, pullbackIsoConstantOfHomotopy_hom_app]
  -- The identity comparison of `pullbackIdIso` sits between objects that are only definitionally
  -- equal, so the unit law is applied by `exact`.
  exact (congrArg (· ≫ _) (pullbackIdIso_inv_app_app X L x')).trans (Category.id_comp _)

/-- At a point `x'`, the inverse of the comparison
`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy` is transport along any path from `x` to
`x'`: the space is contractible, so all such paths are homotopic. -/
theorem isoConstantOfHomotopy_inv_app
    (H : (ContinuousMap.id X).Homotopy (ContinuousMap.const X x))
    (L : LocalCoefficientSystem.{u, v, w} R X) {x' : FundamentalGroupoid X}
    (q : FundamentalGroupoid.mk x ⟶ x') :
    (isoConstantOfHomotopy H L).inv.app x' = L.map q := by
  have : ContractibleSpace X := (contractible_iff_id_nullhomotopic _).2 ⟨x, ⟨H⟩⟩
  refine ((isoConstantOfHomotopy H L).app x').inv_ext ?_
  rw [Iso.app_hom, isoConstantOfHomotopy_hom_app]
  -- The space is contractible, so its fundamental groupoid is thin.
  exact (L.map_comp _ q).symm.trans ((congrArg L.map
    (Subsingleton.elim (α := Path.Homotopic.Quotient _ _) _ _)).trans (L.map_id _))

end TauCeti.LocalCoefficientSystem
