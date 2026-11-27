/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.FiniteEtale.Limits
public import TauCeti.AlgebraicGeometry.Morphisms.Unramified.Section
public import TauCeti.AlgebraicGeometry.ResidueField
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic

/-!
# Detecting section images in a geometric fibre

A finite étale scheme has as many points in a geometric fibre as its rank at the underlying
base point. Over a connected base this count detects whether a clopen subscheme is the image
of a section. It is enough to count its points above one chosen geometric point of the base.
A count of one gives a unique section.

The finite set in these statements is the value of the geometric fibre functor
`TauCeti.FiniteEtaleScheme.fiber`, so its points are lifts of the chosen geometric point.
The count uses `AlgebraicGeometry.Scheme.Hom.natCard_eq_finrank_of_etale` over the
separably closed field and invariance of rank under base change.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The cardinality of a geometric fibre of a finite étale scheme is its rank at the
underlying point of the base. -/
@[simp]
theorem natCard_fiber_obj (Y : FiniteEtaleScheme S) (x : Spec (.of Ω) ⟶ S) :
    Nat.card ((fiber x).obj Y) = Y.obj.hom.finrank (x default) := by
  let Z := (pullback x).obj Y
  calc
    Nat.card ((fiber x).obj Y) = Nat.card (Over.mk (𝟙 _) ⟶ Z.obj) :=
      Nat.card_congr ((equivOfIsSepClosedFunctorCompInclIso Ω).app Z).toEquiv
    _ = Z.obj.hom.finrank default := Z.obj.hom.natCard_eq_finrank_of_etale default
    _ = Y.obj.hom.finrank (x default) := Scheme.Hom.finrank_pullback_snd Y.obj.hom x default

/-- The number of geometric points above each point of the base is locally constant. -/
theorem isLocallyConstant_natCard_fiber_obj (Y : FiniteEtaleScheme S) :
    IsLocallyConstant fun s : S ↦ Nat.card ((fiber (S.fromSpecAlgebraicClosure s)).obj Y) := by
  simpa only [natCard_fiber_obj, Scheme.fromSpecAlgebraicClosure_apply] using
    Y.obj.hom.isLocallyConstant_finrank

/-- A finite étale scheme over a connected base maps isomorphically to the base exactly when
its fibre at one chosen geometric point has cardinality one. -/
theorem isIso_hom_iff_natCard_fiber_obj_eq_one [PreconnectedSpace S] (Y : FiniteEtaleScheme S)
    (x : Spec (.of Ω) ⟶ S) : IsIso Y.obj.hom ↔ Nat.card ((fiber x).obj Y) = 1 := by
  rw [natCard_fiber_obj, Y.obj.hom.isIso_iff_finrank_eq]
  exact ⟨fun h ↦ congrFun h _, fun h ↦ funext fun s ↦
    (Y.obj.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace s (x default)).trans h⟩

/-- Over a connected base, the sections of a finite étale scheme are in bijection with its
clopen subschemes that have exactly one point in a chosen geometric fibre. -/
noncomputable def splitEpiEquivClopensFiber [PreconnectedSpace S] (Y : FiniteEtaleScheme S)
    (x : Spec (.of Ω) ⟶ S) :
    SplitEpi Y.obj.hom ≃ {U : Clopens Y.obj.left //
      Nat.card ((fiber x).obj (clopenSubscheme (Y := Y) U.toOpens U.isClosed)) = 1} :=
  Y.obj.hom.splitEpiEquivClopens.trans <| Equiv.subtypeEquivRight fun U ↦ by
    rw [← isIso_hom_iff_natCard_fiber_obj_eq_one]
    exact Iff.of_eq (congrArg (fun W : Over S ↦ IsIso W.hom)
      (clopenSubscheme_obj (Y := Y) U.toOpens U.isClosed)).symm

/-- The clopen selected by the geometric fibre criterion is the image of the section. -/
@[simp]
theorem coe_splitEpiEquivClopensFiber_apply [PreconnectedSpace S] (Y : FiniteEtaleScheme S)
    (x : Spec (.of Ω) ⟶ S) (s : SplitEpi Y.obj.hom) :
    ((Y.splitEpiEquivClopensFiber x s).val : Set Y.obj.left) = Set.range s.section_ :=
  Y.obj.hom.coe_splitEpiEquivClopens_apply s

/-- The inverse correspondence recovers the section with the prescribed clopen image. -/
@[simp]
theorem range_splitEpiEquivClopensFiber_symm_section [PreconnectedSpace S] (Y : FiniteEtaleScheme S)
    (x : Spec (.of Ω) ⟶ S) (U : {U : Clopens Y.obj.left //
      Nat.card ((fiber x).obj (clopenSubscheme (Y := Y) U.toOpens U.isClosed)) = 1}) :
    Set.range ((Y.splitEpiEquivClopensFiber x).symm U).section_ = U.val := by
  rw [← Y.coe_splitEpiEquivClopensFiber_apply x, Equiv.apply_symm_apply]

end TauCeti.FiniteEtaleScheme
