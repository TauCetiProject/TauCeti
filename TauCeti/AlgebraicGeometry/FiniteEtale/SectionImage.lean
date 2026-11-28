/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.FiniteEtale.Limits
public import TauCeti.AlgebraicGeometry.Morphisms.Unramified.Section

/-!
# Detecting section images in a geometric fibre

Over a connected base, a clopen subscheme of a finite étale scheme is the image of a unique
section if its fibre at one chosen geometric point has cardinality one.

The finite set in these statements is the value of the geometric fibre functor
`TauCeti.FiniteEtaleScheme.fiber`, so its points are lifts of the chosen geometric point.
The correspondence uses `TauCeti.FiniteEtaleScheme.isIso_hom_iff_natCard_fiber_obj_eq_one`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

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
