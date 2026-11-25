/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.CoefficientChange

/-!
# Examples for change of coefficients of smooth representations

Base change along the identity is naturally the identity functor, and the unit of the base change
adjunction sends `v` to `1 ⊗ v`.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti

variable {A B G : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G]

/-- Base change along the identity is naturally the identity functor. -/
noncomputable example : (SmoothRep.extendScalars A : SmoothRep.{0} A G ⥤ SmoothRep.{0} A G) ≅ 𝟭 _ :=
  SmoothRep.extendScalarsId A

/-- The unit of `extendScalars B ⊣ restrictScalars A` sends `v` to `1 ⊗ v`. -/
example (V : SmoothRep.{0} A G) (v : V.obj) :
    ((SmoothRep.extendRestrictScalarsAdj A B).unit.app V).hom.hom v = (1 : B) ⊗ₜ[A] v := by
  rw [SmoothRep.extendRestrictScalarsAdj_unit_app_hom,
    Rep.extendRestrictScalarsAdj_unit_app_hom_apply]

end TauCeti
