/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import TauCeti.RingTheory.Localization.Colon

/-!
# Colon ideal sheaves

If the denominator ideal sheaf has finitely generated ideals on affine opens, the colon ideals
commute with basic-open restriction and define an ideal sheaf. This construction requires no
Noetherian hypothesis on the ambient scheme.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}}

/-- The colon ideal sheaf `(D : E)`, for an ideal sheaf `E` of finite type. -/
@[expose] noncomputable def colon (D E : X.IdealSheafData) (hE : ∀ U, (E.ideal U).FG) :
    X.IdealSheafData where
  ideal U := (D.ideal U).colon (E.ideal U : Set Γ(X, U))
  map_ideal_basicOpen U f := by
    have := U.2.isLocalization_basicOpen f
    rw [← D.map_ideal_basicOpen, ← E.map_ideal_basicOpen]
    exact Ideal.map_colon_of_isLocalization (Submonoid.powers f) _ _ (hE U)

/-- On an affine open, the colon ideal sheaf is the colon of the section ideals. -/
@[simp]
theorem ideal_colon (D E : X.IdealSheafData) (hE : ∀ U, (E.ideal U).FG)
    (U : X.affineOpens) :
    (D.colon E hE).ideal U = (D.ideal U).colon (E.ideal U : Set Γ(X, U)) := rfl

end AlgebraicGeometry.Scheme.IdealSheafData
