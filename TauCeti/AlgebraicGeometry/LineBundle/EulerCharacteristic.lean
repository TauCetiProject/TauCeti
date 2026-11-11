/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.LineBundle.Class

/-!
# Euler characteristics of line-bundle classes

The truncated Euler characteristic `Scheme.Modules.eulerCharBelow` of an invertible sheaf only
depends on its class in the Picard group `LineBundleClass X`.

## Main results

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerCharBelow_eq_of_mk_eq`: invertible sheaves with
  the same class in the Picard group have the same truncated Euler characteristic.
-/

public section

open AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Invertible sheaves with the same class in the Picard group have the same truncated Euler
characteristic. -/
lemma eulerCharBelow_eq_of_mk_eq {L L' : InvertibleSheaf X}
    (h : LineBundleClass.mk L = LineBundleClass.mk L') (n : ℕ) :
    Scheme.Modules.eulerCharBelow k X L.obj n = Scheme.Modules.eulerCharBelow k X L'.obj n := by
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.1 h
  exact Scheme.Modules.eulerCharBelow_congr k e n

end TauCeti.AlgebraicGeometry.InvertibleSheaf
