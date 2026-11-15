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
* `TauCeti.AlgebraicGeometry.LineBundleClass.eulerCharBelow`: the truncated Euler characteristic
  descended to line-bundle classes, with `LineBundleClass.eulerCharBelow_mk` and
  `LineBundleClass.eulerCharBelow_one`.
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

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The truncated Euler characteristic `Σ_{i<n} (−1)ⁱ dim_k Hⁱ` of a line-bundle class, descended
from `Scheme.Modules.eulerCharBelow`. -/
noncomputable def eulerCharBelow (a : LineBundleClass X) (n : ℕ) : ℤ :=
  lift (fun L ↦ Scheme.Modules.eulerCharBelow k X L.obj n)
    (fun _ _ h ↦ InvertibleSheaf.eulerCharBelow_eq_of_mk_eq k (mk_eq_mk_iff.2 h) n) a

@[simp]
lemma eulerCharBelow_mk (L : InvertibleSheaf X) (n : ℕ) :
    eulerCharBelow k (mk L) n = Scheme.Modules.eulerCharBelow k X L.obj n :=
  lift_mk L

@[simp]
lemma eulerCharBelow_one (n : ℕ) :
    eulerCharBelow k (1 : LineBundleClass X) n =
      Scheme.Modules.eulerCharBelow k X (InvertibleSheaf.trivial X).obj n := by
  rw [← mk_trivial, eulerCharBelow_mk]

end TauCeti.AlgebraicGeometry.LineBundleClass
