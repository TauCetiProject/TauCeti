/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
import Mathlib.RingTheory.Etale.Descent

/-!
# Smoothness of closed subgroups under faithfully flat base change

A closed subgroup cut out by a Hopf ideal `J` is smooth exactly when the closed subgroup cut out
by its base change `J_K` along a faithfully flat extension `k → K` is smooth. The coordinate
quotient of `J_K` is identified with the base change of the coordinate quotient of `J` by
`CommHopfAlgCat.quotientBaseChangeIso`. Smoothness is preserved by base change, and descends
along the faithfully flat extension by Mathlib's
`Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`.

## Main declarations

* `TauCeti.smoothCommHopfAlgProperty_quotient_baseChange_iff`: smoothness of a closed subgroup is
  equivalent to smoothness of its faithfully flat base change.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

variable {k : Type u} {K : Type w} [CommRing k] [CommRing K] [Algebra k K]
variable {H : _root_.CommHopfAlgCat.{v} k}

/-- Along a faithfully flat extension `k → K`, the closed subgroup cut out by a Hopf ideal `J` is
smooth exactly when the closed subgroup cut out by its base change `J_K` is smooth. -/
theorem smoothCommHopfAlgProperty_quotient_baseChange_iff [Module.FaithfullyFlat k K]
    (J : HopfIdeal k H) :
    smoothCommHopfAlgProperty K
        (CommHopfAlgCat.quotient (CommHopfAlgCat.baseChange (K := K) H)
          (CommHopfAlgCat.baseChangeHopfIdeal (K := K) J)) ↔
      smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H J) := by
  let qIso := CommHopfAlgCat.quotientBaseChangeIso (K := K) J
  constructor
  · intro hJ
    have hsmooth := (smoothCommHopfAlgProperty K).prop_of_iso qIso hJ
    let _ : Algebra.Smooth K
        (CommHopfAlgCat.baseChange (K := K) (CommHopfAlgCat.quotient H J)) :=
      (smoothCommHopfAlgProperty_iff _).mp hsmooth
    rw [smoothCommHopfAlgProperty_iff]
    exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K
  · intro hJ
    apply (smoothCommHopfAlgProperty K).prop_of_iso qIso.symm
    let _ : Algebra.Smooth k (CommHopfAlgCat.quotient H J) :=
      (smoothCommHopfAlgProperty_iff _).mp hJ
    exact (smoothCommHopfAlgProperty_iff _).mpr inferInstance

end TauCeti
