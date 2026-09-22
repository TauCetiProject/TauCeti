/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.RingTheory.Henselian.Basic

/-!
# Henselianity of nonarchimedean local fields

The integer ring of a nonarchimedean local field is complete for the topology of its maximal
ideal, and is therefore a Henselian local ring.

## Main results

* `TauCeti.henselianLocalRing_integer`: the integer ring of a nonarchimedean local field is a
  Henselian local ring.
-/

public section

open IsLocalRing ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The integer ring of a nonarchimedean local field is a Henselian local ring: it is local and
complete for the topology of its maximal ideal. -/
instance henselianLocalRing_integer : HenselianLocalRing 𝒪[K] where
  is_henselian := by
    let _ := IsTopologicalAddGroup.rightUniformSpace K
    let _ := isUniformAddGroup_of_addCommGroup (G := K)
    exact IsAdicComplete.henselianLocalRing 𝒪[K] |>.is_henselian

end TauCeti
