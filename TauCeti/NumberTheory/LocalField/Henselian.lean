/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.RingTheory.AdicCompletion.Pow
public import TauCeti.RingTheory.Henselian.Basic

/-!
# Henselianity of nonarchimedean local fields

The integer ring of a nonarchimedean local field is complete for the topology of its maximal
ideal, and is therefore a Henselian local ring. It is also complete for the adic topology of every
positive power `𝓂[K] ^ (n + 1)` of the maximal ideal, which defines the same topology, and is
therefore Henselian at each of them: a simple approximate root modulo `𝓂[K] ^ (n + 1)` lifts to a
root congruent to it modulo `𝓂[K] ^ (n + 1)`.

## Main results

* `TauCeti.henselianLocalRing_integer`: the integer ring of a nonarchimedean local field is a
  Henselian local ring.
* `TauCeti.isAdicComplete_maximalIdeal_pow_succ`: the integer ring is complete for the adic
  topology of each positive power of its maximal ideal, hence Henselian at it through Mathlib's
  `IsAdicComplete.henselianRing`.
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

/-- The integer ring of a nonarchimedean local field is complete for the adic topology of every
positive power of its maximal ideal. Mathlib records the completeness at `𝓂[K]` itself for the
uniformity attached to the topological additive group `K`; the powers follow because the
`𝓂[K] ^ (n + 1)`-adic filtration is cofinal in the `𝓂[K]`-adic one. -/
instance isAdicComplete_maximalIdeal_pow_succ (n : ℕ) :
    IsAdicComplete (𝓂[K] ^ (n + 1)) 𝒪[K] := by
  let _ := IsTopologicalAddGroup.rightUniformSpace K
  let _ := isUniformAddGroup_of_addCommGroup (G := K)
  exact IsAdicComplete.pow n.succ_ne_zero

end TauCeti
