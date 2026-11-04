/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.WittVector.Primitive.Quotient

/-!
# Checks for the quotient of the Witt vectors by a distinguished element

Let `S` be a perfect ring of characteristic `p`.

* For `ξ = p`, whose zeroth Witt coordinate is `0`, the quotient `𝕎 S ⧸ (p)` is `[ϖ]`-adically
  and `p`-adically complete whenever `S` is `ϖ`-adically complete, and the reduction modulo `[ϖ]`
  sends the class of `[a] + p x` to the class of `a`: the Witt coordinates above the zeroth one
  are forgotten.
* For `ϖ = 1` the reduction is the zero ring.
* For the nonzerodivisor `ϖ = 1`, the ideal `(p)` of the localization `𝕎 S [1/[1]] = 𝕎 S`
  contracts to `(p)`.
-/

open Ideal WittVector

namespace TauCeti.Examples

variable {p : ℕ} [hp : Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

-- `𝕎 S ⧸ (p)` is `[ϖ]`-adically complete when `S` is `ϖ`-adically complete.
example (ϖ : S) [IsAdicComplete (span {ϖ}) S] :
    IsAdicComplete (span {Ideal.Quotient.mk (span {(p : WittVector p S)}) (teichmuller p ϖ)})
      (WittVector p S ⧸ span {(p : WittVector p S)}) :=
  isDistinguished_p.isAdicComplete_quotient (by simp)

-- `𝕎 S ⧸ (p)` is also `p`-adically complete.
example (ϖ : S) [IsAdicComplete (span {ϖ}) S] :
    IsAdicComplete (span {(p : WittVector p S ⧸ span {(p : WittVector p S)})})
      (WittVector p S ⧸ span {(p : WittVector p S)}) :=
  isDistinguished_p.isAdicComplete_quotient_natCast (ϖ := ϖ) (by simp)

-- Computation: modulo `(p, [ϖ])`, the class of `[a] + p x` is the class of `a`.
example (ϖ a : S) (x : WittVector p S) :
    isDistinguished_p.quotientTeichmullerEquiv (ϖ := ϖ) (by simp)
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (teichmuller p a + p * x))) =
      Ideal.Quotient.mk _ a := by
  simp [← map_natCast (Ideal.Quotient.mk (span {ϖ})) p]

-- Degenerate case: for `ϖ = 1` the reduction modulo `[1] = 1` is the zero ring.
example : Subsingleton ((WittVector p S ⧸ span {(p : WittVector p S)}) ⧸
    span {Ideal.Quotient.mk (span {(p : WittVector p S)}) (teichmuller p (1 : S))}) := by
  have e := isDistinguished_p.quotientTeichmullerEquiv (S := S) (ϖ := 1) (by simp)
  have : Subsingleton (S ⧸ span {(1 : S)}) := by
    rw [span_singleton_one]
    infer_instance
  exact e.toEquiv.subsingleton

-- Degenerate case: localizing at `[1] = 1` changes nothing, and `(p)` contracts to itself.
example : ((span {(p : WittVector p S)}).map (algebraMap (WittVector p S) (WittVector p S))).comap
    (algebraMap (WittVector p S) (WittVector p S)) = span {(p : WittVector p S)} :=
  haveI : IsLocalization.Away (teichmuller p (1 : S)) (WittVector p S) := by
    rw [map_one]
    exact IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id
  isDistinguished_p.comap_map_algebraMap (by simp) (one_mem _) _

end TauCeti.Examples
