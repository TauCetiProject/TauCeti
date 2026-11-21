/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.LocalRing.HilbertSamuel.Basic
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.Length

/-!
# Completion invariance of the local Hilbert–Samuel function

Whenever the maximal ideal `𝔪` of a commutative local ring `A` is finitely generated (in
particular, when `A` is Noetherian), the `𝔪`-adic completion `Â = AdicCompletion 𝔪 A` has the
same reductions modulo powers of the maximal ideal, so extending an ideal `I` to `Â` preserves
every value of `I.hilbertSamuel` (`Ideal.hilbertSamuel_map_adicCompletion_of_fg`,
`Ideal.hilbertSamuel_map_adicCompletion`).

## Main results

* `Ideal.hilbertSamuel_map_adicCompletion_of_fg`, `Ideal.hilbertSamuel_map_adicCompletion`,
  `Ideal.hilbertSamuel_adicCompletion_bot_of_fg`, `Ideal.hilbertSamuel_adicCompletion_bot`:
  invariance of `Ideal.hilbertSamuel` under maximal-adic completion.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Remarks 1.3 (pp. 213–214).
-/

public section

namespace Ideal

open IsLocalRing

section Completion

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- Extending an ideal to the maximal-adic completion preserves every value of the Hilbert–Samuel
function whenever the maximal ideal is finitely generated. -/
theorem hilbertSamuel_map_adicCompletion_of_fg (hfg : (maximalIdeal A).FG) (I : Ideal A) (n : ℕ) :
    haveI := AdicCompletion.isLocalRing_of_fg hfg
    (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))).hilbertSamuel n =
      I.hilbertSamuel n := by
  have := AdicCompletion.isLocalRing_of_fg hfg
  set 𝔪 := maximalIdeal A
  set Â := AdicCompletion 𝔪 A
  have hq_surj : Function.Surjective (AdicCompletion.evalₐ 𝔪 (n + 1)) :=
    AdicCompletion.surjective_evalₐ 𝔪 (n + 1)
  have hq_ker : RingHom.ker (AdicCompletion.evalₐ 𝔪 (n + 1)) = maximalIdeal Â ^ (n + 1) := by
    rw [AdicCompletion.ker_evalₐ_eq_map_pow hfg (n + 1), Ideal.map_pow,
      AdicCompletion.maximalIdeal_eq_map_of_fg hfg]
  have hcomp :
      (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom.comp (algebraMap A Â) =
        Ideal.Quotient.mk (𝔪 ^ (n + 1)) := by
    ext x
    exact AdicCompletion.evalₐ_of 𝔪 (n + 1) x
  rw [hilbertSamuel_def, ← hq_ker,
    ← Ideal.length_quotient_map_of_surjective (I.map (algebraMap A Â)) hq_surj,
    ← Ideal.map_coe, Ideal.map_map, ← AlgHom.toRingHom_eq_coe, hcomp,
    Ideal.length_quotient_map_of_surjective I Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, ← hilbertSamuel_def]

/-- The maximal-adic completion of a local ring with finitely generated maximal ideal has the same
Hilbert–Samuel function at `⊥` as the original ring. -/
theorem hilbertSamuel_adicCompletion_bot_of_fg (hfg : (maximalIdeal A).FG) (n : ℕ) :
    haveI := AdicCompletion.isLocalRing_of_fg hfg
    (⊥ : Ideal (AdicCompletion (maximalIdeal A) A)).hilbertSamuel n =
      (⊥ : Ideal A).hilbertSamuel n := by
  have := AdicCompletion.isLocalRing_of_fg hfg
  simpa using hilbertSamuel_map_adicCompletion_of_fg hfg ⊥ n

/-- Extending an ideal of a Noetherian local ring to its maximal-adic completion preserves every
value of the Hilbert–Samuel function. -/
@[simp]
theorem hilbertSamuel_map_adicCompletion [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))).hilbertSamuel n =
      I.hilbertSamuel n :=
  hilbertSamuel_map_adicCompletion_of_fg (IsNoetherian.noetherian _) I n

/-- The maximal-adic completion of a Noetherian local ring has the same Hilbert–Samuel function at
`⊥` as the original ring. -/
@[simp]
theorem hilbertSamuel_adicCompletion_bot [IsNoetherianRing A] (n : ℕ) :
    (⊥ : Ideal (AdicCompletion (maximalIdeal A) A)).hilbertSamuel n =
      (⊥ : Ideal A).hilbertSamuel n := by
  simpa using hilbertSamuel_map_adicCompletion (⊥ : Ideal A) n

end Completion

end Ideal
