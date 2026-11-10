/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.RingTheory.AdicCompletion.Pow
public import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.LocalRing.QuadraticDoubleRoot

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
* `TauCeti.henselianLocalRing_valuationSubring`: the same Henselian structure for the valuation
  subring used by valuation-based reduction APIs.
* `TauCeti.isAdicComplete_maximalIdeal_pow_succ`: the integer ring is complete for the adic
  topology of each positive power of its maximal ideal, hence Henselian at it through Mathlib's
  `IsAdicComplete.henselianRing`.
* `TauCeti.adjoin_eq_bot_of_sq_add_mul_add_eq_zero_of_isUnit`: a root in the separable closure of a
  quadratic `X ^ 2 + b X + c` with `b` a unit and `c` in the maximal ideal already lies in `K`.
-/

public section

open IsLocalRing ValuativeRel
open scoped IntermediateField

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

/-- The valuation subring of a nonarchimedean local field is Henselian. -/
instance henselianLocalRing_valuationSubring : HenselianLocalRing (valuation K).valuationSubring :=
  -- Mathlib defines `Valuation.valuationSubring` by extending `Valuation.integer`, so both
  -- presentations inherit the same ring structure on the same subtype.
  inferInstanceAs (HenselianLocalRing 𝒪[K])

/-- The integer ring of a nonarchimedean local field is complete for the adic topology of every
positive power of its maximal ideal. Mathlib records the completeness at `𝓂[K]` itself for the
uniformity attached to the topological additive group `K`; the powers follow because the
`𝓂[K] ^ (n + 1)`-adic filtration is cofinal in the `𝓂[K]`-adic one. -/
instance isAdicComplete_maximalIdeal_pow_succ (n : ℕ) :
    IsAdicComplete (𝓂[K] ^ (n + 1)) 𝒪[K] := by
  let _ := IsTopologicalAddGroup.rightUniformSpace K
  let _ := isUniformAddGroup_of_addCommGroup (G := K)
  exact IsAdicComplete.pow n.succ_ne_zero

variable {K}

/-- If `b` is a unit and `c` lies in the maximal ideal, a root in the separable closure of
`X ^ 2 + b X + c` already lies in `K`: the reduction `X (X + b)` has the simple root `0`, which
Hensel's lemma lifts to a root in `𝒪[K]`. -/
theorem adjoin_eq_bot_of_sq_add_mul_add_eq_zero_of_isUnit {b c : 𝒪[K]} (hb : IsUnit b)
    (hc : c ∈ 𝓂[K]) {x : SeparableClosure K}
    (hx : x ^ 2 + algebraMap K (SeparableClosure K) b * x +
      algebraMap K (SeparableClosure K) c = 0) :
    K⟮x⟯ = ⊥ := by
  have hd : IsUnit (b ^ 2 + 4 * -c) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro h
    have h4 : 4 * -c ∈ 𝓂[K] := Ideal.mul_mem_left _ _ (neg_mem hc)
    exact IsLocalRing.notMem_maximalIdeal.mpr (hb.pow 2) (by simpa using sub_mem h h4)
  obtain ⟨s, hs, -, -⟩ := HenselianLocalRing.exists_quadratic_root_of_isUnit_discriminant
    (a := b) (b := -c) (t := 0) hd (by simpa using hc)
  have hs' : algebraMap K (SeparableClosure K) s ^ 2 +
      algebraMap K (SeparableClosure K) b * algebraMap K (SeparableClosure K) s +
        algebraMap K (SeparableClosure K) c = 0 := by
    have := congrArg (fun y : 𝒪[K] ↦ algebraMap K (SeparableClosure K) (y : K)) hs
    simpa using this
  have hfac : (x - algebraMap K (SeparableClosure K) s) *
      (x + algebraMap K (SeparableClosure K) s + algebraMap K (SeparableClosure K) b) = 0 := by
    linear_combination hx - hs'
  rw [IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot]
  rcases mul_eq_zero.mp hfac with h | h
  · exact ⟨s, (sub_eq_zero.mp h).symm⟩
  · exact ⟨-(s : K) - b, by simp only [map_sub, map_neg]; linear_combination -h⟩

end TauCeti
