/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Ring.PUnit
public import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.RationalCompletion
public import TauCeti.RingTheory.Huber.Padic.Field
public import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Checks for `IsRationalCompletion` and simple Laurent surjectivity

* Degenerate denominator `0`: `PUnit` models `A⟨{1}/0⟩`, and any model of `A⟨{1}/0⟩` is a
  subsingleton.
* Concrete denominator `1`: for every prime `p`, `ℚ_[p]` itself models `ℚ_[p]⟨{p, 1}/1⟩`.
* Sign and surjectivity check: at `f = 1`, `IsRationalCompletion.surjective_algebraMap_sub_laurent`
  on `B₁ = B₂ = B₁₂ = ℚ_[p]` gives surjectivity of `(x, y) ↦ x - y : ℚ_[p] × ℚ_[p] → ℚ_[p]`.
* Non-example: `ℚ_[p] × ℚ_[p]` is *not* a model of `ℚ_[p]⟨{1}/1⟩`, because its two projections to
  `ℚ_[p]` are distinct continuous `ℚ_[p]`-algebra homomorphisms.
-/

public section

namespace TauCeti.Huber.RationalCompletionChecks

/-- **Degenerate denominator `0`**: `PUnit` is a model of `A⟨{1}/0⟩`. -/
example {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) :
    IsRationalCompletion P {1} 0 (isOpen_span_of_one_mem (by simp)) PUnit :=
  isRationalCompletion_of_subsingleton_denom_zero P {1} _ PUnit

/-- **Degenerate denominator `0`**: conversely, every model of `A⟨{1}/0⟩` is a subsingleton. -/
example {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (P : PairOfDefinition A)
    {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra A B]
    (h : IsRationalCompletion P {1} 0 (isOpen_span_of_one_mem (by simp)) B) :
    Subsingleton B :=
  h.subsingleton_of_denom_zero

section Padic

variable (p : ℕ) [Fact p.Prime]

open Classical in
/-- **Concrete model at denominator `1`**: `ℚ_[p]` itself models `ℚ_[p]⟨{p, 1}/1⟩`. -/
example :
    let P := (IsHuberRing.nonempty_pairOfDefinition (A := ℚ_[p])).some
    IsRationalCompletion P {(p : ℚ_[p]), 1} 1
      (isOpen_span_of_one_mem (by simp)) ℚ_[p] := by
  let P := (IsHuberRing.nonempty_pairOfDefinition (A := ℚ_[p])).some
  refine isRationalCompletion_self_denom_one P {(p : ℚ_[p]), 1} _ fun t ht ↦ ?_
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact P.isBounded_ringOfDefinition.isPowerBounded_of_mem (natCast_mem _ p)
  · exact Finset.mem_singleton.mp ht ▸ isPowerBounded_one

/-- **Sign check on Laurent surjectivity**: at `f = 1`, `B₁ = B₂ = B₁₂ = ℚ_[p]` all model their
respective rational completions, and `surjective_algebraMap_sub_laurent` recovers surjectivity of
`(x, y) ↦ x - y` on `ℚ_[p]`. -/
example : Function.Surjective fun x : ℚ_[p] × ℚ_[p] ↦ x.1 - x.2 := by
  classical
  let P := (IsHuberRing.nonempty_pairOfDefinition (A := ℚ_[p])).some
  have mk : ∀ {T : Finset ℚ_[p]} (h1 : (1 : ℚ_[p]) ∈ T), (∀ t ∈ T, t = 1) →
      IsRationalCompletion P T 1
        (isOpen_span_of_one_mem (Finset.mem_coe.mpr h1)) ℚ_[p] :=
    fun _ hT ↦ isRationalCompletion_self_denom_one _ _ _ fun t ht ↦ hT t ht ▸ isPowerBounded_one
  exact (mk (T := {(1 : ℚ_[p]), 1}) (by simp) (by simp)).surjective_algebraMap_sub_laurent
    (mk (T := {1}) (by simp) (by simp)) (mk (T := {(1 : ℚ_[p]) * 1, 1}) (by simp) (by simp))
    continuous_id continuous_id

/-- **Non-example**: `ℚ_[p] × ℚ_[p]` is not a model of `ℚ_[p]⟨{1}/1⟩`, since its two coordinate
projections are distinct continuous `ℚ_[p]`-algebra homomorphisms into `ℚ_[p]`. -/
example :
    let P := (IsHuberRing.nonempty_pairOfDefinition (A := ℚ_[p])).some
    ¬ IsRationalCompletion P {1} 1 (isOpen_span_of_one_mem (by simp))
      (ℚ_[p] × ℚ_[p]) := fun h ↦
  one_ne_zero (congrArg (fun φ : ℚ_[p] × ℚ_[p] →ₐ[ℚ_[p]] ℚ_[p] ↦ φ (1, 0))
    (h.algHom_ext_of_continuous (f := AlgHom.fst ℚ_[p] ℚ_[p] ℚ_[p])
      (g := AlgHom.snd ℚ_[p] ℚ_[p] ℚ_[p]) continuous_fst continuous_snd))

end Padic

end TauCeti.Huber.RationalCompletionChecks

end
