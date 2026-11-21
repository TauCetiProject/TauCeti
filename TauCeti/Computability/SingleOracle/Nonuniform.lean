/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Evaln
public import TauCeti.Computability.TuringDegree

/-!
# A pointwise computable family of set-oracle functions with no uniform program

Being computable relative to every oracle does not make a family of functions computable by one
program for every oracle: `∀ Z, ∃ c` does not become `∃ c, ∀ Z`. A witness is the **emptiness
indicator** `Z.emptinessIndicator`, the constant function with value `1` when `Z = ∅` and `0`
otherwise. For each fixed `Z` it is a constant function, computed relative to `Z.oracle` by a
query-free program. No single program computes it relative to `Z.oracle` for every `Z`, not even
at one fixed input. The obstruction is the use principle [S, III.1]: a run that succeeds against
the empty oracle has a finite use `u`, and the singleton `{u}` has the same members as `∅` below
`u`. So the program has the same output relative to `{u}.oracle`, but the prescribed values on `∅`
and on `{u}` are `1` and `0`.

## Main definitions

* `Set.emptinessIndicator`: the constant function `1` on the empty set and `0` on every nonempty
  set.

## Main results

* `TauCeti.Oracle.Single.Code.mem_eval_oracle_of_evaln_setAnswers_eq_some`: the **use principle
  for set oracles**, a successful run against the answers of `A` computes its output relative to
  the oracle of every set with the same members as `A` below the use.
* `TauCeti.Oracle.Single.Code.exists_eval_oracle_eq_emptinessIndicator`: for each set `Z`, some
  program computes `Z.emptinessIndicator` relative to `Z.oracle`.
* `TauCeti.Oracle.Single.Code.not_exists_forall_eval_oracle_apply_eq_emptinessIndicator`: at any
  fixed input, no single program computes the emptiness indicator relative to every set oracle.
* `TauCeti.Oracle.Single.Code.not_exists_forall_eval_oracle_eq_emptinessIndicator`: no single
  program computes the emptiness indicator uniformly in the set oracle.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.1.
-/

public section

namespace Set

open Classical in
/-- The **emptiness indicator** of a set `Z` of naturals: the constant function with value `1`
when `Z` is empty and `0` otherwise. -/
noncomputable def emptinessIndicator (Z : Set ℕ) : ℕ → ℕ :=
  fun _ => if Z = ∅ then 1 else 0

open Classical in
/-- The value of the emptiness indicator, at every input. -/
theorem emptinessIndicator_apply (Z : Set ℕ) (x : ℕ) :
    Z.emptinessIndicator x = if Z = ∅ then 1 else 0 :=
  (rfl)

/-- The emptiness indicator of the empty set is constantly `1`. -/
@[simp]
theorem emptinessIndicator_empty (x : ℕ) : (∅ : Set ℕ).emptinessIndicator x = 1 := by
  simp [emptinessIndicator_apply]

/-- The emptiness indicator of a nonempty set is constantly `0`. -/
theorem Nonempty.emptinessIndicator_eq_zero {Z : Set ℕ} (hZ : Z.Nonempty) (x : ℕ) :
    Z.emptinessIndicator x = 0 := by
  simp [emptinessIndicator_apply, hZ.ne_empty]

/-- The emptiness indicator of a singleton is constantly `0`. -/
@[simp]
theorem emptinessIndicator_singleton (u x : ℕ) : ({u} : Set ℕ).emptinessIndicator x = 0 :=
  (singleton_nonempty u).emptinessIndicator_eq_zero x

end Set

namespace TauCeti.Oracle.Single.Code

variable {k n : ℕ} {c : Code} {d : Halt}

/-- **The use principle for set oracles.** If a run against the answers of a set `A` succeeds,
its output is a value of the program relative to the oracle of every set `B` with the same members
as `A` below the use of the run. -/
theorem mem_eval_oracle_of_evaln_setAnswers_eq_some {A B : Set ℕ}
    (h : evaln (setAnswers A) k c n = some d) (hAB : ∀ z < d.use, (z ∈ A ↔ z ∈ B)) :
    d.output ∈ eval B.oracle c n :=
  evaln_sound (evaln_eq_some_of_eqOn h (eqOn_setAnswers_iff.2 hAB)) (by simp)

/-- **Pointwise computability.** For each set `Z`, the emptiness indicator of `Z` is computed
relative to `Z.oracle` by a program: the query-free program of the constant function with the
value of `Z.emptinessIndicator`. The program depends on `Z`. -/
theorem exists_eval_oracle_eq_emptinessIndicator (Z : Set ℕ) :
    ∃ c : Code, ∀ x, eval Z.oracle c x = Part.some (Z.emptinessIndicator x) := by
  refine ⟨(Nat.Partrec.Code.const (Z.emptinessIndicator 0)).toSingleOracleCode, fun x => ?_⟩
  rw [eval_toSingleOracleCode, Nat.Partrec.Code.eval_const]
  simp only [Set.emptinessIndicator_apply]

/-- **No uniform program, already at one input.** For each input `x`, no single program computes
the emptiness indicator at `x` relative to every set oracle. A run computing the value `1` against
the empty oracle has a finite use `u`, and `{u}` agrees with `∅` below `u`, so the program also
outputs `1` relative to `{u}.oracle`, where the prescribed value is `0`. -/
theorem not_exists_forall_eval_oracle_apply_eq_emptinessIndicator (x : ℕ) :
    ¬∃ c : Code, ∀ Z : Set ℕ, eval Z.oracle c x = Part.some (Z.emptinessIndicator x) := by
  rintro ⟨c, hc⟩
  -- a successful run against the empty oracle, with output `1` and use `u`
  have h₁ : 1 ∈ eval (∅ : Set ℕ).oracle c x := by
    rw [hc ∅, Set.emptinessIndicator_empty]
    exact Part.mem_some 1
  obtain ⟨k, d, hd, hout⟩ := exists_evaln_eq_some_of_mem_eval (σ := setAnswers ∅) (by simp) h₁
  -- the singleton `{u}` has the same members as `∅` below `u`
  have hagree : ∀ z < d.use, (z ∈ (∅ : Set ℕ) ↔ z ∈ ({d.use} : Set ℕ)) := fun z hz => by
    simp [hz.ne]
  have h₀ := mem_eval_oracle_of_evaln_setAnswers_eq_some hd hagree
  rw [hc {d.use}, hout, Set.emptinessIndicator_singleton, Part.mem_some_iff] at h₀
  exact one_ne_zero h₀

/-- **No uniform program.** No single program computes the emptiness indicator of `Z` relative to
`Z.oracle` for every set `Z`, although for each `Z` some program does
(`exists_eval_oracle_eq_emptinessIndicator`). -/
theorem not_exists_forall_eval_oracle_eq_emptinessIndicator :
    ¬∃ c : Code, ∀ Z : Set ℕ, ∀ x, eval Z.oracle c x = Part.some (Z.emptinessIndicator x) :=
  fun ⟨c, hc⟩ => not_exists_forall_eval_oracle_apply_eq_emptinessIndicator 0 ⟨c, fun Z => hc Z 0⟩

end TauCeti.Oracle.Single.Code
