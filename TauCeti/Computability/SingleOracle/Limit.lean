/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Evaln
public import TauCeti.Computability.Enumeration.Converges

/-!
# Oracle computations along approximations of the oracle

A construction in stages computes against a moving oracle: at stage `s` it runs a program against
the answers `σs s` of the current approximation, rather than against the limit oracle `σ`. This
file relates these stage computations to computations against the limit, in both directions.

**From the limit to the stages.** When the answers converge pointwise, `σs s z = σ z` for all
large `s` at each address `z`, a successful run against the limit is eventually a successful run,
with the same output and use, against every approximation. The run reads only the finitely many
addresses below its use, and these are simultaneously correct from some stage on. Combined with
completeness of bounded evaluation, every value of a program relative to the limit oracle is
eventually found by the stage computations with growing fuel. For a set enumerated in monotone
finite stages, the set-oracle answers of the stages converge to those of the limit set, so this
applies to the stage computations `Φ_{e,s}^{A_s}(x)`
(`TauCeti.Enumeration.converges_indicator_stageLimit`).

**From the stages to the limit.** The converse fails without further information: a stage
computation may read an address whose answer later changes. It holds when nothing enters the
enumeration below the use after the stage of the computation. Then the computation persists, with
the same output and use, at every later stage and against the limit set. The priority-method
consequences, for requirements that are not injured, are in
`TauCeti.Computability.Priority.Preservation`.

## Main results

* `TauCeti.Oracle.Single.Code.eventually_evaln_eq_some_of_converges`: a successful run against the
  limit of converging answers is eventually a successful run against the approximations, with the
  same output and use.
* `TauCeti.Oracle.Single.Code.exists_eventually_evaln_eq_some_of_mem_eval`: every value of a
  program relative to the limit oracle is eventually found by the stage computations, with fuel
  growing along any clock tending to infinity.
* `TauCeti.Oracle.Single.Code.exists_eventually_evaln_indicator_eq_some_of_mem_eval`: a
  convergent computation relative to the limit of a monotone enumeration is eventually found by
  the stage computations against the finite stages.
* `TauCeti.Oracle.Single.Code.evaln_indicator_eq_some_of_forall_notMem_fresh`,
  `TauCeti.Oracle.Single.Code.evaln_indicator_stageLimit_eq_some_of_forall_notMem_fresh`:
  **preservation**, a stage computation below whose use nothing enters persists at every later
  stage and against the limit set.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters III.1 and VII.1.
-/

public section

open Filter TauCeti.Approximation TauCeti.Enumeration

namespace TauCeti

namespace Oracle.Single.Code

variable {σs : ℕ → ℕ → Option ℕ} {σ : ℕ → Option ℕ} {k n : ℕ} {c : Code} {d : Halt}

/-! ### From the limit oracle to the approximations -/

/-- **Eventual visibility.** If the answers `σs s` converge pointwise to `σ`, a successful run
against `σ` is, from some stage on, a successful run with the same fuel, output and use against
`σs s`. -/
theorem eventually_evaln_eq_some_of_converges (hσ : Converges σs σ)
    (h : evaln σ k c n = some d) : ∀ᶠ s in atTop, evaln (σs s) k c n = some d :=
  (hσ.eventually_forall_mem (Finset.range d.use)).mono fun _ hs =>
    evaln_eq_some_of_eqOn h fun z hz => (hs z (Finset.mem_range.2 hz)).symm

/-- **Eventual visibility with growing fuel.** If the answers `σs s` converge pointwise to `σ`, a
successful run against `σ` is, from some stage on, a successful run with the same output and use
against `σs s` with fuel `t s`, for any clock `t` tending to infinity. -/
theorem eventually_evaln_eq_some_of_converges_of_tendsto (hσ : Converges σs σ) {t : ℕ → ℕ}
    (ht : Tendsto t atTop atTop) (h : evaln σ k c n = some d) :
    ∀ᶠ s in atTop, evaln (σs s) (t s) c n = some d :=
  ((eventually_evaln_eq_some_of_converges hσ h).and (ht.eventually_ge_atTop k)).mono
    fun _ hs => evaln_mono hs.2 hs.1

/-- **Stage computations find every limit value.** Suppose the answers `σs s` converge pointwise to
answers `σ` that give every value of the oracle `O`. Every value `y` of a program relative to `O`
is the output of a single run, with a fixed use, that from some stage on succeeds against `σs s`
with fuel `t s`, for any clock `t` tending to infinity. -/
theorem exists_eventually_evaln_eq_some_of_mem_eval {O : ℕ →. ℕ}
    (hO : ∀ z y, y ∈ O z → σ z = some y) (hσ : Converges σs σ) {t : ℕ → ℕ}
    (ht : Tendsto t atTop atTop) {y : ℕ} (h : y ∈ eval O c n) :
    ∃ d : Halt, d.output = y ∧ ∀ᶠ s in atTop, evaln (σs s) (t s) c n = some d := by
  obtain ⟨k, d, hd, rfl⟩ := exists_evaln_eq_some_of_mem_eval hO h
  exact ⟨d, rfl, eventually_evaln_eq_some_of_converges_of_tendsto hσ ht hd⟩

variable {A : ℕ → Finset ℕ}

/-- **Stage computations against a monotone enumeration.** If a program relative to the set oracle
of the limit of monotone finite stages `A s` has the value `y`, then a single run with output `y`
and a fixed use succeeds, from some stage on, against the set oracle of `A s` with fuel `t s`, for
any clock `t` tending to infinity. -/
theorem exists_eventually_evaln_indicator_eq_some_of_mem_eval (hA : Monotone A) {t : ℕ → ℕ}
    (ht : Tendsto t atTop atTop) {y : ℕ}
    (h : y ∈ eval (fun z => Part.some ((stageLimit A).indicator 1 z)) c n) :
    ∃ d : Halt, d.output = y ∧
      ∀ᶠ s in atTop, evaln (fun z => some ((A s : Set ℕ).indicator 1 z)) (t s) c n = some d :=
  exists_eventually_evaln_eq_some_of_mem_eval (σ := fun z => some ((stageLimit A).indicator 1 z))
    (by simp) (converges_iff_eventually.2 fun z =>
      (converges_iff_eventually.1 (converges_indicator_stageLimit hA 1) z).mono fun _ hs => by
        rw [hs]) ht h

/-! ### From the approximations to the limit oracle -/

variable {s : ℕ}

/-- **Preservation at later stages.** Under monotone stages, if a run against the set oracle of
`A s` succeeds and no number below its use enters after stage `s`, then it succeeds with the same
output and use against the set oracle of every later stage. -/
theorem evaln_indicator_eq_some_of_forall_notMem_fresh (hA : Monotone A)
    (h : evaln (fun z => some ((A s : Set ℕ).indicator 1 z)) k c n = some d)
    (hfresh : ∀ t, s ≤ t → ∀ z, z < d.use → z ∉ fresh A t) {t : ℕ} (hst : s ≤ t) :
    evaln (fun z => some ((A t : Set ℕ).indicator 1 z)) k c n = some d :=
  evaln_eq_some_of_eqOn h fun z hz => by
    -- below the use, `A s ⊆ A t ⊆ stageLimit A` and the outer two agree
    have hlim := limit_agrees_of_no_fresh_below hA hfresh z hz
    exact congrArg some <| Set.indicator_eq_indicator
      ⟨fun hzs => hA hst hzs, fun hzt => hlim.2 (subset_stageLimit A t hzt)⟩ rfl

/-- **Preservation in the limit.** Under monotone stages, if a run against the set oracle of `A s`
succeeds and no number below its use enters after stage `s`, then it succeeds with the same output
and use against the set oracle of the limit. -/
theorem evaln_indicator_stageLimit_eq_some_of_forall_notMem_fresh (hA : Monotone A)
    (h : evaln (fun z => some ((A s : Set ℕ).indicator 1 z)) k c n = some d)
    (hfresh : ∀ t, s ≤ t → ∀ z, z < d.use → z ∉ fresh A t) :
    evaln (fun z => some ((stageLimit A).indicator 1 z)) k c n = some d :=
  evaln_eq_some_of_eqOn h fun z hz => congrArg some <|
    Set.indicator_eq_indicator (limit_agrees_of_no_fresh_below hA hfresh z hz) rfl

end Oracle.Single.Code

end TauCeti
