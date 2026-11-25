/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Priority.Preservation
public import TauCeti.Computability.SingleOracle.Stage

/-!
# Regression examples: what absence of injury preserves, and what it does not

These examples exercise the preservation theorems of `TauCeti.Computability.Priority.Preservation`
and the stage computations of `TauCeti.Computability.SingleOracle.Stage` from a downstream module,
through public statements of the library; only the stages and restraints defined here are
unfolded. The computations are runs of the `oracle` instruction, which
queries the oracle at its input `n` and has use `n + 1`.

* An entry at the exclusive use boundary injures under the conservative inclusive restraint, yet
  leaves the protected computation intact: the run at input `0` has use `1`, the restraint is
  `some 1`, and `1` enters. Nothing breaches the use prefix, so the run persists in the limit.
* One restraint covering two computations with different uses, `1` and `3`, preserves both when it
  is never injured. When `2` enters instead, between the two uses, only the run with the smaller
  use persists in the limit.
* Finite injury alone does not make an arbitrary restraint stabilize: under a restraint
  alternating between `none` and `some 0` nothing is ever injured, although every number enters.
* A stage computation against a fixed oracle persists at every later stage; one against a moving
  oracle can disappear: the computation found at a stage `m` against the empty stage is no longer
  a stage computation at stage `m + 1`, after `0` enters the enumeration.
* Without injury, a restraint that later drops does not preserve an earlier use it no longer
  covers: the restraint `some 0` protects the run at input `0` at stage `0` and is then lifted,
  after which `0` enters without injury and the run against the limit has another output.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters III.1 and VII.1.
-/

public section

open Filter TauCeti.Enumeration TauCeti.Priority TauCeti.Oracle.Single Code

namespace TauCeti.PreservationExample

/-! ### An entry at the use boundary -/

/-- The stages of the boundary example: `1` enters at stage `1`. -/
def boundaryStages (s : ℕ) : Finset ℕ :=
  if s = 0 then ∅ else {1}

/-- The stages of the boundary example are monotone. -/
theorem monotone_boundaryStages : Monotone boundaryStages := by
  intro s t hst
  simp only [boundaryStages]
  split_ifs <;> simp_all

-- At stage `0` the run at input `0` has output `0` and use `1`.
example : evaln (setAnswers ↑(boundaryStages 0)) 1 oracle 0 = some ⟨0, 1⟩ := by
  simp [boundaryStages]

-- Under the restraint `some 1`, equal to the use, the entry `1` injures ...
example :
    1 ∈ injurySet boundaryStages (fun _ _ => some 1) 0 :=
  mem_injurySet.2 ⟨0, by simp [boundaryStages]⟩

-- ... although it breaches no use prefix ...
example :
    injurySet boundaryStages (usePrefixRestraint fun _ _ => some 1) 0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨s, hs⟩ := mem_injurySet.1 hx
  simp only [mem_injuriesAt_usePrefixRestraint, boundaryStages] at hs
  split_ifs at hs <;> simp_all

-- ... so the run persists, with the same output and use, against the limit.
example :
    evaln (setAnswers (stageLimit boundaryStages)) 1 oracle 0 =
      some ⟨0, 1⟩ :=
  evaln_setAnswers_stageLimit_eq_some_of_injuriesAt_usePrefixRestraint_eq_empty
    (r := fun _ _ => some 1) (e := 0) (s := 0) monotone_boundaryStages (by simp [boundaryStages])
    (fun _ _ z hz => ⟨1, rfl, hz⟩) fun t _ => by
      ext x
      simp only [mem_injuriesAt_usePrefixRestraint, boundaryStages, Finset.notMem_empty, iff_false]
      split_ifs <;> simp_all

/-! ### Two computations with different uses -/

/-- The stages `[3, s + 3)`, where the numbers from `3` on enter one at a time, are monotone. -/
theorem monotone_Ico_three : Monotone fun s => Finset.Ico 3 (s + 3) :=
  fun _ _ hst => Finset.Ico_subset_Ico_right (by omega)

-- At stage `0` the runs at inputs `0` and `2` have uses `1` and `3`.
example :
    evaln (setAnswers ↑(Finset.Ico 3 (0 + 3))) 3 oracle 0 = some ⟨0, 1⟩ ∧
      evaln (setAnswers ↑(Finset.Ico 3 (0 + 3))) 3 oracle 2 = some ⟨0, 3⟩ := by
  simp

/-- The constant restraint `some 2`, covering both uses, is not injured at any stage. -/
theorem injuriesAt_Ico_three_eq_empty (t : ℕ) :
    injuriesAt (fun s => Finset.Ico 3 (s + 3)) (fun _ _ => some 2) 0 t = ∅ := by
  ext x
  simp only [mem_injuriesAt, Finset.mem_Ico, Option.some.injEq, Finset.notMem_empty, iff_false]
  omega

-- So both runs persist against the limit.
example :
    evaln (setAnswers (stageLimit fun s => Finset.Ico 3 (s + 3))) 3 oracle 0 = some ⟨0, 1⟩ ∧
      evaln (setAnswers (stageLimit fun s => Finset.Ico 3 (s + 3))) 3 oracle 2 =
        some ⟨0, 3⟩ := by
  -- A run against stage `0` with use at most `3` is covered by the restraint `some 2`.
  have h {n : ℕ} {d : Halt} (hd : evaln (setAnswers ↑(Finset.Ico 3 (0 + 3))) 3 oracle n = some d)
      (hu : d.use ≤ 3) : evaln (setAnswers (stageLimit fun s => Finset.Ico 3 (s + 3))) 3 oracle n =
        some d :=
    evaln_setAnswers_stageLimit_eq_some_of_injuriesAt_eq_empty monotone_Ico_three hd
      (fun _ _ z hz => ⟨2, rfl, by omega⟩) fun t _ => injuriesAt_Ico_three_eq_empty t
  exact ⟨h (by simp) (by simp), h (by simp) (by simp)⟩

-- When `2` enters instead, between the two uses, the run with use `1` persists against the limit
-- while the run with use `3` changes its output.
example :
    evaln (setAnswers (stageLimit fun s => if s = 0 then ∅ else {2})) 1 oracle 0 = some ⟨0, 1⟩ ∧
      evaln (setAnswers (stageLimit fun s => if s = 0 then ∅ else {2})) 3 oracle 2 =
        some ⟨1, 3⟩ := by
  have h0 : 0 ∉ stageLimit fun s => if s = 0 then (∅ : Finset ℕ) else {2} := by
    simp only [mem_stageLimit, not_exists]
    intro s
    split_ifs <;> simp
  have h2 : 2 ∈ stageLimit fun s => if s = 0 then (∅ : Finset ℕ) else {2} :=
    mem_stageLimit.2 ⟨1, by simp⟩
  simp [h0, h2]

/-! ### Finite injury without a stable restraint -/

/-- A restraint alternating between inactive, at even stages, and `some 0`, at odd stages. -/
def alternatingRestraint (_ s : ℕ) : Option ℕ :=
  if Even s then none else some 0

-- Every number enters, at the stage equal to it, and nothing is injured: `0` enters at stage `0`
-- while the restraint is inactive, and later entries are positive ...
example : injurySet Finset.range alternatingRestraint 0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨s, hs⟩ := mem_injurySet.1 hx
  simp only [mem_injuriesAt, Finset.mem_range, alternatingRestraint] at hs
  obtain ⟨hx, hxs, b, hb, hxb⟩ := hs
  split_ifs at hb with he
  simp only [Option.some.injEq] at hb
  subst hb
  have hs0 : s = 0 := by omega
  exact he (hs0 ▸ ⟨0, rfl⟩)

-- ... yet the restraint never stabilizes.
example : ¬∃ b, ∀ᶠ s in atTop, alternatingRestraint 0 s = b := by
  rintro ⟨b, h⟩
  obtain ⟨s₀, h⟩ := eventually_atTop.1 h
  have h₀ := h (2 * s₀) (by omega)
  have h₁ := h (2 * s₀ + 1) (by omega)
  simp only [alternatingRestraint, even_two_mul, ↓reduceIte, Nat.not_even_two_mul_add_one] at h₀ h₁
  exact absurd (h₀.trans h₁.symm) (by simp)

/-! ### Fixed and moving oracles -/

/-- The stages of a moving oracle: empty up to stage `m`, and `{0}` afterwards. -/
def movingStages (m s : ℕ) : Finset ℕ :=
  if s ≤ m then ∅ else {0}

/-- The stages of the moving oracle are monotone: a single entry at stage `m + 1`. -/
theorem monotone_movingStages (m : ℕ) : Monotone (movingStages m) := by
  intro s t hst
  simp only [movingStages]
  split_ifs <;> first | omega | simp

-- At any stage `m` large enough for the program index, the run at input `0` against the stage
-- `∅` is a stage computation, and against this fixed oracle it persists at every later stage ...
example (m : ℕ) (hm : Encodable.encode oracle < m) (t : ℕ) (ht : m ≤ t) :
    evalStage (setAnswers ↑(movingStages m m)) m oracle 0 = some ⟨0, 1⟩ ∧
      evalStage (setAnswers ↑(movingStages m m)) t oracle 0 = some ⟨0, 1⟩ := by
  have h : evalStage (setAnswers ↑(movingStages m m)) m oracle 0 = some ⟨0, 1⟩ :=
    evalStage_eq_some_of_evaln (k := 1) (by simp [movingStages]) (by omega) hm (by simp; omega)
  exact ⟨h, evalStage_mono ht h⟩

-- ... but against the moving oracle it is no longer a stage computation at stage `m + 1`, after
-- `0` enters.
example (m : ℕ) :
    evalStage (setAnswers ↑(movingStages m (m + 1))) (m + 1) oracle 0 ≠ some ⟨0, 1⟩ := by
  simp [movingStages]

/-! ### A dropping restraint -/

/-- The restraint `some 0` at stage `0`, lifted at every later stage. -/
def dropRestraint (_ s : ℕ) : Option ℕ :=
  if s = 0 then some 0 else none

-- The stages are `movingStages 1`, where `0` enters at stage `2`. At stage `0` the run at input
-- `0` has output `0` and use `1`, covered by the restraint `some 0` ...
example :
    evaln (setAnswers ↑(movingStages 1 0)) 1 oracle 0 = some ⟨0, 1⟩ ∧
      dropRestraint 0 0 = some 0 := by
  simp [movingStages, dropRestraint]

-- ... and nothing is ever injured, since `0` enters after the restraint is lifted ...
example : injurySet (movingStages 1) dropRestraint 0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨s, hs⟩ := mem_injurySet.1 hx
  simp only [mem_injuriesAt, movingStages, dropRestraint] at hs
  rcases s with - | s <;> simp_all

-- ... but against the limit the run has output `1`: the earlier computation is not preserved.
example : evaln (setAnswers (stageLimit (movingStages 1))) 1 oracle 0 = some ⟨1, 1⟩ := by
  have h0 : 0 ∈ stageLimit (movingStages 1) := mem_stageLimit.2 ⟨2, by simp [movingStages]⟩
  simp [h0]

end TauCeti.PreservationExample
