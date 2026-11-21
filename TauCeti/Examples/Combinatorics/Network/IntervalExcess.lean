/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.IntervalExcess

/-!
# Interval-excess examples

These examples exercise the difference between exact prescribed excess and flexible excess
intervals. A one-arrow network realizes a flexible supply-and-demand problem, and equal vertex
bounds recover the exact-excess interface without changing the arrow assignment. A network with
no arrows then shows that the global balance condition is not sufficient: its total excess
interval contains zero, but a singleton vertex set strictly violates a cut inequality.

Positive excess denotes demand and negative excess denotes supply throughout.
-/

public section

namespace TauCeti.Examples.IntervalExcess

open Finset

/-! ## A flexible supply-and-demand problem -/

/-- The sole arrow of the example, from the supply vertex to the demand vertex. -/
inductive Hom : Bool → Bool → Type
  | edge : Hom false true
  deriving DecidableEq

instance {x y : Bool} : Subsingleton (Hom x y) := ⟨by
  intro e f
  cases e
  cases f
  rfl⟩

noncomputable instance {x y : Bool} : Fintype (Hom x y) := Fintype.ofFinite _

private instance : IsEmpty (Hom false false) := ⟨fun e ↦ nomatch e⟩
private instance : IsEmpty (Hom true false) := ⟨fun e ↦ nomatch e⟩
private instance : IsEmpty (Hom true true) := ⟨fun e ↦ nomatch e⟩

/-- Zero lower bounds on the one-arrow network. -/
def lower : Assignment Hom ℤ := 0

@[simp]
theorem lower_apply {x y : Bool} (e : Hom x y) : lower e = 0 := (rfl)

/-- The unique arrow has capacity three. -/
def upper : Assignment Hom ℤ
  | _, _, .edge => 3

@[simp]
theorem upper_apply {x y : Bool} (e : Hom x y) : upper e = 3 := by
  cases e
  rfl

/-- Send `q` units along the unique arrow. -/
private def assignment (q : ℤ) : Assignment Hom ℤ
  | _, _, .edge => q

@[simp]
private theorem assignment_edge (q : ℤ) : assignment q Hom.edge = q := (rfl)

@[simp]
private theorem excessAt_assignment_false (q : ℤ) :
    excessAt (assignment q) false = -q := by
  rw [excessAt_def]
  simp only [Fintype.sum_bool, Fintype.sum_empty, add_zero]
  rw [Fintype.sum_subsingleton (fun e : Hom false true ↦ assignment q e) Hom.edge]
  simp

@[simp]
private theorem excessAt_assignment_true (q : ℤ) :
    excessAt (assignment q) true = q := by
  rw [excessAt_def]
  simp only [Fintype.sum_bool, Fintype.sum_empty, add_zero]
  rw [Fintype.sum_subsingleton (fun e : Hom false true ↦ assignment q e) Hom.edge]
  simp

private theorem assignment_mem_Icc {q : ℤ} (hq₀ : 0 ≤ q) (hq₃ : q ≤ 3) :
    assignment q ∈ Set.Icc lower upper := by
  constructor <;> intro x y e <;> cases e
  · simpa [lower, assignment] using hq₀
  · simpa [upper, assignment] using hq₃

/-- Lower excess bounds: supply at most three at `false`, demand at least one at `true`. -/
def flexibleLower : Bool → ℤ
  | false => -3
  | true => 1

@[simp]
theorem flexibleLower_false : flexibleLower false = -3 := (rfl)

@[simp]
theorem flexibleLower_true : flexibleLower true = 1 := (rfl)

/-- Upper excess bounds: supply at least one at `false`, demand at most three at `true`. -/
def flexibleUpper : Bool → ℤ
  | false => -1
  | true => 3

@[simp]
theorem flexibleUpper_false : flexibleUpper false = -1 := (rfl)

@[simp]
theorem flexibleUpper_true : flexibleUpper true = 3 := (rfl)

/-- Sending two units is feasible for the flexible supply-and-demand bounds. -/
private def flexibleFlow :
    ExcessIntervalFlow lower upper flexibleLower flexibleUpper :=
  ⟨assignment 2, assignment_mem_Icc (by omega) (by omega), by
    constructor <;> intro v <;> cases v <;>
      norm_num [flexibleLower, flexibleUpper]⟩

/-- A flexible interval permits two units of supply and demand while retaining the arrow bounds. -/
theorem exists_flexibleFlow :
    ∃ f : ExcessIntervalFlow lower upper flexibleLower flexibleUpper,
      f.val Hom.edge = 2 ∧ excessAt f.val false = -2 ∧ excessAt f.val true = 2 := by
  refine ⟨flexibleFlow, rfl, by simp [flexibleFlow], by simp [flexibleFlow]⟩

/-! ## Equal endpoints recover exact prescribed excess -/

/-- Exact supply two at `false` and exact demand two at `true`. -/
def exactExcess : Bool → ℤ
  | false => -2
  | true => 2

@[simp]
theorem exactExcess_false : exactExcess false = -2 := (rfl)

@[simp]
theorem exactExcess_true : exactExcess true = 2 := (rfl)

/-- The flexible witness also realizes the equal-endpoint interval. -/
private def exactIntervalFlow : ExcessIntervalFlow lower upper exactExcess exactExcess :=
  ⟨assignment 2, assignment_mem_Icc (by omega) (by omega), by
    constructor <;> intro v <;> cases v <;> norm_num [exactExcess]⟩

/-- Passing through the equal-endpoint equivalence preserves the assignment and recovers exact
excess at both vertices. -/
theorem exists_exactFlow :
    ∃ (fᵢ : ExcessIntervalFlow lower upper exactExcess exactExcess)
      (fₑ : ExcessFlow lower upper exactExcess),
      fₑ = ExcessIntervalFlow.equivExcessFlow lower upper exactExcess fᵢ ∧
        fₑ.val = fᵢ.val ∧ fₑ.val Hom.edge = 2 ∧ excessAt fₑ.val false = -2 ∧
        excessAt fₑ.val true = 2 ∧
        (ExcessIntervalFlow.equivExcessFlow lower upper exactExcess).symm fₑ = fᵢ := by
  let fₑ := ExcessIntervalFlow.equivExcessFlow lower upper exactExcess exactIntervalFlow
  refine ⟨exactIntervalFlow, fₑ, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact ExcessIntervalFlow.equivExcessFlow_apply_val lower upper exactExcess exactIntervalFlow
  · rw [ExcessIntervalFlow.equivExcessFlow_apply_val]
    exact assignment_edge 2
  · simpa [fₑ, exactExcess] using fₑ.excessAt_eq false
  · simpa [fₑ, exactExcess] using fₑ.excessAt_eq true
  · exact (ExcessIntervalFlow.equivExcessFlow lower upper exactExcess).symm_apply_apply
      exactIntervalFlow

/-! ## Global balance does not replace the cut inequalities -/

/-- There are no arrows in the obstructed problem. -/
abbrev NoHom (_ _ : Bool) : Type := Empty

/-- The source must supply between one and two units, while the sink must demand between one and
two units. -/
def obstructedLower : Bool → ℤ
  | false => -2
  | true => 1

@[simp]
theorem obstructedLower_false : obstructedLower false = -2 := (rfl)

@[simp]
theorem obstructedLower_true : obstructedLower true = 1 := (rfl)

/-- Upper bounds for the obstructed excess intervals. -/
def obstructedUpper : Bool → ℤ
  | false => -1
  | true => 2

@[simp]
theorem obstructedUpper_false : obstructedUpper false = -1 := (rfl)

@[simp]
theorem obstructedUpper_true : obstructedUpper true = 2 := (rfl)

private theorem obstructedLower_le_upper : obstructedLower ≤ obstructedUpper := by
  intro v
  cases v <;> norm_num [obstructedLower, obstructedUpper]

/-- The total allowed excess interval contains zero, but the demand singleton has lower excess one
and no incoming cut capacity. This strict cut obstruction rules out every assignment. -/
theorem obstructed_not_nonempty :
    let lo : Assignment NoHom ℤ := 0
    let hi : Assignment NoHom ℤ := 0
    (∑ v, obstructedLower v) ≤ 0 ∧ 0 ≤ ∑ v, obstructedUpper v ∧
      cutBound lo hi ({true} : Finset Bool)ᶜ < ∑ v ∈ ({true} : Finset Bool), obstructedLower v ∧
      ¬Nonempty (ExcessIntervalFlow lo hi obstructedLower obstructedUpper) := by
  intro lo hi
  have hcut :
      cutBound lo hi ({true} : Finset Bool)ᶜ <
        ∑ v ∈ ({true} : Finset Bool), obstructedLower v := by
    norm_num [cutBound_def, arrowSum_def, lo, hi, obstructedLower]
  refine ⟨by norm_num [obstructedLower], by norm_num [obstructedUpper], hcut, ?_⟩
  exact (ExcessIntervalFlow.not_nonempty_iff (lo := lo) (hi := hi)
    (a := obstructedLower) (b := obstructedUpper) le_rfl obstructedLower_le_upper).2
      (Or.inl ⟨{true}, hcut⟩)

end TauCeti.Examples.IntervalExcess
