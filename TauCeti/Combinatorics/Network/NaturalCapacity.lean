/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Nonnegative

/-!
# Natural capacities over ordered coefficient groups

Natural-number capacities can be read in any linearly ordered additive group `K` with a unit
`0 ≤ 1`, such as `ℤ`, `ℚ` or `ℝ`, through `Nat.cast`. They then lie in the additive subgroup
`AddSubgroup.zmultiples 1`, whose nonnegative elements are exactly the natural casts. So the
integrality theorem `TauCeti.Flow.exists_isMaximum_mem` gives a maximum flow over `K` all of whose
arrow values are natural numbers, and whose value is the natural capacity of a cut.

Flows with natural arrow values over different coefficient groups are compared through the integer
flows `TauCeti.NatFlow`. The flow `TauCeti.NatFlow.castFlow K f` over `K` has the same natural
arrow values as the integer flow `f`, and its value is the cast of the value of `f`. The range of
`TauCeti.NatFlow.castFlow K` consists of the flows over `K` with natural arrow values, and when
`1 ≠ 0` in `K` it is injective and preserves and reflects maximality. A flow over `ℚ` with
natural arrow values therefore has the same arrow values, value and maximality as the
corresponding flows over `ℤ` and `ℝ`.

## Main definitions

* `TauCeti.NatFlow.castFlow K f`: the flow over `K` with the natural arrow values of the integer
  flow `f`.

## Main results

* `TauCeti.excessAt_map_natCast`: the excess of a natural assignment read in `K` is the cast of
  its integer excess.
* `TauCeti.Flow.exists_isMaximum_eq_natCast`: for natural capacities, some maximum flow over `K`
  has natural arrow values.
* `TauCeti.Flow.exists_eq_natCast_val_eq_arrowSum`: max-flow/min-cut for natural capacities over
  `K`, with natural arrow values and a natural cut capacity.
* `TauCeti.NatFlow.exists_castFlow_eq_iff`: a flow over `K` comes from an integer flow exactly
  when its arrow values are natural numbers.
* `TauCeti.NatFlow.isMaximum_castFlow_iff`: `TauCeti.NatFlow.castFlow K` preserves and reflects
  maximality.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

variable [Fintype V] [∀ v w, Fintype (Q v w)]

/-- The excess of a natural assignment read in `K` is the cast of its integer excess. -/
theorem excessAt_map_natCast [AddCommGroupWithOne K] (a : Assignment Q ℕ) (v : V) :
    excessAt (a.map (Nat.cast : ℕ → K)) v = ((excessAt (a.map (Nat.cast : ℕ → ℤ)) v : ℤ) : K) := by
  simp [excessAt_def]

namespace Flow

variable [AddCommGroupWithOne K] [LinearOrder K] [IsOrderedAddMonoid K] [ZeroLEOneClass K]
variable (cap : Assignment Q ℕ) {s t : V}

/-- **Integrality for natural capacities.** For natural capacities read in a linearly ordered
additive group `K` with `0 ≤ 1`, such as `ℤ`, `ℚ` or `ℝ`, some maximum ordinary flow has natural
arrow values. This is the case `H = AddSubgroup.zmultiples 1` of
`TauCeti.Flow.exists_isMaximum_mem`. -/
theorem exists_isMaximum_eq_natCast :
    ∃ (f : Flow (cap.map (Nat.cast : ℕ → K)) s t) (a : Assignment Q ℕ),
      f.IsMaximum ∧ f.toFun = a.map Nat.cast := by
  obtain ⟨f, hf, hfH⟩ := exists_isMaximum_mem (cap := cap.map (Nat.cast : ℕ → K)) (s := s)
    (t := t) (fun _ _ e ↦ Nat.cast_nonneg' (cap e)) (AddSubgroup.zmultiples 1)
    fun _ _ e ↦ ⟨cap e, by simp⟩
  -- A nonnegative integer multiple of `1` is a natural cast.
  have hnat ⦃x y : V⦄ (e : Q x y) : ∃ n : ℕ, f.toFun e = n := by
    obtain ⟨k, hk⟩ := hfH e
    simp only [zsmul_one] at hk
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · exact ⟨n, by simp [← hk]⟩
    · refine ⟨0, le_antisymm ?_ (by simpa using f.nonneg e)⟩
      simp [← hk]
  choose a ha using hnat
  exact ⟨f, fun _ _ e ↦ a e, hf, by funext x y e; exact ha e⟩

/-- **Max-flow/min-cut for natural capacities.** For natural capacities read in a linearly
ordered additive group `K` with `0 ≤ 1` and distinct terminals, some ordinary flow over `K` with
natural arrow values has value equal to the cast of the natural capacity of the arrows leaving some
vertex set containing `s` but not `t`. -/
theorem exists_eq_natCast_val_eq_arrowSum [DecidableEq V] (hst : s ≠ t) :
    ∃ (f : Flow (cap.map (Nat.cast : ℕ → K)) s t) (a : Assignment Q ℕ) (S : Finset V),
      f.toFun = a.map Nat.cast ∧ s ∈ S ∧ t ∉ S ∧ f.val = ((arrowSum cap S Sᶜ : ℕ) : K) := by
  obtain ⟨f, a, hf, ha⟩ := exists_isMaximum_eq_natCast (K := K) cap (s := s) (t := t)
  obtain ⟨S, hs, ht, hS⟩ := hf.exists_val_eq_arrowSum hst
  exact ⟨f, a, S, ha, hs, ht, by rw [hS, ← Nat.coe_castAddMonoidHom, map_arrowSum]⟩

end Flow

namespace NatFlow

section PartialOrder

variable [AddCommGroupWithOne K] [PartialOrder K] [IsOrderedAddMonoid K] [ZeroLEOneClass K]
variable {cap : Assignment Q ℕ} {s t : V}

variable (K) in
/-- The ordinary flow for the natural capacities `cap` read in `K` whose arrow values are the
natural arrow values of the integer flow `f`. -/
def castFlow (f : NatFlow cap s t) : Flow (cap.map (Nat.cast : ℕ → K)) s t where
  toFun := f.natAssignment.map Nat.cast
  mem_Icc := ⟨fun _ _ _ ↦ Nat.cast_nonneg' _, fun _ _ e ↦ Nat.mono_cast (f.natAssignment_le e)⟩
  conserve v hvs hvt := by
    rw [excessAt_map_natCast, Flow.natAssignment_map_cast, f.conserve v hvs hvt, Int.cast_zero]
  excessAt_sink_nonneg := by
    rw [excessAt_map_natCast, Flow.natAssignment_map_cast]
    exact Int.cast_nonneg f.excessAt_sink_nonneg

@[simp]
theorem castFlow_toFun (f : NatFlow cap s t) :
    (f.castFlow K).toFun = f.natAssignment.map Nat.cast :=
  (rfl)

/-- The arrow values of `f.castFlow K` are the casts of the integer arrow values of `f`. -/
theorem castFlow_toFun_apply (f : NatFlow cap s t) {x y : V} (e : Q x y) :
    (f.castFlow K).toFun e = (f.toFun e : K) := by
  rw [castFlow_toFun, Assignment.map_apply, ← f.coe_natAssignment e, Int.cast_natCast]

/-- The value of `f.castFlow K` is the cast of the integer value of `f`. -/
@[simp]
theorem val_castFlow (f : NatFlow cap s t) : (f.castFlow K).val = (f.val : K) := by
  rw [BoundedFlow.val_def, BoundedFlow.val_def, castFlow_toFun, excessAt_map_natCast,
    Flow.natAssignment_map_cast]

/-- Over `ℤ`, `TauCeti.NatFlow.castFlow` returns the integer flow itself. -/
@[simp]
theorem castFlow_int (f : NatFlow cap s t) : f.castFlow ℤ = f :=
  Flow.ext f.natAssignment_map_cast

/-- A flow over `K` for natural capacities comes from an integer flow exactly when its arrow values
are natural numbers. -/
theorem exists_castFlow_eq_iff {g : Flow (cap.map (Nat.cast : ℕ → K)) s t} :
    (∃ f : NatFlow cap s t, f.castFlow K = g) ↔ ∃ a : Assignment Q ℕ, g.toFun = a.map Nat.cast := by
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨f.natAssignment, hf ▸ rfl⟩, fun ⟨a, ha⟩ ↦ ?_⟩
  by_cases h1 : (1 : K) = 0
  · -- Every natural cast vanishes, so `g` is the zero flow.
    have hcast (n : ℕ) : (n : K) = 0 := by rw [← nsmul_one, h1, nsmul_zero]
    refine ⟨Flow.zero fun _ _ e ↦ Int.natCast_nonneg (cap e), Flow.ext ?_⟩
    funext x y e
    rw [castFlow_toFun, Assignment.map_apply, hcast]
    exact (le_antisymm (by simpa [hcast] using g.le_upper e) (g.nonneg e)).symm
  have : NeZero (1 : K) := ⟨h1⟩
  -- The integer excess of `a` casts to the excess of `g` over `K`.
  have hexc (v : V) : ((excessAt (a.map (Nat.cast : ℕ → ℤ)) v : ℤ) : K) = excessAt g.toFun v := by
    rw [ha, excessAt_map_natCast (K := K)]
  let f : NatFlow cap s t :=
    { toFun := a.map Nat.cast
      mem_Icc := by
        refine ⟨fun _ _ _ ↦ Int.natCast_nonneg _, fun _ _ e ↦ ?_⟩
        have he : ((a e : ℤ) : K) ≤ ((cap e : ℤ) : K) := by simpa [ha] using g.le_upper e
        simpa using (Int.cast_le (R := K)).1 he
      conserve v hvs hvt := (Int.cast_strictMono (R := K)).injective <| by
        simpa [hexc] using g.conserve v hvs hvt
      excessAt_sink_nonneg := (Int.cast_le (R := K)).1 <| by
        simpa [hexc] using g.excessAt_sink_nonneg }
  exact ⟨f, Flow.ext <| by rw [castFlow_toFun, Flow.natAssignment_eq f rfl, ha]⟩

/-- When `1 ≠ 0` in `K`, distinct integer flows give distinct flows over `K`. -/
theorem castFlow_injective [NeZero (1 : K)] :
    Function.Injective (fun f : NatFlow cap s t ↦ f.castFlow K) := by
  intro f g h
  refine Flow.ext ?_
  funext x y e
  refine (Int.cast_strictMono (R := K)).injective ?_
  simpa only [castFlow_toFun_apply] using congrArg (fun f ↦ f.toFun e) h

end PartialOrder

variable [AddCommGroupWithOne K] [LinearOrder K] [IsOrderedAddMonoid K] [ZeroLEOneClass K]
  [NeZero (1 : K)] {cap : Assignment Q ℕ} {s t : V}

/-- When `1 ≠ 0` in `K`, an integer flow for natural capacities is maximum exactly when the flow
over `K` with the same natural arrow values is maximum. -/
theorem isMaximum_castFlow_iff {f : NatFlow cap s t} :
    (f.castFlow K).IsMaximum ↔ f.IsMaximum := by
  refine ⟨fun hf ↦ Flow.isMaximum_iff.2 fun g ↦ ?_, fun hf ↦ ?_⟩
  · have hg := Flow.isMaximum_iff.1 hf (castFlow K g)
    rwa [val_castFlow, val_castFlow, Int.cast_le] at hg
  · -- Compare with a maximum flow over `K` with natural arrow values.
    obtain ⟨g₀, a, hg₀, ha⟩ := Flow.exists_isMaximum_eq_natCast (K := K) cap (s := s) (t := t)
    obtain ⟨f₀, rfl⟩ := exists_castFlow_eq_iff.2 ⟨a, ha⟩
    refine Flow.isMaximum_iff.2 fun g ↦ (Flow.isMaximum_iff.1 hg₀ g).trans ?_
    rw [val_castFlow, val_castFlow]
    exact Int.cast_mono (Flow.isMaximum_iff.1 hf f₀)

end NatFlow

/-! The following examples read the capacities `3` on two parallel arrows from `false` to `true`
in `ℚ` and in `ℝ`. A maximum flow over `ℝ` with natural arrow values has value `6`. A maximum flow
over `ℚ` with natural arrow values comes from an integer flow, and the flow over `ℝ` with the same
natural arrow values is again maximum, with the same value. -/

example : ∃ (f : Flow (Assignment.map (fun _ _ _ ↦ 3 : Assignment (fun _ _ : Bool ↦ Fin 2) ℕ)
      (Nat.cast : ℕ → ℝ)) false true) (a : Assignment (fun _ _ : Bool ↦ Fin 2) ℕ),
    f.toFun = a.map Nat.cast ∧ f.val = 6 := by
  obtain ⟨f, a, S, ha, hs, ht, h⟩ := Flow.exists_eq_natCast_val_eq_arrowSum (K := ℝ)
    (Q := fun _ _ : Bool ↦ Fin 2) (fun _ _ _ ↦ 3) Bool.false_ne_true
  have hS : S = {false} := by
    ext b
    cases b <;> simp_all
  refine ⟨f, a, ha, ?_⟩
  norm_num [h, hS, arrowSum_def, Finset.card_compl]

example {g : Flow (Assignment.map (fun _ _ _ ↦ 3 : Assignment (fun _ _ : Bool ↦ Fin 2) ℕ)
      (Nat.cast : ℕ → ℚ)) false true} {a : Assignment (fun _ _ : Bool ↦ Fin 2) ℕ}
    (ha : g.toFun = a.map Nat.cast) (hg : g.IsMaximum) :
    ∃ f : NatFlow (fun _ _ _ ↦ 3 : Assignment (fun _ _ : Bool ↦ Fin 2) ℕ) false true,
      f.castFlow ℚ = g ∧ (f.castFlow ℝ).IsMaximum ∧ (f.castFlow ℝ).val = g.val := by
  obtain ⟨f, rfl⟩ := NatFlow.exists_castFlow_eq_iff.2 ⟨a, ha⟩
  refine ⟨f, rfl, NatFlow.isMaximum_castFlow_iff.2 (NatFlow.isMaximum_castFlow_iff.1 hg), ?_⟩
  simp

end TauCeti
