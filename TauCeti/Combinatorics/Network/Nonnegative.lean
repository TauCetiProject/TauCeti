/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Defs
public import TauCeti.Combinatorics.Network.ShortestAugmentation

/-!
# Nonnegative coefficients for finite flows

Capacities and arrow values can live in `Nonneg K`, while excess and flow value remain in the
ordered additive group `K`. `NonnegFlow` is just an ordinary flow for the coerced capacities,
not a second flow structure. `Flow.nonnegAssignment` recovers its nonnegative arrow values.
Coercing finite cut sums agrees with computing them in `K`, so max-flow/min-cut and
additive-subgroup integrality apply directly, including for `Nonneg ℚ` and `Nonneg ℝ`.

For natural capacities, `NatFlow` uses integer excess. Its arrow values are recovered by
`Flow.natAssignment`, with exact round trips, capacity bounds, and natural cut sums.
The named rational and real interfaces specialize this API, and reverse recovery lemmas
characterize assignments by their nonnegative or natural arrow values.
-/

public section

namespace TauCeti

open scoped _root_.NNRat _root_.NNReal

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

/-- Coercion of a nonnegative arrow sum is the arrow sum of the coerced assignment. -/
@[simp]
theorem coe_arrowSum_nonneg [AddCommMonoid K] [Preorder K] [AddLeftMono K]
    [∀ v w, Fintype (Q v w)]
    (c : Assignment Q (Nonneg K)) (S T : Finset V) :
    (↑(arrowSum c S T) : K) = arrowSum (c.map Subtype.val) S T :=
  map_arrowSum Nonneg.coeAddMonoidHom c S T

section Nonnegative

variable [AddCommGroup K] [Preorder K]
variable [Fintype V] [∀ v w, Fintype (Q v w)]

/-- Flows for nonnegative capacities, with excess and value computed in `K`. -/
abbrev NonnegFlow (cap : Assignment Q (Nonneg K)) (s t : V) :=
  Flow (cap.map Subtype.val) s t

namespace Flow

variable {cap : Assignment Q K} {s t : V}

/-- The arrow values of an ordinary flow, bundled as nonnegative elements. -/
def nonnegAssignment (f : Flow cap s t) : Assignment Q (Nonneg K) :=
  fun _ _ e ↦ ⟨f.toFun e, f.nonneg e⟩

@[simp]
theorem coe_nonnegAssignment (f : Flow cap s t) {x y : V} (e : Q x y) :
    (f.nonnegAssignment e : K) = f.toFun e :=
  (rfl)

/-- Forgetting the nonnegativity proofs recovers the original assignment. -/
@[simp]
theorem nonnegAssignment_map_coe (f : Flow cap s t) :
    f.nonnegAssignment.map Subtype.val = f.toFun :=
  (rfl)

/-- Nonnegative arrow values determine the original assignment and conversely. -/
@[simp]
theorem nonnegAssignment_eq_iff {c : Assignment Q (Nonneg K)} (f : Flow cap s t) :
    f.nonnegAssignment = c ↔ f.toFun = c.map Subtype.val := by
  constructor
  · rintro rfl
    exact f.nonnegAssignment_map_coe.symm
  · intro hf
    funext x y e
    apply Subtype.ext
    simp [hf]

/-- Nonnegative arrow values satisfy the capacity bound in the nonnegative subtype. -/
theorem nonnegAssignment_le {c : Assignment Q (Nonneg K)} (f : NonnegFlow c s t)
    {x y : V} (e : Q x y) : f.nonnegAssignment e ≤ c e :=
  f.le_upper e

/-- The flow value is bounded by the coerced nonnegative cut sum. -/
theorem val_le_coe_arrowSum [IsOrderedAddMonoid K] [DecidableEq V] {c : Assignment Q (Nonneg K)}
    (f : NonnegFlow c s t) {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    f.val ≤ (↑(arrowSum c S Sᶜ) : K) := by
  rw [coe_arrowSum_nonneg]
  exact f.val_le_arrowSum hs ht

end Flow

end Nonnegative

namespace NonnegFlow

variable [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]
variable [Fintype V] [∀ v w, Fintype (Q v w)]
variable (cap : Assignment Q (Nonneg K)) {s t : V}

/-- Max-flow/min-cut for nonnegative capacities, with an attaining assignment in any additive
subgroup containing the coerced capacities. The cut sum is computed in `Nonneg K`. -/
theorem exists_val_eq_coe_arrowSum_mem [DecidableEq V] (hst : s ≠ t)
    (H : AddSubgroup K) (hcap : ∀ ⦃x y⦄ (e : Q x y), (cap e : K) ∈ H) :
    ∃ f : NonnegFlow cap s t, (∀ ⦃x y⦄ (e : Q x y), (f.nonnegAssignment e : K) ∈ H) ∧
      ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = (↑(arrowSum cap S Sᶜ) : K) := by
  obtain ⟨f, hf, hfH⟩ := Flow.exists_isMaximum_mem
    (cap := cap.map Subtype.val) (fun _ _ e ↦ (cap e).property) H hcap
  obtain ⟨S, hs, ht, hS⟩ := hf.exists_val_eq_arrowSum hst
  exact ⟨f, hfH, S, hs, ht, by simpa using hS⟩

/-- Max-flow/min-cut for capacities in `Nonneg K`, with no additional coefficient assumptions. -/
theorem exists_val_eq_coe_arrowSum [DecidableEq V] (hst : s ≠ t) :
    ∃ f : NonnegFlow cap s t, ∃ S : Finset V,
      s ∈ S ∧ t ∉ S ∧ f.val = (↑(arrowSum cap S Sᶜ) : K) := by
  obtain ⟨f, _, h⟩ := exists_val_eq_coe_arrowSum_mem cap hst ⊤
    (fun _ _ _ ↦ AddSubgroup.mem_top _)
  exact ⟨f, h⟩

end NonnegFlow

section Natural

variable [Fintype V] [∀ v w, Fintype (Q v w)]

/-- Flows for natural capacities, with signed integer excess and value. -/
abbrev NatFlow (cap : Assignment Q ℕ) (s t : V) :=
  Flow (cap.map (Nat.cast : ℕ → ℤ)) s t

namespace Flow

variable {cap : Assignment Q ℤ} {s t : V}

/-- The natural arrow values of an integer flow. Nonnegativity makes this conversion exact. -/
def natAssignment (f : Flow cap s t) : Assignment Q ℕ :=
  f.toFun.map Int.toNat

theorem natAssignment_apply (f : Flow cap s t) {x y : V} (e : Q x y) :
    f.natAssignment e = (f.toFun e).toNat :=
  (rfl)

@[simp]
theorem coe_natAssignment (f : Flow cap s t) {x y : V} (e : Q x y) :
    (f.natAssignment e : ℤ) = f.toFun e :=
  Int.toNat_of_nonneg (f.nonneg e)

/-- Casting the recovered natural values returns the original assignment. -/
@[simp]
theorem natAssignment_map_cast (f : Flow cap s t) :
    f.natAssignment.map (Nat.cast : ℕ → ℤ) = f.toFun := by
  funext x y e
  exact f.coe_natAssignment e

/-- Natural arrow values are bounded by the original natural capacities. -/
theorem natAssignment_le {c : Assignment Q ℕ} (f : NatFlow c s t)
    {x y : V} (e : Q x y) : f.natAssignment e ≤ c e := by
  have h := f.le_upper e
  rw [← f.coe_natAssignment e, Assignment.map_apply] at h
  exact_mod_cast h

/-- Recovering natural values from an assignment already expressed by natural numbers is an
exact round trip. -/
theorem natAssignment_eq {a : Assignment Q ℕ}
    (f : Flow cap s t) (ha : f.toFun = a.map (Nat.cast : ℕ → ℤ)) : f.natAssignment = a := by
  funext x y e
  simp [natAssignment_apply, ha]

/-- Natural arrow values determine the original integer assignment and conversely. -/
@[simp]
theorem natAssignment_eq_iff {a : Assignment Q ℕ} (f : Flow cap s t) :
    f.natAssignment = a ↔ f.toFun = a.map (Nat.cast : ℕ → ℤ) := by
  constructor
  · rintro rfl
    exact f.natAssignment_map_cast.symm
  · exact f.natAssignment_eq

/-- Natural and nonnegative-integer arrow values represent the same coefficient. -/
theorem nonnegAssignment_apply_eq_natCast (f : Flow cap s t) {x y : V} (e : Q x y) :
    f.nonnegAssignment e = (f.natAssignment e : Nonneg ℤ) :=
  Subtype.ext (by
    simpa only [coe_nonnegAssignment, Nonneg.coe_natCast] using
      (f.coe_natAssignment e).symm)

end Flow

omit [Fintype V] in
/-- Natural cut capacity casts to the integer cut capacity. -/
@[simp]
theorem coe_arrowSum_nat (c : Assignment Q ℕ) (S T : Finset V) :
    (↑(arrowSum c S T) : ℤ) = arrowSum (c.map (Nat.cast : ℕ → ℤ)) S T :=
  map_arrowSum (Nat.castAddMonoidHom ℤ) c S T

namespace NatFlow

variable (cap : Assignment Q ℕ) {s t : V}

/-- Natural capacities admit a natural-valued maximum flow and an equal natural cut capacity;
excess and the flow value remain integer-valued. -/
theorem exists_val_eq_coe_arrowSum [DecidableEq V] (hst : s ≠ t) :
    ∃ f : NatFlow cap s t, ∃ S : Finset V,
      s ∈ S ∧ t ∉ S ∧ f.val = (↑(arrowSum cap S Sᶜ) : ℤ) := by
  obtain ⟨f, S, hs, ht, hS⟩ := Flow.exists_val_eq_arrowSum
    (cap := cap.map (Nat.cast : ℕ → ℤ)) hst (fun _ _ e ↦ Int.natCast_nonneg (cap e))
  exact ⟨f, S, hs, ht, by simpa using hS⟩

end NatFlow

end Natural

/-! The following examples include parallel arrows, opposite arrows, and loops. Only the two
arrows from `false` to `true` contribute to the displayed cuts. -/

example : ∃ f : NatFlow (Q := fun _ _ : Bool ↦ Fin 2) (fun _ _ _ ↦ 3) false true,
    f.val = 6 ∧ ∀ ⦃x y⦄ (e : Fin 2), f.natAssignment (x := x) (y := y) e ≤ 3 := by
  obtain ⟨f, S, hs, ht, h⟩ := NatFlow.exists_val_eq_coe_arrowSum
    (Q := fun _ _ : Bool ↦ Fin 2) (fun _ _ _ ↦ 3) Bool.false_ne_true
  have hS : S = {false} := by
    ext b
    cases b <;> simp_all
  refine ⟨f, ?_, fun _ _ e ↦ f.natAssignment_le e⟩
  simpa [hS, arrowSum_def, Finset.card_compl] using h

example : ∃ f : NonnegFlow (K := ℚ) (Q := fun _ _ : Bool ↦ Fin 2)
    (fun _ _ _ ↦ ⟨1 / 2, by norm_num⟩) false true, f.val = 1 := by
  obtain ⟨f, S, hs, ht, h⟩ := NonnegFlow.exists_val_eq_coe_arrowSum
    (K := ℚ) (Q := fun _ _ : Bool ↦ Fin 2)
    (fun _ _ _ ↦ ⟨1 / 2, by norm_num⟩) Bool.false_ne_true
  have hS : S = {false} := by
    ext b
    cases b <;> simp_all
  rw [coe_arrowSum_nonneg] at h
  exact ⟨f, by simpa [hS, arrowSum_def, Finset.card_compl] using h⟩

example : ∃ f : NonnegFlow (K := ℝ) (Q := fun _ _ : Bool ↦ Fin 2)
    (fun _ _ _ ↦ ⟨3 / 4, by norm_num⟩) false true, f.val = 3 / 2 := by
  obtain ⟨f, S, hs, ht, h⟩ := NonnegFlow.exists_val_eq_coe_arrowSum
    (K := ℝ) (Q := fun _ _ : Bool ↦ Fin 2)
    (fun _ _ _ ↦ ⟨3 / 4, by norm_num⟩) Bool.false_ne_true
  have hS : S = {false} := by
    ext b
    cases b <;> simp_all
  rw [coe_arrowSum_nonneg] at h
  refine ⟨f, ?_⟩
  norm_num [hS, arrowSum_def, Finset.card_compl] at h ⊢
  exact h

/-! ### Named nonnegative rational and real types -/

section RationalReal

-- The named types unfold to Nonneg ℚ and Nonneg ℝ, and their derived additive and order
-- instances agree with those of Nonneg. Their coercion homomorphisms act as Subtype.val,
-- so the accessors and theorems below specialize the generic interface directly.

variable [Fintype V] [∀ x y, Fintype (Q x y)]

/-- Ordinary rational flows with capacities in `ℚ≥0`, using its canonical rational coercion. -/
abbrev NNRatFlow (cap : Assignment Q ℚ≥0) (s t : V) :=
  Flow (cap.map NNRat.coeHom) s t

/-- Ordinary real flows with capacities in `ℝ≥0`, using its canonical real coercion. -/
abbrev NNRealFlow (cap : Assignment Q ℝ≥0) (s t : V) :=
  Flow (cap.map NNReal.toRealHom) s t

/-- The arrow values of a rational flow, bundled in the named nonnegative rational type. -/
def Flow.toNNRat {cap : Assignment Q ℚ} {s t : V} (f : Flow cap s t) : Assignment Q ℚ≥0 :=
  f.nonnegAssignment

@[simp]
theorem Flow.coe_toNNRat_apply {cap : Assignment Q ℚ} {s t : V} (f : Flow cap s t)
    {x y : V} (e : Q x y) : (f.toNNRat e : ℚ) = f.toFun e :=
  f.coe_nonnegAssignment e

/-- Coercing nonnegative rational arrow values recovers the original assignment. -/
@[simp]
theorem Flow.toNNRat_map_coe {cap : Assignment Q ℚ} {s t : V} (f : Flow cap s t) :
    f.toNNRat.map ((↑) : ℚ≥0 → ℚ) = f.toFun :=
  f.nonnegAssignment_map_coe

/-- The arrow values of a real flow, bundled in the named nonnegative real type. -/
def Flow.toNNReal {cap : Assignment Q ℝ} {s t : V} (f : Flow cap s t) : Assignment Q ℝ≥0 :=
  f.nonnegAssignment

@[simp]
theorem Flow.coe_toNNReal_apply {cap : Assignment Q ℝ} {s t : V} (f : Flow cap s t)
    {x y : V} (e : Q x y) : (f.toNNReal e : ℝ) = f.toFun e :=
  f.coe_nonnegAssignment e

/-- Coercing nonnegative real arrow values recovers the original assignment. -/
@[simp]
theorem Flow.toNNReal_map_coe {cap : Assignment Q ℝ} {s t : V} (f : Flow cap s t) :
    f.toNNReal.map ((↑) : ℝ≥0 → ℝ) = f.toFun :=
  f.nonnegAssignment_map_coe

/-- Nonnegative rational values recover the original rational assignment. -/
@[simp]
theorem Flow.toNNRat_eq_iff {cap : Assignment Q ℚ} {s t : V} (f : Flow cap s t)
    {c : Assignment Q ℚ≥0} : f.toNNRat = c ↔ f.toFun = c.map NNRat.coeHom :=
  f.nonnegAssignment_eq_iff

/-- Nonnegative real values recover the original real assignment. -/
@[simp]
theorem Flow.toNNReal_eq_iff {cap : Assignment Q ℝ} {s t : V} (f : Flow cap s t)
    {c : Assignment Q ℝ≥0} : f.toNNReal = c ↔ f.toFun = c.map NNReal.toRealHom :=
  f.nonnegAssignment_eq_iff

/-- Nonnegative rational arrow values respect the original capacities. -/
theorem NNRatFlow.toNNRat_le {cap : Assignment Q ℚ≥0} {s t : V} (f : NNRatFlow cap s t) :
    f.toNNRat ≤ cap :=
  fun _ _ e ↦ f.nonnegAssignment_le e

/-- Nonnegative real arrow values respect the original capacities. -/
theorem NNRealFlow.toNNReal_le {cap : Assignment Q ℝ≥0} {s t : V} (f : NNRealFlow cap s t) :
    f.toNNReal ≤ cap :=
  fun _ _ e ↦ f.nonnegAssignment_le e

/-- Max-flow/min-cut and subgroup integrality for capacities in `ℚ≥0`. -/
theorem NNRatFlow.exists_val_eq_arrowSum_mem [DecidableEq V]
    {cap : Assignment Q ℚ≥0} {s t : V} (hst : s ≠ t) (H : AddSubgroup ℚ)
    (hcapH : ∀ ⦃x y⦄ (e : Q x y), (cap e : ℚ) ∈ H) :
    ∃ f : NNRatFlow cap s t, ∃ S : Finset V,
      s ∈ S ∧ t ∉ S ∧ f.val = ((arrowSum cap S Sᶜ : ℚ≥0) : ℚ) ∧
        ∀ ⦃x y⦄ (e : Q x y), (f.toNNRat e : ℚ) ∈ H := by
  obtain ⟨f, hfH, S, hs, ht, hval⟩ :=
    NonnegFlow.exists_val_eq_coe_arrowSum_mem cap hst H hcapH
  exact ⟨f, S, hs, ht, hval, hfH⟩

/-- Max-flow/min-cut and subgroup integrality for capacities in `ℝ≥0`. -/
theorem NNRealFlow.exists_val_eq_arrowSum_mem [DecidableEq V]
    {cap : Assignment Q ℝ≥0} {s t : V} (hst : s ≠ t) (H : AddSubgroup ℝ)
    (hcapH : ∀ ⦃x y⦄ (e : Q x y), (cap e : ℝ) ∈ H) :
    ∃ f : NNRealFlow cap s t, ∃ S : Finset V,
      s ∈ S ∧ t ∉ S ∧ f.val = ((arrowSum cap S Sᶜ : ℝ≥0) : ℝ) ∧
        ∀ ⦃x y⦄ (e : Q x y), (f.toNNReal e : ℝ) ∈ H := by
  obtain ⟨f, hfH, S, hs, ht, hval⟩ :=
    NonnegFlow.exists_val_eq_coe_arrowSum_mem cap hst H hcapH
  exact ⟨f, S, hs, ht, hval, hfH⟩

end RationalReal

end TauCeti
