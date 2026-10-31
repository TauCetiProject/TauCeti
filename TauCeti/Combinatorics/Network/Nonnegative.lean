/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Defs
public import TauCeti.Combinatorics.Network.ShortestAugmentation

/-!
# Flows with nonnegative and natural coefficients

Nonnegative capacities are coerced into the coefficient group for conservation and residual
calculations. `NonnegFlow` is an abbreviation for the existing ordinary flow type with these
coerced capacities; excess and value stay in the group. `Flow.toNonneg` bundles its arrow values
in `Nonneg K`. Coercion commutes with arrow sums, so max-flow/min-cut and subgroup integrality
apply directly to capacities in this subtype, including nonnegative rationals and reals.

`NatFlow` similarly uses natural capacities and integer excess. Its arrow values can be recovered
as natural numbers by `Flow.toNat`, with exact round trips, capacity bounds, and sum formulas.
`NNRatFlow` and `NNRealFlow` use the canonical coercions of the named nonnegative rational and
real types. No interface introduces an additional flow structure or conservation law.

The existence results specialize `Flow.exists_isMaximum_mem` and
`Flow.IsMaximum.exists_val_eq_arrowSum` from the ordered-group flow theory.
-/

public section

namespace TauCeti

open Finset
open scoped _root_.NNRat _root_.NNReal

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

section ArrowSum

variable [∀ x y, Fintype (Q x y)] [AddCommMonoid K] [Preorder K] [AddLeftMono K]

/-- Coercion from nonnegative coefficients commutes with every arrow sum, in particular cuts. -/
@[simp]
theorem Nonneg.coe_arrowSum (f : Assignment Q (Nonneg K)) (S T : Finset V) :
    ((arrowSum f S T : Nonneg K) : K) = arrowSum (f.map Subtype.val) S T :=
  map_arrowSum Nonneg.coeAddMonoidHom f S T

end ArrowSum

section Nonnegative

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K] [Preorder K]

/-- Ordinary flows for capacities in `Nonneg K`, with excess and value computed in `K`. -/
abbrev NonnegFlow (cap : Assignment Q (Nonneg K)) (s t : V) :=
  Flow (cap.map Subtype.val) s t

namespace Flow

variable {cap : Assignment Q K} {s t : V}

/-- The arrow values of an ordinary flow, bundled as nonnegative coefficients. -/
def toNonneg (f : Flow cap s t) : Assignment Q (Nonneg K) :=
  fun _ _ e ↦ ⟨f.toFun e, f.nonneg e⟩

@[simp]
theorem coe_toNonneg_apply (f : Flow cap s t) {x y : V} (e : Q x y) :
    (f.toNonneg e : K) = f.toFun e :=
  (rfl)

/-- Coercing the bundled arrow values recovers the original assignment. -/
@[simp]
theorem toNonneg_map_coe (f : Flow cap s t) : f.toNonneg.map Subtype.val = f.toFun :=
  (rfl)

/-- Nonnegative arrow values determine the original assignment and conversely. -/
@[simp]
theorem toNonneg_eq_iff {c : Assignment Q (Nonneg K)} (f : Flow cap s t) :
    f.toNonneg = c ↔ f.toFun = c.map Subtype.val := by
  constructor
  · rintro rfl
    exact f.toNonneg_map_coe.symm
  · intro hf
    funext x y e
    apply Subtype.ext
    simp [hf]

end Flow

/-- The bundled arrow values respect the supplied nonnegative capacities. -/
theorem NonnegFlow.toNonneg_le {cap : Assignment Q (Nonneg K)} {s t : V}
    (f : NonnegFlow cap s t) : f.toNonneg ≤ cap := by
  intro x y e
  apply Subtype.coe_le_coe.mp
  simpa only [Flow.coe_toNonneg_apply, Assignment.map_apply] using f.le_upper e

end Nonnegative

namespace NonnegFlow

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K] [LinearOrder K]
  [IsOrderedAddMonoid K] [DecidableEq V]
variable {cap : Assignment Q (Nonneg K)} {s t : V}

/-- Max-flow/min-cut for nonnegative coefficients, with the attaining arrow values in any
additive subgroup containing the capacities. Cut capacity is computed in `Nonneg K` and coerced
to the coefficient group. -/
theorem exists_val_eq_arrowSum_mem (hst : s ≠ t) (H : AddSubgroup K)
    (hcapH : ∀ ⦃x y⦄ (e : Q x y), (cap e : K) ∈ H) :
    ∃ f : NonnegFlow cap s t, ∃ S : Finset V,
      s ∈ S ∧ t ∉ S ∧ f.val = ((arrowSum cap S Sᶜ : Nonneg K) : K) ∧
        ∀ ⦃x y⦄ (e : Q x y), (f.toNonneg e : K) ∈ H := by
  obtain ⟨f, hf, hfH⟩ := Flow.exists_isMaximum_mem
    (cap := cap.map Subtype.val)
    (fun _ _ e ↦ by simpa only [Assignment.map_apply, Pi.zero_apply] using (cap e).property) H
    (fun _ _ e ↦ by simpa only [Assignment.map_apply] using hcapH e)
  obtain ⟨S, hs, ht, hval⟩ := hf.exists_val_eq_arrowSum hst
  refine ⟨f, S, hs, ht, (Nonneg.coe_arrowSum cap S Sᶜ).symm ▸ hval, ?_⟩
  intro x y e
  simpa only [Flow.coe_toNonneg_apply] using hfH e

/-- Nonnegative capacities admit a flow attaining the capacity of a terminal-separating cut. -/
theorem exists_val_eq_arrowSum (hst : s ≠ t) :
    ∃ f : NonnegFlow cap s t, ∃ S : Finset V,
      s ∈ S ∧ t ∉ S ∧ f.val = ((arrowSum cap S Sᶜ : Nonneg K) : K) := by
  obtain ⟨f, S, hs, ht, hval, _⟩ := exists_val_eq_arrowSum_mem (cap := cap) hst ⊤
    (fun _ _ _ ↦ AddSubgroup.mem_top _)
  exact ⟨f, S, hs, ht, hval⟩

end NonnegFlow

section Natural

variable [Fintype V] [∀ x y, Fintype (Q x y)]

/-- Ordinary flows for natural capacities. Arrow assignments, excess, and value are integer-valued;
`Flow.toNat` recovers their natural arrow values. -/
abbrev NatFlow (cap : Assignment Q ℕ) (s t : V) :=
  Flow (cap.map (Nat.castAddMonoidHom ℤ)) s t

namespace Flow

variable {cap : Assignment Q ℤ} {s t : V}

/-- The natural arrow values of an integer flow. Nonnegativity makes conversion exact. -/
def toNat (f : Flow cap s t) : Assignment Q ℕ :=
  f.toFun.map Int.toNat

theorem toNat_apply (f : Flow cap s t) {x y : V} (e : Q x y) :
    f.toNat e = (f.toFun e).toNat :=
  (rfl)

@[simp]
theorem natCast_toNat_apply (f : Flow cap s t) {x y : V} (e : Q x y) :
    (f.toNat e : ℤ) = f.toFun e :=
  Int.toNat_of_nonneg (f.nonneg e)

/-- Casting natural arrow values back to integers recovers the flow assignment. -/
@[simp]
theorem toNat_map_natCast (f : Flow cap s t) :
    f.toNat.map (fun n : ℕ ↦ (n : ℤ)) = f.toFun := by
  funext x y e
  exact f.natCast_toNat_apply e

/-- Natural arrow values determine the original integer assignment and conversely. -/
@[simp]
theorem toNat_eq_iff {c : Assignment Q ℕ} (f : Flow cap s t) :
    f.toNat = c ↔ f.toFun = c.map (Nat.castAddMonoidHom ℤ) := by
  constructor
  · rintro rfl
    exact f.toNat_map_natCast.symm
  · intro hf
    funext x y e
    simp [toNat_apply, hf]

/-- Natural and nonnegative-integer arrow values represent the same coefficient. -/
theorem toNonneg_apply_eq_natCast (f : Flow cap s t) {x y : V} (e : Q x y) :
    f.toNonneg e = (f.toNat e : Nonneg ℤ) :=
  Subtype.ext (by
    simpa only [coe_toNonneg_apply, Nonneg.coe_natCast] using
      (f.natCast_toNat_apply e).symm)

end Flow

/-- Natural arrow values are bounded by the original natural capacities. -/
theorem NatFlow.toNat_le {cap : Assignment Q ℕ} {s t : V} (f : NatFlow cap s t) :
    f.toNat ≤ cap := by
  intro x y e
  apply Int.ofNat_le.mp
  simpa only [Assignment.map_apply, Nat.coe_castAddMonoidHom] using
    (f.natCast_toNat_apply e).trans_le (f.le_upper e)

omit [Fintype V] in
/-- Casting a natural arrow sum gives the arrow sum of the integer-cast assignment. -/
@[simp]
theorem natCast_arrowSum (f : Assignment Q ℕ) (S T : Finset V) :
    ((arrowSum f S T : ℕ) : ℤ) = arrowSum (f.map (Nat.castAddMonoidHom ℤ)) S T :=
  map_arrowSum (Nat.castAddMonoidHom ℤ) f S T

/-- Max-flow/min-cut for natural capacities: a flow's integer value equals the cast natural
capacity of a terminal-separating cut. Natural arrow values are available via `Flow.toNat`,
bounded by `NatFlow.toNat_le`. -/
theorem NatFlow.exists_val_eq_arrowSum [DecidableEq V] {cap : Assignment Q ℕ} {s t : V}
    (hst : s ≠ t) :
    ∃ f : NatFlow cap s t, ∃ S : Finset V,
      s ∈ S ∧ t ∉ S ∧ f.val = ((arrowSum cap S Sᶜ : ℕ) : ℤ) := by
  obtain ⟨f, S, hs, ht, hval⟩ := Flow.exists_val_eq_arrowSum
    (cap := cap.map (Nat.castAddMonoidHom ℤ)) hst (fun _ _ e ↦ Int.natCast_nonneg (cap e))
  exact ⟨f, S, hs, ht, (natCast_arrowSum cap S Sᶜ).symm ▸ hval⟩

end Natural

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
  f.toNonneg

@[simp]
theorem Flow.coe_toNNRat_apply {cap : Assignment Q ℚ} {s t : V} (f : Flow cap s t)
    {x y : V} (e : Q x y) : (f.toNNRat e : ℚ) = f.toFun e :=
  f.coe_toNonneg_apply e

/-- Coercing nonnegative rational arrow values recovers the original assignment. -/
@[simp]
theorem Flow.toNNRat_map_coe {cap : Assignment Q ℚ} {s t : V} (f : Flow cap s t) :
    f.toNNRat.map ((↑) : ℚ≥0 → ℚ) = f.toFun :=
  f.toNonneg_map_coe

/-- The arrow values of a real flow, bundled in the named nonnegative real type. -/
def Flow.toNNReal {cap : Assignment Q ℝ} {s t : V} (f : Flow cap s t) : Assignment Q ℝ≥0 :=
  f.toNonneg

@[simp]
theorem Flow.coe_toNNReal_apply {cap : Assignment Q ℝ} {s t : V} (f : Flow cap s t)
    {x y : V} (e : Q x y) : (f.toNNReal e : ℝ) = f.toFun e :=
  f.coe_toNonneg_apply e

/-- Coercing nonnegative real arrow values recovers the original assignment. -/
@[simp]
theorem Flow.toNNReal_map_coe {cap : Assignment Q ℝ} {s t : V} (f : Flow cap s t) :
    f.toNNReal.map ((↑) : ℝ≥0 → ℝ) = f.toFun :=
  f.toNonneg_map_coe

/-- Nonnegative rational values recover the original rational assignment. -/
@[simp]
theorem Flow.toNNRat_eq_iff {cap : Assignment Q ℚ} {s t : V} (f : Flow cap s t)
    {c : Assignment Q ℚ≥0} : f.toNNRat = c ↔ f.toFun = c.map NNRat.coeHom :=
  f.toNonneg_eq_iff

/-- Nonnegative real values recover the original real assignment. -/
@[simp]
theorem Flow.toNNReal_eq_iff {cap : Assignment Q ℝ} {s t : V} (f : Flow cap s t)
    {c : Assignment Q ℝ≥0} : f.toNNReal = c ↔ f.toFun = c.map NNReal.toRealHom :=
  f.toNonneg_eq_iff

/-- Nonnegative rational arrow values respect the original capacities. -/
theorem NNRatFlow.toNNRat_le {cap : Assignment Q ℚ≥0} {s t : V} (f : NNRatFlow cap s t) :
    f.toNNRat ≤ cap :=
  NonnegFlow.toNonneg_le f

/-- Nonnegative real arrow values respect the original capacities. -/
theorem NNRealFlow.toNNReal_le {cap : Assignment Q ℝ≥0} {s t : V} (f : NNRealFlow cap s t) :
    f.toNNReal ≤ cap :=
  NonnegFlow.toNonneg_le f

omit [Fintype V] in
/-- Rational coercion commutes with arrow sums for the named nonnegative rational type. -/
@[simp]
theorem NNRat.coe_arrowSum (f : Assignment Q ℚ≥0) (S T : Finset V) :
    ((arrowSum f S T : ℚ≥0) : ℚ) = arrowSum (f.map NNRat.coeHom) S T :=
  map_arrowSum NNRat.coeHom f S T

omit [Fintype V] in
/-- Real coercion commutes with arrow sums for the named nonnegative real type. -/
@[simp]
theorem NNReal.coe_arrowSum (f : Assignment Q ℝ≥0) (S T : Finset V) :
    ((arrowSum f S T : ℝ≥0) : ℝ) = arrowSum (f.map NNReal.toRealHom) S T :=
  map_arrowSum NNReal.toRealHom f S T

/-- Max-flow/min-cut and subgroup integrality for capacities in `ℚ≥0`. -/
theorem NNRatFlow.exists_val_eq_arrowSum_mem [DecidableEq V]
    {cap : Assignment Q ℚ≥0} {s t : V} (hst : s ≠ t) (H : AddSubgroup ℚ)
    (hcapH : ∀ ⦃x y⦄ (e : Q x y), (cap e : ℚ) ∈ H) :
    ∃ f : NNRatFlow cap s t, ∃ S : Finset V,
      s ∈ S ∧ t ∉ S ∧ f.val = ((arrowSum cap S Sᶜ : ℚ≥0) : ℚ) ∧
        ∀ ⦃x y⦄ (e : Q x y), (f.toNNRat e : ℚ) ∈ H :=
  NonnegFlow.exists_val_eq_arrowSum_mem hst H hcapH

/-- Max-flow/min-cut and subgroup integrality for capacities in `ℝ≥0`. -/
theorem NNRealFlow.exists_val_eq_arrowSum_mem [DecidableEq V]
    {cap : Assignment Q ℝ≥0} {s t : V} (hst : s ≠ t) (H : AddSubgroup ℝ)
    (hcapH : ∀ ⦃x y⦄ (e : Q x y), (cap e : ℝ) ∈ H) :
    ∃ f : NNRealFlow cap s t, ∃ S : Finset V,
      s ∈ S ∧ t ∉ S ∧ f.val = ((arrowSum cap S Sᶜ : ℝ≥0) : ℝ) ∧
        ∀ ⦃x y⦄ (e : Q x y), (f.toNNReal e : ℝ) ∈ H :=
  NonnegFlow.exists_val_eq_arrowSum_mem hst H hcapH

end RationalReal

end TauCeti
