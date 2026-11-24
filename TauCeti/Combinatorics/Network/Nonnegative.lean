/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Defs
public import TauCeti.Algebra.Order.Ring.Cast
public import TauCeti.Combinatorics.Network.Coefficients
public import TauCeti.Combinatorics.Network.ShortestAugmentation
public import TauCeti.Data.Rat.Cast.Order

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

Natural capacities can also be read through `Nat.cast` in any ordered additive group `K` with
`0 ≤ 1`, such as `ℤ`, `ℚ` or `ℝ`. The flow `NatFlow.castFlow K f` over `K` is the integer flow
`f` with its coefficients changed along the integer cast by `Flow.map`; it has the same natural
arrow values, and its value is the cast of the value of `f`. Its range consists of the flows over
`K` with natural arrow values, and when `1 ≠ 0` in `K` it is injective and preserves and reflects
maximality. Changing its coefficients further along an order-preserving additive map
`φ : K →+o L` with `φ 1 = 1`, such as `Rat.castOrderAddMonoidHom ℝ : ℚ →+o ℝ`, gives the flow
over `L` with the same natural arrow values. A flow over `ℚ` with natural arrow values therefore
has the same arrow values, value and maximality as the corresponding flows over `ℤ` and `ℝ`.
Casting a maximum integer flow and its attaining natural cut gives a maximum flow over `K` with
natural arrow values whose value is the cast of a natural cut capacity. Over linearly ordered `K`
this is the case `H = AddSubgroup.zmultiples 1` of the integrality theorem
`Flow.exists_isMaximum_mem`; casting the integer case needs no linear order on `K`.

## Main definitions

* `TauCeti.NatFlow.castFlow K f`: the flow over `K` with the natural arrow values of the integer
  flow `f`.

## Main results

* `TauCeti.NatFlow.exists_castFlow_eq_iff`: a flow over `K` comes from an integer flow exactly
  when its arrow values are natural numbers.
* `TauCeti.NatFlow.isMaximum_castFlow_iff`: `TauCeti.NatFlow.castFlow K` preserves and reflects
  maximality.
* `TauCeti.NatFlow.congr_map_castFlow`: changing coefficients along `K →+o L` takes
  `castFlow K f` to `castFlow L f`.
* `TauCeti.Flow.exists_isMaximum_eq_natCast`: for natural capacities, some maximum flow over `K`
  has natural arrow values.
* `TauCeti.Flow.exists_eq_natCast_val_eq_arrowSum`: max-flow/min-cut for natural capacities over
  `K`, with natural arrow values and a natural cut capacity.
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

/-! ### Natural capacities over ordered coefficient groups -/

/-- Reading natural values in `K` and then applying an additive map `φ` with `φ 1 = 1` reads them
in `L`. -/
theorem Assignment.map_map_natCast {L F : Type*} [AddMonoidWithOne K] [AddMonoidWithOne L]
    [FunLike F K L] [AddMonoidHomClass F K L] (φ : F) (hφ : φ 1 = 1) (a : Assignment Q ℕ) :
    (a.map (Nat.cast : ℕ → K)).map φ = a.map Nat.cast := by
  funext x y e
  exact map_natCast' φ hφ (a e)

section NaturalCoefficients

variable [Fintype V] [∀ v w, Fintype (Q v w)]
variable [AddCommGroupWithOne K] [PartialOrder K] [IsOrderedAddMonoid K] [ZeroLEOneClass K]
variable {cap : Assignment Q ℕ} {s t : V}

namespace NatFlow

variable (K) in
/-- The ordinary flow for the natural capacities `cap` read in `K` whose arrow values are the
natural arrow values of the integer flow `f`. It is `TauCeti.Flow.map` along the integer cast,
with the mapped capacities written as `cap.map Nat.cast`. -/
def castFlow (f : NatFlow cap s t) : Flow (cap.map (Nat.cast : ℕ → K)) s t :=
  Flow.congr (cap.map_map_natCast (Int.castOrderAddMonoidHom K) (by simp)) rfl rfl
    (f.map (Int.castOrderAddMonoidHom K))

/-- `f.castFlow K` is the image of `f` under the integer cast, with its capacities rewritten. -/
theorem castFlow_eq_congr_map (f : NatFlow cap s t) :
    f.castFlow K = Flow.congr (cap.map_map_natCast (Int.castOrderAddMonoidHom K) (by simp))
      rfl rfl (f.map (Int.castOrderAddMonoidHom K)) :=
  (rfl)

/-- The arrow values of `f.castFlow K` are the casts of the integer arrow values of `f`. -/
theorem castFlow_toFun_apply (f : NatFlow cap s t) {x y : V} (e : Q x y) :
    (f.castFlow K).toFun e = (f.toFun e : K) := by
  simp only [castFlow_eq_congr_map, Flow.toBoundedFlow_congr, BoundedFlow.congr_apply_toFun,
    Flow.map_toFun, Assignment.map_apply, Int.coe_castOrderAddMonoidHom]

@[simp]
theorem castFlow_toFun (f : NatFlow cap s t) :
    (f.castFlow K).toFun = f.natAssignment.map Nat.cast := by
  funext x y e
  rw [castFlow_toFun_apply, Assignment.map_apply, ← f.coe_natAssignment e, Int.cast_natCast]

/-- The value of `f.castFlow K` is the cast of the integer value of `f`. -/
@[simp]
theorem val_castFlow (f : NatFlow cap s t) : (f.castFlow K).val = (f.val : K) := by
  rw [castFlow_eq_congr_map (K := K), Flow.toBoundedFlow_congr, BoundedFlow.val_congr]
  exact (Flow.val_map _ f).trans (congrFun (Int.coe_castOrderAddMonoidHom K) f.val)

/-- Over `ℤ`, `TauCeti.NatFlow.castFlow` returns the integer flow itself. -/
@[simp]
theorem castFlow_int (f : NatFlow cap s t) : f.castFlow ℤ = f :=
  Flow.ext <| funext fun _ ↦ funext fun _ ↦ funext fun e ↦ by
    rw [castFlow_toFun_apply, Int.cast_id]

/-- A flow over `K` for natural capacities comes from an integer flow exactly when its arrow values
are natural numbers. -/
theorem exists_castFlow_eq_iff {g : Flow (cap.map (Nat.cast : ℕ → K)) s t} :
    (∃ f : NatFlow cap s t, f.castFlow K = g) ↔ ∃ a : Assignment Q ℕ, g.toFun = a.map Nat.cast := by
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨f.natAssignment, hf ▸ castFlow_toFun f⟩, fun ⟨a, ha⟩ ↦ ?_⟩
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
    simpa [ha, Assignment.map_map, Function.comp_def] using map_excessAt (Int.castAddHom K)
      (a.map (Nat.cast : ℕ → ℤ)) v
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

/-- The flow over `K` with the natural arrow values of a maximum integer flow is maximum. -/
theorem isMaximum_castFlow {f : NatFlow cap s t} (hf : f.IsMaximum) :
    (f.castFlow K).IsMaximum := by
  rcases eq_or_ne s t with rfl | hst
  · exact Flow.isMaximum_iff.2 fun g ↦
      (BoundedFlow.val_eq_zero_of_eq rfl _).trans_le (BoundedFlow.val_eq_zero_of_eq rfl _).ge
  rw [castFlow_eq_congr_map, Flow.isMaximum_congr_iff]
  exact hf.map hst _

/-- When `1 ≠ 0` in `K`, an integer flow for natural capacities is maximum exactly when the flow
over `K` with the same natural arrow values is maximum. -/
theorem isMaximum_castFlow_iff [NeZero (1 : K)] {f : NatFlow cap s t} :
    (f.castFlow K).IsMaximum ↔ f.IsMaximum := by
  refine ⟨fun hf ↦ Flow.isMaximum_iff.2 fun g ↦ ?_, isMaximum_castFlow⟩
  have hg := Flow.isMaximum_iff.1 hf (castFlow K g)
  rwa [val_castFlow, val_castFlow, Int.cast_le] at hg

/-- Changing the coefficients of `f.castFlow K` along an order-preserving additive map
`φ : K →+o L` with `φ 1 = 1`, such as the rational cast from `ℚ` to `ℝ`, gives `f.castFlow L`. -/
theorem congr_map_castFlow {L : Type*} [AddCommGroupWithOne L] [PartialOrder L]
    [IsOrderedAddMonoid L] [ZeroLEOneClass L] (φ : K →+o L) (hφ : φ 1 = 1) (f : NatFlow cap s t) :
    Flow.congr (cap.map_map_natCast φ hφ) rfl rfl ((f.castFlow K).map φ) = f.castFlow L :=
  Flow.ext <| funext fun _ ↦ funext fun _ ↦ funext fun e ↦ by
    simp only [Flow.toBoundedFlow_congr, BoundedFlow.congr_apply_toFun, Flow.map_toFun,
      Assignment.map_apply, castFlow_toFun_apply, map_intCast' φ hφ]

end NatFlow

namespace Flow

variable (cap)

/-- **Integrality for natural capacities.** For natural capacities read in an ordered additive
group `K` with `0 ≤ 1`, such as `ℤ`, `ℚ` or `ℝ`, some maximum ordinary flow has natural arrow
values: the flow over `K` with the arrow values of a maximum integer flow. -/
theorem exists_isMaximum_eq_natCast :
    ∃ (f : Flow (cap.map (Nat.cast : ℕ → K)) s t) (a : Assignment Q ℕ),
      f.IsMaximum ∧ f.toFun = a.map Nat.cast := by
  obtain ⟨f, hf⟩ := exists_isMaximum (cap := cap.map (Nat.cast : ℕ → ℤ)) (s := s) (t := t)
    fun _ _ e ↦ Int.natCast_nonneg (cap e)
  exact ⟨NatFlow.castFlow K f, f.natAssignment, NatFlow.isMaximum_castFlow hf,
    NatFlow.castFlow_toFun f⟩

/-- **Max-flow/min-cut for natural capacities.** For natural capacities read in an ordered
additive group `K` with `0 ≤ 1` and distinct terminals, some ordinary flow over `K` with natural
arrow values has value equal to the cast of the natural capacity of the arrows leaving some vertex
set containing `s` but not `t`. -/
theorem exists_eq_natCast_val_eq_arrowSum [DecidableEq V] (hst : s ≠ t) :
    ∃ (f : Flow (cap.map (Nat.cast : ℕ → K)) s t) (a : Assignment Q ℕ) (S : Finset V),
      f.toFun = a.map Nat.cast ∧ s ∈ S ∧ t ∉ S ∧ f.val = ((arrowSum cap S Sᶜ : ℕ) : K) := by
  obtain ⟨f, S, hs, ht, hS⟩ := NatFlow.exists_val_eq_coe_arrowSum cap hst
  exact ⟨NatFlow.castFlow K f, f.natAssignment, S, NatFlow.castFlow_toFun f, hs, ht,
    by rw [NatFlow.val_castFlow, hS, Int.cast_natCast]⟩

end Flow

end NaturalCoefficients

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

/-! The following examples read the same capacities `3` in `ℚ` and in `ℝ`. A maximum flow over `ℝ`
with natural arrow values has value `6`. A maximum flow over `ℚ` with natural arrow values comes
from an integer flow; casting it to `ℝ` gives the flow over `ℝ` with the same natural arrow
values, which is again maximum, with the same value. -/

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
      f.castFlow ℚ = g ∧
      Flow.congr (Assignment.map_map_natCast (Rat.castOrderAddMonoidHom ℝ) (by simp) _) rfl rfl
        (g.map (Rat.castOrderAddMonoidHom ℝ)) = f.castFlow ℝ ∧
      (f.castFlow ℝ).IsMaximum ∧ (f.castFlow ℝ).val = g.val := by
  obtain ⟨f, rfl⟩ := NatFlow.exists_castFlow_eq_iff.2 ⟨a, ha⟩
  refine ⟨f, rfl, NatFlow.congr_map_castFlow _ (by simp) f,
    NatFlow.isMaximum_castFlow (NatFlow.isMaximum_castFlow_iff.1 hg), ?_⟩
  simp

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
