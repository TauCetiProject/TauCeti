/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Shift
public import TauCeti.Combinatorics.Network.AuxiliaryTerminals
public import TauCeti.Combinatorics.Network.ShortestAugmentation
import TauCeti.Algebra.Order.BigOperators.Sum.PosPart

/-!
# Hoffman's feasibility theorem

An assignment between signed lower and upper bounds with prescribed excess exists precisely when
the prescribed excess is balanced and every vertex set satisfies the corresponding cut inequality.
The result includes additive-subgroup integrality and strict cut certificates of infeasibility.

The auxiliary-terminal reduction first subtracts the lower bound. For nonnegative capacities and
prescribed excess `b`, the fresh source supplies `max (-b v) 0` to each vertex and each vertex sends
`max (b v) 0` to the fresh sink. A flow of the required value saturates both families of new arrows.
The construction retains every original arrow, including parallel arrows and loops.

## References

* D. P. Bertsekas, *Linear Network Optimization*, Section 1.1.3 and Exercises 2.4–2.6.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Volume A.
-/

public section

namespace TauCeti

open Finset Sum

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}
variable [Fintype V] [∀ x y, Fintype (Q x y)]
variable [AddCommGroup K]

namespace ExcessFlow

variable [Preorder K] {lo hi : Assignment Q K} {b : V → K}

/-- Prescribed excess of a feasible assignment has total zero. -/
theorem sum_eq_zero (f : ExcessFlow lo hi b) : ∑ v, b v = 0 := by
  simpa only [← f.property.2] using sum_excessAt f.val

end ExcessFlow

namespace ExcessFlow

variable [PartialOrder K] [IsOrderedAddMonoid K] [DecidableEq V]
variable {lo hi : Assignment Q K} {b : V → K}

/-- Every feasible prescribed-excess assignment satisfies the incoming cut inequality. -/
theorem sum_add_arrowSum_le (f : ExcessFlow lo hi b) (S : Finset V) :
    (∑ v ∈ S, b v) + arrowSum lo S Sᶜ ≤ arrowSum hi Sᶜ S := by
  have hex : ∑ v ∈ S, b v = arrowSum f.val Sᶜ S - arrowSum f.val S Sᶜ := by
    simpa only [← f.property.2] using sum_excessAt_eq_arrowSum_sub f.val S
  rw [hex, sub_add_eq_add_sub, sub_le_iff_le_add]
  exact add_le_add (arrowSum_mono f.mem_Icc.2 Sᶜ S) (arrowSum_mono f.mem_Icc.1 S Sᶜ)

end ExcessFlow

variable [LinearOrder K] [IsOrderedAddMonoid K] [DecidableEq V]

/-- Capacities for the auxiliary-terminal reduction of prescribed excess with zero lower bounds.
The source supplies the negative part of `b`, and the sink receives its positive part. -/
def excessCapacity (cap : Assignment Q K) (b : V → K) :
    Assignment (AuxTerminalHom Q univ univ) K :=
  auxTerminalCapacity cap (fun v ↦ max (-b v) 0) (fun v ↦ max (b v) 0)

omit [∀ x y, Fintype (Q x y)] [IsOrderedAddMonoid K] [DecidableEq V] in
/-- The auxiliary capacities are nonnegative when the original capacities are. -/
theorem excessCapacity_nonneg {cap : Assignment Q K} (hcap : 0 ≤ cap) (b : V → K) :
    0 ≤ excessCapacity cap b :=
  auxTerminalCapacity_nonneg hcap (fun _ _ ↦ le_max_right _ _) (fun _ _ ↦ le_max_right _ _)

omit [∀ x y, Fintype (Q x y)] [IsOrderedAddMonoid K] [DecidableEq V] in
@[simp]
theorem excessCapacity_original (cap : Assignment Q K) (b : V → K) {x y : V} (e : Q x y) :
    excessCapacity cap b (AuxTerminalHom.original e) = cap e :=
  auxTerminalCapacity_original _ _ _ e

omit [∀ x y, Fintype (Q x y)] [IsOrderedAddMonoid K] [DecidableEq V] in
@[simp]
theorem excessCapacity_source (cap : Assignment Q K) (b : V → K) (x : V) :
    excessCapacity cap b (AuxTerminalHom.source (mem_univ x)) = max (-b x) 0 :=
  auxTerminalCapacity_source _ _ _ (mem_univ x)

omit [∀ x y, Fintype (Q x y)] [IsOrderedAddMonoid K] [DecidableEq V] in
@[simp]
theorem excessCapacity_sink (cap : Assignment Q K) (b : V → K) (x : V) :
    excessCapacity cap b (AuxTerminalHom.sink (mem_univ x)) = max (b x) 0 :=
  auxTerminalCapacity_sink _ _ _ (mem_univ x)

omit [∀ x y, Fintype (Q x y)] [IsOrderedAddMonoid K] [DecidableEq V] in
/-- The auxiliary capacities preserve an additive subgroup containing capacities and excesses. -/
theorem excessCapacity_mem {cap : Assignment Q K} {b : V → K} (H : AddSubgroup K)
    (hcap : ∀ ⦃x y⦄ (e : Q x y), cap e ∈ H) (hb : ∀ v, b v ∈ H) :
    ∀ ⦃x y⦄ (e : AuxTerminalHom Q univ univ x y), excessCapacity cap b e ∈ H := by
  refine AuxTerminalHom.forall_iff.2 ?_
  refine ⟨fun _ _ e ↦ by simpa using hcap e, fun x _ ↦ ?_, fun x _ ↦ ?_⟩
  · simpa only [excessCapacity, auxTerminalCapacity_source] using
      (max_rec' (· ∈ H) (H.neg_mem (hb x)) H.zero_mem : max (-b x) 0 ∈ H)
  · simpa only [excessCapacity, auxTerminalCapacity_sink] using
      (max_rec' (· ∈ H) (hb x) H.zero_mem : max (b x) 0 ∈ H)

namespace ExcessFlow

variable {cap : Assignment Q K} {b : V → K}

/-- Extend a zero-lower-bound prescribed-excess assignment to an ordinary auxiliary flow.
Both auxiliary arrows at each original vertex are saturated. -/
def toAuxFlow (f : ExcessFlow 0 cap b) :
    Flow (excessCapacity cap b) (inr false) (inr true) where
  toFun := auxTerminalCapacity f.val (fun v ↦ max (-b v) 0) (fun v ↦ max (b v) 0)
  mem_Icc := ⟨auxTerminalCapacity_nonneg f.mem_Icc.1
    (fun _ _ ↦ le_max_right _ _) (fun _ _ ↦ le_max_right _ _),
    AuxTerminalHom.forall_iff.2 ⟨fun _ _ e ↦ by simpa [excessCapacity] using f.mem_Icc.2 _ _ e,
      fun _ _ ↦ by simp [excessCapacity], fun _ _ ↦ by simp [excessCapacity]⟩⟩
  conserve
    | inl v, _, _ => by
      rw [AuxTerminalHom.excessAt_inl, auxTerminalRestrict_auxTerminalCapacity,
        sum_auxTerminalCapacity_source, sum_auxTerminalCapacity_sink]
      simp only [mem_univ, ↓reduceIte, f.excessAt_eq]
      exact sub_eq_zero.2 (eq_add_of_sub_eq (max_zero_sub_max_neg_zero_eq_self (b v))).symm
    | inr false, h, _ => (h rfl).elim
    | inr true, _, h => (h rfl).elim
  excessAt_sink_nonneg := by
    rw [AuxTerminalHom.excessAt_inr_true]
    simp only [sum_auxTerminalCapacity_sink, mem_univ, ↓reduceIte]
    exact sum_nonneg fun _ _ ↦ le_max_right _ _

@[simp]
theorem toAuxFlow_original (f : ExcessFlow 0 cap b) {x y : V} (e : Q x y) :
    f.toAuxFlow.toFun (AuxTerminalHom.original e) = f.val e := by
  simp [toAuxFlow]

@[simp]
theorem toAuxFlow_source (f : ExcessFlow 0 cap b) (x : V) :
    f.toAuxFlow.toFun (AuxTerminalHom.source (mem_univ x)) = max (-b x) 0 := by
  simp [toAuxFlow]

@[simp]
theorem toAuxFlow_sink (f : ExcessFlow 0 cap b) (x : V) :
    f.toAuxFlow.toFun (AuxTerminalHom.sink (mem_univ x)) = max (b x) 0 := by
  simp [toAuxFlow]

/-- The auxiliary flow has the total positive prescribed excess as its value. -/
@[simp]
theorem val_toAuxFlow (f : ExcessFlow 0 cap b) : f.toAuxFlow.val = ∑ v, max (b v) 0 := by
  rw [BoundedFlow.val_def, AuxTerminalHom.excessAt_inr_true]
  simp only [AuxTerminalHom.sum_sink (mem_univ _), toAuxFlow_sink]

/-- Extending a prescribed-excess assignment preserves subgroup values in both directions. -/
theorem toAuxFlow_mem_iff (f : ExcessFlow 0 cap b) (H : AddSubgroup K) (hb : ∀ v, b v ∈ H) :
    (∀ ⦃x y⦄ (e : AuxTerminalHom Q univ univ x y), f.toAuxFlow.toFun e ∈ H) ↔
      ∀ ⦃x y⦄ (e : Q x y), f.val e ∈ H := by
  refine ⟨fun h _ _ e ↦ by simpa using h (AuxTerminalHom.original e), fun h ↦ ?_⟩
  simpa only [toAuxFlow, excessCapacity] using excessCapacity_mem H h hb

end ExcessFlow

namespace Flow

variable {cap : Assignment Q K} {b : V → K}

/-- The value of an auxiliary flow is bounded by the total positive prescribed excess. -/
theorem val_le_sum_max (g : Flow (excessCapacity cap b) (inr false) (inr true)) :
    g.val ≤ ∑ v, max (b v) 0 := by
  rw [BoundedFlow.val_def, AuxTerminalHom.excessAt_inr_true]
  exact sum_le_sum fun v _ ↦ by
    rw [AuxTerminalHom.sum_sink (mem_univ v)]
    simpa using g.le_upper (AuxTerminalHom.sink (mem_univ v))

/-- At the required value every arrow to the fresh sink is saturated. -/
theorem sink_eq_of_val_eq_sum_max
    (g : Flow (excessCapacity cap b) (inr false) (inr true))
    (hg : g.val = ∑ v, max (b v) 0) (v : V) :
    g.toFun (AuxTerminalHom.sink (mem_univ v)) = max (b v) 0 := by
  rw [BoundedFlow.val_def, AuxTerminalHom.excessAt_inr_true] at hg
  simp only [AuxTerminalHom.sum_sink (mem_univ _)] at hg
  exact (sum_eq_sum_iff_of_le fun x _ ↦
    (by simpa using g.le_upper (AuxTerminalHom.sink (mem_univ x)))).1 hg v (mem_univ v)

/-- For balanced excess, the required value saturates every arrow from the fresh source. -/
theorem source_eq_of_val_eq_sum_max
    (g : Flow (excessCapacity cap b) (inr false) (inr true))
    (hb : ∑ v, b v = 0) (hg : g.val = ∑ v, max (b v) 0) (v : V) :
    g.toFun (AuxTerminalHom.source (mem_univ v)) = max (-b v) 0 := by
  have hs := g.excessAt_source
  have he : excessAt g.toFun (inr false) =
      -(∑ x, g.toFun (AuxTerminalHom.source (mem_univ x))) := by
    simp [excessAt_def, Fintype.sum_sum_type,
      AuxTerminalHom.sum_source (mem_univ _)]
  rw [he, hg, neg_inj, ← sum_max_neg_eq_sum_max univ b hb] at hs
  exact (sum_eq_sum_iff_of_le fun x _ ↦
    (by simpa using g.le_upper (AuxTerminalHom.source (mem_univ x)))).1 hs v (mem_univ v)

/-- For balanced excess, an auxiliary flow has the required value exactly when both families
of auxiliary arrows are saturated. -/
theorem val_eq_sum_max_iff
    (g : Flow (excessCapacity cap b) (inr false) (inr true)) (hb : ∑ v, b v = 0) :
    g.val = ∑ v, max (b v) 0 ↔
      (∀ v, g.toFun (AuxTerminalHom.source (mem_univ v)) = max (-b v) 0) ∧
      ∀ v, g.toFun (AuxTerminalHom.sink (mem_univ v)) = max (b v) 0 := by
  refine ⟨fun hg ↦ ⟨g.source_eq_of_val_eq_sum_max hb hg, g.sink_eq_of_val_eq_sum_max hg⟩,
    fun h ↦ ?_⟩
  rw [BoundedFlow.val_def, AuxTerminalHom.excessAt_inr_true]
  simp only [AuxTerminalHom.sum_sink (mem_univ _), h.2]

/-- Restricting a balanced auxiliary flow of the required value realizes its prescribed excess. -/
def toExcessFlow (g : Flow (excessCapacity cap b) (inr false) (inr true))
    (hb : ∑ v, b v = 0) (hg : g.val = ∑ v, max (b v) 0) : ExcessFlow 0 cap b :=
  ⟨auxTerminalRestrict g.toFun,
    ⟨fun _ _ e ↦ by simpa using g.nonneg (AuxTerminalHom.original e),
      fun _ _ e ↦ by simpa using g.le_upper (AuxTerminalHom.original e)⟩, by
    funext v
    have h := g.conserve (inl v) inl_ne_inr inl_ne_inr
    rw [AuxTerminalHom.excessAt_inl, AuxTerminalHom.sum_source (mem_univ v),
      AuxTerminalHom.sum_sink (mem_univ v), g.source_eq_of_val_eq_sum_max hb hg,
      g.sink_eq_of_val_eq_sum_max hg] at h
    exact (eq_sub_of_add_eq (eq_of_sub_eq_zero h)).trans
      (max_zero_sub_max_neg_zero_eq_self (b v))⟩

@[simp]
theorem toExcessFlow_apply (g : Flow (excessCapacity cap b) (inr false) (inr true))
    (hb : ∑ v, b v = 0) (hg : g.val = ∑ v, max (b v) 0) {x y : V} (e : Q x y) :
    (g.toExcessFlow hb hg).val e = g.toFun (AuxTerminalHom.original e) :=
  auxTerminalRestrict_apply _ e

end Flow

namespace ExcessFlow

variable {lo hi : Assignment Q K} {b : V → K}

variable {cap : Assignment Q K}

/-- Realizing prescribed excess is equivalent to an ordinary auxiliary flow of the required
value. Restriction and extension preserve all original arrow values. -/
def zeroAuxFlowEquiv (hb : ∑ v, b v = 0) :
    ExcessFlow 0 cap b ≃
      {g : Flow (excessCapacity cap b) (inr false) (inr true) //
        g.val = ∑ v, max (b v) 0} where
  toFun f := ⟨f.toAuxFlow, f.val_toAuxFlow⟩
  invFun g := g.val.toExcessFlow hb g.property
  left_inv f := by
    apply Subtype.ext
    funext x y e
    simp
  right_inv g := by
    apply Subtype.ext
    apply Flow.ext
    exact funext₃ (AuxTerminalHom.forall_iff.2
      ⟨fun _ _ e ↦ by simp, fun x _ ↦ by
        simpa using (g.val.source_eq_of_val_eq_sum_max hb g.property x).symm,
        fun x _ ↦ by
        simpa using (g.val.sink_eq_of_val_eq_sum_max g.property x).symm⟩)

@[simp]
theorem zeroAuxFlowEquiv_apply_val (hb : ∑ v, b v = 0) (f : ExcessFlow 0 cap b) :
    (zeroAuxFlowEquiv hb f).val = f.toAuxFlow :=
  (rfl)

@[simp]
theorem zeroAuxFlowEquiv_symm_apply (hb : ∑ v, b v = 0)
    (g : {g : Flow (excessCapacity cap b) (inr false) (inr true) //
      g.val = ∑ v, max (b v) 0}) :
    (zeroAuxFlowEquiv hb).symm g = g.val.toExcessFlow hb g.property :=
  (rfl)

/-- Restriction after extension recovers the original prescribed-excess assignment. -/
@[simp]
theorem toAuxFlow_toExcessFlow (hb : ∑ v, b v = 0) (f : ExcessFlow 0 cap b) :
    f.toAuxFlow.toExcessFlow hb f.val_toAuxFlow = f :=
  (zeroAuxFlowEquiv hb).symm_apply_apply f

/-- Subtracting the lower bound gives an equivalence with ordinary auxiliary flows of the
required value for the shifted excess. The lower bound need not itself be feasible. -/
def auxFlowEquiv (lo hi : Assignment Q K) (b : V → K) (hb : ∑ v, b v = 0) :
    ExcessFlow lo hi b ≃
      {g : Flow (excessCapacity (hi - lo) (b - excessAt lo)) (inr false) (inr true) //
        g.val = ∑ v, max ((b - excessAt lo) v) 0} :=
  (shiftLowerEquiv lo hi b).trans (zeroAuxFlowEquiv (by
    simp only [Pi.sub_apply, sum_sub_distrib, sum_excessAt, sub_zero, hb]))

@[simp]
theorem auxFlowEquiv_apply_original (hb : ∑ v, b v = 0) (f : ExcessFlow lo hi b)
    {x y : V} (e : Q x y) :
    (auxFlowEquiv lo hi b hb f).val.toFun (AuxTerminalHom.original e) = f.val e - lo e := by
  simp [auxFlowEquiv]

@[simp]
theorem auxFlowEquiv_symm_apply_original (hb : ∑ v, b v = 0)
    (g : {g : Flow (excessCapacity (hi - lo) (b - excessAt lo)) (inr false) (inr true) //
      g.val = ∑ v, max ((b - excessAt lo) v) 0}) {x y : V} (e : Q x y) :
    ((auxFlowEquiv lo hi b hb).symm g).val e =
      g.val.toFun (AuxTerminalHom.original e) + lo e := by
  simp [auxFlowEquiv]

@[simp]
theorem auxFlowEquiv_apply_source (hb : ∑ v, b v = 0) (f : ExcessFlow lo hi b) (x : V) :
    (auxFlowEquiv lo hi b hb f).val.toFun (AuxTerminalHom.source (mem_univ x)) =
      max (-((b - excessAt lo) x)) 0 := by
  simp [auxFlowEquiv]

@[simp]
theorem auxFlowEquiv_apply_sink (hb : ∑ v, b v = 0) (f : ExcessFlow lo hi b) (x : V) :
    (auxFlowEquiv lo hi b hb f).val.toFun (AuxTerminalHom.sink (mem_univ x)) =
      max ((b - excessAt lo) x) 0 := by
  simp [auxFlowEquiv]

/-- The signed auxiliary reduction preserves subgroup values in both directions. -/
theorem auxFlowEquiv_mem_iff (hb : ∑ v, b v = 0) (f : ExcessFlow lo hi b)
    (H : AddSubgroup K) (hloH : ∀ ⦃x y⦄ (e : Q x y), lo e ∈ H) (hbH : ∀ v, b v ∈ H) :
    (∀ ⦃x y⦄ (e : AuxTerminalHom Q univ univ x y),
      (auxFlowEquiv lo hi b hb f).val.toFun e ∈ H) ↔
        ∀ ⦃x y⦄ (e : Q x y), f.val e ∈ H := by
  rw [auxFlowEquiv, Equiv.trans_apply, zeroAuxFlowEquiv_apply_val,
    toAuxFlow_mem_iff _ H (fun v ↦ H.sub_mem (hbH v) (excessAt_mem hloH v))]
  exact forall_congr' fun x ↦ forall_congr' fun y ↦ forall_congr' fun e ↦ by
    rw [shiftLowerEquiv_apply_val]
    exact Assignment.sub_apply_mem_iff e (hloH e)

end ExcessFlow

/-- Extension after restriction recovers an auxiliary flow of the required value. -/
@[simp]
theorem Flow.toExcessFlow_toAuxFlow {cap : Assignment Q K} {b : V → K}
    (g : Flow (excessCapacity cap b) (inr false) (inr true))
    (hb : ∑ v, b v = 0) (hg : g.val = ∑ v, max (b v) 0) :
    (g.toExcessFlow hb hg).toAuxFlow = g :=
  congrArg Subtype.val ((ExcessFlow.zeroAuxFlowEquiv hb).apply_symm_apply ⟨g, hg⟩)

/-- Every auxiliary terminal cut has at least the required value when every original cut satisfies
the prescribed-excess inequality. -/
theorem sum_max_le_arrowSum_excessCapacity {cap : Assignment Q K} {b : V → K}
    (hb : ∑ v, b v = 0)
    (hcut : ∀ S : Finset V, ∑ v ∈ S, b v ≤ arrowSum cap Sᶜ S)
    {S : Finset (V ⊕ Bool)} (hσ : inr false ∈ S) (hτ : inr true ∉ S) :
    (∑ v, max (b v) 0) ≤ arrowSum (excessCapacity cap b) S Sᶜ := by
  rw [excessCapacity, arrowSum_auxTerminalCapacity _ _ _ hσ hτ]
  simp only [← compl_eq_univ_sdiff, univ_inter]
  have hbalance : ∑ v ∈ S.toLeftᶜ, b v = -(∑ v ∈ S.toLeft, b v) := by
    rw [eq_neg_iff_add_eq_zero, sum_compl_add_sum]
    exact hb
  have hc := hcut S.toLeftᶜ
  rw [compl_compl, hbalance] at hc
  have hparts : (∑ v ∈ S.toLeft, max (b v) 0) -
      ∑ v ∈ S.toLeft, max (-b v) 0 = ∑ v ∈ S.toLeft, b v := by
    simp only [← sum_sub_distrib, max_zero_sub_max_neg_zero_eq_self]
  calc
    (∑ v, max (b v) 0) =
        (∑ v ∈ S.toLeftᶜ, max (-b v) 0) + ∑ v ∈ S.toLeft, max (-b v) 0 := by
      rw [sum_compl_add_sum, sum_max_neg_eq_sum_max univ b hb]
    _ ≤ (∑ v ∈ S.toLeftᶜ, max (-b v) 0) +
        ((∑ v ∈ S.toLeft, max (b v) 0) + arrowSum cap S.toLeft S.toLeftᶜ) := by
      apply add_le_add le_rfl
      rw [← hparts, neg_sub] at hc
      exact sub_le_iff_le_add'.1 hc
    _ = _ := (add_assoc _ _ _).symm

namespace ExcessFlow

variable {lo hi cap : Assignment Q K} {b : V → K}

/-- Nonnegative capacities and balanced prescribed excess admit a subgroup-valued realization
whenever every cut can supply its prescribed demand. -/
theorem exists_mem_of_forall_cut_zero (hcap : 0 ≤ cap) (hb : ∑ v, b v = 0)
    (hcut : ∀ S : Finset V, ∑ v ∈ S, b v ≤ arrowSum cap Sᶜ S)
    (H : AddSubgroup K) (hcapH : ∀ ⦃x y⦄ (e : Q x y), cap e ∈ H) (hbH : ∀ v, b v ∈ H) :
    ∃ f : ExcessFlow 0 cap b, ∀ ⦃x y⦄ (e : Q x y), f.val e ∈ H := by
  obtain ⟨g, hg, hgH⟩ := Flow.exists_isMaximum_mem
    (s := inr false) (t := inr true) (excessCapacity_nonneg hcap b) H
    (excessCapacity_mem H hcapH hbH)
  obtain ⟨S, hσ, hτ, hS⟩ := hg.exists_val_eq_arrowSum (by simp)
  have hval : g.val = ∑ v, max (b v) 0 := le_antisymm g.val_le_sum_max
    (hS ▸ sum_max_le_arrowSum_excessCapacity hb hcut hσ hτ)
  exact ⟨g.toExcessFlow hb hval, fun _ _ e ↦ by simpa using hgH (AuxTerminalHom.original e)⟩

/-- **Integrality of prescribed-excess feasibility.** Signed bounds and prescribed excess in
an additive subgroup have a realization in that subgroup if the balance and cut conditions hold. -/
theorem exists_mem_of_forall_cut (hlo : lo ≤ hi) (hb : ∑ v, b v = 0)
    (hcut : ∀ S : Finset V, (∑ v ∈ S, b v) + arrowSum lo S Sᶜ ≤ arrowSum hi Sᶜ S)
    (H : AddSubgroup K) (hloH : ∀ ⦃x y⦄ (e : Q x y), lo e ∈ H)
    (hhiH : ∀ ⦃x y⦄ (e : Q x y), hi e ∈ H) (hbH : ∀ v, b v ∈ H) :
    ∃ f : ExcessFlow lo hi b, ∀ ⦃x y⦄ (e : Q x y), f.val e ∈ H := by
  have hcap : 0 ≤ hi - lo := sub_nonneg.2 hlo
  have hbalance : ∑ v, (b - excessAt lo) v = 0 := by
    simp only [Pi.sub_apply, sum_sub_distrib, sum_excessAt, sub_zero, hb]
  have hcuts (S : Finset V) :
      ∑ v ∈ S, (b - excessAt lo) v ≤ arrowSum (hi - lo) Sᶜ S := by
    simp only [Pi.sub_apply, sum_sub_distrib, sum_excessAt_eq_arrowSum_sub, arrowSum_sub]
    convert sub_le_sub_right (hcut S) (arrowSum lo Sᶜ S) using 1; abel
  obtain ⟨f, hf⟩ := exists_mem_of_forall_cut_zero hcap hbalance hcuts H
    (fun _ _ e ↦ H.sub_mem (hhiH e) (hloH e))
    (fun v ↦ H.sub_mem (hbH v) (excessAt_mem hloH v))
  refine ⟨(shiftLowerEquiv lo hi b).symm f, fun x y e ↦ ?_⟩
  rw [shiftLowerEquiv_symm_apply_val]
  exact H.add_mem (hf e) (hloH e)

/-- **Generalized Hoffman's theorem.** Ordered signed bounds admit an assignment of prescribed
excess exactly when that excess is balanced and every cut can supply its demand. -/
theorem nonempty_iff (hlo : lo ≤ hi) :
    Nonempty (ExcessFlow lo hi b) ↔ (∑ v, b v = 0) ∧
      ∀ S : Finset V, (∑ v ∈ S, b v) + arrowSum lo S Sᶜ ≤ arrowSum hi Sᶜ S := by
  refine ⟨fun ⟨f⟩ ↦ ⟨f.sum_eq_zero, f.sum_add_arrowSum_le⟩, fun ⟨hb, hc⟩ ↦ ?_⟩
  obtain ⟨f, _⟩ := exists_mem_of_forall_cut hlo hb hc ⊤
    (fun _ _ _ ↦ AddSubgroup.mem_top _) (fun _ _ _ ↦ AddSubgroup.mem_top _)
    (fun _ ↦ AddSubgroup.mem_top _)
  exact ⟨f⟩

/-- Subgroup-valued feasibility has the same balance and cut criterion as unrestricted
feasibility when both bounds and prescribed excess take values in the subgroup. -/
theorem exists_mem_iff (hlo : lo ≤ hi) (H : AddSubgroup K)
    (hloH : ∀ ⦃x y⦄ (e : Q x y), lo e ∈ H)
    (hhiH : ∀ ⦃x y⦄ (e : Q x y), hi e ∈ H) (hbH : ∀ v, b v ∈ H) :
    (∃ f : ExcessFlow lo hi b, ∀ ⦃x y⦄ (e : Q x y), f.val e ∈ H) ↔
      (∑ v, b v = 0) ∧
        ∀ S : Finset V, (∑ v ∈ S, b v) + arrowSum lo S Sᶜ ≤ arrowSum hi Sᶜ S :=
  ⟨fun ⟨f, _⟩ ↦ ⟨f.sum_eq_zero, f.sum_add_arrowSum_le⟩,
    fun ⟨hb, hc⟩ ↦ exists_mem_of_forall_cut hlo hb hc H hloH hhiH hbH⟩

/-- An infeasible prescribed-excess problem has either nonzero total excess or a strictly
violating vertex set. Conversely, either certificate rules out every feasible assignment. -/
theorem not_nonempty_iff (hlo : lo ≤ hi) :
    ¬Nonempty (ExcessFlow lo hi b) ↔ (∑ v, b v ≠ 0) ∨
      ∃ S : Finset V, arrowSum hi Sᶜ S < (∑ v ∈ S, b v) + arrowSum lo S Sᶜ := by
  rw [nonempty_iff hlo]
  simp only [not_and_or, not_forall, not_le]

/-- Either the prescribed excess is realized, or its total is nonzero, or a vertex set strictly
violates the feasibility inequality. -/
theorem nonempty_or_certificate (hlo : lo ≤ hi) :
    Nonempty (ExcessFlow lo hi b) ∨ (∑ v, b v ≠ 0) ∨
      ∃ S : Finset V, arrowSum hi Sᶜ S < (∑ v ∈ S, b v) + arrowSum lo S Sᶜ := by
  classical
  exact or_iff_not_imp_left.2 ((not_nonempty_iff hlo).1)

end ExcessFlow

/-- **Hoffman's circulation theorem.** A bounded circulation exists exactly when every vertex
set has total lower bound entering it at most the total upper bound leaving it. -/
theorem exists_isCirculation_iff {lo hi : Assignment Q K} (hlo : lo ≤ hi) :
    (∃ f : Assignment Q K, f ∈ Set.Icc lo hi ∧ IsCirculation f) ↔
      ∀ S : Finset V, arrowSum lo Sᶜ S ≤ arrowSum hi S Sᶜ := by
  have he : (∃ f : Assignment Q K, f ∈ Set.Icc lo hi ∧ IsCirculation f) ↔
      Nonempty (ExcessFlow lo hi 0) := by
    simp only [ExcessFlow, isCirculation_iff, funext_iff, Pi.zero_apply,
      nonempty_subtype]
  rw [he, ExcessFlow.nonempty_iff hlo]
  simp only [Pi.zero_apply, sum_const_zero, zero_add, true_and]
  exact ⟨fun h S ↦ by simpa only [compl_compl] using h Sᶜ,
    fun h S ↦ by simpa only [compl_compl] using h Sᶜ⟩

/-- Hoffman's cut criterion also characterizes subgroup-valued circulations when both bounds
lie in the additive subgroup. -/
theorem exists_isCirculation_mem_iff {lo hi : Assignment Q K} (hlo : lo ≤ hi)
    (H : AddSubgroup K) (hloH : ∀ ⦃x y⦄ (e : Q x y), lo e ∈ H)
    (hhiH : ∀ ⦃x y⦄ (e : Q x y), hi e ∈ H) :
    (∃ f : Assignment Q K, f ∈ Set.Icc lo hi ∧ IsCirculation f ∧
      ∀ ⦃x y⦄ (e : Q x y), f e ∈ H) ↔
        ∀ S : Finset V, arrowSum lo Sᶜ S ≤ arrowSum hi S Sᶜ := by
  refine ⟨fun ⟨f, hf, hc, _⟩ ↦ (exists_isCirculation_iff hlo).1 ⟨f, hf, hc⟩, fun hc ↦ ?_⟩
  have hcuts (S : Finset V) :
      (∑ v ∈ S, (0 : V → K) v) + arrowSum lo S Sᶜ ≤ arrowSum hi Sᶜ S := by
    simpa only [Pi.zero_apply, sum_const_zero, zero_add, compl_compl] using hc Sᶜ
  obtain ⟨f, hf⟩ := ExcessFlow.exists_mem_of_forall_cut hlo (by simp) hcuts H hloH hhiH
    (fun _ ↦ H.zero_mem)
  exact ⟨f.val, f.mem_Icc, (isCirculation_iff _).2 (fun v ↦ f.excessAt_eq v), hf⟩

/-- Infeasibility of a circulation is witnessed by a strict Hoffman cut. -/
theorem not_exists_isCirculation_iff {lo hi : Assignment Q K} (hlo : lo ≤ hi) :
    ¬(∃ f : Assignment Q K, f ∈ Set.Icc lo hi ∧ IsCirculation f) ↔
      ∃ S : Finset V, arrowSum hi S Sᶜ < arrowSum lo Sᶜ S := by
  rw [exists_isCirculation_iff hlo]
  simp only [not_forall, not_le]

/-- Either a bounded circulation exists or a strict Hoffman cut certifies infeasibility. -/
theorem exists_isCirculation_or_cut {lo hi : Assignment Q K} (hlo : lo ≤ hi) :
    (∃ f : Assignment Q K, f ∈ Set.Icc lo hi ∧ IsCirculation f) ∨
      ∃ S : Finset V, arrowSum hi S Sᶜ < arrowSum lo Sᶜ S := by
  classical
  exact or_iff_not_imp_left.2 ((not_exists_isCirculation_iff hlo).1)

/-! ### Signed feasibility and obstruction examples -/

-- Both bounds on every arrow, including every loop, are negative. The asymmetric assignment
-- realizes one unit of demand at `false` and one unit of supply at `true`.
example :
    let Q : Bool → Bool → Type := fun _ _ ↦ Unit
    let lo : Assignment Q ℤ := fun _ _ _ ↦ -2
    let hi : Assignment Q ℤ := fun _ _ _ ↦ -1
    Nonempty (ExcessFlow lo hi (fun v ↦ if v then -1 else 1)) := by
  intro Q lo hi
  let f : Assignment Q ℤ := fun x y _ ↦ if x = false ∧ y = true then -2 else -1
  refine ⟨⟨f, ⟨?_, ?_⟩, ?_⟩⟩
  · intro x y e
    cases x <;> cases y <;> norm_num [lo, f]
  · intro x y e
    cases x <;> cases y <;> norm_num [hi, f]
  · funext x
    cases x <;> norm_num [excessAt_def, f, Fintype.sum_bool]

-- Twice that demand violates the inequality for the singleton containing `false`.
example :
    let Q : Bool → Bool → Type := fun _ _ ↦ Unit
    let lo : Assignment Q ℤ := fun _ _ _ ↦ -2
    let hi : Assignment Q ℤ := fun _ _ _ ↦ -1
    ¬Nonempty (ExcessFlow lo hi (fun v ↦ if v then -2 else 2)) := by
  intro Q lo hi
  apply (ExcessFlow.not_nonempty_iff (by intro x y e; norm_num [lo, hi])).2
  refine Or.inr ⟨{false}, ?_⟩
  norm_num [arrowSum_eq_sum_ite, Fintype.sum_bool, lo, hi]

end TauCeti
