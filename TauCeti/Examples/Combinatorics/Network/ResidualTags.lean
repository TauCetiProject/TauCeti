/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
public import TauCeti.Combinatorics.Network.AugmentingPath

/-!
# Residual tags on parallel, antiparallel, loop and zero-capacity arrows

Take the source `0` and the sink `1`, with two parallel arrows `false` and `true` for every
ordered pair of vertices, so that there are antiparallel arrows between `0` and `1` and two loops
at each vertex. Fix `c ≥ 0` in a linearly ordered additive group. Every arrow `true` has capacity
zero; the arrow `false` from `0` to `1` has capacity `c + c`, and every other arrow `false`,
including the antiparallel arrow from `1` to `0` and both loops, has capacity `c`.

The flow carrying `c` on the arrow `false` from `0` to `1` and on the loop `false` at `0` has
value `c`: the loop enters and leaves `0`, so its contribution to the excess cancels. Among its
residual arrows from `1` to `0`, two have capacity `c`: the forward copy `Sum.inl false` of the
antiparallel arrow and the reverse copy `Sum.inr false` of the arrow from `0` to `1`. Updating by
`c` along either one is feasible and lowers the value to zero, with the same change of excess, but
the first update raises the antiparallel arrow while the second lowers the arrow from `0` to `1`;
so the two tags cannot be merged. The two residual copies of the saturated loop are likewise
distinct, with capacities `0` and `c`, and every zero-capacity arrow remains as two residual
arrows of capacity zero.

Augmenting along the forward residual arrow from `0` to `1` by its bottleneck `c` saturates that
arrow and gives a flow of value `c + c`. It is maximum, certified by the cut `{0}`, whose capacity
sums over both parallel arrows from `0` to `1`, including the zero-capacity one, and ignores the
antiparallel arrow and the loops. For `c > 0` the original flow is therefore not maximum.

The construction is generic in the coefficient group, and the examples at the end instantiate it
over `ℤ`, `ℚ` and `ℝ`, with `c` equal to `1`, `1 / 2` and `√2`.
-/

namespace TauCeti.Examples.ResidualTags

open Finset

/-- Two parallel arrows `false` and `true` for every ordered pair of the vertices `0` and `1`. -/
public abbrev Hom (_ _ : Fin 2) : Type := Bool

variable {K : Type*} [AddCommGroup K]

/-- The capacities: zero on every arrow `true`, `c + c` on the arrow `false` from `0` to `1`, and
`c` on every other arrow `false`. -/
private def cap (c : K) : Assignment Hom K := fun v w e ↦
  if e then 0 else if v = 0 ∧ w = 1 then c + c else c

/-- The assignment carrying `c` on the arrow `false` from `0` to `1` and on the loop `false` at
`0`, and zero elsewhere. -/
private def flowFun (c : K) : Assignment Hom K := fun v _ e ↦
  if e = false ∧ v = 0 then c else 0

/-- The assignment carrying `c + c` on the arrow `false` from `0` to `1`, `c` on the loop `false`
at `0`, and zero elsewhere. -/
private def maxFun (c : K) : Assignment Hom K := fun v w e ↦
  if e = false ∧ v = 0 then (if w = 1 then c + c else c) else 0

/-! ### Excess and cut capacity as finite sums -/

/-- Conservation is vacuous on two vertices, since both are terminals. -/
private theorem conserve_fin_two (f : Assignment Hom K) (v : Fin 2) (h₀ : v ≠ 0) (h₁ : v ≠ 1) :
    excessAt f v = 0 := by
  fin_cases v <;> simp_all

/-- The loop at the source contributes to both sums in its excess, so only the arrow from the
source to the sink counts. -/
private theorem excessAt_flowFun (c : K) (v : Fin 2) :
    excessAt (flowFun c) v = if v = 0 then -c else c := by
  fin_cases v <;> simp [excessAt_def, flowFun, two_nsmul]

private theorem excessAt_maxFun_one (c : K) : excessAt (maxFun c) 1 = c + c := by
  simp [excessAt_def, maxFun]

/-- The cut `{0}` crosses the two parallel arrows from `0` to `1`, one of capacity zero, and
neither the antiparallel arrow nor a loop. -/
private theorem arrowSum_cap (c : K) : arrowSum (cap c) {0} {0}ᶜ = c + c := by
  have : ({0}ᶜ : Finset (Fin 2)) = {1} := by decide
  simp [arrowSum_def, this, cap]

/-! ### Residual capacities -/

/-- From the sink to the source, the forward copy of the antiparallel arrow and the reverse copy
of the arrow from the source each have residual capacity `c`. -/
private theorem residualCapacity_one_zero (c : K) :
    residualCapacity 0 (cap c) (flowFun c) (x := 1) (y := 0) (Sum.inl false) = c ∧
      residualCapacity 0 (cap c) (flowFun c) (x := 1) (y := 0) (Sum.inr false) = c := by
  simp [cap, flowFun]

-- The forward copy of the saturated loop has residual capacity zero, and its reverse copy has
-- residual capacity `c`.
example (c : K) :
    residualCapacity 0 (cap c) (flowFun c) (x := 0) (y := 0) (Sum.inl false) = 0 ∧
      residualCapacity 0 (cap c) (flowFun c) (x := 0) (y := 0) (Sum.inr false) = c := by
  simp [cap, flowFun]

-- Both residual copies of every zero-capacity arrow are retained, with residual capacity zero.
example (c : K) (v w : Fin 2) :
    residualCapacity 0 (cap c) (flowFun c) (x := v) (y := w) (Sum.inl true) = 0 ∧
      residualCapacity 0 (cap c) (flowFun c) (x := v) (y := w) (Sum.inr true) = 0 := by
  simp [cap, flowFun]

/-- The residual capacities from the sink to the source sum to `c + c`, one `c` for each tag. -/
private theorem sum_residualCapacity_one_zero (c : K) :
    ∑ a : ResidualHom Hom 1 0, residualCapacity 0 (cap c) (flowFun c) a = c + c := by
  simp [cap, flowFun]

-- The residual capacities from the source to the sink sum to `c`, all of it on the forward copy
-- of the arrow `false`.
example (c : K) :
    ∑ a : ResidualHom Hom 0 1, residualCapacity 0 (cap c) (flowFun c) a = c := by
  simp [cap, flowFun]

/-! ### Two residual updates with the same change of excess -/

/-- The one-arrow residual walk from the sink to the source along the forward copy of the
antiparallel arrow. -/
private def forwardWalk : ArrowWalk (ResidualHom Hom) 1 0 :=
  (ArrowWalk.nil 1).cons (x := 0) (Sum.inl false)

/-- The one-arrow residual walk from the sink to the source along the reverse copy of the arrow
from the source. -/
private def reverseWalk : ArrowWalk (ResidualHom Hom) 1 0 :=
  (ArrowWalk.nil 1).cons (x := 0) (Sum.inr false)

/-- The residual assignment carrying `c` on the forward copy of the antiparallel arrow. -/
private noncomputable def forwardTag (c : K) : Assignment (ResidualHom Hom) K :=
  walkAssignment forwardWalk c

/-- The residual assignment carrying `c` on the reverse copy of the arrow from the source. -/
private noncomputable def reverseTag (c : K) : Assignment (ResidualHom Hom) K :=
  walkAssignment reverseWalk c

private theorem forwardTag_eq (c : K) :
    forwardTag c =
      Assignment.single (Q := ResidualHom Hom) (Sum.inl false : ResidualHom Hom 1 0) c := by
  simp [forwardTag, forwardWalk]

private theorem reverseTag_eq (c : K) :
    reverseTag c =
      Assignment.single (Q := ResidualHom Hom) (Sum.inr false : ResidualHom Hom 1 0) c := by
  simp [reverseTag, reverseWalk]

-- Both residual walks run from the sink to the source, so they change the excess in the same way.
example (c : K) : excessAt (forwardTag c) = excessAt (reverseTag c) :=
  funext fun v ↦ by simp [forwardTag, reverseTag, excessAt_walkAssignment]

-- After either update the sink has excess zero.
example (c : K) :
    excessAt (residualUpdate (flowFun c) (forwardTag c)) 1 = 0 ∧
      excessAt (residualUpdate (flowFun c) (reverseTag c)) 1 = 0 := by
  simp [forwardTag, reverseTag, excessAt_walkAssignment, excessAt_flowFun]

/-- The forward tag raises the antiparallel arrow from `0` to `c` and keeps `c` on the arrow from
the source, while the reverse tag lowers the arrow from the source to `0` and keeps the
antiparallel arrow at `0`. -/
private theorem residualUpdate_tags (c : K) :
    residualUpdate (flowFun c) (forwardTag c) (x := 1) (y := 0) false = c ∧
      residualUpdate (flowFun c) (forwardTag c) (x := 0) (y := 1) false = c ∧
      residualUpdate (flowFun c) (reverseTag c) (x := 1) (y := 0) false = 0 ∧
      residualUpdate (flowFun c) (reverseTag c) (x := 0) (y := 1) false = 0 := by
  simp [forwardTag, reverseTag, forwardWalk, reverseWalk, Assignment.single_apply, flowFun]

/-! ### Feasibility, augmentation and maximality -/

variable [LinearOrder K] [IsOrderedAddMonoid K]

private theorem flowFun_mem_Icc {c : K} (hc : 0 ≤ c) : flowFun c ∈ Set.Icc 0 (cap c) := by
  constructor <;> intro v w e <;> fin_cases v <;> fin_cases w <;> cases e <;>
    simp [cap, flowFun, hc]

/-- The flow of value `c` described in the module docstring. -/
private def flow {c : K} (hc : 0 ≤ c) : Flow (cap c) 0 1 where
  toFun := flowFun c
  mem_Icc := flowFun_mem_Icc hc
  conserve := conserve_fin_two _
  excessAt_sink_nonneg := by simpa [excessAt_flowFun] using hc

private theorem flow_toFun {c : K} (hc : 0 ≤ c) : (flow hc).toFun = flowFun c :=
  (rfl)

private theorem flow_val {c : K} (hc : 0 ≤ c) : (flow hc).val = c := by
  simp [BoundedFlow.val_def, flow_toFun, excessAt_flowFun]

/-- Both residual updates from the sink to the source are feasible. -/
private theorem residualUpdate_mem_Icc_tags {c : K} (hc : 0 ≤ c) :
    residualUpdate (flowFun c) (forwardTag c) ∈ Set.Icc 0 (cap c) ∧
      residualUpdate (flowFun c) (reverseTag c) ∈ Set.Icc 0 (cap c) :=
  ⟨residualUpdate_mem_Icc (walkAssignment_mem_Icc (by simp [forwardWalk]) hc
      (residualCapacity_nonneg (flowFun_mem_Icc hc)) (by simp [forwardWalk, cap, flowFun])),
    residualUpdate_mem_Icc (walkAssignment_mem_Icc (by simp [reverseWalk]) hc
      (residualCapacity_nonneg (flowFun_mem_Icc hc)) (by simp [reverseWalk, flowFun]))⟩

/-- The one-arrow augmenting path along the forward copy of the arrow `false` from `0` to `1`. -/
private def augmentingPath : ArrowWalk (ResidualHom Hom) 0 1 :=
  (ArrowWalk.nil 0).cons (x := 1) (Sum.inl false)

private theorem augmentingPath_arrows :
    augmentingPath.arrows = [⟨0, 1, Sum.inl false⟩] := by
  simp [augmentingPath]

private theorem augmentingPath_nodup : augmentingPath.arrows.Nodup := by
  simp [augmentingPath_arrows]

private theorem augmentingPath_ne_nil : augmentingPath.arrows ≠ [] := by
  simp [augmentingPath_arrows]

omit [IsOrderedAddMonoid K] in
private theorem bottleneck_augmentingPath (c : K) :
    augmentingPath.bottleneck (residualCapacity 0 (cap c) (flowFun c)) augmentingPath_ne_nil =
      c := by
  obtain ⟨a, ha, hb⟩ := ArrowWalk.exists_mem_bottleneck_eq (c := residualCapacity 0 (cap c)
    (flowFun c)) (hne := augmentingPath_ne_nil)
  rw [augmentingPath_arrows, List.mem_singleton] at ha
  subst ha
  simpa [cap, flowFun] using hb

/-- The flow obtained by augmenting `flow hc` along `augmentingPath` by its bottleneck. -/
private noncomputable def augmented {c : K} (hc : 0 ≤ c) : Flow (cap c) 0 1 :=
  (flow hc).augmentBottleneck augmentingPath augmentingPath_nodup augmentingPath_ne_nil

/-- Augmentation saturates the arrow `false` from `0` to `1` and leaves the loop unchanged. -/
private theorem augmented_toFun {c : K} (hc : 0 ≤ c) : (augmented hc).toFun = maxFun c := by
  rw [augmented, Flow.augmentBottleneck_toFun, flow_toFun, bottleneck_augmentingPath]
  funext v w e
  fin_cases v <;> fin_cases w <;> cases e <;>
    simp [augmentingPath, Assignment.single_apply, flowFun, maxFun]

private theorem augmented_val {c : K} (hc : 0 ≤ c) : (augmented hc).val = c + c := by
  rw [BoundedFlow.val_def, augmented_toFun, excessAt_maxFun_one]

/-- The augmented flow is maximum: its value is the capacity of the cut `{0}`. -/
private theorem augmented_isMaximum {c : K} (hc : 0 ≤ c) : (augmented hc).IsMaximum := by
  have h := ((augmented hc).tfae_isMaximum (by decide)).out 1 3
  exact h.2 ⟨{0}, mem_singleton_self 0, by decide, by rw [augmented_val, arrowSum_cap]⟩

/-- For `c > 0`, the flow of value `c` is not maximum. -/
private theorem flow_not_isMaximum {c : K} (hc : 0 < c) : ¬(flow hc.le).IsMaximum := by
  rw [Flow.isMaximum_iff, not_forall]
  exact ⟨augmented hc.le, by simpa [augmented_val, flow_val] using hc⟩

/-- For `c > 0`, augmenting along `augmentingPath` is an augmentation step. -/
private theorem flow_augmentsTo {c : K} (hc : 0 < c) : (flow hc.le).AugmentsTo (augmented hc.le) :=
  Flow.augmentsTo_augmentBottleneck _ _ _ (by simp [augmentingPath_arrows, flow_toFun, cap,
    flowFun, hc])

/-- Take two parallel arrows `false` and `true` for every ordered pair of the vertices `0` and
`1`, and `c > 0` in a linearly ordered additive group. Give every arrow `true` capacity zero, the
arrow `false` from `0` to `1` capacity `c + c`, and every other arrow `false` capacity `c`. Some
flow `f` of value `c` has two residual arrows from `1` to `0` of capacity `c`, the forward copy of
the antiparallel arrow and the reverse copy of the arrow from `0` to `1`. The residual updates by
`c` along them are both feasible, but only the second changes the arrow from `0` to `1`. One
augmentation step turns `f` into a maximum flow `g` whose value `c + c` is the capacity of the
cut `{0}`. -/
public theorem exists_residual_tags_and_maximum_augmentation {c : K} (hc : 0 < c) :
    ∃ (cap : Assignment Hom K) (f g : Flow cap 0 1),
      (∀ v w e, cap (x := v) (y := w) e = if e then 0 else if v = 0 ∧ w = 1 then c + c else c) ∧
      f.val = c ∧ ¬f.IsMaximum ∧
      residualCapacity 0 cap f.toFun (x := 1) (y := 0) (Sum.inl false) = c ∧
      residualCapacity 0 cap f.toFun (x := 1) (y := 0) (Sum.inr false) = c ∧
      residualUpdate f.toFun
          (.single (Q := ResidualHom Hom) (x := 1) (y := 0) (Sum.inl false) c) ∈ Set.Icc 0 cap ∧
      residualUpdate f.toFun
          (.single (Q := ResidualHom Hom) (x := 1) (y := 0) (Sum.inr false) c) ∈ Set.Icc 0 cap ∧
      residualUpdate f.toFun
          (.single (Q := ResidualHom Hom) (x := 1) (y := 0) (Sum.inl false) c)
          (x := 0) (y := 1) false = c ∧
      residualUpdate f.toFun
          (.single (Q := ResidualHom Hom) (x := 1) (y := 0) (Sum.inr false) c)
          (x := 0) (y := 1) false = 0 ∧
      f.AugmentsTo g ∧ g.val = c + c ∧ g.IsMaximum ∧ g.val = arrowSum cap {0} {0}ᶜ := by
  have hupd := residualUpdate_mem_Icc_tags hc.le
  have htags := residualUpdate_tags c
  rw [forwardTag_eq, reverseTag_eq] at hupd htags
  exact ⟨cap c, flow hc.le, augmented hc.le, fun _ _ _ ↦ rfl, flow_val hc.le,
    flow_not_isMaximum hc, (residualCapacity_one_zero c).1, (residualCapacity_one_zero c).2,
    hupd.1, hupd.2, htags.2.1, htags.2.2.2, flow_augmentsTo hc, augmented_val hc.le,
    augmented_isMaximum hc.le, by rw [augmented_val, arrowSum_cap]⟩

/-! ### Integer, rational and real coefficients -/

-- Over `ℤ` with `c = 1`, the two tags from the sink to the source each have residual capacity
-- `1`, and augmentation reaches the maximum value `2`.
example :
    residualCapacity 0 (cap (1 : ℤ)) (flowFun 1) (x := 1) (y := 0) (Sum.inl false) = 1 ∧
      residualCapacity 0 (cap (1 : ℤ)) (flowFun 1) (x := 1) (y := 0) (Sum.inr false) = 1 ∧
      ¬(flow (zero_le_one' ℤ)).IsMaximum ∧ (augmented (zero_le_one' ℤ)).val = 2 ∧
      (augmented (zero_le_one' ℤ)).IsMaximum :=
  ⟨(residualCapacity_one_zero 1).1, (residualCapacity_one_zero 1).2, flow_not_isMaximum one_pos,
    by rw [augmented_val]; norm_num, augmented_isMaximum _⟩

-- Over `ℚ` with `c = 1 / 2`, the flow of value `1 / 2` augments to the maximum value `1`, and
-- the residual capacities from the sink to the source sum to `1` over both tags.
example :
    ∑ a : ResidualHom Hom 1 0, residualCapacity 0 (cap (1 / 2 : ℚ)) (flowFun (1 / 2)) a = 1 ∧
      (flow (c := (1 / 2 : ℚ)) (by norm_num)).val = 1 / 2 ∧
      ¬(flow (c := (1 / 2 : ℚ)) (by norm_num)).IsMaximum ∧
      (augmented (c := (1 / 2 : ℚ)) (by norm_num)).val = 1 ∧
      (augmented (c := (1 / 2 : ℚ)) (by norm_num)).IsMaximum := by
  refine ⟨?_, flow_val _, flow_not_isMaximum (by norm_num), ?_, augmented_isMaximum _⟩
  · rw [sum_residualCapacity_one_zero]
    norm_num
  · rw [augmented_val]
    norm_num

-- Over `ℝ` with the irrational capacity `c = √2`, the two updates from the sink to the source are
-- feasible and differ on the arrow from the source, and augmentation reaches `2 * √2`.
example :
    residualUpdate (flowFun √2) (forwardTag √2) ∈ Set.Icc 0 (cap (√2 : ℝ)) ∧
      residualUpdate (flowFun √2) (reverseTag √2) ∈ Set.Icc 0 (cap (√2 : ℝ)) ∧
      residualUpdate (flowFun √2) (forwardTag √2) (x := 0) (y := 1) false = √2 ∧
      residualUpdate (flowFun √2) (reverseTag √2) (x := 0) (y := 1) false = 0 ∧
      (augmented (Real.sqrt_nonneg 2)).val = 2 * √2 ∧
      (augmented (Real.sqrt_nonneg 2)).IsMaximum := by
  refine ⟨(residualUpdate_mem_Icc_tags (Real.sqrt_nonneg 2)).1,
    (residualUpdate_mem_Icc_tags (Real.sqrt_nonneg 2)).2, (residualUpdate_tags _).2.1,
    (residualUpdate_tags _).2.2.2, ?_, augmented_isMaximum _⟩
  rw [augmented_val, two_mul]

end TauCeti.Examples.ResidualTags
