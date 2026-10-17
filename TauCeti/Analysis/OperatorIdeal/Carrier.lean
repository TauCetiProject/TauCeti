/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# The normed ideal of an operator-ideal family

An operator-ideal family `Φ` assigns an extended gauge `Φ.gauge A ∈ [0, ∞]` to every bounded
operator `A : E →L[𝕜] F` between Hilbert spaces. The operators of finite gauge form the ideal
`Φ.ideal E F`, a submodule of `E →L[𝕜] F` that is stable under composition with bounded operators
on either side. The finite real value of the gauge is a norm on this ideal, in general finer than
the operator norm. Since that norm differs from the operator norm, the ideal is packaged as a
separate type `Φ.Carrier E F` rather than as the subtype of `Φ.ideal E F`, which would inherit the
operator norm.

The carrier `Φ.Carrier E F` is a normed space over `𝕜` with `‖T‖ = (Φ.gauge T).toReal`. No
information is lost in passing to the real norm, since `‖T‖ₑ = Φ.gauge T`, and the inclusion into
bounded operators is a contraction.

A family is complete (`OperatorIdealFamily.IsComplete`) when all of its carriers are Banach spaces.
This holds as soon as every gauge is lower semicontinuous for the operator-norm topology: a Cauchy
sequence for the ideal norm is Cauchy for the operator norm, and lower semicontinuity bounds the
ideal norm of the distance to its operator-norm limit.

## Main declarations

* `TauCeti.OperatorIdealFamily.ideal`: the submodule of operators of finite gauge.
* `TauCeti.OperatorIdealFamily.comp_left_mem_ideal`,
  `TauCeti.OperatorIdealFamily.comp_right_mem_ideal`: the ideal is stable under composition.
* `TauCeti.OperatorIdealFamily.Carrier`: the normed space of operators of finite gauge.
* `TauCeti.OperatorIdealFamily.Carrier.norm_def`,
  `TauCeti.OperatorIdealFamily.Carrier.enorm_eq_gauge`: the norm of the carrier is the gauge.
* `TauCeti.OperatorIdealFamily.Carrier.toContinuousLinearMapL`: the contractive inclusion of the
  carrier into bounded operators.
* `TauCeti.OperatorIdealFamily.IsComplete`: every carrier of the family is complete.
* `TauCeti.OperatorIdealFamily.isComplete_of_lowerSemicontinuous`: a family with lower
  semicontinuous gauges is complete.

## References

* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  AMS, 1969, Chapter III.
-/

public section

noncomputable section

open scoped ENNReal Topology

universe u v w

namespace TauCeti

namespace OperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]
variable (Φ : OperatorIdealFamily.{u, v, w} 𝕜)
variable (E : Type v) (F : Type w)
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-! ### The ideal of operators of finite gauge -/

/-- The operators of finite gauge form a submodule of the bounded operators. -/
def ideal : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {A | Φ.gauge A < ∞}
  add_mem' {A B} hA hB :=
    (Φ.gauge_add_le A B).trans_lt (ENNReal.add_lt_top.2 ⟨hA, hB⟩)
  zero_mem' := by simp
  smul_mem' c A hA := by
    simpa [Φ.gauge_smul] using ENNReal.mul_lt_top enorm_lt_top hA

variable {Φ E F}

@[simp]
theorem mem_ideal_iff {A : E →L[𝕜] F} : A ∈ Φ.ideal E F ↔ Φ.gauge A < ∞ := Iff.rfl

/-- The ideal is stable under composition on the left with a bounded operator. -/
theorem comp_left_mem_ideal {G : Type w}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : A ∈ Φ.ideal E F) : L ∘L A ∈ Φ.ideal E G :=
  (Φ.gauge_comp_left_le L A).trans_lt (ENNReal.mul_lt_top enorm_lt_top hA)

/-- The ideal is stable under composition on the right with a bounded operator. -/
theorem comp_right_mem_ideal {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {A : E →L[𝕜] F} (hA : A ∈ Φ.ideal E F) (R : H →L[𝕜] E) : A ∘L R ∈ Φ.ideal H F :=
  (Φ.gauge_comp_right_le A R).trans_lt (ENNReal.mul_lt_top hA enorm_lt_top)

/-! ### The normed carrier -/

variable (Φ E F) in
/-- The operators of finite gauge, normed by the finite real value of the gauge.

This is a separate type from the subtype of `Φ.ideal E F`, which carries the operator norm. -/
@[ext]
structure Carrier where
  /-- The underlying bounded operator. -/
  toContinuousLinearMap : E →L[𝕜] F
  /-- The underlying operator has finite gauge. -/
  mem_ideal : toContinuousLinearMap ∈ Φ.ideal E F

namespace Carrier

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : Φ.Carrier E F → E →L[𝕜] F) :=
  fun _ _ ↦ Carrier.ext

@[simp]
theorem toContinuousLinearMap_inj {S T : Φ.Carrier E F} :
    S.toContinuousLinearMap = T.toContinuousLinearMap ↔ S = T :=
  toContinuousLinearMap_injective.eq_iff

/-- The underlying operators of the carrier are exactly the operators of finite gauge. -/
@[simp]
theorem range_toContinuousLinearMap :
    Set.range (toContinuousLinearMap : Φ.Carrier E F → E →L[𝕜] F) = Φ.ideal E F := by
  ext A
  exact ⟨fun ⟨T, hT⟩ ↦ hT ▸ T.mem_ideal, fun hA ↦ ⟨⟨A, hA⟩, rfl⟩⟩

theorem gauge_lt_top (T : Φ.Carrier E F) : Φ.gauge T.toContinuousLinearMap < ∞ :=
  mem_ideal_iff.1 T.mem_ideal

instance : Zero (Φ.Carrier E F) := ⟨⟨0, (Φ.ideal E F).zero_mem⟩⟩

instance : Add (Φ.Carrier E F) :=
  ⟨fun S T ↦ ⟨S.toContinuousLinearMap + T.toContinuousLinearMap,
    (Φ.ideal E F).add_mem S.mem_ideal T.mem_ideal⟩⟩

instance : Neg (Φ.Carrier E F) :=
  ⟨fun T ↦ ⟨-T.toContinuousLinearMap, (Φ.ideal E F).neg_mem T.mem_ideal⟩⟩

instance : Sub (Φ.Carrier E F) :=
  ⟨fun S T ↦ ⟨S.toContinuousLinearMap - T.toContinuousLinearMap,
    (Φ.ideal E F).sub_mem S.mem_ideal T.mem_ideal⟩⟩

instance {R : Type*} [SMul R 𝕜] [SMul R (E →L[𝕜] F)] [IsScalarTower R 𝕜 (E →L[𝕜] F)] :
    SMul R (Φ.Carrier E F) :=
  ⟨fun c T ↦ ⟨c • T.toContinuousLinearMap,
    (Φ.ideal E F).smul_of_tower_mem c T.mem_ideal⟩⟩

@[simp]
theorem toContinuousLinearMap_zero : (0 : Φ.Carrier E F).toContinuousLinearMap = 0 := rfl

@[simp]
theorem toContinuousLinearMap_add (S T : Φ.Carrier E F) :
    (S + T).toContinuousLinearMap = S.toContinuousLinearMap + T.toContinuousLinearMap := rfl

@[simp]
theorem toContinuousLinearMap_neg (T : Φ.Carrier E F) :
    (-T).toContinuousLinearMap = -T.toContinuousLinearMap := rfl

@[simp]
theorem toContinuousLinearMap_sub (S T : Φ.Carrier E F) :
    (S - T).toContinuousLinearMap = S.toContinuousLinearMap - T.toContinuousLinearMap := rfl

@[simp]
theorem toContinuousLinearMap_smul {R : Type*} [SMul R 𝕜] [SMul R (E →L[𝕜] F)]
    [IsScalarTower R 𝕜 (E →L[𝕜] F)] (c : R) (T : Φ.Carrier E F) :
    (c • T).toContinuousLinearMap = c • T.toContinuousLinearMap := rfl

instance : AddCommGroup (Φ.Carrier E F) :=
  toContinuousLinearMap_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module 𝕜 (Φ.Carrier E F) :=
  toContinuousLinearMap_injective.module 𝕜
    { toFun := toContinuousLinearMap, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    fun _ _ ↦ rfl

variable (Φ E F) in
/-- The gauge of the underlying operator, as an additive group norm on the carrier. -/
def addGroupNorm : AddGroupNorm (Φ.Carrier E F) where
  toFun T := (Φ.gauge T.toContinuousLinearMap).toReal
  map_zero' := by simp
  add_le' S T := by
    rw [← ENNReal.toReal_add S.gauge_lt_top.ne T.gauge_lt_top.ne]
    exact ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨S.gauge_lt_top, T.gauge_lt_top⟩).ne
      (Φ.gauge_add_le _ _)
  neg' T := by simp
  eq_zero_of_map_eq_zero' T hT := by
    rw [ENNReal.toReal_eq_zero_iff, or_iff_left T.gauge_lt_top.ne, gauge_eq_zero_iff] at hT
    exact Carrier.ext hT

instance : NormedAddCommGroup (Φ.Carrier E F) := (addGroupNorm Φ E F).toNormedAddCommGroup

/-- The norm of an element of the carrier is the finite real value of its gauge. -/
theorem norm_def (T : Φ.Carrier E F) : ‖T‖ = (Φ.gauge T.toContinuousLinearMap).toReal := (rfl)

/-- The extended norm of an element of the carrier is its gauge. -/
@[simp]
theorem enorm_eq_gauge (T : Φ.Carrier E F) : ‖T‖ₑ = Φ.gauge T.toContinuousLinearMap := by
  rw [← _root_.ofReal_norm, norm_def, ENNReal.ofReal_toReal T.gauge_lt_top.ne]

/-- Passing from the gauge to the real norm of the carrier loses no information. -/
theorem ofReal_norm_eq_gauge (T : Φ.Carrier E F) :
    ENNReal.ofReal ‖T‖ = Φ.gauge T.toContinuousLinearMap := by
  rw [_root_.ofReal_norm, enorm_eq_gauge]

instance : NormedSpace 𝕜 (Φ.Carrier E F) where
  norm_smul_le c T := by
    rw [norm_def, norm_def, toContinuousLinearMap_smul, Φ.gauge_smul, ENNReal.toReal_mul,
      toReal_enorm]

/-- The operator norm is dominated by the norm of the carrier. -/
theorem norm_toContinuousLinearMap_le (T : Φ.Carrier E F) : ‖T.toContinuousLinearMap‖ ≤ ‖T‖ := by
  rw [← enorm_le_iff_norm_le, enorm_eq_gauge]
  exact Φ.enorm_le_gauge _

variable (Φ E F) in
/-- The inclusion of the carrier into the bounded operators, as a bounded linear map. -/
def toContinuousLinearMapL : Φ.Carrier E F →L[𝕜] E →L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := toContinuousLinearMap, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } 1
    fun T ↦ by simpa using norm_toContinuousLinearMap_le T

@[simp]
theorem toContinuousLinearMapL_apply (T : Φ.Carrier E F) :
    toContinuousLinearMapL Φ E F T = T.toContinuousLinearMap := (rfl)

/-- The inclusion of the carrier into the bounded operators is a contraction. -/
theorem norm_toContinuousLinearMapL_le : ‖toContinuousLinearMapL Φ E F‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Carrier

/-! ### Completeness -/

/-- If the gauge is lower semicontinuous for the operator-norm topology, then the carrier is
complete. -/
theorem completeSpace_carrier_of_lowerSemicontinuous
    (h : LowerSemicontinuous fun A : E →L[𝕜] F ↦ Φ.gauge A) : CompleteSpace (Φ.Carrier E F) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  set v : ℕ → E →L[𝕜] F := fun n ↦ (u n).toContinuousLinearMap
  -- The underlying operators form a Cauchy sequence for the operator norm, with a limit `A`.
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete
    ((Carrier.toContinuousLinearMapL Φ E F).uniformContinuous.comp_cauchySeq hu)
  -- Lower semicontinuity bounds the gauge of `A - v n` by the tail of the Cauchy sequence.
  have hbound : ∀ ε > 0, ∃ N, ∀ n ≥ N, Φ.gauge (A - v n) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    refine ⟨N, fun n hn ↦ not_lt.1 fun hlt ↦ ?_⟩
    have hlim : Filter.Tendsto (fun m ↦ v m - v n) Filter.atTop (𝓝 (A - v n)) :=
      hA.sub_const (v n)
    obtain ⟨m, hm, hmN⟩ := ((hlim.eventually (h _ _ hlt)).and (Filter.eventually_ge_atTop N)).exists
    have hlt' : ‖u m - u n‖ < ε := by simpa [dist_eq_norm] using hN m hmN n hn
    rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _),
      Carrier.ofReal_norm_eq_gauge] at hlt'
    exact hm.not_gt hlt'
  have hAmem : A ∈ Φ.ideal E F := by
    obtain ⟨N, hN⟩ := hbound 1 one_pos
    have hsum := (Φ.ideal E F).add_mem ((hN N le_rfl).trans_lt ENNReal.ofReal_lt_top)
      (u N).mem_ideal
    rwa [sub_add_cancel] at hsum
  refine ⟨⟨A, hAmem⟩, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hbound (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, ← norm_neg, neg_sub, ← ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _),
    Carrier.ofReal_norm_eq_gauge]
  exact (hN n hn).trans_lt (ENNReal.ofReal_lt_ofReal_iff hε |>.2 (half_lt_self hε))

variable (Φ) in
/-- An operator-ideal family is complete when the normed carrier of every Hilbert-space pair is a
Banach space. -/
class IsComplete : Prop where
  /-- Every carrier of the family is complete. -/
  completeSpace_carrier : ∀ (E : Type v) (F : Type w)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
    CompleteSpace (Φ.Carrier E F)

instance [Φ.IsComplete] : CompleteSpace (Φ.Carrier E F) :=
  IsComplete.completeSpace_carrier E F

/-- An operator-ideal family whose gauges are lower semicontinuous for the operator-norm topology
is complete. -/
theorem isComplete_of_lowerSemicontinuous
    (h : ∀ (E : Type v) (F : Type w)
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      LowerSemicontinuous fun A : E →L[𝕜] F ↦ Φ.gauge A) :
    Φ.IsComplete :=
  ⟨fun E F _ _ _ _ _ _ ↦ completeSpace_carrier_of_lowerSemicontinuous (h E F)⟩

end OperatorIdealFamily

end TauCeti
