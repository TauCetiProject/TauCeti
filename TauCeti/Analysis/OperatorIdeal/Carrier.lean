/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Operator gauges and their normed carriers

An operator gauge `g : OperatorGauge 𝕜 E F` assigns an extended value `g A ∈ [0, ∞]` to every
bounded operator `A : E →L[𝕜] F` between normed spaces. It is subadditive, absolutely
homogeneous, and dominates the operator norm. Examples are the Schatten and Ky Fan gauges on
Hilbert spaces, and the nuclear and absolutely summing gauges on Banach spaces; the operator-ideal
families of `TauCeti.Analysis.OperatorIdeal.Family` restrict to operator gauges on each pair of
Hilbert spaces.

The operators of finite gauge form the submodule `g.finiteSubmodule` of `E →L[𝕜] F`. The finite
real value of the gauge is a norm on it, in general finer than the operator norm. Since that norm
differs from the operator norm, the finite-gauge operators are packaged as a separate type
`g.Carrier` rather than as the subtype of `g.finiteSubmodule`, which would inherit the operator
norm.

When `F` is a normed space, the carrier `g.Carrier` is a normed space over `𝕜` with
`‖T‖ = (g T).toReal`. No information is lost in passing to the real norm, since `‖T‖ₑ = g T`, and
the inclusion into bounded operators is a contraction. If moreover `F` is complete and the gauge
is lower semicontinuous for the operator-norm topology, then the carrier is a Banach space: a
Cauchy sequence for the gauge norm is Cauchy for the operator norm, and lower semicontinuity
bounds the gauge of the distance to its operator-norm limit.

## Main declarations

* `TauCeti.OperatorGauge`: an extended gauge on bounded operators.
* `TauCeti.OperatorGauge.finiteSubmodule`: the submodule of operators of finite gauge.
* `TauCeti.OperatorGauge.Carrier`: the normed space of operators of finite gauge.
* `TauCeti.OperatorGauge.Carrier.norm_def`, `TauCeti.OperatorGauge.Carrier.enorm_eq_gauge`: the
  norm of the carrier is the gauge.
* `TauCeti.OperatorGauge.Carrier.toContinuousLinearMapL`: the contractive inclusion of the carrier
  into bounded operators.
* `TauCeti.OperatorGauge.completeSpace_carrier_of_lowerSemicontinuous`: a lower semicontinuous
  gauge into a Banach space has a complete carrier.

## References

* A. Pietsch, *Operator Ideals*, North-Holland, 1980, Chapter 6.
* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
-/

public section

noncomputable section

open scoped ENNReal Topology

namespace TauCeti

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An operator gauge on `E →L[𝕜] F`: an extended nonnegative function on bounded operators that
is subadditive, absolutely homogeneous and dominates the operator norm. -/
structure OperatorGauge where
  /-- The gauge of a bounded operator. -/
  toFun : (E →L[𝕜] F) → ℝ≥0∞
  /-- The gauge is subadditive. -/
  map_add_le' (A B : E →L[𝕜] F) : toFun (A + B) ≤ toFun A + toFun B
  /-- The gauge is absolutely homogeneous. -/
  map_smul' (c : 𝕜) (A : E →L[𝕜] F) : toFun (c • A) = ‖c‖ₑ * toFun A
  /-- The gauge dominates the extended operator norm. -/
  enorm_le' (A : E →L[𝕜] F) : ‖A‖ₑ ≤ toFun A

namespace OperatorGauge

variable {𝕜 E F}

instance : FunLike (OperatorGauge 𝕜 E F) (E →L[𝕜] F) ℝ≥0∞ where
  coe := toFun
  coe_injective g h e := by cases g; cases h; congr

@[ext]
theorem ext {g h : OperatorGauge 𝕜 E F} (H : ∀ A, g A = h A) : g = h :=
  DFunLike.ext _ _ H

@[simp]
theorem coe_mk (f : (E →L[𝕜] F) → ℝ≥0∞) (h₁ h₂ h₃) :
    ⇑(⟨f, h₁, h₂, h₃⟩ : OperatorGauge 𝕜 E F) = f := rfl

variable (g : OperatorGauge 𝕜 E F)

@[simp]
theorem toFun_eq_coe : g.toFun = ⇑g := rfl

/-- An operator gauge is subadditive. -/
theorem map_add_le (A B : E →L[𝕜] F) : g (A + B) ≤ g A + g B :=
  g.map_add_le' A B

/-- An operator gauge is absolutely homogeneous. -/
@[simp]
theorem map_smul (c : 𝕜) (A : E →L[𝕜] F) : g (c • A) = ‖c‖ₑ * g A :=
  g.map_smul' c A

/-- An operator gauge dominates the extended operator norm. -/
theorem enorm_le (A : E →L[𝕜] F) : ‖A‖ₑ ≤ g A :=
  g.enorm_le' A

@[simp]
theorem map_zero : g 0 = 0 := by
  simpa using g.map_smul 0 0

@[simp]
theorem map_neg (A : E →L[𝕜] F) : g (-A) = g A := by
  simpa using g.map_smul (-1) A

/-- An operator gauge into a normed space vanishes exactly at zero. -/
@[simp]
theorem map_eq_zero_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (g : OperatorGauge 𝕜 E F) {A : E →L[𝕜] F} : g A = 0 ↔ A = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ g.map_zero⟩
  exact A.opENorm_eq_zero_iff.mp (le_antisymm (h ▸ g.enorm_le A) bot_le)

/-! ### The submodule of operators of finite gauge -/

/-- The operators of finite gauge form a submodule of the bounded operators. -/
def finiteSubmodule : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {A | g A < ∞}
  add_mem' {A B} hA hB := (g.map_add_le A B).trans_lt (ENNReal.add_lt_top.2 ⟨hA, hB⟩)
  zero_mem' := by simp
  smul_mem' c A hA := by simpa using ENNReal.mul_lt_top enorm_lt_top hA

variable {g}

@[simp]
theorem mem_finiteSubmodule {A : E →L[𝕜] F} : A ∈ g.finiteSubmodule ↔ g A < ∞ := Iff.rfl

/-! ### The normed carrier -/

variable (g) in
/-- The operators of finite gauge, normed by the finite real value of the gauge.

This is a separate type from the subtype of `g.finiteSubmodule`, which carries the operator
norm. -/
@[ext]
structure Carrier where
  /-- The underlying bounded operator. -/
  toContinuousLinearMap : E →L[𝕜] F
  /-- The underlying operator has finite gauge. -/
  mem_finiteSubmodule : toContinuousLinearMap ∈ g.finiteSubmodule

namespace Carrier

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : g.Carrier → E →L[𝕜] F) :=
  fun _ _ ↦ Carrier.ext

@[simp]
theorem toContinuousLinearMap_inj {S T : g.Carrier} :
    S.toContinuousLinearMap = T.toContinuousLinearMap ↔ S = T :=
  toContinuousLinearMap_injective.eq_iff

/-- The underlying operators of the carrier are exactly the operators of finite gauge. -/
@[simp]
theorem range_toContinuousLinearMap :
    Set.range (toContinuousLinearMap : g.Carrier → E →L[𝕜] F) = g.finiteSubmodule := by
  ext A
  exact ⟨fun ⟨T, hT⟩ ↦ hT ▸ T.mem_finiteSubmodule, fun hA ↦ ⟨⟨A, hA⟩, rfl⟩⟩

theorem gauge_lt_top (T : g.Carrier) : g T.toContinuousLinearMap < ∞ :=
  OperatorGauge.mem_finiteSubmodule.1 T.mem_finiteSubmodule

instance : Zero g.Carrier := ⟨⟨0, g.finiteSubmodule.zero_mem⟩⟩

instance : Add g.Carrier :=
  ⟨fun S T ↦ ⟨S.toContinuousLinearMap + T.toContinuousLinearMap,
    g.finiteSubmodule.add_mem S.mem_finiteSubmodule T.mem_finiteSubmodule⟩⟩

instance : Neg g.Carrier :=
  ⟨fun T ↦ ⟨-T.toContinuousLinearMap, g.finiteSubmodule.neg_mem T.mem_finiteSubmodule⟩⟩

instance : Sub g.Carrier :=
  ⟨fun S T ↦ ⟨S.toContinuousLinearMap - T.toContinuousLinearMap,
    g.finiteSubmodule.sub_mem S.mem_finiteSubmodule T.mem_finiteSubmodule⟩⟩

instance {R : Type*} [SMul R 𝕜] [SMul R (E →L[𝕜] F)] [IsScalarTower R 𝕜 (E →L[𝕜] F)] :
    SMul R g.Carrier :=
  ⟨fun c T ↦ ⟨c • T.toContinuousLinearMap,
    g.finiteSubmodule.smul_of_tower_mem c T.mem_finiteSubmodule⟩⟩

@[simp]
theorem toContinuousLinearMap_zero : (0 : g.Carrier).toContinuousLinearMap = 0 := rfl

@[simp]
theorem toContinuousLinearMap_add (S T : g.Carrier) :
    (S + T).toContinuousLinearMap = S.toContinuousLinearMap + T.toContinuousLinearMap := rfl

@[simp]
theorem toContinuousLinearMap_neg (T : g.Carrier) :
    (-T).toContinuousLinearMap = -T.toContinuousLinearMap := rfl

@[simp]
theorem toContinuousLinearMap_sub (S T : g.Carrier) :
    (S - T).toContinuousLinearMap = S.toContinuousLinearMap - T.toContinuousLinearMap := rfl

@[simp]
theorem toContinuousLinearMap_smul {R : Type*} [SMul R 𝕜] [SMul R (E →L[𝕜] F)]
    [IsScalarTower R 𝕜 (E →L[𝕜] F)] (c : R) (T : g.Carrier) :
    (c • T).toContinuousLinearMap = c • T.toContinuousLinearMap := rfl

instance : AddCommGroup g.Carrier :=
  toContinuousLinearMap_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module 𝕜 g.Carrier :=
  toContinuousLinearMap_injective.module 𝕜
    { toFun := toContinuousLinearMap, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    fun _ _ ↦ rfl

end Carrier

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {g : OperatorGauge 𝕜 E F}

namespace Carrier

variable (g) in
/-- The gauge of the underlying operator, as an additive group norm on the carrier. -/
def addGroupNorm : AddGroupNorm g.Carrier where
  toFun T := (g T.toContinuousLinearMap).toReal
  map_zero' := by simp
  add_le' S T := by
    rw [← ENNReal.toReal_add S.gauge_lt_top.ne T.gauge_lt_top.ne]
    exact ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨S.gauge_lt_top, T.gauge_lt_top⟩).ne
      (g.map_add_le _ _)
  neg' T := by simp
  eq_zero_of_map_eq_zero' T hT := by
    rw [ENNReal.toReal_eq_zero_iff, or_iff_left T.gauge_lt_top.ne, map_eq_zero_iff] at hT
    exact Carrier.ext hT

instance : NormedAddCommGroup g.Carrier := (addGroupNorm g).toNormedAddCommGroup

/-- The norm of an element of the carrier is the finite real value of its gauge. -/
theorem norm_def (T : g.Carrier) : ‖T‖ = (g T.toContinuousLinearMap).toReal := (rfl)

/-- The extended norm of an element of the carrier is its gauge. -/
@[simp]
theorem enorm_eq_gauge (T : g.Carrier) : ‖T‖ₑ = g T.toContinuousLinearMap := by
  rw [← _root_.ofReal_norm, norm_def, ENNReal.ofReal_toReal T.gauge_lt_top.ne]

/-- Passing from the gauge to the real norm of the carrier loses no information. -/
theorem ofReal_norm_eq_gauge (T : g.Carrier) :
    ENNReal.ofReal ‖T‖ = g T.toContinuousLinearMap := by
  rw [_root_.ofReal_norm, enorm_eq_gauge]

instance : NormedSpace 𝕜 g.Carrier where
  norm_smul_le c T := by
    rw [norm_def, norm_def, toContinuousLinearMap_smul, g.map_smul, ENNReal.toReal_mul,
      toReal_enorm]

/-- The operator norm is dominated by the norm of the carrier. -/
theorem norm_toContinuousLinearMap_le (T : g.Carrier) : ‖T.toContinuousLinearMap‖ ≤ ‖T‖ := by
  rw [← enorm_le_iff_norm_le, enorm_eq_gauge]
  exact g.enorm_le _

variable (g) in
/-- The inclusion of the carrier into the bounded operators, as a bounded linear map. -/
def toContinuousLinearMapL : g.Carrier →L[𝕜] E →L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := toContinuousLinearMap, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } 1
    fun T ↦ by simpa using norm_toContinuousLinearMap_le T

@[simp]
theorem toContinuousLinearMapL_apply (T : g.Carrier) :
    toContinuousLinearMapL g T = T.toContinuousLinearMap := (rfl)

/-- The inclusion of the carrier into the bounded operators is a contraction. -/
theorem norm_toContinuousLinearMapL_le : ‖toContinuousLinearMapL g‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Carrier

/-! ### Completeness -/

/-- If the target is complete and the gauge is lower semicontinuous for the operator-norm
topology, then the carrier is complete. -/
theorem completeSpace_carrier_of_lowerSemicontinuous [CompleteSpace F]
    (h : LowerSemicontinuous g) : CompleteSpace g.Carrier := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  set v : ℕ → E →L[𝕜] F := fun n ↦ (u n).toContinuousLinearMap
  -- The underlying operators form a Cauchy sequence for the operator norm, with a limit `A`.
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete
    ((Carrier.toContinuousLinearMapL g).uniformContinuous.comp_cauchySeq hu)
  -- Lower semicontinuity bounds the gauge of `A - v n` by the tail of the Cauchy sequence.
  have hbound : ∀ ε > 0, ∃ N, ∀ n ≥ N, g (A - v n) ≤ ENNReal.ofReal ε := by
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
  have hAmem : A ∈ g.finiteSubmodule := by
    obtain ⟨N, hN⟩ := hbound 1 one_pos
    have hsum := g.finiteSubmodule.add_mem ((hN N le_rfl).trans_lt ENNReal.ofReal_lt_top)
      (u N).mem_finiteSubmodule
    rwa [sub_add_cancel] at hsum
  refine ⟨⟨A, hAmem⟩, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hbound (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, ← norm_neg, neg_sub, ← ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _),
    Carrier.ofReal_norm_eq_gauge]
  exact (hN n hn).trans_lt (ENNReal.ofReal_lt_ofReal_iff hε |>.2 (half_lt_self hε))

end Normed

end OperatorGauge

end TauCeti
