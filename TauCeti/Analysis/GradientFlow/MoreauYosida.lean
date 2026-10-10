/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.EMetricSpace.Basic

/-!
# The Moreau–Yosida functional and metric resolvent

For an extended-real energy `φ` on an extended metric space, the Moreau–Yosida functional at
`x` is the infimum of `φ y + edist x y ^ 2 / (2τ)` over `y`. Its minimizers form the metric
resolvent set. The squared-distance term is infinite outside the finite-distance component of
`x` when `τ > 0`, so minimization never silently crosses components at finite energy.

The resolvent can be multivalued. We provide a map only on the domain where its minimizer is
unique; the set-valued interface remains available without existence or uniqueness assumptions.
This is the static variational step used to define implicit Euler and minimizing-movement
sequences for metric gradient flows.

The energy may take `∞`. The finite-component statement excludes `-∞` at the minimizer, as a
proper energy would; energy descent itself needs no such assumption. Existence of minimizers
requires separate compactness or convexity hypotheses.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 2.
-/

public section

noncomputable section

open Set
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*}

section Pseudo

variable [PseudoEMetricSpace X]

/-- The squared-distance penalty `d(x,y)²/(2τ)` in a metric resolvent problem. -/
def moreauYosidaPenalty (τ : ℝ≥0) (x y : X) : ℝ≥0∞ :=
  edist x y ^ 2 / (2 * (τ : ℝ≥0∞))

/-- The squared-distance penalty with the time-step normalization explicit. -/
theorem moreauYosidaPenalty_def (τ : ℝ≥0) (x y : X) :
    moreauYosidaPenalty τ x y = edist x y ^ 2 / (2 * (τ : ℝ≥0∞)) :=
  (rfl)

/-- The metric resolvent objective at base point `x`: energy plus squared-distance penalty. -/
def moreauYosidaObjective (φ : X → EReal) (τ : ℝ≥0) (x y : X) : EReal :=
  φ y + (moreauYosidaPenalty τ x y : EReal)

/-- The objective evaluated at a candidate resolvent point. -/
theorem moreauYosidaObjective_def (φ : X → EReal) (τ : ℝ≥0) (x y : X) :
    moreauYosidaObjective φ τ x y = φ y + (moreauYosidaPenalty τ x y : EReal) :=
  (rfl)

/-- The Moreau–Yosida regularization of an extended-real energy. -/
def moreauYosida (φ : X → EReal) (τ : ℝ≥0) (x : X) : EReal :=
  ⨅ y, moreauYosidaObjective φ τ x y

/-- The Moreau–Yosida value as an infimum of the resolvent objective. -/
theorem moreauYosida_def (φ : X → EReal) (τ : ℝ≥0) (x : X) :
    moreauYosida φ τ x = ⨅ y, moreauYosidaObjective φ τ x y :=
  (rfl)

/-- Every candidate bounds the Moreau–Yosida value from above. -/
theorem moreauYosida_le_objective (φ : X → EReal) (τ : ℝ≥0) (x y : X) :
    moreauYosida φ τ x ≤ moreauYosidaObjective φ τ x y :=
  iInf_le _ y

/-- The resolvent set consists of the minimizers of the Moreau–Yosida objective. -/
def metricResolventSet (φ : X → EReal) (τ : ℝ≥0) (x : X) : Set X :=
  {y | ∀ z, moreauYosidaObjective φ τ x y ≤ moreauYosidaObjective φ τ x z}

/-- A resolvent point minimizes the objective against every competitor. -/
theorem mem_metricResolventSet_iff_forall (φ : X → EReal) (τ : ℝ≥0) (x y : X) :
    y ∈ metricResolventSet φ τ x ↔
      ∀ z, moreauYosidaObjective φ τ x y ≤ moreauYosidaObjective φ τ x z :=
  Iff.rfl

@[simp]
theorem moreauYosidaPenalty_self (τ : ℝ≥0) (x : X) :
    moreauYosidaPenalty τ x x = 0 := by simp [moreauYosidaPenalty]

/-- The squared-distance penalty vanishes exactly at zero ground distance. -/
theorem moreauYosidaPenalty_eq_zero_iff (τ : ℝ≥0) (x y : X) :
    moreauYosidaPenalty τ x y = 0 ↔ edist x y = 0 := by
  constructor
  · intro h
    have hpow : edist x y ^ 2 = 0 := by
      rcases ENNReal.div_eq_zero_iff.mp h with h | h
      · exact h
      · exact False.elim ((ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) h)
    by_contra hd
    exact (ENNReal.pow_ne_zero hd 2) hpow
  · intro h
    simp [moreauYosidaPenalty, h]

@[simp]
theorem moreauYosidaObjective_self (φ : X → EReal) (τ : ℝ≥0) (x : X) :
    moreauYosidaObjective φ τ x x = φ x := by simp [moreauYosidaObjective]

/-- An energy bounds its Moreau–Yosida regularization from above. -/
theorem moreauYosida_le (φ : X → EReal) (τ : ℝ≥0) (x : X) :
    moreauYosida φ τ x ≤ φ x := by
  simpa [moreauYosida, moreauYosidaObjective_self] using
    (iInf_le (fun y ↦ moreauYosidaObjective φ τ x y) x)

/-- A point belongs to the resolvent set exactly when it achieves the Moreau–Yosida value. -/
theorem mem_metricResolventSet_iff (φ : X → EReal) (τ : ℝ≥0) (x y : X) :
    y ∈ metricResolventSet φ τ x ↔
      moreauYosidaObjective φ τ x y = moreauYosida φ τ x := by
  simp only [metricResolventSet, Set.mem_ofPred_eq, moreauYosida]
  constructor
  · intro h
    exact le_antisymm (le_iInf h) (iInf_le _ y)
  · intro h z
    exact h.le.trans (iInf_le _ z)

/-- Every resolvent minimizer has objective at most the energy of the base point. -/
theorem moreauYosidaObjective_le_of_mem_metricResolventSet
    {φ : X → EReal} {τ : ℝ≥0} {x y : X} (hy : y ∈ metricResolventSet φ τ x) :
    moreauYosidaObjective φ τ x y ≤ φ x := by
  simpa only [moreauYosidaObjective_self] using hy x

/-- A resolvent step cannot increase the energy. -/
theorem energy_le_of_mem_metricResolventSet {φ : X → EReal} {τ : ℝ≥0}
    {x y : X} (hy : y ∈ metricResolventSet φ τ x) : φ y ≤ φ x :=
  (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg (moreauYosidaPenalty τ x y))).trans
    (moreauYosidaObjective_le_of_mem_metricResolventSet hy)

/-- A point infinitely far from the base point pays infinite penalty. -/
theorem moreauYosidaPenalty_eq_top_of_edist_eq_top {τ : ℝ≥0}
    {x y : X} (hxy : edist x y = ∞) : moreauYosidaPenalty τ x y = ∞ := by
  simpa [moreauYosidaPenalty, hxy] using
    (ENNReal.top_div_of_ne_top
      (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ENNReal.coe_ne_top))

/-- A finite-energy resolvent step stays in the base point's finite-distance component.
The exclusion of `-∞` prevents the undefined extended-real sum `-∞ + ∞`. -/
theorem edist_ne_top_of_mem_metricResolventSet {φ : X → EReal} {τ : ℝ≥0}
    {x y : X} (hx : φ x ≠ ⊤) (hy : φ y ≠ ⊥)
    (hmin : y ∈ metricResolventSet φ τ x) : edist x y ≠ ∞ := by
  intro hxy
  have hpen := moreauYosidaPenalty_eq_top_of_edist_eq_top (τ := τ) hxy
  have hobj : moreauYosidaObjective φ τ x y = ⊤ := by
    simpa [moreauYosidaObjective, hpen] using EReal.add_top_of_ne_bot hy
  have hle := moreauYosidaObjective_le_of_mem_metricResolventSet hmin
  rw [hobj] at hle
  exact hx (top_le_iff.mp hle)

/-- The domain on which the metric resolvent has exactly one point. -/
def metricResolventDomain (φ : X → EReal) (τ : ℝ≥0) : Set X :=
  {x | ∃! y, y ∈ metricResolventSet φ τ x}

/-- The resolvent is single-valued at a base point exactly when it has a unique minimizer. -/
theorem mem_metricResolventDomain_iff (φ : X → EReal) (τ : ℝ≥0) (x : X) :
    x ∈ metricResolventDomain φ τ ↔ ∃! y, y ∈ metricResolventSet φ τ x :=
  Iff.rfl

/-- The single-valued metric resolvent, defined on its natural domain. -/
def metricResolvent (φ : X → EReal) (τ : ℝ≥0) (x : metricResolventDomain φ τ) : X :=
  Classical.choose x.property

/-- The selected resolvent belongs to the minimizing set. -/
theorem metricResolvent_mem (φ : X → EReal) (τ : ℝ≥0) (x : metricResolventDomain φ τ) :
    metricResolvent φ τ x ∈ metricResolventSet φ τ x :=
  (Classical.choose_spec x.property).1

/-- On its single-valued domain, the resolvent realizes the Moreau–Yosida infimum. -/
theorem moreauYosidaObjective_metricResolvent (φ : X → EReal) (τ : ℝ≥0)
    (x : metricResolventDomain φ τ) :
    moreauYosidaObjective φ τ x (metricResolvent φ τ x) = moreauYosida φ τ x :=
  (mem_metricResolventSet_iff φ τ x _).mp (metricResolvent_mem φ τ x)

/-- A minimizer equals the selected resolvent wherever the latter is single-valued. -/
theorem eq_metricResolvent_of_mem {φ : X → EReal} {τ : ℝ≥0}
    (x : metricResolventDomain φ τ) {y : X} (hy : y ∈ metricResolventSet φ τ x) :
    y = metricResolvent φ τ x :=
  (Classical.choose_spec x.property).2 y hy

end Pseudo

section Metric

variable [EMetricSpace X]

/-- The resolvent of the zero energy is the identity: the squared-distance penalty has its unique
minimum at the base point on an extended metric space. -/
@[simp]
theorem metricResolventSet_zero (τ : ℝ≥0) (x : X) :
    metricResolventSet (fun _ ↦ (0 : EReal)) τ x = {x} := by
  ext y
  constructor
  · intro hy
    have h := hy x
    simp only [moreauYosidaObjective, zero_add, moreauYosidaPenalty_self,
      EReal.coe_ennreal_zero] at h
    have hpen : moreauYosidaPenalty τ x y = 0 := by
      exact le_antisymm (EReal.coe_ennreal_le_coe_ennreal_iff.mp h) bot_le
    have hdist : edist x y = 0 := (moreauYosidaPenalty_eq_zero_iff τ x y).mp hpen
    exact Set.mem_singleton_iff.mpr (edist_eq_zero.mp hdist).symm
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    intro z
    simp [moreauYosidaObjective, EReal.coe_ennreal_nonneg]

/-- Every point has a single-valued resolvent for the zero energy. -/
@[simp]
theorem metricResolventDomain_zero (τ : ℝ≥0) :
    metricResolventDomain (fun _ : X ↦ (0 : EReal)) τ = Set.univ := by
  ext x
  simp [metricResolventDomain, metricResolventSet_zero]

/-- The selected resolvent of the zero energy is the identity. -/
@[simp]
theorem metricResolvent_zero (τ : ℝ≥0)
    (x : metricResolventDomain (fun _ : X ↦ (0 : EReal)) τ) :
    metricResolvent (fun _ : X ↦ (0 : EReal)) τ x = x := by
  have h := metricResolvent_mem (fun _ : X ↦ (0 : EReal)) τ x
  simpa only [metricResolventSet_zero, Set.mem_singleton_iff] using h

end Metric

end TauCeti

end

end
