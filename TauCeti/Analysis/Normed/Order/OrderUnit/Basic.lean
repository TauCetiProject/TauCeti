/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Order-unit spaces and the order-unit norm

An **order-unit space** is a real partially ordered vector space `E` whose order is compatible with
addition and nonnegative scalar multiplication, equipped with a distinguished nonzero element
`e : E` satisfying the order-unit property `∀ a, ∃ r > 0, -r • e ≤ a ∧ a ≤ r • e` and the
Archimedean property `(∀ ε > 0, a ≤ ε • e) → a ≤ 0`. On any such space, the formula

```text
‖a‖ = inf { r ≥ 0 : -r • e ≤ a ∧ a ≤ r • e }
```

defines a norm (`orderUnitNorm e`), called the **order-unit norm**, characterized by `‖e‖ = 1` and
the closed-interval equivalence `‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e` for all `r ≥ 0`.

Rather than bundling the norm in a wrapper type, this file expresses compatibility of an existing
norm and partial order with an order unit `e` via the predicate `IsOrderUnitNorm e`. Every space
carrying `IsOrderUnitNorm e` automatically satisfies `PosSMulMono ℝ E`, the Archimedean property,
definiteness of the seminorm, closedness of the positive cone (with `e` in its interior), and the
norm characterization of positivity `0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖`.

## Main definitions and results

* `TauCeti.OrderUnit.IsArchimedeanOrderUnit`: the algebraic order-unit and Archimedean axioms.
* `TauCeti.OrderUnit.orderUnitNorm`: the infimal norm `inf { r ≥ 0 : -r • e ≤ a ∧ a ≤ r • e }`.
* `TauCeti.OrderUnit.IsArchimedeanOrderUnit.normedAddCommGroup` and
  `TauCeti.OrderUnit.IsArchimedeanOrderUnit.normedSpace`: the normed-space structure induced by
  `orderUnitNorm e`, satisfying `IsOrderUnitNorm e`.
* `TauCeti.OrderUnit.IsOrderUnitNorm`: predicate asserting `‖e‖ = 1` and the interval formula
  `‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e` for `r ≥ 0`.
* `TauCeti.OrderUnit.IsOrderUnitNorm.nonneg_iff`, `isClosed_nonneg`, `mem_interior_nonneg`,
  `posSMulMono`, `archimedean`: order and topological properties recovered from `IsOrderUnitNorm`.
* Constructions preserving `IsOrderUnitNorm`: unital submodules (`submodule`), binary and finite
  products (`prod`, `pi`), automatic isometry of unital order embeddings
  (`IsOrderUnitNorm.norm_map_eq_of_map_nonneg_iff`,
  `IsOrderUnitNorm.linearIsometryEquivOfMapNonnegIff`), and the norm completion
  (`completionPosCone`, `completionPartialOrder`, `completion_le_iff`,
  `isOrderUnitNorm_completion`).
* Basic examples: `ℝ` and `ι → ℝ` for finite nonempty `ι`.

## References

* Marc A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, Section 1.
* Richard V. Kadison, *A representation theory for commutative topological algebra*,
  Mem. Amer. Math. Soc. 7 (1951).
-/

public section

open Set Metric
open scoped Topology

namespace TauCeti.OrderUnit

/-! ### Core predicates -/

/-- An **Archimedean order unit** in a real ordered vector space is a nonzero element `e` that
dominates every element up to a positive real multiple and satisfies the Archimedean condition
`(∀ ε > 0, a ≤ ε • e) → a ≤ 0`. -/
structure IsArchimedeanOrderUnit {E : Type*} [Zero E] [SMul ℝ E] [LE E] (e : E) : Prop where
  /-- The order unit is nonzero. -/
  ne_zero : e ≠ 0
  /-- Every element lies in some symmetric order interval `[-r • e, r • e]` with `r > 0`. -/
  orderUnit : ∀ a : E, ∃ r : ℝ, 0 < r ∧ -r • e ≤ a ∧ a ≤ r • e
  /-- The Archimedean property: `a ≤ ε • e` for all `ε > 0` implies `a ≤ 0`. -/
  archimedean : ∀ a : E, (∀ ε : ℝ, 0 < ε → a ≤ ε • e) → a ≤ 0

/-- Compatibility of an existing norm and partial order with a distinguished order unit `e`:
`‖e‖ = 1` and `‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e` for all `r ≥ 0`. -/
structure IsOrderUnitNorm {E : Type*} [Norm E] [SMul ℝ E] [LE E] (e : E) : Prop where
  /-- The order unit has norm `1`. -/
  norm_e : ‖e‖ = 1
  /-- Closed norm balls coincide with symmetric order intervals around `0`. -/
  norm_le_iff : ∀ (a : E) (r : ℝ), 0 ≤ r → (‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e)

/-- The **order-unit norm** associated with `e`: the infimum of all `r ≥ 0` such that
`-r • e ≤ a ≤ r • e`. -/
noncomputable def orderUnitNorm {E : Type*} [SMul ℝ E] [LE E] (e : E) (a : E) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}

/-- Unfolding lemma for `orderUnitNorm`. -/
theorem orderUnitNorm_def {E : Type*} [SMul ℝ E] [LE E] (e a : E) :
    orderUnitNorm e a = sInf {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e} :=
  (rfl)

/-! ### Construction of the order-unit norm from an Archimedean order unit -/

section Archimedean

private theorem bddBelow_orderUnitSet {E : Type*} [SMul ℝ E] [LE E] (e a : E) :
    BddBelow {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e} :=
  ⟨0, fun _ hr => hr.1⟩

/-- The order-unit norm is always nonnegative. -/
theorem orderUnitNorm_nonneg {E : Type*} [SMul ℝ E] [LE E] (e a : E) :
    0 ≤ orderUnitNorm e a :=
  Real.sInf_nonneg fun _ hr => hr.1

/-- Any `r ≥ 0` with `-r • e ≤ a ≤ r • e` bounds `orderUnitNorm e a` from above. -/
theorem orderUnitNorm_le_of_mem {E : Type*} [SMul ℝ E] [LE E] {e a : E} {r : ℝ} (hr : 0 ≤ r)
    (hlo : -r • e ≤ a) (hhi : a ≤ r • e) : orderUnitNorm e a ≤ r :=
  csInf_le (bddBelow_orderUnitSet e a) ⟨hr, hlo, hhi⟩

/-- The order-unit norm of `0` is `0`. -/
@[simp]
theorem orderUnitNorm_zero {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E] (e : E) :
    orderUnitNorm e 0 = 0 :=
  le_antisymm (orderUnitNorm_le_of_mem le_rfl (by simp) (by simp)) (orderUnitNorm_nonneg e 0)

/-- The order-unit norm is invariant under negation. -/
@[simp]
theorem orderUnitNorm_neg {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] (e a : E) : orderUnitNorm e (-a) = orderUnitNorm e a := by
  unfold orderUnitNorm
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, neg_smul, neg_le_neg_iff, neg_le]
  tauto

/-- `orderUnitNorm e` coincides with the Minkowski gauge of `Set.Icc (-e) e`. -/
theorem orderUnitNorm_eq_gauge {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
    [PosSMulMono ℝ E] (e a : E) :
    orderUnitNorm e a = gauge (Set.Icc (-e) e) a := by
  by_cases ha : a = 0
  · subst ha
    simp
  rw [orderUnitNorm_def, gauge_def']
  congr 1
  ext r
  refine ⟨fun ⟨hr, hlo, hhi⟩ => ?_, fun ⟨hr, hlo, hhi⟩ => ?_⟩
  · have hrpos : 0 < r := lt_of_le_of_ne hr fun h0 => by
      subst h0
      simp only [neg_zero, zero_smul] at hlo hhi
      exact ha (le_antisymm hhi hlo)
    refine ⟨hrpos, ?_, ?_⟩
    · have h := smul_le_smul_of_nonneg_left hlo (inv_nonneg.mpr hrpos.le)
      simpa [smul_smul, hrpos.ne'] using h
    · have h := smul_le_smul_of_nonneg_left hhi (inv_nonneg.mpr hrpos.le)
      simpa [smul_smul, hrpos.ne'] using h
  · refine ⟨hr.le, ?_, ?_⟩
    · have h := smul_le_smul_of_nonneg_left hlo hr.le
      simpa [smul_smul, hr.ne', neg_smul] using h
    · have h := smul_le_smul_of_nonneg_left hhi hr.le
      simpa [smul_smul, hr.ne'] using h

private theorem IsArchimedeanOrderUnit.nonempty_set {E : Type*} [Zero E] [SMul ℝ E] [LE E]
    {e : E} (he : IsArchimedeanOrderUnit e) (a : E) :
    {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}.Nonempty := by
  obtain ⟨r, hr, hlo, hhi⟩ := he.orderUnit a
  exact ⟨r, hr.le, hlo, hhi⟩

/-- An Archimedean order unit is nonnegative. -/
theorem IsArchimedeanOrderUnit.nonneg_unit {E : Type*} [AddCommGroup E] [Module ℝ E]
    [PartialOrder E] [PosSMulMono ℝ E] {e : E} (he : IsArchimedeanOrderUnit e) : 0 ≤ e := by
  obtain ⟨r, hr, _, hhi⟩ := he.orderUnit 0
  have h := smul_le_smul_of_nonneg_left hhi (inv_nonneg.mpr hr.le)
  simpa [smul_smul, hr.ne'] using h

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e : E} (he : IsArchimedeanOrderUnit e)

include he

/-- Every element is bounded above by `orderUnitNorm e a • e`. -/
theorem IsArchimedeanOrderUnit.le_orderUnitNorm_smul (a : E) :
    a ≤ orderUnitNorm e a • e := by
  rw [← sub_nonpos]
  refine he.archimedean (a - orderUnitNorm e a • e) fun ε hε => ?_
  rw [sub_le_iff_le_add, add_comm, ← add_smul]
  have hlt : orderUnitNorm e a < orderUnitNorm e a + ε := lt_add_of_pos_right _ hε
  obtain ⟨r, hr, hrl⟩ := (csInf_lt_iff (bddBelow_orderUnitSet e a) (he.nonempty_set a)).mp hlt
  exact hr.2.2.trans (smul_le_smul_of_nonneg_right hrl.le he.nonneg_unit)

/-- Every element is bounded below by `-orderUnitNorm e a • e`. -/
theorem IsArchimedeanOrderUnit.neg_orderUnitNorm_smul_le (a : E) :
    -(orderUnitNorm e a) • e ≤ a := by
  have h := he.le_orderUnitNorm_smul (-a)
  rw [orderUnitNorm_neg] at h
  simpa [neg_smul] using neg_le.mp h

/-- The closed-interval characterization of the constructed order-unit norm. -/
theorem IsArchimedeanOrderUnit.orderUnitNorm_le_iff (a : E) {r : ℝ} (hr : 0 ≤ r) :
    orderUnitNorm e a ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hlo, hhi⟩ => orderUnitNorm_le_of_mem hr hlo hhi⟩
  · exact (smul_le_smul_of_nonneg_right (neg_le_neg h) he.nonneg_unit).trans
      (he.neg_orderUnitNorm_smul_le a)
  · exact (he.le_orderUnitNorm_smul a).trans (smul_le_smul_of_nonneg_right h he.nonneg_unit)

/-- The order-unit norm vanishes only at `0`. -/
theorem IsArchimedeanOrderUnit.orderUnitNorm_eq_zero_iff {a : E} :
    orderUnitNorm e a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ orderUnitNorm_zero e⟩
  have ⟨hlo, hhi⟩ := (he.orderUnitNorm_le_iff a le_rfl).mp h.le
  simp only [neg_zero, zero_smul] at hlo hhi
  exact le_antisymm hhi hlo

/-- The order-unit norm of the order unit `e` itself is `1`. -/
theorem IsArchimedeanOrderUnit.orderUnitNorm_unit : orderUnitNorm e e = 1 := by
  refine le_antisymm ?_ (le_csInf (he.nonempty_set e) ?_)
  · refine orderUnitNorm_le_of_mem zero_le_one ?_ (by simp)
    rw [neg_smul, one_smul]
    exact (neg_nonpos.mpr he.nonneg_unit).trans he.nonneg_unit
  · intro r ⟨_, _, hhi⟩
    by_contra hlt
    push Not at hlt
    have hpos : 0 < 1 - r := sub_pos.mpr hlt
    have hle : (1 - r) • e ≤ 0 := by
      rw [sub_smul, one_smul, sub_nonpos]
      exact hhi
    have he0 : e ≤ 0 := by
      have h := smul_le_smul_of_nonneg_left hle (inv_nonneg.mpr hpos.le)
      simpa [smul_smul, hpos.ne'] using h
    exact he.ne_zero (le_antisymm he0 he.nonneg_unit)

private theorem IsArchimedeanOrderUnit.balanced_Icc_neg_unit :
    Balanced ℝ (Set.Icc (-e) e) := by
  refine balanced_iff_smul_mem.mpr fun {r} hr {x} hx => ?_
  have hrabs : |r| ≤ 1 := by simpa [Real.norm_eq_abs] using hr
  have hnonneg : ∀ (c : ℝ), 0 ≤ c → c ≤ 1 → ∀ z : E,
      -e ≤ z → z ≤ e → c • z ∈ Set.Icc (-e) e := fun c hc0 hc1 z hzlo hzhi => by
    refine ⟨?_, ?_⟩
    · calc
        -e = (-1 : ℝ) • e := by simp
        _ ≤ (-c) • e := smul_le_smul_of_nonneg_right (neg_le_neg hc1) he.nonneg_unit
        _ = c • (-e) := by rw [neg_smul, smul_neg]
        _ ≤ c • z := smul_le_smul_of_nonneg_left hzlo hc0
    · calc
        c • z ≤ c • e := smul_le_smul_of_nonneg_left hzhi hc0
        _ ≤ (1 : ℝ) • e := smul_le_smul_of_nonneg_right hc1 he.nonneg_unit
        _ = e := one_smul ℝ e
  rcases le_total 0 r with hr0 | hr0
  · exact hnonneg r hr0 (le_of_abs_le hrabs) x hx.1 hx.2
  · rw [← neg_smul_neg]
    exact hnonneg (-r) (neg_nonneg.mpr hr0) (by simpa [abs_of_nonpos hr0] using hrabs)
      (-x) (neg_le_neg hx.2) (by simpa using neg_le_neg hx.1)

private theorem IsArchimedeanOrderUnit.absorbent_Icc_neg_unit :
    Absorbent ℝ (Set.Icc (-e) e) := by
  intro x
  obtain ⟨r, hr, hlo, hhi⟩ := he.orderUnit x
  have hrx : r⁻¹ • x ∈ Set.Icc (-e) e := by
    refine ⟨?_, ?_⟩
    · have h := smul_le_smul_of_nonneg_left hlo (inv_nonneg.mpr hr.le)
      simpa [smul_smul, hr.ne'] using h
    · have h := smul_le_smul_of_nonneg_left hhi (inv_nonneg.mpr hr.le)
      simpa [smul_smul, hr.ne'] using h
  refine Absorbs.of_norm ⟨r, fun c hc => ?_⟩
  have hc0 : c ≠ 0 := by
    intro h0
    simp [h0] at hc
    linarith
  rw [Set.singleton_subset_iff, Set.mem_smul_set_iff_inv_smul_mem₀ hc0]
  have hnorm : ‖r * c⁻¹‖ ≤ 1 := by
    rw [norm_mul, norm_inv, Real.norm_of_nonneg hr.le]
    exact mul_inv_le_one_of_le₀ hc (norm_nonneg c)
  have hmem := he.balanced_Icc_neg_unit.smul_mem hnorm hrx
  rwa [smul_smul, mul_comm r c⁻¹, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one] at hmem

/-- The order-unit norm is absolutely homogeneous. -/
theorem IsArchimedeanOrderUnit.orderUnitNorm_smul (c : ℝ) (a : E) :
    orderUnitNorm e (c • a) = |c| * orderUnitNorm e a := by
  rw [orderUnitNorm_eq_gauge, orderUnitNorm_eq_gauge,
    gauge_smul he.balanced_Icc_neg_unit, Real.norm_eq_abs]

/-- The order-unit norm satisfies the triangle inequality. -/
theorem IsArchimedeanOrderUnit.orderUnitNorm_add_le (a b : E) :
    orderUnitNorm e (a + b) ≤ orderUnitNorm e a + orderUnitNorm e b := by
  rw [orderUnitNorm_eq_gauge, orderUnitNorm_eq_gauge, orderUnitNorm_eq_gauge]
  exact gauge_add_le (convex_Icc (-e) e) he.absorbent_Icc_neg_unit a b

/-- The `NormedSpace.Core` data for the order-unit norm `orderUnitNorm e`. -/
theorem IsArchimedeanOrderUnit.normedSpaceCore :
    @NormedSpace.Core ℝ E _ _ _ ⟨orderUnitNorm e⟩ := by
  let : Norm E := ⟨orderUnitNorm e⟩
  exact
    { norm_nonneg := orderUnitNorm_nonneg e
      norm_smul := fun c a => by simpa [Real.norm_eq_abs] using he.orderUnitNorm_smul c a
      norm_triangle := he.orderUnitNorm_add_le
      norm_eq_zero_iff := fun _ => he.orderUnitNorm_eq_zero_iff }

/-- The `NormedAddCommGroup` structure induced by an Archimedean order unit `e`. -/
@[instance_reducible]
noncomputable def IsArchimedeanOrderUnit.normedAddCommGroup : NormedAddCommGroup E :=
  @NormedAddCommGroup.ofCore ℝ E _ _ _ ⟨orderUnitNorm e⟩ he.normedSpaceCore

/-- The `NormedSpace ℝ` structure induced by an Archimedean order unit `e`. -/
@[instance_reducible]
noncomputable def IsArchimedeanOrderUnit.normedSpace :
    @NormedSpace ℝ E _ he.normedAddCommGroup.toSeminormedAddCommGroup :=
  @NormedSpace.ofCore ℝ E _ he.normedAddCommGroup.toSeminormedAddCommGroup _ he.normedSpaceCore

/-- The norm of `he.normedAddCommGroup` is `orderUnitNorm e`. -/
@[simp]
theorem IsArchimedeanOrderUnit.norm_eq_orderUnitNorm (a : E) :
    @norm E he.normedAddCommGroup.toNorm a = orderUnitNorm e a :=
  (rfl)

/-- The norm constructed from an Archimedean order unit satisfies `IsOrderUnitNorm e`. -/
theorem IsArchimedeanOrderUnit.isOrderUnitNorm :
    @IsOrderUnitNorm E he.normedAddCommGroup.toNorm _ _ e := by
  let : Norm E := he.normedAddCommGroup.toNorm
  exact ⟨he.orderUnitNorm_unit, fun a r hr => he.orderUnitNorm_le_iff a hr⟩

end Archimedean

/-! ### Fundamental properties of `IsOrderUnitNorm` -/

/-- Any norm satisfying `IsOrderUnitNorm e` coincides with `orderUnitNorm e`. -/
theorem IsOrderUnitNorm.norm_eq_orderUnitNorm {E : Type*} [SeminormedAddCommGroup E]
    [SMul ℝ E] [LE E] {e : E} (he : IsOrderUnitNorm e) (a : E) :
    ‖a‖ = orderUnitNorm e a := by
  have hset : {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e} = Set.Ici ‖a‖ := by
    ext r
    exact ⟨fun ⟨hr, hlo, hhi⟩ => (he.norm_le_iff a r hr).mpr ⟨hlo, hhi⟩,
      fun hr => let h0 : 0 ≤ r := (norm_nonneg a).trans hr
        ⟨h0, (he.norm_le_iff a r h0).mp hr⟩⟩
  rw [orderUnitNorm_def, hset, csInf_Ici]

section BasicMinimal

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  {e : E} (he : IsOrderUnitNorm e)

include he

/-- Every element is bounded below by `-‖a‖ • e`. -/
theorem IsOrderUnitNorm.neg_norm_smul_le (a : E) : -‖a‖ • e ≤ a :=
  ((he.norm_le_iff a ‖a‖ (norm_nonneg a)).mp le_rfl).1

/-- Every element is bounded above by `‖a‖ • e`. -/
theorem IsOrderUnitNorm.le_norm_smul (a : E) : a ≤ ‖a‖ • e :=
  ((he.norm_le_iff a ‖a‖ (norm_nonneg a)).mp le_rfl).2

/-- Every nonnegative scalar multiple of an order unit is nonnegative. -/
theorem IsOrderUnitNorm.smul_nonneg_unit {r : ℝ} (hr : 0 ≤ r) : 0 ≤ r • e :=
  ((he.norm_le_iff 0 r hr).mp (by simpa using hr)).2

/-- An order unit is nonnegative. -/
theorem IsOrderUnitNorm.nonneg_unit : 0 ≤ e := by
  simpa using he.smul_nonneg_unit zero_le_one

/-- An order unit is nonzero. -/
theorem IsOrderUnitNorm.ne_zero : e ≠ 0 := by
  intro h
  have := he.norm_e
  simp [h] at this

/-- A space carrying an order-unit norm is nontrivial. -/
theorem IsOrderUnitNorm.nontrivial : Nontrivial E :=
  ⟨⟨e, 0, he.ne_zero⟩⟩

/-- An order-unit seminorm is automatically definite (`‖a‖ = 0 ↔ a = 0`). -/
theorem IsOrderUnitNorm.norm_eq_zero_iff {a : E} : ‖a‖ = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have ⟨hlo, hhi⟩ := (he.norm_le_iff a 0 le_rfl).mp h.le
  simp only [neg_zero, zero_smul] at hlo hhi
  exact le_antisymm hhi hlo

/-- Scalar multiples of the order unit satisfy `‖r • e‖ = |r|`. -/
theorem IsOrderUnitNorm.norm_smul_unit (r : ℝ) : ‖r • e‖ = |r| := by
  rw [norm_smul, Real.norm_eq_abs, he.norm_e, mul_one]

end BasicMinimal

section BasicOrdered

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- For a nonnegative element `a`, `‖a‖ ≤ r` is equivalent to `a ≤ r • e`. -/
theorem IsOrderUnitNorm.norm_le_iff_of_nonneg {a : E} (ha : 0 ≤ a) {r : ℝ} (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ a ≤ r • e := by
  rw [he.norm_le_iff a r hr, and_iff_right_iff_imp]
  intro _
  have hneg : -r • e ≤ 0 := by
    rw [neg_smul, neg_nonpos]
    exact he.smul_nonneg_unit hr
  exact hneg.trans ha

/-- Monotonicity of the order-unit norm on symmetric order intervals: `-b ≤ a ≤ b` implies
`‖a‖ ≤ ‖b‖`. -/
theorem IsOrderUnitNorm.norm_le_norm_of_le {a b : E} (hlo : -b ≤ a) (hhi : a ≤ b) :
    ‖a‖ ≤ ‖b‖ := by
  refine (he.norm_le_iff a ‖b‖ (norm_nonneg b)).mpr ⟨?_, hhi.trans (he.le_norm_smul b)⟩
  have h : -‖b‖ • e ≤ -b := by
    rw [neg_smul]
    exact neg_le_neg (he.le_norm_smul b)
  exact h.trans hlo

/-- On the positive cone, the order-unit norm is monotone: `0 ≤ a ≤ b` implies `‖a‖ ≤ ‖b‖`. -/
theorem IsOrderUnitNorm.norm_le_norm_of_nonneg_le {a b : E} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖a‖ ≤ ‖b‖ :=
  he.norm_le_norm_of_le ((neg_nonpos.mpr (ha.trans hab)).trans ha) hab

/-- Recovery of the positive cone from the norm and the order unit:
`0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖`. -/
theorem IsOrderUnitNorm.nonneg_iff {a : E} : 0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖ := by
  rw [he.norm_le_iff (‖a‖ • e - a) ‖a‖ (norm_nonneg a)]
  refine ⟨fun ha => ⟨?_, sub_le_self _ ha⟩, fun ⟨_, hhi⟩ => ?_⟩
  · have hneg : -‖a‖ • e ≤ 0 := by
      rw [neg_smul, neg_nonpos]
      exact he.smul_nonneg_unit (norm_nonneg a)
    exact hneg.trans (sub_nonneg.mpr (he.le_norm_smul a))
  · exact le_add_iff_nonneg_right (‖a‖ • e) |>.mp (sub_le_iff_le_add.mp hhi)

/-- An element `a` is nonnegative iff `‖r • e - a‖ ≤ r` for some `r ≥ 0`. -/
theorem IsOrderUnitNorm.nonneg_iff_exists {a : E} :
    0 ≤ a ↔ ∃ r : ℝ, 0 ≤ r ∧ ‖r • e - a‖ ≤ r := by
  refine ⟨fun ha => ⟨‖a‖, norm_nonneg a, he.nonneg_iff.mp ha⟩, fun ⟨r, hr, hle⟩ => ?_⟩
  have hhi := ((he.norm_le_iff (r • e - a) r hr).mp hle).2
  exact le_add_iff_nonneg_right (r • e) |>.mp (sub_le_iff_le_add.mp hhi)

/-- Recovery of the partial order from the norm and the order unit. -/
theorem IsOrderUnitNorm.le_iff {a b : E} :
    a ≤ b ↔ ‖‖b - a‖ • e - (b - a)‖ ≤ ‖b - a‖ := by
  rw [← sub_nonneg, he.nonneg_iff]

/-- Compatibility of the partial order with nonnegative scalar multiplication follows
automatically from `IsOrderUnitNorm`. -/
theorem IsOrderUnitNorm.posSMulMono : PosSMulMono ℝ E := by
  refine ⟨fun c hc a b hab => ?_⟩
  rw [← sub_nonneg, ← smul_sub, he.nonneg_iff]
  have hx : ‖‖b - a‖ • e - (b - a)‖ ≤ ‖b - a‖ := he.nonneg_iff.mp (sub_nonneg.mpr hab)
  calc
    ‖‖c • (b - a)‖ • e - c • (b - a)‖
        = ‖c • (‖b - a‖ • e - (b - a))‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_smul, ← smul_sub]
    _ = c * ‖‖b - a‖ • e - (b - a)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ c * ‖b - a‖ := mul_le_mul_of_nonneg_left hx hc
    _ = ‖c • (b - a)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

/-- The interval formula forces the order to be Archimedean: if `a ≤ ε • e` for every `ε > 0`,
then `a ≤ 0`. -/
theorem IsOrderUnitNorm.archimedean {a : E} (h : ∀ ε : ℝ, 0 < ε → a ≤ ε • e) : a ≤ 0 := by
  have hbound : ∀ ε : ℝ, 0 < ε → ‖‖a‖ • e + a‖ ≤ ‖a‖ + ε := by
    intro ε hε
    have hr : 0 ≤ ‖a‖ + ε := add_nonneg (norm_nonneg a) hε.le
    refine (he.norm_le_iff (‖a‖ • e + a) (‖a‖ + ε) hr).mpr ⟨?_, ?_⟩
    · have h0 : 0 ≤ ‖a‖ • e + a := by
        have hlo := he.neg_norm_smul_le a
        rw [neg_smul] at hlo
        exact neg_le_iff_add_nonneg'.mp hlo
      have hneg : -(‖a‖ + ε) • e ≤ 0 := by
        rw [neg_smul, neg_nonpos]
        exact he.smul_nonneg_unit hr
      exact hneg.trans h0
    · rw [add_smul]
      exact add_le_add_right (h ε hε) _
  have hle : ‖‖-a‖ • e - (-a)‖ ≤ ‖-a‖ := by
    simpa [norm_neg, sub_neg_eq_add] using le_of_forall_pos_le_add hbound
  exact neg_nonneg.mp (he.nonneg_iff.mpr hle)

/-- A space carrying `IsOrderUnitNorm e` satisfies `IsArchimedeanOrderUnit e`. -/
theorem IsOrderUnitNorm.isArchimedeanOrderUnit : IsArchimedeanOrderUnit e where
  ne_zero := he.ne_zero
  orderUnit a := ⟨‖a‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg a) zero_lt_one,
    (he.norm_le_iff a (‖a‖ + 1) (by linarith [norm_nonneg a])).mp (by linarith)⟩
  archimedean _ := he.archimedean

/-- The positive cone `{a : E | 0 ≤ a}` is norm closed. -/
theorem IsOrderUnitNorm.isClosed_nonneg : IsClosed {a : E | 0 ≤ a} := by
  have hset : {a : E | 0 ≤ a} = {a : E | ‖‖a‖ • e - a‖ ≤ ‖a‖} :=
    Set.ext fun _ => he.nonneg_iff
  rw [hset]
  exact isClosed_le
    (((continuous_norm.smul continuous_const).sub continuous_id).norm)
    continuous_norm

/-- The order of an order-unit space is closed in the norm topology. -/
theorem IsOrderUnitNorm.orderClosedTopology : OrderClosedTopology E :=
  ⟨isClosed_le_of_isClosed_nonneg he.isClosed_nonneg⟩

/-- The closed unit ball around the order unit `e` lies inside the positive cone. -/
theorem IsOrderUnitNorm.closedBall_subset_nonneg : closedBall e 1 ⊆ {a : E | 0 ≤ a} := by
  intro a ha
  rw [mem_closedBall_iff_norm] at ha
  have hlo := ((he.norm_le_iff (a - e) 1 zero_le_one).mp ha).1
  rw [neg_smul, one_smul] at hlo
  exact sub_nonneg.mp (by simpa [sub_eq_add_neg, add_comm] using add_le_add_left hlo e)

/-- The order unit `e` is an interior point of the positive cone. -/
theorem IsOrderUnitNorm.mem_interior_nonneg : e ∈ interior {a : E | 0 ≤ a} :=
  mem_interior.mpr ⟨ball e 1, ball_subset_closedBall.trans he.closedBall_subset_nonneg,
    isOpen_ball, mem_ball_self zero_lt_one⟩

end BasicOrdered

/-! ### Constructions preserving `IsOrderUnitNorm` -/

section Constructions

/-- Restricting an order-unit space to a real subspace containing `e` yields an order-unit space
with the inherited norm and order. -/
theorem IsOrderUnitNorm.submodule {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [PartialOrder E] {e : E} (he : IsOrderUnitNorm e) (S : Submodule ℝ E) (hmem : e ∈ S) :
    IsOrderUnitNorm (⟨e, hmem⟩ : S) where
  norm_e := he.norm_e
  norm_le_iff a r hr := he.norm_le_iff a.1 r hr

/-- The product of two order-unit spaces, with the coordinatewise order and maximum norm, has order
unit `(e, f)`. -/
theorem IsOrderUnitNorm.prod {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [PartialOrder E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
    {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) :
    IsOrderUnitNorm (e, f) where
  norm_e := by simp [Prod.norm_def, he.norm_e, hf.norm_e]
  norm_le_iff a r hr := by
    rcases a with ⟨a₁, a₂⟩
    rw [Prod.norm_def, max_le_iff, he.norm_le_iff a₁ r hr, hf.norm_le_iff a₂ r hr]
    simp only [Prod.smul_mk, Prod.mk_le_mk]
    tauto

/-- A finite nonempty product of order-unit spaces, with the coordinatewise order and supremum
norm, is an order-unit space. -/
theorem IsOrderUnitNorm.pi {ι : Type*} [Fintype ι] [Nonempty ι] {G : ι → Type*}
    [∀ i, SeminormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
    [∀ i, PartialOrder (G i)]
    {e : ∀ i, G i} (he : ∀ i, IsOrderUnitNorm (e i)) : IsOrderUnitNorm e where
  norm_e := by
    refine le_antisymm ?_ ?_
    · exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (he i).norm_e.le
    · obtain ⟨i₀⟩ := ‹Nonempty ι›
      exact (he i₀).norm_e.symm.trans_le (norm_le_pi_norm e i₀)
  norm_le_iff a r hr := by
    rw [pi_norm_le_iff_of_nonneg hr]
    simp only [fun i => (he i).norm_le_iff (a i) r hr, Pi.le_def, Pi.smul_apply]
    exact forall_and

section Maps

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
  [IsOrderedAddMonoid F]

/-- A unital real-linear map between order-unit spaces that preserves and reflects positivity is
automatically isometric. -/
theorem IsOrderUnitNorm.norm_map_eq_of_map_nonneg_iff {e : E} {f : F} (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E →ₗ[ℝ] F) (hTe : T e = f)
    (hpos : ∀ a : E, 0 ≤ T a ↔ 0 ≤ a) (a : E) : ‖T a‖ = ‖a‖ := by
  have hle_iff (x y : E) : T x ≤ T y ↔ x ≤ y := by
    rw [← sub_nonneg, ← map_sub, hpos, sub_nonneg]
  have hle : ∀ r : ℝ, 0 ≤ r → (‖T a‖ ≤ r ↔ ‖a‖ ≤ r) := fun r hr => by
    rw [hf.norm_le_iff (T a) r hr, he.norm_le_iff a r hr, ← hTe, ← map_smul, ← map_smul,
      hle_iff, hle_iff]
  exact le_antisymm ((hle ‖a‖ (norm_nonneg a)).mpr le_rfl)
    ((hle ‖T a‖ (norm_nonneg (T a))).mp le_rfl)

/-- A unital linear order isomorphism between order-unit spaces is automatically a linear
isometry equivalence. -/
def IsOrderUnitNorm.linearIsometryEquivOfMapNonnegIff {e : E} {f : F} (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E ≃ₗ[ℝ] F) (hTe : T e = f)
    (hpos : ∀ a : E, 0 ≤ T a ↔ 0 ≤ a) : E ≃ₗᵢ[ℝ] F where
  toLinearEquiv := T
  norm_map' := he.norm_map_eq_of_map_nonneg_iff hf T.toLinearMap hTe hpos

/-- Evaluating `linearIsometryEquivOfMapNonnegIff` agrees with the underlying linear equivalence. -/
@[simp]
theorem IsOrderUnitNorm.linearIsometryEquivOfMapNonnegIff_apply {e : E} {f : F}
    (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : E ≃ₗ[ℝ] F) (hTe : T e = f)
    (hpos : ∀ a : E, 0 ≤ T a ↔ 0 ≤ a) (a : E) :
    he.linearIsometryEquivOfMapNonnegIff hf T hTe hpos a = T a :=
  (rfl)

/-- Evaluating the inverse of `linearIsometryEquivOfMapNonnegIff` agrees with `T.symm`. -/
@[simp]
theorem IsOrderUnitNorm.linearIsometryEquivOfMapNonnegIff_symm_apply {e : E} {f : F}
    (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : E ≃ₗ[ℝ] F) (hTe : T e = f)
    (hpos : ∀ a : E, 0 ≤ T a ↔ 0 ≤ a) (b : F) :
    (he.linearIsometryEquivOfMapNonnegIff hf T hTe hpos).symm b = T.symm b :=
  (rfl)

/-- Transport of `IsOrderUnitNorm` back along a linear isometric order embedding. -/
theorem IsOrderUnitNorm.of_linearIsometry {e : E} {f : F} (hf : IsOrderUnitNorm f)
    (T : E →ₗᵢ[ℝ] F) (hTe : T e = f) (hpos : ∀ a : E, 0 ≤ T a ↔ 0 ≤ a) :
    IsOrderUnitNorm e where
  norm_e := by rw [← T.norm_map e, hTe, hf.norm_e]
  norm_le_iff a r hr := by
    have hle_iff (x y : E) : T x ≤ T y ↔ x ≤ y := by
      rw [← sub_nonneg, ← map_sub, hpos, sub_nonneg]
    rw [← T.norm_map a, hf.norm_le_iff (T a) r hr, ← hTe, ← map_smul, ← map_smul,
      hle_iff, hle_iff]

end Maps

end Constructions

/-! ### Norm completion of an order-unit space -/

section Completion

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- The closed positive cone in the norm completion `UniformSpace.Completion E`, obtained by
mapping `ProperCone.positive ℝ E` along `E →L[ℝ] UniformSpace.Completion E`. -/
noncomputable def IsOrderUnitNorm.completionPosCone : ProperCone ℝ (UniformSpace.Completion E) :=
  let : PosSMulMono ℝ E := he.posSMulMono
  have : OrderClosedTopology E := he.orderClosedTopology
  (ProperCone.positive ℝ E).map (UniformSpace.Completion.toComplL (S := ℝ) (α := E))

/-- As a set, `he.completionPosCone` is the closure of the image of the positive cone of `E`. -/
theorem IsOrderUnitNorm.coe_completionPosCone :
    (he.completionPosCone : Set (UniformSpace.Completion E)) =
      closure (((↑) : E → UniformSpace.Completion E) '' Set.Ici (0 : E)) := by
  let : PosSMulMono ℝ E := he.posSMulMono
  have : OrderClosedTopology E := he.orderClosedTopology
  ext x
  simp only [IsOrderUnitNorm.completionPosCone, SetLike.mem_coe, ProperCone.mem_map]
  change x ∈ ((PointedCone.map (UniformSpace.Completion.toComplL (S := ℝ) (α := E) :
    E →ₗ[ℝ] UniformSpace.Completion E) (ProperCone.positive ℝ E).toPointedCone).topologicalClosure :
    Set (UniformSpace.Completion E)) ↔ _
  rw [Submodule.topologicalClosure_coe, PointedCone.coe_map, ProperCone.toPointedCone_positive]
  have himg : ((UniformSpace.Completion.toComplL (S := ℝ) (α := E) :
      E →ₗ[ℝ] UniformSpace.Completion E) '' (PointedCone.positive ℝ E : Set E)) =
      (((↑) : E → UniformSpace.Completion E) '' Set.Ici (0 : E)) := by
    ext y
    simp [UniformSpace.Completion.toComplL]
  rw [himg]

/-- An element of `E` lies in `he.completionPosCone` iff it is nonnegative in `E`. -/
theorem IsOrderUnitNorm.coe_mem_completionPosCone_iff {a : E} :
    (a : UniformSpace.Completion E) ∈ he.completionPosCone ↔ 0 ≤ a := by
  have h := (UniformSpace.Completion.isUniformInducing_coe E).isInducing
    |>.closure_eq_preimage_closure_image (Set.Ici (0 : E))
  have hcl : closure (Set.Ici (0 : E)) = Set.Ici (0 : E) := he.isClosed_nonneg.closure_eq
  rw [hcl] at h
  change (a : UniformSpace.Completion E) ∈ (he.completionPosCone : Set _) ↔ 0 ≤ a
  rw [he.coe_completionPosCone]
  exact Set.ext_iff.mp h.symm a

private theorem IsOrderUnitNorm.norm_sub_le_norm_add_of_mem_completionPosCone
    {u v : UniformSpace.Completion E}
    (hu : u ∈ he.completionPosCone) (hv : v ∈ he.completionPosCone) :
    ‖u - v‖ ≤ ‖u + v‖ := by
  change u ∈ (he.completionPosCone : Set _) at hu
  change v ∈ (he.completionPosCone : Set _) at hv
  rw [he.coe_completionPosCone] at hu hv
  let S : Set (UniformSpace.Completion E) :=
    ((↑) : E → UniformSpace.Completion E) '' Set.Ici (0 : E)
  have huv : (u, v) ∈ closure (S ×ˢ S) := by
    rw [closure_prod_eq]
    exact ⟨hu, hv⟩
  refine closure_minimal ?_
    (isClosed_le (continuous_fst.sub continuous_snd).norm
      (continuous_fst.add continuous_snd).norm) huv
  rintro ⟨u', v'⟩ ⟨⟨p, hp, hup⟩, ⟨q, hq, hvq⟩⟩
  dsimp only at hup hvq
  change ‖u' - v'‖ ≤ ‖u' + v'‖
  rw [← hup, ← hvq, ← UniformSpace.Completion.coe_sub, ← UniformSpace.Completion.coe_add,
    UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  refine he.norm_le_norm_of_le ?_ ?_
  · rw [neg_add, sub_eq_add_neg]
    exact add_le_add ((neg_nonpos.mpr hp).trans hp) le_rfl
  · rw [sub_eq_add_neg]
    exact add_le_add le_rfl ((neg_nonpos.mpr hq).trans hq)

/-- The completion positive cone is pointed (`x ∈ C` and `-x ∈ C` imply `x = 0`). -/
theorem IsOrderUnitNorm.eq_zero_of_mem_completionPosCone_of_neg_mem
    {x : UniformSpace.Completion E} (hx : x ∈ he.completionPosCone)
    (hneg : -x ∈ he.completionPosCone) : x = 0 := by
  have h := he.norm_sub_le_norm_add_of_mem_completionPosCone hx hneg
  rw [sub_neg_eq_add, add_neg_cancel, norm_zero, ← two_smul ℝ x, norm_smul,
    Real.norm_eq_abs, abs_of_pos two_pos] at h
  exact norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg x))

private theorem IsOrderUnitNorm.salient_completionPosCone :
    (he.completionPosCone : ConvexCone ℝ (UniformSpace.Completion E)).Salient :=
  fun _ hx hx0 hneg => hx0 (he.eq_zero_of_mem_completionPosCone_of_neg_mem hx hneg)

/-- The partial order on `UniformSpace.Completion E` defined by the closed positive cone
`he.completionPosCone`. -/
@[instance_reducible]
noncomputable def IsOrderUnitNorm.completionPartialOrder :
    PartialOrder (UniformSpace.Completion E) :=
  (he.completionPosCone : ConvexCone ℝ (UniformSpace.Completion E)).toPartialOrder
    he.completionPosCone.pointed_toConvexCone he.salient_completionPosCone

/-- Characterization of the completion partial order in terms of `he.completionPosCone`. -/
theorem IsOrderUnitNorm.completion_le_iff {x y : UniformSpace.Completion E} :
    @LE.le _ he.completionPartialOrder.toLE x y ↔ y - x ∈ he.completionPosCone :=
  (Iff.rfl)

/-- Nonnegativity in the completion partial order is membership in `he.completionPosCone`. -/
theorem IsOrderUnitNorm.completion_nonneg_iff {x : UniformSpace.Completion E} :
    @LE.le _ he.completionPartialOrder.toLE 0 x ↔ x ∈ he.completionPosCone := by
  rw [he.completion_le_iff, sub_zero]

/-- Addition is compatible with the completion partial order. -/
theorem IsOrderUnitNorm.completionIsOrderedAddMonoid :
    @IsOrderedAddMonoid (UniformSpace.Completion E) _ he.completionPartialOrder.toPreorder :=
  (he.completionPosCone : ConvexCone ℝ (UniformSpace.Completion E)).to_isOrderedAddMonoid
    he.completionPosCone.pointed_toConvexCone he.salient_completionPosCone

/-- The canonical embedding `E → UniformSpace.Completion E` preserves and reflects the order. -/
theorem IsOrderUnitNorm.completion_coe_le_coe_iff {a b : E} :
    @LE.le _ he.completionPartialOrder.toLE
      (a : UniformSpace.Completion E) (b : UniformSpace.Completion E) ↔ a ≤ b := by
  rw [he.completion_le_iff, ← UniformSpace.Completion.coe_sub, he.coe_mem_completionPosCone_iff,
    sub_nonneg]

private theorem IsOrderUnitNorm.add_norm_smul_mem_completionPosCone
    (x : UniformSpace.Completion E) :
    x + ‖x‖ • (e : UniformSpace.Completion E) ∈ he.completionPosCone := by
  refine UniformSpace.Completion.denseRange_coe.induction_on x ?_ fun a => ?_
  · exact he.completionPosCone.isClosed.preimage
      (continuous_id.add (continuous_norm.smul continuous_const))
  · rw [UniformSpace.Completion.norm_coe, ← UniformSpace.Completion.coe_smul,
      ← UniformSpace.Completion.coe_add]
    refine he.coe_mem_completionPosCone_iff.mpr ?_
    have hlo := he.neg_norm_smul_le a
    rw [neg_smul] at hlo
    exact neg_le_iff_add_nonneg.mp hlo

/-- The norm completion of an order-unit space, with the closed positive cone and the image of `e`,
is an order-unit space with its completion norm. -/
theorem IsOrderUnitNorm.isOrderUnitNorm_completion :
    @IsOrderUnitNorm (UniformSpace.Completion E) _ _ he.completionPartialOrder.toLE
      (e : UniformSpace.Completion E) := by
  let : PartialOrder (UniformSpace.Completion E) := he.completionPartialOrder
  refine ⟨by rw [UniformSpace.Completion.norm_coe, he.norm_e], fun x r hr => ⟨?_, ?_⟩⟩
  · intro hxr
    have hrsub : (r - ‖x‖) • (e : UniformSpace.Completion E) ∈ he.completionPosCone := by
      rw [← UniformSpace.Completion.coe_smul]
      exact he.coe_mem_completionPosCone_iff.mpr (he.smul_nonneg_unit (sub_nonneg.mpr hxr))
    rw [he.completion_le_iff, he.completion_le_iff]
    refine ⟨?_, ?_⟩
    · have heq : x - (-r • (e : UniformSpace.Completion E)) =
          (x + ‖x‖ • (e : UniformSpace.Completion E)) +
            (r - ‖x‖) • (e : UniformSpace.Completion E) := by
        rw [neg_smul, sub_neg_eq_add, sub_smul]; abel
      rw [heq]
      exact he.completionPosCone.add_mem (he.add_norm_smul_mem_completionPosCone x) hrsub
    · have heq : r • (e : UniformSpace.Completion E) - x =
          (-x + ‖-x‖ • (e : UniformSpace.Completion E)) +
            (r - ‖x‖) • (e : UniformSpace.Completion E) := by
        rw [norm_neg, sub_smul]; abel
      rw [heq]
      exact he.completionPosCone.add_mem (he.add_norm_smul_mem_completionPosCone (-x)) hrsub
  · rw [he.completion_le_iff, he.completion_le_iff]
    rintro ⟨hlo, hhi⟩
    have hlo' : x + r • (e : UniformSpace.Completion E) ∈ he.completionPosCone := by
      simpa [neg_smul, sub_neg_eq_add] using hlo
    have hbound := he.norm_sub_le_norm_add_of_mem_completionPosCone hlo' hhi
    have hsub : (x + r • (e : UniformSpace.Completion E)) -
        (r • (e : UniformSpace.Completion E) - x) = (2 : ℝ) • x := by rw [two_smul]; abel
    have hadd : (x + r • (e : UniformSpace.Completion E)) +
        (r • (e : UniformSpace.Completion E) - x) =
        (2 * r) • (e : UniformSpace.Completion E) := by rw [mul_smul, two_smul]; abel
    rw [hsub, hadd, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos two_pos,
      abs_of_nonneg (by positivity), UniformSpace.Completion.norm_coe, he.norm_e, mul_one] at hbound
    linarith

end Completion

/-! ### Standard examples -/

section Examples

/-- The real line with `e = 1` is an order-unit space with its standard absolute value norm. -/
theorem isOrderUnitNorm_one_real : IsOrderUnitNorm (1 : ℝ) where
  norm_e := by simp
  norm_le_iff a r _ := by simp [Real.norm_eq_abs, abs_le]

/-- Finite-dimensional `ℓ∞(ι, ℝ)` with `e = 1` is an order-unit space. -/
theorem isOrderUnitNorm_one_pi {ι : Type*} [Fintype ι] [Nonempty ι] :
    IsOrderUnitNorm (1 : ι → ℝ) :=
  IsOrderUnitNorm.pi fun _ => isOrderUnitNorm_one_real

end Examples

end TauCeti.OrderUnit
