/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.Analysis.CStarAlgebra.SelfAdjointSpectrumInterval

/-!
# Order-unit spaces and order-unit norms

An **Archimedean order-unit space** is a partially ordered real vector space `E` together with a
distinguished nonzero element `e : E` such that:

* every `a : E` is bounded by a positive multiple of `e`, i.e., `-r • e ≤ a` and `a ≤ r • e` for
  some `r > 0`;
* the order is Archimedean: if `a ≤ ε • e` for every `ε > 0`, then `a ≤ 0`.

On such a space, the **order-unit norm**
```text
‖a‖ = sInf {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}
```
is a norm satisfying `‖e‖ = 1` and the closed-interval characterization
`‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e` for all `r ≥ 0`. Conversely, on a space equipped with
a norm, a real scalar action, and an order relation, the predicate `TauCeti.IsOrderUnitNorm e`
records `‖e‖ = 1` and this interval formula. On an additive-order-compatible real module with a
seminorm (`SeminormedAddCommGroup E`, `Module ℝ E`, `Preorder E`, `IsOrderedAddMonoid E`), it
automatically forces closedness of the positive cone (`OrderClosedTopology E`), the Archimedean
property, and recovery of the order from the norm via `0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖`; additionally
assuming `NormedSpace ℝ E` gives positivity of nonnegative scalar multiplication
(`PosSMulMono ℝ E`), and antisymmetry (`PartialOrder E`) gives definiteness of the seminorm.

## Main definitions

* `TauCeti.IsArchimedeanOrderUnit`: the algebraic axioms of an Archimedean order unit.
* `TauCeti.orderUnitNorm`: the infimum norm `sInf {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}`.
* `TauCeti.WithOrderUnitNorm`: wrapper equipping an Archimedean order-unit space with its
  order-unit norm as a `NormedAddCommGroup` and `NormedSpace ℝ`.
* `TauCeti.IsOrderUnitNorm`: compatibility of an existing norm and partial order with a unit `e`.

## Main results

* `TauCeti.WithOrderUnitNorm.isOrderUnitNorm`: the constructed order-unit norm satisfies
  `IsOrderUnitNorm`.
* `TauCeti.IsOrderUnitNorm.nonneg_iff_norm_sub_le`: `0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖`.
* `TauCeti.IsOrderUnitNorm.posSMulMono`, `TauCeti.IsOrderUnitNorm.orderClosedTopology`,
  `TauCeti.IsOrderUnitNorm.isArchimedeanOrderUnit`, `TauCeti.IsOrderUnitNorm.norm_eq_orderUnitNorm`:
  scalar monotonicity, closed positive cone, the Archimedean property, and uniqueness of the norm.
* `TauCeti.IsOrderUnitNorm.submodule`, `TauCeti.IsOrderUnitNorm.prod`,
  `TauCeti.IsOrderUnitNorm.pi`, `TauCeti.IsOrderUnitNorm.norm_map_of_orderIso`:
  permanence under unital subspaces, nonempty finite products, and unital order isomorphisms.
* `TauCeti.IsOrderUnitNorm.real_one`, `TauCeti.IsOrderUnitNorm.pi_real_one`,
  `TauCeti.IsOrderUnitNorm.continuousMap_one`,
  `TauCeti.IsOrderUnitNorm.boundedContinuousFunction_one`,
  `TauCeti.IsOrderUnitNorm.selfAdjoint_one`: concrete order-unit spaces.

## References

* R. V. Kadison, *A representation theory for commutative topological algebra*, Mem. Amer. Math.
  Soc. **7** (1951).
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. **4** (1999), 559–600, §1.
-/

public section

noncomputable section

open Set Filter Topology
open scoped BoundedContinuousFunction

namespace TauCeti

/-! ### Archimedean order units and the constructed order-unit norm -/

/-- An element `e` of an ordered real vector space is an **Archimedean order unit** if it is
nonzero, dominates every element up to a positive scalar, and satisfies the Archimedean property
`(∀ ε > 0, a ≤ ε • e) → a ≤ 0`. -/
structure IsArchimedeanOrderUnit {E : Type*} [Zero E] [SMul ℝ E] [LE E] (e : E) : Prop where
  /-- The order unit is nonzero. -/
  ne_zero : e ≠ 0
  /-- Every element lies in some symmetric interval `[-r • e, r • e]` with `r > 0`. -/
  orderUnit : ∀ a : E, ∃ r : ℝ, 0 < r ∧ -r • e ≤ a ∧ a ≤ r • e
  /-- The Archimedean condition: being bounded above by every positive multiple of `e` forces
  nonpositivity. -/
  archimedean : ∀ a : E, (∀ ε : ℝ, 0 < ε → a ≤ ε • e) → a ≤ 0

/-- The order-unit norm `inf {r ≥ 0 : -r • e ≤ a ∧ a ≤ r • e}` associated to an element `e`. -/
def orderUnitNorm {E : Type*} [SMul ℝ E] [LE E] (e a : E) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}

theorem orderUnitNorm_def {E : Type*} [SMul ℝ E] [LE E] (e a : E) :
    orderUnitNorm e a = sInf {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e} := (rfl)

theorem bddBelow_orderUnitNormSet {E : Type*} [SMul ℝ E] [LE E] (e a : E) :
    BddBelow {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e} :=
  ⟨0, fun _ hr => hr.1⟩

theorem orderUnitNorm_nonneg {E : Type*} [SMul ℝ E] [LE E] (e a : E) :
    0 ≤ orderUnitNorm e a :=
  Real.sInf_nonneg fun _ hr => hr.1

namespace IsArchimedeanOrderUnit

theorem nonempty_orderUnitNormSet {E : Type*} [Zero E] [SMul ℝ E] [LE E]
    {e : E} (he : IsArchimedeanOrderUnit e) (a : E) :
    {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}.Nonempty := by
  obtain ⟨r, hr, h1, h2⟩ := he.orderUnit a
  exact ⟨r, hr.le, h1, h2⟩

theorem nonneg {E : Type*} [AddCommMonoid E] [Module ℝ E] [Preorder E] [PosSMulMono ℝ E]
    {e : E} (he : IsArchimedeanOrderUnit e) : 0 ≤ e := by
  obtain ⟨r, hr, -, h0⟩ := he.orderUnit 0
  have h := smul_le_smul_of_nonneg_left h0 (inv_nonneg.mpr hr.le)
  simpa [smul_smul, hr.ne'] using h

theorem pos {E : Type*} [AddCommMonoid E] [Module ℝ E] [PartialOrder E] [PosSMulMono ℝ E]
    {e : E} (he : IsArchimedeanOrderUnit e) : 0 < e :=
  he.nonneg.lt_of_ne' he.ne_zero

section Preorder

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Preorder E] [IsOrderedAddMonoid E]
  [PosSMulMono ℝ E] {e : E} (he : IsArchimedeanOrderUnit e)

include he

/-- Closed-interval characterization of the constructed order-unit norm: for `r ≥ 0`,
`orderUnitNorm e a ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e`. -/
theorem orderUnitNorm_le_iff {a : E} {r : ℝ} (hr : 0 ≤ r) :
    orderUnitNorm e a ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => csInf_le (bddBelow_orderUnitNormSet e a) ⟨hr, h1, h2⟩⟩
  have upper : ∀ x : E, (∀ s : ℝ, orderUnitNorm e a < s → x ≤ s • e) → x ≤ r • e := by
    intro x hx
    have hsub : x - r • e ≤ 0 := he.archimedean _ fun ε hε => by
      have hlt : orderUnitNorm e a < r + ε := lt_of_le_of_lt h (lt_add_of_pos_right r hε)
      have := hx (r + ε) hlt
      rw [add_smul] at this
      exact sub_le_iff_le_add'.mpr this
    exact sub_nonpos.mp hsub
  have exists_bound : ∀ s : ℝ, orderUnitNorm e a < s → -s • e ≤ a ∧ a ≤ s • e := by
    intro s hs
    obtain ⟨t, ⟨-, ht1, ht2⟩, hts⟩ :=
      exists_lt_of_csInf_lt (he.nonempty_orderUnitNormSet a) hs
    have hts' : 0 ≤ (s - t) • e := smul_nonneg (sub_nonneg.mpr hts.le) he.nonneg
    refine ⟨?_, ?_⟩
    · calc -s • e = -t • e - (s - t) • e := by rw [sub_smul, neg_smul, neg_smul]; abel
        _ ≤ -t • e := sub_le_self _ hts'
        _ ≤ a := ht1
    · calc a ≤ t • e := ht2
        _ ≤ t • e + (s - t) • e := le_add_of_nonneg_right hts'
        _ = s • e := by rw [sub_smul]; abel
  refine ⟨?_, upper a fun s hs => (exists_bound s hs).2⟩
  have hneg : -a ≤ r • e := upper (-a) fun s hs => by
    have := (exists_bound s hs).1
    rw [neg_smul] at this
    exact neg_le.mp this
  rw [neg_smul]
  exact neg_le.mp hneg

theorem neg_orderUnitNorm_smul_le (a : E) : -(orderUnitNorm e a) • e ≤ a :=
  ((he.orderUnitNorm_le_iff (orderUnitNorm_nonneg e a)).mp le_rfl).1

theorem le_orderUnitNorm_smul (a : E) : a ≤ orderUnitNorm e a • e :=
  ((he.orderUnitNorm_le_iff (orderUnitNorm_nonneg e a)).mp le_rfl).2

@[simp]
theorem orderUnitNorm_zero : orderUnitNorm e 0 = 0 :=
  le_antisymm ((he.orderUnitNorm_le_iff le_rfl).mpr ⟨by simp, by simp⟩) (orderUnitNorm_nonneg e 0)

@[simp]
theorem orderUnitNorm_neg (a : E) : orderUnitNorm e (-a) = orderUnitNorm e a := by
  refine le_antisymm ?_ ?_
  · rw [he.orderUnitNorm_le_iff (orderUnitNorm_nonneg e a)]
    refine ⟨?_, ?_⟩
    · rw [neg_smul]; exact neg_le.mp (by simpa using he.le_orderUnitNorm_smul a)
    · have := he.neg_orderUnitNorm_smul_le a
      rw [neg_smul] at this
      exact neg_le.mp this
  · rw [he.orderUnitNorm_le_iff (orderUnitNorm_nonneg e (-a))]
    refine ⟨?_, ?_⟩
    · have := he.le_orderUnitNorm_smul (-a)
      rw [neg_smul]
      exact neg_le.mp this
    · have := he.neg_orderUnitNorm_smul_le (-a)
      rw [neg_smul] at this
      exact neg_le_neg_iff.mp this

theorem orderUnitNorm_add_le (a b : E) :
    orderUnitNorm e (a + b) ≤ orderUnitNorm e a + orderUnitNorm e b := by
  rw [he.orderUnitNorm_le_iff (add_nonneg (orderUnitNorm_nonneg e a) (orderUnitNorm_nonneg e b))]
  refine ⟨?_, ?_⟩
  · calc -(orderUnitNorm e a + orderUnitNorm e b) • e
        = -(orderUnitNorm e a) • e + -(orderUnitNorm e b) • e := by rw [neg_add, add_smul]
      _ ≤ a + b := add_le_add (he.neg_orderUnitNorm_smul_le a) (he.neg_orderUnitNorm_smul_le b)
  · calc a + b ≤ orderUnitNorm e a • e + orderUnitNorm e b • e :=
          add_le_add (he.le_orderUnitNorm_smul a) (he.le_orderUnitNorm_smul b)
      _ = (orderUnitNorm e a + orderUnitNorm e b) • e := (add_smul _ _ _).symm

private theorem orderUnitNorm_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (a : E) :
    orderUnitNorm e (r • a) = r * orderUnitNorm e a := by
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [he.orderUnitNorm_zero]
  · refine le_antisymm ?_ ?_
    · rw [he.orderUnitNorm_le_iff (mul_nonneg hrpos.le (orderUnitNorm_nonneg e a))]
      refine ⟨?_, ?_⟩
      · calc -(r * orderUnitNorm e a) • e = r • (-(orderUnitNorm e a) • e) := by
              rw [smul_smul, mul_neg]
          _ ≤ r • a := smul_le_smul_of_nonneg_left (he.neg_orderUnitNorm_smul_le a) hrpos.le
      · calc r • a ≤ r • (orderUnitNorm e a • e) :=
              smul_le_smul_of_nonneg_left (he.le_orderUnitNorm_smul a) hrpos.le
          _ = (r * orderUnitNorm e a) • e := (mul_smul _ _ _).symm
    · rw [← le_inv_mul_iff₀ hrpos]
      rw [he.orderUnitNorm_le_iff (mul_nonneg (inv_nonneg.mpr hrpos.le) (orderUnitNorm_nonneg e _))]
      have h1 := smul_le_smul_of_nonneg_left (he.neg_orderUnitNorm_smul_le (r • a))
        (inv_nonneg.mpr hrpos.le)
      have h2 := smul_le_smul_of_nonneg_left (he.le_orderUnitNorm_smul (r • a))
        (inv_nonneg.mpr hrpos.le)
      simp only [smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul] at h1 h2
      refine ⟨?_, h2⟩
      simpa [mul_neg] using h1

@[simp]
theorem orderUnitNorm_smul (r : ℝ) (a : E) :
    orderUnitNorm e (r • a) = |r| * orderUnitNorm e a := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, he.orderUnitNorm_smul_of_nonneg hr]
  · rw [abs_of_nonpos hr, ← he.orderUnitNorm_neg, ← neg_smul,
      he.orderUnitNorm_smul_of_nonneg (neg_nonneg.mpr hr)]

end Preorder

section PartialOrder

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono ℝ E] {e : E} (he : IsArchimedeanOrderUnit e)

include he

/-- Definiteness of the constructed order-unit norm: `orderUnitNorm e a = 0` if and only if
`a = 0`. -/
@[simp]
theorem orderUnitNorm_eq_zero_iff {a : E} : orderUnitNorm e a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ he.orderUnitNorm_zero⟩
  have ⟨h1, h2⟩ := (he.orderUnitNorm_le_iff le_rfl).mp h.le
  simp only [neg_zero, zero_smul] at h1 h2
  exact le_antisymm h2 h1

/-- Normalization of the constructed order-unit norm at the distinguished order unit:
`orderUnitNorm e e = 1`. -/
@[simp]
theorem orderUnitNorm_self : orderUnitNorm e e = 1 := by
  refine le_antisymm ?_ ?_
  · rw [he.orderUnitNorm_le_iff zero_le_one]
    refine ⟨?_, by simp⟩
    calc -(1 : ℝ) • e = -e := by simp
      _ ≤ 0 := neg_nonpos.mpr he.nonneg
      _ ≤ e := he.nonneg
  · by_contra! hlt
    have hle : e ≤ orderUnitNorm e e • e := he.le_orderUnitNorm_smul e
    have hpos : 0 < 1 - orderUnitNorm e e := sub_pos.mpr hlt
    have hsub : (1 - orderUnitNorm e e) • e ≤ 0 := by
      rw [sub_smul, one_smul]
      exact sub_nonpos.mpr hle
    have he0 : e ≤ 0 := by
      have := smul_le_smul_of_nonneg_left hsub (inv_nonneg.mpr hpos.le)
      simpa [smul_smul, hpos.ne'] using this
    exact he.pos.not_ge he0

end PartialOrder

end IsArchimedeanOrderUnit

/-- Wrapper equipping an Archimedean order-unit space `(E, e)` with the norm `orderUnitNorm e`. -/
@[ext]
structure WithOrderUnitNorm {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e : E} (he : IsArchimedeanOrderUnit e) where
  /-- The underlying element of the ordered real vector space. -/
  val : E

namespace WithOrderUnitNorm

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono ℝ E] {e : E} {he : IsArchimedeanOrderUnit e}

instance : Zero (WithOrderUnitNorm he) := ⟨⟨0⟩⟩
instance : Add (WithOrderUnitNorm he) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance : Neg (WithOrderUnitNorm he) := ⟨fun x => ⟨-x.val⟩⟩
instance : Sub (WithOrderUnitNorm he) := ⟨fun x y => ⟨x.val - y.val⟩⟩
instance : SMul ℕ (WithOrderUnitNorm he) := ⟨fun n x => ⟨n • x.val⟩⟩
instance : SMul ℤ (WithOrderUnitNorm he) := ⟨fun n x => ⟨n • x.val⟩⟩
instance : SMul ℝ (WithOrderUnitNorm he) := ⟨fun r x => ⟨r • x.val⟩⟩
instance : LE (WithOrderUnitNorm he) := ⟨fun x y => x.val ≤ y.val⟩
instance : LT (WithOrderUnitNorm he) := ⟨fun x y => x.val < y.val⟩

@[simp] theorem val_zero : (0 : WithOrderUnitNorm he).val = 0 := (rfl)
@[simp] theorem val_add (x y : WithOrderUnitNorm he) : (x + y).val = x.val + y.val := (rfl)
@[simp] theorem val_neg (x : WithOrderUnitNorm he) : (-x).val = -x.val := (rfl)
@[simp] theorem val_sub (x y : WithOrderUnitNorm he) : (x - y).val = x.val - y.val := (rfl)
@[simp] theorem val_smul (r : ℝ) (x : WithOrderUnitNorm he) : (r • x).val = r • x.val := (rfl)
@[simp] theorem le_iff (x y : WithOrderUnitNorm he) : x ≤ y ↔ x.val ≤ y.val := Iff.rfl
@[simp] theorem lt_iff (x y : WithOrderUnitNorm he) : x < y ↔ x.val < y.val := Iff.rfl

instance : AddCommGroup (WithOrderUnitNorm he) :=
  Function.Injective.addCommGroup val (fun _ _ h => WithOrderUnitNorm.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℝ (WithOrderUnitNorm he) :=
  Function.Injective.module ℝ
    { toFun := val, map_zero' := rfl, map_add' := fun _ _ => rfl }
    (fun _ _ h => WithOrderUnitNorm.ext h) (fun _ _ => rfl)

instance : PartialOrder (WithOrderUnitNorm he) where
  le_refl a := le_refl a.val
  le_trans _ _ _ h1 h2 := le_trans h1 h2
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge
  le_antisymm _ _ h1 h2 := WithOrderUnitNorm.ext (le_antisymm h1 h2)

instance : IsOrderedAddMonoid (WithOrderUnitNorm he) where
  add_le_add_left _ _ h c := add_le_add_left (α := E) h c.val

instance : PosSMulMono ℝ (WithOrderUnitNorm he) where
  smul_le_smul_of_nonneg_left _ hr _ _ h := smul_le_smul_of_nonneg_left (α := ℝ) (β := E) h hr

instance : Norm (WithOrderUnitNorm he) := ⟨fun x => orderUnitNorm e x.val⟩

theorem norm_def (x : WithOrderUnitNorm he) : ‖x‖ = orderUnitNorm e x.val := (rfl)

/-- The `NormedSpace.Core` data witnessing that `orderUnitNorm e` is a real norm. -/
theorem normedSpaceCore (he : IsArchimedeanOrderUnit e) :
    NormedSpace.Core ℝ (WithOrderUnitNorm he) where
  norm_nonneg x := orderUnitNorm_nonneg e x.val
  norm_eq_zero_iff x := by
    rw [norm_def, he.orderUnitNorm_eq_zero_iff, WithOrderUnitNorm.ext_iff, val_zero]
  norm_smul r x := by
    rw [norm_def, val_smul, he.orderUnitNorm_smul, Real.norm_eq_abs, norm_def]
  norm_triangle x y := he.orderUnitNorm_add_le x.val y.val

instance : NormedAddCommGroup (WithOrderUnitNorm he) :=
  NormedAddCommGroup.ofCore (normedSpaceCore he)

instance : NormedSpace ℝ (WithOrderUnitNorm he) :=
  NormedSpace.ofCore (normedSpaceCore he)

/-- The canonical linear equivalence between `WithOrderUnitNorm he` and `E`. -/
def toLinearEquiv (he : IsArchimedeanOrderUnit e) : WithOrderUnitNorm he ≃ₗ[ℝ] E where
  toFun := val
  invFun := mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem toLinearEquiv_apply (x : WithOrderUnitNorm he) : toLinearEquiv he x = x.val := (rfl)
@[simp] theorem toLinearEquiv_symm_apply (a : E) : (toLinearEquiv he).symm a = ⟨a⟩ := (rfl)

/-- The distinguished order unit viewed as an element of `WithOrderUnitNorm he`. -/
def unit (he : IsArchimedeanOrderUnit e) : WithOrderUnitNorm he := ⟨e⟩

@[simp] theorem val_unit (he : IsArchimedeanOrderUnit e) : (unit he).val = e := (rfl)

end WithOrderUnitNorm

/-! ### The predicate `IsOrderUnitNorm` and its basic properties -/

/-- Compatibility of an existing norm and partial order with an order unit `e`: `‖e‖ = 1` and
`‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e` for every `r ≥ 0`. -/
structure IsOrderUnitNorm {E : Type*} [Norm E] [SMul ℝ E] [LE E] (e : E) : Prop where
  /-- The order unit has norm one. -/
  norm_e : ‖e‖ = 1
  /-- The closed-interval norm characterization: `‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e` for `r ≥ 0`. -/
  norm_le_iff : ∀ (a : E) (r : ℝ), 0 ≤ r → (‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e)

/-- The constructed norm on `WithOrderUnitNorm he` satisfies `IsOrderUnitNorm`. -/
theorem WithOrderUnitNorm.isOrderUnitNorm {E : Type*} [AddCommGroup E] [Module ℝ E]
    [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e : E}
    (he : IsArchimedeanOrderUnit e) :
    IsOrderUnitNorm (WithOrderUnitNorm.unit he) where
  norm_e := he.orderUnitNorm_self
  norm_le_iff _ _ hr := he.orderUnitNorm_le_iff hr

namespace IsOrderUnitNorm

section Seminormed

variable {E : Type*} [SeminormedAddGroup E] [SMul ℝ E] [LE E] {e : E} (he : IsOrderUnitNorm e)

include he

theorem neg_norm_smul_le (a : E) : -‖a‖ • e ≤ a :=
  ((he.norm_le_iff a ‖a‖ (norm_nonneg a)).mp le_rfl).1

theorem le_norm_smul (a : E) : a ≤ ‖a‖ • e :=
  ((he.norm_le_iff a ‖a‖ (norm_nonneg a)).mp le_rfl).2

theorem smul_nonneg_of_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ r • e :=
  ((he.norm_le_iff 0 r hr).mp (by simpa using hr)).2

theorem ne_zero : e ≠ 0 := by
  intro h
  have := he.norm_e
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem nontrivial : Nontrivial E :=
  ⟨⟨e, 0, he.ne_zero⟩⟩

/-- Uniqueness of the order-unit norm: any norm satisfying `IsOrderUnitNorm e` coincides with
`orderUnitNorm e`. -/
theorem norm_eq_orderUnitNorm (a : E) : ‖a‖ = orderUnitNorm e a := by
  rw [orderUnitNorm_def]
  have hset : {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e} = Set.Ici ‖a‖ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    exact ⟨fun ⟨hr, h⟩ => (he.norm_le_iff a r hr).mpr h,
      fun hr => ⟨(norm_nonneg a).trans hr,
        (he.norm_le_iff a r ((norm_nonneg a).trans hr)).mp hr⟩⟩
  rw [hset, csInf_Ici]

end Seminormed

section Basic

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] {e : E}

theorem nonneg [LE E] (he : IsOrderUnitNorm e) : 0 ≤ e := by
  simpa using he.smul_nonneg_of_nonneg zero_le_one

theorem pos [PartialOrder E] (he : IsOrderUnitNorm e) : 0 < e :=
  he.nonneg.lt_of_ne' he.ne_zero

/-- The interval formula forces definiteness: an element of norm zero must be zero. -/
theorem eq_zero_of_norm_eq_zero [PartialOrder E] (he : IsOrderUnitNorm e) {a : E} (ha : ‖a‖ = 0) :
    a = 0 := by
  have ⟨h1, h2⟩ := (he.norm_le_iff a 0 le_rfl).mp ha.le
  simp only [neg_zero, zero_smul] at h1 h2
  exact le_antisymm h2 h1

@[simp]
theorem norm_smul_self {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [LE E] {e : E}
    (he : IsOrderUnitNorm e) (r : ℝ) : ‖r • e‖ = |r| := by
  rw [norm_smul, Real.norm_eq_abs, he.norm_e, mul_one]

end Basic

section Ordered

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [Preorder E] [IsOrderedAddMonoid E]
  {e : E} (he : IsOrderUnitNorm e)

include he

/-- Monotonicity of the order-unit norm on symmetric intervals: `-b ≤ a ≤ b` implies `‖a‖ ≤ ‖b‖`. -/
theorem norm_le_of_neg_le_of_le {a b : E} (h1 : -b ≤ a) (h2 : a ≤ b) : ‖a‖ ≤ ‖b‖ := by
  rw [he.norm_le_iff a ‖b‖ (norm_nonneg b)]
  refine ⟨?_, h2.trans (he.le_norm_smul b)⟩
  have hneg : -‖b‖ • e ≤ -b := by
    rw [neg_smul]
    exact neg_le.mp (by simpa using he.le_norm_smul b)
  exact hneg.trans h1

/-- Monotonicity of the order-unit norm on the positive cone: `0 ≤ a ≤ b` implies `‖a‖ ≤ ‖b‖`. -/
theorem norm_le_of_nonneg_of_le {a b : E} (ha : 0 ≤ a) (hab : a ≤ b) : ‖a‖ ≤ ‖b‖ :=
  he.norm_le_of_neg_le_of_le ((neg_nonpos.mpr (ha.trans hab)).trans ha) hab

/-- **Order recovery from the norm and unit:** `0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖`. -/
theorem nonneg_iff_norm_sub_le (a : E) : 0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖ := by
  rw [he.norm_le_iff (‖a‖ • e - a) ‖a‖ (norm_nonneg a)]
  refine ⟨fun ha => ⟨?_, sub_le_self _ ha⟩, fun ⟨_, h2⟩ => ?_⟩
  · have hstep : -‖a‖ • e + a ≤ ‖a‖ • e := by
      calc -‖a‖ • e + a ≤ -‖a‖ • e + ‖a‖ • e := add_le_add_right (he.le_norm_smul a) _
        _ = 0 := by rw [neg_smul, neg_add_cancel]
        _ ≤ ‖a‖ • e := he.smul_nonneg_of_nonneg (norm_nonneg a)
    exact le_sub_iff_add_le.mpr hstep
  · simpa using sub_le_iff_le_add.mp h2

/-- The interval formula forces the positive cone to be Archimedean. -/
theorem archimedean {a : E} (h : ∀ ε : ℝ, 0 < ε → a ≤ ε • e) : a ≤ 0 := by
  have hnorm : ‖a + ‖a‖ • e‖ ≤ ‖a‖ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [he.norm_le_iff (a + ‖a‖ • e) (‖a‖ + ε) (by positivity)]
    refine ⟨?_, ?_⟩
    · calc -(‖a‖ + ε) • e ≤ 0 := by
              rw [neg_smul]
              exact neg_nonpos.mpr (he.smul_nonneg_of_nonneg (by positivity))
        _ = -‖a‖ • e + ‖a‖ • e := by rw [neg_smul, neg_add_cancel]
        _ ≤ a + ‖a‖ • e := add_le_add_left (he.neg_norm_smul_le a) _
    · calc a + ‖a‖ • e ≤ ε • e + ‖a‖ • e := add_le_add_left (h ε hε) _
        _ = (‖a‖ + ε) • e := by rw [add_smul, add_comm]
  have hneg : ‖‖-a‖ • e - (-a)‖ ≤ ‖-a‖ := by
    simpa [norm_neg, sub_neg_eq_add, add_comm] using hnorm
  exact neg_nonneg.mp ((he.nonneg_iff_norm_sub_le (-a)).mpr hneg)

/-- An order-compatible seminorm supplies a nonzero Archimedean order unit `e` in an ordered real
vector space. -/
theorem isArchimedeanOrderUnit : IsArchimedeanOrderUnit e where
  ne_zero := he.ne_zero
  orderUnit a := ⟨‖a‖ + 1, by positivity,
    (he.norm_le_iff a (‖a‖ + 1) (by positivity)).mp (le_add_of_nonneg_right zero_le_one)⟩
  archimedean _ h := he.archimedean h

/-- The order relation of an order-unit space is closed in `E × E`. -/
theorem orderClosedTopology : OrderClosedTopology E where
  isClosed_le' := by
    have hset : {p : E × E | p.1 ≤ p.2} =
        (fun p : E × E => ‖‖p.2 - p.1‖ • e - (p.2 - p.1)‖ - ‖p.2 - p.1‖) ⁻¹' Set.Iic 0 := by
      ext ⟨a, b⟩
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic, sub_nonpos,
        ← he.nonneg_iff_norm_sub_le, sub_nonneg]
    have hsmul : Continuous (fun r : ℝ => r • e) := by
      refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun r s => ?_)
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← sub_smul, Real.norm_eq_abs,
        he.norm_le_iff _ |r - s| (abs_nonneg _)]
      rcases le_total 0 (r - s) with h | h
      · rw [abs_of_nonneg h, neg_smul]
        exact ⟨(neg_nonpos.mpr (he.smul_nonneg_of_nonneg h)).trans
          (he.smul_nonneg_of_nonneg h), le_rfl⟩
      · rw [abs_of_nonpos h, neg_neg]
        have hnn := he.smul_nonneg_of_nonneg (neg_nonneg.mpr h)
        have hneg : (r - s) • e ≤ 0 := by
          rw [← neg_neg ((r - s) • e), ← neg_smul]
          exact neg_nonpos.mpr hnn
        exact ⟨le_rfl, hneg.trans hnn⟩
    rw [hset]
    have hdiff : Continuous (fun p : E × E => p.2 - p.1) := continuous_snd.sub continuous_fst
    exact isClosed_Iic.preimage ((((hsmul.comp hdiff.norm).sub hdiff).norm).sub hdiff.norm)

theorem isClosed_nonneg : IsClosed {a : E | 0 ≤ a} := by
  have := he.orderClosedTopology
  exact isClosed_Ici

/-- Every point within distance `1` of the order unit `e` is nonnegative. -/
theorem closedBall_subset_nonneg : Metric.closedBall e 1 ⊆ {a : E | 0 ≤ a} := by
  intro a ha
  rw [Metric.mem_closedBall, dist_eq_norm] at ha
  have h1 : -(1 : ℝ) • e ≤ a - e := ((he.norm_le_iff (a - e) 1 zero_le_one).mp ha).1
  rw [neg_smul, one_smul] at h1
  simpa using add_le_add_left h1 e

/-- The order unit `e` lies in the interior of the positive cone. -/
theorem mem_interior_nonneg : e ∈ interior {a : E | 0 ≤ a} :=
  interior_mono he.closedBall_subset_nonneg <|
    mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds e zero_lt_one)

end Ordered

/-- Compatibility of the order with nonnegative real scalar multiplication follows automatically
from `IsOrderUnitNorm` in a real normed space. -/
theorem posSMulMono {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [Preorder E]
    [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e) : PosSMulMono ℝ E where
  smul_le_smul_of_nonneg_left r hr a b hab := by
    have hc : 0 ≤ b - a := sub_nonneg.mpr hab
    have hnorm : ‖‖b - a‖ • e - (b - a)‖ ≤ ‖b - a‖ := (he.nonneg_iff_norm_sub_le (b - a)).mp hc
    have hmul : ‖‖r • (b - a)‖ • e - r • (b - a)‖ ≤ ‖r • (b - a)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, mul_smul, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hr]
      exact mul_le_mul_of_nonneg_left hnorm hr
    have hrba : 0 ≤ r • (b - a) := (he.nonneg_iff_norm_sub_le _).mpr hmul
    rw [smul_sub, sub_nonneg] at hrba
    exact hrba

/-! ### Permanence properties -/

/-- Restriction of an order-unit norm to a real subspace containing `e`. -/
theorem submodule {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [LE E]
    {e : E} (he : IsOrderUnitNorm e) (S : Submodule ℝ E) (hmem : e ∈ S) :
    IsOrderUnitNorm (⟨e, hmem⟩ : S) where
  norm_e := he.norm_e
  norm_le_iff a r hr := he.norm_le_iff a.1 r hr

/-- Product of two order-unit spaces with the coordinatewise order and maximum norm. -/
theorem prod {E F : Type*} [Norm E] [SMul ℝ E] [LE E] [Norm F] [SMul ℝ F] [LE F]
    {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) :
    IsOrderUnitNorm (e, f) where
  norm_e := by rw [Prod.norm_def, he.norm_e, hf.norm_e, max_self]
  norm_le_iff x r hr := by
    rw [Prod.norm_def, max_le_iff, he.norm_le_iff x.1 r hr, hf.norm_le_iff x.2 r hr,
      Prod.le_def, Prod.le_def]
    simp only [Prod.smul_mk]
    tauto

/-- Finite nonempty product of order-unit spaces with the coordinatewise order and supremum norm. -/
theorem pi {ι : Type*} [Fintype ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] [∀ i, SMul ℝ (E i)] [∀ i, LE (E i)]
    {e : ∀ i, E i} (he : ∀ i, IsOrderUnitNorm (e i)) :
    IsOrderUnitNorm e where
  norm_e := by
    refine le_antisymm ?_ ?_
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      exact (he i).norm_e.le
    · obtain ⟨i⟩ := ‹Nonempty ι›
      rw [← (he i).norm_e]
      exact norm_le_pi_norm e i
  norm_le_iff x r hr := by
    rw [pi_norm_le_iff_of_nonneg hr]
    simp_rw [(he _).norm_le_iff _ r hr, Pi.le_def, Pi.smul_apply]
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun ⟨h1, h2⟩ i => ⟨h1 i, h2 i⟩⟩

/-- Transport of `IsOrderUnitNorm` along a unital linear isometric order equivalence. -/
theorem map_linearIsometryEquiv {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [LE E]
    [SeminormedAddCommGroup F] [Module ℝ F] [LE F] {e : E} (he : IsOrderUnitNorm e)
    (Φ : E ≃ₗᵢ[ℝ] F) (hord : ∀ a b : E, Φ a ≤ Φ b ↔ a ≤ b) :
    IsOrderUnitNorm (Φ e) where
  norm_e := by rw [Φ.norm_map, he.norm_e]
  norm_le_iff b r hr := by
    obtain ⟨a, rfl⟩ := Φ.surjective b
    rw [Φ.norm_map, he.norm_le_iff a r hr, ← map_smul, ← map_smul, hord, hord]

/-- Every unital real linear order isomorphism between order-unit spaces is automatically
isometric. -/
theorem norm_map_of_orderIso {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [LE E]
    [SeminormedAddCommGroup F] [Module ℝ F] [LE F]
    {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (Φ : E ≃ₗ[ℝ] F) (hunit : Φ e = f) (hord : ∀ a b : E, Φ a ≤ Φ b ↔ a ≤ b) (a : E) :
    ‖Φ a‖ = ‖a‖ := by
  refine le_antisymm ?_ ?_
  · rw [hf.norm_le_iff (Φ a) ‖a‖ (norm_nonneg a), ← hunit, ← map_smul, ← map_smul, hord, hord]
    exact ⟨he.neg_norm_smul_le a, he.le_norm_smul a⟩
  · rw [he.norm_le_iff a ‖Φ a‖ (norm_nonneg (Φ a)), ← hord, ← hord, map_smul, map_smul, hunit]
    exact ⟨hf.neg_norm_smul_le (Φ a), hf.le_norm_smul (Φ a)⟩

/-- Bundle a unital linear order isomorphism between order-unit spaces as a
`LinearIsometryEquiv`. -/
def linearIsometryEquivOfOrderIso {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [LE E]
    [SeminormedAddCommGroup F] [Module ℝ F] [LE F]
    {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (Φ : E ≃ₗ[ℝ] F) (hunit : Φ e = f) (hord : ∀ a b : E, Φ a ≤ Φ b ↔ a ≤ b) :
    E ≃ₗᵢ[ℝ] F where
  toLinearEquiv := Φ
  norm_map' := he.norm_map_of_orderIso hf Φ hunit hord

@[simp]
theorem linearIsometryEquivOfOrderIso_apply {E F : Type*} [SeminormedAddCommGroup E]
    [Module ℝ E] [LE E] [SeminormedAddCommGroup F] [Module ℝ F] [LE F]
    {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (Φ : E ≃ₗ[ℝ] F) (hunit : Φ e = f) (hord : ∀ a b : E, Φ a ≤ Φ b ↔ a ≤ b) (a : E) :
    he.linearIsometryEquivOfOrderIso hf Φ hunit hord a = Φ a := (rfl)

@[simp]
theorem linearIsometryEquivOfOrderIso_symm_apply {E F : Type*} [SeminormedAddCommGroup E]
    [Module ℝ E] [LE E] [SeminormedAddCommGroup F] [Module ℝ F] [LE F]
    {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (Φ : E ≃ₗ[ℝ] F) (hunit : Φ e = f) (hord : ∀ a b : E, Φ a ≤ Φ b ↔ a ≤ b) (b : F) :
    (he.linearIsometryEquivOfOrderIso hf Φ hunit hord).symm b = Φ.symm b := (rfl)

/-! ### Concrete examples of order-unit spaces -/

/-- `ℝ` with its standard absolute value and order is an order-unit space with unit `1`. -/
theorem real_one : IsOrderUnitNorm (1 : ℝ) where
  norm_e := norm_one
  norm_le_iff a r _ := by
    simp [Real.norm_eq_abs, abs_le]

/-- Finite nonempty products `ι → ℝ` with coordinatewise order and supremum norm are order-unit
spaces with unit `1`. -/
theorem pi_real_one {ι : Type*} [Fintype ι] [Nonempty ι] : IsOrderUnitNorm (1 : ι → ℝ) :=
  IsOrderUnitNorm.pi fun _ => real_one

/-- `C(K, ℝ)` for nonempty compact `K` with pointwise order and supremum norm is an order-unit
space with unit `1`. -/
theorem continuousMap_one {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K] :
    IsOrderUnitNorm (1 : C(K, ℝ)) where
  norm_e := norm_one
  norm_le_iff f r hr := by
    rw [ContinuousMap.norm_le f hr]
    simp only [Real.norm_eq_abs, abs_le, ContinuousMap.le_def, ContinuousMap.coe_smul,
      Pi.smul_apply, ContinuousMap.coe_one, Pi.one_apply, smul_eq_mul, mul_one]
    exact ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun ⟨h1, h2⟩ x => ⟨h1 x, h2 x⟩⟩

/-- `K →ᵇ ℝ` for nonempty `K` with pointwise order and supremum norm is an order-unit space with
unit `1`. -/
theorem boundedContinuousFunction_one {K : Type*} [TopologicalSpace K] [Nonempty K] :
    IsOrderUnitNorm (1 : K →ᵇ ℝ) where
  norm_e := norm_one
  norm_le_iff f r hr := by
    rw [BoundedContinuousFunction.norm_le hr]
    have hle : ∀ g h : K →ᵇ ℝ, g ≤ h ↔ ∀ x, g x ≤ h x := fun _ _ => Iff.rfl
    simp only [Real.norm_eq_abs, abs_le, hle, FunLike.coe_smul, Pi.smul_apply, FunLike.coe_one,
      Pi.one_apply, smul_eq_mul, mul_one]
    exact ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun ⟨h1, h2⟩ x => ⟨h1 x, h2 x⟩⟩

/-- The self-adjoint part `selfAdjoint A` of a unital star-ordered normed algebra with isometric
real continuous functional calculus (in particular, any nonzero unital C⋆-algebra) is an
order-unit space with unit `1`. -/
theorem selfAdjoint_one {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
    [StarModule ℝ A] [PartialOrder A] [StarOrderedRing A]
    [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]
    [NormOneClass A] :
    IsOrderUnitNorm (1 : selfAdjoint A) where
  norm_e := by
    rw [AddSubgroup.coe_norm, selfAdjoint.val_one, norm_one]
  norm_le_iff a r hr := by
    have ha : IsSelfAdjoint (a : A) := a.2
    rw [AddSubgroup.coe_norm, ha.norm_le_iff_spectrum_subset_Icc hr]
    simp only [Set.subset_def, Set.mem_Icc, ← Subtype.coe_le_coe, selfAdjoint.val_smul,
      selfAdjoint.val_one, ← Algebra.algebraMap_eq_smul_one]
    rw [algebraMap_le_iff_le_spectrum ha, le_algebraMap_iff_spectrum_le ha]
    exact ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
      fun ⟨h1, h2⟩ x hx => ⟨h1 x hx, h2 x hx⟩⟩

end IsOrderUnitNorm

end TauCeti
