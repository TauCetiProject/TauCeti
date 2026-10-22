/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Basic.Real.Pointwise
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The gauge of a Tate ring

Let `A` be a commutative ring, `A₀` a subring and `ϖ` a unit of `A`. For a real base `a > 1` the
*Tate gauge* is
`tateGauge A₀ ϖ a x = inf { a ^ (-n) | n ∈ ℤ, ϖ ^ (-n) * x ∈ A₀ }`,
so `x` has gauge at most `a ^ (-n)` when it lies in `ϖ ^ n A₀`. Multiplication by `ϖ ^ k` scales
the gauge exactly by `a ^ (-k)`, and changing the base `a > 1` to `b > 1` raises it to the power
`log b / log a`. When `ϖ ∈ A₀`, every element of `A` is moved into `A₀` by some power of `ϖ`
(that is, `A = A₀[1/ϖ]`) and `a > 1`, the gauge is an ultrametric ring seminorm whose closed ball
of radius `a ^ (-n)` is exactly `ϖ ^ n A₀`.

When moreover `A` is a topological ring in which the sets `ϖ ^ n A₀`, `n ≥ 0`, form a
neighbourhood basis of zero, as for a ring of definition of a Tate ring and a pseudo-uniformiser
in it, the gauge recovers the topology: its open balls about zero form a neighbourhood basis of
zero. Its zero set is the closure of zero, so it separates points exactly when `A` is Hausdorff,
and it takes the value one at one when `A` is moreover nonzero. Two subrings with this property
give gauges bounded by constant multiples of each other.

This is how a Tate ring is given a norm. The gauge is explicit data attached to the choice of the
subring `A₀`, the unit `ϖ ∈ A₀` and the base `a`, and its exact `ϖ`-scaling makes `ϖ` a
multiplicative pseudo-uniformiser for it; a topologically nilpotent unit need not scale an
arbitrary compatible norm in this way.

## Main definitions

* `TauCeti.Huber.tateGauge A₀ ϖ a`: the Tate gauge.
* `TauCeti.Huber.tateSeminorm`: the Tate gauge as a `RingSeminorm`, when `ϖ ∈ A₀`,
  `A = A₀[1/ϖ]` and `a > 1`.

## Main results

* `TauCeti.Huber.tateGauge_zpow_mul`: exact scaling
  `tateGauge A₀ ϖ a (ϖ ^ k * x) = a ^ (-k) * tateGauge A₀ ϖ a x`.
* `TauCeti.Huber.tateGauge_rpow`: changing the base.
* `TauCeti.Huber.isNonarchimedean_tateGauge` and `TauCeti.Huber.tateGauge_le_zpow_iff`: the gauge
  is ultrametric, and its closed ball of radius `a ^ (-n)` is `ϖ ^ n A₀`.
* `TauCeti.Huber.hasBasis_tateGauge` and `TauCeti.Huber.exists_tateSeminorm`: the gauge is an
  ultrametric ring seminorm defining the topology.
* `TauCeti.Huber.tateGauge_equiv`: changing the subring gives a bounded-equivalent gauge.
* `TauCeti.Huber.tateGauge_eq_zero_iff` and
  `TauCeti.Huber.t2Space_iff_forall_tateGauge_eq_zero_iff`: the zero set of the gauge is the
  closure of zero, so the gauge separates points exactly when the ring is Hausdorff.
* `TauCeti.Huber.tateGauge_one`: in a nonzero Hausdorff ring the gauge of one is one.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4 and Remark 2.4.4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Filter Topology Pointwise

namespace TauCeti.Huber

variable {A : Type*} [CommRing A]

/-- The *Tate gauge* of a subring `A₀`, a unit `ϖ` and a base `a`: the infimum of `a ^ (-n)` over
the integers `n` with `ϖ ^ (-n) * x ∈ A₀`, that is with `x ∈ ϖ ^ n A₀`. -/
noncomputable def tateGauge (A₀ : Subring A) (ϖ : Aˣ) (a : ℝ) (x : A) : ℝ :=
  sInf ((fun n : ℤ ↦ a ^ (-n)) '' {n | ((ϖ ^ (-n) : Aˣ) : A) * x ∈ A₀})

theorem tateGauge_def (A₀ : Subring A) (ϖ : Aˣ) (a : ℝ) (x : A) :
    tateGauge A₀ ϖ a x = sInf ((fun n : ℤ ↦ a ^ (-n)) '' {n | ((ϖ ^ (-n) : Aˣ) : A) * x ∈ A₀}) :=
  (rfl)

variable {A₀ : Subring A} {ϖ : Aˣ} {a : ℝ}

/-! ### Elementary properties -/

section Basic

/-- The Tate gauge is nonnegative for a nonnegative base. -/
theorem tateGauge_nonneg (ha : 0 ≤ a) (x : A) : 0 ≤ tateGauge A₀ ϖ a x :=
  Real.sInf_nonneg <| by
    rintro _ ⟨n, -, rfl⟩
    exact zpow_nonneg ha _

/-- The radii `a ^ (-n)` whose infimum defines the Tate gauge of `B₀` at `x` are bounded below. -/
private theorem bddBelow_tateGauge_radii (ha : 0 ≤ a) (B₀ : Subring A) (x : A) :
    BddBelow ((fun n : ℤ ↦ a ^ (-n)) '' {n | ((ϖ ^ (-n) : Aˣ) : A) * x ∈ B₀}) :=
  ⟨0, by rintro _ ⟨n, -, rfl⟩; exact zpow_nonneg ha _⟩

/-- An element of `ϖ ^ n A₀` has Tate gauge at most `a ^ (-n)`. -/
theorem tateGauge_le_zpow (ha : 0 ≤ a) {x : A} {n : ℤ}
    (hn : ((ϖ ^ (-n) : Aˣ) : A) * x ∈ A₀) : tateGauge A₀ ϖ a x ≤ a ^ (-n) :=
  csInf_le (bddBelow_tateGauge_radii ha _ _) ⟨n, hn, rfl⟩

/-- An element of `A₀` has Tate gauge at most one. -/
theorem tateGauge_le_one (ha : 0 ≤ a) {x : A} (hx : x ∈ A₀) : tateGauge A₀ ϖ a x ≤ 1 := by
  simpa using tateGauge_le_zpow (A₀ := A₀) (ϖ := ϖ) ha (n := 0) (by simpa using hx)

/-- The Tate gauge is below `r` exactly when `x ∈ ϖ ^ n A₀` for some `n` with `a ^ (-n) < r`,
provided some power of `ϖ` moves `x` into `A₀`. -/
theorem tateGauge_lt_iff (ha : 0 ≤ a) {x : A} (hx : ∃ n : ℤ, ((ϖ ^ n : Aˣ) : A) * x ∈ A₀)
    {r : ℝ} :
    tateGauge A₀ ϖ a x < r ↔ ∃ n : ℤ, ((ϖ ^ (-n) : Aˣ) : A) * x ∈ A₀ ∧ a ^ (-n) < r := by
  obtain ⟨n, hn⟩ := hx
  rw [tateGauge_def,
    csInf_lt_iff (bddBelow_tateGauge_radii ha _ _) ⟨_, -n, by simpa using hn, rfl⟩]
  simp

@[simp]
theorem tateGauge_neg (x : A) : tateGauge A₀ ϖ a (-x) = tateGauge A₀ ϖ a x := by
  simp [tateGauge_def, mul_neg, neg_mem_iff]

private theorem coe_zpow_mul_coe_zpow (m n : ℤ) :
    ((ϖ ^ m : Aˣ) : A) * ((ϖ ^ n : Aˣ) : A) = ((ϖ ^ (m + n) : Aˣ) : A) := by
  rw [← Units.val_mul, ← zpow_add]

private theorem zpow_neg_mul_zpow_mul (n k : ℤ) (x : A) :
    ((ϖ ^ (-n) : Aˣ) : A) * (((ϖ ^ k : Aˣ) : A) * x) = ((ϖ ^ (-(n - k)) : Aˣ) : A) * x := by
  rw [← mul_assoc, coe_zpow_mul_coe_zpow, neg_sub, neg_add_eq_sub]

/-- Multiplication by `ϖ ^ k` scales the Tate gauge exactly by `a ^ (-k)`. -/
theorem tateGauge_zpow_mul (ha : 0 < a) (k : ℤ) (x : A) :
    tateGauge A₀ ϖ a (((ϖ ^ k : Aˣ) : A) * x) = a ^ (-k) * tateGauge A₀ ϖ a x := by
  rw [tateGauge_def, tateGauge_def, ← smul_eq_mul (a ^ (-k)),
    ← Real.sInf_smul_of_nonneg (zpow_nonneg ha.le _)]
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_smul_set, Set.mem_ofPred_eq, zpow_neg_mul_zpow_mul,
    smul_eq_mul]
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨_, ⟨n - k, hn, rfl⟩, ?_⟩
    rw [← zpow_add₀ ha.ne']
    congr 1
    ring
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨m + k, by simpa using hm, ?_⟩
    rw [← zpow_add₀ ha.ne']
    congr 1
    ring

private theorem tateGauge_le_tateGauge (ha : 0 ≤ a) {B₀ : Subring A} {x y : A}
    (hy : ∃ n : ℤ, ((ϖ ^ n : Aˣ) : A) * y ∈ B₀)
    (h : ∀ n : ℤ, ((ϖ ^ (-n) : Aˣ) : A) * y ∈ B₀ → ((ϖ ^ (-n) : Aˣ) : A) * x ∈ A₀) :
    tateGauge A₀ ϖ a x ≤ tateGauge B₀ ϖ a y := by
  obtain ⟨n, hn⟩ := hy
  exact csInf_le_csInf (bddBelow_tateGauge_radii ha _ _) ⟨_, -n, by simpa using hn, rfl⟩ <|
    Set.image_mono fun m hm ↦ h m hm

private theorem tateGauge_eq_zero_of_forall (ha : 1 < a) {x : A}
    (h : ∀ n : ℕ, ((ϖ ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ A₀) : tateGauge A₀ ϖ a x = 0 := by
  have ha₀ : 0 ≤ a := zero_le_one.trans ha.le
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) (tateGauge_nonneg ha₀ _)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ ha)
  rw [zero_add]
  refine (tateGauge_le_zpow ha₀ (h n)).trans ?_
  simpa [zpow_neg] using hn.le

@[simp]
theorem tateGauge_zero (ha : 1 < a) : tateGauge A₀ ϖ a 0 = 0 :=
  tateGauge_eq_zero_of_forall ha fun _ ↦ by simp

/-- If `ϖ ^ k B₀ ⊆ A₀` and a power of `ϖ` moves `x` into `B₀`, then the Tate gauge of `A₀` at
`x` is at most `a ^ k` times that of `B₀`. -/
theorem tateGauge_le_zpow_mul_tateGauge (ha : 0 < a) {B₀ : Subring A} (x : A)
    (hB : ∃ n : ℤ, ((ϖ ^ n : Aˣ) : A) * x ∈ B₀) {k : ℤ}
    (hk : ∀ y ∈ B₀, ((ϖ ^ k : Aˣ) : A) * y ∈ A₀) :
    tateGauge A₀ ϖ a x ≤ a ^ k * tateGauge B₀ ϖ a x := by
  have h : tateGauge A₀ ϖ a (((ϖ ^ k : Aˣ) : A) * x) ≤ tateGauge B₀ ϖ a x :=
    tateGauge_le_tateGauge ha.le hB fun n hn ↦ by
      rw [mul_left_comm]
      exact hk _ hn
  rw [tateGauge_zpow_mul ha] at h
  calc tateGauge A₀ ϖ a x = a ^ k * (a ^ (-k) * tateGauge A₀ ϖ a x) := by
        rw [← mul_assoc, ← zpow_add₀ ha.ne', add_neg_cancel, zpow_zero, one_mul]
    _ ≤ a ^ k * tateGauge B₀ ϖ a x := by gcongr

/-- Changing the base `a > 1` to `b > 1` raises the Tate gauge to the power `log b / log a`. -/
theorem tateGauge_rpow (ha : 1 < a) {b : ℝ} (hb : 1 < b) (x : A) :
    tateGauge A₀ ϖ b x = tateGauge A₀ ϖ a x ^ (Real.log b / Real.log a) := by
  have ha₀ : 0 < a := zero_lt_one.trans ha
  have ht : 0 < Real.log b / Real.log a := div_pos (Real.log_pos hb) (Real.log_pos ha)
  have hpow (n : ℤ) : (a ^ (-n)) ^ (Real.log b / Real.log a) = b ^ (-n) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul ha₀.le, Real.rpow_def_of_pos ha₀,
      ← Real.rpow_intCast, Real.rpow_def_of_pos (zero_lt_one.trans hb)]
    congr 1
    field_simp [(Real.log_pos ha).ne']
  rw [tateGauge_def, tateGauge_def]
  set S : Set ℤ := {n | ((ϖ ^ (-n) : Aˣ) : A) * x ∈ A₀}
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Set.image_empty, Set.image_empty, Real.sInf_empty, Real.zero_rpow ht.ne']
  have h := MonotoneOn.map_csInf_of_continuousWithinAt
    (f := fun y : ℝ ↦ y ^ (Real.log b / Real.log a))
    (Real.continuousAt_rpow_const _ _ (Or.inr ht.le)).continuousWithinAt ?_ (hS.image _)
    (bddBelow_tateGauge_radii ha₀.le _ _)
  · rw [h, Set.image_image]
    simp_rw [hpow]
  · rintro _ ⟨m, -, rfl⟩ _ ⟨m', -, rfl⟩ h
    exact Real.rpow_le_rpow (zpow_nonneg ha₀.le _) h ht.le

end Basic

/-! ### The Tate gauge as an ultrametric ring seminorm -/

section Seminorm

variable (hϖ : (ϖ : A) ∈ A₀) (hA : ∀ x : A, ∃ n : ℤ, ((ϖ ^ n : Aˣ) : A) * x ∈ A₀)
include hϖ

/-- If `ϖ ∈ A₀`, the sets `ϖ ^ n A₀` decrease in `n`: an element of `ϖ ^ n A₀` lies in `ϖ ^ m A₀`
for every `m ≤ n`. -/
theorem zpow_neg_mul_mem_of_le {x : A} {m n : ℤ} (hmn : m ≤ n)
    (hn : ((ϖ ^ (-n) : Aˣ) : A) * x ∈ A₀) : ((ϖ ^ (-m) : Aˣ) : A) * x ∈ A₀ := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hmn)
  have h : ((ϖ ^ (-m) : Aˣ) : A) * x = (ϖ : A) ^ k * (((ϖ ^ (-n) : Aˣ) : A) * x) := by
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← hk, ← mul_assoc,
      coe_zpow_mul_coe_zpow]
    congr 3
    omega
  rw [h]
  exact A₀.mul_mem (A₀.pow_mem hϖ k) hn

/-- If some power of `ϖ` moves `x` into `A₀`, then membership of `x` in the closed ball of radius
`a ^ (-n)` of the Tate gauge is equivalent to membership in `ϖ ^ n A₀`. -/
theorem tateGauge_le_zpow_iff {x : A}
    (hx : ∃ m : ℤ, ((ϖ ^ m : Aˣ) : A) * x ∈ A₀) (ha : 1 < a) {n : ℤ} :
    tateGauge A₀ ϖ a x ≤ a ^ (-n) ↔ ((ϖ ^ (-n) : Aˣ) : A) * x ∈ A₀ := by
  refine ⟨fun h ↦ ?_, tateGauge_le_zpow (zero_le_one.trans ha.le)⟩
  obtain ⟨m, hm, hmn⟩ := (tateGauge_lt_iff (zero_le_one.trans ha.le) hx).1 <|
    h.trans_lt ((zpow_lt_zpow_iff_right₀ ha).2 (by omega : -n < -(n - 1)))
  rw [zpow_lt_zpow_iff_right₀ ha] at hmn
  exact zpow_neg_mul_mem_of_le hϖ (by omega) hm

include hA in
/-- The Tate gauge is ultrametric. -/
theorem isNonarchimedean_tateGauge (ha : 0 ≤ a) :
    IsNonarchimedean (tateGauge A₀ ϖ a) := by
  intro x y
  refine le_of_forall_gt fun r hr ↦ ?_
  rw [sup_lt_iff] at hr
  obtain ⟨n, hn, hnr⟩ := (tateGauge_lt_iff ha (hA x)).1 hr.1
  obtain ⟨m, hm, hmr⟩ := (tateGauge_lt_iff ha (hA y)).1 hr.2
  rcases le_total n m with h | h
  · refine (tateGauge_le_zpow ha ?_).trans_lt hnr
    rw [mul_add]
    exact A₀.add_mem hn (zpow_neg_mul_mem_of_le hϖ h hm)
  · refine (tateGauge_le_zpow ha ?_).trans_lt hmr
    rw [mul_add]
    exact A₀.add_mem (zpow_neg_mul_mem_of_le hϖ h hn) hm

omit hϖ in
/-- Multiplying an eligible element by an element of `A₀` does not increase the Tate gauge. -/
theorem tateGauge_mul_le_of_mem {x y : A}
    (hy : ∃ n : ℤ, ((ϖ ^ n : Aˣ) : A) * y ∈ A₀) (ha : 0 ≤ a) (hx : x ∈ A₀) :
    tateGauge A₀ ϖ a (x * y) ≤ tateGauge A₀ ϖ a y := by
  refine tateGauge_le_tateGauge ha hy fun m hm ↦ ?_
  rw [mul_left_comm]
  exact A₀.mul_mem hx hm

omit hϖ in
/-- The Tate gauge is submultiplicative on elements that some powers of `ϖ` move into `A₀`. -/
theorem tateGauge_mul_le (x y : A) (hx : ∃ n : ℤ, ((ϖ ^ n : Aˣ) : A) * x ∈ A₀)
    (hy : ∃ n : ℤ, ((ϖ ^ n : Aˣ) : A) * y ∈ A₀) (ha : 0 < a) :
    tateGauge A₀ ϖ a (x * y) ≤ tateGauge A₀ ϖ a x * tateGauge A₀ ϖ a y := by
  obtain ⟨n, hn⟩ := hx
  rw [mul_comm (tateGauge A₀ ϖ a x), tateGauge_def A₀ ϖ a x, ← smul_eq_mul (tateGauge A₀ ϖ a y),
    ← Real.sInf_smul_of_nonneg (tateGauge_nonneg ha.le y)]
  refine le_csInf ⟨_, Set.smul_mem_smul_set ⟨-n, by simpa using hn, rfl⟩⟩ ?_
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  have h : x * y = ((ϖ ^ m : Aˣ) : A) * ((((ϖ ^ (-m) : Aˣ) : A) * x) * y) := by
    rw [← mul_assoc, ← mul_assoc, coe_zpow_mul_coe_zpow]
    simp
  rw [h, tateGauge_zpow_mul ha]
  simp only [smul_eq_mul]
  rw [mul_comm]
  gcongr
  exact tateGauge_mul_le_of_mem hy ha.le hm

include hA in
/-- The Tate gauge of `A₀`, `ϖ` and `a > 1` as a ring seminorm, when every element of `A` is
moved into `A₀` by some power of `ϖ`. -/
noncomputable def tateSeminorm (ha : 1 < a) : RingSeminorm A where
  toFun := tateGauge A₀ ϖ a
  map_zero' := tateGauge_zero ha
  add_le' x y := (isNonarchimedean_tateGauge hϖ hA (zero_le_one.trans ha.le) x y).trans <|
    max_le_add_of_nonneg (tateGauge_nonneg (zero_le_one.trans ha.le) x)
      (tateGauge_nonneg (zero_le_one.trans ha.le) y)
  neg' := tateGauge_neg
  mul_le' x y := tateGauge_mul_le x y (hA x) (hA y) (zero_lt_one.trans ha)

@[simp]
theorem coe_tateSeminorm (ha : 1 < a) : ⇑(tateSeminorm hϖ hA ha) = tateGauge A₀ ϖ a :=
  (rfl)

/-- An element that some power of `ϖ` moves into `A₀` has Tate gauge zero exactly when it lies in
every `ϖ ^ n A₀`, `n ≥ 0`. -/
theorem tateGauge_eq_zero_iff_forall {x : A}
    (hx : ∃ m : ℤ, ((ϖ ^ m : Aˣ) : A) * x ∈ A₀) (ha : 1 < a) :
    tateGauge A₀ ϖ a x = 0 ↔ ∀ n : ℕ, ((ϖ ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ A₀ :=
  ⟨fun h _ ↦ (tateGauge_le_zpow_iff hϖ hx ha).1 (h ▸ zpow_nonneg (zero_le_one.trans ha.le) _),
    tateGauge_eq_zero_of_forall ha⟩

end Seminorm

/-! ### Recovering the topology -/

section Topology

variable [TopologicalSpace A]
  (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
    (fun n ↦ {x | ((ϖ ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ A₀}))
include hb

private theorem mem_nhds_zero_of_hasBasis : (A₀ : Set A) ∈ 𝓝 (0 : A) := by
  simpa using hb.mem_of_mem (i := 0) trivial

/-- If the sets `ϖ ^ n A₀`, `n ≥ 0`, form a neighbourhood basis of zero and multiplication is
separately continuous, then every element of `A` is moved into `A₀` by some power of `ϖ`. -/
theorem exists_zpow_mul_mem_of_hasBasis [SeparatelyContinuousMul A] (x : A) :
    ∃ n : ℤ, ((ϖ ^ n : Aˣ) : A) * x ∈ A₀ := by
  have h : (· * x) ⁻¹' (A₀ : Set A) ∈ 𝓝 (0 : A) :=
    (continuous_mul_const x).continuousAt.preimage_mem_nhds <| by
      rw [zero_mul]
      exact mem_nhds_zero_of_hasBasis hb
  obtain ⟨n, -, hn⟩ := hb.mem_iff.1 h
  refine ⟨n, hn ?_⟩
  simp [← mul_pow]

/-- If the sets `ϖ ^ n A₀`, `n ≥ 0`, form a neighbourhood basis of zero, then so do the open
balls about zero of the Tate gauge. -/
theorem hasBasis_tateGauge [SeparatelyContinuousMul A] (ha : 1 < a) (hϖ : (ϖ : A) ∈ A₀) :
    (𝓝 (0 : A)).HasBasis (fun ε : ℝ ↦ 0 < ε) (fun ε ↦ {x | tateGauge A₀ ϖ a x < ε}) := by
  refine hb.to_hasBasis (fun n _ ↦ ⟨a ^ (-(n : ℤ)), zpow_pos (zero_lt_one.trans ha) _,
    fun x hx ↦ (tateGauge_le_zpow_iff hϖ (exists_zpow_mul_mem_of_hasBasis hb x) ha).1
      (le_of_lt hx)⟩) fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ ha)
  exact ⟨n, trivial, fun x hx ↦ (tateGauge_le_zpow (zero_le_one.trans ha.le) hx).trans_lt <|
    by simpa [zpow_neg] using hn⟩

/-- A ring with separately continuous multiplication in which the sets `ϖ ^ n A₀`, `n ≥ 0`, form
a neighbourhood basis of zero carries an ultrametric ring seminorm, equal to the Tate gauge, whose
open balls about zero form a neighbourhood basis of zero. -/
theorem exists_tateSeminorm [SeparatelyContinuousMul A] (ha : 1 < a) (hϖ : (ϖ : A) ∈ A₀) :
    ∃ α : RingSeminorm A, (∀ x, α x = tateGauge A₀ ϖ a x) ∧ IsNonarchimedean α ∧
      (𝓝 (0 : A)).HasBasis (fun ε : ℝ ↦ 0 < ε) (fun ε ↦ {x | α x < ε}) := by
  have hA := exists_zpow_mul_mem_of_hasBasis hb
  refine ⟨tateSeminorm hϖ hA ha, by simp, ?_, ?_⟩
  · simpa using isNonarchimedean_tateGauge hϖ hA (zero_le_one.trans ha.le)
  · simpa using hasBasis_tateGauge hb ha hϖ

private theorem exists_tateGauge_le_zpow_mul [SeparatelyContinuousMul A] (ha : 0 < a)
    {B₀ : Subring A}
    (hbB : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {x | ((ϖ ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ B₀})) :
    ∃ k : ℕ, ∀ x, tateGauge A₀ ϖ a x ≤ a ^ (k : ℤ) * tateGauge B₀ ϖ a x := by
  obtain ⟨k, -, hk⟩ := hbB.mem_iff.1 (mem_nhds_zero_of_hasBasis hb)
  refine ⟨k, fun x ↦ tateGauge_le_zpow_mul_tateGauge ha x
    (exists_zpow_mul_mem_of_hasBasis hbB x) fun y hy ↦ hk ?_⟩
  simpa [← mul_assoc, ← mul_pow] using hy

/-- For two subrings `A₀` and `B₀` such that the sets `ϖ ^ n A₀` and the sets `ϖ ^ n B₀` both form
neighbourhood bases of zero, the two Tate gauges for any positive base are bounded by constant
multiples of each other. -/
theorem tateGauge_equiv [SeparatelyContinuousMul A] (ha : 0 < a) {B₀ : Subring A}
    (hbB : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {x | ((ϖ ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ B₀})) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, tateGauge A₀ ϖ a x ≤ C * tateGauge B₀ ϖ a x ∧
      tateGauge B₀ ϖ a x ≤ C * tateGauge A₀ ϖ a x := by
  obtain ⟨k, hk⟩ := exists_tateGauge_le_zpow_mul hb ha hbB
  obtain ⟨l, hl⟩ := exists_tateGauge_le_zpow_mul hbB ha hb
  refine ⟨max (a ^ (k : ℤ)) (a ^ (l : ℤ)), lt_max_of_lt_left (zpow_pos ha _), fun x ↦
    ⟨(hk x).trans ?_, (hl x).trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (tateGauge_nonneg ha.le _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (tateGauge_nonneg ha.le _)

/-- If the sets `ϖ ^ n A₀`, `n ≥ 0`, form a neighbourhood basis of zero and `ϖ ∈ A₀`, then the
zero set of the Tate gauge is the closure of zero. -/
theorem tateGauge_eq_zero_iff [SeparatelyContinuousMul A] [R0Space A] (ha : 1 < a)
    (hϖ : (ϖ : A) ∈ A₀) {x : A} :
    tateGauge A₀ ϖ a x = 0 ↔ x ∈ closure ({0} : Set A) := by
  rw [tateGauge_eq_zero_iff_forall hϖ (exists_zpow_mul_mem_of_hasBasis hb x) ha,
    R0Space.closure_singleton, hb.ker]
  simp

/-- If the sets `ϖ ^ n A₀`, `n ≥ 0`, form a neighbourhood basis of zero and `ϖ ∈ A₀`, then the
Tate gauge separates points exactly when `A` is Hausdorff. -/
theorem t2Space_iff_forall_tateGauge_eq_zero_iff [SeparatelyContinuousMul A]
    [IsTopologicalAddGroup A] (ha : 1 < a)
    (hϖ : (ϖ : A) ∈ A₀) : T2Space A ↔ ∀ x, (tateGauge A₀ ϖ a x = 0 ↔ x = 0) := by
  simp_rw [tateGauge_eq_zero_iff hb ha hϖ, IsTopologicalAddGroup.t2Space_iff_zero_closed,
    ← closure_subset_iff_isClosed, Set.subset_def, Set.mem_singleton_iff]
  exact ⟨fun h x ↦ ⟨h x, fun hx ↦ hx ▸ subset_closure rfl⟩, fun h x ↦ (h x).1⟩

/-- If the sets `ϖ ^ n A₀`, `n ≥ 0`, form a neighbourhood basis of zero in a nonzero T₁ ring
with separately continuous multiplication and `ϖ ∈ A₀`, then the Tate gauge of one is one. -/
theorem tateGauge_one [SeparatelyContinuousMul A] [T1Space A] [Nontrivial A] (ha : 1 < a)
    (hϖ : (ϖ : A) ∈ A₀) : tateGauge A₀ ϖ a 1 = 1 := by
  have hA := exists_zpow_mul_mem_of_hasBasis hb
  have ha₀ : 0 ≤ a := zero_le_one.trans ha.le
  rw [← coe_tateSeminorm hϖ hA ha]
  apply (RingSeminorm.seminorm_one_eq_one_iff_ne_zero _
    (tateGauge_le_one ha₀ A₀.one_mem)).2
  intro h
  have h1 : tateGauge A₀ ϖ a 1 = 0 := by
    simpa using RingSeminorm.eq_zero_iff.1 h 1
  simpa using (tateGauge_eq_zero_iff hb ha hϖ).1 h1

end Topology

end TauCeti.Huber
