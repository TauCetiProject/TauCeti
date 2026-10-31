/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

import Mathlib.NumberTheory.Ostrowski

/-!
# The approximation product of a system of linear forms

Let `K` be a number field, `F` a field extension of `K`, and `x : ι → K` a point. Fix finite sets
`Sinf` of infinite places and `Sfin` of finite places of `K`, at each such place `v` an absolute
value `w v` of `F` and a family of linear forms `L v i` on `F^ι`. The quantity measuring how well
`x` approximates the zeros of the forms is the product, over the places in `Sinf` and `Sfin`, of

`∏ i, w v (L v i x) / ⨆ j, v (x j)`,

raised to the power `mult v` at an infinite place. This is `NumberField.approxProd`. Points lie in
`K` and the forms have coefficients in `F`. The forms and the absolute values are indexed by the
underlying absolute value of a place, so that one family serves both sets of places. The
definition makes sense for any field `F` and any absolute values `w v`; the Diophantine
interpretation below needs more.

The normalization is Mathlib's relative one, as in `Height.mulHeight`: the local factor at an
infinite place carries the exponent `mult v`. Suppose that `F` is algebraic over `K` (for instance
an algebraic closure of `K`), that each `w v` lies over `v`, and that the forms at each place are
linearly independent, and let `ε > 0`. Then the Subspace Theorem says that the nonzero `x` with
`approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-card ι - ε)` lie in finitely many proper subspaces
of `K^ι`: this is the number-field form of Schlickewei and Evertse, and with `K = ℚ` Schmidt's
form with algebraic coefficients. This file develops the quantity itself, not the theorem, and
assumes `w v` lies over `v` only where a result needs it.

## Main results

* `NumberField.approxProd_smul`: the approximation product is a function on projective space,
  `approxProd … (c • x) = approxProd … x` for `c ≠ 0`, because each `w v` lies over `v`. The
  example at the end of the file shows that the hypothesis cannot be dropped.
* `NumberField.apply_div_iSup_smul` and `NumberField.prod_div_iSup_nonneg`: one factor of a local
  factor is invariant under nonzero scaling when `w` lies over `v`, and a local factor is
  nonnegative.
* `NumberField.approxProd_union`: it is multiplicative in disjoint sets of places, and
  `NumberField.approxProd_empty`: it is `1` over no places.
* `NumberField.prod_proj_div_iSup_le_one`: the local factor of the coordinate forms is at most
  `1`; hence `NumberField.approxProd_le_one` when every place carries the coordinate forms, and
  `NumberField.approxProd_le_approxProd_of_subset`: enlarging the sets of places by places
  carrying the coordinate forms can only decrease the approximation product.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Theorem 7.2.2 and §7.2.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute subspace theorem*,
  J. reine angew. Math. 548 (2002).
-/

public section

open AbsoluteValue Module

namespace NumberField

variable {K F ι : Type*} [Field K] [Field F] [Algebra K F]

/-- One factor of a local factor of `approxProd` is unchanged under scaling the point by a nonzero
scalar, when `w` lies over `v`. -/
theorem apply_div_iSup_smul {v : AbsoluteValue K ℝ} {w : AbsoluteValue F ℝ}
    [w.LiesOver v] (l : Dual F (ι → F)) {c : K} (hc : c ≠ 0) (x : ι → K) :
    w (l fun j ↦ algebraMap K F ((c • x) j)) / ⨆ j, v ((c • x) j) =
      w (l fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  have h : (fun j ↦ algebraMap K F ((c • x) j)) =
      algebraMap K F c • fun j ↦ algebraMap K F (x j) := by
    ext j
    simp
  rw [h, map_smul, smul_eq_mul, map_mul, LiesOver.apply_algebraMap v]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← Real.mul_iSup_of_nonneg (v.nonneg c), mul_div_mul_left _ _ (v.ne_zero hc)]

variable [Fintype ι]

/-- A local factor of `approxProd` is nonnegative. -/
theorem prod_div_iSup_nonneg (v : AbsoluteValue K ℝ) (w : AbsoluteValue F ℝ)
    (l : ι → Dual F (ι → F)) (x : ι → K) :
    0 ≤ ∏ i, w (l i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) :=
  Finset.prod_nonneg fun _ _ ↦
    div_nonneg (apply_nonneg _ _) (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)

/-- The local factor of the coordinate forms at an absolute value `w` lying over `v` is at most
`1`: each coordinate is bounded by the local sup norm. -/
theorem prod_proj_div_iSup_le_one {v : AbsoluteValue K ℝ} {w : AbsoluteValue F ℝ}
    [w.LiesOver v] (x : ι → K) :
    ∏ i, w (LinearMap.proj (R := F) i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) ≤ 1 := by
  refine Finset.prod_le_one₀ (fun i _ ↦ ?_) fun i _ ↦ ?_
  · exact div_nonneg (apply_nonneg _ _) (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
  · rw [LinearMap.proj_apply, LiesOver.apply_algebraMap v]
    exact div_le_one_of_le₀ (le_ciSup (f := fun j ↦ v (x j)) (Finite.bddAbove_range _) i)
      (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)

variable [NumberField K]

/-- The approximation product of a point `x : ι → K` with respect to linear forms `L v i` with
coefficients in `F` at the places of `K` in `Sinf` and `Sfin`, each measured by an absolute value
`w v` of `F`: the product over `v ∈ Sinf` of `(∏ i, w v (L v i x) / ⨆ j, v (x j)) ^ mult v`, times
the product over `v ∈ Sfin` of `∏ i, w v (L v i x) / ⨆ j, v (x j)`, where `x` is mapped into `F`.

The data `w` and `L` are indexed by the underlying absolute value of a place, and their values off
`Sinf ∪ Sfin` play no role. -/
noncomputable def approxProd (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (x : ι → K) : ℝ :=
  (∏ v ∈ Sinf, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult) *
    ∏ v ∈ Sfin, ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)

theorem approxProd_def (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (x : ι → K) :
    approxProd Sinf Sfin w L x =
      (∏ v ∈ Sinf, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult) *
        ∏ v ∈ Sfin, ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  rw [approxProd]

variable {Sinf Sinf' : Finset (InfinitePlace K)} {Sfin Sfin' : Finset (FinitePlace K)}
  {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}

/-- The approximation product is invariant under scaling the point by a nonzero element of `K`,
provided that each absolute value `w v` lies over `v`. -/
theorem approxProd_smul (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1) {c : K} (hc : c ≠ 0) (x : ι → K) :
    approxProd Sinf Sfin w L (c • x) = approxProd Sinf Sfin w L x := by
  simp only [approxProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  congr 1
  · refine Finset.prod_congr rfl fun v hv ↦ ?_
    have := hwInf v hv
    simp only [apply_div_iSup_smul _ hc]
  · refine Finset.prod_congr rfl fun v hv ↦ ?_
    have := hwFin v hv
    simp only [apply_div_iSup_smul _ hc]

/-- The approximation product is nonnegative. -/
theorem approxProd_nonneg (x : ι → K) : 0 ≤ approxProd Sinf Sfin w L x := by
  simp only [approxProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  exact mul_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (prod_div_iSup_nonneg _ _ _ x) _)
    (Finset.prod_nonneg fun v _ ↦ prod_div_iSup_nonneg _ _ _ x)

/-- The approximation product over no places is `1`. -/
@[simp]
theorem approxProd_empty (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) :
    approxProd ∅ ∅ w L x = 1 := by
  simp [approxProd_def]

/-- The approximation product is multiplicative in disjoint sets of places. -/
theorem approxProd_union [DecidableEq (InfinitePlace K)] [DecidableEq (FinitePlace K)]
    (hinf : Disjoint Sinf Sinf') (hfin : Disjoint Sfin Sfin') (x : ι → K) :
    approxProd (Sinf ∪ Sinf') (Sfin ∪ Sfin') w L x =
      approxProd Sinf Sfin w L x * approxProd Sinf' Sfin' w L x := by
  simp only [approxProd_def, Finset.prod_union hinf, Finset.prod_union hfin]
  ring

/-- The approximation product is at most `1` when every place carries the coordinate forms,
measured by an absolute value lying over it. -/
theorem approxProd_le_one (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1) (hLInf : ∀ v ∈ Sinf, ∀ i, L v.1 i = LinearMap.proj i)
    (hLFin : ∀ v ∈ Sfin, ∀ i, L v.1 i = LinearMap.proj i) (x : ι → K) :
    approxProd Sinf Sfin w L x ≤ 1 := by
  simp only [approxProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  have hinf : ∀ v ∈ Sinf,
      ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v.1 (x j) ≤ 1 := fun v hv ↦ by
    have := hwInf v hv
    simpa only [hLInf v hv] using prod_proj_div_iSup_le_one (w := w v.1) x
  have hfin : ∀ v ∈ Sfin,
      ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v.1 (x j) ≤ 1 := fun v hv ↦ by
    have := hwFin v hv
    simpa only [hLFin v hv] using prod_proj_div_iSup_le_one (w := w v.1) x
  refine (mul_le_of_le_one_left (Finset.prod_nonneg fun v _ ↦ prod_div_iSup_nonneg _ _ _ x)
    (Finset.prod_le_one₀ (fun v _ ↦ pow_nonneg (prod_div_iSup_nonneg _ _ _ x) _)
      fun v hv ↦ pow_le_one₀ (prod_div_iSup_nonneg _ _ _ x) (hinf v hv))).trans ?_
  exact Finset.prod_le_one₀ (fun v _ ↦ prod_div_iSup_nonneg _ _ _ x) hfin

/-- Enlarging the sets of places by places carrying the coordinate forms, each measured by an
absolute value lying over it, can only decrease the approximation product. -/
theorem approxProd_le_approxProd_of_subset (hinf : Sinf ⊆ Sinf') (hfin : Sfin ⊆ Sfin')
    (hwInf : ∀ v ∈ Sinf', v ∉ Sinf → (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ Sfin', v ∉ Sfin → (w v.1).LiesOver v.1)
    (hLInf : ∀ v ∈ Sinf', v ∉ Sinf → ∀ i, L v.1 i = LinearMap.proj i)
    (hLFin : ∀ v ∈ Sfin', v ∉ Sfin → ∀ i, L v.1 i = LinearMap.proj i) (x : ι → K) :
    approxProd Sinf' Sfin' w L x ≤ approxProd Sinf Sfin w L x := by
  classical
  rw [← Finset.union_sdiff_of_subset hinf, ← Finset.union_sdiff_of_subset hfin,
    approxProd_union Finset.disjoint_sdiff Finset.disjoint_sdiff]
  refine mul_le_of_le_one_right (approxProd_nonneg x) (approxProd_le_one ?_ ?_ ?_ ?_ x) <;>
    simp only [Finset.mem_sdiff] <;> grind

/-- `approxProd_smul` needs `w v` to lie over `v`: over `ℚ`, measuring the coordinate forms at
the real place by the `3`-adic absolute value, scaling the point `(1, …, 1)` by `3` divides the
approximation product by `9 ^ card ι`. -/
example [Nonempty ι] :
    approxProd {Rat.infinitePlace} ∅ (fun _ ↦ Rat.AbsoluteValue.padic 3)
        (fun _ i ↦ LinearMap.proj i) ((3 : ℚ) • fun _ : ι ↦ (1 : ℚ)) =
      (9 ^ Fintype.card ι)⁻¹ *
        approxProd {Rat.infinitePlace} ∅ (fun _ ↦ Rat.AbsoluteValue.padic 3)
          (fun _ i ↦ LinearMap.proj i) fun _ : ι ↦ (1 : ℚ) := by
  have h3 : padicValRat 3 3 = 1 := by exact_mod_cast padicValRat.self (p := 3) (by norm_num)
  norm_num [approxProd_def, Rat.infinitePlace_apply, Rat.isReal_infinitePlace.mult_eq_one, h3,
    div_eq_mul_inv, ← mul_inv, ← mul_pow]

end NumberField
