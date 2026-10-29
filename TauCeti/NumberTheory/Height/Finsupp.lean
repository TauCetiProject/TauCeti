/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.Data.Finsupp.SMul
import all Mathlib.NumberTheory.Height.Basic

/-!
# Heights of finitely supported coefficient vectors

The native `Finsupp.mulHeight` is a projective height on the nonzero support.
This module identifies it with finite tuples containing that support, and proves
invariance under scalar multiplication and injective reindexing. These interfaces
allow polynomial coefficient heights to use the finite-tuple height estimates in Mathlib.

`Finsupp.mulHeight_eq_mul_of_injOn` transfers Mathlib's Segre relation
`Height.mulHeight_fun_mul_eq` to finitely supported vectors: a vector whose nonzero entries are
exactly the products `x a * y b`, each occurring once, has the product of the heights of `x` and
`y`. The coefficients of a product of polynomials in disjoint sets of variables have this form.

## References

* The multiplication-table height follows `DiophantineApproximation/DisjointVariables.lean` in
  Ralf Stephan's `rwst/Subspace-Theorems`, snapshot `c26d909dc48cf7fe` (Apache 2.0).
-/

public section

namespace Finsupp

variable {K α β : Type*} [Field K] [Height.AdmissibleAbsValues K]

/-- Padding a finitely supported coefficient vector by zeroes does not change its height. -/
theorem mulHeight_eq_of_support_subset (x : α →₀ K) (s : Finset α)
    (hs : x.support ⊆ s) :
    x.mulHeight = Height.mulHeight (fun i : s ↦ x i) := by
  classical
  let e : x.support ≃ (fun i : s ↦ x i).support := Equiv.ofBijective
    (fun i ↦ ⟨⟨i, hs i.prop⟩, by simpa using mem_support_iff.mp i.prop⟩)
    ⟨fun _ _ h ↦ Subtype.ext (congrArg (fun j ↦ j.val.val) h),
      fun j ↦ ⟨⟨j.val, by exact mem_support_iff.mpr j.prop⟩, rfl⟩⟩
  rw [Height.mulHeight_eq_mulHeight_restrict_support]
  exact Height.mulHeight_comp_equiv e (fun i ↦ x i.val.val)

@[simp]
theorem mulHeight_zero : (0 : α →₀ K).mulHeight = 1 := by
  simp [Finsupp.mulHeight]

@[simp]
theorem logHeight_zero : (0 : α →₀ K).logHeight = 0 := by
  simp [Finsupp.logHeight]

theorem one_le_mulHeight (x : α →₀ K) : 1 ≤ x.mulHeight :=
  Height.one_le_mulHeight _

theorem mulHeight_pos (x : α →₀ K) : 0 < x.mulHeight :=
  zero_lt_one.trans_le (one_le_mulHeight x)

/-- The full coefficient function and its nonzero support have the same projective height,
even when the index type is infinite. -/
theorem mulHeight_eq_mulHeight_coe (x : α →₀ K) : x.mulHeight = Height.mulHeight ⇑x := by
  classical
  -- Mathlib's support-restriction theorem requires a finite index type; here α is arbitrary.
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Finsupp.mulHeight]
  have hfun : (⇑x : α → K) ≠ 0 := by simpa using hx
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hfun
  have : Nonempty α := ⟨i⟩
  have : Nonempty x.support := ⟨⟨i, mem_support_iff.mpr hi⟩⟩
  have hs : (fun j : x.support ↦ x j) ≠ 0 :=
    Function.ne_iff.mpr ⟨⟨i, mem_support_iff.mpr hi⟩, hi⟩
  have hv (v : AbsoluteValue K ℝ) :
      (⨆ j : x.support, v (x j)) = ⨆ j, v (x j) := by
    refine le_antisymm (ciSup_le fun j ↦ ?_) (ciSup_le fun j ↦ ?_)
    · exact le_ciSup_of_le
        (by simpa [Set.range_comp'] using (x.finite_range.image v).bddAbove) j le_rfl
    · by_cases hj : x j = 0
      · simpa [hj] using Real.iSup_nonneg (fun j : x.support ↦ v.nonneg (x j))
      · exact Finite.le_ciSup_of_le ⟨j, mem_support_iff.mpr hj⟩ le_rfl
  simp only [Finsupp.mulHeight, Height.mulHeight_eq hs, Height.mulHeight_eq hfun, hv]

/-- The native logarithmic Finsupp height is the logarithm of its support height.
Mathlib's native characteristic equation uses `Height.mulHeight ⇑x`; this bridge uses
`Finsupp.mulHeight x`, the height on the finite support. -/
theorem logHeight_eq_log_mulHeight_support (x : α →₀ K) :
    x.logHeight = Real.log x.mulHeight := by
  exact (Finsupp.logHeight_eq_log_mulHeight x).trans
    (congrArg Real.log (mulHeight_eq_mulHeight_coe x).symm)

theorem logHeight_nonneg (x : α →₀ K) : 0 ≤ x.logHeight := by
  rw [logHeight_eq_log_mulHeight_support]
  exact Real.log_nonneg (one_le_mulHeight x)

/-- A coefficient vector supported at one index has projective height one. -/
@[simp]
theorem mulHeight_single (i : α) (c : K) : (single i c).mulHeight = 1 := by
  classical
  rw [mulHeight_eq_of_support_subset _ {i} support_single_subset]
  exact Height.mulHeight_eq_one_of_subsingleton _

@[simp]
theorem logHeight_single (i : α) (c : K) : (single i c).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight_support]

/-- Multiplication by a nonzero scalar preserves projective coefficient height. -/
@[simp]
theorem mulHeight_smul (x : α →₀ K) {c : K} (hc : c ≠ 0) :
    (c • x).mulHeight = x.mulHeight := by
  classical
  rw [mulHeight_eq_of_support_subset _ x.support (support_smul_eq hc).subset]
  exact Height.mulHeight_smul_eq_mulHeight (fun i : x.support ↦ x i) hc

@[simp]
theorem logHeight_smul (x : α →₀ K) {c : K} (hc : c ≠ 0) :
    (c • x).logHeight = x.logHeight := by
  rw [logHeight_eq_log_mulHeight_support, mulHeight_smul x hc,
    logHeight_eq_log_mulHeight_support]

/-- Injective reindexing preserves the height of a finitely supported coefficient vector. -/
@[simp]
theorem mulHeight_embDomain (x : α →₀ K) (f : α ↪ β) :
    (x.embDomain f).mulHeight = x.mulHeight := by
  classical
  rw [mulHeight_eq_of_support_subset _ (x.support.map f) (by simp)]
  rw [← Height.mulHeight_comp_equiv (Finset.equivMap f x.support)]
  congr 1
  ext i
  exact embDomain_apply_self f x i

@[simp]
theorem logHeight_embDomain (x : α →₀ K) (f : α ↪ β) :
    (x.embDomain f).logHeight = x.logHeight := by
  rw [logHeight_eq_log_mulHeight_support, mulHeight_embDomain,
    logHeight_eq_log_mulHeight_support]

/-- **The height of a multiplication table.** Suppose that `e` is injective on pairs of indices
in the supports of `x` and `y`, that `z (e (a, b)) = x a * y b` for such pairs, and that every
index in the support of `z` is of this form. If `x` and `y` are nonzero, then the height of `z`
is the product of the heights of `x` and `y`. This is the Segre relation
`Height.mulHeight_fun_mul_eq` for finitely supported vectors. -/
theorem mulHeight_eq_mul_of_injOn {γ : Type*} {x : α →₀ K} {y : β →₀ K} {z : γ →₀ K}
    {e : α × β → γ} (he : Set.InjOn e (x.support ×ˢ y.support : Finset (α × β)))
    (hz : ∀ a ∈ x.support, ∀ b ∈ y.support, z (e (a, b)) = x a * y b)
    (hsupp : ∀ c ∈ z.support, ∃ a ∈ x.support, ∃ b ∈ y.support, e (a, b) = c)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    z.mulHeight = x.mulHeight * y.mulHeight := by
  classical
  set s : Finset γ := (x.support ×ˢ y.support).image e
  have hs : z.support ⊆ s := fun c hc ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := hsupp c hc
    exact Finset.mem_image_of_mem e (Finset.mem_product.2 ⟨ha, hb⟩)
  -- The pairs of indices in the two supports are in bijection with `s`.
  let E : x.support × y.support ≃ s := (Equiv.Finset.prod x.support y.support).symm.trans
    ((Equiv.Set.imageOfInjOn e _ he).trans (Set.equivOfEq Finset.coe_image.symm))
  have hx' : (fun a : x.support ↦ x a) ≠ 0 := by
    obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.2 hx
    exact Function.ne_iff.2 ⟨⟨a, ha⟩, mem_support_iff.1 ha⟩
  have hy' : (fun b : y.support ↦ y b) ≠ 0 := by
    obtain ⟨b, hb⟩ := Finsupp.support_nonempty_iff.2 hy
    exact Function.ne_iff.2 ⟨⟨b, hb⟩, mem_support_iff.1 hb⟩
  have hzE : (fun c : s ↦ z c) ∘ E = fun p : x.support × y.support ↦ x p.1 * y p.2 :=
    funext fun p ↦ hz _ p.1.2 _ p.2.2
  rw [mulHeight_eq_of_support_subset z s hs, ← Height.mulHeight_comp_equiv E, hzE,
    Height.mulHeight_fun_mul_eq hx' hy', mulHeight_eq_of_support_subset x x.support subset_rfl,
    mulHeight_eq_of_support_subset y y.support subset_rfl]

/-- **The logarithmic height of a multiplication table.** Under the hypotheses of
`Finsupp.mulHeight_eq_mul_of_injOn`, the logarithmic height of `z` is the sum of the logarithmic
heights of `x` and `y`. -/
theorem logHeight_eq_add_of_injOn {γ : Type*} {x : α →₀ K} {y : β →₀ K} {z : γ →₀ K}
    {e : α × β → γ} (he : Set.InjOn e (x.support ×ˢ y.support : Finset (α × β)))
    (hz : ∀ a ∈ x.support, ∀ b ∈ y.support, z (e (a, b)) = x a * y b)
    (hsupp : ∀ c ∈ z.support, ∃ a ∈ x.support, ∃ b ∈ y.support, e (a, b) = c)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    z.logHeight = x.logHeight + y.logHeight := by
  rw [logHeight_eq_log_mulHeight_support, logHeight_eq_log_mulHeight_support,
    logHeight_eq_log_mulHeight_support, mulHeight_eq_mul_of_injOn he hz hsupp hx hy,
    Real.log_mul (mulHeight_pos x).ne' (mulHeight_pos y).ne']

end Finsupp
