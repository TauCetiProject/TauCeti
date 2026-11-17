/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Analysis.Convex.Hull
public import TauCeti.Analysis.Normed.Lp.LeftTranslation
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Analysis.Convex.Combination
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Finitely supported probability vectors in `ℓ¹`

For a type `α`, `lp.stdSimplex α` is the set of finitely supported probability vectors in
`ℓ¹(α) = lp (fun _ : α ↦ ℝ) 1`: the nonnegative real sequences with finite support and sum one.
It is the convex hull of the unit vectors `δ_a = lp.single 1 a 1`, as for Mathlib's finite
`stdSimplex` (`convexHull_basis_eq_stdSimplex`). It is preserved by reindexing along an
equivalence of index types, in particular by left translation `L_g u = u (g⁻¹ • ·)` for an action
of a group on `α`.

For a discrete group `G`, these vectors are the finitely supported probability densities of
Reiter's condition, `∑_{g ∈ K} ‖L_g u - u‖ < ε`. The description as a convex hull is what lets a
Hahn–Banach separation argument in `ℓ¹(G)` produce such a density from an invariant mean.

## Main definitions

* `lp.stdSimplex α`: the finitely supported probability vectors in `ℓ¹(α)`.

## Main results

* `lp.convexHull_range_single_eq_stdSimplex`: `lp.stdSimplex α` is the convex hull of the unit
  vectors.
* `lp.norm_eq_one_of_mem_stdSimplex`: its elements have `ℓ¹` norm one.
* `lp.convex_stdSimplex`: it is convex.
* `lp.lpCongrLeft_mem_stdSimplex_iff`, `lp.leftTranslation_mem_stdSimplex_iff`: it is preserved
  by reindexing, and in particular by left translation.
-/

public section

noncomputable section

open Function Set

namespace lp

variable {α : Type*}

variable (α) in
/-- The finitely supported probability vectors in `ℓ¹(α)`: nonnegative real sequences with finite
support and sum one. This is the convex hull of the unit vectors
(`lp.convexHull_range_single_eq_stdSimplex`). -/
def stdSimplex : Set (lp (fun _ : α ↦ ℝ) 1) :=
  {u | (∀ a, 0 ≤ u a) ∧ (⇑u).HasFiniteSupport ∧ ∑' a, u a = 1}

theorem mem_stdSimplex_iff {u : lp (fun _ : α ↦ ℝ) 1} :
    u ∈ stdSimplex α ↔ (∀ a, 0 ≤ u a) ∧ (⇑u).HasFiniteSupport ∧ ∑' a, u a = 1 :=
  Iff.rfl

/-- The unit vector `δ_a` is a finitely supported probability vector. -/
theorem single_mem_stdSimplex [DecidableEq α] (a : α) :
    lp.single 1 a (1 : ℝ) ∈ stdSimplex α := by
  refine ⟨fun b ↦ ?_, ?_, ?_⟩
  · rw [lp.single_apply, Pi.single_apply]
    split_ifs <;> norm_num
  · rw [lp.coeFn_single]
    exact (finite_singleton a).subset (Pi.support_single_subset)
  · rw [lp.coeFn_single, tsum_pi_single]

/-- A finitely supported probability vector has `ℓ¹` norm one. -/
theorem norm_eq_one_of_mem_stdSimplex {u : lp (fun _ : α ↦ ℝ) 1} (hu : u ∈ stdSimplex α) :
    ‖u‖ = 1 := by
  rw [← (hasSum_norm_one u).tsum_eq, ← hu.2.2]
  exact tsum_congr fun a ↦ Real.norm_of_nonneg (hu.1 a)

/-- The finitely supported probability vectors form a convex set. -/
theorem convex_stdSimplex : Convex ℝ (stdSimplex α) := by
  rintro u ⟨hu0, hufin, hu1⟩ v ⟨hv0, hvfin, hv1⟩ a b ha hb hab
  have hcoe : ⇑(a • u + b • v) = a • ⇑u + b • ⇑v := by
    rw [lp.coeFn_add, lp.coeFn_smul, lp.coeFn_smul]
  have hau : (a • ⇑u).HasFiniteSupport := hufin.subset (support_const_smul_subset a _)
  have hbv : (b • ⇑v).HasFiniteSupport := hvfin.subset (support_const_smul_subset b _)
  refine ⟨fun x ↦ ?_, ?_, ?_⟩
  · rw [hcoe]
    exact add_nonneg (mul_nonneg ha (hu0 x)) (mul_nonneg hb (hv0 x))
  · rw [hcoe]
    exact hau.add hbv
  · rw [hcoe, Pi.add_def, Summable.tsum_add (summable_of_hasFiniteSupport hau)
      (summable_of_hasFiniteSupport hbv)]
    simp [tsum_mul_left, hu1, hv1, hab]

/-- The finitely supported probability vectors in `ℓ¹(α)` are the convex combinations of the unit
vectors `δ_a`. -/
theorem convexHull_range_single_eq_stdSimplex [DecidableEq α] :
    convexHull ℝ (range fun a : α ↦ lp.single 1 a (1 : ℝ)) = stdSimplex α := by
  refine Subset.antisymm (convexHull_min (range_subset_iff.2 single_mem_stdSimplex)
    convex_stdSimplex) ?_
  rintro u ⟨hu0, hufin, hu1⟩
  have hufin' : (support u).Finite := hufin
  set s := hufin'.toFinset
  have hu : u = ∑ a ∈ s, u a • lp.single 1 a (1 : ℝ) := by
    ext x
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.coeFn_smul, lp.coeFn_single, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, s, Finite.mem_toFinset, mem_support]
    split_ifs with hx
    · rfl
    · exact not_not.1 hx
  have hs : ∑ a ∈ s, u a = 1 := by
    rw [← hu1, tsum_eq_sum fun x hx ↦ ?_]
    simpa [s] using hx
  rw [hu]
  exact (convex_convexHull ℝ _).sum_mem (fun a _ ↦ hu0 a) hs
    fun a _ ↦ subset_convexHull ℝ _ ⟨a, rfl⟩

/-- Reindexing along an equivalence takes finitely supported probability vectors to finitely
supported probability vectors. -/
theorem lpCongrLeft_mem_stdSimplex {β : Type*} (e : α ≃ β) {u : lp (fun _ : α ↦ ℝ) 1}
    (hu : u ∈ stdSimplex α) : LinearIsometryEquiv.lpCongrLeft 1 ℝ ℝ e u ∈ stdSimplex β := by
  obtain ⟨hu0, hufin, hu1⟩ := hu
  have hcoe : ⇑(LinearIsometryEquiv.lpCongrLeft 1 ℝ ℝ e u) = ⇑u ∘ e.symm :=
    funext fun b ↦ LinearIsometryEquiv.lpCongrLeft_apply e u b
  refine ⟨fun b ↦ by simp [hu0], ?_, ?_⟩
  · rw [hcoe]
    exact hufin.comp_of_injective e.symm.injective
  · simpa [hu1] using e.symm.tsum_eq u

/-- Reindexing along an equivalence preserves the finitely supported probability vectors. -/
@[simp]
theorem lpCongrLeft_mem_stdSimplex_iff {β : Type*} (e : α ≃ β) {u : lp (fun _ : α ↦ ℝ) 1} :
    LinearIsometryEquiv.lpCongrLeft 1 ℝ ℝ e u ∈ stdSimplex β ↔ u ∈ stdSimplex α := by
  refine ⟨fun h ↦ ?_, lpCongrLeft_mem_stdSimplex e⟩
  simpa [← LinearIsometryEquiv.lpCongrLeft_symm] using lpCongrLeft_mem_stdSimplex e.symm h

/-- Left translation preserves the finitely supported probability vectors. -/
@[simp]
theorem leftTranslation_mem_stdSimplex_iff {G : Type*} [Group G] [MulAction G α] (g : G)
    {u : lp (fun _ : α ↦ ℝ) 1} : leftTranslation 1 ℝ g u ∈ stdSimplex α ↔ u ∈ stdSimplex α := by
  rw [leftTranslation_def, lpCongrLeft_mem_stdSimplex_iff]

end lp
