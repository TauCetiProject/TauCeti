/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Order.Group.Pointwise.Interval

/-!
# Points of a rank-one subgroup of `ℤ^m` in a box

A subgroup `H ≤ ℤ^m` of rank at most one is contained in `ℤ h` for a single vector `h`. A nonzero
multiple `k h` with all coordinates of absolute value at most `R` has `|k| ≤ R`, since some
coordinate of `h` has absolute value at least one. So `H` has at most `2R + 1` points in the box
`‖s‖∞ ≤ R`.

By rank-nullity, a `ℤ`-linear map `φ` out of `ℤ^m` whose image has rank at least `m - 1` has a
kernel of rank at most one. For `φ s = ∏ α_j ^ s_j` into the multiplicative group of a field,
viewed additively, the rank of the image is the multiplicative rank of `α₁, …, α_m`. So when the
`α_j` generate a group of rank at least `m - 1`, at most `2R + 1` exponent vectors in the box
`‖s‖∞ ≤ R` satisfy `∏ α_j ^ s_j = 1`. This is the count by which the multiplicative rank enters
the subgroup obstruction of Waldschmidt's rank argument (Proposition 9.16).

Two points of a set `S ⊆ ℤ^m` with the same image under `s ↦ ∏ α_j ^ s_j` differ by a vector of
the kernel, a multiple `k h` of a single vector `h`. So if the differences of `S` lie in the box
`‖s‖∞ ≤ R`, the points of a fibre of this map on `S`, and more generally of any map `g` whose
fibres on `S` lie in its fibres, have distinct coordinates within `R` of each other in a direction
where `h` does not vanish. Each fibre therefore has at most `R + 1` points, and
`#S ≤ (R + 1) · #g(S)`. Comparing differences rather than points saves a factor `2` over the box
count `2R + 1`, which the subgroup obstruction with trivial torus part needs.

## Main results

* `Submodule.ncard_setOf_mem_abs_le_le_of_finrank_le_one`: a rank-at-most-one subgroup of `ℤ^m`
  has at most `2R + 1` points in the box `‖s‖∞ ≤ R`.
* `LinearMap.ncard_setOf_apply_eq_zero_abs_le_le`: a map out of `ℤ^m` with image of rank at
  least `m - 1` vanishes at most at `2R + 1` points of the box `‖s‖∞ ≤ R`.
* `LinearMap.ncard_le_ncard_image_mul_add_one`: a set `S ⊆ ℤ^m` whose differences lie in
  the box `‖s‖∞ ≤ R` has at most `(R + 1) · #g(S)` elements, for every map `g` whose fibres on
  `S` lie in the fibres of such a map.
* `TauCeti.ncard_setOf_prod_zpow_eq_one_abs_le_le` and
  `TauCeti.ncard_le_ncard_image_mul_add_one`: the same two counts for
  `s ↦ α₁ ^ s₁ ⋯ αₘ ^ sₘ`, when `α₁, …, αₘ` generate a subgroup of rank at least `m - 1` of a
  commutative group.
* `TauCeti.ncard_nsmul_le_ncard_image_mul_add_one`: the second count for the
  `k`-fold sumset `k • A` of a set `A` in the box `‖s‖∞ ≤ R`, the form in which it applies
  to the columns `((S - S) ∩ V)[m + 1]` of Waldschmidt's rank argument.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §9.2.3, Proposition 9.16.
-/

public section

open Module Set
open scoped Pointwise

namespace Submodule

/-- A subgroup of `ℤ^m` of rank at most one has at most `2R + 1` points whose coordinates all
have absolute value at most `R`. -/
theorem ncard_setOf_mem_abs_le_le_of_finrank_le_one {m : ℕ} {H : Submodule ℤ (Fin m → ℤ)}
    (hH : finrank ℤ H ≤ 1) (R : ℕ) :
    {s : Fin m → ℤ | s ∈ H ∧ ∀ i, |s i| ≤ R}.ncard ≤ 2 * R + 1 := by
  obtain ⟨h, hh⟩ := finrank_le_one_iff.mp hH
  have hsub : {s : Fin m → ℤ | s ∈ H ∧ ∀ i, |s i| ≤ R} ⊆
      (fun k : ℤ ↦ k • (h : Fin m → ℤ)) '' Icc (-(R : ℤ)) R := by
    rintro s ⟨hs, hbox⟩
    obtain ⟨k, hk⟩ := hh ⟨s, hs⟩
    have hks : k • (h : Fin m → ℤ) = s := congrArg Subtype.val hk
    by_cases h0 : (h : Fin m → ℤ) = 0
    · exact ⟨0, by simp, by simp [← hks, h0]⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h0
    refine ⟨k, abs_le.mp ?_, hks⟩
    have := hbox i
    rw [← hks, Pi.smul_apply, smul_eq_mul, abs_mul] at this
    nlinarith [Int.one_le_abs hi, abs_nonneg k]
  calc _ ≤ ((fun k : ℤ ↦ k • (h : Fin m → ℤ)) '' Icc (-(R : ℤ)) R).ncard :=
        ncard_le_ncard hsub ((finite_Icc _ _).image _)
    _ ≤ (Icc (-(R : ℤ)) R).ncard := ncard_image_le (finite_Icc _ _)
    _ = 2 * R + 1 := by
        rw [ncard_eq_toFinset_card', toFinset_Icc, Int.card_Icc]
        omega

end Submodule

namespace LinearMap

variable {m : ℕ} {M : Type*} [AddCommGroup M]

/-- A `ℤ`-linear map out of `ℤ^m` whose image has rank at least `m - 1` vanishes at no more than
`2R + 1` points whose coordinates all have absolute value at most `R`: by rank-nullity, its kernel
has rank at most one. -/
theorem ncard_setOf_apply_eq_zero_abs_le_le (φ : (Fin m → ℤ) →ₗ[ℤ] M)
    (hφ : m ≤ finrank ℤ (range φ) + 1) (R : ℕ) :
    {s : Fin m → ℤ | φ s = 0 ∧ ∀ i, |s i| ≤ R}.ncard ≤ 2 * R + 1 := by
  have h := φ.finrank_range_add_finrank_ker
  rw [finrank_fin_fun] at h
  exact Submodule.ncard_setOf_mem_abs_le_le_of_finrank_le_one (H := ker φ) (by omega) R

/-- Let `φ` be a `ℤ`-linear map out of `ℤ^m` whose image has rank at least `m - 1`, and let `g` be
a map such that any two points of a set `S ⊆ ℤ^m` with the same image under `g` have the same image
under `φ`. If the differences of `S` all have coordinates of absolute value at most `R`, each fibre
of `g` on `S` has at most `R + 1` points, so `#S ≤ (R + 1) · #g(S)`: the kernel of `φ` lies on a
line `ℤ h`, two points of a fibre differ by a multiple `k h`, and the coordinates of the points of a
fibre in a direction where `h` does not vanish are distinct integers within `R` of each other. -/
theorem ncard_le_ncard_image_mul_add_one (φ : (Fin m → ℤ) →ₗ[ℤ] M)
    (hφ : m ≤ finrank ℤ (range φ) + 1) {C : Type*} (g : (Fin m → ℤ) → C) {S : Set (Fin m → ℤ)}
    {R : ℕ} (hg : ∀ s ∈ S, ∀ t ∈ S, g s = g t → φ s = φ t)
    (hR : ∀ s ∈ S, ∀ t ∈ S, ∀ i, |s i - t i| ≤ R) :
    S.ncard ≤ (g '' S).ncard * (R + 1) := by
  rcases S.infinite_or_finite with hS | hS
  · simp [hS.ncard]
  -- The kernel of `φ` has rank at most one, so it lies on a line `ℤ h`.
  have hker : finrank ℤ (ker φ) ≤ 1 := by
    have h := φ.finrank_range_add_finrank_ker
    rw [finrank_fin_fun] at h
    omega
  obtain ⟨h, hh⟩ := finrank_le_one_iff.mp hker
  have hline (s : Fin m → ℤ) (hs : s ∈ S) (t : Fin m → ℤ) (ht : t ∈ S) (hst : g s = g t) :
      ∃ k : ℤ, s - t = k • (h : Fin m → ℤ) := by
    obtain ⟨k, hk⟩ := hh ⟨s - t, by rw [mem_ker, map_sub, hg s hs t ht hst, sub_self]⟩
    exact ⟨k, (congrArg Subtype.val hk).symm⟩
  by_cases h0 : (h : Fin m → ℤ) = 0
  · -- The kernel of `φ` is trivial, so `g` is injective on `S`.
    have hinj : InjOn g S := fun s hs t ht hst ↦ by
      obtain ⟨k, hk⟩ := hline s hs t ht hst
      rwa [h0, smul_zero, sub_eq_zero] at hk
    rw [hinj.ncard_image]
    exact Nat.le_mul_of_pos_right _ R.succ_pos
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h0
  -- On `S`, the point `s` is determined by `g s` and by `s i` modulo `R + 1`.
  have hinj : InjOn (fun s ↦ (g s, s i % ((R : ℤ) + 1))) S := by
    intro s hs t ht hst
    obtain ⟨k, hk⟩ := hline s hs t ht (congrArg Prod.fst hst)
    have hsub : s i - t i = 0 := Int.eq_zero_of_abs_lt_dvd
      (Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
        (congrArg Prod.snd hst))) (by have := hR s hs t ht i; omega)
    have hki : k * (h : Fin m → ℤ) i = 0 := by simpa [hsub] using (congrFun hk i).symm
    rw [(mul_eq_zero.mp hki).resolve_right hi, zero_smul, sub_eq_zero] at hk
    exact hk
  have himage : (fun s ↦ (g s, s i % ((R : ℤ) + 1))) '' S ⊆ (g '' S) ×ˢ Ico 0 ((R : ℤ) + 1) :=
    image_subset_iff.mpr fun s hs ↦ ⟨mem_image_of_mem g hs,
      Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  calc S.ncard = ((fun s ↦ (g s, s i % ((R : ℤ) + 1))) '' S).ncard := hinj.ncard_image.symm
    _ ≤ ((g '' S) ×ˢ Ico 0 ((R : ℤ) + 1)).ncard :=
        ncard_le_ncard himage ((hS.image g).prod (finite_Ico _ _))
    _ = (g '' S).ncard * (R + 1) := by
        rw [ncard_prod, ← Finset.coe_Ico, ncard_coe_finset, Int.card_Ico]
        congr 1

end LinearMap

namespace TauCeti

variable {m : ℕ} {G : Type*} [CommGroup G]

/-- If `α₁, …, αₘ` generate a subgroup of rank at least `m - 1` of a commutative group, then at
most `2R + 1` exponent vectors `s` with all coordinates of absolute value at most `R` satisfy
`α₁ ^ s₁ ⋯ αₘ ^ sₘ = 1`. -/
theorem ncard_setOf_prod_zpow_eq_one_abs_le_le (α : Fin m → G)
    (hα : m ≤ finrank ℤ (Submodule.span ℤ (range fun j ↦ Additive.ofMul (α j))) + 1) (R : ℕ) :
    {s : Fin m → ℤ | ∏ j, α j ^ s j = 1 ∧ ∀ i, |s i| ≤ R}.ncard ≤ 2 * R + 1 := by
  have h := LinearMap.ncard_setOf_apply_eq_zero_abs_le_le
    (Fintype.linearCombination ℤ fun j ↦ Additive.ofMul (α j))
    (by rwa [Fintype.range_linearCombination]) R
  simpa only [Fintype.linearCombination_apply, ← ofMul_zpow, ← ofMul_prod, ofMul_eq_zero]
    using h

/-- Let `α₁, …, αₘ` generate a subgroup of rank at least `m - 1` of a commutative group, and let
`g` be a map such that any two points of a set `S ⊆ ℤ^m` with the same image under `g` have the
same image under `s ↦ α₁ ^ s₁ ⋯ αₘ ^ sₘ`. If the differences of `S` all have coordinates of
absolute value at most `R`, then `S` has at most `(R + 1) · #g(S)` elements. This is the subgroup
obstruction's count in Waldschmidt's rank argument, for `g` the quotient map of an obstruction
subgroup with trivial torus part. -/
theorem ncard_le_ncard_image_mul_add_one {C : Type*} (α : Fin m → G)
    (hα : m ≤ finrank ℤ (Submodule.span ℤ (range fun j ↦ Additive.ofMul (α j))) + 1)
    (g : (Fin m → ℤ) → C) {S : Set (Fin m → ℤ)} {R : ℕ}
    (hg : ∀ s ∈ S, ∀ t ∈ S, g s = g t → ∏ j, α j ^ s j = ∏ j, α j ^ t j)
    (hR : ∀ s ∈ S, ∀ t ∈ S, ∀ i, |s i - t i| ≤ R) :
    S.ncard ≤ (g '' S).ncard * (R + 1) :=
  (Fintype.linearCombination ℤ fun j ↦ Additive.ofMul (α j)).ncard_le_ncard_image_mul_add_one
    (by rwa [Fintype.range_linearCombination]) g
    (fun s hs t ht hst ↦ by
      simp only [Fintype.linearCombination_apply, ← ofMul_zpow, ← ofMul_prod, hg s hs t ht hst])
    hR

/-- Let `α₁, …, αₘ` generate a subgroup of rank at least `m - 1` of a commutative group, and let
`g` be a map such that any two points of the `k`-fold sumset `k • A` with the same image under `g`
have the same image under `s ↦ α₁ ^ s₁ ⋯ αₘ ^ sₘ`. If every point of `A ⊆ ℤ^m` has coordinates of
absolute value at most `R`, then `k • A` has at most `(2kR + 1) · #g(k • A)` points.
In Waldschmidt's rank argument, `A = (S - S) ∩ V` and `k = m + 1`. -/
theorem ncard_nsmul_le_ncard_image_mul_add_one {C : Type*} (α : Fin m → G)
    (hα : m ≤ finrank ℤ (Submodule.span ℤ (range fun j ↦ Additive.ofMul (α j))) + 1)
    (g : (Fin m → ℤ) → C) {A : Set (Fin m → ℤ)} {k : ℕ}
    (hg : ∀ s ∈ k • A, ∀ t ∈ k • A, g s = g t → ∏ j, α j ^ s j = ∏ j, α j ^ t j)
    {R : ℕ} (hR : ∀ a ∈ A, ∀ i, |a i| ≤ R) :
    (k • A).ncard ≤ (g '' (k • A)).ncard * (2 * k * R + 1) := by
  have hA : A ⊆ Icc (fun _ ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ)) := fun a ha ↦
    ⟨fun i ↦ (abs_le.mp (hR a ha i)).1, fun i ↦ (abs_le.mp (hR a ha i)).2⟩
  have hbox {s : Fin m → ℤ} (hs : s ∈ k • A) (i : Fin m) : |s i| ≤ k * R := by
    have h := nsmul_Icc_subset (fun _ : Fin m ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ)) k
      (nsmul_subset_nsmul_left hA hs)
    exact abs_le.mpr (by simpa [nsmul_eq_mul] using And.intro (h.1 i) (h.2 i))
  refine ncard_le_ncard_image_mul_add_one α hα g hg fun s hs t ht i ↦ ?_
  calc |s i - t i| ≤ |s i| + |t i| := abs_sub _ _
    _ ≤ k * R + k * R :=
        add_le_add (hbox hs i) (hbox ht i)
    _ = ((2 * k * R : ℕ) : ℤ) := by push_cast; ring

end TauCeti
