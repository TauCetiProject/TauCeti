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
public import TauCeti.Combinatorics.Additive.ImageCard

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

Two points of a finite set `S ⊆ ℤ^m` with the same image under `s ↦ ∏ α_j ^ s_j` differ by a
vector of the kernel. So if the differences of `S` lie in the box `‖s‖∞ ≤ R`, each fibre of this
map on `S`, and more generally of any homomorphism `g` whose kernel lies in that kernel, has at
most `2R + 1` points, and `#S ≤ (2R + 1) · #g(S)`.

## Main results

* `Submodule.ncard_setOf_mem_abs_le_le_of_finrank_le_one`: a rank-at-most-one subgroup of `ℤ^m`
  has at most `2R + 1` points in the box `‖s‖∞ ≤ R`.
* `LinearMap.ncard_setOf_apply_eq_zero_abs_le_le`: a map out of `ℤ^m` with image of rank at
  least `m - 1` vanishes at most at `2R + 1` points of the box `‖s‖∞ ≤ R`.
* `LinearMap.ncard_le_mul_ncard_image_of_ker_le`: a set `S ⊆ ℤ^m` whose differences lie in
  the box `‖s‖∞ ≤ R` has at most `(2R + 1) · #g(S)` elements, for every homomorphism `g` whose
  kernel lies in the kernel of such a map.
* `TauCeti.ncard_setOf_prod_zpow_eq_one_abs_le_le` and
  `TauCeti.ncard_le_mul_ncard_image_of_prod_zpow_eq_one`: the same two counts for
  `s ↦ α₁ ^ s₁ ⋯ αₘ ^ sₘ`, when `α₁, …, αₘ` generate a subgroup of rank at least `m - 1` of a
  commutative group.
* `TauCeti.ncard_nsmul_le_mul_ncard_image_of_prod_zpow_eq_one`: the second count for the
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
an additive homomorphism whose kernel lies in the kernel of `φ`. A set `S ⊆ ℤ^m` whose
differences all have coordinates of absolute value at most `R` meets each fibre of `g` in at most
`2R + 1` points, so it has at most `(2R + 1) · #g(S)` elements. -/
theorem ncard_le_mul_ncard_image_of_ker_le {C : Type*} [AddZeroClass C] (φ : (Fin m → ℤ) →ₗ[ℤ] M)
    (hφ : m ≤ finrank ℤ (range φ) + 1) (g : (Fin m → ℤ) →+ C) (hg : ∀ s, g s = 0 → φ s = 0)
    {S : Set (Fin m → ℤ)} {R : ℕ} (hR : ∀ s ∈ S, ∀ t ∈ S, ∀ i, |s i - t i| ≤ R) :
    S.ncard ≤ (g '' S).ncard * (2 * R + 1) := by
  rcases S.infinite_or_finite with hS | hS
  · simp [hS.ncard]
  have hbox : {s : Fin m → ℤ | φ s = 0 ∧ ∀ i, |s i| ≤ R}.Finite :=
    (Finite.pi (t := fun _ : Fin m ↦ Icc (-(R : ℤ)) R) fun _ ↦ finite_Icc _ _).subset
      fun s hs i _ ↦ abs_le.mp (hs.2 i)
  have hsub : (AddMonoidHom.id _ '' ((S - S) ∩ g.ker)) ⊆
      {s : Fin m → ℤ | φ s = 0 ∧ ∀ i, |s i| ≤ R} := by
    rintro _ ⟨_, ⟨⟨s, hs, t, ht, rfl⟩, hker⟩, rfl⟩
    exact ⟨hg _ hker, hR s hs t ht⟩
  calc S.ncard = (AddMonoidHom.id _ '' S).ncard := by simp
    _ ≤ (g '' S).ncard * (AddMonoidHom.id _ '' ((S - S) ∩ g.ker)).ncard :=
        (AddMonoidHom.id _).ncard_image_le_mul_ncard_image_sub_inter_ker g hS
    _ ≤ (g '' S).ncard * (2 * R + 1) :=
        Nat.mul_le_mul_left _ ((ncard_le_ncard hsub hbox).trans
          (φ.ncard_setOf_apply_eq_zero_abs_le_le hφ R))

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
`g` be an additive homomorphism out of `ℤ^m` with `α₁ ^ s₁ ⋯ αₘ ^ sₘ = 1` whenever `g s = 0`. A
set `S ⊆ ℤ^m` whose differences all have coordinates of absolute value at most `R` has at
most `(2R + 1) · #g(S)` elements. This is the subgroup obstruction's count in Waldschmidt's rank
argument, for `g` the quotient map of an obstruction subgroup. -/
theorem ncard_le_mul_ncard_image_of_prod_zpow_eq_one {C : Type*} [AddZeroClass C] (α : Fin m → G)
    (hα : m ≤ finrank ℤ (Submodule.span ℤ (range fun j ↦ Additive.ofMul (α j))) + 1)
    (g : (Fin m → ℤ) →+ C) (hg : ∀ s, g s = 0 → ∏ j, α j ^ s j = 1)
    {S : Set (Fin m → ℤ)} {R : ℕ} (hR : ∀ s ∈ S, ∀ t ∈ S, ∀ i, |s i - t i| ≤ R) :
    S.ncard ≤ (g '' S).ncard * (2 * R + 1) :=
  (Fintype.linearCombination ℤ fun j ↦ Additive.ofMul (α j)).ncard_le_mul_ncard_image_of_ker_le
    (by rwa [Fintype.range_linearCombination]) g
    (fun s hs ↦ by
      rw [Fintype.linearCombination_apply]
      simp only [← ofMul_zpow, ← ofMul_prod, hg s hs, ofMul_one]) hR

/-- Let `α₁, …, αₘ` generate a subgroup of rank at least `m - 1` of a commutative group, and let
`g` be an additive homomorphism vanishing only on exponent vectors `s` with
`α₁ ^ s₁ ⋯ αₘ ^ sₘ = 1`. If every point of a set `A ⊆ ℤ^m` has coordinates of absolute
value at most `R`, then the `k`-fold sumset `k • A` has at most `(4kR + 1) · #g(k • A)` points.
In Waldschmidt's rank argument, `A = (S - S) ∩ V` and `k = m + 1`. -/
theorem ncard_nsmul_le_mul_ncard_image_of_prod_zpow_eq_one {C : Type*} [AddZeroClass C]
    (α : Fin m → G)
    (hα : m ≤ finrank ℤ (Submodule.span ℤ (range fun j ↦ Additive.ofMul (α j))) + 1)
    (g : (Fin m → ℤ) →+ C) (hg : ∀ s, g s = 0 → ∏ j, α j ^ s j = 1)
    {A : Set (Fin m → ℤ)} {R : ℕ} (hR : ∀ a ∈ A, ∀ i, |a i| ≤ R) (k : ℕ) :
    (k • A).ncard ≤ (g '' (k • A)).ncard * (2 * (2 * k * R) + 1) := by
  have hA : A ⊆ Icc (fun _ ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ)) := fun a ha ↦
    ⟨fun i ↦ (abs_le.mp (hR a ha i)).1, fun i ↦ (abs_le.mp (hR a ha i)).2⟩
  have hbox {s : Fin m → ℤ} (hs : s ∈ k • A) (i : Fin m) : |s i| ≤ k * R := by
    have h := nsmul_Icc_subset (fun _ : Fin m ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ)) k
      (nsmul_subset_nsmul_left hA hs)
    exact abs_le.mpr (by simpa [nsmul_eq_mul] using And.intro (h.1 i) (h.2 i))
  refine ncard_le_mul_ncard_image_of_prod_zpow_eq_one α hα g hg fun s hs t ht i ↦ ?_
  calc |s i - t i| ≤ |s i| + |t i| := abs_sub _ _
    _ ≤ k * R + k * R :=
        add_le_add (hbox hs i) (hbox ht i)
    _ = ((2 * k * R : ℕ) : ℤ) := by push_cast; ring

end TauCeti
