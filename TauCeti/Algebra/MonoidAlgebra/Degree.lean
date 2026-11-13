/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Weight bounds on the support of an `AddMonoidAlgebra`

Given a weight function `φ : G → M` into an ordered type `M`, this file bounds `φ` from below
across the support of binary sums `f + h` and finite sums `∑ i ∈ s, F i` in `R[G]`. When
`φ : G →+ M` is an additive homomorphism into a preordered (or partially ordered) additive monoid
`M`, it further bounds `φ` from below across the support of products, powers, and perturbed powers
`(f₀ + f₁) ^ n - f₀ ^ n`.

Unlike `AddMonoidAlgebra.infDegree` in `Mathlib.Algebra.MonoidAlgebra.Degree`, which takes infima in
an `OrderTop` (where `WithTop M` is not strictly ordered under addition because `⊤ + a = ⊤`),
working directly on `coeff.support` avoids any lattice hypothesis on `M` and yields strict lower
bounds over arbitrary partially ordered additive monoids with strictly monotone addition.

## Main results

* `AddMonoidAlgebra.le_apply_of_mem_support_coeff_add`,
  `AddMonoidAlgebra.lt_apply_of_mem_support_coeff_add`,
  `AddMonoidAlgebra.le_apply_of_mem_support_coeff_sum`, and
  `AddMonoidAlgebra.lt_apply_of_mem_support_coeff_sum`: non-strict and strict lower bounds on `φ`
  over the support of binary sums and `Finset.sum`.
* `AddMonoidAlgebra.add_le_apply_of_mem_support_coeff_mul` and
  `AddMonoidAlgebra.nsmul_le_apply_of_mem_support_coeff_pow`: lower bounds on `φ` over the support
  of a product and of a power.
* `AddMonoidAlgebra.nsmul_lt_apply_of_mem_support_coeff_add_pow_sub_pow`: if `f₀` has `φ`-weight at
  least `μ` and `f₁` has `φ`-weight strictly above `μ`, then `(f₀ + f₁) ^ n - f₀ ^ n` is supported
  at `φ`-weights strictly above `n • μ`.
-/

public section

namespace AddMonoidAlgebra

section AddAndSum

variable {R G M : Type*} [Semiring R]

/-- If `f` and `h` are both supported at `φ`-weights at least `μ`, then `f + h` is supported at
`φ`-weights at least `μ`. -/
theorem le_apply_of_mem_support_coeff_add [LE M] (φ : G → M) {f h : AddMonoidAlgebra R G} {μ : M}
    (hf : ∀ g ∈ f.coeff.support, μ ≤ φ g) (hh : ∀ g ∈ h.coeff.support, μ ≤ φ g)
    {g : G} (hg : g ∈ (f + h).coeff.support) :
    μ ≤ φ g := by
  classical
  rw [coeff_add] at hg
  rcases Finset.mem_union.mp (Finsupp.support_add hg) with hg | hg
  · exact hf g hg
  · exact hh g hg

/-- If `f` and `h` are both supported at `φ`-weights strictly above `μ`, then `f + h` is supported
at `φ`-weights strictly above `μ`. -/
theorem lt_apply_of_mem_support_coeff_add [LT M] (φ : G → M) {f h : AddMonoidAlgebra R G} {μ : M}
    (hf : ∀ g ∈ f.coeff.support, μ < φ g) (hh : ∀ g ∈ h.coeff.support, μ < φ g)
    {g : G} (hg : g ∈ (f + h).coeff.support) :
    μ < φ g := by
  classical
  rw [coeff_add] at hg
  rcases Finset.mem_union.mp (Finsupp.support_add hg) with hg | hg
  · exact hf g hg
  · exact hh g hg

/-- If each `F i` (`i ∈ s`) is supported at `φ`-weights at least `μ`, then `∑ i ∈ s, F i` is
supported at `φ`-weights at least `μ`. -/
theorem le_apply_of_mem_support_coeff_sum {ι : Type*} [LE M] (φ : G → M) {s : Finset ι}
    {F : ι → AddMonoidAlgebra R G} {μ : M} (hF : ∀ i ∈ s, ∀ g ∈ (F i).coeff.support, μ ≤ φ g)
    {g : G} (hg : g ∈ (∑ i ∈ s, F i).coeff.support) :
    μ ≤ φ g := by
  have hsum_ne : ∑ i ∈ s, (F i).coeff g ≠ 0 := by
    simpa [coeff_sum, Finsupp.finsetSum_apply] using Finsupp.mem_support_iff.mp hg
  obtain ⟨i, hi, hgi_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  exact hF i hi g (Finsupp.mem_support_iff.mpr hgi_ne)

/-- If each `F i` (`i ∈ s`) is supported at `φ`-weights strictly above `μ`, then `∑ i ∈ s, F i` is
supported at `φ`-weights strictly above `μ`. -/
theorem lt_apply_of_mem_support_coeff_sum {ι : Type*} [LT M] (φ : G → M) {s : Finset ι}
    {F : ι → AddMonoidAlgebra R G} {μ : M} (hF : ∀ i ∈ s, ∀ g ∈ (F i).coeff.support, μ < φ g)
    {g : G} (hg : g ∈ (∑ i ∈ s, F i).coeff.support) :
    μ < φ g := by
  have hsum_ne : ∑ i ∈ s, (F i).coeff g ≠ 0 := by
    simpa [coeff_sum, Finsupp.finsetSum_apply] using Finsupp.mem_support_iff.mp hg
  obtain ⟨i, hi, hgi_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  exact hF i hi g (Finsupp.mem_support_iff.mpr hgi_ne)

end AddAndSum

section Monotone

variable {R G M : Type*} [Semiring R] [AddMonoid G] [AddMonoid M] [Preorder M]
  [AddLeftMono M] [AddRightMono M]

/-- If `f` is supported at `φ`-weights at least `μ` and `h` at `φ`-weights at least `ν`, then
`f * h` is supported at `φ`-weights at least `μ + ν`. -/
theorem add_le_apply_of_mem_support_coeff_mul (φ : G →+ M) {f h : AddMonoidAlgebra R G} {μ ν : M}
    (hf : ∀ g ∈ f.coeff.support, μ ≤ φ g) (hh : ∀ g ∈ h.coeff.support, ν ≤ φ g)
    {g : G} (hg : g ∈ (f * h).coeff.support) :
    μ + ν ≤ φ g := by
  classical
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_coeff_mul_subset f h hg)
  rw [map_add]
  exact add_le_add (hf a ha) (hh b hb)

/-- If `f` is supported at `φ`-weights at least `μ`, then `f ^ n` is supported at `φ`-weights at
least `n • μ`. -/
theorem nsmul_le_apply_of_mem_support_coeff_pow (φ : G →+ M) {f : AddMonoidAlgebra R G} {μ : M}
    (hf : ∀ g ∈ f.coeff.support, μ ≤ φ g) (n : ℕ) {g : G} (hg : g ∈ (f ^ n).coeff.support) :
    n • μ ≤ φ g := by
  induction n generalizing g with
  | zero =>
    rw [pow_zero] at hg
    rw [Finset.mem_singleton.mp (support_coeff_one_subset hg), zero_nsmul, map_zero]
  | succ n ih =>
    rw [pow_succ] at hg
    rw [succ_nsmul]
    exact add_le_apply_of_mem_support_coeff_mul φ (fun _ hx => ih hx) hf hg

end Monotone

section StrictMono

variable {R G M : Type*} [AddMonoid G] [AddMonoid M] [PartialOrder M]
  [AddLeftStrictMono M] [AddRightStrictMono M]

/-- If `f₀` has `φ`-weights at least `μ` and `f₁` has `φ`-weights strictly above `μ`, then every
monomial in `(f₀ + f₁) ^ n - f₀ ^ n` has `φ`-weight strictly above `n • μ`. -/
theorem nsmul_lt_apply_of_mem_support_coeff_add_pow_sub_pow [Ring R] (φ : G →+ M)
    {f₀ f₁ : AddMonoidAlgebra R G} {μ : M}
    (hf₀ : ∀ g ∈ f₀.coeff.support, μ ≤ φ g) (hf₁ : ∀ g ∈ f₁.coeff.support, μ < φ g)
    (n : ℕ) {g : G} (hg : g ∈ ((f₀ + f₁) ^ n - f₀ ^ n).coeff.support) :
    n • μ < φ g := by
  classical
  have hf : ∀ x ∈ (f₀ + f₁).coeff.support, μ ≤ φ x :=
    fun _ => le_apply_of_mem_support_coeff_add φ hf₀ fun x hx => (hf₁ x hx).le
  induction n generalizing g with
  | zero => simp at hg
  | succ n ih =>
    have := addLeftMono_of_addLeftStrictMono M
    have := addRightMono_of_addRightStrictMono M
    have hid : (f₀ + f₁) ^ (n + 1) - f₀ ^ (n + 1) =
        ((f₀ + f₁) ^ n - f₀ ^ n) * f₀ + (f₀ + f₁) ^ n * f₁ := by
      rw [pow_succ, pow_succ, mul_add, sub_mul, add_sub_right_comm]
    rw [hid] at hg
    rw [succ_nsmul]
    refine lt_apply_of_mem_support_coeff_add φ (fun x hx => ?_) (fun x hx => ?_) hg
    · obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_coeff_mul_subset _ _ hx)
      rw [map_add]
      exact add_lt_add_of_lt_of_le (ih ha) (hf₀ b hb)
    · obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_coeff_mul_subset _ _ hx)
      rw [map_add]
      exact add_lt_add_of_le_of_lt (nsmul_le_apply_of_mem_support_coeff_pow φ hf n ha) (hf₁ b hb)

end StrictMono

end AddMonoidAlgebra
