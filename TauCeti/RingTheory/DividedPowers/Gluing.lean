/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import TauCeti.RingTheory.DividedPowers.FromGens

/-!
# Gluing divided power structures on sums of ideals

Given divided power structures `hI : DividedPowers I` and `hJ : DividedPowers J` on ideals `I` and
`J` of a commutative ring `A`, this file formalizes Stacks Project, Lemma 23.2.5 (tag `07GQ`):
there exists a divided power structure on `I ⊔ J` restricting to `hI` on `I` and `hJ` on `J` if
and only if `hI` and `hJ` agree on `I ⊓ J` in every degree, and when it exists it is unique.

The construction proceeds in three steps:
1. Define the antidiagonal convolution `DividedPowers.dpowConv hI hJ n x y`, which is the `n`-th
   coefficient of the power series product `hI.exp x * hJ.exp y` (valid over any commutative
   semiring).
2. Over a commutative ring, when `hI` and `hJ` agree on `I ⊓ J`, prove that `dpowConv hI hJ n x y`
   depends only on the sum `x + y` (`dpowConv_eq_of_add_eq`) via `DividedPowers.exp_add`.
3. Assemble the induced additive divided power candidate `DividedPowers.supAdditive hI hJ h` on
   `I ⊔ J` and upgrade it to `DividedPowers.sup hI hJ h : DividedPowers (I ⊔ J)` via the generator
   criterion `TauCeti.AdditiveDividedPowers.toDividedPowers` on `(I : Set A) ∪ (J : Set A)`.

When `I ⊓ J = I * J`, agreement on `I ⊓ J` is automatic by `DividedPowers.coincide_on_smul`,
yielding an unconditional glued divided power structure on `I ⊔ J`.

## Main definitions and results

* `DividedPowers.dpowConv`: antidiagonal convolution
  `∑ k ∈ antidiagonal n, hI.dpow k.1 x * hJ.dpow k.2 y`.
* `DividedPowers.coeff_exp_mul_exp`: `dpowConv` computes the coefficients of `hI.exp x * hJ.exp y`.
* `DividedPowers.dpowConv_eq_of_add_eq`: independence of `dpowConv` from the decomposition
  `z = x + y` when `hI` and `hJ` agree on `I ⊓ J`.
* `DividedPowers.supAdditive`: the glued additive divided power candidate on `I ⊔ J` for
  compatible `hI` and `hJ`, with evaluation `DividedPowers.supAdditive_dpow_add` and restrictions
  `DividedPowers.supAdditive_dpow_left`, `DividedPowers.supAdditive_dpow_right`.
* `DividedPowers.sup`: the glued divided power structure on `I ⊔ J` for compatible `hI` and `hJ`.
* `DividedPowers.isDPMorphism_sup_iff`: universal property of `DividedPowers.sup` with respect to
  divided power morphisms.
* `DividedPowers.eq_sup_iff`: characterization of `DividedPowers.sup` by its restrictions to `I`
  and `J`.
* `DividedPowers.exists_unique_sup_iff`: existence and uniqueness of a common extension to `I ⊔ J`
  holds if and only if `hI` and `hJ` agree on `I ⊓ J`.
* `DividedPowers.coincide_on_inf_of_inf_eq_mul` and
  `DividedPowers.exists_unique_sup_of_inf_eq_mul`: automatic compatibility and gluing when
  `I ⊓ J = I * J`.

## References

* [Stacks: Divided power algebra, Lemma 07GQ](https://stacks.math.columbia.edu/tag/07GQ).
* P. Berthelot, *Cohomologie cristalline des schémas de caractéristique $p > 0$*, Lecture Notes in
  Math. 407 (1974), I.1.6.
* Mathlib's `DividedPowers`, from the divided powers formalization of A. Chambert-Loir and
  M. I. de Frutos-Fernández.
-/

public section

open Finset Nat Ideal

namespace DividedPowers

section CommSemiring

variable {A : Type*} [CommSemiring A] {I J : Ideal A}

/-- The antidiagonal convolution of two divided power structures `hI` on `I` and `hJ` on `J`:
`dpowConv hI hJ n x y = ∑ k ∈ antidiagonal n, hI.dpow k.1 x * hJ.dpow k.2 y`. -/
def dpowConv (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x y : A) : A :=
  ∑ k ∈ antidiagonal n, hI.dpow k.1 x * hJ.dpow k.2 y

/-- The defining equation of `DividedPowers.dpowConv`. -/
theorem dpowConv_def (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x y : A) :
    hI.dpowConv hJ n x y = ∑ k ∈ antidiagonal n, hI.dpow k.1 x * hJ.dpow k.2 y := by
  rfl

/-- `dpowConv hI hJ n x y` is the `n`-th coefficient of the power series product
`hI.exp x * hJ.exp y`. -/
theorem coeff_exp_mul_exp (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x y : A) :
    PowerSeries.coeff n (hI.exp x * hJ.exp y) = hI.dpowConv hJ n x y := by
  rw [PowerSeries.coeff_mul, dpowConv_def]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [DividedPowers.exp]

/-- Exchanging the two divided power structures and arguments leaves `dpowConv` unchanged. -/
theorem dpowConv_comm (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x y : A) :
    hI.dpowConv hJ n x y = hJ.dpowConv hI n y x := by
  rw [dpowConv_def, dpowConv_def, ← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact mul_comm _ _

/-- In degree `0`, `dpowConv hI hJ 0 x y = 1` for `x ∈ I` and `y ∈ J`. -/
@[simp]
theorem dpowConv_zero (hI : DividedPowers I) (hJ : DividedPowers J)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    hI.dpowConv hJ 0 x y = 1 := by
  simp [dpowConv_def, hI.dpow_zero hx, hJ.dpow_zero hy]

/-- In degree `1`, `dpowConv hI hJ 1 x y = x + y` for `x ∈ I` and `y ∈ J`. -/
@[simp]
theorem dpowConv_one (hI : DividedPowers I) (hJ : DividedPowers J)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    hI.dpowConv hJ 1 x y = x + y := by
  rw [dpowConv_def, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp [hI.dpow_zero hx, hI.dpow_one hx, hJ.dpow_zero hy, hJ.dpow_one hy, add_comm]

/-- In degree `2`, `dpowConv hI hJ 2 x y = hI.dpow 2 x + x * y + hJ.dpow 2 y` for `x ∈ I` and
`y ∈ J`. -/
theorem dpowConv_two (hI : DividedPowers I) (hJ : DividedPowers J)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    hI.dpowConv hJ 2 x y = hI.dpow 2 x + x * y + hJ.dpow 2 y := by
  rw [dpowConv_def, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp [hI.dpow_zero hx, hI.dpow_one hx, hJ.dpow_zero hy, hJ.dpow_one hy]
  ring

/-- For `n ≠ 0`, `x ∈ I`, and `y ∈ J`, `dpowConv hI hJ n x y` belongs to `I ⊔ J`. -/
theorem dpowConv_mem (hI : DividedPowers I) (hJ : DividedPowers J)
    {n : ℕ} (hn : n ≠ 0) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    hI.dpowConv hJ n x y ∈ I ⊔ J := by
  rw [dpowConv_def]
  refine Submodule.sum_mem (I ⊔ J) fun k hk ↦ ?_
  have hk_sum : k.1 + k.2 = n := mem_antidiagonal.mp hk
  by_cases h1 : k.1 = 0
  · have h2 : k.2 ≠ 0 := by omega
    exact Ideal.mul_mem_left (I ⊔ J) _ (Ideal.mem_sup_right (hJ.dpow_mem h2 hy))
  · exact Ideal.mul_mem_right _ (I ⊔ J) (Ideal.mem_sup_left (hI.dpow_mem h1 hx))

/-- If `x ∉ I`, then `dpowConv hI hJ n x y = 0`. -/
@[simp]
theorem dpowConv_null_left (hI : DividedPowers I) (hJ : DividedPowers J)
    {n : ℕ} {x y : A} (hx : x ∉ I) :
    hI.dpowConv hJ n x y = 0 := by
  simp [dpowConv_def, hI.dpow_null hx]

/-- If `y ∉ J`, then `dpowConv hI hJ n x y = 0`. -/
@[simp]
theorem dpowConv_null_right (hI : DividedPowers I) (hJ : DividedPowers J)
    {n : ℕ} {x y : A} (hy : y ∉ J) :
    hI.dpowConv hJ n x y = 0 := by
  simp [dpowConv_def, hJ.dpow_null hy]

/-- Evaluating `dpowConv` at `0` on the left recovers `hJ.dpow`. -/
@[simp]
theorem dpowConv_zero_left (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (y : A) :
    hI.dpowConv hJ n 0 y = hJ.dpow n y := by
  rw [dpowConv_def, Finset.sum_eq_single (0, n)]
  · rw [hI.dpow_zero I.zero_mem, one_mul]
  · intro k hk hne
    have hk_sum : k.1 + k.2 = n := mem_antidiagonal.mp hk
    have h1 : k.1 ≠ 0 := by
      intro h0
      exact hne (Prod.ext h0 (by omega))
    rw [hI.dpow_eval_zero h1, zero_mul]
  · intro hnot
    exact absurd (mem_antidiagonal.mpr (zero_add n)) hnot

/-- Evaluating `dpowConv` at `0` on the right recovers `hI.dpow`. -/
@[simp]
theorem dpowConv_zero_right (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x : A) :
    hI.dpowConv hJ n x 0 = hI.dpow n x := by
  rw [dpowConv_comm, dpowConv_zero_left hJ hI n x]

/-- The convolution of `hI` with itself is `hI.dpow` of the sum. -/
theorem dpowConv_self (hI : DividedPowers I) (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    hI.dpowConv hI n x y = hI.dpow n (x + y) := by
  rw [dpowConv_def, hI.dpow_add hx hy]

/-- Scalar homogeneity of `dpowConv` under simultaneous multiplication by `a : A`. -/
theorem dpowConv_mul (hI : DividedPowers I) (hJ : DividedPowers J)
    (n : ℕ) (a : A) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    hI.dpowConv hJ n (a * x) (a * y) = a ^ n * hI.dpowConv hJ n x y := by
  rw [dpowConv_def, dpowConv_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [hI.dpow_mul hx, hJ.dpow_mul hy, ← mem_antidiagonal.mp hk, pow_add]
  ring

/-- Additivity law of `dpowConv`. -/
theorem dpowConv_add (hI : DividedPowers I) (hJ : DividedPowers J)
    (n : ℕ) {x x' y y' : A} (hx : x ∈ I) (hx' : x' ∈ I) (hy : y ∈ J) (hy' : y' ∈ J) :
    hI.dpowConv hJ n (x + x') (y + y') =
      ∑ k ∈ antidiagonal n, hI.dpowConv hJ k.1 x y * hI.dpowConv hJ k.2 x' y' := by
  rw [← coeff_exp_mul_exp, hI.exp_add hx hx', hJ.exp_add hy hy']
  have hprod :
      (hI.exp x * hI.exp x') * (hJ.exp y * hJ.exp y') =
        (hI.exp x * hJ.exp y) * (hI.exp x' * hJ.exp y') := by
    ring
  rw [hprod, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coeff_exp_mul_exp, coeff_exp_mul_exp]

/-- If `I ⊓ J = I * J`, then any two divided power structures `hI` on `I` and `hJ` on `J` agree
on `I ⊓ J` in every degree. -/
theorem coincide_on_inf_of_inf_eq_mul (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : I ⊓ J = I * J) (n : ℕ) (w : A) (hw : w ∈ I ⊓ J) :
    hI.dpow n w = hJ.dpow n w := by
  have hw' : w ∈ I • J := by rwa [smul_eq_mul, ← hIJ]
  exact hI.coincide_on_smul hJ hw'

end CommSemiring

section CommRing

variable {A : Type*} [CommRing A] {I J : Ideal A}

/-- If `hI` and `hJ` agree on `I ⊓ J`, then `dpowConv hI hJ n x y` depends only on `x + y`. -/
theorem dpowConv_eq_of_add_eq (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    {n : ℕ} {x x' y y' : A} (hx : x ∈ I) (hx' : x' ∈ I) (hy : y ∈ J) (hy' : y' ∈ J)
    (hxy : x + y = x' + y') :
    hI.dpowConv hJ n x y = hI.dpowConv hJ n x' y' := by
  let w : A := x - x'
  have hwI : w ∈ I := I.sub_mem hx hx'
  have hw_eq : w = y' - y := by
    dsimp only [w]
    exact sub_eq_sub_iff_add_eq_add.mpr (by rw [add_comm y' x', ← hxy, add_comm])
  have hwJ : w ∈ J := hw_eq ▸ J.sub_mem hy' hy
  have hw : w ∈ I ⊓ J := ⟨hwI, hwJ⟩
  have hexp_w : hI.exp w = hJ.exp w := by
    ext k
    simp [DividedPowers.exp, h k w hw]
  have hexp_eq : hI.exp x * hJ.exp y = hI.exp x' * hJ.exp y' := by
    have hx_eq : x = x' + w := (add_sub_cancel x' x).symm
    have hy'_eq : y' = w + y := by rw [hw_eq, sub_add_cancel]
    calc
      hI.exp x * hJ.exp y
          = (hI.exp x' * hI.exp w) * hJ.exp y := by rw [hx_eq, hI.exp_add hx' hwI]
      _ = hI.exp x' * (hJ.exp w * hJ.exp y) := by rw [hexp_w, mul_assoc]
      _ = hI.exp x' * hJ.exp y' := by rw [hy'_eq, hJ.exp_add hwJ hy]
  rw [← coeff_exp_mul_exp, ← coeff_exp_mul_exp, hexp_eq]

private noncomputable def supDpow (hI : DividedPowers I) (hJ : DividedPowers J)
    (n : ℕ) (z : A) : A := by
  classical
  exact if hz : z ∈ I ⊔ J then
    let x := (Submodule.mem_sup.mp hz).choose
    let y := (Submodule.mem_sup.mp hz).choose_spec.2.choose
    hI.dpowConv hJ n x y
  else 0

private lemma supDpow_add_eq (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    supDpow hI hJ n (x + y) = hI.dpowConv hJ n x y := by
  classical
  have hz : x + y ∈ I ⊔ J := Submodule.add_mem_sup hx hy
  simp only [supDpow, hz, ↓reduceDIte]
  have hspec := (Submodule.mem_sup.mp hz).choose_spec
  have hspec2 := hspec.2.choose_spec
  exact hI.dpowConv_eq_of_add_eq hJ h hspec.1 hx hspec2.1 hy hspec2.2

/-- The glued additive divided power candidate on `I ⊔ J` constructed from `hI` and `hJ`
when they agree on `I ⊓ J` in every degree. -/
noncomputable def supAdditive (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    TauCeti.AdditiveDividedPowers (I ⊔ J) where
  dpow := supDpow hI hJ
  dpow_null {n z} hz := by
    classical
    simp [supDpow, hz]
  dpow_zero {z} hz := by
    rcases Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, rfl⟩
    rw [supDpow_add_eq hI hJ h 0 hx hy, hI.dpowConv_zero hJ hx hy]
  dpow_one {z} hz := by
    rcases Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, rfl⟩
    rw [supDpow_add_eq hI hJ h 1 hx hy, hI.dpowConv_one hJ hx hy]
  dpow_mem {n z} hn hz := by
    rcases Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, rfl⟩
    rw [supDpow_add_eq hI hJ h n hx hy]
    exact hI.dpowConv_mem hJ hn hx hy
  dpow_add {n z₁ z₂} hz₁ hz₂ := by
    rcases Submodule.mem_sup.mp hz₁ with ⟨x₁, hx₁, y₁, hy₁, rfl⟩
    rcases Submodule.mem_sup.mp hz₂ with ⟨x₂, hx₂, y₂, hy₂, rfl⟩
    have hsum : (x₁ + y₁) + (x₂ + y₂) = (x₁ + x₂) + (y₁ + y₂) := by ring
    rw [hsum, supDpow_add_eq hI hJ h n (I.add_mem hx₁ hx₂) (J.add_mem hy₁ hy₂),
      hI.dpowConv_add hJ n hx₁ hx₂ hy₁ hy₂]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [supDpow_add_eq hI hJ h k.1 hx₁ hy₁, supDpow_add_eq hI hJ h k.2 hx₂ hy₂]
  dpow_mul {n a z} hz := by
    rcases Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, rfl⟩
    rw [mul_add, supDpow_add_eq hI hJ h n (I.mul_mem_left a hx) (J.mul_mem_left a hy),
      supDpow_add_eq hI hJ h n hx hy, hI.dpowConv_mul hJ n a hx hy]

private lemma supAdditive_dpow (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    (supAdditive hI hJ h).dpow = supDpow hI hJ := by
  rfl

/-- On a sum `x + y` with `x ∈ I` and `y ∈ J`, `(hI.supAdditive hJ h).dpow n (x + y)` equals
the antidiagonal convolution `hI.dpowConv hJ n x y`. -/
theorem supAdditive_dpow_add (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (hI.supAdditive hJ h).dpow n (x + y) = hI.dpowConv hJ n x y := by
  simpa only [supAdditive_dpow] using supDpow_add_eq hI hJ h n hx hy

/-- The glued additive divided power candidate `hI.supAdditive hJ h` agrees with `hI` on `I`. -/
@[simp]
theorem supAdditive_dpow_left (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.supAdditive hJ h).dpow n x = hI.dpow n x := by
  simpa only [add_zero] using
    (hI.supAdditive_dpow_add hJ h n hx J.zero_mem).trans (hI.dpowConv_zero_right hJ n x)

/-- The glued additive divided power candidate `hI.supAdditive hJ h` agrees with `hJ` on `J`. -/
@[simp]
theorem supAdditive_dpow_right (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) (n : ℕ) {y : A} (hy : y ∈ J) :
    (hI.supAdditive hJ h).dpow n y = hJ.dpow n y := by
  simpa only [zero_add] using
    (hI.supAdditive_dpow_add hJ h n I.zero_mem hy).trans (hI.dpowConv_zero_left hJ n y)

/-- Stacks Project, Lemma 23.2.5 (tag `07GQ`): given divided power structures `hI` on `I` and
`hJ` on `J` that agree on `I ⊓ J` in every degree, construct the unique divided power structure on
`I ⊔ J` extending both `hI` and `hJ`. -/
noncomputable def sup (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    DividedPowers (I ⊔ J) :=
  (supAdditive hI hJ h).toDividedPowers
    (by rw [← Ideal.span_eq I, ← Ideal.span_eq J, ← Ideal.span_union])
    (by
      rintro s (hsI | hsJ) m n
      · simp only [supAdditive_dpow_left hI hJ h _ hsI, hI.mul_dpow hsI]
      · simp only [supAdditive_dpow_right hI hJ h _ hsJ, hJ.mul_dpow hsJ])
    (by
      rintro s (hsI | hsJ) m n hn
      · rw [supAdditive_dpow_left hI hJ h n hsI,
          supAdditive_dpow_left hI hJ h m (hI.dpow_mem hn hsI),
          supAdditive_dpow_left hI hJ h (m * n) hsI, hI.dpow_comp hn hsI]
      · rw [supAdditive_dpow_right hI hJ h n hsJ,
          supAdditive_dpow_right hI hJ h m (hJ.dpow_mem hn hsJ),
          supAdditive_dpow_right hI hJ h (m * n) hsJ, hJ.dpow_comp hn hsJ])

/-- On a sum `x + y` with `x ∈ I` and `y ∈ J`, `(hI.sup hJ h).dpow n (x + y)` equals the
antidiagonal convolution `hI.dpowConv hJ n x y`. -/
theorem sup_dpow_add (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (hI.sup hJ h).dpow n (x + y) = hI.dpowConv hJ n x y := by
  rw [sup, TauCeti.AdditiveDividedPowers.toDividedPowers_dpow,
    hI.supAdditive_dpow_add hJ h n hx hy]

/-- The glued divided power structure `hI.sup hJ h` agrees with `hI` on `I`. -/
@[simp]
theorem sup_dpow_left (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.sup hJ h).dpow n x = hI.dpow n x := by
  simpa only [add_zero] using
    (hI.sup_dpow_add hJ h n hx J.zero_mem).trans (hI.dpowConv_zero_right hJ n x)

/-- The glued divided power structure `hI.sup hJ h` agrees with `hJ` on `J`. -/
@[simp]
theorem sup_dpow_right (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {y : A} (hy : y ∈ J) :
    (hI.sup hJ h).dpow n y = hJ.dpow n y := by
  simpa only [zero_add] using
    (hI.sup_dpow_add hJ h n I.zero_mem hy).trans (hI.dpowConv_zero_left hJ n y)

/-- Gluing is symmetric in the two ideals and divided power structures. -/
theorem sup_dpow_comm (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) (n : ℕ) (z : A) :
    (hI.sup hJ h).dpow n z =
      (hJ.sup hI fun m w hw ↦ (h m w ⟨hw.2, hw.1⟩).symm).dpow n z := by
  by_cases hz : z ∈ I ⊔ J
  · rcases Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, rfl⟩
    rw [hI.sup_dpow_add hJ h n hx hy, add_comm x y,
      hJ.sup_dpow_add hI _ n hy hx, hI.dpowConv_comm hJ]
  · have hz' : z ∉ J ⊔ I := by rwa [sup_comm]
    rw [(hI.sup hJ h).dpow_null hz, (hJ.sup hI _).dpow_null hz']

/-- Gluing a divided power structure with itself recovers the original operations on all of `A`. -/
@[simp]
theorem sup_dpow_self (hI : DividedPowers I)
    (h : ∀ n, ∀ w ∈ I ⊓ I, hI.dpow n w = hI.dpow n w) (n : ℕ) (z : A) :
    (hI.sup hI h).dpow n z = hI.dpow n z := by
  by_cases hz : z ∈ I
  · exact hI.sup_dpow_left hI h n hz
  · have hz' : z ∉ I ⊔ I := by simpa only [sup_idem] using hz
    rw [(hI.sup hI h).dpow_null hz', hI.dpow_null hz]

/-- Gluing `hI` with `dividedPowersBot A` recovers the original operations of `hI` on all of `A`. -/
@[simp]
theorem sup_dpow_bot (hI : DividedPowers I)
    (h : ∀ n, ∀ w ∈ I ⊓ (⊥ : Ideal A), hI.dpow n w = (dividedPowersBot A).dpow n w)
    (n : ℕ) (z : A) :
    (hI.sup (dividedPowersBot A) h).dpow n z = hI.dpow n z := by
  by_cases hz : z ∈ I
  · exact hI.sup_dpow_left (dividedPowersBot A) h n hz
  · have hz' : z ∉ I ⊔ (⊥ : Ideal A) := by simpa only [sup_bot_eq] using hz
    rw [(hI.sup (dividedPowersBot A) h).dpow_null hz', hI.dpow_null hz]

/-- The identity ring homomorphism is a divided power morphism from `(I, hI)` to
`(I ⊔ J, hI.sup hJ h)`. -/
theorem isDPMorphism_id_sup_left (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    IsDPMorphism hI (hI.sup hJ h) (RingHom.id A) where
  ideal_comp := by simp only [Ideal.map_id, le_sup_left]
  dpow_comp {n} a ha := by simp [ha]

/-- The identity ring homomorphism is a divided power morphism from `(J, hJ)` to
`(I ⊔ J, hI.sup hJ h)`. -/
theorem isDPMorphism_id_sup_right (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    IsDPMorphism hJ (hI.sup hJ h) (RingHom.id A) where
  ideal_comp := by simp only [Ideal.map_id, le_sup_right]
  dpow_comp {n} b hb := by simp [hb]

/-- Universal property of `DividedPowers.sup`: a ring homomorphism `g : A →+* C` is a divided
power morphism from `(I ⊔ J, hI.sup hJ h)` to `(K, hK)` if and only if it is a divided power
morphism from both `(I, hI)` and `(J, hJ)` to `(K, hK)`. -/
@[simp]
theorem isDPMorphism_sup_iff (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    {C : Type*} [CommSemiring C] {K : Ideal C} (hK : DividedPowers K) (g : A →+* C) :
    IsDPMorphism (hI.sup hJ h) hK g ↔ IsDPMorphism hI hK g ∧ IsDPMorphism hJ hK g := by
  constructor
  · intro hg
    exact ⟨hg.comp hK (hI.isDPMorphism_id_sup_left hJ h),
      hg.comp hK (hI.isDPMorphism_id_sup_right hJ h)⟩
  · rintro ⟨hgI, hgJ⟩
    refine IsDPMorphism.on_span (hI.sup hJ h) hK
      (by rw [← Ideal.span_eq I, ← Ideal.span_eq J, ← Ideal.span_union]) ?_ ?_
    · rintro s (hsI | hsJ)
      · exact hgI.ideal_comp (Ideal.mem_map_of_mem g hsI)
      · exact hgJ.ideal_comp (Ideal.mem_map_of_mem g hsJ)
    · rintro n s (hsI | hsJ)
      · rw [hI.sup_dpow_left hJ h n hsI, hgI.map_dpow hsI]
      · rw [hI.sup_dpow_right hJ h n hsJ, hgJ.map_dpow hsJ]

/-- A divided power structure `θ` on `I ⊔ J` equals `hI.sup hJ h` if and only if it restricts to
`hI` on `I` and to `hJ` on `J`. -/
theorem eq_sup_iff (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    {θ : DividedPowers (I ⊔ J)} :
    θ = hI.sup hJ h ↔
      (∀ n, ∀ x ∈ I, θ.dpow n x = hI.dpow n x) ∧ (∀ n, ∀ y ∈ J, θ.dpow n y = hJ.dpow n y) := by
  constructor
  · rintro rfl
    exact ⟨fun n _ hx ↦ hI.sup_dpow_left hJ h n hx, fun n _ hy ↦ hI.sup_dpow_right hJ h n hy⟩
  · rintro ⟨hθI, hθJ⟩
    refine (hI.sup hJ h).dpow_eq_from_gens θ
      (by rw [← Ideal.span_eq I, ← Ideal.span_eq J, ← Ideal.span_union]) ?_
    rintro n s (hsI | hsJ)
    · rw [hI.sup_dpow_left hJ h n hsI, hθI n s hsI]
    · rw [hI.sup_dpow_right hJ h n hsJ, hθJ n s hsJ]

/-- Stacks Project, Lemma 23.2.5 (tag `07GQ`): there exists a unique divided power structure on
`I ⊔ J` restricting to `hI` on `I` and to `hJ` on `J` if and only if `hI` and `hJ` agree on
`I ⊓ J` in every degree. -/
theorem exists_unique_sup_iff (hI : DividedPowers I) (hJ : DividedPowers J) :
    (∃! θ : DividedPowers (I ⊔ J),
      (∀ n, ∀ x ∈ I, θ.dpow n x = hI.dpow n x) ∧ (∀ n, ∀ y ∈ J, θ.dpow n y = hJ.dpow n y)) ↔
      ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w := by
  constructor
  · rintro ⟨θ, ⟨hθI, hθJ⟩, _⟩ n w ⟨hwI, hwJ⟩
    rw [← hθI n w hwI, hθJ n w hwJ]
  · intro h
    refine ⟨hI.sup hJ h, (hI.eq_sup_iff hJ h).mp rfl, fun θ hθ ↦ (hI.eq_sup_iff hJ h).mpr hθ⟩

/-- When `I ⊓ J = I * J`, there is a unique divided power structure on `I ⊔ J` restricting to `hI`
on `I` and to `hJ` on `J`. -/
theorem exists_unique_sup_of_inf_eq_mul (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : I ⊓ J = I * J) :
    ∃! θ : DividedPowers (I ⊔ J),
      (∀ n, ∀ x ∈ I, θ.dpow n x = hI.dpow n x) ∧ (∀ n, ∀ y ∈ J, θ.dpow n y = hJ.dpow n y) :=
  (hI.exists_unique_sup_iff hJ).mpr (hI.coincide_on_inf_of_inf_eq_mul hJ hIJ)

end CommRing

end DividedPowers
