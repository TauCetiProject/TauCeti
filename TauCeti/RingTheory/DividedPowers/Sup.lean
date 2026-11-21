/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import TauCeti.RingTheory.DividedPowers.Generators

/-!
# Gluing divided powers on a sum of ideals

Given divided power structures `hI : DividedPowers I` and `hJ : DividedPowers J` on ideals `I`
and `J` of a commutative ring `A`, there exists a divided power structure on the sum ideal `I ⊔ J`
restricting to `hI` on `I` and to `hJ` on `J` if and only if `hI` and `hJ` agree on the
intersection `I ⊓ J` in every degree. When this compatibility holds, the glued structure
`DividedPowers.sup hI hJ hIJ` is unique and is given on `x + y` (`x ∈ I`, `y ∈ J`) by the
antidiagonal convolution `DividedPowers.convolution hI hJ n x y`.

In particular, whenever `I ⊓ J = I * J` (as for the extended base ideal and augmentation ideal of
a divided power algebra), `DividedPowers.coincide_on_smul` automatically supplies agreement on
`I ⊓ J`, yielding `DividedPowers.supOfInfEqMul`.

## Main definitions

* `DividedPowers.convolution`: the antidiagonal convolution
  `∑ k ∈ antidiagonal n, hI.dpow k.1 x * hJ.dpow k.2 y`.
* `DividedPowers.supCandidate`: the `TauCeti.AdditivePowers (I ⊔ J)` candidate defined by
  convolution when `hI` and `hJ` agree on `I ⊓ J`.
* `DividedPowers.sup`: the unique glued `DividedPowers (I ⊔ J)` structure when `hI` and `hJ` agree
  on `I ⊓ J`.
* `DividedPowers.supOfInfEqMul`: the unique glued `DividedPowers (I ⊔ J)` structure when
  `I ⊓ J = I * J`.

## Main results

* `DividedPowers.convolution_eq_coeff_exp_mul`: `convolution` computes the coefficients of
  `hI.exp x * hJ.exp y`.
* `DividedPowers.convolution_eq_of_add_eq`: independence of the decomposition `x + y = x' + y'`
  when `hI` and `hJ` agree on `I ⊓ J`.
* `DividedPowers.isDPMorphism_sup_iff`: universal property of `DividedPowers.sup` for
  `DividedPowers.IsDPMorphism`.
* `DividedPowers.eq_sup_iff` and `DividedPowers.exists_sup_iff`: existence and uniqueness of the
  glued divided power structure on `I ⊔ J`.

## References

* [Stacks: Divided Power Algebra, Lemma 07GQ](https://stacks.math.columbia.edu/tag/07GQ).
* P. Berthelot, *Cohomologie cristalline des schémas de caractéristique $p > 0$*,
  Lecture Notes in Math. 407, Springer (1974), I §1.6.
* Mathlib's `DividedPowers`, from the formalization of A. Chambert-Loir and
  M. I. de Frutos-Fernández.
-/

public section

open Finset

namespace DividedPowers

section CommSemiring

variable {A : Type*} [CommSemiring A] {I J : Ideal A}

/-- The antidiagonal convolution `∑_{i + j = n} hI.dpow i x * hJ.dpow j y` of two divided power
structures. -/
def convolution (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x y : A) : A :=
  ∑ k ∈ antidiagonal n, hI.dpow k.1 x * hJ.dpow k.2 y

/-- The defining formula for `DividedPowers.convolution`. -/
theorem convolution_def (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x y : A) :
    hI.convolution hJ n x y = ∑ k ∈ antidiagonal n, hI.dpow k.1 x * hJ.dpow k.2 y := (rfl)

/-- The `n`-th convolution equals the `n`-th coefficient of the product of exponential power
series `hI.exp x * hJ.exp y`. -/
theorem convolution_eq_coeff_exp_mul (hI : DividedPowers I) (hJ : DividedPowers J)
    (n : ℕ) (x y : A) :
    hI.convolution hJ n x y = PowerSeries.coeff n (hI.exp x * hJ.exp y) := by
  rw [convolution_def, PowerSeries.coeff_mul]
  exact sum_congr rfl fun k _ ↦ by simp [DividedPowers.exp]

/-- Exchanging the two divided power structures and elements leaves `convolution` unchanged. -/
theorem convolution_comm (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x y : A) :
    hI.convolution hJ n x y = hJ.convolution hI n y x := by
  rw [convolution_eq_coeff_exp_mul, convolution_eq_coeff_exp_mul, mul_comm]

/-- In degree `0`, the convolution of elements of `I` and `J` equals `1`. -/
@[simp]
theorem convolution_zero (hI : DividedPowers I) (hJ : DividedPowers J)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    hI.convolution hJ 0 x y = 1 := by
  simp [convolution_def, hI.dpow_zero hx, hJ.dpow_zero hy]

/-- In degree `1`, the convolution of `x ∈ I` and `y ∈ J` equals `x + y`. -/
@[simp]
theorem convolution_one (hI : DividedPowers I) (hJ : DividedPowers J)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    hI.convolution hJ 1 x y = x + y := by
  rw [convolution_def, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ, sum_range_one]
  simp [hI.dpow_zero hx, hI.dpow_one hx, hJ.dpow_zero hy, hJ.dpow_one hy, add_comm]

/-- In degree `2`, the convolution of `x ∈ I` and `y ∈ J` is `hI.dpow 2 x + x * y + hJ.dpow 2 y`. -/
theorem convolution_two (hI : DividedPowers I) (hJ : DividedPowers J)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    hI.convolution hJ 2 x y = hI.dpow 2 x + x * y + hJ.dpow 2 y := by
  rw [convolution_def, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ, sum_range_succ,
    sum_range_one]
  simp only [Nat.sub_zero, Nat.reduceSub, Nat.sub_self, hI.dpow_zero hx, hI.dpow_one hx,
    hJ.dpow_zero hy, hJ.dpow_one hy, one_mul, mul_one]
  ring

/-- In positive degree, the convolution of any two elements lies in `I ⊔ J`. -/
theorem convolution_mem (hI : DividedPowers I) (hJ : DividedPowers J)
    {n : ℕ} (hn : n ≠ 0) (x y : A) :
    hI.convolution hJ n x y ∈ I ⊔ J := by
  by_cases hx : x ∈ I
  · by_cases hy : y ∈ J
    · rw [convolution_def]
      refine Submodule.sum_mem _ fun ⟨i, j⟩ hk ↦ ?_
      have hij : i + j = n := mem_antidiagonal.mp hk
      by_cases hi : i = 0
      · exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (hJ.dpow_mem (by omega) hy))
      · exact Ideal.mul_mem_right _ _ (Ideal.mem_sup_left (hI.dpow_mem hi hx))
    · rw [convolution_def, sum_eq_zero fun k _ ↦ by rw [hJ.dpow_null hy, mul_zero]]
      exact Submodule.zero_mem _
  · rw [convolution_def, sum_eq_zero fun k _ ↦ by rw [hI.dpow_null hx, zero_mul]]
    exact Submodule.zero_mem _

/-- The convolution satisfies the divided-power addition law in pairs of elements from `I × J`. -/
theorem convolution_add (hI : DividedPowers I) (hJ : DividedPowers J)
    {n : ℕ} {x x' y y' : A} (hx : x ∈ I) (hx' : x' ∈ I) (hy : y ∈ J) (hy' : y' ∈ J) :
    hI.convolution hJ n (x + x') (y + y') =
      ∑ k ∈ antidiagonal n, hI.convolution hJ k.1 x y * hI.convolution hJ k.2 x' y' := by
  rw [convolution_eq_coeff_exp_mul, hI.exp_add hx hx', hJ.exp_add hy hy', mul_mul_mul_comm,
    PowerSeries.coeff_mul]
  exact sum_congr rfl fun k _ ↦ by
    rw [convolution_eq_coeff_exp_mul, convolution_eq_coeff_exp_mul]

/-- The convolution is homogeneous of degree `n` under simultaneous scalar multiplication. -/
theorem convolution_mul (hI : DividedPowers I) (hJ : DividedPowers J)
    (n : ℕ) (a : A) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    hI.convolution hJ n (a * x) (a * y) = a ^ n * hI.convolution hJ n x y := by
  rw [convolution_def, convolution_def, mul_sum]
  refine sum_congr rfl fun ⟨i, j⟩ hk ↦ ?_
  have hij : i + j = n := mem_antidiagonal.mp hk
  rw [hI.dpow_mul hx, hJ.dpow_mul hy, ← hij, pow_add]
  ring

/-- Evaluating the convolution at `0` in the second argument recovers `hI.dpow`. -/
@[simp]
theorem convolution_zero_right (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x : A) :
    hI.convolution hJ n x 0 = hI.dpow n x := by
  rw [convolution_def]
  have hmem : (n, 0) ∈ antidiagonal n := mem_antidiagonal.mpr (add_zero n)
  rw [sum_eq_single (n, 0)]
  · simp [hJ.dpow_zero J.zero_mem]
  · intro ⟨i, j⟩ hk hne
    have hj : j ≠ 0 := by
      have hij : i + j = n := mem_antidiagonal.mp hk
      intro h0
      exact hne (Prod.ext (by omega) h0)
    rw [hJ.dpow_eval_zero hj, mul_zero]
  · exact fun h ↦ absurd hmem h

/-- Evaluating the convolution at `0` in the first argument recovers `hJ.dpow`. -/
@[simp]
theorem convolution_zero_left (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (y : A) :
    hI.convolution hJ n 0 y = hJ.dpow n y := by
  rw [convolution_comm, convolution_zero_right]

/-- The convolution of a divided power structure with itself computes `hI.dpow n (x + y)`. -/
theorem convolution_self (hI : DividedPowers I) (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    hI.convolution hI n x y = hI.dpow n (x + y) :=
  (hI.dpow_add hx hy).symm

/-- If `I ⊓ J = I * J`, then every two divided power structures on `I` and `J` agree on `I ⊓ J`
in every degree. -/
theorem coincide_of_inf_eq_mul (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : I ⊓ J = I * J) (n : ℕ) {w : A} (hw : w ∈ I ⊓ J) :
    hI.dpow n w = hJ.dpow n w := by
  rw [h, ← smul_eq_mul] at hw
  exact hI.coincide_on_smul hJ hw

end CommSemiring

section CommRing

variable {A : Type*} [CommRing A] {I J : Ideal A}

/-- If `hI` and `hJ` agree on `I ⊓ J`, then `convolution hI hJ n x y` depends only on `x + y`. -/
theorem convolution_eq_of_add_eq (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    {n : ℕ} {x x' y y' : A} (hx : x ∈ I) (hx' : x' ∈ I) (hy : y ∈ J) (hy' : y' ∈ J)
    (hadd : x + y = x' + y') :
    hI.convolution hJ n x y = hI.convolution hJ n x' y' := by
  have hwI : x - x' ∈ I := I.sub_mem hx hx'
  have hw_eq : x - x' = y' - y := sub_eq_sub_iff_add_eq_add.mpr (by rw [hadd, add_comm])
  have hwJ : x - x' ∈ J := hw_eq ▸ J.sub_mem hy' hy
  have hexp_w : hI.exp (x - x') = hJ.exp (x - x') := by
    ext k
    simp [DividedPowers.exp, hIJ k (x - x') ⟨hwI, hwJ⟩]
  have hexp : hI.exp x * hJ.exp y = hI.exp x' * hJ.exp y' := by
    calc
      hI.exp x * hJ.exp y
        = hI.exp (x' + (x - x')) * hJ.exp y := by rw [add_sub_cancel]
      _ = hI.exp x' * hI.exp (x - x') * hJ.exp y := by rw [hI.exp_add hx' hwI]
      _ = hI.exp x' * (hJ.exp (x - x') * hJ.exp y) := by rw [hexp_w, mul_assoc]
      _ = hI.exp x' * hJ.exp (x - x' + y) := by rw [← hJ.exp_add hwJ hy]
      _ = hI.exp x' * hJ.exp y' := by rw [hw_eq, sub_add_cancel]
  rw [convolution_eq_coeff_exp_mul, convolution_eq_coeff_exp_mul, hexp]

private noncomputable def supDpow (hI : DividedPowers I) (hJ : DividedPowers J)
    (n : ℕ) (z : A) : A :=
  open scoped Classical in
  if hz : z ∈ I ⊔ J then
    have hmem : ∃ x ∈ I, ∃ y ∈ J, x + y = z := Submodule.mem_sup.mp hz
    hI.convolution hJ n hmem.choose hmem.choose_spec.2.choose
  else 0

private theorem supDpow_add_eq (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    supDpow hI hJ n (x + y) = hI.convolution hJ n x y := by
  classical
  have hz : x + y ∈ I ⊔ J := Submodule.add_mem_sup hx hy
  simp only [supDpow, dite_eq_left hz]
  set hmem := Submodule.mem_sup.mp hz
  exact hI.convolution_eq_of_add_eq hJ hIJ hmem.choose_spec.1 hx
    hmem.choose_spec.2.choose_spec.1 hy hmem.choose_spec.2.choose_spec.2

/-- The additive divided-power candidate on `I ⊔ J` defined by `convolution` whenever `hI` and
`hJ` agree on `I ⊓ J`. -/
noncomputable def supCandidate (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    TauCeti.AdditivePowers (I ⊔ J) where
  dpow := supDpow hI hJ
  dpow_null {n z} hz := by classical simp [supDpow, hz]
  dpow_zero {z} hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [supDpow_add_eq hI hJ hIJ 0 hx hy, hI.convolution_zero hJ hx hy]
  dpow_one {z} hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [supDpow_add_eq hI hJ hIJ 1 hx hy, hI.convolution_one hJ hx hy]
  dpow_mem {n z} hn hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [supDpow_add_eq hI hJ hIJ n hx hy]
    exact hI.convolution_mem hJ hn x y
  dpow_add {n z z'} hz hz' := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨x', hx', y', hy', rfl⟩ := Submodule.mem_sup.mp hz'
    have hrearr : x + y + (x' + y') = (x + x') + (y + y') := by ring
    rw [hrearr, supDpow_add_eq hI hJ hIJ n (I.add_mem hx hx') (J.add_mem hy hy'),
      hI.convolution_add hJ hx hx' hy hy']
    exact sum_congr rfl fun k _ ↦ by
      rw [supDpow_add_eq hI hJ hIJ k.1 hx hy, supDpow_add_eq hI hJ hIJ k.2 hx' hy']
  dpow_mul {n a z} hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [mul_add, supDpow_add_eq hI hJ hIJ n (I.mul_mem_left a hx) (J.mul_mem_left a hy),
      supDpow_add_eq hI hJ hIJ n hx hy, hI.convolution_mul hJ n a hx hy]

/-- On `x + y` with `x ∈ I` and `y ∈ J`, `supCandidate` evaluates to `convolution`. -/
theorem supCandidate_dpow_add (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (hI.supCandidate hJ hIJ).dpow n (x + y) = hI.convolution hJ n x y :=
  supDpow_add_eq hI hJ hIJ n hx hy

/-- `supCandidate` restricts to `hI` on `I`. -/
theorem supCandidate_dpow_left (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.supCandidate hJ hIJ).dpow n x = hI.dpow n x := by
  simpa using hI.supCandidate_dpow_add hJ hIJ n hx J.zero_mem

/-- `supCandidate` restricts to `hJ` on `J`. -/
theorem supCandidate_dpow_right (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {y : A} (hy : y ∈ J) :
    (hI.supCandidate hJ hIJ).dpow n y = hJ.dpow n y := by
  simpa using hI.supCandidate_dpow_add hJ hIJ n I.zero_mem hy

/-- The unique glued `DividedPowers (I ⊔ J)` structure restricting to `hI` on `I` and to `hJ` on
`J`, given that `hI` and `hJ` agree on `I ⊓ J` (Stacks Project Lemma 23.2.5, Tag 07GQ). -/
noncomputable def sup (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    DividedPowers (I ⊔ J) :=
  (hI.supCandidate hJ hIJ).toDividedPowers (S := (I : Set A) ∪ (J : Set A))
    (by rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq])
    (fun m n s hs ↦ by
      rcases hs with hs | hs
      · simp only [hI.supCandidate_dpow_left hJ hIJ _ hs]
        exact hI.mul_dpow hs
      · simp only [hI.supCandidate_dpow_right hJ hIJ _ hs]
        exact hJ.mul_dpow hs)
    (fun m n hn s hs ↦ by
      rcases hs with hs | hs
      · rw [hI.supCandidate_dpow_left hJ hIJ n hs,
          hI.supCandidate_dpow_left hJ hIJ m (hI.dpow_mem hn hs),
          hI.supCandidate_dpow_left hJ hIJ (m * n) hs]
        exact hI.dpow_comp hn hs
      · rw [hI.supCandidate_dpow_right hJ hIJ n hs,
          hI.supCandidate_dpow_right hJ hIJ m (hJ.dpow_mem hn hs),
          hI.supCandidate_dpow_right hJ hIJ (m * n) hs]
        exact hJ.dpow_comp hn hs)

/-- On `x + y` with `x ∈ I` and `y ∈ J`, the glued structure `sup` evaluates to `convolution`. -/
theorem sup_dpow_add (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (hI.sup hJ hIJ).dpow n (x + y) = hI.convolution hJ n x y := by
  rw [sup, TauCeti.AdditivePowers.toDividedPowers_dpow]
  exact hI.supCandidate_dpow_add hJ hIJ n hx hy

/-- The glued structure `sup` restricts to `hI` on `I`. -/
@[simp]
theorem sup_dpow_left (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.sup hJ hIJ).dpow n x = hI.dpow n x := by
  rw [sup, TauCeti.AdditivePowers.toDividedPowers_dpow]
  exact hI.supCandidate_dpow_left hJ hIJ n hx

/-- The glued structure `sup` restricts to `hJ` on `J`. -/
@[simp]
theorem sup_dpow_right (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {y : A} (hy : y ∈ J) :
    (hI.sup hJ hIJ).dpow n y = hJ.dpow n y := by
  rw [sup, TauCeti.AdditivePowers.toDividedPowers_dpow]
  exact hI.supCandidate_dpow_right hJ hIJ n hy

/-- The identity map is a PD morphism from `(I, hI)` to `(I ⊔ J, hI.sup hJ hIJ)`. -/
theorem isDPMorphism_id_sup_left (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    IsDPMorphism hI (hI.sup hJ hIJ) (RingHom.id A) :=
  ⟨by rw [Ideal.map_id]; exact le_sup_left, fun _ ha ↦ hI.sup_dpow_left hJ hIJ _ ha⟩

/-- The identity map is a PD morphism from `(J, hJ)` to `(I ⊔ J, hI.sup hJ hIJ)`. -/
theorem isDPMorphism_id_sup_right (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    IsDPMorphism hJ (hI.sup hJ hIJ) (RingHom.id A) :=
  ⟨by rw [Ideal.map_id]; exact le_sup_right, fun _ ha ↦ hI.sup_dpow_right hJ hIJ _ ha⟩

/-- Universal property of `DividedPowers.sup`: a ring homomorphism `g : A →+* B` is a PD morphism
from `(I ⊔ J, hI.sup hJ hIJ)` to `(K, hK)` if and only if it is a PD morphism from both `(I, hI)`
and `(J, hJ)`. -/
theorem isDPMorphism_sup_iff (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    {B : Type*} [CommSemiring B] {K : Ideal B} (hK : DividedPowers K) (g : A →+* B) :
    IsDPMorphism (hI.sup hJ hIJ) hK g ↔ IsDPMorphism hI hK g ∧ IsDPMorphism hJ hK g := by
  constructor
  · intro hg
    exact ⟨hg.comp hK (hI.isDPMorphism_id_sup_left hJ hIJ),
      hg.comp hK (hI.isDPMorphism_id_sup_right hJ hIJ)⟩
  · rintro ⟨hgI, hgJ⟩
    refine IsDPMorphism.on_span (hI.sup hJ hIJ) hK (S := (I : Set A) ∪ (J : Set A))
      (by rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq]) ?_ ?_
    · rintro s (hs | hs)
      · exact hgI.ideal_comp (Ideal.mem_map_of_mem g hs)
      · exact hgJ.ideal_comp (Ideal.mem_map_of_mem g hs)
    · rintro n s (hs | hs)
      · rw [hI.sup_dpow_left hJ hIJ n hs, hgI.dpow_comp s hs]
      · rw [hI.sup_dpow_right hJ hIJ n hs, hgJ.dpow_comp s hs]

/-- A divided power structure on `I ⊔ J` equals `hI.sup hJ hIJ` if and only if it restricts to
`hI` on `I` and to `hJ` on `J`. -/
theorem eq_sup_iff (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (hK : DividedPowers (I ⊔ J)) :
    hK = hI.sup hJ hIJ ↔
      (∀ n, ∀ x ∈ I, hK.dpow n x = hI.dpow n x) ∧
      (∀ n, ∀ y ∈ J, hK.dpow n y = hJ.dpow n y) := by
  constructor
  · rintro rfl
    exact ⟨fun n _ hx ↦ hI.sup_dpow_left hJ hIJ n hx,
      fun n _ hy ↦ hI.sup_dpow_right hJ hIJ n hy⟩
  · rintro ⟨hKI, hKJ⟩
    refine (hI.sup hJ hIJ).dpow_eq_from_gens hK (S := (I : Set A) ∪ (J : Set A))
      (by rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq]) ?_
    rintro n s (hs | hs)
    · rw [hI.sup_dpow_left hJ hIJ n hs, hKI n s hs]
    · rw [hI.sup_dpow_right hJ hIJ n hs, hKJ n s hs]

/-- A divided power structure on `I ⊔ J` restricting to `hI` on `I` and to `hJ` on `J` exists if
and only if `hI` and `hJ` agree on `I ⊓ J` in every degree. -/
theorem exists_sup_iff (hI : DividedPowers I) (hJ : DividedPowers J) :
    (∃ hK : DividedPowers (I ⊔ J),
        (∀ n, ∀ x ∈ I, hK.dpow n x = hI.dpow n x) ∧
        (∀ n, ∀ y ∈ J, hK.dpow n y = hJ.dpow n y)) ↔
      ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w := by
  constructor
  · rintro ⟨hK, hKI, hKJ⟩ n w ⟨hwI, hwJ⟩
    rw [← hKI n w hwI, hKJ n w hwJ]
  · intro hIJ
    exact ⟨hI.sup hJ hIJ, (hI.eq_sup_iff hJ hIJ (hI.sup hJ hIJ)).mp rfl⟩

/-- Gluing is symmetric: `hI.sup hJ hIJ` and `hJ.sup hI _` have the same operations everywhere. -/
theorem sup_comm_dpow (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) (n : ℕ) (z : A) :
    (hI.sup hJ hIJ).dpow n z =
      (hJ.sup hI fun m w hw ↦ (hIJ m w ⟨hw.2, hw.1⟩).symm).dpow n z := by
  by_cases hz : z ∈ I ⊔ J
  · obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [hI.sup_dpow_add hJ hIJ n hx hy, add_comm x y, hJ.sup_dpow_add hI _ n hy hx,
      hI.convolution_comm hJ]
  · rw [DividedPowers.dpow_null _ hz, DividedPowers.dpow_null _ (by rwa [sup_comm])]

/-- Gluing `hI` with itself recovers `hI.dpow` everywhere. -/
theorem sup_self_dpow (hI : DividedPowers I) (n : ℕ) (x : A) :
    (hI.sup hI fun _ _ _ ↦ rfl).dpow n x = hI.dpow n x := by
  by_cases hx : x ∈ I
  · exact hI.sup_dpow_left hI (fun _ _ _ ↦ rfl) n hx
  · rw [DividedPowers.dpow_null _ (by rwa [sup_idem]), hI.dpow_null hx]

/-- Gluing `hI` with the zero ideal recovers `hI.dpow` everywhere. -/
theorem sup_bot_dpow (hI : DividedPowers I) (n : ℕ) (x : A) :
    (hI.sup (dividedPowersBot A) fun m w hw ↦ by
        rcases eq_or_ne m 0 with rfl | hm
        · rw [hI.dpow_zero hw.1, (dividedPowersBot A).dpow_zero hw.2]
        · rw [Ideal.mem_bot.mp hw.2, hI.dpow_eval_zero hm,
            (dividedPowersBot A).dpow_eval_zero hm]).dpow n x = hI.dpow n x := by
  by_cases hx : x ∈ I
  · exact hI.sup_dpow_left _ _ n hx
  · rw [DividedPowers.dpow_null _ (by rwa [sup_bot_eq]), hI.dpow_null hx]

/-- The unique glued divided power structure on `I ⊔ J` when `I ⊓ J = I * J`. -/
noncomputable def supOfInfEqMul (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : I ⊓ J = I * J) : DividedPowers (I ⊔ J) :=
  hI.sup hJ fun n _ hw ↦ hI.coincide_of_inf_eq_mul hJ h n hw

/-- `supOfInfEqMul` is defined via `DividedPowers.sup` and `coincide_of_inf_eq_mul`. -/
theorem supOfInfEqMul_eq_sup (hI : DividedPowers I) (hJ : DividedPowers J) (h : I ⊓ J = I * J) :
    hI.supOfInfEqMul hJ h = hI.sup hJ fun n _ hw ↦ hI.coincide_of_inf_eq_mul hJ h n hw := (rfl)

/-- On `x + y` with `x ∈ I` and `y ∈ J`, `supOfInfEqMul` evaluates to `convolution`. -/
theorem supOfInfEqMul_dpow_add (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : I ⊓ J = I * J) (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (hI.supOfInfEqMul hJ h).dpow n (x + y) = hI.convolution hJ n x y :=
  hI.sup_dpow_add hJ _ n hx hy

/-- `supOfInfEqMul` restricts to `hI` on `I`. -/
@[simp]
theorem supOfInfEqMul_dpow_left (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : I ⊓ J = I * J) (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.supOfInfEqMul hJ h).dpow n x = hI.dpow n x :=
  hI.sup_dpow_left hJ _ n hx

/-- `supOfInfEqMul` restricts to `hJ` on `J`. -/
@[simp]
theorem supOfInfEqMul_dpow_right (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : I ⊓ J = I * J) (n : ℕ) {y : A} (hy : y ∈ J) :
    (hI.supOfInfEqMul hJ h).dpow n y = hJ.dpow n y :=
  hI.sup_dpow_right hJ _ n hy

/-- A divided power structure on `I ⊔ J` (with `I ⊓ J = I * J`) equals `hI.supOfInfEqMul hJ h`
if and only if it restricts to `hI` on `I` and to `hJ` on `J`. -/
theorem eq_supOfInfEqMul_iff (hI : DividedPowers I) (hJ : DividedPowers J)
    (h : I ⊓ J = I * J) (hK : DividedPowers (I ⊔ J)) :
    hK = hI.supOfInfEqMul hJ h ↔
      (∀ n, ∀ x ∈ I, hK.dpow n x = hI.dpow n x) ∧
      (∀ n, ∀ y ∈ J, hK.dpow n y = hJ.dpow n y) :=
  hI.eq_sup_iff hJ _ hK

end CommRing

end DividedPowers
