/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.Basic
public import TauCeti.RingTheory.DividedPowers.Generators
public import Mathlib.RingTheory.DividedPowers.DPMorphism

/-!
# Gluing divided powers on a sum of ideals

Let `γ` be a divided power structure on an ideal `I` and `ε` one on an ideal `J` of a commutative
ring `A`. If `γ` and `ε` agree on `I ⊓ J`, there is a unique divided power structure
`DividedPowers.glue γ ε h` on `I ⊔ J` restricting to `γ` on `I` and to `ε` on `J`; at `x + y`,
with `x ∈ I` and `y ∈ J`, it is the convolution `∑_{i + j = n} γᵢ(x) εⱼ(y)`.

Agreement on `I ⊓ J` is also necessary for such a common extension to exist, and it holds
automatically when `I ⊓ J = I * J`. This is the gluing used, for instance, to put divided powers
on `I · A⟨x⟩ + A⟨x⟩₊` in a divided power polynomial algebra.

## Main definitions

* `DividedPowers.convolution γ ε n x y`: the antidiagonal sum `∑_{i + j = n} γᵢ(x) εⱼ(y)`.
* `DividedPowers.glue γ ε h`: the glued divided power structure on `I ⊔ J`.

## Main results

* `DividedPowers.convolution_eq_of_add_eq`: the convolution only depends on `x + y`.
* `DividedPowers.eq_glue_iff`: `glue γ ε h` is the only divided power structure on `I ⊔ J`
  restricting to `γ` and to `ε`.
* `DividedPowers.glue_comm`, `DividedPowers.glue_of_le_left`, `DividedPowers.glue_of_le_right`,
  `DividedPowers.glue_self`, `DividedPowers.glue_bot`, `DividedPowers.bot_glue`: symmetry,
  dominance, idempotence, and unit laws for gluing.
* `DividedPowers.exists_dividedPowers_sup_iff`,
  `DividedPowers.existsUnique_dividedPowers_sup_iff`: a common extension exists (and is unique)
  if and only if `γ` and `ε` agree on `I ⊓ J`.
* `DividedPowers.isDPMorphism_glue_iff`: a ring map is a divided power morphism out of the glued
  structure if and only if it is one out of `γ` and out of `ε`.
* `DividedPowers.coincide_on_inf` and `DividedPowers.existsUnique_dividedPowers_sup_of_inf_eq_mul`:
  if `I ⊓ J = I * J`, any `γ` and `ε` agree on `I ⊓ J` and glue uniquely.

## References

* [Stacks Project, Tag 07GQ](https://stacks.math.columbia.edu/tag/07GQ)
-/

public section

open Finset

namespace DividedPowers

section Convolution

variable {A : Type*} [CommSemiring A] {I J : Ideal A} (γ : DividedPowers I) (ε : DividedPowers J)

/-- The convolution `Cₙ(x, y) = ∑_{i + j = n} γᵢ(x) εⱼ(y)` of two divided power structures. -/
def convolution (n : ℕ) (x y : A) : A :=
  ∑ k ∈ antidiagonal n, γ.dpow k.1 x * ε.dpow k.2 y

theorem convolution_def (n : ℕ) (x y : A) :
    convolution γ ε n x y = ∑ k ∈ antidiagonal n, γ.dpow k.1 x * ε.dpow k.2 y :=
  (rfl)

/-- `convolution γ ε n x y` is the `n`-th coefficient of `γ.exp x * ε.exp y`. -/
@[simp]
theorem coeff_exp_mul_exp (n : ℕ) (x y : A) :
    PowerSeries.coeff n (γ.exp x * ε.exp y) = convolution γ ε n x y := by
  simp [convolution_def, PowerSeries.coeff_mul, exp]

/-- Exchanging the two structures and the two arguments leaves the convolution unchanged. -/
theorem convolution_comm (n : ℕ) (x y : A) : convolution γ ε n x y = convolution ε γ n y x := by
  rw [convolution_def, convolution_def, ← Nat.sum_antidiagonal_swap]
  exact sum_congr rfl fun k _ ↦ mul_comm _ _

/-- In degree `0`, `convolution γ ε 0 x y = 1` for `x ∈ I` and `y ∈ J`. -/
@[simp]
theorem convolution_zero {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    convolution γ ε 0 x y = 1 := by
  simp [convolution_def, γ.dpow_zero hx, ε.dpow_zero hy]

/-- In degree `1`, `convolution γ ε 1 x y = x + y` for `x ∈ I` and `y ∈ J`. -/
@[simp]
theorem convolution_one {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    convolution γ ε 1 x y = x + y := by
  rw [convolution_def, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ, sum_range_one]
  simp [γ.dpow_zero hx, γ.dpow_one hx, ε.dpow_zero hy, ε.dpow_one hy, add_comm]

/-- In degree `2`, `convolution γ ε 2 x y = γ.dpow 2 x + x * y + ε.dpow 2 y` for `x ∈ I` and
`y ∈ J`. -/
theorem convolution_two {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    convolution γ ε 2 x y = γ.dpow 2 x + x * y + ε.dpow 2 y := by
  rw [convolution_def, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ, sum_range_succ,
    sum_range_one]
  simp only [Nat.reduceSub, Nat.sub_zero, tsub_self, γ.dpow_zero hx, γ.dpow_one hx,
    ε.dpow_zero hy, ε.dpow_one hy]
  ring

/-- If `x ∉ I`, then `convolution γ ε n x y = 0`. -/
@[simp]
theorem convolution_null_left {n : ℕ} {x y : A} (hx : x ∉ I) :
    convolution γ ε n x y = 0 := by
  simp [convolution_def, γ.dpow_null hx]

/-- If `y ∉ J`, then `convolution γ ε n x y = 0`. -/
@[simp]
theorem convolution_null_right {n : ℕ} {x y : A} (hy : y ∉ J) :
    convolution γ ε n x y = 0 := by
  simp [convolution_def, ε.dpow_null hy]

@[simp]
theorem convolution_zero_right (n : ℕ) (x : A) : convolution γ ε n x 0 = γ.dpow n x := by
  rw [convolution_def, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_eq_single n]
  · simp [ε.dpow_zero J.zero_mem]
  · intro k hk hkn
    rw [ε.dpow_eval_zero (by grind), mul_zero]
  · simp

@[simp]
theorem convolution_zero_left (n : ℕ) (y : A) : convolution γ ε n 0 y = ε.dpow n y := by
  rw [convolution_comm, convolution_zero_right]

/-- The convolution of `γ` with itself is `γ.dpow` of the sum. -/
@[simp low]
theorem convolution_self (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    convolution γ γ n x y = γ.dpow n (x + y) := by
  rw [convolution_def, γ.dpow_add hx hy]

/-- In positive degree the convolution of `x ∈ I` and `y ∈ J` lies in `I ⊔ J`. -/
theorem convolution_mem {n : ℕ} (hn : n ≠ 0) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    convolution γ ε n x y ∈ I ⊔ J := by
  refine sum_mem fun k hk ↦ ?_
  by_cases hk1 : k.1 = 0
  · have hk2 : k.2 ≠ 0 := by grind [mem_antidiagonal]
    exact Ideal.mem_sup_right (J.mul_mem_left _ (ε.dpow_mem hk2 hy))
  · exact Ideal.mem_sup_left (I.mul_mem_right _ (γ.dpow_mem hk1 hx))

/-- The convolution is homogeneous of degree `n` in the pair `(x, y)`. -/
theorem convolution_mul (n : ℕ) (a : A) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    convolution γ ε n (a * x) (a * y) = a ^ n * convolution γ ε n x y := by
  rw [convolution_def, convolution_def, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [γ.dpow_mul hx, ε.dpow_mul hy, ← (mem_antidiagonal.mp hk), pow_add]
  ring

/-- The addition law of the convolution in the pair `(x, y)`. -/
theorem convolution_add (n : ℕ) {x x' y y' : A} (hx : x ∈ I) (hx' : x' ∈ I) (hy : y ∈ J)
    (hy' : y' ∈ J) :
    convolution γ ε n (x + x') (y + y') =
      ∑ k ∈ antidiagonal n, convolution γ ε k.1 x y * convolution γ ε k.2 x' y' := by
  simp only [← coeff_exp_mul_exp, γ.exp_add hx hx', ε.exp_add hy hy']
  rw [← PowerSeries.coeff_mul, mul_mul_mul_comm]

/-- If `I ⊓ J = I * J`, any divided power structures on `I` and on `J` agree on `I ⊓ J`. -/
theorem coincide_on_inf (hIJ : I ⊓ J = I * J) {n : ℕ} {w : A} (hw : w ∈ I ⊓ J) :
    γ.dpow n w = ε.dpow n w :=
  γ.coincide_on_smul ε (by rwa [Ideal.smul_eq_mul, ← hIJ])

/-- Any divided power structure on `I` agrees with `dividedPowersBot A` on `I ⊓ ⊥`. -/
theorem coincide_on_inf_bot_right :
    ∀ n, ∀ w ∈ I ⊓ ⊥, γ.dpow n w = (dividedPowersBot A).dpow n w :=
  fun _ _ ↦ coincide_on_inf γ (dividedPowersBot A) ((inf_bot_eq I).trans (Ideal.mul_bot I).symm)

/-- `dividedPowersBot A` agrees with any divided power structure on `J` on `⊥ ⊓ J`. -/
theorem coincide_on_inf_bot_left :
    ∀ n, ∀ w ∈ ⊥ ⊓ J, (dividedPowersBot A).dpow n w = ε.dpow n w :=
  fun n w hw ↦ (coincide_on_inf_bot_right ε n w ⟨hw.2, hw.1⟩).symm

end Convolution

section Glue

variable {A : Type*} [CommRing A] {I J : Ideal A} (γ : DividedPowers I) (ε : DividedPowers J)

/-- If `γ` and `ε` agree on `I ⊓ J`, the convolution `Cₙ(x, y)` only depends on `x + y`. -/
theorem convolution_eq_of_add_eq (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w) (n : ℕ)
    {x x' y y' : A} (hx : x ∈ I) (hx' : x' ∈ I) (hy : y ∈ J) (hy' : y' ∈ J)
    (hxy : x + y = x' + y') :
    convolution γ ε n x y = convolution γ ε n x' y' := by
  have hw : x - x' ∈ I ⊓ J := by
    refine ⟨I.sub_mem hx hx', ?_⟩
    rw [sub_eq_sub_iff_add_eq_add.mpr (by rw [hxy, add_comm])]
    exact J.sub_mem hy' hy
  have hexp : γ.exp (x - x') = ε.exp (x - x') := by
    ext k
    simp [exp, h k _ hw]
  have hx₀ : γ.exp x = γ.exp x' * γ.exp (x - x') := by
    rw [← γ.exp_add hx' hw.1, add_sub_cancel]
  have hy₀ : ε.exp y' = ε.exp (x - x') * ε.exp y := by
    rw [← ε.exp_add hw.2 hy, sub_add_eq_add_sub, hxy, add_sub_cancel_left]
  rw [← coeff_exp_mul_exp, ← coeff_exp_mul_exp, hx₀, hy₀, hexp, mul_assoc]

variable {γ ε} (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w)

private theorem exists_decomposition {z : A} (hz : z ∈ I ⊔ J) :
    ∃ p : A × A, p.1 ∈ I ∧ p.2 ∈ J ∧ p.1 + p.2 = z := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
  exact ⟨(x, y), hx, hy, rfl⟩

/-- The operations of the glued structure: `δₙ(x + y) = Cₙ(x, y)` for `x ∈ I` and `y ∈ J`. -/
private noncomputable def supDpow (n : ℕ) (z : A) : A :=
  open scoped Classical in
  if hz : z ∈ I ⊔ J then
    convolution γ ε n (exists_decomposition hz).choose.1 (exists_decomposition hz).choose.2
  else 0

include h in
private theorem supDpow_add (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    supDpow (γ := γ) (ε := ε) n (x + y) = convolution γ ε n x y := by
  have hz : x + y ∈ I ⊔ J := Submodule.add_mem_sup hx hy
  obtain ⟨h1, h2, h3⟩ := (exists_decomposition hz).choose_spec
  rw [supDpow, dite_eq_left hz]
  exact convolution_eq_of_add_eq γ ε h n h1 hx h2 hy h3

/-- The additive divided-power candidate on `I ⊔ J` defined by convolution. -/
private noncomputable def supPowers : TauCeti.PD.AdditivePowers (I ⊔ J) where
  dpow := supDpow (γ := γ) (ε := ε)
  dpow_null hz := by rw [supDpow, dite_eq_right hz]
  dpow_zero hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    simp [supDpow_add h 0 hx hy, convolution_def, γ.dpow_zero hx, ε.dpow_zero hy]
  dpow_one hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    simp [supDpow_add h 1 hx hy, convolution_def, Nat.antidiagonal_succ, γ.dpow_zero hx,
      ε.dpow_zero hy, γ.dpow_one hx, ε.dpow_one hy, add_comm]
  dpow_mem hn hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [supDpow_add h _ hx hy]
    exact convolution_mem γ ε hn hx hy
  dpow_add hz hz' := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨x', hx', y', hy', rfl⟩ := Submodule.mem_sup.mp hz'
    rw [add_add_add_comm, supDpow_add h _ (I.add_mem hx hx') (J.add_mem hy hy'),
      convolution_add γ ε _ hx hx' hy hy']
    exact sum_congr rfl fun k _ ↦ by rw [supDpow_add h _ hx hy, supDpow_add h _ hx' hy']
  dpow_mul {n a _} hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [mul_add, supDpow_add h _ (I.mul_mem_left a hx) (J.mul_mem_left a hy),
      supDpow_add h _ hx hy, convolution_mul γ ε n a hx hy]

private theorem supPowers_dpow_add (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (supPowers h).dpow n (x + y) = convolution γ ε n x y :=
  supDpow_add h n hx hy

private theorem supPowers_dpow_of_mem_left (n : ℕ) {x : A} (hx : x ∈ I) :
    (supPowers h).dpow n x = γ.dpow n x := by
  simpa using supPowers_dpow_add h n hx J.zero_mem

private theorem supPowers_dpow_of_mem_right (n : ℕ) {y : A} (hy : y ∈ J) :
    (supPowers h).dpow n y = ε.dpow n y := by
  simpa using supPowers_dpow_add h n I.zero_mem hy

/-- The divided power structure on `I ⊔ J` glued from divided power structures `γ` on `I` and `ε`
on `J` that agree on `I ⊓ J`. -/
noncomputable def glue (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w) : DividedPowers (I ⊔ J) :=
  (supPowers h).toDividedPowers (S := (I : Set A) ∪ (J : Set A))
    (by rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq])
    (by
      rintro s (hs | hs) m n
      · simp only [supPowers_dpow_of_mem_left h _ hs]
        exact γ.mul_dpow hs
      · simp only [supPowers_dpow_of_mem_right h _ hs]
        exact ε.mul_dpow hs)
    (by
      rintro s (hs | hs) m n hn
      · rw [supPowers_dpow_of_mem_left h _ hs, supPowers_dpow_of_mem_left h _ (γ.dpow_mem hn hs),
          supPowers_dpow_of_mem_left h _ hs]
        exact γ.dpow_comp hn hs
      · rw [supPowers_dpow_of_mem_right h _ hs,
          supPowers_dpow_of_mem_right h _ (ε.dpow_mem hn hs), supPowers_dpow_of_mem_right h _ hs]
        exact ε.dpow_comp hn hs)

/-- At `x + y` with `x ∈ I` and `y ∈ J`, the glued operation is the convolution `Cₙ(x, y)`. -/
theorem glue_dpow_add (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (glue γ ε h).dpow n (x + y) = convolution γ ε n x y := by
  rw [glue, TauCeti.PD.AdditivePowers.toDividedPowers_dpow, supPowers_dpow_add h n hx hy]

@[simp]
theorem glue_dpow_of_mem_left (n : ℕ) {x : A} (hx : x ∈ I) :
    (glue γ ε h).dpow n x = γ.dpow n x := by
  simpa using glue_dpow_add h n hx J.zero_mem

@[simp]
theorem glue_dpow_of_mem_right (n : ℕ) {y : A} (hy : y ∈ J) :
    (glue γ ε h).dpow n y = ε.dpow n y := by
  simpa using glue_dpow_add h n I.zero_mem hy

/-- Gluing is symmetric in the two ideals and divided power structures. -/
theorem glue_dpow_comm (n : ℕ) (z : A) :
    (glue γ ε h).dpow n z =
      (glue ε γ fun m w hw ↦ (h m w ⟨hw.2, hw.1⟩).symm).dpow n z := by
  by_cases hz : z ∈ I ⊔ J
  · obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [glue_dpow_add h n hx hy, add_comm x y, glue_dpow_add _ n hy hx, convolution_comm]
  · have hz' : z ∉ J ⊔ I := by rwa [sup_comm]
    rw [(glue γ ε h).dpow_null hz, (glue ε γ _).dpow_null hz']

/-- When `J ≤ I`, gluing `γ` and `ε` recovers the operations of `γ` on all of `A`. -/
theorem glue_dpow_of_le_left (hJI : J ≤ I) (n : ℕ) (z : A) :
    (glue γ ε h).dpow n z = γ.dpow n z := by
  by_cases hz : z ∈ I
  · exact glue_dpow_of_mem_left h n hz
  · have hz' : z ∉ I ⊔ J := by rwa [sup_of_le_left hJI]
    rw [(glue γ ε h).dpow_null hz', γ.dpow_null hz]

/-- When `I ≤ J`, gluing `γ` and `ε` recovers the operations of `ε` on all of `A`. -/
theorem glue_dpow_of_le_right (hIJ : I ≤ J) (n : ℕ) (z : A) :
    (glue γ ε h).dpow n z = ε.dpow n z := by
  rw [glue_dpow_comm, glue_dpow_of_le_left _ hIJ]

/-- Gluing a divided power structure with itself recovers the original operations on all of `A`. -/
@[simp]
theorem glue_dpow_self (γ : DividedPowers I) (n : ℕ) (z : A) :
    (glue γ γ fun _ _ _ ↦ rfl).dpow n z = γ.dpow n z :=
  glue_dpow_of_le_left (fun _ _ _ ↦ rfl) le_rfl n z

/-- Gluing `γ` with `dividedPowersBot A` recovers the original operations of `γ` on all of `A`. -/
@[simp]
theorem glue_dpow_bot (γ : DividedPowers I) (n : ℕ) (z : A) :
    (glue γ (dividedPowersBot A) (coincide_on_inf_bot_right γ)).dpow n z = γ.dpow n z :=
  glue_dpow_of_le_left _ bot_le n z

/-- Gluing `dividedPowersBot A` with `ε` recovers the original operations of `ε` on all of `A`. -/
@[simp]
theorem bot_glue_dpow (ε : DividedPowers J) (n : ℕ) (z : A) :
    (glue (dividedPowersBot A) ε (coincide_on_inf_bot_left ε)).dpow n z = ε.dpow n z :=
  glue_dpow_of_le_right _ bot_le n z

/-- Gluing divided power structures is symmetric as a bundled `DividedPowers` structure up to
transport along `sup_comm`. -/
protected theorem glue_comm :
    (sup_comm I J ▸ glue γ ε h) =
      glue ε γ fun m w hw ↦ (h m w ⟨hw.2, hw.1⟩).symm := by
  ext n z _
  rw [dpow_eqRec, glue_dpow_comm h n z]

/-- When `J ≤ I`, gluing `γ` and `ε` recovers `γ` as a bundled `DividedPowers` structure up to
transport along `sup_of_le_left`. -/
protected theorem glue_of_le_left (hJI : J ≤ I) :
    (sup_of_le_left hJI ▸ glue γ ε h) = γ := by
  ext n z _
  rw [dpow_eqRec, glue_dpow_of_le_left h hJI n z]

/-- When `I ≤ J`, gluing `γ` and `ε` recovers `ε` as a bundled `DividedPowers` structure up to
transport along `sup_of_le_right`. -/
protected theorem glue_of_le_right (hIJ : I ≤ J) :
    (sup_of_le_right hIJ ▸ glue γ ε h) = ε := by
  ext n z _
  rw [dpow_eqRec, glue_dpow_of_le_right h hIJ n z]

/-- Gluing a divided power structure with itself recovers `γ` as a bundled `DividedPowers`
structure up to transport along `sup_idem`. -/
theorem glue_self (γ : DividedPowers I) :
    (sup_idem I ▸ glue γ γ fun _ _ _ ↦ rfl) = γ := by
  rw [Subsingleton.elim (sup_idem I) (sup_of_le_left (le_refl I)),
    DividedPowers.glue_of_le_left (fun _ _ _ ↦ rfl) le_rfl]

/-- Gluing `γ` with `dividedPowersBot A` recovers `γ` as a bundled `DividedPowers` structure up
to transport along `sup_bot_eq`. -/
theorem glue_bot (γ : DividedPowers I) :
    (sup_bot_eq I ▸ glue γ (dividedPowersBot A) (coincide_on_inf_bot_right γ)) = γ := by
  rw [Subsingleton.elim (sup_bot_eq I) (sup_of_le_left (bot_le : (⊥ : Ideal A) ≤ I)),
    DividedPowers.glue_of_le_left _ bot_le]

/-- Gluing `dividedPowersBot A` with `ε` recovers `ε` as a bundled `DividedPowers` structure up
to transport along `bot_sup_eq`. -/
theorem bot_glue (ε : DividedPowers J) :
    (bot_sup_eq J ▸ glue (dividedPowersBot A) ε (coincide_on_inf_bot_left ε)) = ε := by
  rw [Subsingleton.elim (bot_sup_eq J) (sup_of_le_right (bot_le : (⊥ : Ideal A) ≤ J)),
    DividedPowers.glue_of_le_right _ bot_le]

/-- The glued structure is the only divided power structure on `I ⊔ J` restricting to `γ` on `I`
and to `ε` on `J`. -/
theorem eq_glue_iff (θ : DividedPowers (I ⊔ J)) :
    θ = glue γ ε h ↔
      (∀ n, ∀ x ∈ I, θ.dpow n x = γ.dpow n x) ∧ ∀ n, ∀ y ∈ J, θ.dpow n y = ε.dpow n y := by
  refine ⟨?_, fun ⟨hθI, hθJ⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨fun n x hx ↦ glue_dpow_of_mem_left h n hx, fun n y hy ↦ glue_dpow_of_mem_right h n hy⟩
  · refine θ.ext _ fun n z hz ↦ ?_
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [θ.dpow_add (Ideal.mem_sup_left hx) (Ideal.mem_sup_right hy), glue_dpow_add h n hx hy,
      convolution_def]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hθI _ _ hx, hθJ _ _ hy]

/-- The identity of `A` is a divided power morphism from `γ` to the glued structure. -/
theorem isDPMorphism_glue_left : IsDPMorphism γ (glue γ ε h) (RingHom.id A) :=
  ⟨by rw [Ideal.map_id]; exact le_sup_left, fun a ha ↦ by simp [glue_dpow_of_mem_left h _ ha]⟩

/-- The identity of `A` is a divided power morphism from `ε` to the glued structure. -/
theorem isDPMorphism_glue_right : IsDPMorphism ε (glue γ ε h) (RingHom.id A) :=
  ⟨by rw [Ideal.map_id]; exact le_sup_right, fun a ha ↦ by simp [glue_dpow_of_mem_right h _ ha]⟩

/-- A ring map is a divided power morphism out of the glued structure if and only if it is one
out of `γ` and out of `ε`. -/
theorem isDPMorphism_glue_iff {C : Type*} [CommSemiring C] {K : Ideal C} (κ : DividedPowers K)
    (g : A →+* C) : IsDPMorphism (glue γ ε h) κ g ↔ IsDPMorphism γ κ g ∧ IsDPMorphism ε κ g := by
  refine ⟨fun hg ↦ ⟨?_, ?_⟩, fun ⟨hγ, hε⟩ ↦ ?_⟩
  · simpa using hg.comp κ (isDPMorphism_glue_left h)
  · simpa using hg.comp κ (isDPMorphism_glue_right h)
  · refine IsDPMorphism.on_span (glue γ ε h) κ (S := (I : Set A) ∪ (J : Set A))
      (by rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq]) ?_ ?_
    · rintro s (hs | hs)
      · exact hγ.ideal_comp (Ideal.mem_map_of_mem g hs)
      · exact hε.ideal_comp (Ideal.mem_map_of_mem g hs)
    · rintro n s (hs | hs)
      · rw [glue_dpow_of_mem_left h n hs, hγ.dpow_comp s hs]
      · rw [glue_dpow_of_mem_right h n hs, hε.dpow_comp s hs]

/-- A divided power structure on `I ⊔ J` restricting to `γ` on `I` and to `ε` on `J` exists if and
only if `γ` and `ε` agree on `I ⊓ J`; it is then `glue γ ε h`, by `eq_glue_iff`. -/
theorem exists_dividedPowers_sup_iff :
    (∃ θ : DividedPowers (I ⊔ J),
        (∀ n, ∀ x ∈ I, θ.dpow n x = γ.dpow n x) ∧ ∀ n, ∀ y ∈ J, θ.dpow n y = ε.dpow n y) ↔
      ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w := by
  refine ⟨fun ⟨θ, hθI, hθJ⟩ n w hw ↦ ?_, fun h ↦ ⟨glue γ ε h, (eq_glue_iff h _).mp rfl⟩⟩
  rw [← hθI n w hw.1, hθJ n w hw.2]

/-- Stacks Project, Lemma 23.2.5 (tag `07GQ`): there exists a unique divided power structure on
`I ⊔ J` restricting to `γ` on `I` and to `ε` on `J` if and only if `γ` and `ε` agree on `I ⊓ J`
in every degree. -/
theorem existsUnique_dividedPowers_sup_iff (γ : DividedPowers I) (ε : DividedPowers J) :
    (∃! θ : DividedPowers (I ⊔ J),
        (∀ n, ∀ x ∈ I, θ.dpow n x = γ.dpow n x) ∧ ∀ n, ∀ y ∈ J, θ.dpow n y = ε.dpow n y) ↔
      ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w := by
  refine ⟨fun ⟨θ, ⟨hθI, hθJ⟩, _⟩ n w hw ↦ ?_,
    fun h ↦ ⟨glue γ ε h, (eq_glue_iff h _).mp rfl, fun θ hθ ↦ (eq_glue_iff h θ).mpr hθ⟩⟩
  rw [← hθI n w hw.1, hθJ n w hw.2]

/-- When `I ⊓ J = I * J`, there is a unique divided power structure on `I ⊔ J` restricting to `γ`
on `I` and to `ε` on `J`. -/
theorem existsUnique_dividedPowers_sup_of_inf_eq_mul (γ : DividedPowers I) (ε : DividedPowers J)
    (hIJ : I ⊓ J = I * J) :
    ∃! θ : DividedPowers (I ⊔ J),
      (∀ n, ∀ x ∈ I, θ.dpow n x = γ.dpow n x) ∧ ∀ n, ∀ y ∈ J, θ.dpow n y = ε.dpow n y :=
  (existsUnique_dividedPowers_sup_iff γ ε).mpr (fun _ _ hw ↦ coincide_on_inf γ ε hIJ hw)

end Glue

end DividedPowers
