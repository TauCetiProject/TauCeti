/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `DividedPowers.exists_dividedPowers_sup_iff`: a common extension exists if and only if `γ` and
  `ε` agree on `I ⊓ J`.
* `DividedPowers.isDPMorphism_glue_iff`: a ring map is a divided power morphism out of the glued
  structure if and only if it is one out of `γ` and out of `ε`.
* `DividedPowers.coincide_on_inf`: if `I ⊓ J = I * J`, any `γ` and `ε` agree on `I ⊓ J`.

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

/-- The convolution is the `n`-th coefficient of the product of the exponential series. -/
theorem convolution_eq_coeff_exp_mul (n : ℕ) (x y : A) :
    convolution γ ε n x y = PowerSeries.coeff n (γ.exp x * ε.exp y) := by
  simp [convolution_def, PowerSeries.coeff_mul, exp]

/-- Exchanging the two structures and the two arguments leaves the convolution unchanged. -/
theorem convolution_comm (n : ℕ) (x y : A) : convolution γ ε n x y = convolution ε γ n y x := by
  rw [convolution_def, convolution_def, ← Nat.sum_antidiagonal_swap]
  exact sum_congr rfl fun k _ ↦ mul_comm _ _

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
  simp only [convolution_eq_coeff_exp_mul, γ.exp_add hx hx', ε.exp_add hy hy']
  rw [← PowerSeries.coeff_mul, mul_mul_mul_comm]

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
  rw [convolution_eq_coeff_exp_mul, convolution_eq_coeff_exp_mul, hx₀, hy₀, hexp, mul_assoc]

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

private theorem sup_eq_span_union : I ⊔ J = Ideal.span ((I : Set A) ∪ J) := by
  rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq]

/-- The divided power structure on `I ⊔ J` glued from divided power structures `γ` on `I` and `ε`
on `J` that agree on `I ⊓ J`. -/
noncomputable def glue (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w) : DividedPowers (I ⊔ J) :=
  (supPowers h).toDividedPowers sup_eq_span_union
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
  · refine IsDPMorphism.on_span (glue γ ε h) κ sup_eq_span_union ?_ ?_
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

end Glue

/-- If `I ⊓ J = I * J`, any divided power structures on `I` and on `J` agree on `I ⊓ J`. -/
theorem coincide_on_inf {A : Type*} [CommSemiring A] {I J : Ideal A} (γ : DividedPowers I)
    (ε : DividedPowers J) (hIJ : I ⊓ J = I * J) {n : ℕ} {w : A} (hw : w ∈ I ⊓ J) :
    γ.dpow n w = ε.dpow n w :=
  γ.coincide_on_smul ε (by rwa [Ideal.smul_eq_mul, ← hIJ])

end DividedPowers
