/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import TauCeti.NumberTheory.Padics.Complex.IntegralAway

import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Admissible combinations

Let `V` be a complex vector space, `(v x)_{x ∈ X}` a family of vectors of `V`, `A ⊆ X`, `q` and `d`
natural numbers, `B` a real number and `P` a proposition. A vector `z` is an *admissible
combination* of the `v x`, `x ∈ A`, with denominator `d` away from `q` and size `B` under `P` if
`z = ∑ₓ r x • v x` for a finitely supported family of coefficients `r` supported in `A`, such that
each `d * r x` is integral away from `q` (`TauCeti.integralAway`), and, if `P` holds,
`∑ₓ ‖σ (r x)‖ ≤ B` for every automorphism `σ` of `ℂ`.

Such combinations control at once the denominators of the coefficients at all primes not dividing
`q`, through every embedding `ℂ →+* ℂ_[ℓ]`, and the archimedean size of all their Galois
conjugates. The size is only bounded when `P` holds; taking for `P` a condition that may fail
allows one statement to bound sizes in some cases while still controlling denominators in all.

This file develops their closure properties. Admissible combinations are stable under
substitution: if each `v x` is itself an admissible combination of vectors `v' y`, then so is `z`,
with the product of the denominators and of the sizes. They are carried to admissible combinations
by linear maps, by bilinear maps (with the product of the denominators and of the sizes), by
multilinear maps and in particular to pure tensors of `PiTensorProduct`; they are stable under sums
and under multiplication by scalars integral away from `q` whose conjugates have absolute value at
most `1`, such as roots of unity, and the vectors `v x` may be replaced by root of unity multiples
of other vectors. Finally `d • z` lies in every module over a subring containing the elements
integral away from `q`, for instance over the ring `ι⁻¹(𝓞_ℂ_[ℓ])` for a prime `ℓ ∤ q` and
`ι : ℂ →+* ℂ_[ℓ]`, that contains the `v x`.

## Main definitions

* `TauCeti.IsAdmissibleCombination v A q d B P z`: `z` is an admissible combination of the `v x`,
  `x ∈ A`, with denominator `d` away from `q` and size `B` under `P`.

## Main results

* `TauCeti.isAdmissibleCombination_sum_smul`: a finite sum `∑ i ∈ s, c i • v (f i)` with
  controlled coefficients is an admissible combination.
* `TauCeti.IsAdmissibleCombination.trans`: substitution of admissible combinations.
* `TauCeti.IsAdmissibleCombination.map`, `TauCeti.IsAdmissibleCombination.map₂`,
  `TauCeti.IsAdmissibleCombination.multilinearMap`, `TauCeti.IsAdmissibleCombination.tprod`:
  images under linear, bilinear and multilinear maps, and pure tensors.
* `TauCeti.IsAdmissibleCombination.add`, `TauCeti.IsAdmissibleCombination.sum`,
  `TauCeti.IsAdmissibleCombination.smul`, `TauCeti.IsAdmissibleCombination.smul_of_isOfFinOrder`:
  sums and scalar multiples.
* `TauCeti.IsAdmissibleCombination.of_eq_isOfFinOrder_smul`: replacing the vectors by root of
  unity multiples of other vectors.
* `TauCeti.IsAdmissibleCombination.smul_mem`,
  `TauCeti.IsAdmissibleCombination.smul_mem_of_not_dvd`: integrality of `d • z`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/New/UpperBound/Seesaw/AdmissibleCombinations.lean` (declarations
  `New.Seesaw.IsAdmissibleCombination`, `New.Seesaw.IsAdmissibleCoeffs`,
  `New.Seesaw.IsAdmissibleCombination.bind`, `New.Seesaw.IsAdmissibleCombination.map_bilinear`,
  `New.Seesaw.IsAdmissibleCombination.pure`, `New.Seesaw.IsAdmissibleCombination.smul_mem`);
  Apache 2.0, Copyright 2026 Anthropic, PBC. The notion of admissible combination and the list of
  its closure properties follow the ones used there.
-/

public section

open Finsupp

namespace TauCeti

variable {X Y V V' W : Type*} [AddCommMonoid V] [Module ℂ V] [AddCommMonoid V'] [Module ℂ V']
  [AddCommMonoid W] [Module ℂ W]

/-- `z` is an *admissible combination* of the vectors `v x`, `x ∈ A`, with denominator `d` away
from `q` and size `B` under the condition `P`: `z = ∑ₓ r x • v x` for finitely supported
coefficients `r` vanishing outside `A`, with every `d * r x` integral away from `q`, and, if `P`
holds, `∑ₓ ‖σ (r x)‖ ≤ B` for every automorphism `σ` of `ℂ`. -/
def IsAdmissibleCombination (v : X → V) (A : Set X) (q d : ℕ) (B : ℝ) (P : Prop) (z : V) :
    Prop :=
  ∃ r : X →₀ ℂ, ↑r.support ⊆ A ∧ (∀ x, (d : ℂ) * r x ∈ integralAway ℂ q) ∧
    (P → ∀ σ : ℂ ≃+* ℂ, ∑ x ∈ r.support, ‖σ (r x)‖ ≤ B) ∧ linearCombination ℂ v r = z

variable {v : X → V} {A : Set X} {q d : ℕ} {B : ℝ} {P : Prop} {z : V}

/-- Unfolding `IsAdmissibleCombination`: the coefficients are a finitely supported `r : X →₀ ℂ`
with `linearCombination ℂ v r = z`. -/
theorem isAdmissibleCombination_iff :
    IsAdmissibleCombination v A q d B P z ↔
      ∃ r : X →₀ ℂ, ↑r.support ⊆ A ∧ (∀ x, (d : ℂ) * r x ∈ integralAway ℂ q) ∧
        (P → ∀ σ : ℂ ≃+* ℂ, ∑ x ∈ r.support, ‖σ (r x)‖ ≤ B) ∧ linearCombination ℂ v r = z :=
  Iff.rfl

/-- A finite sum `∑ i ∈ s, c i • v (f i)` with all `f i ∈ A`, all `d * c i` integral away from
`q`, and, under `P`, `∑ i ∈ s, ‖σ (c i)‖ ≤ B` for every automorphism `σ` of `ℂ`, is an admissible
combination of the `v x`, `x ∈ A`, with denominator `d` and size `B`. The indices `f i` need not be
distinct. -/
theorem isAdmissibleCombination_sum_smul {ι : Type*} (s : Finset ι) (f : ι → X) (c : ι → ℂ)
    (hf : ∀ i ∈ s, f i ∈ A) (hc : ∀ i ∈ s, (d : ℂ) * c i ∈ integralAway ℂ q)
    (hB : P → ∀ σ : ℂ ≃+* ℂ, ∑ i ∈ s, ‖σ (c i)‖ ≤ B) :
    IsAdmissibleCombination v A q d B P (∑ i ∈ s, c i • v (f i)) := by
  classical
  -- The coefficient at `x` is the sum of the `c i` over the fibre of `f` above `x`.
  set r : X →₀ ℂ := ∑ i ∈ s, single (f i) (c i)
  have hr (x : X) : r x = ∑ i ∈ s with f i = x, c i := by
    simp [r, Finset.sum_apply', single_apply, Finset.sum_filter]
  have hsupp : r.support ⊆ s.image f := fun x hx ↦ by
    obtain ⟨i, hi, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hr x ▸ mem_support_iff.1 hx)
    rw [Finset.mem_filter] at hi
    exact Finset.mem_image.2 ⟨i, hi⟩
  refine ⟨r, fun x hx ↦ ?_, fun x ↦ ?_, fun hP σ ↦ ?_, by simp [r, map_sum]⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (hsupp hx)
    exact hf i hi
  · rw [hr, Finset.mul_sum]
    exact Subring.sum_mem _ fun i hi ↦ hc i (Finset.mem_filter.1 hi).1
  · calc ∑ x ∈ r.support, ‖σ (r x)‖ ≤ ∑ x ∈ s.image f, ‖σ (r x)‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsupp fun _ _ _ ↦ norm_nonneg _
      _ ≤ ∑ x ∈ s.image f, ∑ i ∈ s with f i = x, ‖σ (c i)‖ := by
          gcongr with x
          rw [hr, map_sum]
          exact norm_sum_le _ _
      _ = ∑ i ∈ s, ‖σ (c i)‖ :=
          Finset.sum_fiberwise_of_maps_to (fun i hi ↦ Finset.mem_image_of_mem f hi) _
      _ ≤ B := hB hP σ

/-- `0` is an admissible combination of any family, of any size that is nonnegative under `P`. -/
theorem isAdmissibleCombination_zero (hB : P → 0 ≤ B) :
    IsAdmissibleCombination v A q d B P 0 :=
  ⟨0, by simp, by simp, fun hP _ ↦ by simpa using hB hP, map_zero _⟩

/-- A vector `v x` with `x ∈ A` is an admissible combination of the `v x`, `x ∈ A`, of any
denominator and of any size that is at least `1` under `P`. -/
theorem isAdmissibleCombination_of_mem {x : X} (hx : x ∈ A) (hB : P → 1 ≤ B) :
    IsAdmissibleCombination v A q d B P (v x) := by
  simpa using isAdmissibleCombination_sum_smul (v := v) {x} id (fun _ ↦ 1) (by simpa using hx)
    (by simp [natCast_mem]) (fun hP σ ↦ by simpa using hB hP)

namespace IsAdmissibleCombination

/-- An admissible combination is a finite sum over the support of its coefficients. -/
private theorem exists_sum_smul (h : IsAdmissibleCombination v A q d B P z) :
    ∃ r : X →₀ ℂ, ↑r.support ⊆ A ∧ (∀ x, (d : ℂ) * r x ∈ integralAway ℂ q) ∧
      (P → ∀ σ : ℂ ≃+* ℂ, ∑ x ∈ r.support, ‖σ (r x)‖ ≤ B) ∧
        ∑ x ∈ r.support, r x • v x = z := by
  obtain ⟨r, hA, hd, hB, rfl⟩ := h
  exact ⟨r, hA, hd, hB, by rw [linearCombination_apply, Finsupp.sum]⟩

/-- The size of an admissible combination is nonnegative when the condition holds. -/
theorem nonneg (h : IsAdmissibleCombination v A q d B P z) (hP : P) : 0 ≤ B := by
  obtain ⟨r, -, -, hB, -⟩ := h
  exact (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _).trans (hB hP (RingEquiv.refl ℂ))

/-- Admissibility is preserved by enlarging the index set, replacing `q` by a multiple and `d` by
a multiple, enlarging the size, and strengthening the condition. -/
theorem mono {A' : Set X} {q' d' : ℕ} {B' : ℝ} {P' : Prop}
    (h : IsAdmissibleCombination v A q d B P z) (hA : A ⊆ A') (hq : q ∣ q') (hd : d ∣ d')
    (hB : B ≤ B') (hP : P' → P) : IsAdmissibleCombination v A' q' d' B' P' z := by
  obtain ⟨r, hrA, hrd, hrB, rfl⟩ := h
  obtain ⟨k, rfl⟩ := hd
  refine ⟨r, hrA.trans hA, fun x ↦ ?_, fun hP' σ ↦ (hrB (hP hP') σ).trans hB, rfl⟩
  rw [Nat.cast_mul, mul_comm (d : ℂ), mul_assoc]
  exact integralAway_mono hq (Subring.mul_mem _ (natCast_mem _ k) (hrd x))

/-- The sum of two admissible combinations with the same denominator is an admissible combination
whose size is the sum of the sizes. -/
theorem add {z' : V} {B' : ℝ} (h : IsAdmissibleCombination v A q d B P z)
    (h' : IsAdmissibleCombination v A q d B' P z') :
    IsAdmissibleCombination v A q d (B + B') P (z + z') := by
  obtain ⟨r, hrA, hrd, hrB, rfl⟩ := h.exists_sum_smul
  obtain ⟨r', hrA', hrd', hrB', rfl⟩ := h'.exists_sum_smul
  simpa [Finset.sum_disjSum] using isAdmissibleCombination_sum_smul (v := v)
    (r.support.disjSum r'.support) (Sum.elim id id) (Sum.elim r r')
    (by rintro (x | x) hx
        exacts [hrA (Finset.inl_mem_disjSum.1 hx), hrA' (Finset.inr_mem_disjSum.1 hx)])
    (by rintro (x | x) _; exacts [hrd x, hrd' x])
    (fun hP σ ↦ by simpa [Finset.sum_disjSum] using add_le_add (hrB hP σ) (hrB' hP σ))

/-- A finite sum of admissible combinations with the same denominator is an admissible combination
whose size is the sum of the sizes. -/
theorem sum {ι : Type*} {s : Finset ι} {z : ι → V} {B : ι → ℝ}
    (h : ∀ i ∈ s, IsAdmissibleCombination v A q d (B i) P (z i)) :
    IsAdmissibleCombination v A q d (∑ i ∈ s, B i) P (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isAdmissibleCombination_zero fun _ ↦ le_rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- Admissible combinations are stable under multiplication by a scalar `c` integral away from `q`
all of whose conjugates have absolute value at most `1` under `P`, for instance by `0` or by a root
of unity (`IsAdmissibleCombination.smul_of_isOfFinOrder`). -/
theorem smul {c : ℂ} (h : IsAdmissibleCombination v A q d B P z) (hc : c ∈ integralAway ℂ q)
    (hcσ : P → ∀ σ : ℂ ≃+* ℂ, ‖σ c‖ ≤ 1) : IsAdmissibleCombination v A q d B P (c • z) := by
  obtain ⟨r, hrA, hrd, hrB, rfl⟩ := h.exists_sum_smul
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  refine isAdmissibleCombination_sum_smul _ _ _ (fun x hx ↦ hrA hx)
    (fun x _ ↦ by rw [mul_left_comm]; exact Subring.mul_mem _ hc (hrd x)) fun hP σ ↦ ?_
  refine (Finset.sum_le_sum fun x _ ↦ ?_).trans (hrB hP σ)
  rw [map_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hcσ hP σ)

/-- Admissible combinations are stable under multiplication by a root of unity. -/
theorem smul_of_isOfFinOrder {ζ : ℂ} (h : IsAdmissibleCombination v A q d B P z)
    (hζ : IsOfFinOrder ζ) : IsAdmissibleCombination v A q d B P (ζ • z) :=
  h.smul (mem_integralAway_of_isIntegral hζ.isIntegral) fun _ σ ↦
    ((σ : ℂ →* ℂ).isOfFinOrder hζ).norm_eq_one.le

/-- The negative of an admissible combination is an admissible combination. -/
theorem neg {V : Type*} [AddCommGroup V] [Module ℂ V] {v : X → V} {z : V}
    (h : IsAdmissibleCombination v A q d B P z) : IsAdmissibleCombination v A q d B P (-z) := by
  simpa using h.smul (c := -1) (neg_mem (one_mem _)) fun _ σ ↦ by simp

/-- The difference of two admissible combinations with the same denominator is an admissible
combination whose size is the sum of the sizes. -/
theorem sub {V : Type*} [AddCommGroup V] [Module ℂ V] {v : X → V} {z z' : V} {B' : ℝ}
    (h : IsAdmissibleCombination v A q d B P z) (h' : IsAdmissibleCombination v A q d B' P z') :
    IsAdmissibleCombination v A q d (B + B') P (z - z') := by
  simpa [sub_eq_add_neg] using h.add h'.neg

/-- A linear map carries an admissible combination of the `v x` to an admissible combination of
the images `f (v x)`, with the same denominator and size. -/
theorem map (h : IsAdmissibleCombination v A q d B P z) (f : V →ₗ[ℂ] W) :
    IsAdmissibleCombination (f ∘ v) A q d B P (f z) := by
  obtain ⟨r, hrA, hrd, hrB, rfl⟩ := h
  exact ⟨r, hrA, hrd, hrB, (apply_linearCombination ℂ f v r).symm⟩

/-- **Substitution.** If `z` is an admissible combination of the `v x`, `x ∈ A`, with denominator
`d` and size `B`, and each `v x`, `x ∈ A`, is an admissible combination of the `v' y`, `y ∈ A'`,
with denominator `d'` and size `B'`, then `z` is an admissible combination of the `v' y`,
`y ∈ A'`, with any denominator `e` divisible by `d * d'` and any size `C ≥ B * |B'|`. -/
theorem trans {v' : Y → V} {A' : Set Y} {d' e : ℕ} {B' C : ℝ}
    (h : IsAdmissibleCombination v A q d B P z)
    (hv : ∀ x ∈ A, IsAdmissibleCombination v' A' q d' B' P (v x)) (he : d * d' ∣ e)
    (hC : B * |B'| ≤ C) : IsAdmissibleCombination v' A' q e C P z := by
  classical
  obtain ⟨r, hrA, hrd, hrB, rfl⟩ := h.exists_sum_smul
  choose! s hsA hsd hsB hs using fun x hx ↦ (hv x hx).exists_sum_smul
  obtain ⟨k, rfl⟩ := he
  have hz : ∑ x ∈ r.support, r x • v x =
      ∑ p ∈ r.support.sigma fun x ↦ (s x).support, (r p.1 * s p.1 p.2) • v' p.2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [← hs x (hrA hx), Finset.smul_sum]
    simp_rw [smul_smul]
  rw [hz]
  refine isAdmissibleCombination_sum_smul _ _ _ (fun p hp ↦ ?_) (fun p hp ↦ ?_) fun hP σ ↦ ?_
  · rw [Finset.mem_sigma] at hp
    exact hsA p.1 (hrA hp.1) hp.2
  · rw [Finset.mem_sigma] at hp
    have := Subring.mul_mem _ (natCast_mem _ k)
      (Subring.mul_mem _ (hrd p.1) (hsd p.1 (hrA hp.1) p.2))
    convert this using 1
    push_cast
    ring
  · rw [Finset.sum_sigma]
    calc ∑ x ∈ r.support, ∑ y ∈ (s x).support, ‖σ (r x * s x y)‖
        = ∑ x ∈ r.support, ‖σ (r x)‖ * ∑ y ∈ (s x).support, ‖σ (s x y)‖ := by
          simp [Finset.mul_sum]
      _ ≤ ∑ x ∈ r.support, ‖σ (r x)‖ * |B'| := by
          gcongr with x hx
          exact (hsB x (hrA hx) hP σ).trans (le_abs_self B')
      _ ≤ B * |B'| := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (hrB hP σ) (abs_nonneg B')
      _ ≤ C := hC

/-- **Root of unity multiples.** If each `v x`, `x ∈ A`, is a root of unity times some `v' y`,
`y ∈ A'`, then an admissible combination of the `v x` is an admissible combination of the `v' y`
with the same denominator and size. -/
theorem of_eq_isOfFinOrder_smul {v' : Y → V} {A' : Set Y}
    (h : IsAdmissibleCombination v A q d B P z)
    (hv : ∀ x ∈ A, ∃ y ∈ A', ∃ ζ : ℂ, IsOfFinOrder ζ ∧ v x = ζ • v' y) :
    IsAdmissibleCombination v' A' q d B P z :=
  h.trans (d' := 1) (B' := 1) (fun x hx ↦ by
    obtain ⟨y, hy, ζ, hζ, hxy⟩ := hv x hx
    exact hxy ▸ (isAdmissibleCombination_of_mem hy fun _ ↦ le_rfl).smul_of_isOfFinOrder hζ)
    (by simp) (by simp)

/-- **Bilinear maps.** If `z` and `z'` are admissible combinations of the `v x`, `x ∈ A`, and of
the `v' y`, `y ∈ A'`, with denominators `d`, `d'` and sizes `B`, `B'`, then for a bilinear map `b`,
`b z z'` is an admissible combination of the `b (v x) (v' y)`, `(x, y) ∈ A ×ˢ A'`, with
denominator `d * d'` and size `B * |B'|`. -/
theorem map₂ {v' : Y → V'} {A' : Set Y} {d' : ℕ} {B' : ℝ} {z' : V'}
    (h : IsAdmissibleCombination v A q d B P z) (h' : IsAdmissibleCombination v' A' q d' B' P z')
    (b : V →ₗ[ℂ] V' →ₗ[ℂ] W) :
    IsAdmissibleCombination (fun p : X × Y ↦ b (v p.1) (v' p.2)) (A ×ˢ A') q (d * d')
      (B * |B'|) P (b z z') := by
  obtain ⟨r, hrA, hrd, hrB, rfl⟩ := h.exists_sum_smul
  obtain ⟨r', hrA', hrd', hrB', rfl⟩ := h'.exists_sum_smul
  have hz : b (∑ x ∈ r.support, r x • v x) (∑ y ∈ r'.support, r' y • v' y) =
      ∑ p ∈ r.support ×ˢ r'.support, (r p.1 * r' p.2) • b (v p.1) (v' p.2) := by
    rw [Finset.sum_product, LinearMap.map_sum₂]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [LinearMap.map_smul₂, map_sum, Finset.smul_sum]
    simp_rw [map_smul, smul_smul]
  rw [hz]
  refine isAdmissibleCombination_sum_smul _ id _ (fun p hp ↦ ?_) (fun p _ ↦ ?_) fun hP σ ↦ ?_
  · rw [Finset.mem_product] at hp
    exact ⟨hrA hp.1, hrA' hp.2⟩
  · rw [Nat.cast_mul, mul_mul_mul_comm]
    exact Subring.mul_mem _ (hrd p.1) (hrd' p.2)
  · have hB := (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _).trans (hrB hP σ)
    calc ∑ p ∈ r.support ×ˢ r'.support, ‖σ (r p.1 * r' p.2)‖
        = (∑ x ∈ r.support, ‖σ (r x)‖) * ∑ y ∈ r'.support, ‖σ (r' y)‖ := by
          simp [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ B * |B'| :=
          mul_le_mul (hrB hP σ) ((hrB' hP σ).trans (le_abs_self B'))
            (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hB

section Multilinear

variable {ι : Type*} [Fintype ι] {κ : ι → Type*} {M : ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module ℂ (M i)] {w : ∀ i, κ i → M i} {C : ∀ i, Set (κ i)}
  {e : ι → ℕ} {D : ι → ℝ} {m : ∀ i, M i}

/-- **Multilinear maps.** If each `m i` is an admissible combination of the `w i y`, `y ∈ C i`,
with denominator `e i` and size `D i`, then for a multilinear map `F`, `F m` is an admissible
combination of the `F (fun i ↦ w i (y i))`, `y ∈ Set.univ.pi C`, with denominator `∏ i, e i` and
size `∏ i, |D i|`. -/
theorem multilinearMap (h : ∀ i, IsAdmissibleCombination (w i) (C i) q (e i) (D i) P (m i))
    (F : (Π i, M i) →ₘₗ[ℂ] W) :
    IsAdmissibleCombination (fun y : ∀ i, κ i ↦ F fun i ↦ w i (y i)) (Set.univ.pi C) q
      (∏ i, e i) (∏ i, |D i|) P (F m) := by
  classical
  choose r hrC hrd hrD hr using fun i ↦ (h i).exists_sum_smul
  have hm : m = fun i ↦ ∑ y ∈ (r i).support, r i y • w i y := funext fun i ↦ (hr i).symm
  rw [hm, F.map_sum_finset]
  simp_rw [F.map_smul_univ]
  refine isAdmissibleCombination_sum_smul _ id _ (fun y hy ↦ ?_) (fun y _ ↦ ?_) fun hP σ ↦ ?_
  · rw [Fintype.mem_piFinset] at hy
    exact fun i _ ↦ hrC i (hy i)
  · rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Subring.prod_mem _ fun i _ ↦ hrd i (y i)
  · calc ∑ y ∈ Fintype.piFinset fun i ↦ (r i).support, ‖σ (∏ i, r i (y i))‖
        = ∏ i, ∑ y ∈ (r i).support, ‖σ (r i y)‖ := by
          rw [Finset.prod_univ_sum]
          simp [map_prod, norm_prod]
      _ ≤ ∏ i, |D i| :=
          Finset.prod_le_prod₀ (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
            fun i _ ↦ (hrD i hP σ).trans (le_abs_self _)

/-- **Pure tensors.** If each `m i` is an admissible combination of the `w i y`, `y ∈ C i`, with
denominator `d` and size `B`, then the pure tensor `⨂ₜ i, m i` is an admissible combination of the
pure tensors `⨂ₜ i, w i (y i)`, `y ∈ Set.univ.pi C`, with denominator `d ^ card ι` and size
`|B| ^ card ι`. -/
theorem tprod (h : ∀ i, IsAdmissibleCombination (w i) (C i) q d B P (m i)) :
    IsAdmissibleCombination (fun y : ∀ i, κ i ↦ ⨂ₜ[ℂ] i, w i (y i)) (Set.univ.pi C) q
      (d ^ Fintype.card ι) (|B| ^ Fintype.card ι) P (⨂ₜ[ℂ] i, m i) := by
  simpa using multilinearMap h (PiTensorProduct.tprod ℂ)

end Multilinear

/-- **Integrality.** If `z` is an admissible combination of the `v x`, `x ∈ A`, with denominator
`d` away from `q`, then `d • z` lies in every `S`-submodule containing the `v x`, `x ∈ A`, for
every subring `S` of `ℂ` containing the numbers integral away from `q`. -/
theorem smul_mem (h : IsAdmissibleCombination v A q d B P z) {S : Subring ℂ}
    (hS : integralAway ℂ q ≤ S) (N : Submodule S V) (hN : ∀ x ∈ A, v x ∈ N) :
    (d : ℂ) • z ∈ N := by
  obtain ⟨r, hrA, hrd, -, rfl⟩ := h.exists_sum_smul
  rw [Finset.smul_sum]
  refine N.sum_mem fun x hx ↦ ?_
  rw [smul_smul]
  exact N.smul_mem (⟨_, hS (hrd x)⟩ : S) (hN x (hrA hx))

/-- **Integrality at a prime.** If `z` is an admissible combination of the `v x`, `x ∈ A`, with
denominator `d` away from `q`, `ℓ ∤ q` is a prime and `ι : ℂ →+* ℂ_[ℓ]`, then `d • z` lies in every
module over the ring `ι⁻¹(𝓞_ℂ_[ℓ])` of the `c ∈ ℂ` with `‖ι c‖ ≤ 1` that contains the `v x`. -/
theorem smul_mem_of_not_dvd (h : IsAdmissibleCombination v A q d B P z) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ¬ℓ ∣ q) (ι : ℂ →+* ℂ_[ℓ]) (N : Submodule ((𝓞_ℂ_[ℓ]).toSubring.comap ι) V)
    (hN : ∀ x ∈ A, v x ∈ N) : (d : ℂ) • z ∈ N :=
  h.smul_mem (integralAway_le_comap hℓ ι) N hN

end IsAdmissibleCombination

-- Sanity checks: both conditions are effective. With `v = 1` on a point, `1 / 2` is not an
-- admissible combination with denominator `1` away from `1`, since `1 / 2` is not integral away
-- from `1`, and `1` has no admissible presentation of size `1 / 2`.
example :
    ¬IsAdmissibleCombination (fun _ : Unit ↦ (1 : ℂ)) Set.univ 1 1 0 False ((2 : ℕ) : ℂ)⁻¹ := by
  rintro ⟨r, -, hrd, -, hr⟩
  rw [linearCombination_unique, smul_eq_mul, mul_one] at hr
  have h2 := hrd default
  rw [Nat.cast_one, one_mul, hr, inv_natCast_mem_integralAway_iff two_ne_zero] at h2
  exact Nat.prime_two.not_dvd_one (h2 2 Nat.prime_two dvd_rfl)

example : ¬IsAdmissibleCombination (fun _ : Unit ↦ (1 : ℂ)) Set.univ 0 0 2⁻¹ True 1 := by
  rintro ⟨r, -, -, hrB, hr⟩
  rw [linearCombination_unique, smul_eq_mul, mul_one] at hr
  have hd : default ∈ r.support := mem_support_iff.2 (hr ▸ one_ne_zero)
  have h := (Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) hd).trans
    (hrB trivial (RingEquiv.refl ℂ))
  rw [hr] at h
  norm_num at h

end TauCeti
