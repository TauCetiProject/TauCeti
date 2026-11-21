/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
public import TauCeti.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.CanonicalProduct.PrimaryProduct

/-!
# Convergence and multiplicities of genus-one canonical products

If the complex slopes `a i` have summable squared norms, the unordered product
`∏' i, Complex.weierstrassFactor 1 (a i * z)` converges uniformly on compact sets and
defines an entire function. Its zeros are exactly the roots of its factors, and its analytic
order counts the factors vanishing there. No enumeration or countability assumption on the
index type is needed.

Natural multiplicities are allowed under the weighted condition `∑ i, m i * ‖a i‖² < ∞`.
The analytic order counts the repeated vanishing factors; for injective slopes this is exactly
the prescribed multiplicity.
These are the convergence and divisor ingredients of Hadamard factorization at order one,
obtained by specializing the variable-genus primary-product theorems in
`TauCeti.Analysis.Complex.CanonicalProduct.PrimaryProduct`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
-/

public section

open Complex Filter Metric Topology
open scoped BigOperators

namespace Complex

variable {ι : Type*} (a : ι → ℂ) (ha : Summable (fun i ↦ ‖a i‖ ^ 2))

include ha

private theorem summable_div_pow_inv :
    ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖(a i)⁻¹‖) ^ (1 + 1) := by
  intro R _
  have heq (i : ι) : (R / ‖(a i)⁻¹‖) ^ (1 + 1) = R ^ 2 * ‖a i‖ ^ 2 := by
    rw [norm_inv, div_inv_eq_mul, mul_pow]
  simpa only [heq] using ha.mul_left (R ^ 2)

omit ha in
private theorem weierstrassFactor_one_mul_eq_div_inv (i : ι) (z : ℂ) :
    weierstrassFactor 1 (a i * z) = weierstrassFactor 1 (z / (a i)⁻¹) := by
  rw [div_inv_eq_mul, mul_comm]

/-- Square-summable slopes give uniform convergence of the genus-one product on every bounded
set. -/
theorem hasProdUniformlyOn_weierstrassFactor_one {K : Set ℂ} (hK : Bornology.IsBounded K) :
    HasProdUniformlyOn (fun i z ↦ weierstrassFactor 1 (a i * z))
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z)) K := by
  have h := (hasProdUniformlyOn_weierstrassFactor_div (a := fun i ↦ (a i)⁻¹) (p := fun _ ↦ 1)
    (summable_div_pow_inv a ha) hK.isCompact_closure).mono subset_closure
  simpa only [← weierstrassFactor_one_mul_eq_div_inv a] using h

/-- The genus-one product converges locally uniformly on the whole plane. -/
theorem hasProdLocallyUniformlyOn_weierstrassFactor_one :
    HasProdLocallyUniformlyOn (fun i z ↦ weierstrassFactor 1 (a i * z))
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z)) Set.univ := by
  simpa only [← weierstrassFactor_one_mul_eq_div_inv a] using
    hasProdLocallyUniformlyOn_weierstrassFactor_div (a := fun i ↦ (a i)⁻¹) (p := fun _ ↦ 1)
      (summable_div_pow_inv a ha)

/-- A genus-one product with square-summable slopes is entire. -/
@[fun_prop]
theorem differentiable_tprod_weierstrassFactor_one :
    Differentiable ℂ (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z)) := by
  simpa only [← weierstrassFactor_one_mul_eq_div_inv a] using
    differentiable_tprod_weierstrassFactor_div (a := fun i ↦ (a i)⁻¹) (p := fun _ ↦ 1)
      (summable_div_pow_inv a ha)

/-- The deviations of the factors from one form an absolutely summable family at each point. -/
theorem summable_norm_weierstrassFactor_one_sub_one (z : ℂ) :
    Summable (fun i ↦ ‖weierstrassFactor 1 (a i * z) - 1‖) := by
  simpa only [← weierstrassFactor_one_mul_eq_div_inv a] using
    summable_norm_weierstrassFactor_div_sub_one (a := fun i ↦ (a i)⁻¹) (p := fun _ ↦ 1)
      (summable_div_pow_inv a ha) z

omit ha in
private theorem tprod_weierstrassFactor_one_eq_subtype (w : ℂ) :
    (∏' i, weierstrassFactor 1 (a i * w)) =
      ∏' i : {i // a i ≠ 0}, weierstrassFactor 1 (w / (a i)⁻¹) := by
  rw [← tprod_subtype_eq_of_mulSupport_subset (s := {i | a i ≠ 0}) fun i hi ↦ ?_]
  · exact tprod_congr fun i ↦ weierstrassFactor_one_mul_eq_div_inv a i w
  · by_contra hai
    simp only [Set.mem_ofPred_eq, not_not] at hai
    exact hi (by simp [hai])

/-- The genus-one product vanishes exactly at a zero of one of its factors. -/
theorem tprod_weierstrassFactor_one_eq_zero_iff (z : ℂ) :
    (∏' i, weierstrassFactor 1 (a i * z)) = 0 ↔ ∃ i, a i * z = 1 := by
  rw [tprod_weierstrassFactor_one_eq_subtype a z,
    tprod_weierstrassFactor_div_eq_zero_iff (a := fun i : {i // a i ≠ 0} ↦ (a i)⁻¹)
      (p := fun _ ↦ 1) (fun i ↦ inv_ne_zero i.property)
      (fun R hR ↦ (summable_div_pow_inv a ha R hR).subtype _)]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← hi, mul_inv_cancel₀ i.property]⟩
  · rintro ⟨i, hi⟩
    have hai : a i ≠ 0 := fun h ↦ by simp [h] at hi
    exact ⟨⟨i, hai⟩, (eq_inv_of_mul_eq_one_right hi).symm⟩

/-- Only finitely many factors can vanish at a fixed point. -/
theorem finite_weierstrassFactor_one_roots (z : ℂ) :
    {i | a i * z = 1}.Finite := by
  have hf := finite_setOf_eq_of_summable_div_pow (a := fun i : {i // a i ≠ 0} ↦ (a i)⁻¹)
    (p := fun _ ↦ 1) (fun i ↦ inv_ne_zero i.property)
    (fun R hR ↦ (summable_div_pow_inv a ha R hR).subtype _) z
  refine (hf.image Subtype.val).subset fun i hi ↦ ?_
  have hai : a i ≠ 0 := fun h ↦ by simp [h] at hi
  exact ⟨⟨i, hai⟩, (eq_inv_of_mul_eq_one_right hi).symm, rfl⟩

/-- The order of the product counts all factors vanishing at that point. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' i, weierstrassFactor 1 (a i * w)) z =
      ({i | a i * z = 1}.ncard : ℕ∞) := by
  have heq : (fun w ↦ ∏' i, weierstrassFactor 1 (a i * w)) =
      fun w ↦ ∏' i : {i // a i ≠ 0}, weierstrassFactor 1 (w / (a i)⁻¹) :=
    funext (tprod_weierstrassFactor_one_eq_subtype a)
  rw [heq, analyticOrderAt_tprod_weierstrassFactor_div
    (a := fun i : {i // a i ≠ 0} ↦ (a i)⁻¹) (p := fun _ ↦ 1)
    (fun i ↦ inv_ne_zero i.property)
    (fun R hR ↦ (summable_div_pow_inv a ha R hR).subtype _) z]
  congr 1
  refine Set.ncard_congr (fun i _ ↦ (i : ι)) (fun i hi ↦ ?_)
    (fun _ _ _ _ h ↦ Subtype.ext h) fun i hi ↦ ?_
  · rw [Set.mem_ofPred_eq, ← (hi : (a i)⁻¹ = z), mul_inv_cancel₀ i.property]
  · have hai : a i ≠ 0 := fun h ↦ by simp [h] at hi
    exact ⟨⟨i, hai⟩, (eq_inv_of_mul_eq_one_right hi).symm, rfl⟩

/-- The product order is the cardinality of any finite set containing exactly its vanishing
factors. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one_of_finset {z : ℂ} (s : Finset ι)
    (hs : ∀ i, a i * z = 1 ↔ i ∈ s) :
    analyticOrderAt (fun w ↦ ∏' i, weierstrassFactor 1 (a i * w)) z = s.card := by
  rw [analyticOrderAt_tprod_weierstrassFactor_one a ha z, show {i | a i * z = 1} = (s : Set ι) from
    Set.ext hs, Set.ncard_coe_finset]

end Complex

namespace Complex

variable {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
  (hm : Summable (fun i ↦ (m i : ℝ) * ‖a i‖ ^ 2))

private theorem weierstrassFactor_one_pow_eq_div_inv (i : ι) (z : ℂ) :
    weierstrassFactor 1 (a i * z) ^ m i =
      weierstrassFactor 1 (z / (a i)⁻¹) ^ (if a i = 0 then 0 else m i) := by
  by_cases hai : a i = 0
  · simp [hai]
  · simp [hai, div_inv_eq_mul, mul_comm]

private theorem inv_ne_zero_of_ite_ne_zero (i : ι)
    (hi : (if a i = 0 then 0 else m i) ≠ 0) : (a i)⁻¹ ≠ 0 := by
  split_ifs at hi with h
  · exact (hi rfl).elim
  · exact inv_ne_zero h

include hm

private theorem summable_ite_mul_div_pow_inv :
    ∀ R : ℝ, 0 < R → Summable fun i ↦
      ((if a i = 0 then 0 else m i : ℕ) : ℝ) * (R / ‖(a i)⁻¹‖) ^ (1 + 1) := by
  intro R _
  have heq (i : ι) :
      ((if a i = 0 then 0 else m i : ℕ) : ℝ) * (R / ‖(a i)⁻¹‖) ^ (1 + 1) =
        R ^ 2 * ((m i : ℝ) * ‖a i‖ ^ 2) := by
    by_cases hai : a i = 0
    · simp [hai]
    · simp only [hai, ↓reduceIte, norm_inv, div_inv_eq_mul, mul_pow]
      ring
  simpa only [heq] using hm.mul_left (R ^ 2)

/-- A product with natural multiplicities is entire under weighted square summability. -/
@[fun_prop]
theorem differentiable_tprod_weierstrassFactor_one_pow :
    Differentiable ℂ (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) := by
  simpa only [← weierstrassFactor_one_pow_eq_div_inv a m] using
    differentiable_tprod_weierstrassFactor_div_pow (a := fun i ↦ (a i)⁻¹) (p := fun _ ↦ 1)
      (m := fun i ↦ if a i = 0 then 0 else m i) (summable_ite_mul_div_pow_inv a m hm)

/-- With arbitrary repeated slopes, the order counts the vanishing factors with their
natural multiplicities, represented by the finite fibers of the multiplicity family. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one_pow (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' j, weierstrassFactor 1 (a j * w) ^ m j) z =
      ({p : Σ j, Fin (m j) | a p.1 * z = 1}.ncard : ℕ∞) := by
  have heq : (fun w ↦ ∏' j, weierstrassFactor 1 (a j * w) ^ m j) =
      fun w ↦ ∏' j, weierstrassFactor 1 (w / (a j)⁻¹) ^ (if a j = 0 then 0 else m j) := by
    ext w
    exact tprod_congr fun j ↦ weierstrassFactor_one_pow_eq_div_inv a m j w
  rw [heq, analyticOrderAt_tprod_weierstrassFactor_div_pow (a := fun j ↦ (a j)⁻¹)
    (p := fun _ ↦ 1) (m := fun j ↦ if a j = 0 then 0 else m j)
    (inv_ne_zero_of_ite_ne_zero a m) (summable_ite_mul_div_pow_inv a m hm) z]
  congr 1
  refine Set.ncard_congr
    (fun (p : Σ j, Fin (if a j = 0 then 0 else m j)) _ ↦
      (⟨p.1, Fin.cast (ite_eq_right_iff.mpr fun h ↦ absurd p.2.isLt (by simp [h])) p.2⟩ :
        Σ j, Fin (m j)))
    (fun p hp ↦ ?_) (fun p q _ _ hpq ↦ ?_) (fun p hp ↦ ?_)
  · have hap : a p.1 ≠ 0 := fun h ↦ by simpa [h] using p.2.isLt
    rw [Set.mem_ofPred_eq] at hp ⊢
    rw [← hp, mul_inv_cancel₀ hap]
  · rcases p with ⟨i, k⟩
    rcases q with ⟨j, l⟩
    simp only [Sigma.mk.inj_iff] at hpq
    rcases hpq with ⟨rfl, hkl⟩
    simp only [heq_eq_eq, Fin.cast_inj] at hkl
    subst hkl
    rfl
  · have hap : a p.1 ≠ 0 := fun h ↦ by simp [h] at hp
    refine ⟨⟨p.1, Fin.cast (ite_eq_right_iff.mpr fun h ↦ absurd h hap).symm p.2⟩,
      (eq_inv_of_mul_eq_one_right hp).symm, ?_⟩
    cases p
    rfl

/-- For distinct slopes, the prescribed multiplicity is the exact order at the corresponding
root. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one_pow_of_injective {z : ℂ} {i : ι}
    (ha : Function.Injective a) (hi : a i * z = 1) :
    analyticOrderAt (fun w ↦ ∏' j, weierstrassFactor 1 (a j * w) ^ m j) z = m i := by
  have hai : a i ≠ 0 := fun h ↦ by simp [h] at hi
  have hzi : z = (a i)⁻¹ := eq_inv_of_mul_eq_one_right hi
  have heq : (fun w ↦ ∏' j, weierstrassFactor 1 (a j * w) ^ m j) =
      fun w ↦ ∏' j, weierstrassFactor 1 (w / (a j)⁻¹) ^ (if a j = 0 then 0 else m j) := by
    ext w
    exact tprod_congr fun j ↦ weierstrassFactor_one_pow_eq_div_inv a m j w
  rw [heq, hzi]
  simpa only [hai, ↓reduceIte] using analyticOrderAt_tprod_weierstrassFactor_div_pow_of_injective
    (a := fun j ↦ (a j)⁻¹) (p := fun _ ↦ 1) (m := fun j ↦ if a j = 0 then 0 else m j)
    (inv_ne_zero_of_ite_ne_zero a m) (summable_ite_mul_div_pow_inv a m hm)
    (inv_injective.comp ha) i

/-- Products with natural multiplicities converge uniformly on every bounded set. -/
theorem hasProdUniformlyOn_weierstrassFactor_one_pow {K : Set ℂ} (hK : Bornology.IsBounded K) :
    HasProdUniformlyOn (fun i z ↦ weierstrassFactor 1 (a i * z) ^ m i)
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) K := by
  have h := (hasProdUniformlyOn_weierstrassFactor_div_pow (a := fun i ↦ (a i)⁻¹) (p := fun _ ↦ 1)
    (m := fun i ↦ if a i = 0 then 0 else m i) (summable_ite_mul_div_pow_inv a m hm)
    hK.isCompact_closure).mono subset_closure
  simpa only [← weierstrassFactor_one_pow_eq_div_inv a m] using h

/-- Products with natural multiplicities converge locally uniformly on the whole plane. -/
theorem hasProdLocallyUniformlyOn_weierstrassFactor_one_pow :
    HasProdLocallyUniformlyOn (fun i z ↦ weierstrassFactor 1 (a i * z) ^ m i)
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) Set.univ := by
  simpa only [← weierstrassFactor_one_pow_eq_div_inv a m] using
    hasProdLocallyUniformlyOn_weierstrassFactor_div_pow (a := fun i ↦ (a i)⁻¹) (p := fun _ ↦ 1)
      (m := fun i ↦ if a i = 0 then 0 else m i) (summable_ite_mul_div_pow_inv a m hm)

/-- The weighted product vanishes exactly at a root whose prescribed multiplicity is nonzero. -/
theorem tprod_weierstrassFactor_one_pow_eq_zero_iff (z : ℂ) :
    (∏' i, weierstrassFactor 1 (a i * z) ^ m i) = 0 ↔
      ∃ i, m i ≠ 0 ∧ a i * z = 1 := by
  have heq : (∏' i, weierstrassFactor 1 (a i * z) ^ m i) =
      ∏' i, weierstrassFactor 1 (z / (a i)⁻¹) ^ (if a i = 0 then 0 else m i) :=
    tprod_congr fun i ↦ weierstrassFactor_one_pow_eq_div_inv a m i z
  rw [heq, tprod_weierstrassFactor_div_pow_eq_zero_iff (a := fun i ↦ (a i)⁻¹) (p := fun _ ↦ 1)
    (m := fun i ↦ if a i = 0 then 0 else m i) (inv_ne_zero_of_ite_ne_zero a m)
    (summable_ite_mul_div_pow_inv a m hm)]
  constructor
  · rintro ⟨i, hmi, hi⟩
    have hai : a i ≠ 0 := fun h ↦ by simp [h] at hmi
    simp only [hai, ↓reduceIte] at hmi
    exact ⟨i, hmi, by rw [← hi, mul_inv_cancel₀ hai]⟩
  · rintro ⟨i, hmi, hi⟩
    have hai : a i ≠ 0 := fun h ↦ by simp [h] at hi
    exact ⟨i, by simp [hai, hmi], (eq_inv_of_mul_eq_one_right hi).symm⟩

end Complex

