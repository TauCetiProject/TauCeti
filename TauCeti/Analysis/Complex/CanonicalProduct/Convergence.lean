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
import TauCeti.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Convergence and multiplicities of genus-one canonical products

If the complex slopes `a i` have summable squared norms, the unordered product
`∏' i, Complex.weierstrassFactor 1 (a i * z)` converges uniformly on compact sets and
defines an entire function. Its zeros are exactly the roots of its factors, and its analytic
order counts the factors vanishing there. No enumeration or countability assumption on the
index type is needed.

Natural multiplicities are allowed under the weighted condition `∑ i, m i * ‖a i‖² < ∞`.
The grouped product of the powers `E₁(a i * z) ^ m i` and the repeated-index product over
`Σ i, Fin (m i)` converge locally uniformly to the same entire function.
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

omit ha in
private def invRootEquiv (z : ℂ) :
    {i : {i // a i ≠ 0} // (a i)⁻¹ = z} ≃ {i : ι // a i * z = 1} where
  toFun | ⟨⟨i, hi⟩, hiz⟩ => ⟨i, by rw [← hiz, mul_inv_cancel₀ hi]⟩
  invFun | ⟨i, hiz⟩ => ⟨⟨i, fun h ↦ by simp [h] at hiz⟩, (eq_inv_of_mul_eq_one_right hiz).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The genus-one product vanishes exactly at a zero of one of its factors. -/
theorem tprod_weierstrassFactor_one_eq_zero_iff (z : ℂ) :
    (∏' i, weierstrassFactor 1 (a i * z)) = 0 ↔ ∃ i, a i * z = 1 := by
  rw [tprod_weierstrassFactor_one_eq_subtype a z,
    tprod_weierstrassFactor_div_eq_zero_iff (a := fun i : {i // a i ≠ 0} ↦ (a i)⁻¹)
      (p := fun _ ↦ 1) (fun i ↦ inv_ne_zero i.property)
      (fun R hR ↦ (summable_div_pow_inv a ha R hR).subtype _),
    ← nonempty_subtype, (invRootEquiv a z).nonempty_congr, nonempty_subtype]

/-- Only finitely many factors can vanish at a fixed point. -/
theorem finite_weierstrassFactor_one_roots (z : ℂ) :
    {i | a i * z = 1}.Finite := by
  have hf := finite_setOf_eq_of_summable_div_pow (a := fun i : {i // a i ≠ 0} ↦ (a i)⁻¹)
    (p := fun _ ↦ 1) (fun i ↦ inv_ne_zero i.property)
    (fun R hR ↦ (summable_div_pow_inv a ha R hR).subtype _) z
  have : Finite {i : ι // a i * z = 1} := (invRootEquiv a z).finite_iff.mp hf.to_subtype
  exact Set.toFinite _

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
    (fun R hR ↦ (summable_div_pow_inv a ha R hR).subtype _) z,
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  congr 1
  exact Nat.card_congr (invRootEquiv a z)

/-- The product order is the cardinality of any finite set containing exactly its vanishing
factors. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one_of_finset {z : ℂ} (s : Finset ι)
    (hs : ∀ i, a i * z = 1 ↔ i ∈ s) :
    analyticOrderAt (fun w ↦ ∏' i, weierstrassFactor 1 (a i * w)) z = s.card := by
  have hset : {i | a i * z = 1} = (s : Set ι) := Set.ext hs
  rw [analyticOrderAt_tprod_weierstrassFactor_one a ha z, hset, Set.ncard_coe_finset]

end Complex

namespace Complex

variable {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
  (hm : Summable (fun i ↦ (m i : ℝ) * ‖a i‖ ^ 2))

include hm

private theorem summable_sigma_sq :
    Summable fun q : Σ i, Fin (m i) ↦ ‖a q.1‖ ^ 2 :=
  (TauCeti.summable_sigma_fin_iff (fun i ↦ sq_nonneg ‖a i‖) m).mpr hm

/-- The product with natural multiplicities is the product over the repeated index
`Σ i, Fin (m i)`, in which the slope `a i` occurs `m i` times. -/
theorem tprod_weierstrassFactor_one_pow_eq_tprod_sigma (z : ℂ) :
    (∏' i, weierstrassFactor 1 (a i * z) ^ m i) =
      ∏' q : Σ i, Fin (m i), weierstrassFactor 1 (a q.1 * z) := by
  have hp : Multipliable fun q : Σ i, Fin (m i) ↦ weierstrassFactor 1 (a q.1 * z) :=
    ((hasProdUniformlyOn_weierstrassFactor_one (fun q : Σ i, Fin (m i) ↦ a q.1)
      (summable_sigma_sq a m hm) Bornology.isBounded_singleton).hasProd
        (Set.mem_singleton z)).multipliable
  rw [hp.tprod_sigma' fun _ ↦ Multipliable.of_finite]
  simp [tprod_fintype]

/-- A product with natural multiplicities is entire under weighted square summability. -/
@[fun_prop]
theorem differentiable_tprod_weierstrassFactor_one_pow :
    Differentiable ℂ (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) := by
  have heq : (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) =
      fun z ↦ ∏' q : Σ i, Fin (m i), weierstrassFactor 1 (a q.1 * z) :=
    funext (tprod_weierstrassFactor_one_pow_eq_tprod_sigma a m hm)
  rw [heq]
  exact differentiable_tprod_weierstrassFactor_one _ (summable_sigma_sq a m hm)

/-- With arbitrary repeated slopes, the order counts the vanishing factors with their
natural multiplicities, represented by the finite fibers of the multiplicity family. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one_pow (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' j, weierstrassFactor 1 (a j * w) ^ m j) z =
      ({p : Σ j, Fin (m j) | a p.1 * z = 1}.ncard : ℕ∞) := by
  have heq : (fun w ↦ ∏' j, weierstrassFactor 1 (a j * w) ^ m j) =
      fun w ↦ ∏' q : Σ j, Fin (m j), weierstrassFactor 1 (a q.1 * w) :=
    funext (tprod_weierstrassFactor_one_pow_eq_tprod_sigma a m hm)
  rw [heq]
  exact analyticOrderAt_tprod_weierstrassFactor_one _ (summable_sigma_sq a m hm) z

/-- For distinct slopes, the prescribed multiplicity is the exact order at the corresponding
root. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one_pow_of_injective {z : ℂ} {i : ι}
    (ha : Function.Injective a) (hi : a i * z = 1) :
    analyticOrderAt (fun w ↦ ∏' j, weierstrassFactor 1 (a j * w) ^ m j) z = m i := by
  have hz0 : z ≠ 0 := right_ne_zero_of_mul (by rw [hi]; exact one_ne_zero)
  have hset : {q : Σ j, Fin (m j) | a q.1 * z = 1} = Set.range (Sigma.mk i) := by
    rw [Set.range_sigmaMk]
    ext q
    exact ⟨fun h ↦ ha (mul_right_cancel₀ hz0 (h.trans hi.symm)), fun (h : q.1 = i) ↦ by
      simp [h, hi]⟩
  rw [analyticOrderAt_tprod_weierstrassFactor_one_pow a m hm z, hset,
    Set.ncard_range_of_injective sigma_mk_injective, Nat.card_fin]

/-- Products with natural multiplicities converge uniformly on every bounded set. -/
theorem hasProdUniformlyOn_weierstrassFactor_one_pow {K : Set ℂ} (hK : Bornology.IsBounded K) :
    HasProdUniformlyOn (fun i z ↦ weierstrassFactor 1 (a i * z) ^ m i)
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) K := by
  have h := (hasProdUniformlyOn_weierstrassFactor_one _ (summable_sigma_sq a m hm)
    hK).sigma_of_finite
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact h.multipliableUniformlyOn.hasProdUniformlyOn

/-- Products with natural multiplicities converge locally uniformly on the whole plane. -/
theorem hasProdLocallyUniformlyOn_weierstrassFactor_one_pow :
    HasProdLocallyUniformlyOn (fun i z ↦ weierstrassFactor 1 (a i * z) ^ m i)
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) Set.univ :=
  hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun _ _ hK ↦
    hasProdUniformlyOn_weierstrassFactor_one_pow a m hm hK.isBounded

/-- The repeated-index product, in which the slope `a i` occurs `m i` times, converges locally
uniformly on the whole plane to the product with natural multiplicities. -/
theorem hasProdLocallyUniformlyOn_sigma_weierstrassFactor_one :
    HasProdLocallyUniformlyOn (fun (p : Σ i, Fin (m i)) z ↦ weierstrassFactor 1 (a p.1 * z))
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) Set.univ := by
  rw [funext (tprod_weierstrassFactor_one_pow_eq_tprod_sigma a m hm)]
  exact hasProdLocallyUniformlyOn_weierstrassFactor_one _
    (summable_sigma_sq a m hm)

/-- The weighted product vanishes exactly at a root whose prescribed multiplicity is nonzero. -/
theorem tprod_weierstrassFactor_one_pow_eq_zero_iff (z : ℂ) :
    (∏' i, weierstrassFactor 1 (a i * z) ^ m i) = 0 ↔
      ∃ i, m i ≠ 0 ∧ a i * z = 1 := by
  rw [tprod_weierstrassFactor_one_pow_eq_tprod_sigma a m hm,
    tprod_weierstrassFactor_one_eq_zero_iff _ (summable_sigma_sq a m hm)]
  constructor
  · rintro ⟨⟨i, k⟩, hi⟩
    exact ⟨i, Nat.ne_zero_of_lt k.isLt, hi⟩
  · rintro ⟨i, hmi, hi⟩
    exact ⟨⟨i, ⟨0, Nat.pos_of_ne_zero hmi⟩⟩, hi⟩

end Complex
