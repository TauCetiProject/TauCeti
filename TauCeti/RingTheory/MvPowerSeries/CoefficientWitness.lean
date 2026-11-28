/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.RingTheory.MvPowerSeries.Rescale

/-!
# Coefficient witnesses in products of power series

For a fixed series `Θ` and a set of allowed multipliers, a coefficient witness consists of
one coefficient of each multiplied copy. The exponents add to the desired multidegree, and
the product of the norms records a lower bound without having to take the logarithm of zero.
This formulation lets valuation bounds from independent blocks of copies be combined.
An integral diagonal rescaling cannot improve the bound obtainable from such witnesses.

The statements use the coefficient-witness formulation of `New.CMLattice.LeastValLE`,
`New.CMLattice.LeastValLE.add` and `New.CMLattice.leastValLE_of_rescale` in
`grh/src/New/Derivatives/Sharpness/LeastValuation.lean` of [grh-lean] (revision `72fead1`).

[grh-lean]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh
-/

public section

open scoped NNReal

namespace MvPowerSeries

variable {σ R : Type*} [SeminormedCommRing R]

/-- There are `n` copies of `Θ` multiplied by elements of `S`, with coefficients whose
exponents sum to `ν` and whose norms have product at least `r`. At positive `r`, this is an
upper bound on the sum of the negative logarithms of the coefficient norms. -/
def HasCoeffNormProductGE (Θ : MvPowerSeries σ R) (S : Set (MvPowerSeries σ R))
    (n : ℕ) (ν : σ →₀ ℕ) (r : ℝ≥0) : Prop :=
  ∃ (H : Fin n → S) (α : Fin n → σ →₀ ℕ),
    ∑ i, α i = ν ∧ r ≤ ∏ i, ‖coeff (α i) ((H i : MvPowerSeries σ R) * Θ)‖₊

/-- A coefficient witness specifies the multipliers, exponents and product bound. -/
theorem hasCoeffNormProductGE_iff {Θ : MvPowerSeries σ R} {S : Set (MvPowerSeries σ R)}
    {n : ℕ} {ν : σ →₀ ℕ} {r : ℝ≥0} :
    Θ.HasCoeffNormProductGE S n ν r ↔
      ∃ (H : Fin n → S) (α : Fin n → σ →₀ ℕ),
        ∑ i, α i = ν ∧ r ≤ ∏ i, ‖coeff (α i) ((H i : MvPowerSeries σ R) * Θ)‖₊ := (Iff.rfl)

variable {Θ : MvPowerSeries σ R} {S : Set (MvPowerSeries σ R)}
  {n m : ℕ} {ν μ : σ →₀ ℕ} {r s : ℝ≥0}

/-- A witness also gives any weaker lower bound on the product of norms. -/
theorem HasCoeffNormProductGE.mono (h : Θ.HasCoeffNormProductGE S n ν r) (hs : s ≤ r) :
    Θ.HasCoeffNormProductGE S n ν s := by
  obtain ⟨H, α, hα, hr⟩ := hasCoeffNormProductGE_iff.mp h
  exact hasCoeffNormProductGE_iff.mpr ⟨H, α, hα, hs.trans hr⟩

/-- The empty family witnesses just degree zero, with product of norms one. -/
@[simp] theorem hasCoeffNormProductGE_zero_copies_iff :
    Θ.HasCoeffNormProductGE S 0 ν r ↔ ν = 0 ∧ r ≤ 1 := by
  simp only [hasCoeffNormProductGE_iff, Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty,
    eq_comm (a := (0 : σ →₀ ℕ))]
  exact ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨Fin.elim0, Fin.elim0, h⟩⟩

/-- For one copy, the witness is a single allowed multiplier with a coefficient at `ν`
of norm at least `r`. -/
@[simp] theorem hasCoeffNormProductGE_one_copy_iff :
    Θ.HasCoeffNormProductGE S 1 ν r ↔ ∃ H ∈ S, r ≤ ‖coeff ν (H * Θ)‖₊ := by
  constructor
  · rintro ⟨H, α, hα, hr⟩
    have he : α 0 = ν := by simpa only [Fin.sum_univ_one] using hα
    exact ⟨H 0, (H 0).property, by simpa only [Fin.prod_univ_one, he] using hr⟩
  · rintro ⟨H, hH, hr⟩
    exact hasCoeffNormProductGE_iff.mpr ⟨fun _ ↦ ⟨H, hH⟩, fun _ ↦ ν, by simp, by simpa⟩

/-- A single allowed multiplier whose constant coefficient contributes norm at least one
can be used in every copy to witness the degree-zero bound. -/
theorem hasCoeffNormProductGE_zero_degree {H : MvPowerSeries σ R} (hH : H ∈ S)
    (hΘ : 1 ≤ ‖(H * Θ).constantCoeff‖₊) : Θ.HasCoeffNormProductGE S n 0 1 := by
  refine hasCoeffNormProductGE_iff.mpr ⟨fun _ ↦ ⟨H, hH⟩, fun _ ↦ 0, by simp, ?_⟩
  exact Finset.one_le_prod fun _ _ ↦ by simpa only [coeff_zero_eq_constantCoeff_apply] using hΘ

/-- Concatenating coefficient witnesses adds the degrees and multiplies the norm bounds. -/
theorem HasCoeffNormProductGE.add (h : Θ.HasCoeffNormProductGE S n ν r)
    (h' : Θ.HasCoeffNormProductGE S m μ s) : Θ.HasCoeffNormProductGE S (n + m) (ν + μ) (r * s) := by
  obtain ⟨H, α, hα, hr⟩ := hasCoeffNormProductGE_iff.mp h
  obtain ⟨K, β, hβ, hs⟩ := hasCoeffNormProductGE_iff.mp h'
  refine hasCoeffNormProductGE_iff.mpr ⟨Fin.append H K, Fin.append α β, ?_, ?_⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hα, hβ]
  · rw [Fin.prod_univ_add]
    simpa only [Fin.append_left, Fin.append_right] using mul_le_mul' hr hs

open Finset in
/-- In an ultrametric ring a positive lower bound on a coefficient norm of a product of
integrally rescaled series gives a degree decomposition with the same lower bound on the
product of the original coefficient norms. -/
theorem exists_le_prod_nnNorm_coeff_of_le_nnNorm_coeff_prod_rescale
    [IsUltrametricDist R] [NormOneClass R] {ι : Type*} (f : ι → MvPowerSeries σ R) (t : Finset ι)
    (a : ι → σ → R) (ha : ∀ i ∈ t, ∀ j, ‖a i j‖₊ ≤ 1) (hr : 0 < r)
    (h : r ≤ ‖coeff ν (∏ i ∈ t, rescale (a i) (f i))‖₊) :
    ∃ α : ι → σ →₀ ℕ, ∑ i ∈ t, α i = ν ∧ r ≤ ∏ i ∈ t, ‖coeff (α i) (f i)‖₊ := by
  classical
  rw [coeff_prod] at h
  let A := finsuppAntidiag t ν
  let c (α : ι →₀ (σ →₀ ℕ)) := ∏ i ∈ t, coeff (α i) (rescale (a i) (f i))
  have hA : A.Nonempty := by
    by_contra! hA
    have he : finsuppAntidiag t ν = ∅ := hA
    rw [he, sum_empty, nnNorm_zero] at h
    exact hr.not_ge h
  obtain ⟨α, hα, he⟩ := exists_mem_eq_sup' hA (fun β ↦ ‖c β‖₊)
  have hmax : ‖∑ β ∈ A, c β‖₊ ≤ ‖c α‖₊ := by
    apply NNReal.coe_le_coe.mp
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun β hβ ↦
      NNReal.coe_le_coe.mpr ((le_sup' (fun b ↦ ‖c b‖₊) hβ).trans_eq he)
  refine ⟨α, (mem_finsuppAntidiag.mp hα).1, (h.trans hmax).trans ?_⟩
  refine le_trans ?_ <| prod_le_prod fun i hi ↦ (f i).nnNorm_coeff_rescale_le (a i) (ha i hi) (α i)
  apply NNReal.coe_le_coe.mp
  simpa only [c, NNReal.coe_prod, coe_nnNorm] using
    TauCeti.norm_prod_le_prod_norm t (fun i ↦ coeff (α i) (rescale (a i) (f i)))

/-- A large coefficient in a product of rescaled, multiplied copies gives a witness
for the same total degree without rescaling. -/
theorem HasCoeffNormProductGE.of_le_nnNorm_coeff_prod_rescale [IsUltrametricDist R] [NormOneClass R]
    (H : Fin n → S) (a : Fin n → σ → R) (ha : ∀ i j, ‖a i j‖₊ ≤ 1) (hr : 0 < r)
    (h : r ≤ ‖coeff ν (∏ i, rescale (a i) ((H i : MvPowerSeries σ R) * Θ))‖₊) :
    Θ.HasCoeffNormProductGE S n ν r := by
  obtain ⟨α, hα, hb⟩ := exists_le_prod_nnNorm_coeff_of_le_nnNorm_coeff_prod_rescale
    (fun i ↦ (H i : MvPowerSeries σ R) * Θ) Finset.univ a (fun i _ ↦ ha i) hr h
  exact hasCoeffNormProductGE_iff.mpr ⟨H, α, hα, hb⟩

end MvPowerSeries
