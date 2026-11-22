/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.Restricted.PolydiscReduction

import TauCeti.RingTheory.Huber.Restricted.Comparison
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval

/-!
# Evaluation Lipschitz bounds and residue reduction on the closed polydisc

Evaluating a restricted power series `f ∈ R⟨T₁, …, Tₖ⟩` on the unit polydisc `(R°)ᵏ` over a
complete ultrametric normed commutative ring is Lipschitz with constant the unit Gauss norm of `f`.
Over a complete ultrametric normed field `K`, evaluating a unit-bounded series `f ∈ K°⟨T₁, …, Tₖ⟩`
at a power-bounded tuple `a ∈ (K°)ᵏ` commutes with coefficientwise residue reduction modulo
`K°° = topologicallyNilpotentIdeal K`.

## Main results

* `TauCeti.ValuationSpectrum.norm_evalAtHom_sub_evalAtHom_le`: evaluation of a restricted series on
  `(R°)ᵏ` is Lipschitz with constant its unit Gauss norm.
* `TauCeti.ValuationSpectrum.lipschitzWith_evalAtHom_apply` and
  `TauCeti.ValuationSpectrum.continuous_evalAtHom_apply`: evaluation of a fixed series is Lipschitz
  and continuous in `a ∈ (K°)ᵏ`.
* `TauCeti.ValuationSpectrum.evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring`:
  evaluation of a unit-bounded series at a power-bounded tuple is power-bounded.
* `TauCeti.ValuationSpectrum.mk_evalAtHom_eq_eval_polydiscReduction`: residue reduction commutes
  with evaluation at power-bounded tuples.
* `TauCeti.ValuationSpectrum.norm_evalAtHom_eq_one_iff_eval_polydiscReduction_ne_zero`:
  `‖f(a)‖ = 1` iff the reduced polynomial does not vanish at `ā`.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber Filter Topology
open scoped NNReal

section EvalLipschitz

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- **Evaluation of a restricted power series is Lipschitz on the closed unit polydisc**, with
Lipschitz constant its unit Gauss norm. -/
theorem norm_evalAtHom_sub_evalAtHom_le {a b : Fin k → R}
    (ha : ∀ i, IsPowerBounded (a i)) (hb : ∀ i, IsPowerBounded (b i))
    (ha₁ : ∀ i, ‖a i‖ ≤ 1) (hb₁ : ∀ i, ‖b i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f - evalAtHom b hb f‖ ≤
      MvPowerSeries.gaussNorm norm (fun _ : Fin k ↦ (1 : ℝ)) (f : MvPowerSeries (Fin k) R) *
        ‖a - b‖ := by
  set f' := restrictedMvPowerSeriesGaussEquiv f
  have hsum : HasSum
      (fun ν : Fin k →₀ ℕ ↦ weightedEvalTerm (RingHom.id R) a (f : MvPowerSeries (Fin k) R) ν -
        weightedEvalTerm (RingHom.id R) b (f : MvPowerSeries (Fin k) R) ν)
      (evalAtHom a ha f - evalAtHom b hb f) := by
    rw [evalAtHom_def, evalAtHom_def, coe_weightedEvalHom, coe_weightedEvalHom]
    exact (hasSum_weightedEval_of_forall_isPowerBounded continuousAt_id ha
      (mem_weightedRestrictedSubring.mp f.property)).sub
      (hasSum_weightedEval_of_forall_isPowerBounded continuousAt_id hb
        (mem_weightedRestrictedSubring.mp f.property))
  rw [← hsum.tsum_eq, ← coe_restrictedMvPowerSeriesGaussEquiv f, ← MvPowerSeries.norm_eq_gaussNorm]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg f') (norm_nonneg (a - b))) fun ν ↦ ?_
  rw [weightedEvalTerm_def, weightedEvalTerm_def, RingHom.id_apply, ← mul_sub]
  have hmon : ‖∏ i, a i ^ ν i - ∏ i, b i ^ ν i‖ ≤ ‖a - b‖ := by
    rw [← Finsupp.prod_fintype ν (a · ^ ·) fun _ ↦ pow_zero _,
      ← Finsupp.prod_fintype ν (b · ^ ·) fun _ ↦ pow_zero _, Finsupp.prod, Finsupp.prod]
    simpa only [one_pow, mul_one] using TauCeti.norm_prod_sub_prod_le (s := ν.support)
      (M := 1) (ε := ‖a - b‖) (norm_nonneg _)
      (fun i hi ↦ (norm_pow_le' (a i) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
        (pow_le_one₀ (norm_nonneg _) (ha₁ i)))
      (fun i hi ↦ (norm_pow_le' (b i) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
        (pow_le_one₀ (norm_nonneg _) (hb₁ i)))
      (fun i _ ↦ by
        have hpow : ‖a i ^ ν i - b i ^ ν i‖ ≤ ‖a i - b i‖ := by
          simpa using TauCeti.norm_prod_sub_prod_le (s := Finset.range (ν i))
            (f := fun _ ↦ a i) (g := fun _ ↦ b i) (M := 1) (norm_nonneg _)
            (fun _ _ ↦ ha₁ i) (fun _ _ ↦ hb₁ i) (fun _ _ ↦ le_rfl)
        exact hpow.trans (norm_le_pi_norm (a - b) i))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ hmon (norm_nonneg _) (norm_nonneg f'))
  simpa only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one] using
    MvPowerSeries.norm_coeff_mul_prod_le f' ν

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- For a fixed restricted power series `f ∈ K⟨T₁, …, Tₖ⟩`, evaluation `a ↦ f(a)` is Lipschitz on
`(K°)ᵏ` with constant the unit Gauss norm of `f`. -/
theorem lipschitzWith_evalAtHom_apply
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    LipschitzWith
      (Real.toNNReal (MvPowerSeries.gaussNorm norm (fun _ : Fin k ↦ (1 : ℝ))
        (f : MvPowerSeries (Fin k) K)))
      fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦ evalAtHom a.val a.property f := by
  refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  have hnonneg : 0 ≤ MvPowerSeries.gaussNorm norm (fun _ : Fin k ↦ (1 : ℝ))
      (f : MvPowerSeries (Fin k) K) := by
    rw [← coe_restrictedMvPowerSeriesGaussEquiv f, ← MvPowerSeries.norm_eq_gaussNorm]
    exact norm_nonneg _
  rw [Real.coe_toNNReal _ hnonneg, dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
  exact norm_evalAtHom_sub_evalAtHom_le a.property b.property
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (a.property i))
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (b.property i)) f

/-- For a fixed restricted power series `f ∈ K⟨T₁, …, Tₖ⟩`, evaluation `a ↦ f(a)` is continuous on
`(K°)ᵏ`. -/
theorem continuous_evalAtHom_apply
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    Continuous fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      evalAtHom a.val a.property f :=
  (lipschitzWith_evalAtHom_apply f).continuous

end EvalLipschitz

section EvalReduction

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Evaluating a unit-bounded series at a power-bounded tuple yields a power-bounded element. -/
theorem evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring
    (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    evalAtHom a ha f.val ∈ powerBoundedSubring K := by
  rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, evalAtHom_def]
  refine (norm_weightedEvalHom_le continuousAt_id (C := 1) (fun r ↦ by simp)
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i)) _ f.val).trans ?_
  rw [one_mul, MvPowerSeries.norm_eq_gaussNorm, coe_restrictedMvPowerSeriesGaussEquiv,
    ← coe_unitGaussValuation]
  exact_mod_cast (unitGaussValuation_le_one_iff_mem_weightedSubring n K).mpr f.property

/-- **Reduction commutes with evaluation at power-bounded tuples.** For `f ∈ K°⟨T₁, …, Tₙ⟩` and
`a ∈ (K°)ⁿ`, the residue class of `f(a)` in `K° ⧸ K°°` equals the value of `polydiscReduction n K f`
at the residue tuple `ā`. -/
theorem mk_evalAtHom_eq_eval_polydiscReduction (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
        ⟨evalAtHom a ha f.val, evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha f⟩ =
      MvPolynomial.eval
        (fun i ↦ Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
          ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩)
        (polydiscReduction n K f) := by
  have : CompleteSpace (powerBoundedSubring K) :=
    (coe_powerBoundedSubring_eq_closedBall K ▸ Metric.isClosed_closedBall).completeSpace_coe
  let b : Fin n → powerBoundedSubring K := fun i ↦ ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩
  have huniv : TauCeti.Huber.IsBounded (Set.univ : Set (powerBoundedSubring K)) := by
    convert (powerBoundedSubring K).isBounded_preimage_subtype
      (IsUniform.isBounded_powerBoundedSubring (A := K))
    ext x
    exact ⟨fun _ ↦ x.property, fun _ ↦ Set.mem_univ x⟩
  have hb : IsWeightBounded (RingHom.id (powerBoundedSubring K))
      (fun _ : Fin n ↦ ({1} : Set (powerBoundedSubring K))) b :=
    (isWeightBounded_one_weight_iff _ _).mpr (huniv.subset (Set.subset_univ _))
  have hsub : Continuous (powerBoundedSubring K).subtype := continuous_subtypeVal
  have hext :
      (powerBoundedSubring K).subtype.comp
          (weightedEvalHom isWeightFamily_one_weight continuousAt_id hb) =
        (evalAtHom a ha).comp (weightedMap hsub isWeightFamily_one_weight isWeightFamily_one_weight
          (fun _ ↦ by simp)) := by
    refine weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      (continuous_subtypeVal.comp (continuous_weightedEvalHom _ _ _))
      ((continuous_evalAtHom a ha).comp (continuous_weightedMap _ _ _ _))
      (fun c ↦ by simp) (fun i ↦ by simp [b])
  have heval :
      (⟨evalAtHom a ha f.val, evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha f⟩ :
          powerBoundedSubring K) =
        weightedEvalHom isWeightFamily_one_weight continuousAt_id hb
          ((weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm f) := by
    refine Subtype.ext ?_
    have h := DFunLike.congr_fun hext
      ((weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm f)
    have hval : weightedMap hsub isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ by simp)
        ((weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm f) =
        f.val := by
      apply Subtype.ext
      rw [coe_weightedMap, ← coe_weightedRestrictedSubringEquivWeightedSubring,
        RingEquiv.apply_symm_apply]
    simpa [hval] using h.symm
  rw [heval, mk_weightedEvalHom_eq_eval₂_restrictedReduction continuousAt_id hb
    isOpen_topologicallyNilpotentIdeal isOpen_topologicallyNilpotentIdeal le_rfl]
  have hid : Ideal.quotientMap (I := topologicallyNilpotentIdeal K)
      (topologicallyNilpotentIdeal K) (RingHom.id (powerBoundedSubring K)) le_rfl =
      RingHom.id _ := RingHom.ext fun q ↦ by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl
  rw [hid, MvPolynomial.eval₂_id, polydiscReduction_def, Ideal.weightedSubringReduction_def,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]

/-- A unit-bounded series `f ∈ K°⟨T₁, …, Tₙ⟩` evaluates to an element of norm `1` at `a ∈ (K°)ⁿ`
if and only if its reduction does not vanish at the residue tuple `ā`. -/
theorem norm_evalAtHom_eq_one_iff_eval_polydiscReduction_ne_zero (a : Fin n → K)
    (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    ‖evalAtHom a ha f.val‖ = 1 ↔
      MvPolynomial.eval
        (fun i ↦ Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
          ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩)
        (polydiscReduction n K f) ≠ 0 := by
  have hle : ‖evalAtHom a ha f.val‖ ≤ 1 :=
    isPowerBounded_iff_norm_le_one.mp
      (mem_powerBoundedSubring.mp
        (evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha f))
  rw [← mk_evalAtHom_eq_eval_polydiscReduction a ha f, Ne, Ideal.Quotient.eq_zero_iff_mem,
    mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
    tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, not_lt]
  exact ⟨fun h ↦ h.ge, fun h ↦ le_antisymm hle h⟩

end EvalReduction

end TauCeti.ValuationSpectrum
