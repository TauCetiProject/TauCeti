/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Algebra.Polynomial

/-!
# Sobolev spaces on nonempty bounded domains are infinite-dimensional

On a nonempty bounded open subset `Ω` of a nontrivial finite-dimensional real inner product space,
`W^{1,p}(Ω)` is infinite-dimensional. The powers `x ↦ ⟪v, x⟫ ^ k` of a unit linear coordinate are
smooth, hence Sobolev functions on the bounded set `Ω`, and they are linearly independent: a
vanishing linear combination is a polynomial in `⟪v, x⟫` that vanishes almost everywhere on `Ω`,
hence everywhere on `Ω` by continuity, hence on an interval of values of the coordinate.

By Riesz's theorem the identity of `W^{1,p}(Ω)` is then not a compact operator. This is the
reason the Rellich–Kondrachov theorem concerns the value map `W^{1,p}(Ω) → Lᵖ(Ω)`, which loses one
derivative, rather than the identity.

## Main declarations

* `TauCeti.W1p.not_finiteDimensional`: `W^{1,p}(Ω)` is infinite-dimensional.
* `TauCeti.W1p.not_isCompactOperator_id`: the identity of `W^{1,p}(Ω)` is not compact.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Polynomial Set TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Sobolev spaces are infinite-dimensional.** On a nonempty bounded open set `Ω` of a
nontrivial finite-dimensional real inner product space, `W^{1,p}(Ω)` is not finite-dimensional:
the powers of a linear coordinate are linearly independent Sobolev functions. -/
theorem W1p.not_finiteDimensional (hb : Bornology.IsBounded (Omega : Set E))
    (hne : (Omega : Set E).Nonempty) : ¬FiniteDimensional ℝ (W1p mu Omega p) := by
  intro hfin
  obtain ⟨v, hv⟩ := exists_norm_eq E zero_le_one
  let ℓ : StrongDual ℝ E := innerSL ℝ v
  have hℓv : ℓ v = 1 := by simp [ℓ, hv]
  -- The powers of the coordinate `ℓ` are Sobolev functions on the bounded set `Ω`.
  have hpow (k : ℕ) : ∃ w : W1p mu Omega p, W1p.value w =ᵐ[mu.restrict Omega] fun x ↦ ℓ x ^ k :=
    (W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (u := fun x ↦ ℓ x ^ k)
      isOpen_univ (ℓ.contDiff.pow k).contDiffOn hb.isCompact_closure subset_closure
      (subset_univ _)).imp fun _ h ↦ h.1
  choose w hw using hpow
  let n := Module.finrank ℝ (W1p mu Omega p)
  have hli : LinearIndependent ℝ fun i : Fin (n + 1) ↦ w i := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let Q : ℝ[X] := ∑ i : Fin (n + 1), C (g i) * X ^ (i : ℕ)
    -- The polynomial `Q` vanishes at `ℓ x` for almost every, hence every, `x ∈ Ω`.
    have hzero : W1p.value (∑ i, g i • w i) =ᵐ[mu.restrict Omega] 0 := by
      rw [hg, ← W1p.valueL_apply, map_zero]
      exact Lp.coeFn_zero _ _ _
    have hae : (fun x ↦ Q.eval (ℓ x)) =ᵐ[mu.restrict Omega] fun _ ↦ 0 := by
      filter_upwards [W1p.value_finsetSum_ae Finset.univ (fun i ↦ g i • w i),
        ae_all_iff.2 fun i : Fin (n + 1) ↦ W1p.value_smul_ae (g i) (w i),
        ae_all_iff.2 fun i : Fin (n + 1) ↦ hw i, hzero] with x hsum hsmul hpowx hx0
      simp only [Pi.zero_apply] at hx0
      rw [hsum] at hx0
      simp only [Q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      rw [← hx0]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hsmul i, Pi.smul_apply, hpowx i, smul_eq_mul]
    have hon : EqOn (fun x ↦ Q.eval (ℓ x)) (fun _ ↦ 0) Omega :=
      Measure.eqOn_open_of_ae_eq hae Omega.isOpen
        (Q.continuous.comp ℓ.continuous).continuousOn continuousOn_const
    obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Omega.isOpen x₀ hx₀
    have hQ : Q = 0 := by
      refine eq_zero_of_infinite_isRoot Q
        ((Ioo_infinite (show ℓ x₀ - ε < ℓ x₀ + ε by linarith)).mono fun t ht ↦ ?_)
      have hmem : x₀ + (t - ℓ x₀) • v ∈ (Omega : Set E) := by
        refine hball ?_
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one,
          Real.norm_eq_abs, abs_lt]
        constructor <;> linarith [ht.1, ht.2]
      have h := hon hmem
      simp only [map_add, map_smul, hℓv, smul_eq_mul, mul_one, add_sub_cancel] at h
      exact h
    intro i
    have hi := congrArg (fun P : ℝ[X] ↦ P.coeff i) hQ
    simpa [Q, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using hi
  have := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at this
  omega

/-- **The identity of a Sobolev space is not compact.** On a nonempty bounded open set `Ω` of a
nontrivial finite-dimensional real inner product space, the identity of `W^{1,p}(Ω)` is not a
compact operator, by Riesz's theorem and `TauCeti.W1p.not_finiteDimensional`. -/
theorem W1p.not_isCompactOperator_id (hb : Bornology.IsBounded (Omega : Set E))
    (hne : (Omega : Set E).Nonempty) :
    ¬IsCompactOperator (id : W1p mu Omega p → W1p mu Omega p) := by
  rw [isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)]
  exact W1p.not_finiteDimensional hb hne

end TauCeti
