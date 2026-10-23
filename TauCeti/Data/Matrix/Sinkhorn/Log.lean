/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Log.SumExp
public import TauCeti.Data.Matrix.Sinkhorn.Basic

/-!
# Max-shift log-domain Sinkhorn iteration

For a real log-kernel `L`, the positive kernel is `L.map Real.exp`. Row and column
potentials are logarithms of scaling factors (without a temperature factor); the marginals
`a` and `b` remain in the original domain. The half-step evaluates
`log a i - log (∑ j, exp (L i j + v j))` by first subtracting the row maximum inside the
exponentials. Both index types must be nonempty for a full step.

`Matrix.exp_logSinkhornUpdate`, `Matrix.exp_logSinkhornStep`, and
`Matrix.exp_logSinkhornStep_iterate` show that exponentiation intertwines these operations
with the existing Sinkhorn operations. `Matrix.exp_logSinkhornPlan` identifies the resulting
plans, so their marginal and convergence guarantees transfer. In particular,
`Matrix.tendsto_exp_logSinkhornPlan_iterate` proves convergence of the plans.

The shift is an exact real-arithmetic identity. The bounds in
`TauCeti.Analysis.SpecialFunctions.Log.SumExp` show that the shifted exponentials are at most
one and their sum is between one and the number of columns. No floating-point error estimate
is asserted. A strictly positive kernel `K` can be supplied as `K.map Real.log`;
`Matrix.exp_logSinkhornUpdate_log` gives the direct connection to its ordinary update.

## References

* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11
  (2019), Remarks 4.21--4.23, especially the log-sum-exp shift in Equation (4.42).
-/

public section

open Filter Real Topology

namespace Matrix

variable {ι κ : Type*} [Fintype κ] [Nonempty κ]

/-- A Sinkhorn half-step on log scaling factors, evaluated with a separate maximum shift
in each row of the log-kernel. The target marginal `a` is in the original domain. -/
noncomputable def logSinkhornUpdate (L : Matrix ι κ ℝ) (a : ι → ℝ) (v : κ → ℝ) : ι → ℝ :=
  fun i ↦
    let c := Finset.univ.sup' Finset.univ_nonempty (fun j ↦ L i j + v j)
    log (a i) - (c + log (∑ j, exp (L i j + v j - c)))

/-- The max-shift formula used to evaluate a log-domain half-step. -/
theorem logSinkhornUpdate_def (L : Matrix ι κ ℝ) (a : ι → ℝ) (v : κ → ℝ) :
    L.logSinkhornUpdate a v = fun i ↦
      let c := Finset.univ.sup' Finset.univ_nonempty (fun j ↦ L i j + v j)
      log (a i) - (c + log (∑ j, exp (L i j + v j - c))) :=
  (rfl)

/-- Max-shift evaluation agrees exactly with the unshifted log-domain formula. -/
@[simp]
theorem logSinkhornUpdate_apply (L : Matrix ι κ ℝ) (a : ι → ℝ) (v : κ → ℝ) (i : ι) :
    L.logSinkhornUpdate a v i = log (a i) - log (∑ j, exp (L i j + v j)) := by
  rw [logSinkhornUpdate_def,
    Finset.log_sum_exp_eq_add_log_sum_exp_sub Finset.univ Finset.univ_nonempty
      (fun j ↦ L i j + v j)
      (Finset.univ.sup' Finset.univ_nonempty (fun j : κ ↦ L i j + v j))]

/-- Exponentiating the stabilized half-step gives the ordinary Sinkhorn half-step. -/
theorem exp_logSinkhornUpdate (L : Matrix ι κ ℝ) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (v : κ → ℝ) :
    exp ∘ L.logSinkhornUpdate a v = (L.map exp).sinkhornUpdate a (exp ∘ v) := by
  funext i
  simp only [Function.comp_apply, logSinkhornUpdate_apply, exp_sub, sinkhornUpdate_apply,
    mulVec_apply_eq_sum, map_apply]
  rw [exp_log (ha i), exp_log (Finset.sum_pos (fun j _ ↦ exp_pos _) Finset.univ_nonempty)]
  simp only [exp_add]

/-- Using the logarithm of a positive kernel recovers its ordinary half-step. -/
theorem exp_logSinkhornUpdate_log {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (v : κ → ℝ) :
    exp ∘ (K.map log).logSinkhornUpdate a v = K.sinkhornUpdate a (exp ∘ v) := by
  rw [exp_logSinkhornUpdate _ ha]
  congr 1
  ext i j
  exact exp_log (hK i j)

/-- Adding a constant to the input potential subtracts it from the updated potential. -/
theorem logSinkhornUpdate_add_const (L : Matrix ι κ ℝ) (a : ι → ℝ) (v : κ → ℝ) (c : ℝ) :
    L.logSinkhornUpdate a (fun j ↦ v j + c) = fun i ↦ L.logSinkhornUpdate a v i - c := by
  funext i
  simp only [logSinkhornUpdate_apply]
  rw [Finset.log_sum_exp_eq_add_log_sum_exp_sub Finset.univ Finset.univ_nonempty
    (fun j ↦ L i j + (v j + c)) c]
  simp only [← add_assoc, add_sub_cancel_right]
  ring

variable [Fintype ι] [Nonempty ι]

/-- A full log-domain Sinkhorn step: update the column potentials, then the row potentials. -/
noncomputable def logSinkhornStep (L : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (u : ι → ℝ) : ι → ℝ :=
  L.logSinkhornUpdate a (Lᵀ.logSinkhornUpdate b u)

/-- The two half-steps of the log-domain iteration. -/
theorem logSinkhornStep_def (L : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) (u : ι → ℝ) :
    L.logSinkhornStep a b u = L.logSinkhornUpdate a (Lᵀ.logSinkhornUpdate b u) :=
  (rfl)

/-- Exponentiation intertwines a full stabilized step with the ordinary Sinkhorn step. -/
theorem exp_logSinkhornStep (L : Matrix ι κ ℝ) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    {b : κ → ℝ} (hb : ∀ j, 0 < b j) (u : ι → ℝ) :
    exp ∘ L.logSinkhornStep a b u = (L.map exp).sinkhornStep a b (exp ∘ u) := by
  simp only [logSinkhornStep_def, sinkhornStep_def, exp_logSinkhornUpdate _ ha,
    exp_logSinkhornUpdate _ hb, transpose_map]

/-- A full log-domain step respects the additive ambiguity of row potentials. -/
theorem logSinkhornStep_add_const (L : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (u : ι → ℝ) (c : ℝ) :
    L.logSinkhornStep a b (fun i ↦ u i + c) = fun i ↦ L.logSinkhornStep a b u i + c := by
  simp only [logSinkhornStep_def, logSinkhornUpdate_add_const, sub_eq_add_neg,
    logSinkhornUpdate_add_const, neg_neg]

/-- Every stabilized iterate refines the corresponding ordinary Sinkhorn iterate. -/
theorem exp_logSinkhornStep_iterate (L : Matrix ι κ ℝ) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    {b : κ → ℝ} (hb : ∀ j, 0 < b j) (u : ι → ℝ) (n : ℕ) :
    exp ∘ (L.logSinkhornStep a b)^[n] u = ((L.map exp).sinkhornStep a b)^[n] (exp ∘ u) := by
  exact (Function.Semiconj.iterate_right (exp_logSinkhornStep L ha hb) n) u

/-- The log of the plan produced by a stabilized step, assembled by adding potentials to
the log-kernel. -/
noncomputable def logSinkhornPlan (L : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (u : ι → ℝ) : Matrix ι κ ℝ :=
  of fun i j ↦ L.logSinkhornStep a b u i + L i j + Lᵀ.logSinkhornUpdate b u j

/-- The entries of the log-domain plan. -/
@[simp]
theorem logSinkhornPlan_apply (L : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (u : ι → ℝ) (i : ι) (j : κ) :
    L.logSinkhornPlan a b u i j =
      L.logSinkhornStep a b u i + L i j + Lᵀ.logSinkhornUpdate b u j :=
  (rfl)

/-- Adding a constant to the input potential leaves the log-domain plan unchanged. -/
theorem logSinkhornPlan_add_const (L : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (u : ι → ℝ) (c : ℝ) :
    L.logSinkhornPlan a b (fun i ↦ u i + c) = L.logSinkhornPlan a b u := by
  ext i j
  simp only [logSinkhornPlan_apply, logSinkhornStep_add_const, logSinkhornUpdate_add_const]
  ring

/-- Exponentiating the log-domain plan gives exactly the ordinary Sinkhorn plan. -/
theorem exp_logSinkhornPlan (L : Matrix ι κ ℝ) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    {b : κ → ℝ} (hb : ∀ j, 0 < b j) (u : ι → ℝ) :
    (L.logSinkhornPlan a b u).map exp = (L.map exp).sinkhornPlan a b (exp ∘ u) := by
  ext i j
  have hrow := congrFun (exp_logSinkhornStep L ha hb u) i
  have hcol := congrFun (exp_logSinkhornUpdate Lᵀ hb u) j
  simp only [Function.comp_apply, transpose_map] at hrow hcol
  simp only [map_apply, logSinkhornPlan_apply, exp_add, sinkhornPlan_apply, hrow, hcol]

/-- The exponentiated log-domain plan has the prescribed sum in every row whose target
is positive. No positivity assumption on the other row targets or column targets is needed. -/
theorem sum_exp_logSinkhornPlan_apply (L : Matrix ι κ ℝ) {a : ι → ℝ}
    (b : κ → ℝ) (u : ι → ℝ) (i : ι) (ha : 0 < a i) :
    ∑ j, exp (L.logSinkhornPlan a b u i j) = a i := by
  have hsum : 0 < ∑ j, exp (L i j + Lᵀ.logSinkhornUpdate b u j) :=
    Finset.sum_pos (fun j _ ↦ exp_pos _) Finset.univ_nonempty
  simp_rw [logSinkhornPlan_apply, add_assoc, exp_add, ← Finset.mul_sum, ← exp_add]
  rw [logSinkhornStep_def, logSinkhornUpdate_apply, exp_sub, exp_log ha, exp_log hsum]
  exact div_mul_cancel₀ _ hsum.ne'

/-- The plans from the stabilized iteration converge to any positive diagonal scaling with
the prescribed marginals, by exact agreement with the ordinary Sinkhorn iteration. -/
theorem tendsto_exp_logSinkhornPlan_iterate (L : Matrix ι κ ℝ) {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (hP : IsDiagonalScaling P (L.map exp) u v)
    (hPm : HasMarginals P a b) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) (u₀ : ι → ℝ) :
    Tendsto (fun n ↦ (L.logSinkhornPlan a b ((L.logSinkhornStep a b)^[n] u₀)).map exp)
      atTop (𝓝 P) := by
  simp only [exp_logSinkhornPlan L ha hb, exp_logSinkhornStep_iterate L ha hb]
  exact tendsto_sinkhornPlan_iterate (fun i j ↦ exp_pos _) ha hb hP hPm hu hv
    (fun i ↦ exp_pos (u₀ i))

end Matrix
