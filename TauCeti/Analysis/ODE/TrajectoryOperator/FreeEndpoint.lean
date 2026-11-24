/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Parametric
public import TauCeti.Analysis.ODE.EnergyEstimate.WeightCrossing
public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.Sobolev.GraphStep.ZeroAtInfty
import TauCeti.Analysis.ODE.TrajectoryOperator.Tanh
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Trajectory operators with free endpoint variables

Let `A : ℝ → End(F)` be a continuous family of operators whose limits `A±` at `±∞` may have a
kernel, as for the linearized negative gradient flow of a Morse–Bott function along a trajectory
between critical manifolds `C` and `D`, where `ker A⁻ = T C` and `ker A⁺ = T D`. On exponentially
weighted spaces `{u | exp w • u ∈ Lᵖ}`, with a weight `w` growing at the ends, the trajectory
operator `D_A u = u' + A u` is Fredholm for suitable weights (for finite-dimensional `F`, when
the slopes of `w` at `±∞` are not real parts of eigenvalues of `A±`; the general index formula below
takes this as a hypothesis), but it only sees solutions decaying to `0`. The solutions
converging to a nonzero vector `v ∈ ker A±` are recovered by adjoining `v` as a free variable,
extended into the line by a cutoff `χ` that is `1` near the corresponding end and `0` near the
other:

`D_extended (u, v) = D_A u + D_A (χ • v)`.

For `v ∈ ker A⁺` the extension `D_A (χ • v) = χ' • v + χ • (A - A⁺) v` lies in the weighted space
when `A` converges to `A⁺` faster than the weight grows: this is the *weighted-tail condition*.

As in `TauCeti.Analysis.ODE.EnergyEstimate.Weighted`, multiplication by `exp w` identifies the
weighted spaces with the unweighted ones and conjugates `D_A` to `D_{A - w'}`. In these
coordinates a free variable `v` at an end with cutoff `χ` contributes the *end tail*

`TauCeti.endTail w χ A v = exp w • (χ' • v + χ • A v)`,

the weighted image of `χ • v` under `D_A`. For a finite family of ends `i` with cutoffs `χ i` and
spaces of free variables `K i`, `TauCeti.WeakDerivStep.endTailL` sends `(v i)ᵢ` to the class of
`∑ i, endTail w (χ i) A (v i)` in `Lᵖ`, and the extended operator is

`(trajectoryOperator AL).coprod (endTailL w χ A hmem)`,

with `AL` the class of `A - w' • id`. The results are:

* **the weighted-tail condition** (`TauCeti.memLp_endTail`): if `A v₀ = 0` for the limit `A₀` at
  the end, and `exp w * |χ| * ‖A - A₀‖` is bounded by a two-sided exponential `C exp (-ε |s|)`,
  then the end tail of `v ∈ ker A₀` lies in every `Lᵖ`. The bound holds when `‖A - A₀‖` decays at
  a rate `κ` larger than the growth rate `δ` of the weight on the support of the cutoff
  (`TauCeti.exp_mul_abs_mul_norm_sub_le`);
* **the kernel of the extended operator** (`TauCeti.WeakDerivStep.coprod_endTailL_eq_zero_iff`):
  `(ξ, v)` lies in it exactly when `u = exp (-w) • ξ + ∑ i, χ i • v i` solves `u' + A u = 0`. So
  the kernel corresponds to the solutions of this form. For a weight bounded below, `u` tends at
  each end to the free variable attached there
  (`TauCeti.WeakDerivStep.tendsto_exp_neg_smul_toZeroAtInfty_add_sum`);
* **the index** (`TauCeti.WeakDerivStep.index_coprod_endTailL`): when the weighted operator is
  Fredholm, so is the extended operator
  (`ContinuousLinearMap.IsFredholm.coprod_of_finiteDimensional`), and its index is
  `index D_{A - w'} + ∑ i, dim K i`.

**Symmetric limits and the Morse–Bott count.** For finite-dimensional `E` and symmetric limits
`A±`, the weighted operator is Fredholm as soon as the limits `δ±` of the slope `w'` are not
eigenvalues of `A±` (`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_sub_smul_id`), and its
index is `n_{< δ⁻}(A⁻) - n_{< δ⁺}(A⁺)`, where `n_{< δ}(B)` counts the eigenvalues of `B` below
`δ` with multiplicity. So the extended operator has index
`n_{< δ⁻}(A⁻) - n_{< δ⁺}(A⁺) + ∑ i, dim K i`
(`TauCeti.WeakDerivStep.index_coprod_endTailL_eq_finrank_pointSpectralSubspace_sub_finrank_add`).
Along a trajectory between critical manifolds `C` and `D` of a Morse–Bott function, the limits are
the Hessians at the ends, with `n_{< 0}(A⁻) = λ_C`, `ker A⁻ = T C`, `n_{< 0}(A⁺) = λ_D` and
`ker A⁺ = T D`. A decay weight at both ends below the spectral gaps, `δ⁻ < 0 < δ⁺` with no
eigenvalue of `A⁻` in `[δ⁻, 0)` and none of `A⁺` in `(0, δ⁺]`, counts the eigenvalue `0` of `A⁺`,
which lies below `δ⁺`, but not that of `A⁻`, which lies above `δ⁻`: the weighted operator has
index `λ_C - λ_D - dim D`. Adjoining the free variables `ker A⁻` at `-∞` and `ker A⁺` at `+∞`
adds `dim C + dim D`, and the extended operator has index `λ_C - λ_D + dim C`
(`index_coprod_endTailL_ker_eq_finrank_pointSpectralSubspace_sub_finrank_add`, in the namespace
`TauCeti.WeakDerivStep`). This is the dimension of the space of trajectories from `C` to `D`
before dividing by the translations of time. When `C` and `D` are critical points, the free
variables are zero and it is the Morse count `λ_C - λ_D`.

For the constant trajectory at a critical manifold filling `E`, the coefficient is `A = 0`. With
the weight `log cosh` the weighted operator is `d/ds - tanh s`, of index `-dim E`, and the two end
variables raise the index to `dim E`, the dimension of the critical manifold
(`TauCeti.WeakDerivStep.index_coprod_endTailL_neg_tanh_smul_id`, stated for any finite family of
free variables in `E`).

## References

* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) **12** (1985), 409–447 (weighted spaces with asymptotic
  kernel elements adjoined).
* F. Bourgeois, *A Morse–Bott approach to contact homology*, PhD thesis, Stanford, 2002,
  Chapter 4 (Fredholm theory for Morse–Bott asymptotics, with free asymptotic variables).
-/

public section

noncomputable section

open Filter MeasureTheory TopologicalSpace Set
open scoped ENNReal Topology

namespace TauCeti

section EndTail

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {w χ : ℝ → ℝ}
  {A : ℝ → F →L[ℝ] F}

/-- The **end tail** of a free endpoint variable `v`: the image `χ' • v + χ • A v` of its cutoff
extension `χ • v` under the trajectory operator `u ↦ u' + A u`, multiplied by the weight
`exp w`. -/
def endTail (w χ : ℝ → ℝ) (A : ℝ → F →L[ℝ] F) (v : F) (s : ℝ) : F :=
  Real.exp (w s) • (deriv χ s • v + χ s • A s v)

theorem endTail_apply (v : F) (s : ℝ) :
    endTail w χ A v s = Real.exp (w s) • (deriv χ s • v + χ s • A s v) := (rfl)

@[simp]
theorem endTail_zero : endTail w χ A (0 : F) = 0 := by
  ext s
  simp [endTail_apply]

theorem endTail_add (v v' : F) : endTail w χ A (v + v') = endTail w χ A v + endTail w χ A v' := by
  ext s
  simp only [endTail_apply, Pi.add_apply, map_add, smul_add]
  abel

theorem endTail_smul (c : ℝ) (v : F) : endTail w χ A (c • v) = c • endTail w χ A v := by
  ext s
  simp only [endTail_apply, Pi.smul_apply, map_smul, smul_add, smul_comm c]

theorem continuous_endTail (hw : Continuous w) (hχ : ContDiff ℝ 1 χ) (hA : Continuous A) (v : F) :
    Continuous (endTail w χ A v) :=
  hw.rexp.smul (((hχ.continuous_deriv le_rfl).smul continuous_const).add
    (hχ.continuous.smul (hA.clm_apply continuous_const)))

/-- **The weighted-tail condition.** Let `A₀` be the limit of `A` at an end and `v ∈ ker A₀`. If
the cutoff `χ` has compactly supported derivative and `exp w * |χ| * ‖A - A₀‖` is bounded by a
two-sided exponential, then the end tail of `v` lies in `Lᵖ`. -/
theorem memLp_endTail {p : ℝ≥0∞} (hw : Continuous w) (hχ : ContDiff ℝ 1 χ)
    (hχ' : HasCompactSupport (deriv χ)) (hA : Continuous A) {A₀ : F →L[ℝ] F} {v : F}
    (hv : A₀ v = 0) {C ε : ℝ} (hε : 0 < ε)
    (htail : ∀ s, Real.exp (w s) * |χ s| * ‖A s - A₀‖ ≤ C * Real.exp (-(ε * |s|))) :
    MemLp (endTail w χ A v) p := by
  -- The derivative of the cutoff contributes a compactly supported continuous term.
  have h₁ : MemLp (fun s ↦ (Real.exp (w s) * deriv χ s) • v) p :=
    ((hw.rexp.mul (hχ.continuous_deriv le_rfl)).smul continuous_const).memLp_of_hasCompactSupport
      (hχ'.mul_left.smul_right)
  -- The cutoff itself contributes a term dominated by the two-sided exponential.
  have h₂ : MemLp (fun s ↦ (Real.exp (w s) * χ s) • A s v) p := by
    refine ((memLp_exp_neg_mul_abs hε p).const_mul (C * ‖v‖)).of_le
      ((hw.rexp.mul hχ.continuous).smul (hA.clm_apply continuous_const)).aestronglyMeasurable
      (.of_forall fun s ↦ ?_)
    have hAv : A s v = (A s - A₀) v := by simp [hv]
    rw [hAv]
    simp only [norm_smul, Real.norm_eq_abs, abs_mul, Real.abs_exp, abs_norm]
    calc Real.exp (w s) * |χ s| * ‖(A s - A₀) v‖
        ≤ Real.exp (w s) * |χ s| * (‖A s - A₀‖ * ‖v‖) := by
          gcongr
          exact (A s - A₀).le_opNorm v
      _ = Real.exp (w s) * |χ s| * ‖A s - A₀‖ * ‖v‖ := by ring
      _ ≤ C * Real.exp (-(ε * |s|)) * ‖v‖ := mul_le_mul_of_nonneg_right (htail s) (norm_nonneg v)
      _ ≤ |C| * ‖v‖ * Real.exp (-(ε * |s|)) := by
          rw [mul_right_comm]
          gcongr
          exact le_abs_self C
  refine (h₁.add h₂).congr_norm (continuous_endTail hw hχ hA v).aestronglyMeasurable
    (.of_forall fun s ↦ ?_)
  simp [endTail_apply, smul_add, mul_smul]

/-- **Decay faster than the weight gives the weighted-tail bound.** If, on the support of a cutoff
`χ` with `|χ| ≤ 1`, the weight grows at most like `δ |s| + c` and `‖A - A₀‖` decays like
`C exp (-κ |s|)`, then `exp w * |χ| * ‖A - A₀‖` is bounded by the two-sided exponential
`C exp c exp (-(κ - δ) |s|)`, which decays when `δ < κ`. -/
theorem exp_mul_abs_mul_norm_sub_le (hχ : ∀ s, |χ s| ≤ 1) {A₀ : F →L[ℝ] F} {C c δ κ : ℝ}
    (hC : 0 ≤ C) (hw : ∀ s ∈ Function.support χ, w s ≤ δ * |s| + c)
    (hA : ∀ s ∈ Function.support χ, ‖A s - A₀‖ ≤ C * Real.exp (-(κ * |s|))) (s : ℝ) :
    Real.exp (w s) * |χ s| * ‖A s - A₀‖ ≤ C * Real.exp c * Real.exp (-((κ - δ) * |s|)) := by
  by_cases hs : χ s = 0
  · rw [hs, abs_zero, mul_zero, zero_mul]
    positivity
  calc Real.exp (w s) * |χ s| * ‖A s - A₀‖
      ≤ Real.exp (δ * |s| + c) * 1 * (C * Real.exp (-(κ * |s|))) := by
        gcongr
        · exact hw s hs
        · exact hχ s
        · exact hA s hs
    _ = C * Real.exp c * Real.exp (-((κ - δ) * |s|)) := by
        have : Real.exp (δ * |s| + c) * Real.exp (-(κ * |s|)) =
            Real.exp c * Real.exp (-((κ - δ) * |s|)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        linear_combination C * this

/-- For the zero coefficient and any continuous weight `w`, the end tail `exp w • χ' • v` of every
free variable lies in `Lᵖ`, whatever the cutoff, as long as its derivative has compact support. -/
theorem memLp_endTail_zero {p : ℝ≥0∞} (hw : Continuous w) (hχ : ContDiff ℝ 1 χ)
    (hχ' : HasCompactSupport (deriv χ)) (v : F) :
    MemLp (endTail w χ (fun _ ↦ 0) v) p :=
  memLp_endTail (A₀ := 0) (C := 0) hw hχ hχ' continuous_const rfl one_pos fun s ↦ by simp

end EndTail

namespace WeakDerivStep

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {w : ℝ → ℝ}
  {A : ℝ → F →L[ℝ] F} {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] {χ : ι → ℝ → ℝ}
  {K : ι → Submodule ℝ F} [∀ i, FiniteDimensional ℝ (K i)]

omit [Fact (1 ≤ p)] [∀ i, FiniteDimensional ℝ (K i)] in
/-- The sum of the end tails of a family of free variables lies in `Lᵖ`. -/
private theorem memLp_sum_endTail (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) p)
    (v : Π i, K i) :
    MemLp (fun s ↦ ∑ i, endTail w (χ i) A (v i) s) p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  (memLp_finsetSum _ fun i _ ↦ hmem i (v i) (v i).property).restrict _

/-- The **free endpoint variables** of a finite family of ends: the map sending `(v i)ᵢ`, with
`v i` in the space `K i` of free variables at the end `i` with cutoff `χ i`, to the class in `Lᵖ`
of the sum of their end tails. Adjoining it to the weighted trajectory operator gives the extended
operator `(trajectoryOperator AL).coprod (endTailL w χ A hmem)`. -/
def endTailL (w : ℝ → ℝ) (χ : ι → ℝ → ℝ) (A : ℝ → F →L[ℝ] F)
    (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) p) :
    (Π i, K i) →L[ℝ] Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun v := (memLp_sum_endTail hmem v).toLp _
      map_add' v v' := by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (.of_forall fun s ↦ ?_)
        simp [endTail_add, Finset.sum_add_distrib]
      map_smul' c v := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (.of_forall fun s ↦ ?_)
        simp [endTail_smul, Finset.smul_sum] }

theorem endTailL_apply_ae (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) p)
    (v : Π i, K i) :
    endTailL w χ A hmem v =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ ∑ i, endTail w (χ i) A (v i) s :=
  MemLp.coeFn_toLp (memLp_sum_endTail hmem v)

/-- The extended operator vanishes at `(ξ, v)` exactly when the weak derivative of `ξ` is,
almost everywhere, the right-hand side `w' ξ - A ξ - exp w • (S' + A S)` of the weighted
equation, with `S = ∑ i, χ i • v i`. -/
private theorem coprod_endTailL_eq_zero_iff_ae [CompleteSpace F] (hp : p ≠ ∞) {w' : ℝ → ℝ}
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) p)
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (v : Π i, K i) :
    (trajectoryOperator AL).coprod (endTailL w χ A hmem) (ξ, v) = 0 ↔
      (fun s ↦ weakFDeriv _ ξ s 1) =ᵐ[volume] fun s ↦
        w' s • toZeroAtInfty hp ξ s - A s (toZeroAtInfty hp ξ s) -
          Real.exp (w s) • (∑ i, deriv (χ i) s • (v i : F) + A s (∑ i, χ i s • (v i : F))) := by
  -- The end tails add up to the weighted image of `∑ i, χ i • v i` under `D_A`.
  have hT (s : ℝ) : ∑ i, endTail w (χ i) A (v i) s = Real.exp (w s) •
      (∑ i, deriv (χ i) s • (v i : F) + A s (∑ i, χ i s • (v i : F))) := by
    simp [endTail_apply, Finset.smul_sum, Finset.sum_add_distrib, map_sum]
  have hD := trajectoryOperator_apply_ae (p := p) AL ξ
  have hE := endTailL_apply_ae hmem v
  have hsum := Lp.coeFn_add (trajectoryOperator (p := p) AL ξ) (endTailL w χ A hmem v)
  have hprev := ae_restrict_of_ae (s := ((⊤ : Opens ℝ) : Set ℝ)) (prev_ae_eq_toZeroAtInfty hp ξ)
  rw [ContinuousLinearMap.coprod_apply, Lp.eq_zero_iff_ae_eq_zero,
    ← Measure.ae_restrict_coe_opens_top (volume : Measure ℝ)]
  constructor
  · intro h
    filter_upwards [hD, hE, hsum, hprev, hAL, h] with s hDs hEs hsums hprevs hALs h0s
    rw [hsums, Pi.add_apply, hDs, hEs, hALs, hprevs, hT] at h0s
    simp only [Pi.zero_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply] at h0s
    rw [← sub_eq_zero, ← h0s]
    abel
  · intro h
    filter_upwards [hD, hE, hsum, hprev, hAL, h] with s hDs hEs hsums hprevs hALs hs
    -- `rewrite` rather than `rw`: closing the goal by `rfl` would unfold the `Lᵖ` classes.
    rewrite [hsums, Pi.add_apply, hDs, hEs, hALs, hprevs, hT]
    simp only [Pi.zero_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply] at hs ⊢
    linear_combination (norm := module) hs

/-- **The kernel of the extended operator.** Let `AL` be the class of `A - w' • id`, the
trajectory operator on the weighted space conjugated by `exp w`. A pair `(ξ, v)` of a path
`ξ ∈ W^{1,p}` and free endpoint variables `v` lies in the kernel of the extended operator exactly
when `u = exp (-w) • ξ + ∑ i, χ i • v i`, with `ξ` read through its continuous representative,
solves `u' + A u = 0`. -/
theorem coprod_endTailL_eq_zero_iff [CompleteSpace F] (hp : p ≠ ∞) {w' : ℝ → ℝ}
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hA : Continuous A) {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) p)
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (v : Π i, K i) :
    (trajectoryOperator AL).coprod (endTailL w χ A hmem) (ξ, v) = 0 ↔
      ∀ s, HasDerivAt
        (fun s ↦ Real.exp (-w s) • toZeroAtInfty hp ξ s + ∑ i, χ i s • (v i : F))
        (-A s (Real.exp (-w s) • toZeroAtInfty hp ξ s + ∑ i, χ i s • (v i : F))) s := by
  set ξc := toZeroAtInfty (F := F) hp ξ
  have hS (s : ℝ) : HasDerivAt (fun s ↦ ∑ i, χ i s • (v i : F))
      (∑ i, deriv (χ i) s • (v i : F)) s :=
    HasDerivAt.fun_sum fun i _ ↦
      ((hχ i).differentiable one_ne_zero s).hasDerivAt.smul_const (v i : F)
  -- The right-hand side of the weighted equation is continuous, so the weak equation for `ξ`
  -- holds classically for its continuous representative.
  have hg : Continuous fun s ↦ w' s • ξc s - A s (ξc s) -
      Real.exp (w s) • (∑ i, deriv (χ i) s • (v i : F) + A s (∑ i, χ i s • (v i : F))) :=
    ((hw'.smul ξc.continuous).sub (hA.clm_apply ξc.continuous)).sub
      ((continuous_iff_continuousAt.2 fun s ↦ (hw s).continuousAt).rexp.smul
        ((continuous_finsetSum _ fun i _ ↦
          ((hχ i).continuous_deriv le_rfl).smul continuous_const).add
        (hA.clm_apply (continuous_iff_continuousAt.2 fun s ↦ (hS s).continuousAt))))
  rw [coprod_endTailL_eq_zero_iff_ae hp hAL hmem ξ v, ← forall_hasDerivAt_toZeroAtInfty_iff hp ξ hg]
  exact TauCeti.forall_hasDerivAt_iff_forall_hasDerivAt_exp_neg_smul_add hw hS

omit [∀ i, FiniteDimensional ℝ (K i)] in
/-- **The free endpoint variables are the limits of the solution.** If the weight `w` is
eventually bounded below along a filter `l` at infinity and each cutoff `χ i` tends to `a i` along
`l`, the path
`u = exp (-w) • ξ + ∑ i, χ i • v i` of a pair `(ξ, v)`, with `ξ` read through its continuous
representative, tends to `∑ i, a i • v i` along `l`. For two ends with cutoffs `χ 0` equal to `1`
near `-∞` and `0` near `+∞`, and `χ 1` the other way round, `u` tends to `v 0` at `-∞` and to
`v 1` at `+∞`. Together with `TauCeti.WeakDerivStep.coprod_endTailL_eq_zero_iff`, the kernel of the
extended operator consists of solutions of `u' + A u = 0` whose limits at the ends are the free
variables, and the projections to the free variables are the endpoint evaluations. -/
theorem tendsto_exp_neg_smul_toZeroAtInfty_add_sum [CompleteSpace F] (hp : p ≠ ∞) {l : Filter ℝ}
    (hl : l ≤ cocompact ℝ) {C : ℝ} (hw : ∀ᶠ s in l, C ≤ w s) {a : ι → ℝ}
    (hχ : ∀ i, Tendsto (χ i) l (𝓝 (a i)))
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (v : Π i, K i) :
    Tendsto (fun s ↦ Real.exp (-w s) • toZeroAtInfty hp ξ s + ∑ i, χ i s • (v i : F)) l
      (𝓝 (∑ i, a i • (v i : F))) := by
  -- The weighted path vanishes at infinity, and `exp (-w)` is bounded by `exp (-C)`.
  have hbdd : IsBoundedUnder (· ≤ ·) l (norm ∘ fun s ↦ Real.exp (-w s)) :=
    isBoundedUnder_of_eventually_le (a := Real.exp (-C)) (hw.mono fun s hs ↦ by
      rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (neg_le_neg hs))
  simpa using (hbdd.smul_tendsto_zero ((zero_at_infty (toZeroAtInfty hp ξ)).mono_left hl)).add
    (tendsto_finsetSum _ fun i _ ↦ (hχ i).smul_const (v i : F))

/-- **The index of the extended operator.** If the weighted trajectory operator is Fredholm,
adjoining the free endpoint variables raises its index by their number of dimensions. -/
theorem index_coprod_endTailL [CompleteSpace F]
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hD : (trajectoryOperator (p := p) AL).IsFredholm)
    (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) p) :
    ((trajectoryOperator (p := p) AL).coprod (endTailL w χ A hmem)).index =
      (trajectoryOperator (p := p) AL).index + ∑ i, (Module.finrank ℝ (K i) : ℤ) := by
  have := hD.finite_ker
  let : FiniteDimensional ℝ (_ ⧸ (trajectoryOperator (p := p) AL).range) := hD.finite_coker
  rw [ContinuousLinearMap.index_coprod, Module.finrank_pi_fintype, Nat.cast_sum]

section SymmetricLimits

/-! ### Symmetric limits and the Morse–Bott count -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The index of the extended operator with symmetric limits.** Let `A` be a continuous family
of operators on a finite-dimensional real inner product space with symmetric limits `A±` at `±∞`,
and let `c` be a continuous slope tending to `δ±` at `±∞`, where `δ±` is not an eigenvalue of
`A±`. Adjoining free endpoint variables in subspaces `K i` to the trajectory operator
`u ↦ u' + (A - c) u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` gives an operator of index
`n_{< δ⁻}(A⁻) - n_{< δ⁺}(A⁺) + ∑ i, dim K i`, where `n_{< δ}(B)` is the number of eigenvalues of
`B` below `δ`, counted with multiplicity. For `c = w'` the trajectory operator is the conjugate of
`D_A` on the spaces weighted by `exp w`, and the extended operator is the weighted operator with
free endpoint variables. Both operators are Fredholm, by
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_sub_smul_id` and
`ContinuousLinearMap.IsFredholm.coprod_of_finiteDimensional`. -/
theorem index_coprod_endTailL_eq_finrank_pointSpectralSubspace_sub_finrank_add
    {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {c : ℝ → ℝ} (hc : Continuous c) {δminus δplus : ℝ}
    (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (hδminus : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus)
    (hδplus : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus)
    {w : ℝ → ℝ} {χ : ι → ℝ → ℝ} {K : ι → Submodule ℝ E}
    (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) 2)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c s • ContinuousLinearMap.id ℝ E) :
    ((trajectoryOperator (p := 2) AL).coprod (endTailL w χ A hmem)).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio δminus)) : ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio δplus)) +
        ∑ i, (Module.finrank ℝ (K i) : ℤ) := by
  rw [index_coprod_endTailL (isFredholm_trajectoryOperator_sub_smul_id hA hsymminus hsymplus hbot
      htop hc hcbot hctop hδminus hδplus AL hAL) hmem,
    index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank hA hsymminus
      hsymplus hbot htop hc hcbot hctop hδminus hδplus AL hAL]

/-- **The Morse–Bott index of a linearized trajectory.** Let `A` be a continuous family of
operators on a finite-dimensional real inner product space with symmetric limits `A±` at `±∞`,
and let `c` be a continuous slope tending to `δ⁻ < 0` at `-∞` and to `δ⁺ > 0` at `+∞`, below the
spectral gaps at zero: `A⁻` has no eigenvalue in `[δ⁻, 0)` and `A⁺` has none in `(0, δ⁺]`. Adjoin
to the trajectory operator `u ↦ u' + (A - c) u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` the free
endpoint variables `ker A⁻` and `ker A⁺`, through any cutoffs `χ 0` and `χ 1`. The resulting
operator, which is Fredholm, has index `n_{< 0}(A⁻) - n_{< 0}(A⁺) + dim ker A⁻`, where
`n_{< 0}(B)` is the number of negative eigenvalues of `B`, counted with multiplicity.

For the linearization of the negative gradient flow of a Morse–Bott function along a trajectory
from a critical manifold `C` to a critical manifold `D`, with `ker A⁻ = T C` and `ker A⁺ = T D`
and the cutoffs attached to `-∞` and `+∞`, this is the count `λ_C - λ_D + dim C` of the dimension
of the trajectories from `C` to `D` before dividing by the translations of time. The weight counts
the eigenvalue `0` of `A⁺`, which lies below `δ⁺`, but not that of `A⁻`, which lies above `δ⁻`;
the free variables `ker A⁺` cancel the first, and `ker A⁻` contributes `dim C`. -/
theorem index_coprod_endTailL_ker_eq_finrank_pointSpectralSubspace_sub_finrank_add
    {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {c : ℝ → ℝ} (hc : Continuous c) {δminus δplus : ℝ}
    (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (hδminus : δminus < 0) (hδplus : 0 < δplus)
    (hgapminus : ∀ μ ∈ Ico δminus 0, ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) μ)
    (hgapplus : ∀ μ ∈ Ioc 0 δplus, ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) μ)
    {w : ℝ → ℝ} {χ : Fin 2 → ℝ → ℝ}
    (hmem : ∀ i, ∀ v ∈ ![LinearMap.ker (Aminus : E →ₗ[ℝ] E), LinearMap.ker (Aplus : E →ₗ[ℝ] E)] i,
      MemLp (endTail w (χ i) A v) 2)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c s • ContinuousLinearMap.id ℝ E) :
    ((trajectoryOperator (p := 2) AL).coprod (endTailL w χ A hmem)).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)) : ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio 0)) +
        Module.finrank ℝ (LinearMap.ker (Aminus : E →ₗ[ℝ] E)) := by
  rw [index_coprod_endTailL (isFredholm_trajectoryOperator_sub_smul_id hA hsymminus hsymplus hbot
      htop hc hcbot hctop (hgapminus δminus ⟨le_rfl, hδminus⟩) (hgapplus δplus ⟨hδplus, le_rfl⟩)
      AL hAL) hmem,
    index_trajectoryOperator_sub_smul_id_eq_finrank_sub_finrank_sub_finrank_ker hA hsymminus
      hsymplus hbot htop hc (δminus := -δminus) (neg_pos.2 hδminus) hδplus
      (by rwa [neg_neg]) hctop (by rwa [neg_neg]) hgapplus AL hAL,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

end SymmetricLimits

section ConstantTrajectory

/-! ### The constant trajectory at a critical manifold -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The constant trajectory at a critical manifold.** Along a constant trajectory at a critical
manifold filling `E`, the linearized coefficient is `A = 0`, whose limits have kernel `E`. With the
weight `log cosh`, of slope `tanh`, the weighted operator is `d/ds - tanh s`, of index `-dim E`.
Adjoining an arbitrary finite family `ι` of free variables in `E`, with arbitrary cutoffs `χ i`,
gives index `(card ι - 1) dim E`; this is index arithmetic and does not use the cutoffs. In the
Morse–Bott situation, which the theorem does not assume, `card ι = 2` with the cutoffs attached
to `-∞` and `+∞`, and the index is `dim E`, the dimension of the critical manifold, as the
Morse–Bott count `ind C - ind C + dim C` predicts for a trajectory from `C` to itself. -/
theorem index_coprod_endTailL_neg_tanh_smul_id {χ : ι → ℝ → ℝ} (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hχ' : ∀ i, HasCompactSupport (deriv (χ i)))
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) :
    ((trajectoryOperator (p := 2) AL).coprod (endTailL (K := fun _ ↦ ⊤)
      (fun s ↦ Real.log (Real.cosh s)) χ (fun _ ↦ 0)
      fun i v _ ↦ TauCeti.memLp_endTail_zero
        (Real.continuous_cosh.log fun s ↦ (Real.cosh_pos s).ne') (hχ i) (hχ' i) v)).index =
      (Fintype.card ι - 1 : ℤ) * Module.finrank ℝ E := by
  rw [index_coprod_endTailL (isFredholm_trajectoryOperator_neg_tanh_smul_id hAL),
    index_trajectoryOperator_neg_tanh_smul_id hAL]
  simp only [finrank_top, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end ConstantTrajectory

end WeakDerivStep

end TauCeti
