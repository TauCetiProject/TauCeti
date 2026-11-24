/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Parametric
public import TauCeti.Analysis.ODE.EnergyEstimate.Lyapunov
public import TauCeti.Analysis.ODE.EnergyEstimate.WeightCrossing
public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.Sobolev.GraphStep.ZeroAtInfty
import TauCeti.Analysis.Fredholm.Stabilization
import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel
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
  (`TauCeti.WeakDerivStep.tendsto_exp_neg_smul_toZeroAtInfty_add_sum`). Conversely, every
  solution `u` whose weighted difference `exp w • (u - ∑ i, χ i • v i)` lies in `Lᵖ` comes from
  the kernel (`TauCeti.WeakDerivStep.exists_coprod_endTailL_eq_zero_of_hasDerivAt`). For `p = 2`,
  reading off the initial value of `u` and the free variables identifies the kernel with the space
  `TauCeti.weightedAsymptoticSolutions` of such solutions
  (`TauCeti.WeakDerivStep.kerCoprodEndTailLEquiv`,
  `TauCeti.WeakDerivStep.finrank_ker_coprod_endTailL`), and the inverse recovers the path as the
  weighted difference of any such solution
  (`TauCeti.WeakDerivStep.coe_toZeroAtInfty_kerCoprodEndTailLEquiv_symm_apply`);
* **the index** (`TauCeti.WeakDerivStep.index_coprod_endTailL`): when the weighted operator is
  Fredholm, so is the extended operator
  (`ContinuousLinearMap.IsFredholm.coprod_of_finiteDimensional`), and its index is
  `index D_{A - w'} + ∑ i, dim K i`. For a continuous family on a finite-dimensional inner product
  space, the extended operator is Fredholm whenever the shifted limits `A± - δ± • id` have Lyapunov
  forms (`TauCeti.WeakDerivStep.isFredholm_coprod_endTailL_of_hasLyapunovForm`).

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

section WeightedAsymptoticSolutions

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]

/-- The **solutions with weighted asymptotics**: the pairs `(x, v)` of an initial value `x` and a
family `v` of free endpoint variables in the spaces `K i` for which some solution `u` of
`u' + A u = 0` with `u 0 = x` has square-integrable weighted difference
`exp w • (u - ∑ i, χ i • v i)`. This is a model of the kernel of the extended operator
(`TauCeti.WeakDerivStep.kerCoprodEndTailLEquiv`), as `TauCeti.squareIntegrableSolutions` is of the
kernel of the trajectory operator. -/
def weightedAsymptoticSolutions (A : ℝ → F →L[ℝ] F) (w : ℝ → ℝ) (K : ι → Submodule ℝ F)
    (χ : ι → ℝ → ℝ) : Submodule ℝ (F × Π i, K i) where
  carrier := {q | ∃ u : ℝ → F, u 0 = q.1 ∧ (∀ s, HasDerivAt u (-A s (u s)) s) ∧
    MemLp (fun s ↦ Real.exp (w s) • (u s - ∑ i, χ i s • (q.2 i : F))) 2}
  zero_mem' := ⟨0, rfl, fun s ↦ by simp, by simp⟩
  add_mem' := by
    rintro ⟨_, v⟩ ⟨_, v'⟩ ⟨u, rfl, hu, hu2⟩ ⟨u', rfl, hu', hu'2⟩
    refine ⟨u + u', rfl, fun s ↦ by simpa [add_comm] using (hu s).add (hu' s), ?_⟩
    convert hu2.add hu'2 using 1
    ext s
    simp only [Prod.snd_add, Pi.add_apply, Submodule.coe_add, smul_add, Finset.sum_add_distrib]
    module
  smul_mem' := by
    rintro c ⟨_, v⟩ ⟨u, rfl, hu, hu2⟩
    refine ⟨c • u, rfl, fun s ↦ by simpa using (hu s).const_smul c, ?_⟩
    convert hu2.const_smul c using 1
    ext s
    simp only [Prod.smul_snd, Pi.smul_apply, SetLike.val_smul, Finset.smul_sum, smul_sub,
      smul_comm c]

/-- A pair lies in `TauCeti.weightedAsymptoticSolutions A w K χ` when its first component is the
initial value of a solution of `u' + A u = 0` whose weighted difference from its free endpoint
variables is square integrable. -/
theorem mem_weightedAsymptoticSolutions {A : ℝ → F →L[ℝ] F} {w : ℝ → ℝ} {K : ι → Submodule ℝ F}
    {χ : ι → ℝ → ℝ} {q : F × Π i, K i} :
    q ∈ weightedAsymptoticSolutions A w K χ ↔
      ∃ u : ℝ → F, u 0 = q.1 ∧ (∀ s, HasDerivAt u (-A s (u s)) s) ∧
        MemLp (fun s ↦ Real.exp (w s) • (u s - ∑ i, χ i s • (q.2 i : F))) 2 :=
  Iff.rfl

end WeightedAsymptoticSolutions

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

omit [∀ i, FiniteDimensional ℝ (K i)] in
/-- The end tails of a family of free variables add up to the weighted image
`exp w • (S' + A S)` of `S = ∑ i, χ i • v i` under `u ↦ u' + A u`. -/
private theorem sum_endTail_apply (v : Π i, K i) (s : ℝ) :
    ∑ i, endTail w (χ i) A (v i) s = Real.exp (w s) •
      (∑ i, deriv (χ i) s • (v i : F) + A s (∑ i, χ i s • (v i : F))) := by
  simp [endTail_apply, Finset.smul_sum, Finset.sum_add_distrib, map_sum]

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
  have hD := trajectoryOperator_apply_ae (p := p) AL ξ
  have hE := endTailL_apply_ae hmem v
  have hsum := Lp.coeFn_add (trajectoryOperator (p := p) AL ξ) (endTailL w χ A hmem v)
  have hprev := ae_restrict_of_ae (s := ((⊤ : Opens ℝ) : Set ℝ)) (prev_ae_eq_toZeroAtInfty hp ξ)
  rw [ContinuousLinearMap.coprod_apply, Lp.eq_zero_iff_ae_eq_zero,
    ← Measure.ae_restrict_coe_opens_top (volume : Measure ℝ)]
  constructor
  · intro h
    filter_upwards [hD, hE, hsum, hprev, hAL, h] with s hDs hEs hsums hprevs hALs h0s
    rw [hsums, Pi.add_apply, hDs, hEs, hALs, hprevs, sum_endTail_apply] at h0s
    simp only [Pi.zero_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply] at h0s
    rw [← sub_eq_zero, ← h0s]
    abel
  · intro h
    filter_upwards [hD, hE, hsum, hprev, hAL, h] with s hDs hEs hsums hprevs hALs hs
    -- `rewrite` rather than `rw`: closing the goal by `rfl` would unfold the `Lᵖ` classes.
    rewrite [hsums, Pi.add_apply, hDs, hEs, hALs, hprevs, sum_endTail_apply]
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

/-- **Solutions with weighted asymptotics come from the kernel.** Let `AL` be the class of
`A - w' • id`. If `u` solves `u' + A u = 0` and its weighted difference
`exp w • (u - ∑ i, χ i • v i)` from the free endpoint variables `v` lies in `Lᵖ`, then that
difference is the value of a path `ξ` with `(ξ, v)` in the kernel of the extended operator. This
is the converse of `TauCeti.WeakDerivStep.coprod_endTailL_eq_zero_iff`. -/
theorem exists_coprod_endTailL_eq_zero_of_hasDerivAt [CompleteSpace F] {w' : ℝ → ℝ}
    (hw : ∀ s, HasDerivAt w (w' s) s) (hχ : ∀ i, Differentiable ℝ (χ i))
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) p)
    {u : ℝ → F} (hu : ∀ s, HasDerivAt u (-A s (u s)) s) (v : Π i, K i)
    (hv : MemLp (fun s ↦ Real.exp (w s) • (u s - ∑ i, χ i s • (v i : F))) p) :
    ∃ ξ, (trajectoryOperator AL).coprod (endTailL w χ A hmem) (ξ, v) = 0 ∧
      ⇑(prev (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ξ)
        =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
          fun s ↦ Real.exp (w s) • (u s - ∑ i, χ i s • (v i : F)) := by
  set ψ : ℝ → F := fun s ↦ Real.exp (w s) • (u s - ∑ i, χ i s • (v i : F))
  set g : ℝ → F := fun s ↦ -∑ i, endTail w (χ i) A (v i) s
  have hS (s : ℝ) : HasDerivAt (fun s ↦ ∑ i, χ i s • (v i : F))
      (∑ i, deriv (χ i) s • (v i : F)) s :=
    HasDerivAt.fun_sum fun i _ ↦ ((hχ i) s).hasDerivAt.smul_const (v i : F)
  -- `ψ` solves the weighted equation `ψ' = g - (A - w') ψ`: it is the change of unknown of the
  -- solution `u = exp (-w) • ψ + ∑ i, χ i • v i`.
  have hψ (s : ℝ) : HasDerivAt ψ (g s - (A s - w' s • ContinuousLinearMap.id ℝ F) (ψ s)) s := by
    refine ((forall_hasDerivAt_iff_forall_hasDerivAt_exp_neg_smul_add (A := A) hw hS).mpr
      (fun s ↦ ?_) s).congr_deriv ?_
    · simpa only [ψ, Real.exp_neg, inv_smul_smul₀ (Real.exp_pos _).ne', sub_add_cancel]
        using hu s
    · simp only [g, sum_endTail_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply]
      abel
  have hg : MemLp g p := (memLp_finsetSum _ fun i _ ↦ hmem i _ (v i).property).neg
  obtain ⟨ξ, hξ, hξψ⟩ := exists_trajectoryOperator_ae_eq_of_hasDerivAt hAL hψ hv hg
  refine ⟨ξ, ?_, hξψ⟩
  rw [ContinuousLinearMap.coprod_apply, Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [Lp.coeFn_add (trajectoryOperator AL ξ) (endTailL w χ A hmem v), hξ,
    endTailL_apply_ae hmem v] with s hs h1 h2
  rw [hs, Pi.add_apply, h1, h2, neg_add_cancel, Pi.zero_apply]

section Kernel

/-! ### The kernel of the extended operator -/

variable [CompleteSpace F] {w' : ℝ → ℝ}
  {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
  {hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) 2}

omit [∀ i, FiniteDimensional ℝ (K i)] in
variable (w χ) in
/-- Evaluation `(ξ, v) ↦ (exp (-w 0) • ξ 0 + ∑ i, χ i 0 • v i, v)` at time `0`, through the
continuous representative of `ξ`: on the kernel of the extended operator, the initial value of
the solution `u = exp (-w) • ξ + ∑ i, χ i • v i` together with the free endpoint variables. -/
private def freeEndpointEval :
    (WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
      Π i, K i) →ₗ[ℝ] F × Π i, K i where
  toFun q := (Real.exp (-w 0) • toZeroAtInfty ENNReal.ofNat_ne_top q.1 0 +
    ∑ i, χ i 0 • (q.2 i : F), q.2)
  map_add' q q' := by
    rw [Prod.mk_add_mk]
    congr 1
    simp only [map_add, FunLike.coe_add,
      Pi.add_apply, Submodule.coe_add, smul_add, Finset.sum_add_distrib]
    abel
  map_smul' c q := by
    rw [RingHom.id_apply, Prod.smul_mk]
    congr 1
    simp only [map_smul, FunLike.coe_smul,
      Pi.smul_apply, SetLike.val_smul, smul_add, Finset.smul_sum, smul_comm c]

omit [∀ i, FiniteDimensional ℝ (K i)] in
private theorem freeEndpointEval_apply
    (q : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
      Π i, K i) :
    freeEndpointEval w χ q = (Real.exp (-w 0) • toZeroAtInfty ENNReal.ofNat_ne_top q.1 0 +
      ∑ i, χ i 0 • (q.2 i : F), q.2) :=
  rfl

/-- The evaluation of a kernel element is a solution with weighted asymptotics. -/
private theorem freeEndpointEval_mem (hA : Continuous A) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    {q : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
      Π i, K i}
    (h0 : (trajectoryOperator AL).coprod (endTailL w χ A hmem) q = 0) :
    freeEndpointEval w χ q ∈ weightedAsymptoticSolutions A w K χ := by
  obtain ⟨ξ, v⟩ := q
  refine ⟨fun s ↦ Real.exp (-w s) • toZeroAtInfty ENNReal.ofNat_ne_top ξ s +
      ∑ i, χ i s • (v i : F), by rw [freeEndpointEval_apply],
    (coprod_endTailL_eq_zero_iff ENNReal.ofNat_ne_top hw hw' hχ hA hAL hmem ξ v).1 h0, ?_⟩
  have hξ : MemLp (toZeroAtInfty ENNReal.ofNat_ne_top ξ) 2 := by
    simpa using (Lp.memLp (prev (ContinuousLinearMap.id ℝ
      (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ξ)).ae_eq
        (ae_restrict_of_ae (prev_ae_eq_toZeroAtInfty ENNReal.ofNat_ne_top ξ))
  convert hξ using 1
  funext s
  simp only [freeEndpointEval_apply, add_sub_cancel_right, Real.exp_neg,
    smul_inv_smul₀ (Real.exp_pos _).ne']

/-- A kernel element with zero evaluation vanishes: its solution has zero initial value, hence
vanishes, and its free endpoint variables are zero. -/
private theorem eq_zero_of_freeEndpointEval_eq_zero (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    {q : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
      Π i, K i}
    (h0 : (trajectoryOperator AL).coprod (endTailL w χ A hmem) q = 0)
    (he : freeEndpointEval w χ q = 0) : q = 0 := by
  obtain ⟨ξ, v⟩ := q
  have hu := (coprod_endTailL_eq_zero_iff ENNReal.ofNat_ne_top hw hw' hχ hA hAL hmem ξ v).1 h0
  rw [freeEndpointEval_apply, Prod.mk_eq_zero] at he
  obtain ⟨he₁, rfl⟩ := he
  have hz (s : ℝ) : HasDerivAt (0 : ℝ → F) (-A s ((0 : ℝ → F) s)) s := by
    simp
  have hu0 := hA.neg.eq_of_hasDerivAt_clm_apply hu hz (t₀ := 0) he₁
  have hξ : toZeroAtInfty ENNReal.ofNat_ne_top ξ = 0 := by
    ext s
    simpa using congrFun hu0 s
  rw [Prod.mk_eq_zero]
  exact ⟨toZeroAtInfty_injective ENNReal.ofNat_ne_top (hξ.trans (map_zero _).symm), rfl⟩

/-- Evaluation on the kernel of the extended operator, with values in the solutions with weighted
asymptotics. -/
private def kerFreeEndpointEval (hA : Continuous A) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) :
    ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).ker →ₗ[ℝ]
      weightedAsymptoticSolutions A w K χ :=
  ((freeEndpointEval w χ).domRestrict
    ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).ker).codRestrict _
    fun q ↦ freeEndpointEval_mem hA hw hw' hχ hAL q.property

private theorem kerFreeEndpointEval_apply (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    (q : ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).ker) :
    (kerFreeEndpointEval hA hw hw' hχ hAL q : F × Π i, K i) = freeEndpointEval w χ q := by
  unfold kerFreeEndpointEval
  exact (LinearMap.codRestrict_apply _ _ q).trans (LinearMap.domRestrict_apply _ _ _)

private theorem bijective_kerFreeEndpointEval (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) :
    Function.Bijective (kerFreeEndpointEval (hmem := hmem) hA hw hw' hχ hAL) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun q he ↦ Subtype.ext ?_, fun y ↦ ?_⟩
  · exact eq_zero_of_freeEndpointEval_eq_zero hA hw hw' hχ hAL q.property
      (congrArg Subtype.val he)
  · obtain ⟨⟨x, v⟩, hy⟩ := y
    -- Unification of these membership and existence statements against their uses is slow, so
    -- their implicit arguments are given and the existential is destructured by `obtain`.
    have hy' := (mem_weightedAsymptoticSolutions (A := A) (w := w) (K := K) (χ := χ)
      (q := (x, v))).1 hy
    obtain ⟨u, hu0, hu, hv⟩ := hy'
    dsimp only at hu0 hv
    have key := exists_coprod_endTailL_eq_zero_of_hasDerivAt (A := A) (w := w) (K := K) (χ := χ)
      (p := 2) (AL := AL) (hmem := hmem) (w' := w') hw
      (fun i ↦ (hχ i).differentiable one_ne_zero) hAL hu v hv
    obtain ⟨ξ, h0, hξ⟩ := key
    refine ⟨⟨(ξ, v), h0⟩, Subtype.ext ?_⟩
    -- The continuous representative of `ξ` is the weighted difference of `u` everywhere.
    have hc : ⇑(toZeroAtInfty ENNReal.ofNat_ne_top ξ) =
        fun s ↦ Real.exp (w s) • (u s - ∑ i, χ i s • (v i : F)) :=
      coe_toZeroAtInfty_eq_of_ae_eq ENNReal.ofNat_ne_top
        ((continuous_iff_continuousAt.2 fun s ↦ (hw s).continuousAt).rexp.smul
          ((continuous_iff_continuousAt.2 fun s ↦ (hu s).continuousAt).sub
            (continuous_finsetSum _ fun i _ ↦ (hχ i).continuous.smul continuous_const)))
        (by simpa using hξ)
    rw [kerFreeEndpointEval_apply, freeEndpointEval_apply]
    simp only [hc, Real.exp_neg, inv_smul_smul₀ (Real.exp_pos _).ne', sub_add_cancel]
    exact Prod.ext hu0 rfl

/-- **The kernel of the extended operator is the space of solutions with weighted asymptotics.**
Let `A` be continuous, `w` differentiable with continuous derivative `w'`, the cutoffs `χ i` of
class `C¹`, and `AL` the class of `A - w' • id`. Sending a kernel element `(ξ, v)` to the initial
value of the solution `u = exp (-w) • ξ + ∑ i, χ i • v i` of `u' + A u = 0`
(`TauCeti.WeakDerivStep.coprod_endTailL_eq_zero_iff`), together with `v`, is a linear equivalence
onto `TauCeti.weightedAsymptoticSolutions A w K χ`. -/
def kerCoprodEndTailLEquiv (hA : Continuous A) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) :
    ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).ker ≃ₗ[ℝ]
      weightedAsymptoticSolutions A w K χ :=
  LinearEquiv.ofBijective _ (bijective_kerFreeEndpointEval hA hw hw' hχ hAL)

/-- The equivalence `TauCeti.WeakDerivStep.kerCoprodEndTailLEquiv` sends a kernel element `(ξ, v)`
to `(u 0, v)`, for the solution `u = exp (-w) • ξ + ∑ i, χ i • v i`, with `ξ` read through its
continuous representative. -/
theorem kerCoprodEndTailLEquiv_apply (hA : Continuous A) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    (q : ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).ker) :
    (kerCoprodEndTailLEquiv hA hw hw' hχ hAL q : F × Π i, K i) =
      (Real.exp (-w 0) • toZeroAtInfty ENNReal.ofNat_ne_top q.val.1 0 +
        ∑ i, χ i 0 • (q.val.2 i : F), q.val.2) := by
  rw [kerCoprodEndTailLEquiv, LinearEquiv.ofBijective_apply, kerFreeEndpointEval_apply,
    freeEndpointEval_apply]

/-- The equivalence `TauCeti.WeakDerivStep.kerCoprodEndTailLEquiv` keeps the free endpoint
variables. -/
theorem kerCoprodEndTailLEquiv_apply_snd (hA : Continuous A) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    (q : ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).ker) :
    (kerCoprodEndTailLEquiv hA hw hw' hχ hAL q : F × Π i, K i).2 = q.val.2 := by
  rw [kerCoprodEndTailLEquiv_apply]

/-- The inverse of `TauCeti.WeakDerivStep.kerCoprodEndTailLEquiv` keeps the free endpoint
variables. -/
theorem kerCoprodEndTailLEquiv_symm_apply_snd (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    (y : weightedAsymptoticSolutions A w K χ) :
    ((kerCoprodEndTailLEquiv (hmem := hmem) hA hw hw' hχ hAL).symm y).val.2 = y.val.2 := by
  rw [← kerCoprodEndTailLEquiv_apply_snd hA hw hw' hχ hAL, LinearEquiv.apply_symm_apply]

/-- The inverse of `TauCeti.WeakDerivStep.kerCoprodEndTailLEquiv` sends `(x, v)` to the pair whose
path, read through its continuous representative, is the weighted difference
`exp w • (u - ∑ i, χ i • v i)` of any solution `u` of `u' + A u = 0` with `u 0 = x`. -/
theorem coe_toZeroAtInfty_kerCoprodEndTailLEquiv_symm_apply (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    (y : weightedAsymptoticSolutions A w K χ) {u : ℝ → F} (hu0 : u 0 = y.val.1)
    (hu : ∀ s, HasDerivAt u (-A s (u s)) s) :
    ⇑(toZeroAtInfty ENNReal.ofNat_ne_top
        ((kerCoprodEndTailLEquiv (hmem := hmem) hA hw hw' hχ hAL).symm y).val.1) =
      fun s ↦ Real.exp (w s) • (u s - ∑ i, χ i s • (y.val.2 i : F)) := by
  obtain ⟨q, rfl⟩ := (kerCoprodEndTailLEquiv (hmem := hmem) hA hw hw' hχ hAL).surjective y
  simp only [kerCoprodEndTailLEquiv_apply] at hu0
  rw [LinearEquiv.symm_apply_apply, kerCoprodEndTailLEquiv_apply_snd]
  -- The path of `q` and `u` solve `u' + A u = 0` with the same initial value, so they agree.
  rw [← hA.neg.eq_of_hasDerivAt_clm_apply
    ((coprod_endTailL_eq_zero_iff ENNReal.ofNat_ne_top hw hw' hχ hA hAL hmem q.val.1 q.val.2).1
      q.property) hu (t₀ := 0) hu0.symm]
  funext s
  simp only [add_sub_cancel_right, Real.exp_neg, smul_inv_smul₀ (Real.exp_pos _).ne']

/-- The kernel of the extended operator has the dimension of the space of solutions with weighted
asymptotics. -/
theorem finrank_ker_coprod_endTailL (hA : Continuous A) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) :
    Module.finrank ℝ ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).ker =
      Module.finrank ℝ (weightedAsymptoticSolutions A w K χ) :=
  (kerCoprodEndTailLEquiv hA hw hw' hχ hAL).finrank_eq

end Kernel

/-- **The extended operator with hyperbolic shifted limits is Fredholm.** Let `A` be a continuous
family of operators on a finite-dimensional real inner product space with limits `A±` at `±∞`, and
`w'` a continuous weight slope with limits `δ±`. If the shifted limits `A± - δ± • id` have Lyapunov
forms, that is, have no purely imaginary eigenvalue, then for the class `AL` of `A - w' • id` the
extended operator is Fredholm. Unlike
`TauCeti.WeakDerivStep.index_coprod_endTailL_eq_finrank_pointSpectralSubspace_sub_finrank_add`,
the limits need not be symmetric. -/
theorem isFredholm_coprod_endTailL_of_hasLyapunovForm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {A : ℝ → E →L[ℝ] E} {K : ι → Submodule ℝ E}
    {w' : ℝ → ℝ} (hA : Continuous A) (hw' : Continuous w') {Aminus Aplus : E →L[ℝ] E}
    {δminus δplus : ℝ} (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus))
    (hminus : (Aminus - δminus • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    (hplus : (Aplus - δplus • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ E)
    (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) 2) :
    ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).IsFredholm :=
  (isFredholm_trajectoryOperator_of_hasLyapunovForm (hA.sub (hw'.smul continuous_const)) hminus
    hplus (hbot.sub (hw'bot.smul tendsto_const_nhds)) (htop.sub (hw'top.smul tendsto_const_nhds))
    AL hAL).coprod_of_finiteDimensional _

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
