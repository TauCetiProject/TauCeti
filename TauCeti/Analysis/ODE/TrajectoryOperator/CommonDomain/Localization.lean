/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Family
public import TauCeti.Analysis.Sobolev.GraphStep.Multiplication
import TauCeti.Analysis.Calculus.BumpFunction.LinePartition
import TauCeti.Analysis.InnerProductSpace.Symmetric.Basic
import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.SemiFredholm
import TauCeti.Analysis.Normed.Operator.Compact.Estimate

/-!
# The semi-Fredholm estimate for continuous families over a common domain, by localization

Let `ι : D →L[ℝ] H` embed a Banach space `D` into a Hilbert space `H`, and let
`A : ℝ → (D →L[ℝ] H)` be a continuous family of operators, `ι`-symmetric
(`⟪A(s) x, ι y⟫ = ⟪ι x, A(s) y⟫`), such that each `A(s) - c ι` is invertible for some real `c`, and
with invertible limits `A±` at `±∞`. This is the setting of a path of self-adjoint operators with
common domain `D` and limits that have no kernel, such as the operators `A(s) = J ∂ₜ + S(s, t)` on
paths `t ↦ ξ(t)`, with `D = H¹` and `H = L²`, of the linearized Floer operator
`∂ₛ + J ∂ₜ + S` on a strip. This file proves that the operator
`u ↦ (ι ∘ u)' + A(s) u(s)` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)`
(`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator`) satisfies the **semi-Fredholm estimate**

`‖u‖ ≤ C (‖(ι ∘ u)' + A u‖ + ‖ι ∘ u‖_{L²((-T, T), H)})`

for some `C` and `T`
(`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_of_continuous`).
When `ι` is compact, the restriction of `ι ∘ u` to `(-T, T)` is a compact operator on the graph
space (`TauCeti.WeakDerivStep.isCompactOperator_restrictBaseL_compLpL`, an Aubin–Lions lemma), so
Peetre's lemma gives the operator a **finite-dimensional kernel and closed range**
(`finiteDimensional_ker_familyDomainTrajectoryOperator_of_continuous`,
`isClosed_range_familyDomainTrajectoryOperator_of_continuous`).

The hypotheses on `A` are local in `s`: no bound of `A(s) - A₊` through `ι` is assumed, so the
operators `A(s)` may differ from their limits by operators that are unbounded on `H`, as when the
principal part `J ∂ₜ` above varies with `s`. The price is the continuity of `A` in `D →L[ℝ] H`.
The same estimate for families that differ from their limit at `+∞` by operators bounded through
`ι`, with no continuity assumed, is
`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL` in
`TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.SemiFredholm`; neither statement implies the
other.

## Proof

The estimate is spliced from local ones by a partition of unity.

* **Ends.** Near `±∞` the coefficient is close to its invertible symmetric limit, so paths
  supported near `+∞` or near `-∞` satisfy `‖u‖ ≤ C ‖(ι ∘ u)' + A u‖`
  (`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop` and
  `..._atBot`).
* **Finite times.** Near a time `s₀`, freezing the coefficient at `A(s₀) - c ι`, which is
  invertible, gives `‖u‖ ≤ C (‖(ι ∘ u)' + A u‖ + |c| ‖ι ∘ u‖)` for paths supported near `s₀`
  (`exists_mem_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_of_tendsto`).
* **Splicing.** Cover a compact interval `[-T₀, T₀]` outside which the end estimates hold by
  finitely many such neighbourhoods, take a smooth partition of unity `∑ ψᵢ = 1` subordinate to
  them and to the two ends (`TauCeti.exists_contDiff_finset_sum_eq_one_of_mem_nhds`), and estimate
  each `ψᵢ u`; these add up to `u` (`TauCeti.WeakDerivStep.sum_smulLeftCLM`). Multiplication
  by `ψᵢ` (`TauCeti.WeakDerivStep.smulLeftCLM`) satisfies the Leibniz rule
  `(ι ∘ (ψ u))' + A (ψ u) = ψ ((ι ∘ u)' + A u) + ψ' (ι ∘ u)`
  (`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator_smulLeftCLM_ae`), and the
  commutator term `ψ' (ι ∘ u)` and the local error terms `ι ∘ (ψ u)` live in a fixed bounded window
  `(-T, T)`.

The estimate is the first half of the Fredholm theory of `∂ₛ + A(s)`; the finiteness of the
cokernel and the identification of the index with the spectral flow of `A` are not proved here.

## Main results

* `exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_of_continuous`:
  the semi-Fredholm estimate.
* `finiteDimensional_ker_familyDomainTrajectoryOperator_of_continuous`,
  `isClosed_range_familyDomainTrajectoryOperator_of_continuous`: for a compact embedding `ι`,
  finite-dimensional kernel and closed range.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §3 (the Fredholm property of `d/ds + A(s)`, proved by splicing estimates
  near the ends with a compact error on a bounded interval).
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace Topology

section Line

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι : D →L[ℝ] H}

omit [CompleteSpace D] in
/-- If `|ψ| ≤ c` and `ψ` vanishes off `(-T, T)`, then `‖ι ∘ (ψ u)‖ ≤ c ‖ι ∘ u‖_{L²((-T, T), H)}`. -/
private theorem norm_compLpL_prev_smulLeftCLM_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ ψ x‖ ≤ C)
    {c T : ℝ} (hc : ∀ s, |ψ s| ≤ c) (hT : ∀ s ∉ Ioo (-T) T, ψ s = 0)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖ι.compLpL 2 μ₀
      (prev _ (smulLeftCLM ψ hψ.contDiffOn h₀ h₁ ι.compLpL_multiplicationOperator u))‖ ≤
      c * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖ := by
  have hae : ae volume = ae μ₀ := by simp
  have hf : ∀ᵐ s ∂volume, ι.compLpL 2 μ₀
      (prev _ (smulLeftCLM ψ hψ.contDiffOn h₀ h₁ ι.compLpL_multiplicationOperator u)) s =
        ψ s • ι (prev _ u s) := by
    filter_upwards [(ι.coeFn_compLpL
        (prev _ (smulLeftCLM ψ hψ.contDiffOn h₀ h₁ ι.compLpL_multiplicationOperator u))).filter_mono
          hae.le,
      (prev_smulLeftCLM_ae hψ.contDiffOn h₀ h₁ ι.compLpL_multiplicationOperator u).filter_mono
        hae.le] with s hs hψs
    rw [hs, hψs, map_smul]
  refine norm_le_mul_norm_restrictBaseL ((abs_nonneg _).trans (hc 0)) u ?_ ?_
  · filter_upwards [hf] with s hs
    rw [hs, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hc s) (norm_nonneg _)
  · filter_upwards [hf] with s hs hsT
    rw [hs, hT s hsT, zero_smul]

omit [CompleteSpace D] in
/-- **Splicing local estimates.** Let `∑ᵢ ψᵢ = 1` be a finite smooth partition of unity on `ℝ` by
functions with bounded derivatives vanishing off `(-T, T)`, and suppose that each `ψᵢ u` satisfies
`‖ψᵢ u‖ ≤ Cᵢ (‖(ι ∘ ψᵢ u)' + A (ψᵢ u)‖ + ‖ι ∘ u‖_{L²((-T, T), H)})`. Then
`‖u‖ ≤ C (‖(ι ∘ u)' + A u‖ + ‖ι ∘ u‖_{L²((-T, T), H)})` for some `C`. -/
private theorem exists_forall_norm_le_of_sum_eq_one (AL : Lp (D →L[ℝ] H) ∞ μ₀) {κ : Type*}
    (t : Finset κ) (ψ : κ → ℝ → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (h₀ : ∀ i, ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖ψ i x‖ ≤ C)
    (h₁ : ∀ i, ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ (ψ i) x‖ ≤ C) (hsum : ∀ x, ∑ i ∈ t, ψ i x = 1)
    {T : ℝ} (hT : ∀ i ∈ t, ∀ s ∉ Ioo (-T) T, deriv (ψ i) s = 0)
    (hest : ∀ i ∈ t, ∃ C : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      ‖smulLeftCLM (ψ i) (hψ i).contDiffOn (h₀ i) (h₁ i) ι.compLpL_multiplicationOperator u‖ ≤
        C * (‖familyDomainTrajectoryOperator ι AL
          (smulLeftCLM (ψ i) (hψ i).contDiffOn (h₀ i) (h₁ i) ι.compLpL_multiplicationOperator u)‖ +
          ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖)) :
    ∃ C : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      ‖u‖ ≤ C * (‖familyDomainTrajectoryOperator ι AL u‖ +
        ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖) := by
  choose! C hC using hest
  have hc₀' (i : κ) (s : ℝ) : |ψ i s| ≤ |(h₀ i).choose| :=
    ((Real.norm_eq_abs _).symm.trans_le ((h₀ i).choose_spec s trivial)).trans (le_abs_self _)
  have hc₁' (i : κ) (s : ℝ) : |deriv (ψ i) s| ≤ |(h₁ i).choose| := by
    rw [← Real.norm_eq_abs, norm_deriv_eq_norm_fderiv]
    exact ((h₁ i).choose_spec s trivial).trans (le_abs_self _)
  refine ⟨∑ i ∈ t, |C i| * (|(h₀ i).choose| + |(h₁ i).choose| + 1), fun u ↦ ?_⟩
  set Du := ‖familyDomainTrajectoryOperator ι AL u‖
  set Ku := ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖
  have hpiece : ∀ i ∈ t,
      ‖smulLeftCLM (ψ i) (hψ i).contDiffOn (h₀ i) (h₁ i) ι.compLpL_multiplicationOperator u‖ ≤
      |C i| * (|(h₀ i).choose| + |(h₁ i).choose| + 1) * (Du + Ku) := fun i hi ↦ by
    have hD := norm_familyDomainTrajectoryOperator_smulLeftCLM_le (hψ i).contDiffOn (h₀ i) (h₁ i)
      (hc₀' i) (hc₁' i) (hT i hi) AL u
    refine (hC i hi u).trans ((mul_le_mul_of_nonneg_right (le_abs_self _)
      (by positivity)).trans ?_)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    nlinarith [abs_nonneg (h₀ i).choose, abs_nonneg (h₁ i).choose,
      (norm_nonneg _ : 0 ≤ Du), (norm_nonneg _ : 0 ≤ Ku)]
  calc ‖u‖ = ‖∑ i ∈ t,
        smulLeftCLM (ψ i) (hψ i).contDiffOn (h₀ i) (h₁ i) ι.compLpL_multiplicationOperator u‖ := by
        rw [sum_smulLeftCLM t ψ (fun i ↦ (hψ i).contDiffOn) h₀ h₁ ι.compLpL_multiplicationOperator
          fun x _ ↦ hsum x]
    _ ≤ ∑ i ∈ t, |C i| * (|(h₀ i).choose| + |(h₁ i).choose| + 1) * (Du + Ku) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hpiece)
    _ = _ := by rw [Finset.sum_mul]

omit [CompleteSpace D] in
/-- **A local estimate for a piece of the partition.** If `ψ` vanishes off `S` and off `(-T, T)`,
and the paths vanishing off `S` satisfy `‖w‖ ≤ C (‖(ι ∘ w)' + A w‖ + e ‖ι ∘ w‖)`, then
`‖ψ u‖ ≤ C' (‖(ι ∘ ψ u)' + A (ψ u)‖ + ‖ι ∘ u‖_{L²((-T, T), H)})` for some `C'`. -/
private theorem exists_forall_norm_smulLeftCLM_le (AL : Lp (D →L[ℝ] H) ∞ μ₀)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖ψ x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ ψ x‖ ≤ C) {S : Set ℝ} {C e T : ℝ} (he : 0 ≤ e)
    (hS : ∀ s ∉ S, ψ s = 0) (hT : ∀ s ∉ Ioo (-T) T, ψ s = 0)
    (hest : ∀ w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, s ∉ S → prev _ w s = 0) →
        ‖w‖ ≤ C * (‖familyDomainTrajectoryOperator ι AL w‖ + e * ‖ι.compLpL 2 μ₀ (prev _ w)‖)) :
    ∃ C' : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      ‖smulLeftCLM ψ hψ.contDiffOn h₀ h₁ ι.compLpL_multiplicationOperator u‖ ≤
        C' * (‖familyDomainTrajectoryOperator ι AL
            (smulLeftCLM ψ hψ.contDiffOn h₀ h₁ ι.compLpL_multiplicationOperator u)‖ +
          ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖) := by
  set c := h₀.choose
  have hc' (s : ℝ) : |ψ s| ≤ |c| :=
    (Real.norm_eq_abs _ ▸ h₀.choose_spec s trivial).trans (le_abs_self c)
  refine ⟨|C| * (1 + e * |c|), fun u ↦ ?_⟩
  set w := smulLeftCLM ψ hψ.contDiffOn h₀ h₁ ι.compLpL_multiplicationOperator u
  set K := restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u
  have hK : e * ‖ι.compLpL 2 μ₀ (prev _ w)‖ ≤ e * (|c| * ‖K‖) :=
    mul_le_mul_of_nonneg_left (norm_compLpL_prev_smulLeftCLM_le hψ h₀ h₁ hc' hT u) he
  have hw : ∀ᵐ s ∂volume, s ∉ S → prev _ w s = 0 := by
    simpa using ae_prev_smulLeftCLM_eq_zero hψ.contDiffOn h₀ h₁ ι.compLpL_multiplicationOperator
      (Z := Sᶜ) hS u
  refine (hest w hw).trans ?_
  refine (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
  nlinarith [norm_nonneg K, mul_nonneg (mul_nonneg he (abs_nonneg c))
    (norm_nonneg (familyDomainTrajectoryOperator ι AL w))]

variable {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} {Abot Atop : D →L[ℝ] H}

/-- **The semi-Fredholm estimate for `∂ₛ + A(s)` over a common domain.** Let `A : ℝ → (D →L[ℝ] H)`
be continuous, with `L∞` class `AL`, each `A(s)` `ι`-symmetric and invertible after subtracting a
multiple of `ι`, and with invertible limits `Abot` at `-∞` and `Atop` at `+∞`. Then there are `C`
and `T` with
`‖u‖ ≤ C (‖(ι ∘ u)' + A u‖ + ‖ι ∘ u‖_{L²((-T, T), H)})`
for every `u ∈ L²(ℝ, D) ∩ W^{1,2}(ℝ, H)`. -/
theorem exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_of_continuous
    (hAL : AL =ᵐ[μ₀] A) (hA : Continuous A) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hres : ∀ s, ∃ c : ℝ, (A s - c • ι).IsInvertible) (hAbot : Tendsto A atBot (𝓝 Abot))
    (hAtop : Tendsto A atTop (𝓝 Atop)) (hAbot' : Abot.IsInvertible) (hAtop' : Atop.IsInvertible) :
    ∃ C T : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      ‖u‖ ≤ C * (‖familyDomainTrajectoryOperator ι AL u‖ +
        ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖) := by
  -- The estimates near the two ends and near each time.
  obtain ⟨Ct, Tt, hCt⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop
      (ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto hAtop
        (.of_forall hSymm)) hAtop' hAL hAtop
  obtain ⟨Cb, Tb, hCb⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atBot
      (ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto hAbot
        (.of_forall hSymm)) hAbot' hAL hAbot
  have hloc (s₀ : ℝ) : ∃ C e : ℝ, 0 ≤ e ∧ ∃ S ∈ 𝓝 s₀,
      ∀ w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, s ∉ S → prev _ w s = 0) →
        ‖w‖ ≤ C * (‖familyDomainTrajectoryOperator ι AL w‖ + e * ‖ι.compLpL 2 μ₀ (prev _ w)‖) := by
    obtain ⟨c, hc⟩ := hres s₀
    obtain ⟨C, S, hS, hC⟩ :=
      exists_mem_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_of_tendsto
        (hSymm s₀) hc hAL (hA.tendsto s₀)
    exact ⟨C, |c|, abs_nonneg c, S, hS, hC⟩
  choose Cl el hel S hS hCl using hloc
  -- A partition of unity: finitely many pieces near `[-T₀, T₀]`, and the two ends.
  set T₀ := max |Tt| |Tb| + 1
  obtain ⟨t, ψ, hψ, hb, hd, hsum, hT, hψb, hψt, hψS⟩ :=
    exists_contDiff_finset_sum_eq_one_of_mem_nhds S hS (T₀ := T₀)
      (by linarith [le_max_left |Tt| |Tb|, abs_nonneg Tt])
  have h₀ (i : Bool ⊕ ℝ) : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖ψ i x‖ ≤ C :=
    (hb i).imp fun _ hC x _ ↦ hC x
  have h₁ (i : Bool ⊕ ℝ) : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ (ψ i) x‖ ≤ C :=
    (hd i).imp fun _ hC x _ ↦ norm_deriv_eq_norm_fderiv (f := ψ i) (x := x) ▸ hC x
  -- An estimate `‖w‖ ≤ C ‖Dw‖` gives the splicing form.
  have hend {w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)} {C K : ℝ} (hK : 0 ≤ K)
      (h : ‖w‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL w‖) :
      ‖w‖ ≤ |C| * (‖familyDomainTrajectoryOperator ι AL w‖ + K) :=
    h.trans (mul_le_mul (le_abs_self _) (le_add_of_nonneg_right hK) (norm_nonneg _)
      (abs_nonneg _))
  obtain ⟨C, hC⟩ := exists_forall_norm_le_of_sum_eq_one AL t ψ hψ h₀ h₁ hsum (fun i _ ↦ hT i) <| by
    rintro ((_ | _) | i) -
    · refine ⟨|Cb|, fun u ↦ hend (norm_nonneg _) (hCb _ ?_)⟩
      simpa using ae_prev_smulLeftCLM_eq_zero (hψ (.inl false)).contDiffOn (h₀ _) (h₁ _)
        ι.compLpL_multiplicationOperator (Z := Ioi Tb)
        (fun s hs ↦ hψb s (by linarith [neg_abs_le Tb, le_max_right |Tt| |Tb|, mem_Ioi.1 hs])) u
    · refine ⟨|Ct|, fun u ↦ hend (norm_nonneg _) (hCt _ ?_)⟩
      simpa using ae_prev_smulLeftCLM_eq_zero (hψ (.inl true)).contDiffOn (h₀ _) (h₁ _)
        ι.compLpL_multiplicationOperator (Z := Iio Tt)
        (fun s hs ↦ hψt s (by linarith [le_abs_self Tt, le_max_left |Tt| |Tb|, mem_Iio.1 hs])) u
    · exact exists_forall_norm_smulLeftCLM_le AL (hψ (.inr i)) (h₀ _) (h₁ _) (hel i)
        (fun s hs ↦ hψS i s fun h ↦ hs h.1) (fun s hs ↦ hψS i s fun h ↦ hs h.2) (hCl i)
  exact ⟨C, T₀ + 1, hC⟩

/-- **Finite-dimensional kernel.** For a compact embedding `ι : D → H` and a continuous family `A`
of `ι`-symmetric operators, each invertible after subtracting a multiple of `ι`, with invertible
limits at `±∞`, the kernel of `u ↦ (ι ∘ u)' + A u` on `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` is
finite-dimensional. -/
theorem finiteDimensional_ker_familyDomainTrajectoryOperator_of_continuous
    (hι : IsCompactOperator ι) (hAL : AL =ᵐ[μ₀] A) (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hres : ∀ s, ∃ c : ℝ, (A s - c • ι).IsInvertible) (hAbot : Tendsto A atBot (𝓝 Abot))
    (hAtop : Tendsto A atTop (𝓝 Atop)) (hAbot' : Abot.IsInvertible) (hAtop' : Atop.IsInvertible) :
    FiniteDimensional ℝ (familyDomainTrajectoryOperator (p := 2) ι AL).ker := by
  obtain ⟨C, T, hC⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_of_continuous hAL hA
      hSymm hres hAbot hAtop hAbot' hAtop'
  obtain ⟨K, hK, hb⟩ := exists_isCompactOperator_and_norm_le_of_forall_norm_le hι hC
  exact ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate _ hK hb

/-- **Closed range.** For a compact embedding `ι : D → H` and a continuous family `A` of
`ι`-symmetric operators, each invertible after subtracting a multiple of `ι`, with invertible
limits at `±∞`, the operator `u ↦ (ι ∘ u)' + A u` on `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` has closed
range. -/
theorem isClosed_range_familyDomainTrajectoryOperator_of_continuous
    (hι : IsCompactOperator ι) (hAL : AL =ᵐ[μ₀] A) (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hres : ∀ s, ∃ c : ℝ, (A s - c • ι).IsInvertible) (hAbot : Tendsto A atBot (𝓝 Abot))
    (hAtop : Tendsto A atTop (𝓝 Atop)) (hAbot' : Abot.IsInvertible) (hAtop' : Atop.IsInvertible) :
    IsClosed ((familyDomainTrajectoryOperator (p := 2) ι AL).range : Set (Lp H 2 μ₀)) := by
  obtain ⟨C, T, hC⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_of_continuous hAL hA
      hSymm hres hAbot hAtop hAbot' hAtop'
  obtain ⟨K, hK, hb⟩ := exists_isCompactOperator_and_norm_le_of_forall_norm_le hι hC
  exact ContinuousLinearMap.isClosed_range_of_compact_estimate _ hK hb

end Line

end TauCeti.WeakDerivStep
