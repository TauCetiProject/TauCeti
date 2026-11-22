/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Family
public import TauCeti.Analysis.Sobolev.GraphStep.Multiplication
import TauCeti.Analysis.Calculus.BumpFunction.LinePartition
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Sobolev.GraphStep.AubinLions

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
(`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL`).
When `ι` is compact, the restriction of `ι ∘ u` to `(-T, T)` is a compact operator on the graph
space (`TauCeti.WeakDerivStep.isCompactOperator_restrictBaseL_compLpL`, an Aubin–Lions lemma), so
Peetre's lemma gives the operator a **finite-dimensional kernel and closed range**
(`finiteDimensional_ker_familyDomainTrajectoryOperator_of_continuous`,
`isClosed_range_familyDomainTrajectoryOperator_of_continuous`).

The hypotheses on `A` are local in `s`: no bound of `A(s) - A₊` through `ι` is assumed, so the
operators `A(s)` may differ from their limits by operators that are unbounded on `H`, as when the
principal part `J ∂ₜ` above varies with `s`. The price is the continuity of `A` in `D →L[ℝ] H`.

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
  each `ψᵢ u`; these add up to `u` (`TauCeti.WeakDerivStep.sum_smulLeftCompLpLCLM`). Multiplication
  by `ψᵢ` (`TauCeti.WeakDerivStep.smulLeftCompLpLCLM`) satisfies the Leibniz rule
  `(ι ∘ (ψ u))' + A (ψ u) = ψ ((ι ∘ u)' + A u) + ψ' (ι ∘ u)`
  (`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator_smulLeftCompLpLCLM_ae`), and the
  commutator term `ψ' (ι ∘ u)` and the local error terms `ι ∘ (ψ u)` live in a fixed bounded window
  `(-T, T)`.

The estimate is the first half of the Fredholm theory of `∂ₛ + A(s)`; the finiteness of the
cokernel and the identification of the index with the spectral flow of `A` are not proved here.

## Main results

* `TauCeti.WeakDerivStep.familyDomainTrajectoryOperator_smulLeftCompLpLCLM_ae`: the Leibniz rule
  for multiplication by a smooth function.
* `exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL`: the
  semi-Fredholm estimate.
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

section Leibniz

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {ψ : ℝ → ℝ}

local notation "μΩ" => (mu.restrict Omega)

/-- **The Leibniz rule for the trajectory operator.** Multiplying a path `u` by a smooth function
`ψ`, with `ψ` and `ψ'` bounded on `Ω`, multiplies `(ι ∘ u)' + A u` by `ψ` and adds the commutator
term `ψ' (ι ∘ u)`. -/
theorem familyDomainTrajectoryOperator_smulLeftCompLpLCLM_ae (ι : D →L[ℝ] H)
    (A : Lp (D →L[ℝ] H) ∞ μΩ) (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) :
    familyDomainTrajectoryOperator ι A (smulLeftCompLpLCLM ι ψ hψ h₀ h₁ u) =ᵐ[μΩ]
      fun s ↦ ψ s • familyDomainTrajectoryOperator ι A u s + deriv ψ s • ι (prev _ u s) := by
  filter_upwards [familyDomainTrajectoryOperator_apply_ae ι A (smulLeftCompLpLCLM ι ψ hψ h₀ h₁ u),
    familyDomainTrajectoryOperator_apply_ae ι A u, weakFDeriv_smulLeftCompLpLCLM_ae ι hψ h₀ h₁ u,
    prev_smulLeftCompLpLCLM_ae ι hψ h₀ h₁ u] with s hψu hu hw hprev
  rw [hψu, hu, hw, hprev, map_smul, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, fderiv_apply_one_eq_deriv, smul_add]
  abel

end Leibniz

section Line

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι : D →L[ℝ] H}

omit [CompleteSpace D] in
/-- If `|φ| ≤ c` and `φ` vanishes off `(-T, T)`, then the path `φ (ι ∘ u)` on `ℝ` has `L²` norm at
most `c` times that of `ι ∘ u` on `(-T, T)`. -/
private theorem norm_le_mul_norm_restrictBaseL {T c : ℝ} {φ : ℝ → ℝ} (hφ : ∀ s, |φ s| ≤ c)
    (hφT : ∀ s ∉ Ioo (-T) T, φ s = 0) (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀))
    {g : Lp H 2 μ₀} (hg : g =ᵐ[μ₀] fun s ↦ φ s • ι (prev _ u s)) :
    ‖g‖ ≤ c * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖ := by
  set f := ι.compLpL 2 μ₀ (prev _ u)
  have hc : 0 ≤ c := (abs_nonneg _).trans (hφ 0)
  have hgf : g =ᵐ[μ₀] fun s ↦ φ s • f s := by
    filter_upwards [hg, ι.coeFn_compLpL (prev _ u)] with s h₁ h₂
    rw [h₁, h₂]
  have hmeas : AEStronglyMeasurable (fun s ↦ φ s • f s) volume := by
    simpa using (Lp.aestronglyMeasurable g).congr hgf
  have hsupp : Function.support (fun s ↦ φ s • f s) ⊆ Ioo (-T) T := fun s hs ↦ by
    by_contra hns
    exact hs (by simp [hφT s hns])
  rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofReal hc, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)) ?_
  have hg' : eLpNorm g 2 μ₀ = eLpNorm (fun s ↦ φ s • f s) 2 (volume.restrict (Ioo (-T) T)) := by
    rw [eLpNorm_congr_ae hgf, eLpNorm_restrict_eq_of_support_subset hmeas hsupp]
    simp
  rw [hg']
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas.restrict ?_ 2
  filter_upwards [restrictBaseL_apply_ae (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u]
    with s hs
  rw [hs, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hφ s) (norm_nonneg _)

omit [CompleteSpace D] in
/-- The commutator estimate: if `|ψ|` and `|ψ'|` are at most `c` and `ψ'` vanishes off `(-T, T)`,
then `‖(ι ∘ (ψ u))' + A (ψ u)‖ ≤ c ‖(ι ∘ u)' + A u‖ + c ‖ι ∘ u‖_{L²((-T, T), H)}`. -/
private theorem norm_familyDomainTrajectoryOperator_smulLeftCompLpLCLM_le
    (AL : Lp (D →L[ℝ] H) ∞ μ₀) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ ψ x‖ ≤ C)
    {c₀ c₁ T : ℝ} (hc₀ : ∀ s, |ψ s| ≤ c₀) (hc₁ : ∀ s, |deriv ψ s| ≤ c₁)
    (hT : ∀ s ∉ Ioo (-T) T, deriv ψ s = 0) (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖familyDomainTrajectoryOperator ι AL (smulLeftCompLpLCLM ι ψ hψ.contDiffOn h₀ h₁ u)‖ ≤
      c₀ * ‖familyDomainTrajectoryOperator ι AL u‖ +
        c₁ * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖ := by
  set f := ι.compLpL 2 μ₀ (prev _ u)
  have hf := ι.coeFn_compLpL (μ := μ₀) (p := 2) (prev _ u)
  -- The commutator term `ψ' (ι ∘ u)` as an element of `L²`.
  have hmem : MemLp (fun s ↦ deriv ψ s • f s) 2 μ₀ :=
    (Lp.memLp f).of_le_mul (c := c₁)
      ((hψ.continuous_deriv (by simp)).aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
      (.of_forall fun s ↦ by rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hc₁ s)
  set g₂ := hmem.toLp _
  set g₁ := familyDomainTrajectoryOperator ι AL (smulLeftCompLpLCLM ι ψ hψ.contDiffOn h₀ h₁ u) - g₂
  have hg₁ : ‖g₁‖ ≤ c₀ * ‖familyDomainTrajectoryOperator ι AL u‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub (familyDomainTrajectoryOperator ι AL
        (smulLeftCompLpLCLM ι ψ hψ.contDiffOn h₀ h₁ u)) g₂, hmem.coeFn_toLp,
      familyDomainTrajectoryOperator_smulLeftCompLpLCLM_ae ι AL hψ.contDiffOn h₀ h₁ u, hf]
      with s hs hs₂ hs₁ hsf
    rw [hs, Pi.sub_apply, hs₂, hs₁, hsf, add_sub_cancel_right, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hc₀ s) (norm_nonneg _)
  have hg₂ :
      ‖g₂‖ ≤ c₁ * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖ :=
    norm_le_mul_norm_restrictBaseL hc₁ hT u (by
      filter_upwards [hmem.coeFn_toLp, hf] with s hs hsf
      rw [hs, hsf])
  calc _ = ‖g₁ + g₂‖ := by rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hg₁ hg₂)

omit [CompleteSpace D] in
/-- If `ψ` vanishes on a set `Z`, so does the path `ψ u`, almost everywhere. -/
private theorem ae_prev_smulLeftCompLpLCLM_eq_zero {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ ψ x‖ ≤ C)
    {Z : Set ℝ} (hZ : ∀ s ∈ Z, ψ s = 0) (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ∀ᵐ s ∂volume, s ∈ Z → prev _ (smulLeftCompLpLCLM ι ψ hψ.contDiffOn h₀ h₁ u) s = 0 := by
  have hae : ae volume = ae μ₀ := by simp
  filter_upwards [(prev_smulLeftCompLpLCLM_ae ι hψ.contDiffOn h₀ h₁ u).filter_mono hae.le]
    with s hs hsZ
  rw [hs, hZ s hsZ, zero_smul]

omit [CompleteSpace D] in
/-- If `|ψ| ≤ c` and `ψ` vanishes off `(-T, T)`, then `‖ι ∘ (ψ u)‖ ≤ c ‖ι ∘ u‖_{L²((-T, T), H)}`. -/
private theorem norm_compLpL_prev_smulLeftCompLpLCLM_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ ψ x‖ ≤ C)
    {c T : ℝ} (hc : ∀ s, |ψ s| ≤ c) (hT : ∀ s ∉ Ioo (-T) T, ψ s = 0)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖ι.compLpL 2 μ₀ (prev _ (smulLeftCompLpLCLM ι ψ hψ.contDiffOn h₀ h₁ u))‖ ≤
      c * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖ :=
  norm_le_mul_norm_restrictBaseL hc hT u (by
    filter_upwards [ι.coeFn_compLpL (prev _ (smulLeftCompLpLCLM ι ψ hψ.contDiffOn h₀ h₁ u)),
      prev_smulLeftCompLpLCLM_ae ι hψ.contDiffOn h₀ h₁ u] with s hs hψs
    rw [hs, hψs, map_smul])

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
      ‖smulLeftCompLpLCLM ι (ψ i) (hψ i).contDiffOn (h₀ i) (h₁ i) u‖ ≤
        C * (‖familyDomainTrajectoryOperator ι AL
          (smulLeftCompLpLCLM ι (ψ i) (hψ i).contDiffOn (h₀ i) (h₁ i) u)‖ +
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
  have hpiece : ∀ i ∈ t, ‖smulLeftCompLpLCLM ι (ψ i) (hψ i).contDiffOn (h₀ i) (h₁ i) u‖ ≤
      |C i| * (|(h₀ i).choose| + |(h₁ i).choose| + 1) * (Du + Ku) := fun i hi ↦ by
    have hD := norm_familyDomainTrajectoryOperator_smulLeftCompLpLCLM_le AL (hψ i) (h₀ i) (h₁ i)
      (hc₀' i) (hc₁' i) (hT i hi) u
    refine (hC i hi u).trans ((mul_le_mul_of_nonneg_right (le_abs_self _)
      (by positivity)).trans ?_)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    nlinarith [abs_nonneg (h₀ i).choose, abs_nonneg (h₁ i).choose,
      (norm_nonneg _ : 0 ≤ Du), (norm_nonneg _ : 0 ≤ Ku)]
  calc ‖u‖ = ‖∑ i ∈ t, smulLeftCompLpLCLM ι (ψ i) (hψ i).contDiffOn (h₀ i) (h₁ i) u‖ := by
        rw [sum_smulLeftCompLpLCLM ι t ψ (fun i ↦ (hψ i).contDiffOn) h₀ h₁ fun x _ ↦ hsum x]
    _ ≤ ∑ i ∈ t, |C i| * (|(h₀ i).choose| + |(h₁ i).choose| + 1) * (Du + Ku) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hpiece)
    _ = _ := by rw [Finset.sum_mul]

omit [CompleteSpace D] in
/-- **A local estimate for a piece of the partition.** If `ψ` vanishes off `S` and off `(-T, T)`,
and the paths vanishing off `S` satisfy `‖w‖ ≤ C (‖(ι ∘ w)' + A w‖ + e ‖ι ∘ w‖)`, then
`‖ψ u‖ ≤ C' (‖(ι ∘ ψ u)' + A (ψ u)‖ + ‖ι ∘ u‖_{L²((-T, T), H)})` for some `C'`. -/
private theorem exists_forall_norm_smulLeftCompLpLCLM_le (AL : Lp (D →L[ℝ] H) ∞ μ₀)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖ψ x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ ψ x‖ ≤ C) {S : Set ℝ} {C e T : ℝ} (he : 0 ≤ e)
    (hS : ∀ s ∉ S, ψ s = 0) (hT : ∀ s ∉ Ioo (-T) T, ψ s = 0)
    (hest : ∀ w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, s ∉ S → prev _ w s = 0) →
        ‖w‖ ≤ C * (‖familyDomainTrajectoryOperator ι AL w‖ + e * ‖ι.compLpL 2 μ₀ (prev _ w)‖)) :
    ∃ C' : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      ‖smulLeftCompLpLCLM ι ψ hψ.contDiffOn h₀ h₁ u‖ ≤
        C' * (‖familyDomainTrajectoryOperator ι AL (smulLeftCompLpLCLM ι ψ hψ.contDiffOn h₀ h₁ u)‖ +
          ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖) := by
  set c := h₀.choose
  have hc' (s : ℝ) : |ψ s| ≤ |c| :=
    (Real.norm_eq_abs _ ▸ h₀.choose_spec s trivial).trans (le_abs_self c)
  refine ⟨|C| * (1 + e * |c|), fun u ↦ ?_⟩
  set w := smulLeftCompLpLCLM ι ψ hψ.contDiffOn h₀ h₁ u
  set K := restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u
  have hK : e * ‖ι.compLpL 2 μ₀ (prev _ w)‖ ≤ e * (|c| * ‖K‖) :=
    mul_le_mul_of_nonneg_left (norm_compLpL_prev_smulLeftCompLpLCLM_le hψ h₀ h₁ hc' hT u) he
  refine (hest w (ae_prev_smulLeftCompLpLCLM_eq_zero hψ h₀ h₁ (Z := Sᶜ) hS u)).trans ?_
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
theorem exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL
    (hAL : AL =ᵐ[μ₀] A) (hA : Continuous A) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hres : ∀ s, ∃ c : ℝ, (A s - c • ι).IsInvertible) (hAbot : Tendsto A atBot (𝓝 Abot))
    (hAtop : Tendsto A atTop (𝓝 Atop)) (hAbot' : Abot.IsInvertible) (hAtop' : Atop.IsInvertible) :
    ∃ C T : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      ‖u‖ ≤ C * (‖familyDomainTrajectoryOperator ι AL u‖ +
        ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖) := by
  -- The estimates near the two ends and near each time.
  obtain ⟨Ct, Tt, hCt⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop
      (inner_apply_eq_of_tendsto hAtop hSymm) hAtop' hAL hAtop
  obtain ⟨Cb, Tb, hCb⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atBot
      (inner_apply_eq_of_tendsto hAbot hSymm) hAbot' hAL hAbot
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
      exact ae_prev_smulLeftCompLpLCLM_eq_zero (hψ (.inl false)) (h₀ _) (h₁ _) (Z := Ioi Tb)
        (fun s hs ↦ hψb s (by linarith [neg_abs_le Tb, le_max_right |Tt| |Tb|, mem_Ioi.1 hs])) u
    · refine ⟨|Ct|, fun u ↦ hend (norm_nonneg _) (hCt _ ?_)⟩
      exact ae_prev_smulLeftCompLpLCLM_eq_zero (hψ (.inl true)) (h₀ _) (h₁ _) (Z := Iio Tt)
        (fun s hs ↦ hψt s (by linarith [le_abs_self Tt, le_max_left |Tt| |Tb|, mem_Iio.1 hs])) u
    · exact exists_forall_norm_smulLeftCompLpLCLM_le AL (hψ (.inr i)) (h₀ _) (h₁ _) (hel i)
        (fun s hs ↦ hψS i s fun h ↦ hs h.1) (fun s hs ↦ hψS i s fun h ↦ hs h.2) (hCl i)
  exact ⟨C, T₀ + 1, hC⟩

/-- Under the hypotheses of the semi-Fredholm estimate, with `ι` compact, the operator satisfies an
estimate `‖u‖ ≤ C ‖(ι ∘ u)' + A u‖ + ‖K u‖` with `K` compact. -/
private theorem exists_isCompactOperator_and_norm_le (hι : IsCompactOperator ι)
    (hAL : AL =ᵐ[μ₀] A) (hA : Continuous A) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hres : ∀ s, ∃ c : ℝ, (A s - c • ι).IsInvertible) (hAbot : Tendsto A atBot (𝓝 Abot))
    (hAtop : Tendsto A atTop (𝓝 Atop)) (hAbot' : Abot.IsInvertible) (hAtop' : Atop.IsInvertible) :
    ∃ (C T : ℝ) (K : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) →L[ℝ]
      Lp H 2 (volume.restrict (Ioo (-T) T))), IsCompactOperator K ∧
        ∀ u, ‖u‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL u‖ + ‖K u‖ := by
  obtain ⟨C, T, hC⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL hAL hA
      hSymm hres hAbot hAtop hAbot' hAtop'
  refine ⟨|C|, T, |C| • restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top,
    ?_, fun u ↦ ?_⟩
  · simpa using (isCompactOperator_restrictBaseL_compLpL (p := 2) hι
      (le_top : (⟨Ioo (-T) T, isOpen_Ioo⟩ : Opens ℝ) ≤ ⊤)).smul |C|
  rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_abs, ← mul_add]
  exact (hC u).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))

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
  obtain ⟨C, T, K, hK, hb⟩ := exists_isCompactOperator_and_norm_le hι hAL hA hSymm hres hAbot hAtop
    hAbot' hAtop'
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
  obtain ⟨C, T, K, hK, hb⟩ := exists_isCompactOperator_and_norm_le hι hAL hA hSymm hres hAbot hAtop
    hAbot' hAtop'
  exact ContinuousLinearMap.isClosed_range_of_compact_estimate _ hK hb

end Line

end TauCeti.WeakDerivStep
