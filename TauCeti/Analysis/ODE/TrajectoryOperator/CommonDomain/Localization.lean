/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Family
public import TauCeti.Analysis.Sobolev.GraphStep.Multiplication
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
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
(`exists_forall_norm_le_familyDomainTrajectoryOperator_add_restrictBaseL_of_continuous`).
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
  them and to the two ends, and estimate each `ψᵢ u`. Multiplication by `ψᵢ`
  (`TauCeti.WeakDerivStep.smulLeftCompLpLCLM`) satisfies the Leibniz rule
  `(ι ∘ (ψ u))' + A (ψ u) = ψ ((ι ∘ u)' + A u) + ψ' (ι ∘ u)`
  (`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator_smulLeftCompLpLCLM_ae`), and the
  commutator term `ψ' (ι ∘ u)` and the local error terms `ι ∘ (ψ u)` live in a fixed bounded window
  `(-T, T)`.

The estimate is the first half of the Fredholm theory of `∂ₛ + A(s)`; the finiteness of the
cokernel and the identification of the index with the spectral flow of `A` are not proved here.

## Main results

* `TauCeti.WeakDerivStep.familyDomainTrajectoryOperator_smulLeftCompLpLCLM_ae`: the Leibniz rule
  for multiplication by a smooth function.
* `exists_forall_norm_le_familyDomainTrajectoryOperator_add_restrictBaseL_of_continuous`: the
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
/-- The paths `ψᵢ u` of a finite smooth partition of unity `∑ᵢ ψᵢ = 1` add up to `u`. -/
private theorem sum_smulLeftCompLpLCLM {κ : Type*} (t : Finset κ) (ψ : κ → ℝ → ℝ)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (h₀ : ∀ i, ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖ψ i x‖ ≤ C)
    (h₁ : ∀ i, ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ (ψ i) x‖ ≤ C) (hsum : ∀ x, ∑ i ∈ t, ψ i x = 1)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ∑ i ∈ t, smulLeftCompLpLCLM ι (ψ i) (hψ i).contDiffOn (h₀ i) (h₁ i) u = u := by
  classical
  -- The field of a partial sum is the partial sum of the `ψᵢ` times the field of `u`.
  have key : ∀ t' : Finset κ, ⇑(prev _ (∑ i ∈ t', smulLeftCompLpLCLM ι (ψ i) (hψ i).contDiffOn
      (h₀ i) (h₁ i) u)) =ᵐ[μ₀] fun s ↦ (∑ i ∈ t', ψ i s) • prev _ u s := by
    intro t'
    induction t' using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, prev_zero, zero_smul]
      exact Lp.coeFn_zero D 2 μ₀
    | insert j t' hj ih =>
      simp only [Finset.sum_insert hj, prev_add]
      filter_upwards [Lp.coeFn_add (prev _ (smulLeftCompLpLCLM ι (ψ j) (hψ j).contDiffOn (h₀ j)
          (h₁ j) u)) (prev _ (∑ i ∈ t', smulLeftCompLpLCLM ι (ψ i) (hψ i).contDiffOn (h₀ i)
          (h₁ i) u)), prev_smulLeftCompLpLCLM_ae ι (hψ j).contDiffOn (h₀ j) (h₁ j) u, ih]
        with s hs hj' ht'
      rw [hs, Pi.add_apply, hj', ht', add_smul]
  refine ext (Lp.ext ?_)
  filter_upwards [key t] with s hs
  rw [hs, hsum, one_smul]

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
        rw [sum_smulLeftCompLpLCLM t ψ hψ h₀ h₁ hsum]
    _ ≤ ∑ i ∈ t, |C i| * (|(h₀ i).choose| + |(h₁ i).choose| + 1) * (Du + Ku) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hpiece)
    _ = _ := by rw [Finset.sum_mul]

/-- **The two end pieces of the partition of unity.** Let `∑ᵢ χᵢ` be a finite sum of nonnegative
smooth functions, supported in `(-T, T)`, at most one everywhere and equal to one on `[-T₀, T₀]`,
where `1 ≤ T₀ < T`. Then `1 - ∑ᵢ χᵢ` splits as `ρbot + ρtop` into smooth functions with values in
`[0, 1]`, locally constant off `(-T, T)`, with `ρbot` vanishing on `[-T₀, ∞)` and `ρtop` on
`(-∞, T₀]`. -/
private theorem exists_end_pieces {κ : Type*} (t : Finset κ) (χ : κ → ℝ → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hχ0 : ∀ i x, 0 ≤ χ i x) (hχle : ∀ x, ∑ i ∈ t, χ i x ≤ 1)
    {T₀ T : ℝ} (hT₀ : 1 ≤ T₀) (hT₀T : T₀ < T) (hχK : ∀ x ∈ Icc (-T₀) T₀, ∑ i ∈ t, χ i x = 1)
    (hχT : ∀ i, tsupport (χ i) ⊆ Ioo (-T) T) :
    ∃ ρbot ρtop : ℝ → ℝ, ContDiff ℝ ∞ ρbot ∧ ContDiff ℝ ∞ ρtop ∧
      (∀ x, ρbot x + ρtop x + ∑ i ∈ t, χ i x = 1) ∧ (∀ x, |ρbot x| ≤ 1) ∧ (∀ x, |ρtop x| ≤ 1) ∧
      (∀ x ∉ Ioo (-T) T, fderiv ℝ ρbot x = 0) ∧ (∀ x ∉ Ioo (-T) T, fderiv ℝ ρtop x = 0) ∧
      (∀ x, -T₀ ≤ x → ρbot x = 0) ∧ (∀ x, x ≤ T₀ → ρtop x = 0) := by
  set θ := Real.smoothTransition
  set χm : ℝ → ℝ := fun x ↦ ∑ i ∈ t, χ i x
  have hχm : ContDiff ℝ ∞ χm := ContDiff.sum fun i _ ↦ hχ i
  have hχm0 (x : ℝ) : 0 ≤ 1 - χm x := sub_nonneg.2 (hχle x)
  have hχm1 (x : ℝ) : 1 - χm x ≤ 1 := sub_le_self _ (Finset.sum_nonneg fun i _ ↦ hχ0 i x)
  -- Off `(-T, T)`, `θ` is locally constant and `∑ᵢ χᵢ` vanishes nearby.
  have hloc (x : ℝ) (hx : x ∉ Ioo (-T) T) :
      ∃ a : ℝ, θ =ᶠ[𝓝 x] (fun _ ↦ a) ∧ χm =ᶠ[𝓝 x] 0 := by
    have hχx : χm =ᶠ[𝓝 x] 0 := (Filter.eventually_all_finset t).2
        (fun i _ ↦ notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (hχT i h)) |>.mono
      fun y hy ↦ Finset.sum_eq_zero hy
    rcases not_and_or.1 hx with hx | hx
    · refine ⟨0, (eventually_lt_nhds (show x < 0 by linarith [not_lt.1 hx])).mono fun y hy ↦
        Real.smoothTransition.zero_of_nonpos hy.le, hχx⟩
    · refine ⟨1, (eventually_gt_nhds (show 1 < x by linarith [not_lt.1 hx])).mono fun y hy ↦
        Real.smoothTransition.one_of_one_le hy.le, hχx⟩
  refine ⟨fun x ↦ (1 - θ x) * (1 - χm x), fun x ↦ θ x * (1 - χm x),
    (contDiff_const.sub Real.smoothTransition.contDiff).mul (contDiff_const.sub hχm),
    Real.smoothTransition.contDiff.mul (contDiff_const.sub hχm), fun x ↦ by ring,
    fun x ↦ ?_, fun x ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [abs_of_nonneg (mul_nonneg (sub_nonneg.2 (Real.smoothTransition.le_one x)) (hχm0 x))]
    nlinarith [Real.smoothTransition.nonneg x, Real.smoothTransition.le_one x, hχm0 x, hχm1 x]
  · rw [abs_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg x) (hχm0 x))]
    nlinarith [Real.smoothTransition.nonneg x, Real.smoothTransition.le_one x, hχm0 x, hχm1 x]
  · obtain ⟨a, hθ, hχx⟩ := hloc x hx
    have h : (fun y ↦ (1 - θ y) * (1 - χm y)) =ᶠ[𝓝 x] fun _ ↦ (1 - a) * 1 := by
      filter_upwards [hθ, hχx] with y h₁ h₂
      simp only [h₁, h₂, Pi.zero_apply, sub_zero]
    rw [h.fderiv_eq]
    exact fderiv_const_apply _
  · obtain ⟨a, hθ, hχx⟩ := hloc x hx
    have h : (fun y ↦ θ y * (1 - χm y)) =ᶠ[𝓝 x] fun _ ↦ a * 1 := by
      filter_upwards [hθ, hχx] with y h₁ h₂
      simp only [h₁, h₂, Pi.zero_apply, sub_zero]
    rw [h.fderiv_eq]
    exact fderiv_const_apply _
  · rcases le_or_gt 1 x with h | h
    · simp [θ, Real.smoothTransition.one_of_one_le h]
    · simp [χm, hχK x ⟨hx, by linarith⟩]
  · rcases le_or_gt x 0 with h | h
    · simp [θ, Real.smoothTransition.zero_of_nonpos h]
    · simp [χm, hχK x ⟨by linarith, hx⟩]

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

omit [CompleteSpace D] [CompleteSpace H] in
/-- The limit of a family of `ι`-symmetric operators is `ι`-symmetric. -/
private theorem inner_apply_eq_of_tendsto {A : ℝ → D →L[ℝ] H} {B : D →L[ℝ] H} {l : Filter ℝ}
    [l.NeBot] (hA : Tendsto A l (𝓝 B)) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (x y : D) : ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ := by
  have hx : Tendsto (fun s ↦ A s x) l (𝓝 (B x)) :=
    ((ContinuousLinearMap.apply ℝ H x).continuous.tendsto B).comp hA
  have hy : Tendsto (fun s ↦ A s y) l (𝓝 (B y)) :=
    ((ContinuousLinearMap.apply ℝ H y).continuous.tendsto B).comp hA
  exact tendsto_nhds_unique (hx.inner tendsto_const_nhds)
    ((tendsto_const_nhds.inner hy).congr fun s ↦ (hSymm s x y).symm)

/-- **A partition of unity adapted to local estimates.** Given a neighbourhood `S s` of every time
`s` and `1 ≤ T₀`, there is a finite smooth partition of unity `∑ᵢ ψᵢ = 1` on `ℝ`, by functions with
bounded values and derivatives, whose derivatives vanish off `(-(T₀ + 1), T₀ + 1)`, made of one
function vanishing on `[-T₀, ∞)`, one vanishing on `(-∞, T₀]`, and functions `ψ (inr s)` vanishing
off `S s ∩ (-(T₀ + 1), T₀ + 1)`. -/
private theorem exists_partition_of_mem_nhds (S : ℝ → Set ℝ) (hS : ∀ s, S s ∈ 𝓝 s) {T₀ : ℝ}
    (hT₀ : 1 ≤ T₀) :
    ∃ (t : Finset (Bool ⊕ ℝ)) (ψ : Bool ⊕ ℝ → ℝ → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
      (h₀ : ∀ i, ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖ψ i x‖ ≤ C)
      (h₁ : ∀ i, ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ (ψ i) x‖ ≤ C),
      (∀ x, ∑ i ∈ t, ψ i x = 1) ∧ (∀ i, ∀ s ∉ Ioo (-(T₀ + 1)) (T₀ + 1), deriv (ψ i) s = 0) ∧
      (∀ s, -T₀ ≤ s → ψ (.inl false) s = 0) ∧ (∀ s, s ≤ T₀ → ψ (.inl true) s = 0) ∧
      ∀ i s, s ∉ S i ∩ Ioo (-(T₀ + 1)) (T₀ + 1) → ψ (.inr i) s = 0 := by
  obtain ⟨t, χ, hχ, hχ0, hχle, hχK⟩ :=
    (isCompact_Icc (a := -T₀) (b := T₀)).exists_contDiff_tsupport_subset_finset_sum_eq_one
      (U := fun s₀ ↦ interior (S s₀) ∩ Ioo (-(T₀ + 1)) (T₀ + 1))
      (fun _ ↦ isOpen_interior.inter isOpen_Ioo) fun x hx ↦ mem_iUnion.2
        ⟨x, mem_interior_iff_mem_nhds.2 (hS x), by linarith [hx.1], by linarith [hx.2]⟩
  have hχT (i : ℝ) : tsupport (χ i) ⊆ Ioo (-(T₀ + 1)) (T₀ + 1) :=
    (hχ i).2.2.trans inter_subset_right
  obtain ⟨ρb, ρt, hρb, hρt, hsum, hρb1, hρt1, hρb', hρt', hρb0, hρt0⟩ :=
    exists_end_pieces t χ (fun i ↦ (hχ i).1) hχ0 hχle hT₀ (by linarith) hχK hχT
  -- The pieces, indexed by `Bool ⊕ ℝ`: the two ends and the pieces near `[-T₀, T₀]`.
  let ψ : Bool ⊕ ℝ → ℝ → ℝ := Sum.elim (fun b ↦ bif b then ρt else ρb) χ
  have hψ : ∀ i, ContDiff ℝ ∞ (ψ i) := by
    rintro ((_ | _) | i)
    exacts [hρb, hρt, (hχ i).1]
  have hfd : ∀ i, ∀ s ∉ Ioo (-(T₀ + 1)) (T₀ + 1), fderiv ℝ (ψ i) s = 0 := by
    rintro ((_ | _) | i) s hs
    exacts [hρb' s hs, hρt' s hs, fderiv_of_notMem_tsupport ℝ fun h ↦ hs (hχT i h)]
  have h₀ : ∀ i, ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖ψ i x‖ ≤ C := by
    rintro ((_ | _) | i)
    · exact ⟨1, fun x _ ↦ (Real.norm_eq_abs _).trans_le (hρb1 x)⟩
    · exact ⟨1, fun x _ ↦ (Real.norm_eq_abs _).trans_le (hρt1 x)⟩
    · obtain ⟨C, hC⟩ := (hχ i).1.continuous.bounded_above_of_compact_support (hχ i).2.1
      exact ⟨C, fun x _ ↦ hC x⟩
  -- The derivatives are continuous and vanish off a compact interval, hence are bounded.
  have h₁ (i : Bool ⊕ ℝ) : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ (ψ i) x‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((hψ i).continuous_fderiv (by simp)).bounded_above_of_compact_support
      (HasCompactSupport.intro (isCompact_Icc (a := -(T₀ + 1)) (b := T₀ + 1)) fun s hs ↦
        hfd i s fun h ↦ hs (Ioo_subset_Icc_self h))
    exact ⟨C, fun x _ ↦ hC x⟩
  refine ⟨Finset.univ.disjSum t, ψ, hψ, h₀, h₁, fun x ↦ ?_,
    fun i s hs ↦ by simp [← fderiv_apply_one_eq_deriv, hfd i s hs], hρb0, hρt0,
    fun i s hs ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hs ⟨interior_subset ((hχ i).2.2 h).1,
      hχT i h⟩⟩
  simp only [Finset.sum_disjSum, Fintype.sum_bool, ψ, Sum.elim_inl, Sum.elim_inr, Bool.cond_true,
    Bool.cond_false]
  linarith [hsum x]

variable {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} {Abot Atop : D →L[ℝ] H}

/-- **The semi-Fredholm estimate for `∂ₛ + A(s)` over a common domain.** Let `A : ℝ → (D →L[ℝ] H)`
be continuous, with `L∞` class `AL`, each `A(s)` `ι`-symmetric and invertible after subtracting a
multiple of `ι`, and with invertible limits `Abot` at `-∞` and `Atop` at `+∞`. Then there are `C`
and `T` with
`‖u‖ ≤ C (‖(ι ∘ u)' + A u‖ + ‖ι ∘ u‖_{L²((-T, T), H)})`
for every `u ∈ L²(ℝ, D) ∩ W^{1,2}(ℝ, H)`. -/
theorem exists_forall_norm_le_familyDomainTrajectoryOperator_add_restrictBaseL_of_continuous
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
  obtain ⟨t, ψ, hψ, h₀, h₁, hsum, hT, hψb, hψt, hψS⟩ :=
    exists_partition_of_mem_nhds S hS (T₀ := T₀)
      (by linarith [le_max_left |Tt| |Tb|, abs_nonneg Tt])
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
    exists_forall_norm_le_familyDomainTrajectoryOperator_add_restrictBaseL_of_continuous hAL hA
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
