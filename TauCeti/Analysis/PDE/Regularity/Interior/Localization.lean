/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.Sobolev.Wkp.Extension

/-!
# Higher-order localization of a weak elliptic equation

A smooth compactly supported cutoff preserves the Sobolev order of the forcing if the
solution has one more derivative. When the cutoff solution has zero trace, extending it
by zero to a larger open domain preserves this forcing order as well.

These results refine the `L²`-forcing localization theorem
`exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem`
in `Regularity/Interior/Basic.lean` to `H^k` forcing.
-/

public section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped BigOperators ContDiff ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι]
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

section HigherOrderExtension
local notation "E" => EuclideanSpace ℝ ι

/-- Let `u ∈ H^{k+1}(Ω)` solve `-div(a ∇u) = F` in `Ω` with `F ∈ H^k(Ω)`,
where `a` has smooth entries and its associated bilinear form is bounded and Lipschitz,
and let `Ω ⊆ H`. If `ψ` is a smooth compactly supported cutoff with
`tsupport ψ ∩ H ⊆ Ω` and `ψ u ∈ H¹₀(Ω)`, then the zero extension of `ψ u` belongs to
`H¹₀(H)`, solves a Dirichlet problem on `H` with forcing in `H^k(H)`, and agrees with
`ψ u` on `Ω`. -/
theorem exists_isWeakSolutionDirichlet_value_ae_eq_indicator {H : Opens E} {M : ℝ} {L : ℝ≥0}
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hL : LipschitzWith L (fun x ↦ matrixBilinearForm (a x)))
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j)) (hΩH : Omega ≤ H)
    (k : ℕ) (F : Wkp mu Omega 2 k) (U : Wkp mu Omega 2 (k + 1))
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (Wkp.firstOrder k U) (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value k F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ∩ H ⊆ (Omega : Set E)) {N : ℝ} (hN : 0 ≤ N)
    (hψN : ∀ x ∈ Omega, |ψ x| ≤ N) (hgradN : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ N)
    (hmem : W1p.contDiffSMul ψ hψ hN hψN hgradN (Wkp.firstOrder k U) ∈
      w1p0Submodule mu Omega 2) :
    ∃ w : W1p0 mu H 2, ∃ G : Wkp mu H 2 k, IsWeakSolutionDirichlet a 0 0 (Wkp.value k G) w ∧
      W1p.value (w : W1p mu H 2) =ᵐ[mu.restrict H]
        (Omega : Set E).indicator (fun x ↦ ψ x * W1p.value (Wkp.firstOrder k U) x) := by
  obtain ⟨w, g, hw, hg, hwv, -⟩ :=
    exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem
      hM hL hΩH hu hψ hψc hts hN hψN hgradN hmem
  obtain ⟨q, hq⟩ := exists_value_ae_eq_localizedForcing k ha hψ hψc F U
  have hq₀ : ∀ᵐ x ∂mu.restrict Omega, x ∉ tsupport ψ → Wkp.value k q x = 0 := by
    filter_upwards [hq] with x hx h
    rw [hx, localizedForcing_def, image_eq_zero_of_notMem_tsupport h, gradient_of_notMem_tsupport h,
      divMatrixGradient_eq_zero_of_notMem_tsupport h]
    simp
  obtain ⟨G, hG⟩ := Wkp.exists_value_ae_eq_indicator_of_isClosed (V := H)
    (isClosed_tsupport ψ) (fun x hx ↦ hts ⟨hx.2, hx.1⟩) k q hq₀
  have hval : Wkp.value k G = g := by
    refine Lp.ext ?_
    filter_upwards [hG, hg, ae_restrict_of_ae ((ae_restrict_iff' Omega.isOpen.measurableSet).1 hq)]
      with x h₁ h₂ h₃
    rw [h₁, h₂]
    by_cases hx : x ∈ (Omega : Set E)
    · rw [indicator_of_mem hx, indicator_of_mem hx, h₃ hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  exact ⟨w, G, hval ▸ hw, hwv⟩

end HigherOrderExtension

end TauCeti.PDE
