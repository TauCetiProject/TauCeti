/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Oscillation
public import TauCeti.MeasureTheory.Function.PreciseRepresentative

/-!
# Hölder continuity of weak solutions (De Giorgi)

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 3`, with constants
`0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ⱼ(aⁱʲ ∂ᵢu) = 0`. This file proves
De Giorgi's theorem: `u` has a representative which is locally Hölder continuous in `Ω`, with an
exponent `α ∈ (0, 1]` depending only on `λ`, `Λ`, the dimension and the normalization of the
Haar measure. No regularity of the coefficients beyond measurability is assumed.

The representative is the precise representative `TauCeti.MeasureTheory.preciseRepresentative`
of `u`, the limit of its averages over shrinking balls. It agrees with `u` almost everywhere on
`Ω` by the Lebesgue differentiation theorem
(`TauCeti.MeasureTheory.ae_restrict_eq_preciseRepresentative`, applied to
`TauCeti.HasWeakFDerivOn.locallyIntegrableOn`). The Hölder estimate on a compact `K ⊆ Ω` combines
two a-priori estimates on the balls `B(x, R)`, `x ∈ K`, contained in `Ω`: De Giorgi's interior
oscillation estimate, which bounds the oscillation of `u` on `B(x, r)` by `C r^α`, and local
boundedness, which bounds `|u|` on `B(x, R/2)`. Both constants are controlled by the `L²` norm of
`u` on `Ω`, and `TauCeti.MeasureTheory.holderOnWith_preciseRepresentative` turns them into a
Hölder bound for the precise representative.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative`: **De Giorgi's theorem**; the precise
  representative of a weak solution is Hölder continuous on every compact subset of `Ω`, with a
  uniform exponent.
* `TauCeti.PDE.continuousOn_preciseRepresentative`: the precise representative of a weak solution
  is continuous on `Ω`.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino (1957).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.22 and Theorem 8.24.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

/-- **De Giorgi's theorem: Hölder continuity of weak solutions.** Let `2*` be the Sobolev
exponent of `W^{1,2}` in dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces
`n ≥ 3`). There is `α ∈ (0, 1]`, depending only on `λ`, `Λ`, the dimension and the normalization
of the additive Haar measure `mu`, such that the following holds. Let `a` be measurable and
uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ⱼ(aⁱʲ ∂ᵢu) = 0`. Then the precise representative of `u` is Hölder continuous with exponent `α`
on every compact `K ⊆ Ω`.

The precise representative agrees with `u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_restrict_eq_preciseRepresentative`). No regularity of the coefficients
beyond measurability is assumed. -/
theorem exists_holderOnWith_preciseRepresentative {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ α : ℝ≥0, 0 < α ∧ α ≤ 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      ∀ {K : Set (EuclideanSpace ℝ ι)}, IsCompact K → K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∃ C : ℝ≥0, HolderOnWith C α (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨α, C₀, hα, hα1, hC₀, hosc⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := lam)
      (Lam := Lam) hpstar hexp
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := lam) (Lam := Lam)
      hpstar hexp
  lift α to ℝ≥0 using hα.le
  refine ⟨α, NNReal.coe_pos.1 hα, NNReal.coe_le_one.1 hα1, ?_⟩
  intro Omega a u h ha hu K hK hKΩ
  -- Every ball of radius `R` centred in `K` lies in `Ω`.
  obtain ⟨R, hR, hRK⟩ := hK.exists_cthickening_subset_open Omega.isOpen hKΩ
  have hball : ∀ x ∈ K, ball x R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := fun x hx =>
    (ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK)
  -- The scaled `L²` norm of `u` on such a ball is at most `N`, its scaled `L²` norm on `Ω`.
  set N := R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu)
  have hN : ∀ x ∈ K, R ^ (-(Fintype.card ι : ℝ) / 2) *
      √(∫ y in ball x R, W1p.value u y ^ 2 ∂mu) ≤ N := fun x hx =>
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (setIntegral_mono_set (s := ball x R)
      (Lp.memLp (W1p.value u)).integrable_sq (ae_of_all _ fun y => sq_nonneg _)
      (hball x hx).eventuallyLE)) (by positivity)
  have hf : ∀ x ∈ K, IntegrableAtFilter (W1p.value u) (𝓝 x) mu := fun x hx => by
    simpa [nhdsWithin_eq_nhds.2 (Omega.isOpen.mem_nhds (hKΩ hx))] using
      (W1p.hasWeakFDerivOn u).locallyIntegrableOn x (hKΩ hx)
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, (C : ℝ) = C₀ * N / R ^ (α : ℝ) / 2 := ⟨⟨_, by positivity⟩, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ≥0, (M : ℝ) = D * N := ⟨⟨_, by positivity⟩, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ) = R / 2 := ⟨⟨_, by positivity⟩, rfl⟩
  refine ⟨_, holderOnWith_preciseRepresentative (C := C) (M := M) (ρ := ρ)
    (NNReal.coe_pos.1 hα) (NNReal.coe_pos.1 (hρ ▸ half_pos hR)) hf
    (fun x hx r hr hrR => ?_) (fun x hx => ?_)⟩
  · -- Oscillation: `u` lies in an interval of length `L ≤ 2 C r^α` on `B(x, r)`.
    rw [hρ] at hrR
    obtain ⟨m', hm'⟩ := hosc h ha hu hr hrR (hball x hx)
    have hL : C₀ * (r / R) ^ (α : ℝ) * (R ^ (-(Fintype.card ι : ℝ) / 2) *
        √(∫ y in ball x R, W1p.value u y ^ 2 ∂mu)) ≤ 2 * (C * r ^ (α : ℝ)) :=
      calc _ ≤ C₀ * (r / R) ^ (α : ℝ) * N := by gcongr; exact hN x hx
        _ = 2 * (C * r ^ (α : ℝ)) := by rw [hC, Real.div_rpow hr.le hR.le]; field_simp
    refine ⟨m' + C * r ^ (α : ℝ), ?_⟩
    filter_upwards [hm'] with y hy
    rw [mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hy.1, hy.2]
  · -- Boundedness: `|u| ≤ D N` on `B(x, R/2)`, by local boundedness.
    rw [hρ]
    filter_upwards [hbound h ha hu hR (hball x hx)] with y hy
    rw [Real.norm_eq_abs, hM]
    refine hy.trans ?_
    rw [mul_assoc]
    gcongr
    exact hN x hx

/-- **Continuity of weak solutions.** Let `2*` be the Sobolev exponent of `W^{1,2}` in dimension
`n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces `n ≥ 3`). Let `a` be measurable and
uniformly elliptic on `Ω`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ⱼ(aⁱʲ ∂ᵢu) = 0`. Then the
precise representative of `u`, which agrees with `u` almost everywhere on `Ω`, is continuous on
`Ω`. -/
theorem continuousOn_preciseRepresentative {pstar : ℝ≥0∞} (hpstar : pstar ≠ (∞ : ℝ≥0∞))
    (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) :
    ContinuousOn (preciseRepresentative mu (W1p.value u)) Omega := by
  obtain ⟨α, hα, -, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative (mu := mu) (lam := lam) (Lam := Lam) hpstar hexp
  intro x hx
  obtain ⟨ε, hε, hsub⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
  obtain ⟨C, hC⟩ := hhol h ha hu (isCompact_closedBall x ε) hsub
  exact ((hC.continuousOn hα).continuousAt (closedBall_mem_nhds x hε)).continuousWithinAt

end PDE

end TauCeti
