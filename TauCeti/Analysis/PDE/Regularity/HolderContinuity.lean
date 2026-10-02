/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Oscillation
public import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative

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
(`TauCeti.W1p.ae_eq_preciseRepresentative`). The Hölder estimate on a set `K` whose closed
`R`-thickening lies in `Ω` combines two a-priori estimates on the balls `B(x, R)`, `x ∈ K`:
De Giorgi's interior oscillation estimate, which bounds the oscillation of `u` on `B(x, r)` by
`C r^α`, and local boundedness, which bounds `|u|` on `B(x, R/2)`. Both constants are controlled
by the `L²` norm of `u` on `Ω`, and `TauCeti.MeasureTheory.holderOnWith_preciseRepresentative`
turns them into a Hölder bound for the precise representative, with constant
`C R^(-α - n/2) ‖u‖_{L²(Ω)}`.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative`: **De Giorgi's theorem**; the precise
  representative of a weak solution is Hölder continuous on every set at positive distance from
  `∂Ω`, with an explicit constant and a uniform exponent.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_isCompact`: the precise representative
  of a weak solution is Hölder continuous on every compact subset of `Ω`, with a uniform exponent.
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
`n ≥ 3`). There are `α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, the dimension and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
solution of `-∂ⱼ(aⁱʲ ∂ᵢu) = 0`. If the closed `R`-thickening of a set `K` lies in `Ω`, then the
precise representative of `u` is Hölder continuous on `K` with exponent `α` and constant
`C R^(-α - n/2) ‖u‖_{L²(Ω)}`.

The precise representative agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`). No regularity of the coefficients
beyond measurability is assumed. -/
theorem exists_holderOnWith_preciseRepresentative {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) * (R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ y in Omega, W1p.value u y ^ 2 ∂mu))).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨α, C₀, hα, hα1, hC₀, hosc⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := lam)
      (Lam := Lam) hpstar hexp
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := lam) (Lam := Lam)
      hpstar hexp
  lift α to ℝ≥0 using hα.le
  refine ⟨α, max C₀ (4 * D), NNReal.coe_pos.1 hα, NNReal.coe_le_one.1 hα1,
    lt_max_of_lt_left hC₀, ?_⟩
  intro Omega a u K R h ha hu hR hRK
  have hKΩ : K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := (self_subset_cthickening K).trans hRK
  -- Every ball of radius `R` centred in `K` lies in `Ω`.
  have hball : ∀ x ∈ K, ball x R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := fun x hx =>
    (ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK)
  -- The scaled `L²` norm of `u` on such a ball is at most `N`, its scaled `L²` norm on `Ω`.
  set N := R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu)
  have hN0 : 0 ≤ N := by positivity
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
  refine (holderOnWith_preciseRepresentative (C := C) (M := M) (ρ := ρ)
    (NNReal.coe_pos.1 hα) (NNReal.coe_pos.1 (hρ ▸ half_pos hR)) hf
    (fun x hx r hr hrR => ?_) (fun x hx => ?_)).mono_const ?_
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
  · -- The constant: `2 C = C₀ N R^(-α)` and `2 M / ρ^α = 2^(1+α) D N R^(-α) ≤ 4 D N R^(-α)`.
    have hRα : 0 < R ^ (α : ℝ) := Real.rpow_pos_of_pos hR _
    have h2α : (2 : ℝ) ^ (α : ℝ) ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le one_le_two hα1
    rw [Real.le_toNNReal_iff_coe_le (by positivity)]
    push_cast
    rw [hC, hM, hρ, Real.div_rpow hR.le zero_le_two, Real.rpow_neg hR.le]
    refine max_le ?_ ?_
    · calc 2 * (C₀ * N / R ^ (α : ℝ) / 2) = C₀ * (R ^ (α : ℝ))⁻¹ * N := by field_simp
        _ ≤ _ := by gcongr; exact le_max_left _ _
    · calc 2 * (D * N) / (R ^ (α : ℝ) / 2 ^ (α : ℝ))
          = 2 * 2 ^ (α : ℝ) * D * (R ^ (α : ℝ))⁻¹ * N := by field_simp
        _ ≤ 2 * 2 * D * (R ^ (α : ℝ))⁻¹ * N := by gcongr
        _ ≤ _ := by
          rw [show (2 : ℝ) * 2 * D = 4 * D by ring]
          gcongr
          exact le_max_right _ _

/-- **De Giorgi's theorem on compact sets.** Let `2*` be the Sobolev exponent of `W^{1,2}` in
dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces `n ≥ 3`). There is
`α ∈ (0, 1]`, depending only on `λ`, `Λ`, the dimension and the normalization of the additive
Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on
`Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ⱼ(aⁱʲ ∂ᵢu) = 0`. Then the
precise representative of `u` is Hölder continuous with exponent `α` on every compact `K ⊆ Ω`. -/
theorem exists_holderOnWith_preciseRepresentative_of_isCompact {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ α : ℝ≥0, 0 < α ∧ α ≤ 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {K : Set (EuclideanSpace ℝ ι)},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      IsCompact K → K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∃ C : ℝ≥0, HolderOnWith C α (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨α, _, hα, hα1, -, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative (mu := mu) (lam := lam) (Lam := Lam) hpstar hexp
  refine ⟨α, hα, hα1, ?_⟩
  intro Omega a u K h ha hu hK hKΩ
  obtain ⟨R, hR, hRK⟩ := hK.exists_cthickening_subset_open Omega.isOpen hKΩ
  exact ⟨_, hhol h ha hu hR hRK⟩

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
  obtain ⟨α, _, hα, -, -, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative (mu := mu) (lam := lam) (Lam := Lam) hpstar hexp
  intro x hx
  obtain ⟨ε, hε, hsub⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
  have hε2 : 0 < ε / 2 := half_pos hε
  have hC := hhol h ha hu hε2 <| by
    rwa [cthickening_closedBall hε2.le hε2.le, add_halves]
  exact ((hC.continuousOn hα).continuousAt (closedBall_mem_nhds x hε2)).continuousWithinAt

end PDE

end TauCeti
