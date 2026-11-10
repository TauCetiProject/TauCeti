/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Inhomogeneous.Basic
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Hölder continuity of weak solutions with a right-hand side in divergence form

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants
`0 < λ ≤ Λ`. This file proves De Giorgi's local boundedness, interior oscillation estimate and
Hölder continuity for weak solutions `u ∈ H¹(Ω)` of

`-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` in `Ω`, that is `a(u, v) = ∫_Ω f v - ∫_Ω F · ∇v` for every
`v ∈ H¹₀(Ω)`,

with a scalar `f ∈ Lʳ`, `r > 1`, `r > n/2`, and a vector field `F ∈ L^q`, `q > 2`, `q > n`. The
data enter the estimates through the Morrey gains `2 - n/r` of `f` and `1 - n/q` of `F`: on a ball
of radius `R` the right-hand side contributes

`(R^(2 - n/r) ‖f‖_{Lʳ} + R^(1 - n/q) ‖F‖_{L^q}) / λ`,

the same scaling as `R^(-n/2) ‖u‖_{L²}`. No regularity of the coefficients beyond measurability
is assumed. The condition `q > 2` matters only for `n = 1`, where it is the hypothesis of
Stampacchia's bound `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence`. The case
`F = 0` is `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp`, which needs no
exponent `q`.

The right-hand side is split off one ball at a time. On `B = B(x₀, ρ) ⊆ Ω`, the Dirichlet
problems `-∂ᵢ(aⁱʲ ∂ⱼw₁) = f` and `-∂ᵢ(aⁱʲ ∂ⱼw₂) = ∂ᵢFⁱ` in `B`, `w₁, w₂ ∈ H¹₀(B)`, have solutions
(`TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp` and
`TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_neg_setIntegral_inner`), and
Stampacchia's bounds `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow` and
`TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence` give
`|w₁| ≤ C ρ^(2 - n/r) ‖f‖_{Lʳ(B)} / λ` and `|w₂| ≤ C ρ^(1 - n/q) ‖F‖_{L^q(B)} / λ`. The
difference `h = u - w₁ - w₂` solves the homogeneous equation on `B`, and the comparison estimates
of `TauCeti/Analysis/PDE/Regularity/Inhomogeneous/Basic.lean` transfer De Giorgi's theorem from
`h` to `u`.

## Main declarations

All in the namespace `TauCeti.PDE`.

* `exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_divergence`: on a ball, a weak solution with
  right-hand side `f + ∂ᵢFⁱ` is a weak solution of the homogeneous equation up to an error
  bounded by `K (ρ^(2 - n/r) ‖f‖_{Lʳ} + ρ^(1 - n/q) ‖F‖_{L^q}) / λ`.
* `exists_ae_abs_value_le_mul_add_of_memLp_divergence`: local boundedness.
* `exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_memLp_divergence`: the interior oscillation
  estimate.
* `exists_holderOnWith_preciseRepresentative_of_memLp_divergence`: **De Giorgi's theorem with a
  right-hand side in divergence form**, the Hölder continuity of the precise representative.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.15, 8.17, 8.22 and 8.24.
* G. Stampacchia, *Le problème de Dirichlet pour les équations elliptiques du second ordre à
  coefficients discontinus*, Ann. Inst. Fourier 15 (1965).
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

namespace PDE

/-! ### Splitting off the right-hand side on a ball -/

/-- The weak solution `w ∈ H¹₀(B)` of `-∂ᵢ(aⁱʲ ∂ⱼw) = ∂ᵢFⁱ` on a ball `B = B(x₀, ρ)`, with
Stampacchia's bound `|w| ≤ K ρ^(1 - n/q) ‖F‖_{L^q(B)} / λ`. -/
private theorem exists_forall_energyFormH1_eq_neg_setIntegral_inner_ae_abs_le [Nonempty ι]
    {q : ℝ≥0} (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (ball x₀ ρ) a lam Lam →
      AEStronglyMeasurable a (mu.restrict (ball x₀ ρ)) →
      MemLp F q (mu.restrict (ball x₀ ρ)) → 0 < ρ →
      ∃ w : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2)
              (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) =
            -∫ x in ball x₀ ρ, ⟪F x, W1p.gradient (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x⟫ ∂mu) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ),
          |W1p.value (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x| ≤
            K * ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
              (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal / lam := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨C, hC, hstamp⟩ := exists_ae_abs_value_le_mul_div_mul_rpow_divergence (mu := mu) hq hqn
  refine ⟨C * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^
      ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹),
    mul_pos hC (Real.rpow_pos_of_pos (measureReal_ball_pos _ _ one_pos) _), ?_⟩
  intro a lam Lam F x₀ ρ h ha hF hρ
  have hBfin : mu (ball x₀ ρ) ≠ ∞ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (mu.restrict (ball x₀ ρ)) := isFiniteMeasure_restrict.2 hBfin
  have hq2 : (2 : ℝ≥0∞) ≤ q := by
    have : (2 : ℝ≥0) ≤ q := by exact_mod_cast hq.le
    exact_mod_cast this
  obtain ⟨w, hw, -⟩ :=
    h.existsUnique_forall_energyFormH1_eq_neg_setIntegral_inner
      (Omega := ⟨ball x₀ ρ, isOpen_ball⟩) (c := 0) (gamma := 0) ha aestronglyMeasurable_const
      (fun _ _ => by simp) (fun _ _ => le_rfl) hBfin (hF.mono_exponent hq2)
  refine ⟨w, hw, ?_⟩
  have hbound := hstamp (Omega := ⟨ball x₀ ρ, isOpen_ball⟩) (c := 0) (gamma := 0) hBfin h ha
    aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hF hw
  -- `mu(B)^(1/n - 1/q) = ρ^(1 - n/q) mu(B(0, 1))^(1/n - 1/q)`.
  have hmeas : mu.real (ball x₀ ρ) ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) =
      ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
        mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) := by
    rw [Measure.addHaar_real_ball_of_pos _ _ hρ, finrank_euclideanSpace,
      Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_natCast,
      ← Real.rpow_mul hρ.le]
    congr 2
    field_simp
  filter_upwards [hbound] with x hx
  refine hx.trans_eq ?_
  simp only [Opens.coe_mk, hmeas]
  ring

/-- **Splitting off a right-hand side `f + ∂ᵢFⁱ` on a ball.** Let `n ≥ 1` be the dimension, let
`r > 1` with `r > n/2`, and let `q > 2` with `q > n`. There is `K > 0`, depending only on `n`,
`r`, `q` and the normalization of `mu`, such that the following holds. Let `a` be measurable and
uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`, that is `a(u, v) = ∫_Ω f v - ∫_Ω F · ∇v` for every `v ∈ H¹₀(Ω)`, with
`f ∈ Lʳ(B(x₀, ρ))`, `F ∈ L^q(B(x₀, ρ))` and `B(x₀, ρ) ⊆ Ω`. Then on `B = B(x₀, ρ)` there is a weak
solution `h ∈ H¹(B)` of the homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼh) = 0` with

`|u - h| ≤ K (ρ^(2 - n/r) ‖f‖_{Lʳ(B)} + ρ^(1 - n/q) ‖F‖_{L^q(B)}) / λ` almost everywhere on `B`.
-/
theorem exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_divergence [Nonempty ι] {r q : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ ρ)) → MemLp F q (mu.restrict (ball x₀ ρ)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ h : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 h (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value h x| ≤
          K * (ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
              (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal +
            ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
              (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal) / lam := by
  obtain ⟨K₁, hK₁, hsplit⟩ := exists_forall_energyFormH1_eq_zero_ae_abs_sub_le (mu := mu) hr hrn
  obtain ⟨K₂, hK₂, hdiv⟩ :=
    exists_forall_energyFormH1_eq_neg_setIntegral_inner_ae_abs_le (mu := mu) hq hqn
  refine ⟨max K₁ K₂, lt_max_of_lt_left hK₁, ?_⟩
  intro Omega a lam Lam f F u x₀ ρ h ha hf hF hu hρ hball
  have hB : (⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ≤ Omega := hball
  have hBell : UniformlyEllipticOn (ball x₀ ρ) a lam Lam := h.mono_set hball
  have hBmeas : AEStronglyMeasurable a (mu.restrict (ball x₀ ρ)) :=
    ha.mono_measure (Measure.restrict_mono hball le_rfl)
  -- The part `w` of `u` on `B` due to `∂ᵢFⁱ`.
  obtain ⟨w, hw, hwb⟩ := hdiv hBell hBmeas hF hρ
  -- `u|_B - w` solves `-∂ᵢ(aⁱʲ ∂ⱼ·) = f` on `B`.
  have hcoeff := memLp_energyIntegrand_of_bounds (Omega := ⟨ball x₀ ρ, isOpen_ball⟩) (b := 0)
    (c := 0) (beta := 0) (gamma := 0) hBell.upper_nonneg hBmeas aestronglyMeasurable_const
    aestronglyMeasurable_const (fun _x hx eta xi => hBell.upper_bound hx eta xi)
    (fun _ _ => by simp) (fun _ _ => by simp)
  have hu' : ∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
      energyFormH1 a 0 0 (W1p.restrictL hB u - (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2))
          (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) =
        ∫ x in ball x₀ ρ, f x * W1p.value (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x ∂mu :=
    fun v => by
      have hres := energyFormH1_restrictL a 0 0 hB u v
      rw [hu, setIntegral_mul_value_extendByZeroL, setIntegral_inner_gradient_extendByZeroL]
        at hres
      simp only [Opens.coe_mk] at hres
      linarith [energyFormH1_sub_left hcoeff (W1p.restrictL hB u)
        (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2), hw v]
  -- The homogeneous part `h` of `u|_B - w`.
  obtain ⟨g, hg, hug⟩ := hsplit hBell hBmeas hf hu' hρ subset_rfl
  refine ⟨g, hg, ?_⟩
  have hlam := h.pos
  filter_upwards [hug, hwb, W1p.value_sub_ae (W1p.restrictL hB u)
      (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2), W1p.value_restrictL_ae hB u]
    with x hx hwx hxs hxr
  rw [hxs, Pi.sub_apply, hxr] at hx
  have hf0 : 0 ≤ ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
      (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam := by positivity
  have hF0 : 0 ≤ ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
      (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal / lam := by positivity
  calc |W1p.value u x - W1p.value g x|
      ≤ |W1p.value u x - W1p.value (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x - W1p.value g x| +
          |W1p.value (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x| := by
        have e : W1p.value u x - W1p.value g x = W1p.value u x -
            W1p.value (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x - W1p.value g x +
              W1p.value (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x := by ring
        rw [e]
        exact abs_add_le _ _
    _ ≤ K₁ * ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam +
          K₂ * ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
            (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal / lam := add_le_add hx hwx
    _ = K₁ * (ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam) +
          K₂ * (ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
            (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal / lam) := by ring
    _ ≤ max K₁ K₂ * (ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam) +
          max K₁ K₂ * (ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
            (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal / lam) := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = _ := by ring

/-- The splitting `TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_divergence` on
every ball `B(x₀, ρ)` with `ρ ≤ R` inside a set `S` carrying `f` and `F`, bounded through the
norms of `f` and `F` on `S` and the power `ρ^γ` of the smaller Morrey gain
`γ = min (2 - n/r) (1 - n/q)`. This is the comparison hypothesis of the estimates of
`TauCeti/Analysis/PDE/Regularity/Inhomogeneous/Basic.lean`. -/
private theorem exists_forall_exists_ae_abs_sub_le_of_memLp_divergence [Nonempty ι]
    {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ} {S : Set (EuclideanSpace ℝ ι)},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict S) → MemLp F q (mu.restrict S) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      ball x₀ R ⊆ S → S ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ ρ, 0 < ρ → ρ ≤ R → ∃ g : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 g (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value g x| ≤
          K * (R ^ (2 - (Fintype.card ι : ℝ) / r -
                min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)) *
              (eLpNorm f r (mu.restrict S)).toReal +
            R ^ (1 - (Fintype.card ι : ℝ) / q -
                min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)) *
              (eLpNorm F q (mu.restrict S)).toReal) / lam *
          ρ ^ min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q) := by
  obtain ⟨K, hK, hsplit⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_divergence (mu := mu) hr hrn hq hqn
  refine ⟨K, hK, fun {Omega a lam Lam f F u x₀ R S} h ha hf hF hu hball hS ρ hρ hρR => ?_⟩
  have hρS : ball x₀ ρ ⊆ S := (ball_subset_ball hρR).trans hball
  obtain ⟨g, hg, hug⟩ := hsplit h ha (hf.mono_measure (Measure.restrict_mono hρS le_rfl))
    (hF.mono_measure (Measure.restrict_mono hρS le_rfl)) hu hρ (hρS.trans hS)
  refine ⟨g, hg, ?_⟩
  have hfρ : (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal ≤
      (eLpNorm f r (mu.restrict S)).toReal :=
    lpNorm_mono_measure hf (Measure.restrict_mono hρS le_rfl)
  have hFρ : (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal ≤
      (eLpNorm F q (mu.restrict S)).toReal :=
    lpNorm_mono_measure hF (Measure.restrict_mono hρS le_rfl)
  -- `ρ^δ ≤ R^(δ - γ) ρ^γ` for both gains `δ ≥ γ`.
  set γ := min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)
  have hpow : ∀ δ, γ ≤ δ → ρ ^ δ ≤ R ^ (δ - γ) * ρ ^ γ := fun δ hδ =>
    calc ρ ^ δ = ρ ^ (δ - γ) * ρ ^ γ := by rw [← Real.rpow_add hρ, sub_add_cancel]
      _ ≤ R ^ (δ - γ) * ρ ^ γ := by gcongr
  have h₁ := hpow _ (min_le_left _ _)
  have h₂ := hpow _ (min_le_right _ _)
  have := h.pos
  have hR : 0 < R := hρ.trans_le hρR
  filter_upwards [hug] with x hx
  refine hx.trans ?_
  calc _ ≤ K * (R ^ (2 - (Fintype.card ι : ℝ) / r - γ) * ρ ^ γ *
          (eLpNorm f r (mu.restrict S)).toReal + R ^ (1 - (Fintype.card ι : ℝ) / q - γ) *
            ρ ^ γ * (eLpNorm F q (mu.restrict S)).toReal) / lam := by gcongr
    _ = _ := by ring

omit [DecidableEq ι] in
/-- `E R^γ` for the comparison bound of
`TauCeti.PDE.exists_forall_exists_ae_abs_sub_le_of_memLp_divergence`: the factors `R^(δ - γ)`
recombine with `R^γ` into the Morrey gains. -/
private theorem mul_rpow_min_eq {r q : ℝ≥0} {K R lam A₁ A₂ : ℝ} (hR : 0 < R) :
    K * (R ^ (2 - (Fintype.card ι : ℝ) / r -
          min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)) * A₁ +
        R ^ (1 - (Fintype.card ι : ℝ) / q -
          min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)) * A₂) / lam *
      R ^ min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q) =
    K * ((R ^ (2 - (Fintype.card ι : ℝ) / r) * A₁ +
      R ^ (1 - (Fintype.card ι : ℝ) / q) * A₂) / lam) := by
  set γ := min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)
  have hpow : ∀ δ, R ^ (δ - γ) * R ^ γ = R ^ δ := fun δ => by
    rw [← Real.rpow_add hR, sub_add_cancel]
  calc _ = K * (R ^ (2 - (Fintype.card ι : ℝ) / r - γ) * R ^ γ * A₁ +
        R ^ (1 - (Fintype.card ι : ℝ) / q - γ) * R ^ γ * A₂) / lam := by ring
    _ = _ := by rw [hpow, hpow]; ring

omit [DecidableEq ι] in
/-- The positivity of the smaller Morrey gain `min (2 - n/r) (1 - n/q)`. -/
private theorem min_sub_div_pos {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r)
    (hqn : (Fintype.card ι : ℝ) < q) :
    0 < min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q) := by
  have hq0 : (0 : ℝ) < q := (Nat.cast_nonneg _).trans_lt hqn
  refine lt_min ?_ ?_
  · rw [sub_pos, div_lt_iff₀ (by exact_mod_cast zero_lt_one.trans hr)]
    linarith only [hrn]
  · rw [sub_pos, div_lt_one hq0]
    exact hqn

/-! ### Local boundedness -/

/-- **Local boundedness of weak solutions with a right-hand side in divergence form.** Let
`n ≥ 1` be the dimension, let `r > 1` with `r > n/2`, and let `q > 2` with `q > n`. There is
`D > 0`, depending only on `λ`, `Λ`, `n`, `r`, `q` and the normalization of `mu`, such that the
following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and
let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` with `f ∈ Lʳ(B(x₀, R))` and
`F ∈ L^q(B(x₀, R))`. If `B(x₀, R) ⊆ Ω`, then almost everywhere on `B(x₀, R/2)`

`|u| ≤ D (R^(-n/2) ‖u‖_{L²(B(x₀, R))} +`
`(R^(2 - n/r) ‖f‖_{Lʳ(B(x₀, R))} + R^(1 - n/q) ‖F‖_{L^q(B(x₀, R))}) / λ)`. -/
theorem exists_ae_abs_value_le_mul_add_of_memLp_divergence [Nonempty ι] {lam Lam : ℝ}
    {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ R)) → MemLp F q (mu.restrict (ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤
        D * (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict (ball x₀ R))).toReal +
            R ^ (1 - (Fintype.card ι : ℝ) / q) *
              (eLpNorm F q (mu.restrict (ball x₀ R))).toReal) / lam) := by
  obtain ⟨K, hK, hsplit⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_divergence (mu := mu) hr hrn hq hqn
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le (mu := mu) (lam := lam) (Lam := Lam)
  refine ⟨D * max 1 K, by positivity, ?_⟩
  intro Omega a f F u x₀ R h ha hf hF hu hR hball
  obtain ⟨g, hg, hug⟩ := hsplit h ha hf hF hu hR hball
  filter_upwards [hbound h ha hR hball hg hug] with x hx
  refine hx.trans ?_
  set Q := R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)
  set P := (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict (ball x₀ R))).toReal +
    R ^ (1 - (Fintype.card ι : ℝ) / q) * (eLpNorm F q (mu.restrict (ball x₀ R))).toReal) / lam
  have hQ : 0 ≤ Q := by positivity
  have hP : 0 ≤ P := by have := h.pos; positivity
  rw [mul_div_assoc, mul_assoc]
  gcongr
  nlinarith [mul_nonneg (sub_nonneg.2 (le_max_left 1 K)) hQ,
    mul_nonneg (sub_nonneg.2 (le_max_right 1 K)) hP]

/-! ### Oscillation decay -/

/-- **De Giorgi's interior oscillation estimate with a right-hand side in divergence form.** Let
`n ≥ 1` be the dimension, let `r > 1` with `r > n/2`, and let `q > 2` with `q > n`. There are
`α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `n`, `r`, `q` and the normalization of
`mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` with
`f ∈ Lʳ(B(x₀, R))` and `F ∈ L^q(B(x₀, R))`. If `B(x₀, R) ⊆ Ω` and `0 < s ≤ R/2`, then almost
everywhere on `B(x₀, s)` the function `u` takes values in an interval of length

`C (s / R)^α (R^(-n/2) ‖u‖_{L²(B(x₀, R))} +`
`(R^(2 - n/r) ‖f‖_{Lʳ(B(x₀, R))} + R^(1 - n/q) ‖F‖_{L^q(B(x₀, R))}) / λ)`. -/
theorem exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_memLp_divergence [Nonempty ι]
    {lam Lam : ℝ} {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r)
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R s : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ R)) → MemLp F q (mu.restrict (ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < s → s ≤ R / 2 → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ m' : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ s), W1p.value u x ∈ Icc m' (m' + C * (s / R) ^ α *
        (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict (ball x₀ R))).toReal +
            R ^ (1 - (Fintype.card ι : ℝ) / q) *
              (eLpNorm F q (mu.restrict (ball x₀ R))).toReal) / lam)) := by
  obtain ⟨K, hK, hcmp⟩ :=
    exists_forall_exists_ae_abs_sub_le_of_memLp_divergence (mu := mu) hr hrn hq hqn
  obtain ⟨α, C, hα, hα1, hC, hosc⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le (mu := mu) (lam := lam)
      (Lam := Lam) (min_sub_div_pos hr hrn hqn)
  refine ⟨α, C * max 1 K, hα, hα1, by positivity, ?_⟩
  intro Omega a f F u x₀ R s h ha hf hF hu hs hsR hball
  have hR : 0 < R := by linarith only [hs, hsR]
  obtain ⟨m', hm'⟩ := hosc h ha (hcmp h ha hf hF hu subset_rfl hball) hs hsR hball
  refine ⟨m', ?_⟩
  set Q := R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)
  set P := (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict (ball x₀ R))).toReal +
    R ^ (1 - (Fintype.card ι : ℝ) / q) * (eLpNorm F q (mu.restrict (ball x₀ R))).toReal) / lam
  have hQ : 0 ≤ Q := by positivity
  have hP : 0 ≤ P := by have := h.pos; positivity
  have hlen : C * (s / R) ^ α * (Q + K * P) ≤ C * max 1 K * (s / R) ^ α * (Q + P) :=
    calc C * (s / R) ^ α * (Q + K * P) ≤ C * (s / R) ^ α * (max 1 K * (Q + P)) := by
          gcongr
          nlinarith [mul_nonneg (sub_nonneg.2 (le_max_left 1 K)) hQ,
            mul_nonneg (sub_nonneg.2 (le_max_right 1 K)) hP]
      _ = _ := by ring
  filter_upwards [hm'] with x hx
  rw [mul_rpow_min_eq hR] at hx
  exact ⟨hx.1, hx.2.trans (by linarith only [hlen])⟩

/-! ### Hölder continuity -/

/-- **De Giorgi's theorem with a right-hand side in divergence form.** Let `n ≥ 1` be the
dimension, let `r > 1` with `r > n/2`, and let `q > 2` with `q > n`. There are `α ∈ (0, 1]` and
`C > 0`, depending only on `λ`, `Λ`, `n`, `r`, `q` and the normalization of the additive Haar
measure `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω`
with constants `λ, Λ`, let `f ∈ Lʳ(Ω)` and `F ∈ L^q(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` be a weak
solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`, that is `a(u, v) = ∫_Ω f v - ∫_Ω F · ∇v` for every
`v ∈ H¹₀(Ω)`. If the closed `R`-thickening of a set `K` lies in `Ω`, then the precise
representative of `u` is Hölder continuous on `K` with exponent `α` and constant

`C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + (R^(2 - n/r) ‖f‖_{Lʳ(Ω)} + R^(1 - n/q) ‖F‖_{L^q(Ω)}) / λ)`.

The precise representative agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`). No regularity of the coefficients beyond
measurability is assumed. -/
theorem exists_holderOnWith_preciseRepresentative_of_memLp_divergence [Nonempty ι]
    {lam Lam : ℝ} {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r)
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict Omega) → MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict Omega)).toReal +
              R ^ (1 - (Fintype.card ι : ℝ) / q) *
                (eLpNorm F q (mu.restrict Omega)).toReal) / lam)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨Ks, hKs, hcmp⟩ :=
    exists_forall_exists_ae_abs_sub_le_of_memLp_divergence (mu := mu) hr hrn hq hqn
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le (mu := mu) (lam := lam)
      (Lam := Lam) (min_sub_div_pos hr hrn hqn)
  refine ⟨α, C * max 1 Ks, hα, hα1, by positivity, ?_⟩
  intro Omega a f F u K R h ha hf hF hu hR hRK
  refine (hhol h ha hR hRK fun x hx => hcmp h ha hf hF hu
    ((ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK))
    subset_rfl).mono_const (Real.toNNReal_le_toNNReal ?_)
  set Q := R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu)
  set P := (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict Omega)).toReal +
    R ^ (1 - (Fintype.card ι : ℝ) / q) * (eLpNorm F q (mu.restrict Omega)).toReal) / lam
  have hQ : 0 ≤ Q := by positivity
  have hP : 0 ≤ P := by have := h.pos; positivity
  rw [mul_rpow_min_eq hR]
  calc C * R ^ (-(α : ℝ)) * (Q + Ks * P) ≤ C * R ^ (-(α : ℝ)) * (max 1 Ks * (Q + P)) := by
        gcongr
        nlinarith [mul_nonneg (sub_nonneg.2 (le_max_left 1 Ks)) hQ,
          mul_nonneg (sub_nonneg.2 (le_max_right 1 Ks)) hP]
    _ = _ := by ring

end PDE

end TauCeti
