/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.GlobalHolder
public import TauCeti.Analysis.Sobolev.LipschitzDomain.MeasureDensity
import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness
import TauCeti.Analysis.PDE.Regularity.Boundary.Divergence
import TauCeti.Analysis.Sobolev.W1p.Lipschitz
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.Topology.MetricSpace.Holder

/-!
# The global Hölder estimate for the Dirichlet problem with boundary values

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants
`0 < λ ≤ Λ`, let `F ∈ L^q(Ω; ℝⁿ)` with `q > 2` and `q > n`, and let `G` be a bounded Lipschitz
function on `Ω`. This file proves that a weak solution `u ∈ H¹(Ω)` of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω`, `u = G` on `∂Ω`,

is Hölder continuous up to the boundary, with one Hölder constant on all of `Ω`, as soon as `Ω`
has finite measure and its complement has uniform positive density at its own points: for some
`θ > 0` and `R > 0`,

`θ |B(z, s)| ≤ |B(z, s) \ Ω|` for every `z ∉ Ω` and `0 < s ≤ R`.

The equation is `a(u, v) = -∫_Ω F · ∇v` for every `v ∈ H¹₀(Ω)`, and the boundary condition is
`u - g ∈ H¹₀(Ω)` for some `g ∈ H¹(Ω)` whose value is `G` almost everywhere. The Hölder constant
is controlled by `‖F‖_{L^q(Ω)} / λ`, the Lipschitz constant of `G` and the bound of `G`, with an
exponent `α ∈ (0, 1]` and a constant depending only on `λ`, `Λ`, `θ`, `q`, the dimension and the
normalization of the Haar measure. No regularity of the coefficients beyond measurability is
used. Every bounded Lipschitz domain has such an exterior density.

* `exists_holderWith_preciseRepresentative_indicator_of_measureReal_ball_diff_divergence`:
  for zero boundary values, the precise representative of the extension of `u` by zero is
  `α`-Hölder on all of `ℝⁿ` with constant `C R^(-α) (|Ω|^(1/n - 1/q) + R^(1 - n/q)) ‖F‖_{L^q} / λ`.
* `TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_inner_of_lipschitzOnWith`,
  `TauCeti.PDE.exists_forall_energyFormH1_sub_eq_neg_setIntegral_inner`: subtracting boundary
  values `g` whose value is `K₁`-Lipschitz on `Ω`, the difference `u - g` solves the equation with
  the datum `F + a ∇g`, of `L^q` norm at most `‖F‖_{L^q} + Λ K₁ |Ω|^(1/q)`.
* `TauCeti.PDE.exists_ae_eq_and_holderOnWith_of_measureReal_ball_diff_divergence`: for boundary
  values `G` with `|G| ≤ K₀` and Lipschitz constant `K₁` on `Ω`, the solution agrees almost
  everywhere on `Ω` with a function that is `α`-Hölder on `Ω` with constant
  `C R^(-α) ((|Ω|^(1/n - 1/q) + R^(1 - n/q)) (‖F‖_{L^q} + Λ K₁ |Ω|^(1/q)) / λ + R K₁ + K₀)`.
* `Set.IsLipschitzDomain.exists_ae_eq_and_holderOnWith_divergence`: on a bounded Lipschitz domain
  the constant becomes `C (‖F‖_{L^q} / λ + K₀ + K₁)`, with `α` and `C` depending on `Ω`, `λ`, `Λ`
  and `q`.

This is the case of a right-hand side in divergence form and Lipschitz boundary values of the
global Hölder estimate of Gilbarg–Trudinger, Theorem 8.29.

## The argument

For zero boundary values three estimates already proved are combined: Stampacchia's maximum
principle with a divergence datum (`TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence`)
bounds `|u|` on `Ω` by `M = C ‖F‖_{L^q} / λ · |Ω|^(1/n - 1/q)`; De Giorgi's boundary estimate
with a divergence datum
(`exists_ae_abs_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence`)
turns the bound `M` and the exterior density into power decay at the points of the complement;
and the covering step
(`TauCeti.PDE.exists_holderWith_preciseRepresentative_indicator_of_memLp_add_divergence`, with no
scalar datum) gives the Hölder estimate on the whole space.

Boundary values are subtracted. Since `a(g, v) = ∫_Ω (a ∇g) · ∇v`, the difference `w = u - g`
lies in `H¹₀(Ω)` and solves `-∂ᵢ(aⁱʲ ∂ⱼw) = ∂ᵢ(Fⁱ + (a ∇g)ⁱ)`. The weak gradient of the
Lipschitz function `G` is its derivative, bounded by `K₁`, so `|a ∇g| ≤ Λ K₁` and the new datum
lies in `L^q(Ω)` with norm at most `‖F‖_{L^q} + Λ K₁ |Ω|^(1/q)`. The precise representative of
the extension of `w` by zero is Hölder on `ℝⁿ`, and `G` is Hölder on `Ω` with constant
`R^(-α) (R K₁ + 2 K₀)`, using its Lipschitz bound at distances below `R` and its bound above.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.15, 8.16, 8.27 and 8.29.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

/-- The bookkeeping of the constant: with the global bound `M = C_b N P / λ` and the decay constant
`N' = C_d (M + Q N / λ)`, the constant `C R^(-α) (M + N' + Q N / λ)` of the covering step is at most
`C (1 + C_d) (1 + C_b) R^(-α) (P + Q) N / λ`. -/
private theorem mul_rpow_mul_add_add_div_le {C Cb Cd R α P Q N lam : ℝ} (hC : 0 ≤ C)
    (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd) (hR : 0 ≤ R) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hN : 0 ≤ N)
    (hlam : 0 < lam) :
    C * R ^ (-α) * (Cb * N / lam * P + Cd * (Cb * N / lam * P + Q * N / lam) + Q * N / lam) ≤
      C * (1 + Cd) * (1 + Cb) * R ^ (-α) * (P + Q) * N / lam := by
  have hPQ : Cb * P + Q ≤ (1 + Cb) * (P + Q) := by nlinarith
  calc C * R ^ (-α) * (Cb * N / lam * P + Cd * (Cb * N / lam * P + Q * N / lam) + Q * N / lam)
      = C * R ^ (-α) * (1 + Cd) * ((Cb * P + Q) * (N / lam)) := by ring
    _ ≤ C * R ^ (-α) * (1 + Cd) * ((1 + Cb) * (P + Q) * (N / lam)) := by gcongr
    _ = C * (1 + Cd) * (1 + Cb) * R ^ (-α) * (P + Q) * N / lam := by ring

/-- **The global Hölder estimate for the Dirichlet problem with a divergence datum, under an
exterior density condition.** Let `n ≥ 1` be the dimension, let `q > 2` with `q > n`, and fix a
proportion `θ > 0`. There are `α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `θ`, `q`, `n`
and the normalization of the additive Haar measure `mu`, such that the following holds. Let `Ω` be
open with finite measure, let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, let `F ∈ L^q(Ω; ℝⁿ)`, and let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ`,
that is `a(u, v) = -∫_Ω F · ∇v` for every `v ∈ H¹₀(Ω)`. Suppose that the complement of `Ω` fills
the proportion `θ` of every ball `B(z, s)` with `z ∉ Ω` and `0 < s ≤ R`. Then the precise
representative of the extension of `u` by zero is Hölder continuous on the whole space with
exponent `α` and constant

`C R^(-α) (|Ω|^(1/n - 1/q) + R^(1 - n/q)) ‖F‖_{L^q(Ω)} / λ`.

No regularity of `∂Ω` beyond the exterior density condition, and no regularity of the
coefficients beyond measurability, is assumed. -/
theorem exists_holderWith_preciseRepresentative_indicator_of_measureReal_ball_diff_divergence
    [Nonempty ι] {lam Lam : ℝ} {q : ℝ≥0} (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ (α : ℝ) ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {R : ℝ},
      mu (Omega : Set (EuclideanSpace ℝ ι)) ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict Omega) →
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ s, 0 < s → s ≤ R →
        θ * mu.real (ball z s) ≤ mu.real (ball z s \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      HolderWith (C * R ^ (-(α : ℝ)) *
          (mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^
              ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) + R ^ (1 - (Fintype.card ι : ℝ) / q)) *
            (eLpNorm F q (mu.restrict Omega)).toReal / lam).toNNReal α
        (preciseRepresentative mu
          ((Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.value u))) := by
  obtain ⟨Cb, hCb, hbd⟩ := exists_ae_abs_value_le_mul_div_mul_rpow_divergence (mu := mu) hq hqn
  obtain ⟨β, Cd, hβ, hCd, hdecay⟩ :=
    exists_ae_abs_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence
      (mu := mu) (lam := lam) (Lam := Lam) hθ hq hqn
  -- There is no scalar datum, so the covering step may use the exponent `q` for it as well.
  have hr : 1 < q := by exact_mod_cast (show (1 : ℝ) < q by linarith)
  have hrn : (Fintype.card ι : ℝ) < 2 * q := by linarith
  obtain ⟨α, C, hα, hαβ, hC, hglob⟩ :=
    exists_holderWith_preciseRepresentative_indicator_of_memLp_add_divergence (mu := mu)
      (lam := lam) (Lam := Lam) hr hrn hq hqn (lt_min hβ one_pos)
  refine ⟨α, C * (1 + Cd) * (1 + Cb), hα, hαβ.trans (min_le_right _ _), by positivity, ?_⟩
  intro Omega a F u R hfin h ha hF hu0 hu hR hext
  have hlam := h.pos
  set N₀ := (eLpNorm F q (mu.restrict Omega)).toReal
  set P := mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹)
  set Q := R ^ (1 - (Fintype.card ι : ℝ) / q)
  set M := Cb * N₀ / lam * P
  set N := Cd * (M + Q * N₀ / lam) with hN
  have hM0 : 0 ≤ M := by positivity
  have hN0 : 0 ≤ N := by positivity
  -- Stampacchia's global bound `|u| ≤ M`.
  have hbound : ∀ᵐ x ∂mu.restrict Omega, |W1p.value u x| ≤ M :=
    hbd (u := ⟨u, hu0⟩) (c := 0) (gamma := 0) hfin h ha aestronglyMeasurable_zero (by simp)
      (by simp) hF hu
  -- De Giorgi's decay at `z ∉ Ω`: `|u| ≤ N (ρ / R)^min(β, 1)` on `Ω ∩ B(z, ρ)`.
  have hbdry : ∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ ρ, 0 < ρ → ρ ≤ R →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball z ρ),
        |W1p.value u x| ≤ (N.toNNReal : ℝ) * (ρ / R) ^ min β 1 := by
    intro z hz ρ hρ hρR
    have hle : mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball z R) ≤
        mu.restrict Omega := Measure.restrict_mono inter_subset_left le_rfl
    have hloc : (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
        ball z R))).toReal ≤ N₀ :=
      ENNReal.toReal_mono hF.eLpNorm_ne_top (eLpNorm_mono_measure F hle)
    have hpow : (ρ / R) ^ β ≤ (ρ / R) ^ min β 1 :=
      Real.rpow_le_rpow_of_exponent_ge (by positivity) ((div_le_one hR).2 hρR) (min_le_left _ _)
    filter_upwards [hdecay h ha (hF.mono_measure hle) hu0 hu hR
      (ae_restrict_of_ae_restrict_of_subset inter_subset_left hbound) (hext z hz) hρ hρR]
      with x hx
    rw [Real.coe_toNNReal _ hN0, hN, mul_right_comm]
    exact hx.trans (by gcongr)
  have hglob' := hglob (f := 0) (M := M.toNNReal) (N := N.toNNReal) h ha MemLp.zero hF
    (fun v => by simp [hu v]) hR
    (by filter_upwards [hbound] with x hx; rwa [Real.coe_toNNReal _ hM0]) hbdry
  refine hglob'.mono (Real.toNNReal_le_toNNReal ?_)
  simp only [eLpNorm_zero, ENNReal.toReal_zero, mul_zero, zero_add, Real.coe_toNNReal _ hM0,
    Real.coe_toNNReal _ hN0]
  exact mul_rpow_mul_add_add_div_le hC.le hCb.le hCd.le hR.le (by positivity) (by positivity)
    ENNReal.toReal_nonneg hlam

/-- The energy form against boundary values `g` whose value is `K₁`-Lipschitz on `Ω`: there is a
field `D`, namely `a ∇g`, with `|D| ≤ Λ K₁` on `Ω` and `a(g, v) = ∫_Ω D · ∇v` for every
`v ∈ H¹₀(Ω)`. On a set of finite measure `D` lies in every `Lᵖ(Ω)`, with
`‖D‖_{Lᵖ(Ω)} ≤ Λ K₁ |Ω|^(1/p)`. -/
theorem exists_forall_energyFormH1_eq_setIntegral_inner_of_lipschitzOnWith
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hfin : mu (Omega : Set (EuclideanSpace ℝ ι)) ≠ ∞) {g : W1p mu Omega 2}
    {G : EuclideanSpace ℝ ι → ℝ} {K₁ : ℝ≥0} (hgG : W1p.value g =ᵐ[mu.restrict Omega] G)
    (hG : LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ ι))) (p : ℝ≥0) :
    ∃ D : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι, MemLp D p (mu.restrict Omega) ∧
      MemLp D 2 (mu.restrict Omega) ∧
      (eLpNorm D p (mu.restrict Omega)).toReal ≤
        Lam * K₁ * mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^ (p : ℝ)⁻¹ ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 g (v : W1p mu Omega 2) =
        ∫ x in Omega, ⟪D x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu := by
  have hΩ : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have : IsFiniteMeasure (mu.restrict Omega) := isFiniteMeasure_restrict.2 hfin
  have hLam := h.upper_nonneg
  set D : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    fun x => toEuclideanCLM (n := ι) (𝕜 := ℝ) (a x) (W1p.gradient g x)
  have hDbd : ∀ᵐ x ∂mu.restrict Omega, ‖D x‖ ≤ Lam * K₁ := by
    filter_upwards [W1p.ae_norm_gradient_le_of_lipschitzOnWith g hgG hG, ae_restrict_mem hΩ]
      with x hx hxΩ
    exact (norm_toEuclideanCLM_apply_le _ _).trans
      (mul_le_mul (h.opNorm_matrixBilinearForm_le hxΩ) hx (norm_nonneg _) hLam)
  have hDm : AEStronglyMeasurable D (mu.restrict Omega) :=
    (continuous_uncurry_toEuclideanCLM (n := ι) (𝕜 := ℝ)).comp_aestronglyMeasurable
      (f := fun x => (a x, (W1p.gradient g x : EuclideanSpace ℝ ι)))
      (ha.prodMk (Lp.aestronglyMeasurable _))
  refine ⟨D, MemLp.of_bound hDm _ hDbd, MemLp.of_bound hDm _ hDbd, ?_, fun v => ?_⟩
  · refine (ENNReal.toReal_mono ?_ (eLpNorm_le_of_ae_bound hDm hDbd)).trans_eq ?_
    · exact ENNReal.mul_ne_top (by simp [ENNReal.rpow_eq_top_iff, hfin]) ENNReal.ofReal_ne_top
    · simp [ENNReal.toReal_rpow, measureReal_def, hLam, mul_comm]
  · rw [energyFormH1_zero_zero_eq_setIntegral]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [matrixBilinearForm_apply, D]
    rw [real_inner_comm, inner_toEuclideanCLM]

/-- **Subtracting boundary values.** If `u ∈ H¹(Ω)` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` with
`F ∈ L^q(Ω; ℝⁿ)`, `q ≥ 2`, and the value of `g ∈ H¹(Ω)` is `K₁`-Lipschitz on `Ω`, then `u - g`
solves `-∂ᵢ(aⁱʲ ∂ⱼ(u - g)) = ∂ᵢF'ⁱ` with `F' = F + a ∇g ∈ L^q(Ω; ℝⁿ)` and
`‖F'‖_{L^q(Ω)} ≤ ‖F‖_{L^q(Ω)} + Λ K₁ |Ω|^(1/q)`. -/
theorem exists_forall_energyFormH1_sub_eq_neg_setIntegral_inner
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hfin : mu (Omega : Set (EuclideanSpace ℝ ι)) ≠ ∞)
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {q : ℝ≥0} (hq : 2 ≤ (q : ℝ))
    (hF : MemLp F q (mu.restrict Omega)) {u g : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu)
    {G : EuclideanSpace ℝ ι → ℝ} {K₁ : ℝ≥0} (hgG : W1p.value g =ᵐ[mu.restrict Omega] G)
    (hG : LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ ι))) :
    ∃ F' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι, MemLp F' q (mu.restrict Omega) ∧
      (eLpNorm F' q (mu.restrict Omega)).toReal ≤ (eLpNorm F q (mu.restrict Omega)).toReal +
        Lam * K₁ * mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^ (q : ℝ)⁻¹ ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u - g) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F' x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu := by
  obtain ⟨D, hD, hD2, hDn, hgD⟩ :=
    exists_forall_energyFormH1_eq_setIntegral_inner_of_lipschitzOnWith h ha hfin hgG hG q
  have hF2 : MemLp F 2 (mu.restrict Omega) := by
    have : IsFiniteMeasure (mu.restrict Omega) := isFiniteMeasure_restrict.2 hfin
    exact hF.mono_exponent (by exact_mod_cast hq)
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) h.upper_nonneg ha
      aestronglyMeasurable_const aestronglyMeasurable_const (fun _ hx => h.upper_bound hx)
      (fun _ _ => by simp) (fun _ _ => by simp)
  refine ⟨F + D, hF.add hD, ?_, fun v => ?_⟩
  · exact (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hF.eLpNorm_ne_top, hD.eLpNorm_ne_top⟩)
      (eLpNorm_add_le (by exact_mod_cast (show (1 : ℝ) ≤ q by linarith)))).trans
      ((ENNReal.toReal_add hF.eLpNorm_ne_top hD.eLpNorm_ne_top).trans_le (by gcongr))
  · have hv2 := Lp.memLp (W1p.gradient (v : W1p mu Omega 2))
    simp only [Pi.add_apply, inner_add_left]
    rw [energyFormH1_sub_left (b := 0) (c := 0) hcoeff, hu v, hgD v,
      integral_add (hF2.integrable_inner hv2) (hD2.integrable_inner hv2)]
    ring

/-- The arithmetic of the constant: if `W ≤ C R^(-α) X` with `X ≥ 0`, then
`W + K₁ R^(1 - α) + 2 K₀ R^(-α) ≤ (C + 2) R^(-α) (X + R K₁ + K₀)`. -/
private theorem add_mul_rpow_add_le {C W X R α K₀ K₁ : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hX : 0 ≤ X) (hW : W ≤ C * R ^ (-α) * X) :
    W + (K₁ * R ^ (1 - α) + 2 * K₀ * R ^ (-α)) ≤ (C + 2) * R ^ (-α) * (X + R * K₁ + K₀) := by
  have hRα : R ^ (1 - α) = R * R ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hR, Real.rpow_one]
  have hR0 : 0 ≤ R ^ (-α) := by positivity
  rw [hRα]
  nlinarith [mul_nonneg hR0 (mul_nonneg hR.le hK₁), mul_nonneg hR0 hK₀, mul_nonneg hR0 hX,
    mul_nonneg (mul_nonneg hC hR0) (mul_nonneg hR.le hK₁), mul_nonneg (mul_nonneg hC hR0) hK₀]

omit [DecidableEq ι] in
/-- For `u, g ∈ H¹(Ω)` and a function `G` agreeing with `g` almost everywhere on `Ω`, the value of
`u` agrees almost everywhere on `Ω` with the precise representative of the extension of `u - g` by
zero plus `G`. -/
private theorem value_ae_eq_preciseRepresentative_indicator_sub_add
    {Omega : Opens (EuclideanSpace ℝ ι)} (u g : W1p mu Omega 2) {G : EuclideanSpace ℝ ι → ℝ}
    (hgG : W1p.value g =ᵐ[mu.restrict Omega] G) :
    W1p.value u =ᵐ[mu.restrict Omega] preciseRepresentative mu
      ((Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.value (u - g))) + G := by
  have hΩ : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hli : LocallyIntegrable ((Omega : Set (EuclideanSpace ℝ ι)).indicator
      (W1p.value (u - g))) mu :=
    ((memLp_indicator_iff_restrict hΩ.nullMeasurableSet).2
      (Lp.memLp (W1p.value (u - g)))).locallyIntegrable (by norm_num)
  filter_upwards [ae_restrict_of_ae (ae_eq_preciseRepresentative hli), W1p.value_sub_ae u g,
    hgG, ae_restrict_mem hΩ] with x h₁ h₂ h₃ hx
  rw [indicator_of_mem hx, h₂] at h₁
  simp only [Pi.add_apply, Pi.sub_apply, ← h₁, ← h₃, sub_add_cancel]

/-- **The global Hölder estimate for the Dirichlet problem with Lipschitz boundary values and a
divergence datum, under an exterior density condition.** Let `n ≥ 1` be the dimension, let `q > 2`
with `q > n`, and fix a proportion `θ > 0`. There are `α ∈ (0, 1]` and `C > 0`, depending only on
`λ`, `Λ`, `θ`, `q`, `n` and the normalization of the additive Haar measure `mu`, such that the
following holds. Let `Ω` be open with finite measure, let `a` be measurable and uniformly elliptic
on `Ω` with constants `λ, Λ`, let `F ∈ L^q(Ω; ℝⁿ)`, and let `G` be bounded by `K₀` and
`K₁`-Lipschitz on `Ω`. Let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` with boundary
values `G`: `a(u, v) = -∫_Ω F · ∇v` for every `v ∈ H¹₀(Ω)`, and `u - g ∈ H¹₀(Ω)` for some
`g ∈ H¹(Ω)` whose value is `G` almost everywhere on `Ω`. Suppose that the complement of `Ω` fills
the proportion `θ` of every ball `B(z, s)` with `z ∉ Ω` and `0 < s ≤ R`. Then `u` agrees almost
everywhere on `Ω` with a function that is `α`-Hölder on `Ω` with constant

`C R^(-α) ((|Ω|^(1/n - 1/q) + R^(1 - n/q)) (‖F‖_{L^q(Ω)} + Λ K₁ |Ω|^(1/q)) / λ + R K₁ + K₀)`.

No regularity of `∂Ω` beyond the exterior density condition, and no regularity of the
coefficients beyond measurability, is assumed. -/
theorem exists_ae_eq_and_holderOnWith_of_measureReal_ball_diff_divergence
    [Nonempty ι] {lam Lam : ℝ} {q : ℝ≥0} (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ (α : ℝ) ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u g : W1p mu Omega 2} {G : EuclideanSpace ℝ ι → ℝ} {K₀ K₁ : ℝ≥0} {R : ℝ},
      mu (Omega : Set (EuclideanSpace ℝ ι)) ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict Omega) →
      u - g ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      W1p.value g =ᵐ[mu.restrict Omega] G →
      LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), |G x| ≤ K₀) →
      0 < R →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ s, 0 < s → s ≤ R →
        θ * mu.real (ball z s) ≤ mu.real (ball z s \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∃ v : EuclideanSpace ℝ ι → ℝ, W1p.value u =ᵐ[mu.restrict Omega] v ∧
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          ((mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^
                ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) + R ^ (1 - (Fintype.card ι : ℝ) / q)) *
              ((eLpNorm F q (mu.restrict Omega)).toReal +
                Lam * K₁ * mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^ (q : ℝ)⁻¹) / lam +
            R * K₁ + K₀)).toNNReal α v Omega := by
  obtain ⟨α, C, hα, hα1, hC, hmain⟩ :=
    exists_holderWith_preciseRepresentative_indicator_of_measureReal_ball_diff_divergence
      (mu := mu) (lam := lam) (Lam := Lam) hq hqn hθ
  refine ⟨α, C + 2, hα, hα1, by positivity, ?_⟩
  intro Omega a F u g G K₀ K₁ R hfin h ha hF hug hu hgG hG hG0 hR hext
  have hlam := h.pos
  -- `w = u - g` vanishes on `∂Ω` and solves `-∂ᵢ(aⁱʲ ∂ⱼw) = ∂ᵢF'ⁱ`, with `F' = F + a ∇g`.
  obtain ⟨F', hF', hF'n, hw⟩ :=
    exists_forall_energyFormH1_sub_eq_neg_setIntegral_inner h ha hfin hq.le hF hu hgG hG
  -- `G` is Hölder on `Ω` at the scale `R`, from its Lipschitz bound below `R` and its bound above.
  have hGH : HolderOnWith (K₁ * R.toNNReal ^ (((1 : ℝ≥0) : ℝ) - α) +
      2 * K₀ * R.toNNReal ^ (-(α : ℝ))) α G Omega :=
    HolderOnWith.of_le_of_dist_le (fun x hx y hy _ => by simpa using hG.dist_le_mul x hx y hy)
      (fun x hx y hy => by
        rw [Real.dist_eq]
        push_cast
        linarith [abs_sub (G x) (G y), hG0 x hx, hG0 y hy])
      (by exact_mod_cast hα1) (Real.toNNReal_pos.2 hR)
  -- The Hölder estimate for `w`, added to that of `G`.
  have hsum := ((hmain hfin h ha hF' hug hw hR hext).holderOnWith
    (Omega : Set (EuclideanSpace ℝ ι))).add hGH
  refine ⟨_, value_ae_eq_preciseRepresentative_indicator_sub_add u g hgG,
    HolderOnWith.of_dist_le fun x hx y hy => (hsum.dist_le hx hy).trans
      (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg dist_nonneg _))⟩
  have hP : 0 ≤ mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^
      ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) + R ^ (1 - (Fintype.card ι : ℝ) / q) := by positivity
  push_cast
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hR.le]
  refine (add_mul_rpow_add_le hC.le hR K₀.coe_nonneg K₁.coe_nonneg ?_ ?_).trans
    (Real.le_coe_toNNReal _)
  · exact div_nonneg (mul_nonneg hP (add_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (mul_nonneg h.upper_nonneg K₁.coe_nonneg) (by positivity)))) hlam.le
  rw [mul_div_assoc, mul_div_assoc, mul_assoc]
  gcongr

end PDE

end TauCeti

namespace Set.IsLipschitzDomain

open TauCeti TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The arithmetic of the constant on a fixed domain. -/
private theorem mul_add_mul_add_add_le {P B N K₀ K₁ : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) :
    P * N + P * B * K₁ + K₁ + K₀ ≤ (P * (1 + B) + 1) * (N + K₀ + K₁) := by
  nlinarith [mul_nonneg hP hK₀, mul_nonneg hP hK₁, mul_nonneg (mul_nonneg hP hB) hN,
    mul_nonneg (mul_nonneg hP hB) hK₀, mul_nonneg hP hN]

/-- **The global Hölder estimate for the Dirichlet problem with Lipschitz boundary values and a
divergence datum on a bounded Lipschitz domain.** Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be a bounded Lipschitz
domain and let `q > 2` with `q > n`. There are `α ∈ (0, 1]` and `C > 0`, depending only on `Ω`,
`λ`, `Λ`, `q` and the normalization of the additive Haar measure `mu`, such that the following
holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let
`F ∈ L^q(Ω; ℝⁿ)`, and let `G` be bounded by `K₀` and `K₁`-Lipschitz on `Ω`. Let `u ∈ H¹(Ω)` be a
weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` with boundary values `G`: `a(u, v) = -∫_Ω F · ∇v` for every
`v ∈ H¹₀(Ω)`, and `u - g ∈ H¹₀(Ω)` for some `g ∈ H¹(Ω)` whose value is `G` almost everywhere on
`Ω`. Then `u` agrees almost everywhere on `Ω` with a function that is `α`-Hölder on `Ω` with
constant `C (‖F‖_{L^q(Ω)} / λ + K₀ + K₁)`.

No regularity of the coefficients beyond measurability is assumed. -/
theorem exists_ae_eq_and_holderOnWith_divergence [Nonempty ι]
    {Omega : Opens (EuclideanSpace ℝ ι)}
    (hΩ : (Omega : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι))) {lam Lam : ℝ} {q : ℝ≥0}
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ (α : ℝ) ≤ 1 ∧ 0 < C ∧ ∀ {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u g : W1p mu Omega 2}
      {G : EuclideanSpace ℝ ι → ℝ} {K₀ K₁ : ℝ≥0},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict Omega) →
      u - g ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      W1p.value g =ᵐ[mu.restrict Omega] G →
      LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), |G x| ≤ K₀) →
      ∃ v : EuclideanSpace ℝ ι → ℝ, W1p.value u =ᵐ[mu.restrict Omega] v ∧
        HolderOnWith (C * ((eLpNorm F q (mu.restrict Omega)).toReal / lam + K₀ + K₁)).toNNReal
          α v Omega := by
  have hK : IsCompact (frontier (Omega : Set (EuclideanSpace ℝ ι))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  -- The exterior density at the radii `s ≤ 1`, in the form of the general estimate.
  obtain ⟨c, hc, hext⟩ :=
    hΩ.exists_pos_mul_measureReal_ball_le_measureReal_ball_diff (μ := mu) hK one_pos
  obtain ⟨α, C, hα, hα1, hC, hmain⟩ :=
    exists_ae_eq_and_holderOnWith_of_measureReal_ball_diff_divergence (mu := mu) (lam := lam)
      (Lam := Lam) hq hqn hc
  set P := mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) + 1
  set S := mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^ (q : ℝ)⁻¹
  refine ⟨α, C * (P * (1 + |Lam| * S / |lam|) + 1), hα, hα1, by positivity, ?_⟩
  intro a F u g G K₀ K₁ h ha hF hug hu hgG hG hG0
  obtain ⟨v, hv, hvH⟩ := hmain hb.measure_lt_top.ne h ha hF hug hu hgG hG hG0 one_pos hext
  refine ⟨v, hv, HolderOnWith.of_dist_le fun x hx y hy => (hvH.dist_le hx hy).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg dist_nonneg _))⟩
  have hlam := h.pos
  have hLam := h.upper_nonneg
  have hB : 0 ≤ Lam * S / lam := by positivity
  rw [abs_of_nonneg hLam, abs_of_pos hlam]
  simp only [Real.one_rpow, one_mul, mul_one]
  refine Real.toNNReal_le_toNNReal ?_
  calc C * (P * ((eLpNorm F q (mu.restrict Omega)).toReal + Lam * K₁ * S) / lam + K₁ + K₀)
      = C * (P * ((eLpNorm F q (mu.restrict Omega)).toReal / lam) + P * (Lam * S / lam) * K₁ +
          K₁ + K₀) := by
        field_simp
    _ ≤ C * ((P * (1 + Lam * S / lam) + 1) *
          ((eLpNorm F q (mu.restrict Omega)).toReal / lam + K₀ + K₁)) := by
        gcongr
        exact mul_add_mul_add_add_le (by positivity) hB (by positivity) K₀.coe_nonneg
          K₁.coe_nonneg
    _ = _ := by ring

end Set.IsLipschitzDomain
