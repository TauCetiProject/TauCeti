/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HarmonicReplacement
public import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder continuity of the gradient for `-Δu = -div G`

Let `u ∈ H¹(Ω)` be a weak solution of `-Δu = -div G` in an open set `Ω ⊆ ℝ^{n+1}`, that is

`∫_Ω ⟨∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ` on `Ω`,

and let `0 < α < 1`. This file proves that `∇u` is as regular as `G` in the interior: if the open
`R`-thickening `S_R` of a set `S` lies in `Ω` and `G` is `α`-Hölder on `S_R` with constant `K`,
then the precise representative of `∇u` is `α`-Hölder on `S` with constant
`C (K + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`, where `C` depends only on `n` and `α`. This is the
interior Schauder estimate for the Laplacian in divergence form,
`[∇u]_{α, S} ≤ C ([G]_{α, S_R} + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`, and its proof is Campanato's.

## The argument

Fix a ball `B_r = ball x₀ r ⊆ Ω`. Since constants have zero divergence, `u` also solves
`-Δu = -div (G - G(x₀))` on `B_r`, now against all of `H¹₀(B_r)`
(`TauCeti.PDE.forall_energyFormH1_restrictL_eq_inner`), and `‖G - G(x₀)‖ ≤ K r^α` there.
Let `w` be the harmonic replacement of `u` on `B_r`
(`TauCeti.PDE.exists_sub_mem_w1p0Submodule_harmonicOnNhd_ae_eq_of_subset_ball`). The energy
estimate bounds `∫_{B_r} ‖∇u - ∇w‖²` by `∫_{B_r} ‖G - G(x₀)‖² ≤ |B_r| K² r^{2α}`, while `∇w` is
harmonic (`TauCeti.PDE.W1p.exists_harmonicOnNhd_ae_eq_gradient`), so its square mean oscillation
decays like `(ρ / r)^{n+3}`
(`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sub_setAverage_sq_le`).
Together (`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sub_setAverage_sq_le_add`), the
square mean oscillation `ψ(ρ) = ∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖²` satisfies

`ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + B K² r^{n+1+2α}` for `0 < ρ ≤ r`.

Since `n + 1 + 2α < n + 3`, the iteration lemma
`TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add` improves this to
`ψ(ρ) ≤ C ρ^{n+1+2α} (R^{-(n+1+2α)} ‖∇u‖² + K²)`. By Jensen's inequality the mean oscillation of
`∇u` on balls of radius `ρ` is then `O(ρ^α)`, and Campanato's theorem
(`TauCeti.MeasureTheory.dist_preciseRepresentative_le_of_setAverage_norm_sub_le`) turns this into
the Hölder estimate. Points farther apart than `R / 2` are compared through the averages of `∇u`
over balls of radius `R`.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`: the interior Hölder estimate
  for `∇u`, with explicit dependence on `K`, `R` and `‖∇u‖_{L²(Ω)}`.

## References

* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 3.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

section Comparison

/-- The constant `2^{3d+8} (d + 1)²` of the Campanato decay estimate for harmonic functions on
`ℝ^d`, `d = n + 1`. -/
private def decayConst (n : ℕ) : ℝ := 2 ^ (3 * (n + 1) + 8) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2

private theorem decayConst_nonneg (n : ℕ) : 0 ≤ decayConst n := by
  unfold decayConst
  positivity

/-- The exponent `n + 1 + 2α` of the comparison estimate splits as `t^{n+1} (t^α)²`. -/
private theorem rpow_add_two_mul_eq {t : ℝ} (ht : 0 < t) (a : ℝ) :
    t ^ ((n : ℝ) + 1 + 2 * a) = t ^ (n + 1) * (t ^ a) ^ 2 := by
  rw [Real.rpow_add ht, ← Real.rpow_natCast, mul_comm (2 : ℝ), Real.rpow_mul ht.le,
    Real.rpow_two, Nat.cast_add, Nat.cast_one]

/-- The volume of a ball of radius `t > 0` in `ℝ^{n+1}` is `t^{n+1}` times that of the unit
ball. -/
private theorem measureReal_ball_eq (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ} (ht : 0 < t) :
    volume.real (ball x t) =
      t ^ (n + 1) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  rw [Measure.addHaar_real_ball_of_pos _ _ ht, finrank_euclideanSpace_fin]

/-- **The energy error of a replacement.** Let `u ∈ H¹(Ω)`, let `B ⊆ Ω` be open and of finite
measure, and let `w ∈ H¹(B)` satisfy the energy estimate `‖∇(u - w)‖_{L²(B)} ≤ ‖G - c‖_{L²(B)}`,
with `∇w = H` almost everywhere on `B`. If `‖G - c‖ ≤ M` on `B`, then
`∫_B ‖∇u - H‖² ≤ |B| M²`. -/
private theorem setIntegral_norm_gradient_sub_sq_le {ι : Type*} [Fintype ι]
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure] {Omega B : Opens (EuclideanSpace ℝ ι)}
    (hB : B ≤ Omega)
    (hBfin : mu B ≠ ⊤) {u : W1p mu Omega 2} {w : W1p mu B 2}
    {G H : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hwH : (W1p.gradient w : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) =ᵐ[mu.restrict B] H)
    {c : EuclideanSpace ℝ ι} (hGc : MemLp (fun x => G x - c) 2 (mu.restrict B))
    (hest : ‖W1p.gradient (W1p.restrictL hB u - w)‖ ≤ ‖hGc.toLp‖) {M : ℝ}
    (hbd : ∀ x ∈ B, ‖G x - c‖ ≤ M) :
    ∫ x in B, ‖W1p.gradient u x - H x‖ ^ 2 ∂mu ≤ mu.real B * M ^ 2 := by
  have hsub : W1p.gradient (W1p.restrictL hB u - w) =
      W1p.gradient (W1p.restrictL hB u) - W1p.gradient w := by
    simp only [← W1p.gradientL_apply, map_sub]
  have h1 : ∫ x in B, ‖W1p.gradient u x - H x‖ ^ 2 ∂mu =
      ‖W1p.gradient (W1p.restrictL hB u - w)‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_restrictL_ae hB u, hwH,
      Lp.coeFn_sub (W1p.gradient (W1p.restrictL hB u)) (W1p.gradient w)] with x h1 h2 h3
    rw [hsub, h3, Pi.sub_apply, h1, h2]
  have h2 : ‖hGc.toLp‖ ^ 2 = ∫ x in B, ‖G x - c‖ ^ 2 ∂mu := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [hGc.coeFn_toLp] with x hx
    rw [hx]
  rw [h1]
  calc ‖W1p.gradient (W1p.restrictL hB u - w)‖ ^ 2 ≤ ‖hGc.toLp‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hest 2
    _ = ∫ x in B, ‖G x - c‖ ^ 2 ∂mu := h2
    _ ≤ ∫ x in B, M ^ 2 ∂mu :=
        setIntegral_mono_on (hGc.integrable_norm_pow two_ne_zero) (integrableOn_const hBfin)
          B.isOpen.measurableSet fun x hx => pow_le_pow_left₀ (norm_nonneg _) (hbd x hx) 2
    _ = mu.real B * M ^ 2 := by rw [setIntegral_const, smul_eq_mul]

/-- **The comparison estimate.** Let `u ∈ H¹(Ω)` solve `-Δu = -div G` weakly on `Ω ⊆ ℝ^{n+1}`,
and let `B_r = ball x₀ r ⊆ Ω` be a ball on which `G` is `α`-Hölder with constant `K`. For
`0 < ρ ≤ r`, the square mean oscillation `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` of the gradient
satisfies `ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + B K² r^{n+1+2α}` with `A`, `B` depending only on `n`. -/
private theorem setIntegral_norm_gradient_sub_setAverage_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K α : ℝ≥0}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ r : ℝ} (hα : 0 < α)
    (hG : HolderOnWith K α G (ball x₀ r))
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hball : ball x₀ r ⊆ Omega) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
      4 * decayConst n * (ρ / r) ^ ((n : ℝ) + 3) *
          (∫ x in ball x₀ r, ‖W1p.gradient u x - ⨍ y in ball x₀ r, W1p.gradient u y‖ ^ 2) +
        (4 * decayConst n + 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) *
          K ^ 2 * r ^ ((n : ℝ) + 1 + 2 * α) := by
  have hr : 0 < r := hρ.trans_le hρr
  set f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ r, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have hx₀ : x₀ ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) := hball (mem_ball_self hr)
  have : IsFiniteMeasure (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- On `B_r`, the field `G - G x₀` is bounded by `K r^α`.
  have hbd : ∀ x ∈ ball x₀ r, ‖G x - G x₀‖ ≤ K * r ^ (α : ℝ) := fun x hx => by
    rw [← dist_eq_norm]
    exact hG.dist_le_mul_rpow_of_mem_ball hx
  have hGc : MemLp (fun x => G x - G x₀) 2
      (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    MemLp.of_bound (((hG.continuousOn hα).aestronglyMeasurable
      measurableSet_ball).sub aestronglyMeasurable_const) (K * r ^ (α : ℝ))
      ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ hbd))
  -- Harmonic replacement on `B_r`, with energy error at most `‖G - G x₀‖_{L²(B_r)}`.
  obtain ⟨w, -, -, ⟨h, hh, hwh⟩, hest⟩ :=
    exists_sub_mem_w1p0Submodule_harmonicOnNhd_ae_eq_of_subset_ball (Omega := B) (z := x₀)
      (R := r) subset_rfl (W1p.restrictL hB u)
  have hest' := hest hGc.toLp (forall_energyFormH1_restrictL_eq_inner hB
    (memLp_top_const (energyIntegrand (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0 0)) hu hGc)
  -- The gradient of the replacement is harmonic.
  obtain ⟨H, hH, hwH⟩ :=
    W1p.exists_harmonicOnNhd_ae_eq_gradient (hh.weaklyHarmonicOn.congr_ae hwh.symm)
  have hHm : MemLp H 2 (volume.restrict (ball x₀ r)) := (Lp.memLp (W1p.gradient w)).ae_eq hwH
  have hfm : MemLp f 2 (volume.restrict (ball x₀ r)) :=
    (Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hball le_rfl)
  -- The energy error `∫_{B_r} ‖∇u - H‖²` is at most `|B_r| (K r^α)²`.
  have hE : ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ≤
      volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * K ^ 2 *
        r ^ ((n : ℝ) + 1 + 2 * α) := by
    refine (setIntegral_norm_gradient_sub_sq_le hB measure_ball_lt_top.ne hwH hGc hest'
      hbd).trans_eq ?_
    simp only [B, Opens.coe_mk]
    rw [measureReal_ball_eq x₀ hr, rpow_add_two_mul_eq hr]
    ring
  have hcomp := hH.setIntegral_ball_norm_sub_setAverage_sq_le_add hfm hHm hρ hρr
  have hq : (ρ / r) ^ (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) + 2) =
      (ρ / r) ^ ((n : ℝ) + 3) := by
    rw [← Real.rpow_natCast, finrank_euclideanSpace_fin]
    congr 1
    push_cast
    ring
  rw [hq, finrank_euclideanSpace_fin] at hcomp
  have hE' := mul_le_mul_of_nonneg_left hE (by positivity [decayConst_nonneg n] :
    (0 : ℝ) ≤ 4 * decayConst n + 2)
  unfold decayConst at hE' ⊢
  linarith

/-- **Campanato decay of the gradient.** For `0 < α < 1` there is `C`, depending only on `n` and
`α`, such that the following holds. Let `u ∈ H¹(Ω)` solve `-Δu = -div G` weakly on
`Ω ⊆ ℝ^{n+1}`. If `ball x R ⊆ Ω`, `G` is `α`-Hölder with constant `K` on `ball x R` and
`0 < ρ ≤ R`, then
`∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ C ρ^{n+1+2α} (R^{-(n+1+2α)} ‖∇u‖²_{L²(Ω)} + K²)`. -/
private theorem exists_setIntegral_norm_gradient_sub_setAverage_sq_le {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
      {x : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ},
      HolderOnWith K α G (ball x R) →
      (∀ φ : 𝓓(Omega, ℝ),
        energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
          ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      ball x R ⊆ Omega → ∀ ρ, 0 < ρ → ρ ≤ R →
        ∫ y in ball x ρ, ‖W1p.gradient u y - ⨍ z in ball x ρ, W1p.gradient u z‖ ^ 2 ≤
          C * ρ ^ ((n : ℝ) + 1 + 2 * α) *
            (R ^ (-((n : ℝ) + 1 + 2 * α)) * ‖W1p.gradient u‖ ^ 2 + K ^ 2) := by
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hω : 0 ≤ ω := measureReal_nonneg
  have hγ : (n : ℝ) + 1 + 2 * α < n + 3 := by
    have : (α : ℝ) < 1 := hα1
    linarith
  obtain ⟨ε₀, C, hε₀, hC, hit⟩ := exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add
    (by positivity [decayConst_nonneg n] : 0 ≤ 4 * decayConst n) hγ hγ
  refine ⟨C * max 1 ((4 * decayConst n + 2) * ω), by positivity, ?_⟩
  intro Omega u G K x R hG hu hball ρ hρ hρR
  have hR : 0 < R := hρ.trans_le hρR
  set f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  set ψ : ℝ → ℝ := fun t => ∫ y in ball x t, ‖f y - ⨍ z in ball x t, f z‖ ^ 2
  have hfint : ∀ t ≤ R, IntegrableOn f (ball x t) ∧
      ∀ c, IntegrableOn (fun y => ‖f y - c‖ ^ 2) (ball x t) := fun t ht =>
    ⟨(Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two
      ((ball_subset_ball ht).trans hball) measure_ball_lt_top.ne,
      (Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset
        ((ball_subset_ball ht).trans hball) measure_ball_lt_top.ne⟩
  have hψ0 : ∀ t, 0 ≤ ψ t := fun t => setIntegral_nonneg measurableSet_ball fun _ _ => by
    positivity
  -- `ψ` is nondecreasing, since the average is the best constant in square mean.
  have hmono : MonotoneOn ψ (Ioc 0 R) := fun s hs t ht hst =>
    (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq measure_ball_lt_top.ne
      (hfint s hs.2).1 ((hfint s hs.2).2 _)).trans
      (setIntegral_mono_set ((hfint t ht.2).2 _) (ae_of_all _ fun _ => by positivity)
        (ball_subset_ball hst).eventuallyLE)
  have hdec := hit (φ := ψ) (R := R) (B := (4 * decayConst n + 2) * ω * K ^ 2) (ε := 0)
    (by positivity [decayConst_nonneg n]) hε₀.le hmono (fun t _ => hψ0 t)
    (fun s t hs hst htR => by
      have := setIntegral_norm_gradient_sub_setAverage_sq_le hα
        (hG.mono (ball_subset_ball htR)) hu hs hst
        ((ball_subset_ball htR).trans hball)
      simp only [ψ, add_zero]
      linarith) ρ R hρ hρR le_rfl
  -- `ψ R ≤ ‖∇u‖²`.
  have hψR : ψ R ≤ ‖W1p.gradient u‖ ^ 2 := by
    have h0 := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq
      measure_ball_lt_top.ne (hfint R le_rfl).1 ((hfint R le_rfl).2 0)
    simp only [sub_zero] at h0
    exact h0.trans (Lp.setIntegral_norm_sq_le_norm_sq (W1p.gradient u) hball)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (n : ℝ) + 1 + 2 * α := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max 1 ((4 * decayConst n + 2) * ω) := ⟨_, rfl⟩
  rw [← hγ] at hdec ⊢
  rw [← hM]
  have hργ : 0 ≤ ρ ^ γ := by positivity
  have hRγ : 0 ≤ R ^ (-γ) := by positivity
  have h1 : (ρ / R) ^ γ * ψ R ≤ M * ρ ^ γ * R ^ (-γ) * ‖W1p.gradient u‖ ^ 2 := by
    rw [Real.div_rpow hρ.le hR.le, div_eq_mul_inv, ← Real.rpow_neg hR.le]
    calc ρ ^ γ * R ^ (-γ) * ψ R ≤ ρ ^ γ * R ^ (-γ) * ‖W1p.gradient u‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hψR (by positivity)
      _ ≤ M * (ρ ^ γ * R ^ (-γ) * ‖W1p.gradient u‖ ^ 2) :=
          le_mul_of_one_le_left (by positivity) (hM ▸ le_max_left _ _)
      _ = M * ρ ^ γ * R ^ (-γ) * ‖W1p.gradient u‖ ^ 2 := by ring
  have h2 : (4 * decayConst n + 2) * ω * K ^ 2 * ρ ^ γ ≤ M * K ^ 2 * ρ ^ γ := by
    have h := mul_le_mul_of_nonneg_right (hM ▸ le_max_right _ _ :
      (4 * decayConst n + 2) * ω ≤ M) (by positivity : (0 : ℝ) ≤ K ^ 2 * ρ ^ γ)
    linarith
  calc ψ ρ ≤ C * ((ρ / R) ^ γ * ψ R + (4 * decayConst n + 2) * ω * K ^ 2 * ρ ^ γ) := hdec
    _ ≤ C * (M * ρ ^ γ * R ^ (-γ) * ‖W1p.gradient u‖ ^ 2 + M * K ^ 2 * ρ ^ γ) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC.le
    _ = C * M * ρ ^ γ * (R ^ (-γ) * ‖W1p.gradient u‖ ^ 2 + K ^ 2) := by ring

/-- **The mean oscillation of the gradient.** For `0 < α < 1` there is `C`, depending only on `n`
and `α`, such that the following holds. Let `u ∈ H¹(Ω)` solve `-Δu = -div G` weakly on
`Ω ⊆ ℝ^{n+1}`. If `ball x R ⊆ Ω`, `G` is `α`-Hölder with constant `K` on `ball x R` and
`0 < t ≤ R`, then the mean oscillation of `∇u` on `closedBall x t` is at most
`C (R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)} + K) t^α`. -/
private theorem exists_setAverage_norm_gradient_sub_le {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
      {x : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ},
      HolderOnWith K α G (ball x R) →
      (∀ φ : 𝓓(Omega, ℝ),
        energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
          ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      ball x R ⊆ Omega → ∀ t, 0 < t → t ≤ R →
        ⨍ y in closedBall x t, ‖W1p.gradient u y - ⨍ z in closedBall x t, W1p.gradient u z‖ ≤
          C * (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ + K) * t ^ (α : ℝ) := by
  obtain ⟨C, hC, hdec⟩ := exists_setIntegral_norm_gradient_sub_setAverage_sq_le hα hα1 (n := n)
  have hω : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    measureReal_ball_pos _ _ one_pos
  refine ⟨√(C / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)), by positivity, ?_⟩
  intro Omega u G K x R hG hu hball t ht htR
  have hR : 0 < R := ht.trans_le htR
  have hsub := (ball_subset_ball htR).trans hball
  -- The averages over `closedBall x t` and `ball x t` agree.
  rw [Measure.restrict_congr_set (volume.addHaar_closedBall_ae_eq_ball x t)]
  -- Jensen's inequality bounds the mean oscillation by the square mean oscillation.
  have hJ : (⨍ y in ball x t, ‖W1p.gradient u y - ⨍ z in ball x t, W1p.gradient u z‖) ^ 2 ≤
      (∫ y in ball x t, ‖W1p.gradient u y - ⨍ z in ball x t, W1p.gradient u z‖ ^ 2) /
        volume.real (ball x t) := by
    rw [div_eq_inv_mul, ← smul_eq_mul, ← setAverage_eq]
    exact sq_setAverage_norm_le_setAverage_norm_sq (measure_ball_pos volume x ht).ne'
      measure_ball_lt_top.ne (((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hsub
        measure_ball_lt_top.ne).sub (integrableOn_const measure_ball_lt_top.ne))
      ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hsub
        measure_ball_lt_top.ne (⨍ z in ball x t, W1p.gradient u z))
  have hψ := hdec hG hu hball t ht htR
  have hN := norm_nonneg (W1p.gradient u)
  have ha2 : (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖) ^ 2 =
      R ^ (-((n : ℝ) + 1 + 2 * α)) * ‖W1p.gradient u‖ ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 2
    push_cast
    ring
  have htn : 0 < t ^ (n + 1) := by positivity
  rw [← pow_le_pow_iff_left₀ (average_nonneg fun _ => norm_nonneg _) (by positivity) two_ne_zero]
  refine hJ.trans ?_
  rw [measureReal_ball_eq x ht, div_le_iff₀ (by positivity), mul_pow, mul_pow,
    Real.sq_sqrt (by positivity)]
  refine hψ.trans ?_
  rw [rpow_add_two_mul_eq ht, ← ha2]
  have hK : (0 : ℝ) ≤ K := K.2
  have hcross : 0 ≤ R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ * K := by positivity
  have key : C * (t ^ (n + 1) * (t ^ (α : ℝ)) ^ 2) *
      ((R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖) ^ 2 + (K : ℝ) ^ 2) ≤
      C * (t ^ (n + 1) * (t ^ (α : ℝ)) ^ 2) *
      (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ + K) ^ 2 := by
    gcongr
    nlinarith
  calc _ ≤ _ := key
    _ = C / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) *
          (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ + K) ^ 2 * (t ^ (α : ℝ)) ^ 2 *
          (t ^ (n + 1) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
        field_simp

/-- The average of `∇u` over `closedBall z R`, for `ball z R ⊆ Ω`, is at most
`ω^{-1/2} R^{-(n+1)/2} ‖∇u‖_{L²(Ω)}` in norm, where `ω` is the measure of the unit ball. -/
private theorem norm_setAverage_closedBall_gradient_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 < R) (hball : ball z R ⊆ Omega) :
    ‖⨍ y in closedBall z R, W1p.gradient u y‖ ≤
      (√(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))⁻¹ *
        (R ^ (-((n : ℝ) + 1) / 2) * ‖W1p.gradient u‖) := by
  have hω : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    measureReal_ball_pos _ _ one_pos
  rw [Measure.restrict_congr_set (volume.addHaar_closedBall_ae_eq_ball z R)]
  -- Hölder's bound `‖⨍_B f‖ ≤ |B|^{-1/2} ‖f‖_{L²(B)}` on an average, with
  -- `‖f‖_{L²(B)} ≤ ‖f‖_{L²(Ω)}`.
  have h := (enorm_setAverage_le (f := W1p.gradient u) (mu := volume) (p := 2)
    one_le_two ENNReal.ofNat_ne_top).trans
    (mul_le_mul' le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)))
  replace h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero
    (measure_ball_pos volume z hR).ne' measure_ball_lt_top.ne) (Lp.eLpNorm_ne_top _)) h
  rw [toReal_enorm, ENNReal.toReal_mul, ← Lp.norm_def, ← ENNReal.toReal_rpow, ← measureReal_def,
    measureReal_ball_eq z hR] at h
  refine h.trans_eq ?_
  rw [ENNReal.toReal_ofNat, Real.mul_rpow (by positivity) hω.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hR.le, Real.sqrt_eq_rpow, ← Real.rpow_neg hω.le]
  push_cast
  ring_nf

/-- The precise representative of `∇u` at `z` is controlled by the mean oscillation of `∇u` near
`z` and by `‖∇u‖_{L²(Ω)}`. If `ball z R ⊆ Ω` and the mean oscillation of `∇u` on `closedBall z t`
is at most `M t^α` for `0 < t ≤ R`, then
`‖∇u*(z)‖ ≤ (2^{n+1} / (1 - 2^{-α}) M + ω^{-1/2} R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)}) R^α`, where `∇u*` is
the precise representative and `ω` is the measure of the unit ball. -/
private theorem norm_preciseRepresentative_gradient_le {α : ℝ≥0} (hα : 0 < α)
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R M : ℝ} (hR : 0 < R) (hball : ball z R ⊆ Omega)
    (hint : IntegrableOn (W1p.gradient u) (closedBall z R))
    (hM : ∀ t, 0 < t → t ≤ R →
      ⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖ ≤
        M * t ^ (α : ℝ)) :
    ‖preciseRepresentative volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) z‖ ≤
      (2 ^ (n + 1) / (1 - 2 ^ (-(α : ℝ))) * M +
        (√(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))⁻¹ *
          (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)) * R ^ (α : ℝ) := by
  -- Compare the precise representative with the average over `closedBall z R`.
  have h1 := norm_setAverage_closedBall_sub_preciseRepresentative_le (α := (α : ℝ))
    (NNReal.coe_pos.2 hα) hint hM hR le_rfl
  rw [finrank_euclideanSpace_fin] at h1
  have h2 := norm_setAverage_closedBall_gradient_le u hR hball
  have haR : R ^ (-((n : ℝ) + 1) / 2) * ‖W1p.gradient u‖ =
      R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ * R ^ (α : ℝ) := by
    rw [mul_right_comm, ← Real.rpow_add hR]
    congr 2
    ring
  rw [haR] at h2
  have h3 := norm_sub_le (⨍ y in closedBall z R, W1p.gradient u y)
    ((⨍ y in closedBall z R, W1p.gradient u y) - preciseRepresentative volume (W1p.gradient u) z)
  rw [sub_sub_cancel] at h3
  calc _ ≤ _ := h3
    _ ≤ _ := add_le_add h2 h1
    _ = _ := by ring

end Comparison

/-- **Interior Hölder continuity of the gradient for `-Δu = -div G`.** Let `0 < α < 1`. There is
a constant `C`, depending only on `n` and `α`, such that the following holds. Let `Ω ⊆ ℝ^{n+1}` be
open and let `u ∈ H¹(Ω)` be a weak solution of `-Δu = -div G` in `Ω`, that is
`∫_Ω ⟨∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ`, where `G` is `α`-Hölder with constant
`K` on the open `R`-thickening of `S` (the points at distance less than `R` from `S`), which lies
in `Ω`. Then the precise representative of `∇u` is `α`-Hölder on `S`, with constant
`C (K + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`.

The precise representative agrees with `∇u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). The exponent of `G` passes to
`∇u` without loss; this is false for `α = 1`, which is why `α < 1` is assumed. -/
theorem exists_holderOnWith_preciseRepresentative_gradient {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      HolderOnWith K α G (thickening R S) →
      (∀ φ : 𝓓(Omega, ℝ),
        energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
          ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      0 < R → thickening R S ⊆ Omega →
        HolderOnWith (C * (K + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)).toNNReal α
          (preciseRepresentative volume
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  obtain ⟨C₀, hC₀, hosc⟩ := exists_setAverage_norm_gradient_sub_le hα hα1 (n := n)
  obtain ⟨ω, hω⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  have hα' : (0 : ℝ) < α := hα
  have hcα : 0 < 1 - (2 : ℝ) ^ (-(α : ℝ)) :=
    sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hα'))
  obtain ⟨cα, hcαdef⟩ : ∃ cα : ℝ, cα = 2 ^ (n + 1) / (1 - 2 ^ (-(α : ℝ))) := ⟨_, rfl⟩
  have hcα0 : 0 ≤ cα := hcαdef ▸ by positivity
  refine ⟨2 * 2 ^ (α : ℝ) * cα * C₀ + 2 * 2 ^ (α : ℝ) * (cα * C₀ + (√ω)⁻¹), by positivity, ?_⟩
  intro Omega u G K S R hG hu hR hRS
  have hball : ∀ z ∈ S, ball z R ⊆ Omega := fun z hz => (ball_subset_thickening hz R).trans hRS
  -- `∇u` is integrable on `closedBall z t` for `t ≤ R`; for `t = R` because `closedBall z R` and
  -- `ball z R` differ by a null set.
  have hint : ∀ z ∈ S, ∀ t ≤ R, IntegrableOn (W1p.gradient u) (closedBall z t) :=
    fun z hz t ht => by
      rcases ht.lt_or_eq with ht | ht
      · exact (Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two
          ((closedBall_subset_ball ht).trans (hball z hz)) measure_closedBall_lt_top.ne
      · rw [ht]
        exact ((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two (hball z hz)
          measure_ball_lt_top.ne).congr_set_ae
            (volume.addHaar_closedBall_ae_eq_ball z R)
  obtain ⟨a, ha⟩ : ∃ a, a = R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ by positivity
  rw [← ha]
  have hM : ∀ z ∈ S, ∀ t, 0 < t → t ≤ R →
      ⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖ ≤
        C₀ * (a + K) * t ^ (α : ℝ) := fun z hz t ht htR => by
    rw [ha]
    exact hosc (hG.mono (ball_subset_thickening hz R)) hu (hball z hz) t ht htR
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have hK : (0 : ℝ) ≤ K := K.2
  suffices h : dist (preciseRepresentative volume (W1p.gradient u) x)
      (preciseRepresentative volume (W1p.gradient u) y) ≤
      (2 * 2 ^ (α : ℝ) * cα * C₀ + 2 * 2 ^ (α : ℝ) * (cα * C₀ + (√ω)⁻¹)) * (K + a) *
        dist x y ^ (α : ℝ) from
    h.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity))
  rcases le_or_gt (2 * dist x y) R with hd | hd
  · -- Nearby points: Campanato's estimate.
    have h := dist_preciseRepresentative_le_of_setAverage_norm_sub_le hα' (hint x hx _ hd)
      (fun r hr hr' => hM x hx r hr (hr'.trans hd))
      (fun r hr hr' => hM y hy r hr (by linarith [dist_nonneg (x := x) (y := y)]))
    rw [finrank_euclideanSpace_fin, ← hcαdef] at h
    refine h.trans ?_
    have hd0 : 0 ≤ dist x y ^ (α : ℝ) := by positivity
    have h1 : 0 ≤ 2 * 2 ^ (α : ℝ) * (cα * C₀ + (√ω)⁻¹) * (K + a) * dist x y ^ (α : ℝ) := by
      positivity
    nlinarith
  · -- Distant points: both values are controlled by averages over balls of radius `R`.
    have hbound : ∀ z ∈ S, ‖preciseRepresentative volume (W1p.gradient u) z‖ ≤
        (cα * C₀ + (√ω)⁻¹) * (a + K) * R ^ (α : ℝ) := fun z hz => by
      refine (norm_preciseRepresentative_gradient_le hα u hR (hball z hz) (hint z hz R le_rfl)
        (hM z hz)).trans ?_
      rw [← hcαdef, ← hω, ← ha]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      nlinarith [mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg ω)) hK]
    have hRd : R ^ (α : ℝ) ≤ 2 ^ (α : ℝ) * dist x y ^ (α : ℝ) := by
      rw [← Real.mul_rpow zero_le_two dist_nonneg]
      exact Real.rpow_le_rpow hR.le hd.le hα'.le
    have hsum := dist_le_norm_add_norm (preciseRepresentative volume (W1p.gradient u) x)
      (preciseRepresentative volume (W1p.gradient u) y)
    have hc : 0 ≤ (cα * C₀ + (√ω)⁻¹) * (a + K) := by positivity
    have h1 : 0 ≤ 2 * 2 ^ (α : ℝ) * cα * C₀ * (K + a) * dist x y ^ (α : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hRd hc
    nlinarith [hbound x hx, hbound y hy]


end PDE

end TauCeti
