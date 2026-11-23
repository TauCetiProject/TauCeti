/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.BoundaryValues
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.PDE.Regularity.Boundary.DirichletHolder

/-!
# The global Hölder estimate for the Dirichlet problem with general data

Let `Ω ⊆ ℝⁿ⁺¹` be a bounded open set, let `a` be measurable and uniformly elliptic on `Ω` with
constants `0 < λ ≤ Λ`, and consider the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` in `Ω`, `u = G` on `∂Ω`,

with a scalar datum `f ∈ L² ∩ Lʳ(Ω)`, `r > 1`, `2 r > n + 1`, a divergence datum
`F ∈ L^q(Ω; ℝⁿ⁺¹)`, `q > 2`, `q > n + 1`, and boundary values `G` that are bounded by `K₀` and
`K₁`-Lipschitz on `Ω`. A weak solution is `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` for some `g ∈ H¹(Ω)`
whose value is `G` almost everywhere, and `a(u, v) = ∫_Ω f v - ∫_Ω F · ∇v` for every
`v ∈ H¹₀(Ω)`. By Lax–Milgram such a solution exists and is unique
(`UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball`,
in the `TauCeti.PDE` namespace).
This file proves that it is Hölder continuous up to the boundary, with the estimate

`[u]_{α; Ω} ≤ C (‖f‖_{Lʳ(Ω)} / λ + ‖F‖_{L^q(Ω)} / λ + K₀ + K₁)`,

as soon as the complement of `Ω` has uniform positive density at its own points. This is the
global Hölder estimate of Gilbarg–Trudinger, Theorem 8.29, with all three kinds of data at once.
It is the linear input of Schauder's fixed-point method for quasilinear equations, where the
estimate must be uniform over all coefficients with the same ellipticity constants: here `α` and
`C` depend only on `λ`, `Λ`, `r`, `q`, the dimension and the geometry of `Ω`, never on `a`.

## Main declarations

* `TauCeti.PDE.exists_ae_eq_and_holderOnWith_of_measureReal_ball_diff_add_divergence`: the
  estimate on a set `Ω ⊆ B(z, ρ)` whose complement fills the proportion `θ` of every ball
  `B(y, s)` with `y ∉ Ω` and `0 < s ≤ R`, with `α` and `C` depending on `Ω` only through `θ`,
  `R` and `ρ`.

The estimate on a bounded Lipschitz domain, for any additive Haar measure and with `f ∈ Lʳ(Ω)`
alone, is `Set.IsLipschitzDomain.exists_ae_eq_and_holderOnWith_add_divergence` in
`TauCeti.Analysis.PDE.Regularity.Boundary.GeneralData`.

## The argument

The equation is linear, so the data are treated separately. By Lax–Milgram there is
`w ∈ H¹₀(Ω)` with `a(w, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. The global Hölder estimate with
zero boundary values
(`TauCeti.PDE.exists_holderWith_preciseRepresentative_indicator_of_measureReal_ball_diff`)
makes `w` Hölder with constant `O(‖f‖_{Lʳ(Ω)} / λ)`. The difference `u - w` has boundary values
`G` and solves `-∂ᵢ(aⁱʲ ∂ⱼ(u - w)) = ∂ᵢFⁱ`, so the estimate with a divergence datum and
Lipschitz boundary values
(`TauCeti.PDE.exists_ae_eq_and_holderOnWith_of_measureReal_ball_diff_divergence`) makes it
Hölder with constant `O(‖F‖_{L^q(Ω)} / λ + K₀ + K₁)`. The two exponents may differ; on the
bounded set `Ω` both functions are Hölder with the smaller one (`HolderOnWith.of_le`), and their
sum represents `u`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.3 and 8.29.
-/

public section

open Filter MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- **Splitting off the scalar datum.** On `Ω ⊆ B(z, ρ)`, let `u` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` with `f ∈ L²(Ω)` and boundary values `g`. Then there is `w ∈ H¹₀(Ω)`
solving `-∂ᵢ(aⁱʲ ∂ⱼw) = f`, and `u - w` has boundary values `g` and solves
`-∂ᵢ(aⁱʲ ∂ⱼ(u - w)) = ∂ᵢFⁱ`. -/
private theorem exists_w1p0_forall_energyFormH1_eq_and_sub
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))} {ρ : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {u g : W1p volume Omega 2} (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z ρ)
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega)) (hf2 : MemLp f 2 (volume.restrict Omega))
    (hug : u - g ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
      (∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x) -
        ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p volume Omega 2) x⟫) :
    ∃ w : W1p0 volume Omega 2,
      (∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 (w : W1p volume Omega 2)
        (v : W1p volume Omega 2) = ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x) ∧
      u - (w : W1p volume Omega 2) - g ∈ w1p0Submodule volume Omega 2 ∧
      ∀ v : W1p0 volume Omega 2,
        energyFormH1 a 0 0 (u - (w : W1p volume Omega 2)) (v : W1p volume Omega 2) =
          -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p volume Omega 2) x⟫ := by
  obtain ⟨w, hw, -⟩ := h.existsUnique_isWeakSolutionDirichlet_of_subset_ball (b := 0) (c := 0)
    (beta := 0) (gamma := 0) ha aestronglyMeasurable_zero aestronglyMeasurable_zero (by simp)
    (by simp) (by simp) hball (by simpa using h.pos) (hf2.toLp f)
  have hw' : ∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 (w : W1p volume Omega 2)
      (v : W1p volume Omega 2) = ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x := by
    intro v
    rw [(isWeakSolutionDirichlet_iff _ _).1 hw v]
    exact integral_congr_ae (by filter_upwards [hf2.coeFn_toLp] with x hx; rw [hx])
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (volume.restrict Omega) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) h.upper_nonneg ha
      aestronglyMeasurable_const aestronglyMeasurable_const (fun _ hx => h.upper_bound hx)
      (fun _ _ => by simp) (fun _ _ => by simp)
  refine ⟨w, hw', ?_, fun v => ?_⟩
  · rw [sub_right_comm, ← ClosedSubmodule.mem_toSubmodule_iff]
    exact Submodule.sub_mem _ ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 hug) w.property
  · rw [energyFormH1_sub_left (b := 0) (c := 0) hcoeff, hu v, hw' v]
    ring

/-- A set inside a ball of radius `ρ` has finite volume, at most the volume of the ball of radius
`ρ` about `0`. -/
private theorem measure_ne_top_and_measureReal_le_of_subset_ball
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))} {ρ : ℝ}
    (hball : s ⊆ ball z ρ) :
    volume s ≠ ∞ ∧ volume.real s ≤ volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ρ) := by
  refine ⟨((measure_mono hball).trans_lt measure_ball_lt_top).ne, ?_⟩
  rw [← Measure.addHaar_real_ball_center volume z ρ]
  exact measureReal_mono hball measure_ball_lt_top.ne

/-- The global Hölder estimate with zero boundary values
(`TauCeti.PDE.exists_holderWith_preciseRepresentative_indicator_of_measureReal_ball_diff`), with
a constant uniform over the open sets inside a ball of radius `ρ` whose complement has density
`θ` at the radii `s ≤ R`. -/
private theorem exists_holderWith_preciseRepresentative_indicator_of_subset_ball
    {lam Lam : ℝ} {r : ℝ≥0} (hr : 1 < r) (hrn : (n : ℝ) + 1 < 2 * r) {θ : ℝ} (hθ : 0 < θ)
    {R ρ : ℝ} (hR : 0 < R) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ 0 < C ∧
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
        {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {w : W1p volume Omega 2},
        (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z ρ →
        (∀ y ∉ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ∀ s, 0 < s → s ≤ R →
          θ * volume.real (ball y s) ≤
            volume.real (ball y s \ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) →
        UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam →
        AEStronglyMeasurable a (volume.restrict Omega) →
        MemLp f r (volume.restrict Omega) →
        w ∈ w1p0Submodule volume Omega 2 →
        (∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 w (v : W1p volume Omega 2) =
          ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x) →
        HolderWith (C * ((eLpNorm f r (volume.restrict Omega)).toReal / lam)).toNNReal α
          (preciseRepresentative volume
            ((Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).indicator (W1p.value w))) := by
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) = n + 1 := by simp
  obtain ⟨α, C, hα, hC, hmain⟩ :=
    exists_holderWith_preciseRepresentative_indicator_of_measureReal_ball_diff
      (mu := (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))) (lam := lam) (Lam := Lam) hr
      (by rwa [hcard]) hθ
  -- `|Ω|` is at most the volume `V` of a ball of radius `ρ`, and its exponent is nonnegative.
  set V := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ρ)
  set N := (Fintype.card (Fin (n + 1)) : ℝ)
  have he : 0 ≤ 2 / N - (r : ℝ)⁻¹ := by
    rw [sub_nonneg, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by rw [hcard]; positivity)]
    linarith
  refine ⟨α, C * R ^ (-(α : ℝ)) * (V ^ (2 / N - (r : ℝ)⁻¹) + R ^ (2 - N / r)), hα,
    by positivity, fun {Omega z a f w} hball hext h ha hf hw0 hw => ?_⟩
  obtain ⟨hfin, hΩV⟩ := measure_ne_top_and_measureReal_le_of_subset_ball hball
  have hlam := h.pos
  refine (hmain hfin h ha hf hw0 hw hR hext).mono (Real.toNNReal_le_toNNReal ?_)
  rw [mul_div_assoc]
  gcongr

/-- The arithmetic of the constant of the divergence datum and the boundary values: if
`0 ≤ P' ≤ P` and `0 ≤ S' ≤ S`, then
`P' (Y + Λ K₁ S') / λ + R K₁ + K₀ ≤ (P (1 + Λ S / λ) + R + 1) (Y / λ + K₀ + K₁)`. -/
private theorem mul_add_mul_div_add_add_le {P P' S S' Y K₀ K₁ R lam Lam : ℝ} (hP' : 0 ≤ P')
    (hPP : P' ≤ P) (hS' : 0 ≤ S') (hSS : S' ≤ S) (hY : 0 ≤ Y) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hR : 0 ≤ R) (hlam : 0 < lam) (hLam : 0 ≤ Lam) :
    P' * (Y + Lam * K₁ * S') / lam + R * K₁ + K₀ ≤
      (P * (1 + Lam * S / lam) + R + 1) * (Y / lam + K₀ + K₁) := by
  have hP : 0 ≤ P := hP'.trans hPP
  have hX : 0 ≤ Y / lam := div_nonneg hY hlam.le
  have hB' : Lam * S' / lam ≤ Lam * S / lam := by gcongr
  have e : P' * (Y + Lam * K₁ * S') / lam = P' * (Y / lam) + P' * (Lam * S' / lam) * K₁ := by
    field_simp
  rw [e]
  have h₁ : P' * (Y / lam) ≤ P * (Y / lam) := mul_le_mul_of_nonneg_right hPP hX
  have h₂ : P' * (Lam * S' / lam) * K₁ ≤ P * (Lam * S / lam) * K₁ :=
    mul_le_mul_of_nonneg_right (mul_le_mul hPP hB' (by positivity) hP) hK₁
  nlinarith [mul_nonneg hP hK₀, mul_nonneg hP hK₁, mul_nonneg hR hX, mul_nonneg hR hK₀,
    mul_nonneg (mul_nonneg hP (div_nonneg (mul_nonneg hLam (hS'.trans hSS)) hlam.le)) hX,
    mul_nonneg (mul_nonneg hP (div_nonneg (mul_nonneg hLam (hS'.trans hSS)) hlam.le)) hK₀]

/-- The global Hölder estimate with a divergence datum and Lipschitz boundary values
(`TauCeti.PDE.exists_ae_eq_and_holderOnWith_of_measureReal_ball_diff_divergence`), with a
constant uniform over the open sets inside a ball of radius `ρ` whose complement has density `θ`
at the radii `s ≤ R`. -/
private theorem exists_ae_eq_and_holderOnWith_of_subset_ball_divergence
    {lam Lam : ℝ} {q : ℝ≥0} (hq : 2 < (q : ℝ)) (hqn : (n : ℝ) + 1 < q) {θ : ℝ} (hθ : 0 < θ)
    {R ρ : ℝ} (hR : 0 < R) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ (α : ℝ) ≤ 1 ∧ 0 < C ∧
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
        {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
        {u g : W1p volume Omega 2} {G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {K₀ K₁ : ℝ≥0},
        (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z ρ →
        (∀ y ∉ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ∀ s, 0 < s → s ≤ R →
          θ * volume.real (ball y s) ≤
            volume.real (ball y s \ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) →
        UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam →
        AEStronglyMeasurable a (volume.restrict Omega) →
        MemLp F q (volume.restrict Omega) →
        u - g ∈ w1p0Submodule volume Omega 2 →
        (∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
          -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p volume Omega 2) x⟫) →
        W1p.value g =ᵐ[volume.restrict Omega] G →
        LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
        (∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) →
        ∃ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, W1p.value u =ᵐ[volume.restrict Omega] v ∧
          HolderOnWith (C * ((eLpNorm F q (volume.restrict Omega)).toReal / lam + K₀ + K₁)).toNNReal
            α v Omega := by
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) = n + 1 := by simp
  obtain ⟨α, C, hα, hα1, hC, hmain⟩ :=
    exists_ae_eq_and_holderOnWith_of_measureReal_ball_diff_divergence
      (mu := (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))) (lam := lam) (Lam := Lam) hq
      (by rwa [hcard]) hθ
  -- `|Ω|` is at most the volume `V` of a ball of radius `ρ`, and its exponents are nonnegative.
  set V := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ρ)
  set N := (Fintype.card (Fin (n + 1)) : ℝ)
  set P := V ^ (N⁻¹ - (q : ℝ)⁻¹) + R ^ (1 - N / q)
  have he : 0 ≤ N⁻¹ - (q : ℝ)⁻¹ :=
    sub_nonneg.2 (inv_anti₀ (by rw [hcard]; positivity) (by linarith))
  refine ⟨α, C * R ^ (-(α : ℝ)) * (P * (1 + |Lam| * V ^ (q : ℝ)⁻¹ / |lam|) + R + 1), hα, hα1,
    by positivity, fun {Omega z a F u g G K₀ K₁} hball hext h ha hF hug hu hgG hG hG0 => ?_⟩
  obtain ⟨hfin, hΩV⟩ := measure_ne_top_and_measureReal_le_of_subset_ball hball
  have hlam := h.pos
  have hLam := h.upper_nonneg
  obtain ⟨v, hv, hvH⟩ := hmain hfin h ha hF hug hu hgG hG hG0 hR hext
  refine ⟨v, hv, hvH.mono_const (Real.toNNReal_le_toNNReal ?_)⟩
  rw [abs_of_nonneg hLam, abs_of_pos hlam, mul_assoc _ (_ + _ + _)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_add_mul_div_add_add_le (by positivity) ?_ (by positivity)
    (Real.rpow_le_rpow measureReal_nonneg hΩV (by positivity)) ENNReal.toReal_nonneg
    K₀.coe_nonneg K₁.coe_nonneg hR.le hlam hLam
  have := Real.rpow_le_rpow measureReal_nonneg hΩV he
  linarith

/-- **The global Hölder estimate for the Dirichlet problem with a scalar datum, a divergence
datum and Lipschitz boundary values, under an exterior density condition.** Let `r > 1` with
`2 r > n + 1`, let `q > 2` with `q > n + 1`, and fix a proportion `θ > 0` and radii `R, ρ > 0`.
There are `α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `r`, `q`, `θ`, `R`, `ρ` and `n`,
such that the following holds on `ℝⁿ⁺¹`. Let `Ω ⊆ B(z, ρ)` be open, and suppose that the
complement of `Ω` fills the proportion `θ` of every ball `B(y, s)` with `y ∉ Ω` and `0 < s ≤ R`.
Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let
`f ∈ L² ∩ Lʳ(Ω)` and `F ∈ L^q(Ω; ℝⁿ⁺¹)`, and let `G` be bounded by `K₀` and `K₁`-Lipschitz on
`Ω`. Let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` with boundary values `G`:
`a(u, v) = ∫_Ω f v - ∫_Ω F · ∇v` for every `v ∈ H¹₀(Ω)`, and `u - g ∈ H¹₀(Ω)` for some
`g ∈ H¹(Ω)` whose value is `G` almost everywhere on `Ω`. Then `u` agrees almost everywhere on
`Ω` with a function that is `α`-Hölder on `Ω` with constant

`C (‖f‖_{Lʳ(Ω)} / λ + ‖F‖_{L^q(Ω)} / λ + K₀ + K₁)`.

No regularity of `∂Ω` beyond the exterior density condition, and no regularity of the
coefficients beyond measurability, is assumed. The datum `f` is assumed square integrable only so
that the scalar part of the problem can be solved by Lax–Milgram; its `L²` norm does not enter the
estimate. -/
theorem exists_ae_eq_and_holderOnWith_of_measureReal_ball_diff_add_divergence
    {lam Lam : ℝ} {r q : ℝ≥0} (hr : 1 < r) (hrn : (n : ℝ) + 1 < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (n : ℝ) + 1 < q) {θ : ℝ} (hθ : 0 < θ) {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ (α : ℝ) ≤ 1 ∧ 0 < C ∧
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
        {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
        {F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
        {u g : W1p volume Omega 2} {G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {K₀ K₁ : ℝ≥0},
        (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z ρ →
        (∀ y ∉ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ∀ s, 0 < s → s ≤ R →
          θ * volume.real (ball y s) ≤
            volume.real (ball y s \ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) →
        UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam →
        AEStronglyMeasurable a (volume.restrict Omega) →
        MemLp f 2 (volume.restrict Omega) →
        MemLp f r (volume.restrict Omega) →
        MemLp F q (volume.restrict Omega) →
        u - g ∈ w1p0Submodule volume Omega 2 →
        (∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
          (∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x) -
            ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p volume Omega 2) x⟫) →
        W1p.value g =ᵐ[volume.restrict Omega] G →
        LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
        (∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) →
        ∃ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, W1p.value u =ᵐ[volume.restrict Omega] v ∧
          HolderOnWith (C * ((eLpNorm f r (volume.restrict Omega)).toReal / lam +
            (eLpNorm F q (volume.restrict Omega)).toReal / lam + K₀ + K₁)).toNNReal α v
            Omega := by
  obtain ⟨α₁, C₁, hα₁, hC₁, h₁⟩ := exists_holderWith_preciseRepresentative_indicator_of_subset_ball
    (lam := lam) (Lam := Lam) (ρ := ρ) hr hrn hθ hR
  obtain ⟨α₂, C₂, hα₂, hα₂1, hC₂, h₂⟩ := exists_ae_eq_and_holderOnWith_of_subset_ball_divergence
    (lam := lam) (Lam := Lam) (ρ := ρ) hq hqn hθ hR
  -- On `Ω ⊆ B(z, ρ)` an `αᵢ`-Hölder function is `min α₁ α₂`-Hölder, at the cost `(2 ρ)^(αᵢ - α)`.
  refine ⟨min α₁ α₂, C₁ * (2 * ρ) ^ ((α₁ : ℝ) - min (α₁ : ℝ) α₂) +
    C₂ * (2 * ρ) ^ ((α₂ : ℝ) - min (α₁ : ℝ) α₂), lt_min hα₁ hα₂,
    (NNReal.coe_le_coe.2 (min_le_right _ _)).trans hα₂1, by positivity,
    fun {Omega z a f F u g G K₀ K₁} hball hext h ha hf2 hf hF hug hu hgG hG hG0 => ?_⟩
  obtain ⟨w, hw, hug₂, hu₂⟩ := exists_w1p0_forall_energyFormH1_eq_and_sub hball h ha hf2 hug hu
  obtain ⟨v₂, hv₂, hH₂⟩ := h₂ hball hext h ha hF hug₂ hu₂ hgG hG hG0
  have hdiam : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∀ y ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
        edist x y ≤ ((2 * ρ).toNNReal : ℝ≥0∞) := fun x hx y hy => by
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ((dist_triangle_right x y z).trans ?_)
    linarith [mem_ball.1 (hball hx), mem_ball.1 (hball hy)]
  have hsum := (((h₁ hball hext h ha hf w.property hw).holderOnWith
    (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))).of_le hdiam (min_le_left α₁ α₂)).add
    (hH₂.of_le hdiam (min_le_right α₁ α₂))
  refine ⟨_, ?_, HolderOnWith.of_dist_le fun x hx y hy => (hsum.dist_le hx hy).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg dist_nonneg _))⟩
  · simpa only [sub_sub_cancel] using
      value_ae_eq_preciseRepresentative_indicator_sub_add u (u - (w : W1p volume Omega 2)) hv₂
  -- The arithmetic of the constant.
  have hlam := h.pos
  have hT₁ : 0 ≤ (2 * ρ) ^ ((α₁ : ℝ) - min (α₁ : ℝ) α₂) := by positivity
  have hT₂ : 0 ≤ (2 * ρ) ^ ((α₂ : ℝ) - min (α₁ : ℝ) α₂) := by positivity
  have hXf : 0 ≤ (eLpNorm f r (volume.restrict Omega)).toReal / lam := by positivity
  have hXF : 0 ≤ (eLpNorm F q (volume.restrict Omega)).toReal / lam + K₀ + K₁ := by positivity
  push_cast
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity),
    Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hC₁.le hT₁) hXF, mul_nonneg (mul_nonneg hC₂.le hT₂) hXf]

end PDE

end TauCeti
