/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness
public import TauCeti.Analysis.PDE.Regularity.HolderContinuity
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.MeasureTheory.Function.EssSup
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Hölder continuity of weak solutions with a right-hand side

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants
`0 < λ ≤ Λ`, and let `f ∈ Lʳ` with `r > 1` and `r > n/2`. This file extends De Giorgi's theorem
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative` from `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` to weak solutions
`u ∈ H¹(Ω)` of

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, that is `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`.

Such a solution is locally bounded and has a locally Hölder continuous representative, with an
exponent depending only on `λ`, `Λ`, `n`, `r` and the normalization of the Haar measure, and with
constants controlled by `‖u‖_{L²}` and `‖f‖_{Lʳ}/λ`. No regularity of the coefficients beyond
measurability is assumed.

The right-hand side is split off one ball at a time. On `B = B(x₀, ρ) ⊆ Ω`, the Dirichlet problem
`-∂ᵢ(aⁱʲ ∂ⱼw) = f` in `B`, `w ∈ H¹₀(B)`, has a solution
(`TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp`), and
Stampacchia's bound `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow` gives
`|w| ≤ C ρ^(2 - n/r) ‖f‖_{Lʳ(B)} / λ`. The difference `h = u - w` solves the homogeneous equation
on `B`, so De Giorgi's local boundedness and oscillation decay apply to it. The error `w` is small
on small balls exactly because `2 - n/r > 0`. Comparing the essential oscillation of `u` on
concentric balls with that of `h` gives

`osc_{B(x₀, s)} u ≤ C₀ (s/ρ)^α₀ osc_{B(x₀, ρ)} u + C ρ^(2 - n/r) ‖f‖_{Lʳ} / λ`,

and the iteration lemma `TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add` turns
this into a power law with exponent `min (2 - n/r) (α₀/2)`. The precise representative then
converts the power law into a Hölder bound, as for the homogeneous equation.

## Main declarations

All in the namespace `TauCeti.PDE`.

* `exists_forall_energyFormH1_eq_zero_ae_abs_sub_le`: on a ball, a weak solution with right-hand
  side `f` is a weak solution of the homogeneous equation up to an error bounded by
  `K ρ^(2 - n/r) ‖f‖_{Lʳ} / λ`.
* `exists_ae_abs_value_le_mul_add_of_memLp`: local boundedness,
  `|u| ≤ D (R^(-n/2) ‖u‖_{L²(B_R)} + R^(2 - n/r) ‖f‖_{Lʳ(B_R)} / λ)` on `B_{R/2}`.
* `exists_essSup_sub_essInf_le_mul_rpow_mul_add_of_memLp`: one step of oscillation decay,
  comparing the essential oscillations of `u` on two concentric balls.
* `exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_memLp`: the interior oscillation estimate.
* `exists_holderOnWith_preciseRepresentative_of_memLp`: **De Giorgi's theorem with a right-hand
  side**, the Hölder continuity of the precise representative.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.17, 8.22 and 8.24, and Lemma 8.23.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
* M. Giaquinta, *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic
  Systems*, Chapter III, Lemma 2.1.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

namespace PDE

/-! ### Splitting off the right-hand side on a ball -/

/-- **Splitting off the right-hand side on a ball.** Let `n ≥ 1` be the dimension and let `r > 1`
with `r > n/2`. There is `K > 0`, depending only on `n`, `r` and the normalization of `mu`, such
that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is
`a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with `f ∈ Lʳ(B(x₀, ρ))` and `B(x₀, ρ) ⊆ Ω`. Then on
`B = B(x₀, ρ)` there is a weak solution `h ∈ H¹(B)` of the homogeneous equation
`-∂ᵢ(aⁱʲ ∂ⱼh) = 0` with

`|u - h| ≤ K ρ^(2 - n/r) ‖f‖_{Lʳ(B)} / λ` almost everywhere on `B`.

This transfers estimates for the homogeneous equation to equations with a right-hand side. -/
theorem exists_forall_energyFormH1_eq_zero_ae_abs_sub_le [Nonempty ι] {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ ρ)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ h : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 h (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value h x| ≤
          K * ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam := by
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨C, hC, hstamp⟩ := exists_ae_abs_value_le_mul_div_mul_rpow (mu := mu) hr hrn
  have hrn' : n * (2 - r) < 2 * r := by
    have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
    nlinarith [mul_pos hn (sub_pos.2 hr1)]
  set e : ℝ := 2 / n - (r : ℝ)⁻¹
  refine ⟨C * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e,
    mul_pos hC (Real.rpow_pos_of_pos (measureReal_ball_pos _ _ one_pos) _), ?_⟩
  intro Omega a lam Lam f u x₀ ρ h ha hf hu hρ hball
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ ρ, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have hBfin : mu B ≠ ∞ := measure_ball_lt_top.ne
  have hBell : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ ι)) a lam Lam := h.mono_set hball
  have hBmeas : AEStronglyMeasurable a (mu.restrict B) :=
    ha.mono_measure (Measure.restrict_mono hball le_rfl)
  -- The weak solution `w ∈ H¹₀(B)` of `-∂ᵢ(aⁱʲ ∂ⱼw) = f` on `B`, and its bound.
  obtain ⟨w, hw, -⟩ :=
    hBell.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp (c := 0) (gamma := 0) hBmeas
      aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hBfin hr hrn' hf
  have hwbound := hstamp (Omega := B) (c := 0) (gamma := 0) hBfin hBell hBmeas
    aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hf hw
  -- The homogeneous part `h = u|_B - w`.
  have huB := energyFormH1_restrictL_eq_setIntegral hB hu
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    hBell.upper_nonneg hBmeas aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => hBell.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  refine ⟨W1p.restrictL hB u - (w : W1p mu B 2), fun v => ?_, ?_⟩
  · rw [energyFormH1_sub_left hcoeff, huB v, hw v, sub_self]
  -- `mu(B)^e = ρ^(2 - n/r) mu(B(0, 1))^e`.
  have hmeas : mu.real (ball x₀ ρ) ^ e =
      ρ ^ (2 - n / r) * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e := by
    rw [Measure.addHaar_real_ball_of_pos _ _ hρ, finrank_euclideanSpace,
      Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    congr 2
    simp only [e, n]
    field_simp
  filter_upwards [hwbound, W1p.value_sub_ae (W1p.restrictL hB u) (w : W1p mu B 2),
    W1p.value_restrictL_ae hB u] with x hx hxs hxr
  rw [hxs, Pi.sub_apply, hxr, sub_sub_cancel]
  refine hx.trans_eq ?_
  simp only [B, Opens.coe_mk, hmeas]
  ring

/-! ### Local boundedness -/

/-- If `|u - g| ≤ W` almost everywhere for a finite measure `ν`, then
`∫ g² ≤ 2 ∫ u² + 2 W² ν(univ)`, since `g² ≤ 2 u² + 2 (u - g)²`. -/
theorem integral_sq_le_two_mul_integral_sq_add {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {u g : α → ℝ} {W : ℝ} (hu : Integrable (fun x => u x ^ 2) ν)
    (h : ∀ᵐ x ∂ν, |u x - g x| ≤ W) :
    ∫ x, g x ^ 2 ∂ν ≤ 2 * ∫ x, u x ^ 2 ∂ν + 2 * W ^ 2 * ν.real Set.univ := by
  have hrhs : ∫ x, (2 * u x ^ 2 + 2 * W ^ 2) ∂ν =
      2 * ∫ x, u x ^ 2 ∂ν + 2 * W ^ 2 * ν.real Set.univ := by
    rw [integral_add (hu.const_mul 2) (integrable_const _), integral_const_mul, integral_const,
      smul_eq_mul]
    ring
  rw [← hrhs]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
    ((hu.const_mul 2).add (integrable_const _)) ?_
  filter_upwards [h] with x hx
  have habs : |u x - g x| ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
  rw [sq_abs] at habs
  nlinarith [sq_nonneg (u x + (u x - g x))]

/-- `√(2 A + 2 W² m) ≤ √2 √A + √2 W √m` for nonnegative `A`, `m`, `W`. -/
theorem sqrt_two_mul_add_two_mul_sq_mul_le {A W m : ℝ} (hA : 0 ≤ A) (hm : 0 ≤ m) (hW : 0 ≤ W) :
    √(2 * A + 2 * W ^ 2 * m) ≤ √2 * √A + √2 * W * √m := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h : (√2 * √A + √2 * W * √m) ^ 2 =
      2 * A + 2 * W ^ 2 * m + 4 * (√A * W * √m) := by
    have e : (√2 * √A + √2 * W * √m) ^ 2 =
        √2 ^ 2 * (√A ^ 2 + W ^ 2 * √m ^ 2 + 2 * (√A * W * √m)) := by ring
    rw [e, Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2), Real.sq_sqrt hA, Real.sq_sqrt hm]
    ring
  nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg A) hW) (Real.sqrt_nonneg m)]

omit [DecidableEq ι] in
/-- The square root of the measure of a ball of radius `R` is `R ^ (n / 2)` times that of the unit
ball. -/
theorem sqrt_measureReal_ball_eq (x : EuclideanSpace ℝ ι) {R : ℝ} (hR : 0 < R) :
    √(mu.real (ball x R)) =
      R ^ ((Fintype.card ι : ℝ) / 2) * √(mu.real (ball (0 : EuclideanSpace ℝ ι) 1)) := by
  rw [Measure.addHaar_real_ball_of_pos _ _ hR, finrank_euclideanSpace, ← Real.rpow_natCast,
    Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
  ring_nf

omit [DecidableEq ι] in
/-- If `|u - g| ≤ W` almost everywhere on a ball `B` of radius `R`, then
`‖g‖_{L²(B)} ≤ √2 ‖u‖_{L²(B)} + √2 W |B|^(1/2)`, where `|B|^(1/2) = R^(n/2) |B(0, 1)|^(1/2)`. -/
theorem sqrt_setIntegral_sq_le_of_ae_abs_sub_le (x₀ : EuclideanSpace ℝ ι) {R W : ℝ}
    {u g : EuclideanSpace ℝ ι → ℝ} (hR : 0 < R) (hW : 0 ≤ W)
    (hu : Integrable (fun x => u x ^ 2) (mu.restrict (ball x₀ R)))
    (h : ∀ᵐ x ∂mu.restrict (ball x₀ R), |u x - g x| ≤ W) :
    √(∫ x in ball x₀ R, g x ^ 2 ∂mu) ≤ √2 * √(∫ x in ball x₀ R, u x ^ 2 ∂mu) +
      √2 * W * √(mu.real (ball (0 : EuclideanSpace ℝ ι) 1)) * R ^ ((Fintype.card ι : ℝ) / 2) := by
  have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hg2 := integral_sq_le_two_mul_integral_sq_add hu h
  rw [measureReal_restrict_apply_univ] at hg2
  calc √(∫ x in ball x₀ R, g x ^ 2 ∂mu)
      ≤ √(2 * ∫ x in ball x₀ R, u x ^ 2 ∂mu + 2 * W ^ 2 * mu.real (ball x₀ R)) :=
        Real.sqrt_le_sqrt hg2
    _ ≤ √2 * √(∫ x in ball x₀ R, u x ^ 2 ∂mu) + √2 * W * √(mu.real (ball x₀ R)) :=
        sqrt_two_mul_add_two_mul_sq_mul_le (integral_nonneg fun _ => sq_nonneg _)
          measureReal_nonneg hW
    _ = _ := by rw [sqrt_measureReal_ball_eq x₀ hR]; ring

/-- **Local boundedness of weak solutions with a right-hand side.** Let `n ≥ 1` be the dimension
and let `r > 1` with `r > n/2`. There is `D > 0`, depending only on `λ`, `Λ`, `n`, `r` and the
normalization of `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ Lʳ(B(x₀, R))`. If `B(x₀, R) ⊆ Ω`, then almost everywhere on
`B(x₀, R/2)`

`|u| ≤ D (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + R^(2 - n/r) ‖f‖_{Lʳ(B(x₀, R))} / λ)`.

For `f = 0` this is `TauCeti.PDE.exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral`. -/
theorem exists_ae_abs_value_le_mul_add_of_memLp [Nonempty ι] {lam Lam : ℝ} {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤
        D * (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          R ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ R))).toReal / lam) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  obtain ⟨K, hK, hsplit⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le (mu := mu) hr hrn
  obtain ⟨D₀, hD₀, hbound⟩ :=
    exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := lam) (Lam := Lam)
  set ω := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hω : 0 < ω := Metric.measureReal_ball_pos mu 0 one_pos
  refine ⟨max (√2 * D₀) ((√2 * D₀ * √ω + 1) * K), lt_max_of_lt_left (by positivity), ?_⟩
  intro Omega a f u x₀ R h ha hf hu hR hball
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ R, isOpen_ball⟩
  obtain ⟨g, hg, hug⟩ := hsplit h ha hf hu hR hball
  set W := K * R ^ (2 - n / r) * (eLpNorm f r (mu.restrict (ball x₀ R))).toReal / lam
  have hW : 0 ≤ W := by have := h.pos; positivity
  -- De Giorgi's bound for the homogeneous part `g` on `B(x₀, R/2)`.
  have hgbound := hbound (Omega := B) (h.mono_set hball)
    (ha.mono_measure (Measure.restrict_mono hball le_rfl)) hg hR (subset_refl _)
  -- `‖g‖_{L²(B)} ≤ √2 ‖u‖_{L²(B)} + √2 W |B|^(1/2)`.
  have hsqrt := sqrt_setIntegral_sq_le_of_ae_abs_sub_le (mu := mu) x₀ hR hW
    (((Lp.memLp (W1p.value u)).integrable_sq).mono_measure (Measure.restrict_mono hball le_rfl))
    (hug.mono fun x hx => hx)
  -- Combine: `|u| ≤ |g| + W`.
  have hR' : R ^ (-n / 2) * R ^ (n / 2) = 1 := by
    rw [← Real.rpow_add hR, neg_div, neg_add_cancel, Real.rpow_zero]
  filter_upwards [hgbound, ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (half_le_self hR.le)) hug] with x hx hxu
  set Q := R ^ (-n / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)
  set P := R ^ (2 - n / r) * (eLpNorm f r (mu.restrict (ball x₀ R))).toReal / lam
  have hQ : 0 ≤ Q := by positivity
  have hP : 0 ≤ P := by have := h.pos; positivity
  have hWP : W = K * P := by simp only [W, P]; ring
  calc |W1p.value u x| ≤ |W1p.value g x| + |W1p.value u x - W1p.value g x| := by
        simpa using abs_add_le (W1p.value g x) (W1p.value u x - W1p.value g x)
    _ ≤ D₀ * R ^ (-n / 2) * √(∫ x in ball x₀ R, W1p.value g x ^ 2 ∂mu) + W := add_le_add hx hxu
    _ ≤ D₀ * R ^ (-n / 2) * (√2 * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          √2 * W * √ω * R ^ (n / 2)) + W := by gcongr
    _ = √2 * D₀ * Q + (√2 * D₀ * √ω + 1) * K * P := by
        rw [hWP]
        linear_combination (√2 * D₀ * K * P * √ω) * hR'
    _ ≤ max (√2 * D₀) ((√2 * D₀ * √ω + 1) * K) * Q +
          max (√2 * D₀) ((√2 * D₀ * √ω + 1) * K) * P := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = _ := by ring

/-! ### Oscillation decay -/

/-- **One step of oscillation decay with a right-hand side.** Let `n ≥ 1` be the dimension and
let `r > 1` with `r > n/2`. There are `α ∈ (0, 1]` and `C, K > 0`, depending only on `λ`, `Λ`,
`n`, `r` and the normalization of `mu`, such that the following holds. Let `a` be measurable and
uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ Lʳ(B(x₀, ρ))`. If `B(x₀, ρ) ⊆ Ω`, `u` is essentially bounded on
`B(x₀, ρ)` and `0 < s ≤ ρ`, then the essential oscillations `osc_s` and `osc_ρ` of `u` on
`B(x₀, s)` and `B(x₀, ρ)` satisfy

`osc_s ≤ C (s/ρ)^α osc_ρ + K ρ^(2 - n/r) ‖f‖_{Lʳ(B(x₀, ρ))} / λ`.

For `f = 0` this is the oscillation decay
`TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_sub` of the homogeneous equation. -/
theorem exists_essSup_sub_essInf_le_mul_rpow_mul_add_of_memLp [Nonempty ι] {lam Lam : ℝ}
    {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ α C K : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {ρ s M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ ρ)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < s → s ≤ ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x| ≤ M) →
      essSup (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ s)) -
          essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ s)) ≤
        C * (s / ρ) ^ α *
            (essSup (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ ρ)) -
              essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ ρ))) +
          K * ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam := by
  obtain ⟨α₀, C₀, hα₀, hα₀1, hC₀, hpow⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_sub (mu := mu) (lam := lam) (Lam := Lam)
  obtain ⟨K, hK, hsplit⟩ := exists_forall_energyFormH1_eq_zero_ae_abs_sub_le (mu := mu) hr hrn
  refine ⟨α₀, C₀, (2 * C₀ + 2) * K, hα₀, hα₀1, hC₀, by positivity, ?_⟩
  intro Omega a f u x₀ ρ s M h ha hf hu hs hsρ hball hM
  have hρ : 0 < ρ := hs.trans_le hsρ
  have : (ae (mu.restrict (ball x₀ s))).NeBot :=
    ae_restrict_neBot.2 (measure_ball_pos mu x₀ hs).ne'
  -- The homogeneous part `g` of `u` on `B(x₀, ρ)`, with `|u - g| ≤ W`.
  obtain ⟨g, hg, hug⟩ := hsplit h ha hf hu hρ hball
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = K * ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
      (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam := ⟨_, rfl⟩
  rw [← hWdef] at hug
  have hW0 : 0 ≤ W := by rw [hWdef]; have := h.pos; positivity
  set m := essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ ρ))
  set m₁ := essSup (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ ρ))
  -- `g` lies in `[m - W, m₁ + W]` on `B(x₀, ρ)`.
  have hgI : ∀ᵐ x ∂mu.restrict (ball x₀ ρ), W1p.value g x ∈ Icc (m - W) (m₁ + W) := by
    filter_upwards [ae_le_essSup (isBoundedUnder_of_eventually_le (a := M)
        (hM.mono fun _ hx => (abs_le.1 hx).2)),
      ae_essInf_le (isBoundedUnder_of_eventually_ge (a := -M)
        (hM.mono fun _ hx => (abs_le.1 hx).1)), hug] with x hx₁ hx₂ hxg
    rw [abs_le] at hxg
    exact ⟨by linarith only [hx₂, hxg.2], by linarith only [hx₁, hxg.1]⟩
  obtain ⟨m', hm'⟩ := hpow (Omega := ⟨ball x₀ ρ, isOpen_ball⟩) (h.mono_set hball)
    (ha.mono_measure (Measure.restrict_mono hball le_rfl)) hg hs hsρ (subset_refl _) hgI
  -- Hence `u` lies in an interval of length `C₀ (s/ρ)^α₀ (m₁ - m + 2W) + 2W` on `B(x₀, s)`.
  have hosc := essSup_sub_essInf_le (f := (W1p.value u : EuclideanSpace ℝ ι → ℝ))
    (ν := mu.restrict (ball x₀ s)) (m := m' - W)
    (L := C₀ * (s / ρ) ^ α₀ * (m₁ + W - (m - W)) + 2 * W) <| by
    filter_upwards [hm', ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hsρ) hug]
      with x hx hxg
    rw [abs_le] at hxg
    exact ⟨by linarith only [hx.1, hxg.1], by linarith only [hx.2, hxg.2]⟩
  have hsρ1 : C₀ * (s / ρ) ^ α₀ ≤ C₀ :=
    mul_le_of_le_one_right hC₀.le
      (Real.rpow_le_one (by positivity) ((div_le_one hρ).2 hsρ) hα₀.le)
  have hC₀s : 0 ≤ C₀ * (s / ρ) ^ α₀ := by positivity
  calc _ ≤ C₀ * (s / ρ) ^ α₀ * (m₁ + W - (m - W)) + 2 * W := hosc
    _ = C₀ * (s / ρ) ^ α₀ * (m₁ - m) + (2 * (C₀ * (s / ρ) ^ α₀) + 2) * W := by ring
    _ ≤ C₀ * (s / ρ) ^ α₀ * (m₁ - m) + (2 * C₀ + 2) * W := by gcongr
    _ = _ := by rw [hWdef]; ring

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- If `|v| ≤ M` almost everywhere on a ball, `v` is essentially bounded on it. -/
theorem isBoundedUnder_ae_restrict_ball_of_ae_abs_le (x₀ : EuclideanSpace ℝ ι) {ρ M : ℝ}
    {v : EuclideanSpace ℝ ι → ℝ} (h : ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |v x| ≤ M) :
    IsBoundedUnder (· ≤ ·) (ae (mu.restrict (ball x₀ ρ))) v ∧
      IsBoundedUnder (· ≥ ·) (ae (mu.restrict (ball x₀ ρ))) v :=
  ⟨isBoundedUnder_of_eventually_le (a := M) (h.mono fun _ hx => (abs_le.1 hx).2),
    isBoundedUnder_of_eventually_ge (a := -M) (h.mono fun _ hx => (abs_le.1 hx).1)⟩

omit [DecidableEq ι] in
/-- The essential oscillation `φ ρ` of a function `v` on `B(x₀, ρ)` is nonnegative and monotone in
`ρ ∈ (0, R₁]`, and at most `2 M` at `R₁`, if `|v| ≤ M` almost everywhere on `B(x₀, R₁)`. -/
theorem essSup_sub_essInf_nonneg_monotoneOn (x₀ : EuclideanSpace ℝ ι) {R₁ M : ℝ}
    {v : EuclideanSpace ℝ ι → ℝ} {φ : ℝ → ℝ}
    (hφ : ∀ ρ, φ ρ = essSup v (mu.restrict (ball x₀ ρ)) - essInf v (mu.restrict (ball x₀ ρ)))
    (hR₁ : 0 < R₁) (hM : ∀ᵐ x ∂mu.restrict (ball x₀ R₁), |v x| ≤ M) :
    (∀ ρ ∈ Ioc 0 R₁, 0 ≤ φ ρ) ∧ MonotoneOn φ (Ioc 0 R₁) ∧ φ R₁ ≤ 2 * M := by
  have hbdd : ∀ ρ ≤ R₁, _ ∧ _ := fun ρ hρ => isBoundedUnder_ae_restrict_ball_of_ae_abs_le (mu := mu)
    x₀ (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρ) hM)
  have hne : ∀ ρ, 0 < ρ → (ae (mu.restrict (ball x₀ ρ))).NeBot := fun ρ hρ =>
    ae_restrict_neBot.2 (measure_ball_pos mu x₀ hρ).ne'
  refine ⟨fun ρ hρ => ?_, fun ρ hρ ρ' hρ' hρρ' => ?_, ?_⟩
  · have := hne ρ hρ.1
    rw [hφ]
    exact sub_nonneg.2 (liminf_le_limsup (hbdd ρ hρ.2).1 (hbdd ρ hρ.2).2)
  · have := hne ρ hρ.1
    rw [hφ, hφ]
    exact essSup_sub_essInf_mono_measure (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (ball_subset_ball hρρ') le_rfl)) (hbdd ρ' hρ'.2).1 (hbdd ρ' hρ'.2).2
  · have := hne R₁ hR₁
    rw [hφ]
    refine essSup_sub_essInf_le (m := -M) ?_
    filter_upwards [hM] with x hx
    rw [abs_le] at hx
    exact ⟨hx.1, by linarith only [hx.2]⟩

/-- The `Lᵖ` norm on a smaller set is at most the `Lᵖ` norm on a larger one, divided by `λ ≥ 0`. -/
theorem toReal_eLpNorm_restrict_div_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {p : ℝ≥0∞} {s t : Set α} (hst : s ⊆ t) (hf : MemLp f p (μ.restrict t)) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    (eLpNorm f p (μ.restrict s)).toReal / lam ≤ (eLpNorm f p (μ.restrict t)).toReal / lam :=
  div_le_div_of_nonneg_right (ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono hst le_rfl))) hlam

/-- `ρ ^ γ ≤ R₁ ^ (γ - β) ρ ^ β` for `0 < ρ ≤ R₁` and `β ≤ γ`. -/
theorem rpow_le_rpow_sub_mul_rpow {ρ R₁ β γ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R₁) (hβγ : β ≤ γ) :
    ρ ^ γ ≤ R₁ ^ (γ - β) * ρ ^ β :=
  calc ρ ^ γ = ρ ^ (γ - β) * ρ ^ β := by rw [← Real.rpow_add hρ, sub_add_cancel]
    _ ≤ R₁ ^ (γ - β) * ρ ^ β := by gcongr

/-- The real-number bookkeeping at the end of the proof of the interior oscillation estimate: from
the iterated bound `φ s ≤ C₁ ((s / R₁)^β φ R₁ + B s^β)` and `φ R₁ ≤ 2 M₀`, with `R₁ = R / 2`,
`M₀ = D (Q + R^γ F)` and `B = K F R₁^(γ - β)`, one gets
`φ s ≤ C₁ 2^β (2 D + K) (s / R)^β (Q + R^γ F)`. -/
theorem oscillation_decay_bound_aux {C₁ K D β γ s R R₁ F Q M₀ B φs φR₁ : ℝ} (hs : 0 < s)
    (hR : 0 < R) (hR₁def : R₁ = R / 2) (hγ : 0 < γ) (hK : 0 ≤ K) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hQ : 0 ≤ Q) (hC₁ : 0 ≤ C₁) (hfin : φs ≤ C₁ * ((s / R₁) ^ β * φR₁ + B * s ^ β))
    (hφR₁ : φR₁ ≤ 2 * M₀) (hM₀def : M₀ = D * (Q + R ^ γ * F)) (hBdef : B = K * F * R₁ ^ (γ - β)) :
    φs ≤ C₁ * 2 ^ β * (2 * D + K) * (s / R) ^ β * (Q + R ^ γ * F) := by
  have hR₁ : 0 < R₁ := hR₁def ▸ half_pos hR
  have hsβ : B * s ^ β = K * F * R₁ ^ γ * (s / R₁) ^ β := by
    rw [hBdef, Real.div_rpow hs.le hR₁.le, Real.rpow_sub hR₁]
    field_simp
  have hR₁γ : R₁ ^ γ ≤ R ^ γ := Real.rpow_le_rpow hR₁.le (hR₁def ▸ half_le_self hR.le) hγ.le
  have hsR₁ : (s / R₁) ^ β = 2 ^ β * (s / R) ^ β := by
    rw [← Real.mul_rpow (by norm_num) (by positivity), hR₁def]
    congr 1
    field_simp
  have hM₀ : 0 ≤ M₀ := by rw [hM₀def]; positivity
  calc φs ≤ C₁ * ((s / R₁) ^ β * φR₁ + B * s ^ β) := hfin
    _ ≤ C₁ * ((s / R₁) ^ β * (2 * M₀) + K * F * R ^ γ * (s / R₁) ^ β) := by
        rw [hsβ]
        gcongr
    _ = C₁ * 2 ^ β * (s / R) ^ β * (2 * D * (Q + R ^ γ * F) + K * (R ^ γ * F)) := by
        rw [hsR₁, hM₀def]
        ring
    _ ≤ C₁ * 2 ^ β * (s / R) ^ β * ((2 * D + K) * (Q + R ^ γ * F)) := by
        gcongr
        nlinarith only [mul_nonneg hK hQ]
    _ = _ := by ring

/-- The iteration step of the interior oscillation estimate, as a statement about the essential
oscillation `φ` alone. If `φ s ≤ C₀ (s/ρ)^α₀ φ ρ + K ρ^γ F` for `s ≤ ρ ≤ R / 2`, with `φ`
nonnegative and monotone on `(0, R/2]` and `φ (R / 2) ≤ 2 D (Q + R^γ F)`, then
`φ s ≤ C (s / R)^β (Q + R^γ F)` for `s ≤ R / 2`, where `β < α₀` and `C` depend only on
`α₀`, `C₀`, `K`, `D` and `γ`. -/
theorem exists_le_mul_rpow_of_essOsc_step {α₀ C₀ K D γ : ℝ} (hα₀ : 0 < α₀) (hC₀ : 0 < C₀)
    (hK : 0 < K) (hD : 0 < D) (hγ : 0 < γ) :
    ∃ β C : ℝ, 0 < β ∧ β < α₀ ∧ 0 < C ∧ ∀ {φ : ℝ → ℝ} {R s Q F M₀ : ℝ}, 0 < s → s ≤ R / 2 →
      0 ≤ Q → 0 ≤ F → MonotoneOn φ (Ioc 0 (R / 2)) → (∀ ρ ∈ Ioc 0 (R / 2), 0 ≤ φ ρ) →
      φ (R / 2) ≤ 2 * M₀ → M₀ = D * (Q + R ^ γ * F) →
      (∀ s ρ, 0 < s → s ≤ ρ → ρ ≤ R / 2 → φ s ≤ C₀ * ((s / ρ) ^ α₀ + 0) * φ ρ + K * ρ ^ γ * F) →
      φ s ≤ C * (s / R) ^ β * (Q + R ^ γ * F) := by
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = min γ (α₀ / 2) := ⟨_, rfl⟩
  have hβ : 0 < β := hβdef ▸ lt_min hγ (half_pos hα₀)
  have hβγ : β ≤ γ := hβdef ▸ min_le_left _ _
  have hβα : β < α₀ := hβdef ▸ (min_le_right _ _).trans_lt (half_lt_self hα₀)
  obtain ⟨ε₀, C₁, hε₀, hC₁, hiter⟩ :=
    exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add hC₀.le hβα hβα
  refine ⟨β, C₁ * 2 ^ β * (2 * D + K), hβ, hβα, by positivity, ?_⟩
  intro φ R s Q F M₀ hs hsR hQ hF hmono hφ0 hφR₁ hM₀def hstep
  have hR : 0 < R := by linarith only [hs, hsR]
  have hB : 0 ≤ K * F * (R / 2) ^ (γ - β) := by positivity
  have hfin := hiter hB hε₀.le hmono hφ0 (fun s ρ hs hsρ hρ => (hstep s ρ hs hsρ hρ).trans <| by
      have := rpow_le_rpow_sub_mul_rpow (hs.trans_le hsρ) hρ hβγ
      have := hs.trans_le hsρ
      calc _ ≤ C₀ * ((s / ρ) ^ α₀ + 0) * φ ρ + K * ((R / 2) ^ (γ - β) * ρ ^ β) * F := by gcongr
        _ = _ := by ring) s (R / 2) hs hsR le_rfl
  exact oscillation_decay_bound_aux hs hR rfl hγ hK.le hD.le hF hQ hC₁.le hfin hφR₁ hM₀def rfl

/-- **De Giorgi's interior oscillation estimate with a right-hand side.** Let `n ≥ 1` be the
dimension and let `r > 1` with `r > n/2`. There are `α ∈ (0, 1]` and `C > 0`, depending only on
`λ`, `Λ`, `n`, `r` and the normalization of `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ Lʳ(B(x₀, R))`. If `B(x₀, R) ⊆ Ω` and `0 < s ≤ R/2`,
then almost everywhere on `B(x₀, s)` the function `u` takes values in an interval of length

`C (s / R)^α (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + R^(2 - n/r) ‖f‖_{Lʳ(B(x₀, R))} / λ)`.

For `f = 0` this is the form of
`TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_rpow_mul_sqrt_setIntegral`. -/
theorem exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_memLp [Nonempty ι] {lam Lam : ℝ}
    {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R s : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < s → s ≤ R / 2 → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ m' : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ s), W1p.value u x ∈ Icc m' (m' + C * (s / R) ^ α *
        (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          R ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ R))).toReal / lam)) := by
  obtain ⟨α₀, C₀, K, hα₀, hα₀1, hC₀, hK, hosc⟩ :=
    exists_essSup_sub_essInf_le_mul_rpow_mul_add_of_memLp (mu := mu) (lam := lam) (Lam := Lam)
      hr hrn
  obtain ⟨D, hD, hloc⟩ :=
    exists_ae_abs_value_le_mul_add_of_memLp (mu := mu) (lam := lam) (Lam := Lam) hr hrn
  -- The exponent `γ = 2 - n/r` of the right-hand side term.
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = 2 - (Fintype.card ι : ℝ) / r := ⟨_, rfl⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast zero_lt_one.trans hr
  have hγ : 0 < γ := hγdef ▸ sub_pos.2 ((div_lt_iff₀ hr0).2 (by linarith only [hrn]))
  obtain ⟨β, C, hβ, hβα, hC, hiter⟩ := exists_le_mul_rpow_of_essOsc_step hα₀ hC₀ hK hD hγ
  refine ⟨β, C, hβ, hβα.le.trans hα₀1, hC, ?_⟩
  intro Omega a f u x₀ R s h ha hf hu hs hsR hball
  rw [← hγdef]
  have hR : 0 < R := by linarith only [hs, hsR]
  have hlam := h.pos
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ, F = (eLpNorm f r (mu.restrict (ball x₀ R))).toReal / lam :=
    ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
      Q = R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) :=
    ⟨_, rfl⟩
  -- Local boundedness: `|u| ≤ M₀` on `B(x₀, R/2)`.
  obtain ⟨M₀, hM₀def⟩ : ∃ M₀ : ℝ, M₀ = D * (Q + R ^ γ * F) := ⟨_, rfl⟩
  have hM : ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤ M₀ := by
    filter_upwards [hloc h ha hf hu hR hball] with x hx
    exact hx.trans_eq (by rw [hM₀def, hQdef, hFdef, hγdef]; ring)
  -- The essential oscillation `φ ρ` of `u` on `B(x₀, ρ)`.
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℝ → ℝ, φ = fun ρ => essSup (W1p.value u : EuclideanSpace ℝ ι → ℝ)
      (mu.restrict (ball x₀ ρ)) - essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ)
        (mu.restrict (ball x₀ ρ)) := ⟨_, rfl⟩
  have hMρ : ∀ ρ, ρ ≤ R / 2 → ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x| ≤ M₀ :=
    fun ρ hρ => ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρ) hM
  obtain ⟨hφ0, hmono, hφR₁⟩ := essSup_sub_essInf_nonneg_monotoneOn (mu := mu) x₀ (φ := φ)
    (fun ρ => by rw [hφdef]) (half_pos hR) hM
  -- One comparison step: `φ s ≤ C₀ (s/ρ)^α₀ φ ρ + K ρ^γ F` for `s ≤ ρ ≤ R / 2`.
  have hstep : ∀ s ρ, 0 < s → s ≤ ρ → ρ ≤ R / 2 →
      φ s ≤ C₀ * ((s / ρ) ^ α₀ + 0) * φ ρ + K * ρ ^ γ * F := by
    intro s ρ hs hsρ hρR₁
    have hρ : 0 < ρ := hs.trans_le hsρ
    have hρR : ball x₀ ρ ⊆ ball x₀ R := ball_subset_ball (hρR₁.trans (half_le_self hR.le))
    have hfρ := hFdef ▸ toReal_eLpNorm_restrict_div_le hρR hf hlam.le
    calc φ s ≤ C₀ * ((s / ρ) ^ α₀ + 0) * φ ρ +
          K * ρ ^ γ * ((eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam) := by
          simpa only [hφdef, hγdef, add_zero, mul_div_assoc] using
            hosc h ha (hf.mono_measure (Measure.restrict_mono hρR le_rfl)) hu hs hsρ
              (hρR.trans hball) (hMρ ρ hρR₁)
      _ ≤ _ := by gcongr
  have hφs := hiter hs hsR (by rw [hQdef]; positivity) (by rw [hFdef]; positivity) hmono hφ0 hφR₁
    hM₀def hstep
  obtain ⟨hb₁, hb₂⟩ := isBoundedUnder_ae_restrict_ball_of_ae_abs_le (mu := mu) x₀ (hMρ s hsR)
  rw [← hQdef, mul_div_assoc, ← hFdef]
  rw [hφdef] at hφs
  refine ⟨essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ s)), ?_⟩
  filter_upwards [ae_le_essSup hb₁, ae_essInf_le hb₂] with x hx₁ hx₂
  exact ⟨hx₂, by linarith only [hφs, hx₁]⟩

/-! ### Hölder continuity -/

/-- If `y ∈ [m, m + L]` and `L ≤ 2 c`, then `y` lies in the closed ball of radius `c` about
`m + c`. -/
theorem mem_closedBall_of_mem_Icc_of_le {y m L c : ℝ} (hy : y ∈ Icc m (m + L)) (hL : L ≤ 2 * c) :
    y ∈ closedBall (m + c) c := by
  rw [mem_closedBall, Real.dist_eq, abs_le]
  constructor <;> linarith [hy.1, hy.2]

/-- Scaling the oscillation bound: if `X ≤ N` and `C = C₀ N / R^α / 2`, then
`C₀ (s / R)^α X ≤ 2 (C s^α)`. -/
theorem mul_div_rpow_mul_le_two_mul_aux {C₀ C N X R s α : ℝ} (hs : 0 < s) (hR : 0 < R)
    (hC₀ : 0 < C₀) (hX : X ≤ N) (hC : C = C₀ * N / R ^ α / 2) :
    C₀ * (s / R) ^ α * X ≤ 2 * (C * s ^ α) :=
  calc _ ≤ C₀ * (s / R) ^ α * N := by gcongr
    _ = 2 * (C * s ^ α) := by rw [hC, Real.div_rpow hs.le hR.le]; field_simp

/-- The constants in Hölder continuity: `2 C = C₀ N R^(-α)` and
`2 M / ρ^α = 2^(1+α) D N R^(-α) ≤ 4 D N R^(-α)` for `α ≤ 1`. -/
theorem max_two_mul_div_rpow_le {C₀ D N R α : ℝ} (hα : α ≤ 1) (hR : 0 < R) (hD : 0 ≤ D)
    (hN : 0 ≤ N) :
    max (2 * (C₀ * N / R ^ α / 2)) (2 * (D * N) / (R ^ α / 2 ^ α)) ≤
      max C₀ (4 * D) * (R ^ α)⁻¹ * N := by
  have h2α : (2 : ℝ) ^ α ≤ 2 := by simpa using Real.rpow_le_rpow_of_exponent_le one_le_two hα
  refine max_le ?_ ?_
  · calc 2 * (C₀ * N / R ^ α / 2) = C₀ * (R ^ α)⁻¹ * N := by field_simp
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · calc 2 * (D * N) / (R ^ α / 2 ^ α) = 2 * 2 ^ α * D * (R ^ α)⁻¹ * N := by field_simp
      _ ≤ 2 * 2 * D * (R ^ α)⁻¹ * N := by gcongr
      _ ≤ _ := by
        rw [show (2 : ℝ) * 2 * D = 4 * D by ring]
        gcongr
        exact le_max_right _ _

omit [DecidableEq ι] in
/-- A function in `H¹(Ω)` is integrable near every point of `Ω`. -/
theorem integrableAtFilter_value_of_mem {Omega : Opens (EuclideanSpace ℝ ι)} (u : W1p mu Omega 2)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι))) :
    IntegrableAtFilter (W1p.value u) (𝓝 x) mu := by
  simpa [nhdsWithin_eq_nhds.2 (Omega.isOpen.mem_nhds hx)] using
    (W1p.hasWeakFDerivOn u).locallyIntegrableOn x hx

omit [DecidableEq ι] in
/-- The scaled norms `R^(-n/2) ‖u‖_{L²} + R^(2 - n/r) ‖f‖_{Lʳ} / λ` of `u` and `f` on a ball
inside `Ω` are at most those on `Ω`. -/
theorem scaled_norm_ball_le {Omega : Opens (EuclideanSpace ℝ ι)} {f : EuclideanSpace ℝ ι → ℝ}
    {u : W1p mu Omega 2} {lam R : ℝ} {r : ℝ≥0} {x : EuclideanSpace ℝ ι} (hlam : 0 < lam)
    (hR : 0 ≤ R) (hf : MemLp f r (mu.restrict Omega))
    (hball : ball x R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in ball x R, W1p.value u y ^ 2 ∂mu) +
        R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict (ball x R))).toReal / lam ≤
      R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
        R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict Omega)).toReal / lam := by
  gcongr
  · exact ae_of_all _ fun y => sq_nonneg _
  · exact (Lp.memLp (W1p.value u)).integrable_sq
  · exact hf.eLpNorm_ne_top

/-- **De Giorgi's theorem with a right-hand side.** Let `n ≥ 1` be the dimension and let `r > 1`
with `r > n/2`. There are `α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `n`, `r` and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `f ∈ Lʳ(Ω)`, and let
`u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is `a(u, v) = ∫_Ω f v` for every
`v ∈ H¹₀(Ω)`. If the closed `R`-thickening of a set `K` lies in `Ω`, then the precise
representative of `u` is Hölder continuous on `K` with exponent `α` and constant

`C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + R^(2 - n/r) ‖f‖_{Lʳ(Ω)} / λ)`.

The precise representative agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`). No regularity of the coefficients beyond
measurability is assumed. -/
theorem exists_holderOnWith_preciseRepresentative_of_memLp [Nonempty ι] {lam Lam : ℝ}
    {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            R ^ (2 - (Fintype.card ι : ℝ) / r) *
              (eLpNorm f r (mu.restrict Omega)).toReal / lam)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨α, C₀, hα, hα1, hC₀, hosc⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_memLp (mu := mu) (lam := lam)
      (Lam := Lam) hr hrn
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_add_of_memLp (mu := mu) (lam := lam) (Lam := Lam) hr hrn
  lift α to ℝ≥0 using hα.le
  refine ⟨α, max C₀ (4 * D), NNReal.coe_pos.1 hα, NNReal.coe_le_one.1 hα1,
    lt_max_of_lt_left hC₀, ?_⟩
  intro Omega a f u K R h ha hf hu hR hRK
  have hlam := h.pos
  have hKΩ : K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := (self_subset_cthickening K).trans hRK
  -- Every ball of radius `R` centred in `K` lies in `Ω`.
  have hball : ∀ x ∈ K, ball x R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := fun x hx =>
    (ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK)
  -- The scaled norms of `u` and `f` on such a ball are at most `N`, their scaled norms on `Ω`.
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N =
      R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
        R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict Omega)).toReal / lam :=
    ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hN := fun x (hx : x ∈ K) =>
    (scaled_norm_ball_le (mu := mu) (u := u) hlam hR.le hf (hball x hx)).trans_eq hNdef.symm
  have hfx : ∀ x ∈ K, MemLp f r (mu.restrict (ball x R)) := fun x hx =>
    hf.mono_measure (Measure.restrict_mono (hball x hx) le_rfl)
  have hint : ∀ x ∈ K, IntegrableAtFilter (W1p.value u) (𝓝 x) mu := fun x hx =>
    integrableAtFilter_value_of_mem u (hKΩ hx)
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, (C : ℝ) = C₀ * N / R ^ (α : ℝ) / 2 := ⟨⟨_, by positivity⟩, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ≥0, (M : ℝ) = D * N := ⟨⟨_, by positivity⟩, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ) = R / 2 := ⟨⟨_, by positivity⟩, rfl⟩
  refine (holderOnWith_preciseRepresentative (C := C) (M := M) (ρ := ρ)
    (NNReal.coe_pos.1 hα) (NNReal.coe_pos.1 (hρ ▸ half_pos hR)) hint
    (fun x hx s hs hsR => ?_) (fun x hx => ?_)).mono_const ?_
  · -- Oscillation: `u` lies in an interval of length `L ≤ 2 C s^α` on `B(x, s)`.
    rw [hρ] at hsR
    obtain ⟨m', hm'⟩ := hosc h ha (hfx x hx) hu hs hsR (hball x hx)
    have hL := mul_div_rpow_mul_le_two_mul_aux hs hR hC₀ (hN x hx) hC
    refine ⟨m' + C * s ^ (α : ℝ), ?_⟩
    filter_upwards [hm'] with y hy
    exact mem_closedBall_of_mem_Icc_of_le hy hL
  · -- Boundedness: `|u| ≤ D N` on `B(x, R/2)`, by local boundedness.
    rw [hρ]
    filter_upwards [hbound h ha (hfx x hx) hu hR (hball x hx)] with y hy
    rw [Real.norm_eq_abs, hM]
    exact hy.trans (mul_le_mul_of_nonneg_left (hN x hx) hD.le)
  · -- The constant: `2 C = C₀ N R^(-α)` and `2 M / ρ^α = 2^(1+α) D N R^(-α) ≤ 4 D N R^(-α)`.
    rw [← hNdef, Real.le_toNNReal_iff_coe_le (by positivity)]
    push_cast
    rw [hC, hM, hρ, Real.div_rpow hR.le zero_le_two, Real.rpow_neg hR.le]
    exact max_two_mul_div_rpow_le hα1 hR hD.le hN0

end PDE

end TauCeti
