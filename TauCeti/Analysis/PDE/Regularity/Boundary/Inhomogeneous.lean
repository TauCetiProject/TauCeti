/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.Oscillation
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness
import TauCeti.Analysis.Sobolev.FiniteMeasure
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# De Giorgi's oscillation decay at the boundary with a right-hand side

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants
`0 < λ ≤ Λ`, let `r > 1` with `r > n/2`, and let `u ∈ H¹(Ω)` be a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` in `Ω`, `u ≤ 0` on `∂Ω`,

that is `a(u, v) ≤ ∫_Ω f v` for every nonnegative `v ∈ H¹₀(Ω)`, and `u⁺ ∈ H¹₀(Ω)`. This file
extends De Giorgi's boundary estimates of `TauCeti.Analysis.PDE.Regularity.Boundary.Oscillation`
from `f = 0` to a right-hand side `f ∈ Lʳ`. Nothing is assumed about the regularity of `∂Ω`
beyond an exterior measure density condition at the boundary point `x₀`: the complement of `Ω`
fills a fixed proportion `θ > 0` of the ball `B(x₀, ρ)`.

* **Reduction of the supremum**
  (`TauCeti.PDE.exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff`): if
  `u ≤ M` on `Ω ∩ B(x₀, 2R)` and `θ |B(x₀, R)| ≤ |B(x₀, R) \ Ω|`, then on `Ω ∩ B(x₀, R/2)`

  `u ≤ (1 - δ) M + K R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, 2R))} / λ`.

* **Geometric decay**
  (`TauCeti.PDE.exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`): if
  `u ≤ M` on `Ω ∩ B(x₀, R)` and the density condition holds for every radius up to `R`, then for
  every `j`, on `Ω ∩ B(x₀, R / 4ʲ)`

  `u ≤ τʲ (M + D R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, R))} / λ)`.

  For a weak solution `u ∈ H¹₀(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, both `u` and `-u` are such subsolutions,
  so `|u|` decays in the same way towards boundary points
  (`TauCeti.PDE.exists_ae_abs_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`).

The constants `δ, τ ∈ (0, 1)` and `D` depend only on `λ`, `Λ`, `θ`, `n`, `r` and the
normalization of the Haar measure, and `K` only on `n`, `r` and that normalization. The datum
enters with the Morrey gain `2 - n/r > 0` of its exponent, which is what makes these estimates
scale like those for the homogeneous equation. They are the boundary counterpart of the interior
estimate `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp`, and the boundary input
for the global Hölder continuity of weak solutions of the Dirichlet problem
`-∂ᵢ(aⁱʲ ∂ⱼu) = f`, `u ∈ H¹₀(Ω)`, on domains with exterior measure density.

## The argument

Extending `a` by `λ I` off `Ω`, the zero extension `ū` of `u⁺` is a weak subsolution of
`-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ g` on the whole space, with `g = 1_Ω f⁺`
(`TauCeti.PDE.exists_uniformlyEllipticOn_top_extendByZeroL_posPart`), and `ū` vanishes on
`B(x₀, R) \ Ω`. The right-hand side is split off on the ball `B = B(x₀, 2R)`, as in the interior
estimates of `TauCeti.Analysis.PDE.Regularity.Inhomogeneous`. The Dirichlet problem
`-∂ᵢ(a'ⁱʲ ∂ⱼw) = g` in `B`, `w ∈ H¹₀(B)`, has a solution
(`TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp`), and
Stampacchia's estimate `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow` bounds it by
`ε = C R^(2 - n/r) ‖g‖_{Lʳ(B)} / λ`. The difference `h = ū - w` is a weak subsolution of the
homogeneous equation on `B`, with `h ≤ M + ε` on `B` and `h ≤ ε` on `B(x₀, R) \ Ω`. De Giorgi's
interior reduction of the supremum (`TauCeti.PDE.exists_ae_value_le_sub_mul_sub`) at the level
`ε` gives `h ≤ (1 - δ) M + ε` on `B(x₀, R/2)`, hence `u⁺ = h + w ≤ (1 - δ) M + 2 ε` there.

The iteration along the radii `R / 4ʲ` absorbs the right-hand side into the geometric factor:
with `τ = max (1 - δ/2) 4^(-(2 - n/r))` and `A = M + (2/δ) K R^(2 - n/r) ‖f‖ / λ`, one has
`(1 - δ) τʲ A + τʲ K R^(2 - n/r) ‖f‖ / λ ≤ τʲ⁺¹ A`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.25, 8.27 and 8.29.
* G. Stampacchia, *Le problème de Dirichlet pour les équations elliptiques du second ordre à
  coefficients discontinus*, Ann. Inst. Fourier (Grenoble) 15 (1965), 189–258.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

omit [DecidableEq ι] in
/-- The homogeneous part of a whole-space subsolution. Let `ū` be a weak subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼū) ≤ g` on the whole space, and let `w ∈ H¹₀(B)` solve `-∂ᵢ(aⁱʲ ∂ⱼw) = g` on an open
set `B` of finite measure, where `g ∈ Lʳ(B)`. Then `ū|_B - w` is a weak subsolution of the
homogeneous equation on `B`. -/
private theorem energyFormH1_restrictL_sub_nonpos [Nonempty ι] {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) * (2 - r) < 2 * r) {B : Opens (EuclideanSpace ℝ ι)}
    (hBfin : mu B ≠ ∞) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {g : EuclideanSpace ℝ ι → ℝ}
    {ub : W1p mu ⊤ 2}
    (hcoeff : MemLp (fun x => energyIntegrand (a x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict B))
    (hsub : ∀ v : W1p0 mu ⊤ 2,
      (∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
        0 ≤ W1p.value (v : W1p mu ⊤ 2) x) →
      Integrable (fun x => g x * W1p.value (v : W1p mu ⊤ 2) x)
        (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) →
      energyFormH1 a 0 0 ub (v : W1p mu ⊤ 2) ≤
        ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          g x * W1p.value (v : W1p mu ⊤ 2) x ∂mu)
    (hg : MemLp g r (mu.restrict B)) {w : W1p0 mu B 2}
    (hw : ∀ v : W1p0 mu B 2, energyFormH1 a 0 0 (w : W1p mu B 2) (v : W1p mu B 2) =
      ∫ x in B, g x * W1p.value (v : W1p mu B 2) x ∂mu)
    (v : W1p0 mu B 2) (hv : ∀ᵐ x ∂mu.restrict B, 0 ≤ W1p.value (v : W1p mu B 2) x) :
    energyFormH1 a 0 0 (W1p.restrictL le_top ub - (w : W1p mu B 2)) (v : W1p mu B 2) ≤ 0 := by
  have hint : Integrable (fun x => g x * W1p.value (v : W1p mu B 2) x) (mu.restrict B) :=
    W1p0.integrable_mul_value_of_memLp hBfin hr (by rwa [finrank_euclideanSpace]) hg v
  -- The zero extension of `v` is a nonnegative test function on the whole space.
  have hext : ∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
      Set (EuclideanSpace ℝ ι)), 0 ≤ W1p.value (W1p0.extendByZeroL le_top v : W1p mu ⊤ 2) x := by
    rw [W1p0.value_extendByZeroL]
    filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ B.isOpen.measurableSet
        (SetLike.coe_subset_coe.mpr (le_top : B ≤ ⊤)) (W1p.value (v : W1p mu B 2)),
      ae_restrict_of_ae ((ae_restrict_iff' B.isOpen.measurableSet).1 hv)] with x hx hxv
    rw [hx]
    by_cases hxB : x ∈ (B : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxB]
      exact hxv hxB
    · rw [indicator_of_notMem hxB]
  -- `a(ū|_B - w, v) = a(ū, v) - ∫_B g v ≤ 0`.
  have hle := hsub (W1p0.extendByZeroL le_top v) hext
    ((W1p0.integrable_mul_value_extendByZeroL_iff le_top g v).2 hint)
  have e1 := W1p0.setIntegral_mul_value_extendByZeroL (mu := mu) le_top g v
  have e2 := energyFormH1_restrictL a 0 0 (le_top : B ≤ ⊤) ub v
  rw [energyFormH1_sub_left hcoeff, hw v, e2]
  linarith

/-- The splitting step behind the boundary estimates. On the ball `B = B(x₀, ρ)`, a weak
subsolution `ū` of `-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ g` on the whole space, with `g ∈ Lʳ(B)`, lies within
`K ρ^(2 - n/r) ‖g‖_{Lʳ(B)} / λ` of a weak subsolution `h ∈ H¹(B)` of the homogeneous equation. -/
private theorem exists_energyFormH1_nonpos_and_ae_abs_sub_le [Nonempty ι] {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ K : ℝ, 0 < K ∧ ∀ {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {g : EuclideanSpace ℝ ι → ℝ}
      {ub : W1p mu ⊤ 2} {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) a
        lam Lam →
      AEStronglyMeasurable a (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι))) →
      (∀ v : W1p0 mu ⊤ 2,
        (∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          0 ≤ W1p.value (v : W1p mu ⊤ 2) x) →
        Integrable (fun x => g x * W1p.value (v : W1p mu ⊤ 2) x)
          (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) →
        energyFormH1 a 0 0 ub (v : W1p mu ⊤ 2) ≤
          ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
            g x * W1p.value (v : W1p mu ⊤ 2) x ∂mu) →
      MemLp g r (mu.restrict (ball x₀ ρ)) → 0 < ρ →
      ∃ h : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          (∀ᵐ x ∂mu.restrict (ball x₀ ρ),
            0 ≤ W1p.value (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x) →
          energyFormH1 a 0 0 h (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) ≤ 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value ub x - W1p.value h x| ≤
          K * ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm g r (mu.restrict (ball x₀ ρ))).toReal / lam := by
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨C, hC, hstamp⟩ := exists_ae_abs_value_le_mul_div_mul_rpow (mu := mu) hr hrn
  have hrn' : n * (2 - r) < 2 * r := by
    have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
    nlinarith [mul_pos hn (sub_pos.2 hr1)]
  set e : ℝ := 2 / n - (r : ℝ)⁻¹
  have hγ : n * e = 2 - n / r := by simp only [e, n]; field_simp
  refine ⟨C * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e,
    mul_pos hC (Real.rpow_pos_of_pos (Metric.measureReal_ball_pos mu 0 one_pos) _), ?_⟩
  intro a g ub x₀ ρ h ha hsub hg hρ
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ ρ, isOpen_ball⟩
  have hBfin : mu B ≠ ∞ := measure_ball_lt_top.ne
  have hBell : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ ι)) a lam Lam :=
    h.mono_set (subset_univ _)
  have hBmeas : AEStronglyMeasurable a (mu.restrict B) :=
    ha.mono_measure (Measure.restrict_mono (subset_univ _) le_rfl)
  -- The weak solution `w ∈ H¹₀(B)` of `-∂ᵢ(aⁱʲ ∂ⱼw) = g` on `B`, and Stampacchia's bound on it.
  obtain ⟨w, hw, -⟩ :=
    hBell.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp (c := 0) (gamma := 0) hBmeas
      aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hBfin hr hrn' hg
  have hwbound := hstamp (Omega := B) (c := 0) (gamma := 0) hBfin hBell hBmeas
    aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hg hw
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    hBell.upper_nonneg hBmeas aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => hBell.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  refine ⟨W1p.restrictL le_top ub - (w : W1p mu B 2),
    energyFormH1_restrictL_sub_nonpos hr hrn' hBfin hcoeff hsub hg hw, ?_⟩
  -- `|ū - (ū|_B - w)| = |w| ≤ C ‖g‖ / λ |B|^e = C |B(0, 1)|^e ρ^(2 - n/r) ‖g‖ / λ`.
  have hmeas : mu.real (ball x₀ ρ) ^ e =
      ρ ^ (2 - n / r) * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e := by
    rw [Measure.addHaar_real_ball_rpow _ _ hρ, finrank_euclideanSpace, hγ]
  simp only [B, Opens.coe_mk] at hwbound
  filter_upwards [hwbound,
    W1p.value_sub_ae (W1p.restrictL le_top ub) (w : W1p mu B 2),
    W1p.value_restrictL_ae (le_top : B ≤ ⊤) ub] with x hx hxs hxr
  rw [hxs, Pi.sub_apply, hxr, sub_sub_cancel]
  refine hx.trans (le_of_eq ?_)
  rw [hmeas]
  ring

/-- The splitting step at a boundary point. Let `u` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f`
with `u⁺ ∈ H¹₀(Ω)` and `f ∈ Lʳ(Ω ∩ B(x₀, ρ))`. Then on `B = B(x₀, ρ)` there are a measurable
coefficient field `a'`, uniformly elliptic with the constants of `a`, and a weak subsolution
`h ∈ H¹(B)` of `-∂ᵢ(a'ⁱʲ ∂ⱼh) ≤ 0` within `K ρ^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B)} / λ` of `1_Ω u⁺`. -/
private theorem exists_energyFormH1_nonpos_and_ae_abs_indicator_sub_le [Nonempty ι] {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
            ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ)) → 0 < ρ →
      ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
        UniformlyEllipticOn (ball x₀ ρ) a' lam Lam ∧
        AEStronglyMeasurable a' (mu.restrict (ball x₀ ρ)) ∧
        ∃ h : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
            (∀ᵐ x ∂mu.restrict (ball x₀ ρ),
              0 ≤ W1p.value (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x) →
            energyFormH1 a' 0 0 h (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) ≤ 0) ∧
          ∀ᵐ x ∂mu.restrict (ball x₀ ρ),
            |(Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (W1p.value u y) 0) x -
              W1p.value h x| ≤
              K * ρ ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict
                ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ))).toReal / lam := by
  obtain ⟨K, hK, hsplit⟩ := exists_energyFormH1_nonpos_and_ae_abs_sub_le (mu := mu)
    (lam := lam) (Lam := Lam) hr hrn
  refine ⟨K, hK, fun {Omega a f u x₀ ρ} h ha hboundary hu hf hρ => ?_⟩
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  -- Extend `a` by `λ I` off `Ω` and `u⁺` by zero: a weak subsolution of
  -- `-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ 1_Ω f⁺` on the whole space.
  obtain ⟨a', h', ha', ub, hsubsol, hval⟩ :=
    exists_uniformlyEllipticOn_top_extendByZeroL_posPart h ha hboundary hu
  -- The datum `1_Ω f⁺` lies in `Lʳ(B(x₀, ρ))`, with norm at most `‖f‖_{Lʳ(Ω ∩ B(x₀, ρ))}`.
  have hOm' : NullMeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) (mu.restrict (ball x₀ ρ)) :=
    hOm.nullMeasurableSet
  have hg : MemLp ((Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (f y) 0)) r
      (mu.restrict (ball x₀ ρ)) := by
    rw [memLp_indicator_iff_restrict hOm', Measure.restrict_restrict hOm]
    exact hf.pos_part
  have hgN : eLpNorm ((Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (f y) 0)) r
      (mu.restrict (ball x₀ ρ)) ≤
        eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hOm', Measure.restrict_restrict hOm]
    refine eLpNorm_mono hf.pos_part.aestronglyMeasurable fun x => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  obtain ⟨hB, hBsub, hBclose⟩ := hsplit h' ha' hsubsol hg hρ
  refine ⟨a', h'.mono_set (subset_univ _),
    ha'.mono_measure (Measure.restrict_mono (subset_univ _) le_rfl), hB, hBsub, ?_⟩
  have hlam := h.pos
  have hN := ENNReal.toReal_mono hf.eLpNorm_ne_top hgN
  filter_upwards [hBclose, ae_restrict_of_ae hval] with x hx hx'
  rw [← hx']
  refine hx.trans ?_
  gcongr

omit [DecidableEq ι] in
/-- The two levels of the boundary reduction. If `|1_Ω u⁺ - h| ≤ ε` on `B(x₀, 2R)`, `u ≤ M` on
`Ω ∩ B(x₀, 2R)` with `M ≥ 0`, and `θ |B(x₀, R)| ≤ |B(x₀, R) \ Ω|`, then `h ≤ M + ε` on
`B(x₀, 2R)` and `h ≤ ε` on a proportion `θ` of `B(x₀, R)`. -/
private theorem ae_value_le_add_and_mul_measureReal_le {Omega : Opens (EuclideanSpace ℝ ι)}
    {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M ε θ : ℝ}
    {h : W1p mu ⟨ball x₀ (2 * R), isOpen_ball⟩ 2} (hR : 0 < R) (hM : 0 ≤ M)
    (hclose : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)),
      |(Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (W1p.value u y) 0) x -
        W1p.value h x| ≤ ε)
    (hle : ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)),
      W1p.value u x ≤ M)
    (hθR : θ * mu.real (ball x₀ R) ≤ mu.real (ball x₀ R \ (Omega : Set (EuclideanSpace ℝ ι)))) :
    (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value h x ≤ M + ε) ∧
      θ * mu.real (ball x₀ R) ≤ (mu.restrict (ball x₀ R)).real {x | W1p.value h x ≤ ε} := by
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  refine ⟨?_, hθR.trans ?_⟩
  · rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hclose,
      (ae_restrict_iff' (hOm.inter measurableSet_ball)).1 hle] with x hxc hx' hxb
    have hub : (Omega : Set (EuclideanSpace ℝ ι)).indicator
        (fun y => max (W1p.value u y) 0) x ≤ M := by
      by_cases hxO : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
      · rw [indicator_of_mem hxO]
        exact max_le (hx' ⟨hxO, hxb⟩) hM
      · rw [indicator_of_notMem hxO]
        exact hM
    linarith [(abs_le.1 (hxc hxb)).1]
  -- On `B(x₀, R) \ Ω` the indicator vanishes, so `h ≤ ε` there.
  rw [Set.sdiff_eq, inter_comm, ← measureReal_restrict_apply hOm.compl]
  refine ENNReal.toReal_mono ((measure_mono (subset_univ _)).trans_lt ?_).ne
    (measure_mono_ae ?_)
  · rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith))
      hclose] with x hxc hxO
    rw [indicator_of_notMem hxO, zero_sub, abs_neg, abs_le] at hxc
    exact hxc.2

/-- **Reduction of the supremum at the boundary with a right-hand side (De Giorgi).** Let `n ≥ 1`
be the dimension, fix a proportion `θ > 0` and let `r > 1` with `r > n/2`. There are `δ ∈ (0, 1)`,
depending only on `λ`, `Λ`, `θ`, the dimension and the normalization of the additive Haar measure
`mu`, and `K > 0`, depending only on `r`, the dimension and the normalization of `mu`, such that
the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and
let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u ≤ 0` on `∂Ω`: that is,
`a(u, v) ≤ ∫_Ω f v` for every nonnegative `v ∈ H¹₀(Ω)`, and `u⁺ ∈ H¹₀(Ω)`. Let
`f ∈ Lʳ(Ω ∩ B(x₀, 2R))`. If `u ≤ M` almost everywhere on `Ω ∩ B(x₀, 2R)` and the complement of
`Ω` fills the proportion `θ` of `B(x₀, R)`, that is `θ |B(x₀, R)| ≤ |B(x₀, R) \ Ω|`, then

`u ≤ (1 - δ) M + K R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, 2R))} / λ`

almost everywhere on `Ω ∩ B(x₀, R/2)`. The ball `B(x₀, 2R)` need not lie in `Ω`, and no
regularity of `∂Ω` is assumed. For `f = 0` this is
`TauCeti.PDE.exists_ae_value_le_mul_of_mul_measureReal_le_measureReal_ball_diff`. -/
theorem exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff [Nonempty ι]
    {θ : ℝ} (hθ : 0 < θ) {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ δ K : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
            ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R))) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)),
        W1p.value u x ≤ M) →
      θ * mu.real (ball x₀ R) ≤ mu.real (ball x₀ R \ (Omega : Set (EuclideanSpace ℝ ι))) →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 2)),
        W1p.value u x ≤ (1 - δ) * M + K * R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ (2 * R)))).toReal / lam := by
  set γ : ℝ := 2 - (Fintype.card ι : ℝ) / r
  obtain ⟨δ, hδ0, hδ1, hred⟩ :=
    exists_ae_value_le_sub_mul_sub (mu := mu) (lam := lam) (Lam := Lam) hθ
  obtain ⟨K, hK, hsplit⟩ := exists_energyFormH1_nonpos_and_ae_abs_indicator_sub_le (mu := mu)
    (lam := lam) (Lam := Lam) hr hrn
  refine ⟨δ, 2 * K * 2 ^ γ, hδ0, hδ1, by positivity, ?_⟩
  intro Omega a f u x₀ R M h ha hboundary hu hf hR hle hθR
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hR2 : ball x₀ (R / 2) ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  set N : ℝ := (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
    ball x₀ (2 * R)))).toReal
  have hlam := h.pos
  rcases lt_or_ge M 0 with hM | hM
  · -- For `M < 0` the claim is weaker than the hypothesis.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_right _ hR2) hle]
      with x hx
    have : 0 ≤ 2 * K * 2 ^ γ * R ^ γ * N / lam := by positivity
    nlinarith
  -- Split off the right-hand side on `B(x₀, 2R)`: `|1_Ω u⁺ - h| ≤ ε` with `h` a homogeneous
  -- subsolution, and reduce the supremum of `h` at the level `ε`.
  obtain ⟨a', h', ha', hB, hBsub, hBclose⟩ := hsplit h ha hboundary hu hf (by positivity)
  set ε : ℝ := K * (2 * R) ^ γ * N / lam with hε_def
  obtain ⟨hM', hθ'⟩ := ae_value_le_add_and_mul_measureReal_le hR hM hBclose hle hθR
  have hred' := hred (Omega := ⟨ball x₀ (2 * R), isOpen_ball⟩) (u := hB) h' ha' hBsub hR
    subset_rfl (by linarith) hM' hθ'
  have h2ε : 2 * ε = 2 * K * 2 ^ γ * R ^ γ * N / lam := by
    rw [hε_def, Real.mul_rpow (by norm_num) hR.le]
    ring
  -- On `Ω ∩ B(x₀, R/2)`: `u ≤ u⁺ ≤ h + ε ≤ (1 - δ) M + 2 ε`.
  rw [ae_restrict_iff' (hOm.inter measurableSet_ball)]
  filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hred',
    (ae_restrict_iff' measurableSet_ball).1 (ae_restrict_of_ae_restrict_of_subset hR2 hBclose)]
    with x hx hxc hxO
  have h1 := hx hxO.2
  have h3 := (abs_le.1 (hxc hxO.2)).2
  rw [indicator_of_mem hxO.1] at h3
  have h4 : W1p.value u x ≤ max (W1p.value u x) 0 := le_max_left _ _
  linarith

/-- The datum along the radii `R / 4ʲ`: on a ball of radius `ρ ≤ R / 4ʲ`, the term
`K ρ^γ N' / λ` of the reduction is at most `τʲ K R^γ N / λ`, once `4^(-γ) ≤ τ` and `N' ≤ N`. -/
private theorem mul_rpow_mul_div_le_pow_mul {K R ρ γ τ lam N N' : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ) (hτ : (4 : ℝ) ^ (-γ) ≤ τ) (hlam : 0 < lam) (hN' : 0 ≤ N')
    (hNN : N' ≤ N) {j : ℕ} (hρj : ρ ≤ R / 4 ^ j) :
    K * ρ ^ γ * N' / lam ≤ τ ^ j * (K * R ^ γ * N / lam) := by
  have h4 : ((4 : ℝ) ^ j) ^ γ = ((4 : ℝ) ^ γ) ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  have hργ : ρ ^ γ ≤ τ ^ j * R ^ γ := by
    refine (Real.rpow_le_rpow hρ hρj hγ).trans ?_
    rw [Real.div_rpow hR (by positivity), h4, div_eq_mul_inv, ← inv_pow, ← Real.rpow_neg
      (by norm_num), mul_comm]
    gcongr
  have hτ0 : 0 ≤ τ := (by positivity : (0 : ℝ) ≤ 4 ^ (-γ)).trans hτ
  calc K * ρ ^ γ * N' / lam ≤ K * (τ ^ j * R ^ γ) * N / lam := by gcongr
    _ = τ ^ j * (K * R ^ γ * N / lam) := by ring

/-- One step of the iteration: if the datum `F` costs at most `δ / 2` of `A ≥ 0` and
`1 - δ / 2 ≤ τ`, then `(1 - δ) τʲ A + τʲ F ≤ τʲ⁺¹ A`. -/
private theorem le_pow_succ_mul_of_le {δ τ A F y : ℝ} {j : ℕ} (hτ0 : 0 ≤ τ) (hδτ : 1 - δ / 2 ≤ τ)
    (hA : 0 ≤ A) (hF : F ≤ δ / 2 * A) (hy : y ≤ (1 - δ) * (τ ^ j * A) + τ ^ j * F) :
    y ≤ τ ^ (j + 1) * A := by
  have hτj := pow_nonneg hτ0 j
  calc y ≤ (1 - δ) * (τ ^ j * A) + τ ^ j * F := hy
    _ ≤ τ ^ j * ((1 - δ / 2) * A) := by nlinarith
    _ ≤ τ ^ j * (τ * A) := by gcongr
    _ = τ ^ (j + 1) * A := by ring

/-- **Geometric decay of the supremum at the boundary with a right-hand side (De Giorgi).** Let
`n ≥ 1` be the dimension, fix a proportion `θ > 0` and let `r > 1` with `r > n/2`. There are
`τ ∈ (0, 1)` and `D > 0`, depending only on `λ`, `Λ`, `θ`, `r`, the dimension and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u⁺ ∈ H¹₀(Ω)`, where `f ∈ Lʳ(Ω ∩ B(x₀, R))`. If `u ≤ M`
almost everywhere on `Ω ∩ B(x₀, R)` and the complement of `Ω` fills the proportion `θ` of every
ball `B(x₀, ρ)`, `0 < ρ ≤ R`, then for every `j`

`u ≤ τʲ (M + D R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, R))} / λ)`

almost everywhere on `Ω ∩ B(x₀, R / 4ʲ)`. For `f = 0` this is
`TauCeti.PDE.exists_ae_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`. -/
theorem exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff [Nonempty ι]
    {θ : ℝ} (hθ : 0 < θ) {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ τ D : ℝ, 0 < τ ∧ τ < 1 ∧ 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
            ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R), W1p.value u x ≤ M) →
      (∀ ρ, 0 < ρ → ρ ≤ R →
        θ * mu.real (ball x₀ ρ) ≤ mu.real (ball x₀ ρ \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
        W1p.value u x ≤ τ ^ j * (M + D * R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ R))).toReal / lam) := by
  set γ : ℝ := 2 - (Fintype.card ι : ℝ) / r
  have hγ : 0 < γ := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast zero_lt_one.trans hr
    exact sub_pos.2 ((div_lt_iff₀ hr0).2 (by linarith only [hrn]))
  obtain ⟨δ, K, hδ0, hδ1, hK, hred⟩ :=
    exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hθ hr hrn
  have h4γ : (4 : ℝ) ^ (-γ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨max (1 - δ / 2) ((4 : ℝ) ^ (-γ)), 2 * K / δ, lt_max_of_lt_left (by linarith),
    max_lt (by linarith) h4γ, by positivity, ?_⟩
  intro Omega a f u x₀ R M h ha hboundary hu hf hR hle hext j
  set τ := max (1 - δ / 2) ((4 : ℝ) ^ (-γ))
  have hτ0 : 0 ≤ τ := le_max_of_le_right (by positivity)
  set N : ℝ := (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
    ball x₀ R))).toReal
  have hlam := h.pos
  have hdiv (k : ℕ) : R / 4 ^ k ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hN : 0 ≤ 2 * K / δ * R ^ γ * N / lam := by positivity
  rcases lt_or_ge M 0 with hM | hM
  · -- For `M < 0` the claim is weaker than the hypothesis, since `τʲ ≤ 1`.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_right _ (ball_subset_ball (hdiv j))) hle] with x hx
    have : M ≤ τ ^ j * M := by nlinarith [pow_le_one₀ hτ0 (max_le (by linarith) h4γ.le) (n := j)]
    nlinarith [pow_nonneg hτ0 j]
  set A := M + 2 * K / δ * R ^ γ * N / lam
  have hA : 0 ≤ A := by positivity
  -- The datum costs at most `δ / 2` of `A` per step.
  have hKA : K * R ^ γ * N / lam ≤ δ / 2 * A := by
    have : δ / 2 * (2 * K / δ * R ^ γ * N / lam) = K * R ^ γ * N / lam := by field_simp
    nlinarith
  induction j with
  | zero => simpa [A] using hle.mono fun x hx => hx.trans (by linarith)
  | succ j ih =>
    -- One reduction step from `B(x₀, 2ρ)` to `B(x₀, ρ / 2)`, with `2ρ = R / 4ʲ`.
    set ρ := R / 4 ^ j / 2 with hρ_def
    have h2ρ : R / 4 ^ j = 2 * ρ := by rw [hρ_def]; ring
    have hρ : 0 < ρ := by positivity
    rw [h2ρ] at ih
    have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * ρ) ⊆
        (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R :=
      inter_subset_inter_right _ (ball_subset_ball (h2ρ ▸ hdiv j))
    have hstep := hred h ha hboundary hu (hf.mono_measure (Measure.restrict_mono hsub le_rfl)) hρ
      ih (hext ρ hρ (by linarith [hdiv j]))
    have hdatum := mul_rpow_mul_div_le_pow_mul hK.le hR.le hρ.le hγ.le
      (le_max_right (1 - δ / 2) _) hlam
      ENNReal.toReal_nonneg (ENNReal.toReal_mono hf.eLpNorm_ne_top
        (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))) (by linarith : ρ ≤ R / 4 ^ j)
    rw [show R / 4 ^ (j + 1) = ρ / 2 by rw [hρ_def, pow_succ]; ring]
    filter_upwards [hstep] with x hx
    exact le_pow_succ_mul_of_le hτ0 (le_max_left _ _) hA hKA (by nlinarith [pow_nonneg hτ0 j])

/-- **Geometric decay of weak solutions at the boundary with a right-hand side (De Giorgi).** Let
`n ≥ 1` be the dimension, fix a proportion `θ > 0` and let `r > 1` with `r > n/2`. There are
`τ ∈ (0, 1)` and `D > 0`, depending only on `λ`, `Λ`, `θ`, `r`, the dimension and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `f ∈ Lʳ(Ω ∩ B(x₀, R))`, and
let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is `a(u, v) = ∫_Ω f v` for every
`v ∈ H¹₀(Ω)`. If `|u| ≤ M` almost everywhere on `Ω ∩ B(x₀, R)` and the complement of `Ω` fills
the proportion `θ` of every ball `B(x₀, ρ)`, `0 < ρ ≤ R`, then for every `j`

`|u| ≤ τʲ (M + D R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, R))} / λ)`

almost everywhere on `Ω ∩ B(x₀, R / 4ʲ)`. -/
theorem exists_ae_abs_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ τ D : ℝ, 0 < τ ∧ τ < 1 ∧ 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R),
        |W1p.value u x| ≤ M) →
      (∀ ρ, 0 < ρ → ρ ≤ R →
        θ * mu.real (ball x₀ ρ) ≤ mu.real (ball x₀ ρ \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
        |W1p.value u x| ≤ τ ^ j * (M + D * R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ R))).toReal / lam) := by
  obtain ⟨τ, D, hτ0, hτ1, hD, hdecay⟩ :=
    exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hθ hr hrn
  refine ⟨τ, D, hτ0, hτ1, hD, ?_⟩
  intro Omega a f u x₀ R M h ha hu0 hu hf hR hle hext j
  have hneg_ae : ∀ᵐ x ∂mu.restrict Omega, W1p.value (-u) x = -W1p.value u x :=
    W1p.value_neg_ae u
  -- Both `u` and `-u` are subsolutions vanishing on the boundary, with data `f` and `-f`.
  have hpos := hdecay h ha (W1p.posPart_mem_w1p0Submodule (by norm_num) hu0)
    (fun v _ => (hu v).le) hf hR (by filter_upwards [hle] with x hx using (abs_le.1 hx).2) hext j
  have hneg := hdecay (f := fun x => -f x) h ha
    (W1p.posPart_mem_w1p0Submodule (by norm_num)
      ((w1p0Submodule mu Omega 2).toSubmodule.neg_mem hu0))
    (fun v _ => by
      rw [energyFormH1_neg_left, hu v, ← integral_neg]
      simp only [neg_mul, le_refl]) hf.neg hR
    (by
      filter_upwards [hle, ae_restrict_of_ae_restrict_of_subset inter_subset_left hneg_ae]
        with x hx hx'
      rw [hx']
      exact neg_le.1 (abs_le.1 hx).1) hext j
  have hnorm : eLpNorm (fun x => -f x) r
      (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) =
        eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) :=
    eLpNorm_neg _ _ _
  rw [hnorm] at hneg
  filter_upwards [hpos, hneg,
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hneg_ae] with x h1 h2 h3
  rw [h3] at h2
  exact abs_le.2 ⟨neg_le.1 h2, h1⟩

end PDE

end TauCeti
