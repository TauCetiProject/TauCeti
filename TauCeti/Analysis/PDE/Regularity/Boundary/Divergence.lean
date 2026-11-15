/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.Oscillation
import Mathlib.Analysis.SpecialFunctions.Log.Base
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness
import TauCeti.Analysis.Sobolev.W1p.Localization
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# De Giorgi's boundary decay with a right-hand side in divergence form

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants
`0 < λ ≤ Λ`, let `q > 2` with `q > n`, and let `u ∈ H¹₀(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω ∩ B(x₀, R)`, `u = 0` on `∂Ω`,

with `F ∈ L^q(Ω ∩ B(x₀, R); ℝⁿ)`: `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)` vanishing off
`B(x₀, R)`. Nothing is assumed about the regularity of `∂Ω`. This file proves that if the
complement of `Ω` fills a fixed proportion `θ > 0` of every ball `B(x₀, s)`, `0 < s ≤ R`, then `u`
decays like a power of the distance to `x₀`:

`|u| ≤ C (ρ / R)^β (M + R^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, R))} / λ)` on `Ω ∩ B(x₀, ρ)`, `0 < ρ ≤ R`,

where `M` bounds `|u|` on `Ω ∩ B(x₀, R)` and `β > 0`, `C` depend only on `λ`, `Λ`, `θ`, `n`, `q`
and the normalization of the Haar measure (in namespace `TauCeti.PDE`,
`exists_ae_abs_value_le_mul_div_rpow_mul_add_of_mul_measureReal_le_divergence`).

A datum in divergence form is how boundary values enter: if `u` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` and
`u - g ∈ H¹₀(Ω)` for a Lipschitz `g ∈ H¹(Ω)`, then `u - g` solves the equation above with
`F = a ∇g`. So this is the boundary counterpart, for such data, of the interior oscillation
estimate `TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le`, and
with it the input for the Hölder continuity of weak solutions up to the boundary of a domain
satisfying an exterior measure density condition, such as a Lipschitz domain.

## The argument

The datum is split off one scale at a time, as in the interior case. On `U = Ω ∩ B(x₀, ρ)`, the
Dirichlet problem `-∂ᵢ(aⁱʲ ∂ⱼw) = ∂ᵢFⁱ` in `U`, `w ∈ H¹₀(U)`, has a solution, and Stampacchia's
bound `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence` gives
`|w| ≤ K ρ^(1 - n/q) ‖F‖_{L^q(U)} / λ`, since `|U| ≤ |B(x₀, ρ)|`. The zero extension `W` of `w`
lies in `H¹₀(Ω)`, so `h = u - W` is again zero on `∂Ω`, and it solves the homogeneous equation
against the test functions vanishing off `B(x₀, ρ/2)`: such a test function restricts to an element
of `H¹₀(U)` (`TauCeti.W1p.restrictL_mem_w1p0Submodule_of_isCompact`), and its gradient vanishes
off `B(x₀, ρ/2)` as well. De Giorgi's reduction at the boundary for solutions of the homogeneous
equation near `x₀`
(`TauCeti.PDE.exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`) then
applies to `h`, and gives

`|u| ≤ (1 - δ) M + 2 K ρ^(1 - n/q) ‖F‖ / λ` on `Ω ∩ B(x₀, ρ/8)`

whenever `|u| ≤ M` on `Ω ∩ B(x₀, ρ)`. Iterating along the radii `R / 8ʲ`, the error terms form a
geometric series, because `1 - n/q > 0`, and the bound decays like `σʲ` for a ratio `σ < 1`.

## Main declarations

All in the namespace `TauCeti.PDE`.

* `exists_ae_abs_value_le_mul_div_rpow_mul_add_of_mul_measureReal_le_divergence`: the power decay
  of `|u|` at a point of positive exterior density.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.27 and 8.29.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

omit [DecidableEq ι] in
/-- The zero extension `W` of the solution `w ∈ H¹₀(Ω ∩ B(x₀, ρ))` of `-∂ᵢ(aⁱʲ ∂ⱼw) = ∂ᵢFⁱ`
satisfies `a(W, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)` vanishing off `B(x₀, ρ/2)`: such a `v`
restricts to an element of `H¹₀(Ω ∩ B(x₀, ρ))`, and its gradient vanishes off `B(x₀, ρ/2)`. -/
private theorem energyFormH1_extendByZeroL_inf_ball_eq_neg_setIntegral
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ} (hρ : 0 < ρ)
    {w : W1p0 mu (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) 2}
    (hw : ∀ v : W1p0 mu (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) 2,
      energyFormH1 a 0 0 (w : W1p mu (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) 2)
          (v : W1p mu (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) 2) =
        -∫ x in ((Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) :
          Set (EuclideanSpace ℝ ι)),
          ⟪F x, W1p.gradient (v : W1p mu (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) 2) x⟫ ∂mu)
    (v : W1p0 mu Omega 2)
    (hv : ∀ᵐ x ∂mu.restrict Omega,
      x ∉ ball x₀ (ρ / 2) → W1p.value (v : W1p mu Omega 2) x = 0) :
    energyFormH1 a 0 0 (W1p0.extendByZeroL inf_le_left w : W1p mu Omega 2)
        (v : W1p mu Omega 2) =
      -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu := by
  set V : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ ρ, isOpen_ball⟩
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hUsub : ((Omega ⊓ V : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) ⊆ Omega :=
    inter_subset_left
  have hvK : ∀ᵐ x ∂mu.restrict Omega,
      x ∉ closedBall x₀ (ρ / 2) → W1p.value (v : W1p mu Omega 2) x = 0 := by
    filter_upwards [hv] with x hx hxK using hx fun hxb => hxK (ball_subset_closedBall hxb)
  have hvU : W1p.restrictL inf_le_left (v : W1p mu Omega 2) ∈ w1p0Submodule mu (Omega ⊓ V) 2 :=
    W1p.restrictL_mem_w1p0Submodule_of_isCompact (V := V) (isCompact_closedBall x₀ (ρ / 2))
      (closedBall_subset_ball (by linarith)) v.2 hvK
  rw [energyFormH1_extendByZeroL_left, hw ⟨_, hvU⟩, neg_inj]
  -- `∇v` vanishes on `Ω \ B(x₀, ρ)`, and agrees with the gradient of the restriction on
  -- `Ω ∩ B(x₀, ρ)`.
  calc _ = ∫ x in ((Omega ⊓ V : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_restrictL_ae inf_le_left (v : W1p mu Omega 2)] with x hx
        rw [hx]
    _ = _ := by
        refine (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hOm.nullMeasurableSet hUsub ?_).symm
        filter_upwards [(ae_restrict_iff' hOm).1
          (W1p.gradient_ae_eq_zero_of_value_ae_eq_zero_of_isClosed isClosed_closedBall hvK)]
          with x hx hxd
        rw [hx hxd.1 fun hxb => hxd.2 ⟨hxd.1, closedBall_subset_ball (by linarith) hxb⟩,
          inner_zero_right]

/-- **Stampacchia's bound on `Ω ∩ B(x₀, ρ)`.** Let `n ≥ 1` and `q > 2` with `q > n`. There is
`K > 0`, depending only on `n`, `q` and the normalization of `mu`, such that the weak solution
`w ∈ H¹₀(Ω ∩ B(x₀, ρ))` of `-∂ᵢ(aⁱʲ ∂ⱼw) = ∂ᵢFⁱ` satisfies
`|w| ≤ K ρ^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, ρ))} / λ`: the measure of `Ω ∩ B(x₀, ρ)` in the global
bound `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence` is at most that of
`B(x₀, ρ)`. -/
private theorem exists_ae_abs_value_le_mul_rpow_of_inf_ball [Nonempty ι] {q : ℝ≥0}
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ} {w : W1p0 mu (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) 2},
      UniformlyEllipticOn ((Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict ((Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩ :
        Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) →
      MemLp F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ)) → 0 < ρ →
      (∀ v : W1p0 mu (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) 2,
        energyFormH1 a 0 0 (w : W1p mu (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) 2)
            (v : W1p mu (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) 2) =
          -∫ x in ((Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) :
            Set (EuclideanSpace ℝ ι)),
            ⟪F x, W1p.gradient (v : W1p mu (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) 2) x⟫ ∂mu) →
      ∀ᵐ x ∂mu.restrict ((Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι)),
        |W1p.value (w : W1p mu (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) 2) x| ≤
          K * ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
            (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ))).toReal /
              lam := by
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨C, hC, hstamp⟩ := exists_ae_abs_value_le_mul_div_mul_rpow_divergence (mu := mu) hq hqn
  -- The exponent `e = 1/n - 1/q > 0` of the measure in Stampacchia's bound, with `n e = 1 - n/q`.
  set e : ℝ := n⁻¹ - (q : ℝ)⁻¹
  have he : 0 ≤ e := sub_nonneg.2 (inv_anti₀ hn hqn.le)
  have hγ : (finrank ℝ (EuclideanSpace ℝ ι) : ℝ) * e = 1 - n / q := by
    rw [finrank_euclideanSpace]
    simp only [e, n]
    field_simp
  refine ⟨C * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e,
    mul_pos hC (Real.rpow_pos_of_pos (measureReal_ball_pos _ _ one_pos) _), ?_⟩
  intro Omega a F x₀ ρ w h ha hF hρ hw
  have hlam := h.pos
  -- `|Ω ∩ B(x₀, ρ)|^e ≤ |B(x₀, ρ)|^e = ρ^(1 - n/q) |B(0, 1)|^e`.
  have hmeas : mu.real ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ) ^ e ≤
      ρ ^ (1 - n / q) * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e := by
    rw [← hγ, ← Measure.addHaar_real_ball_rpow mu x₀ hρ e]
    exact Real.rpow_le_rpow measureReal_nonneg
      (measureReal_mono inter_subset_right measure_ball_lt_top.ne) he
  filter_upwards [hstamp (c := 0) (gamma := 0)
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne h ha
    aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hF hw] with x hx
  refine hx.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left hmeas (by positivity)) ?_)
  simp only [n, Opens.coe_inf, Opens.coe_mk]
  ring

/-- **Splitting off the datum at the boundary.** Let `n ≥ 1` and `q > 2` with `q > n`. There is
`K > 0`, depending only on `n`, `q` and the normalization of `mu`, such that the following holds.
Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` against the test functions vanishing off `B(x₀, ρ)`,
with `F ∈ L^q(Ω ∩ B(x₀, ρ))`. Then there is `W ∈ H¹₀(Ω)` with
`|W| ≤ K ρ^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, ρ))} / λ` such that `u - W` solves the homogeneous equation
against the test functions vanishing off `B(x₀, ρ/2)`. -/
private theorem exists_ae_abs_value_le_and_energyFormH1_sub_eq_zero [Nonempty ι] {q : ℝ≥0}
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ)) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, x ∉ ball x₀ ρ → W1p.value (v : W1p mu Omega 2) x = 0) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < ρ →
      ∃ W : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, |W1p.value (W : W1p mu Omega 2) x| ≤
          K * ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
            (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ))).toReal /
              lam) ∧
        ∀ v : W1p0 mu Omega 2,
          (∀ᵐ x ∂mu.restrict Omega,
            x ∉ ball x₀ (ρ / 2) → W1p.value (v : W1p mu Omega 2) x = 0) →
            energyFormH1 a 0 0 (u - (W : W1p mu Omega 2)) (v : W1p mu Omega 2) = 0 := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_ae_abs_value_le_mul_rpow_of_inf_ball (mu := mu) (lam := lam) (Lam := Lam) hq hqn
  refine ⟨K, hK, fun {Omega a F u x₀ ρ} h ha hF hu hρ => ?_⟩
  set V : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ ρ, isOpen_ball⟩
  have hUsub : ((Omega ⊓ V : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) ⊆ Omega :=
    inter_subset_left
  have hUfin : mu (Omega ⊓ V) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have : IsFiniteMeasure (mu.restrict ((Omega ⊓ V : Opens (EuclideanSpace ℝ ι)) :
      Set (EuclideanSpace ℝ ι))) := isFiniteMeasure_restrict.2 hUfin
  have hUell : UniformlyEllipticOn ((Omega ⊓ V : Opens (EuclideanSpace ℝ ι)) :
      Set (EuclideanSpace ℝ ι)) a lam Lam := h.mono_set hUsub
  have hUmeas : AEStronglyMeasurable a (mu.restrict (Omega ⊓ V)) :=
    ha.mono_measure (Measure.restrict_mono hUsub le_rfl)
  -- `W` is the zero extension of the solution `w ∈ H¹₀(Ω ∩ B(x₀, ρ))` of `-∂ᵢ(aⁱʲ ∂ⱼw) = ∂ᵢFⁱ`,
  -- whose datum `v ↦ -∫ ⟪F, ∇v⟫` is the functional `divergenceForcing F`, as `F ∈ L²`.
  have hF2 : MemLp F 2 (mu.restrict ((Omega ⊓ V : Opens (EuclideanSpace ℝ ι)) :
      Set (EuclideanSpace ℝ ι))) :=
    hF.mono_exponent (by exact_mod_cast (show ((2 : ℝ≥0) : ℝ) ≤ q by exact_mod_cast hq.le))
  obtain ⟨w, hw, -⟩ := hUell.existsUnique_forall_energyFormH1_eq_of_measure_ne_top (c := 0)
    (gamma := 0) hUmeas aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hUfin
    (divergenceForcing (hF2.toLp F))
  have hw' : ∀ v : W1p0 mu (Omega ⊓ V) 2,
      energyFormH1 a 0 0 (w : W1p mu (Omega ⊓ V) 2) (v : W1p mu (Omega ⊓ V) 2) =
        -∫ x in ((Omega ⊓ V : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          ⟪F x, W1p.gradient (v : W1p mu (Omega ⊓ V) 2) x⟫ ∂mu := fun v => by
    rw [hw v, divergenceForcing_apply_eq_neg_setIntegral, neg_inj]
    refine integral_congr_ae ?_
    filter_upwards [hF2.coeFn_toLp] with x hx
    rw [hx]
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    h.upper_nonneg ha aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => h.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  refine ⟨W1p0.extendByZeroL inf_le_left w, ?_, fun v hv => ?_⟩
  · -- `W` is `w` on `Ω ∩ B(x₀, ρ)` and `0` elsewhere.
    filter_upwards [W1p0.value_extendByZeroL_ae_eq_indicator inf_le_left w, ae_restrict_of_ae
      ((ae_restrict_iff' (Omega ⊓ V).isOpen.measurableSet).1 (hbound hUell hUmeas hF hρ hw'))]
      with x hx hwx
    rw [hx]
    by_cases hxU : x ∈ ((Omega ⊓ V : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxU]
      exact hwx hxU
    · rw [indicator_of_notMem hxU, abs_zero]
      have := h.pos
      positivity
  -- `a(u - W, v) = -∫_Ω ⟪F, ∇v⟫ + ∫_Ω ⟪F, ∇v⟫ = 0`.
  have hvρ : ∀ᵐ x ∂mu.restrict Omega, x ∉ ball x₀ ρ → W1p.value (v : W1p mu Omega 2) x = 0 := by
    filter_upwards [hv] with x hx hxρ using hx fun hx2 => hxρ (ball_subset_ball (by linarith) hx2)
  rw [energyFormH1_sub_left hcoeff,
    energyFormH1_extendByZeroL_inf_ball_eq_neg_setIntegral hρ hw' v hv, hu v hvρ, sub_self]

/-- **One step of the boundary decay with a datum in divergence form.** Let `n ≥ 1`, `θ > 0` and
`q > 2` with `q > n`. There are `δ > 0` and `K > 0`, depending only on `λ`, `Λ`, `θ`, `n`, `q` and
the normalization of `mu`, such that the following holds. Let `u ∈ H¹₀(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` against the test functions vanishing off `B(x₀, ρ)`, with
`F ∈ L^q(Ω ∩ B(x₀, ρ))`, and let the complement of `Ω` fill the proportion `θ` of every ball
`B(x₀, s)`, `0 < s ≤ ρ`. If `|u| ≤ M` on `Ω ∩ B(x₀, ρ)`, then on `Ω ∩ B(x₀, ρ/8)`

`|u| ≤ (1 - δ) M + K ρ^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, ρ))} / λ`. -/
private theorem exists_ae_abs_value_le_mul_add_mul_rpow [Nonempty ι] {θ : ℝ} (hθ : 0 < θ)
    {q : ℝ≥0} (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {ρ M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      u ∈ w1p0Submodule mu Omega 2 →
      MemLp F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ)) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, x ∉ ball x₀ ρ → W1p.value (v : W1p mu Omega 2) x = 0) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < ρ →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ),
        |W1p.value u x| ≤ M) →
      (∀ s, 0 < s → s ≤ ρ →
        θ * mu.real (ball x₀ s) ≤ mu.real (ball x₀ s \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (ρ / 8)),
        |W1p.value u x| ≤ (1 - δ) * M + K * ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
          (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ))).toReal /
            lam := by
  obtain ⟨K, hK, hsplit⟩ :=
    exists_ae_abs_value_le_and_energyFormH1_sub_eq_zero (mu := mu) (lam := lam) (Lam := Lam) hq
      hqn
  obtain ⟨δ, hδ0, -, hdecay⟩ :=
    exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hθ
  refine ⟨δ, 2 * K, hδ0, by positivity, ?_⟩
  intro Omega a F u x₀ ρ M h ha hu0 hF hu hρ hle hext
  obtain ⟨W, hWb, hW⟩ := hsplit h ha hF hu hρ
  set E := K * ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
    (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ))).toReal / lam
  have hE : 0 ≤ E := by have := h.pos; positivity
  -- `h = u - W` solves the homogeneous equation near `x₀`, and `|h| ≤ M + E` near `x₀`.
  have hbound : ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (ρ / 2)),
      |W1p.value (u - (W : W1p mu Omega 2)) x| ≤ M + E := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (inter_subset_inter_right _ (ball_subset_ball (by linarith))) hle,
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hWb,
      ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (W1p.value_sub_ae u (W : W1p mu Omega 2))] with x h1 h2 h3
    rw [h3, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hdec := hdecay (u := u - (W : W1p mu Omega 2)) (R := ρ / 2) (M := M + E) h ha
    ((w1p0Submodule mu Omega 2).toSubmodule.sub_mem hu0 W.2) hW (by positivity) hbound
    (fun s hs hsρ => hext s hs (by linarith)) 1
  rw [show ρ / 2 / 4 ^ 1 = ρ / 8 by ring, pow_one] at hdec
  -- `|u| ≤ |u - W| + |W| ≤ (1 - δ) (M + E) + E ≤ (1 - δ) M + 2 E`.
  filter_upwards [hdec, ae_restrict_of_ae_restrict_of_subset inter_subset_left hWb,
    ae_restrict_of_ae_restrict_of_subset inter_subset_left
      (W1p.value_sub_ae u (W : W1p mu Omega 2))] with x h1 h2 h3
  rw [h3, Pi.sub_apply] at h1
  have htri : |W1p.value u x| ≤ |W1p.value u x - W1p.value (W : W1p mu Omega 2) x| +
      |W1p.value (W : W1p mu Omega 2) x| := by
    simpa using abs_add_le (W1p.value u x - W1p.value (W : W1p mu Omega 2) x)
      (W1p.value (W : W1p mu Omega 2) x)
  have : (1 - δ) * E ≤ E := by nlinarith
  calc |W1p.value u x| ≤ (1 - δ) * (M + E) + E := by linarith
    _ ≤ (1 - δ) * M + 2 * E := by linarith
    _ = _ := by simp only [E]; ring

/-- The datum on the ball of radius `R / 8ʲ`: since `(R / 8ʲ)^γ = R^γ (8^(-γ))ʲ`, if
`8^(-γ) ≤ σ` and `N' ≤ N`, then `K (R / 8ʲ)^γ N' / λ ≤ (δ/2) σʲ (2K/δ) R^γ N / λ`. -/
private theorem mul_div_pow_rpow_mul_div_le {K R γ δ σ N N' lam : ℝ} (j : ℕ) (hK : 0 ≤ K)
    (hR : 0 ≤ R) (hlam : 0 ≤ lam) (hδ : 0 < δ) (hN' : 0 ≤ N') (hN : N' ≤ N)
    (hσ : (8 : ℝ) ^ (-γ) ≤ σ) :
    K * (R / 8 ^ j) ^ γ * N' / lam ≤ δ / 2 * σ ^ j * (2 * K / δ * R ^ γ * N / lam) := by
  have hR8 : (R / 8 ^ j) ^ γ = R ^ γ * ((8 : ℝ) ^ (-γ)) ^ j := by
    rw [Real.div_rpow hR (by positivity), ← Real.rpow_natCast (8 : ℝ) j,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast _ j, ← Real.rpow_mul (by norm_num),
      div_eq_mul_inv, ← Real.rpow_neg (by norm_num), mul_comm (j : ℝ) γ, neg_mul]
  have hσj : ((8 : ℝ) ^ (-γ)) ^ j ≤ σ ^ j := pow_le_pow_left₀ (by positivity) hσ j
  have hσ0 : 0 ≤ σ := (Real.rpow_nonneg (by norm_num) _).trans hσ
  rw [hR8]
  calc _ ≤ K * (R ^ γ * σ ^ j) * N / lam := by gcongr
    _ = δ / 2 * σ ^ j * (2 * K / δ * R ^ γ * N / lam) := by field_simp

/-- The arithmetic of one step of the iteration: if `1 - δ/2 ≤ σ` and the error `E` is at most
`(δ/2) σʲ B`, then `(1 - δ) σʲ (M + B) + E ≤ σʲ⁺¹ (M + B)` for `M, B ≥ 0`. -/
private theorem mul_pow_mul_add_le_pow_succ_mul {δ σ M B E : ℝ} {j : ℕ} (hσ : 1 - δ / 2 ≤ σ)
    (hσ0 : 0 ≤ σ) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hB : 0 ≤ B) (hE : E ≤ δ / 2 * σ ^ j * B) :
    (1 - δ) * (σ ^ j * (M + B)) + E ≤ σ ^ (j + 1) * (M + B) := by
  have h1 : δ / 2 * σ ^ j * B ≤ δ / 2 * σ ^ j * (M + B) := by gcongr; linarith
  have h2 := mul_le_mul_of_nonneg_right hσ (mul_nonneg (pow_nonneg hσ0 j) (add_nonneg hM hB))
  rw [pow_succ]
  linarith

/-- **Geometric decay at the boundary with a datum in divergence form.** Let `n ≥ 1`, `θ > 0` and
`q > 2` with `q > n`. There are `σ ∈ (0, 1)` and `D > 0`, depending only on `λ`, `Λ`, `θ`, `n`, `q`
and the normalization of `mu`, such that the following holds. Let `u ∈ H¹₀(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` against the test functions vanishing off `B(x₀, R)`, with
`F ∈ L^q(Ω ∩ B(x₀, R))`, and let the complement of `Ω` fill the proportion `θ` of every ball
`B(x₀, s)`, `0 < s ≤ R`. If `|u| ≤ M` on `Ω ∩ B(x₀, R)`, then for every `j`, on
`Ω ∩ B(x₀, R / 8ʲ)`

`|u| ≤ σʲ (M + D R^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, R))} / λ)`. -/
private theorem exists_ae_abs_value_le_pow_mul_add [Nonempty ι] {θ : ℝ} (hθ : 0 < θ)
    {q : ℝ≥0} (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ σ D : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      u ∈ w1p0Submodule mu Omega 2 →
      MemLp F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, x ∉ ball x₀ R → W1p.value (v : W1p mu Omega 2) x = 0) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R),
        |W1p.value u x| ≤ M) →
      (∀ s, 0 < s → s ≤ R →
        θ * mu.real (ball x₀ s) ≤ mu.real (ball x₀ s \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 8 ^ j)),
        |W1p.value u x| ≤ σ ^ j * (M + D * R ^ (1 - (Fintype.card ι : ℝ) / q) *
          (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal /
            lam) := by
  set γ : ℝ := 1 - (Fintype.card ι : ℝ) / q
  have hγ : 0 < γ := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hqn
  obtain ⟨δ, K, hδ0, hK, hstep⟩ :=
    exists_ae_abs_value_le_mul_add_mul_rpow (mu := mu) (lam := lam) (Lam := Lam) hθ hq hqn
  -- The error terms decay like `tʲ`, `t = 8^(-γ) < 1`; the ratio is `σ = max (1 - δ/2) t`.
  set t : ℝ := (8 : ℝ) ^ (-γ)
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨max (1 - δ / 2) t, 2 * K / δ, lt_max_of_lt_right ht0, max_lt (by linarith) ht1,
    by positivity, ?_⟩
  intro Omega a F u x₀ R M h ha hu0 hF hu hR hle hext j
  set σ := max (1 - δ / 2) t
  set N := (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal
  have hlam : 0 < lam := h.pos
  have hball (j : ℕ) : ball x₀ (R / 8 ^ j) ⊆ ball x₀ R :=
    ball_subset_ball (div_le_self hR.le (one_le_pow₀ (by norm_num)))
  rcases lt_or_ge M 0 with hM | hM
  · -- `|u| ≤ M < 0` almost everywhere forces `Ω ∩ B(x₀, R)` to be null.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_right _ (hball j))
      hle] with x hx
    exact absurd (abs_nonneg (W1p.value u x)) (by linarith)
  induction j with
  | zero =>
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_right _ (hball 0))
      hle] with x hx
    have : 0 ≤ 2 * K / δ * R ^ γ * N / lam := by positivity
    rw [pow_zero, one_mul]
    linarith
  | succ j ih =>
    -- One step from `B(x₀, R / 8ʲ)` to `B(x₀, R / 8ʲ⁺¹)`.
    have hst := hstep (ρ := R / 8 ^ j) (M := σ ^ j * (M + 2 * K / δ * R ^ γ * N / lam)) h ha hu0
      (hF.mono_measure (Measure.restrict_mono (inter_subset_inter_right _ (hball j)) le_rfl))
      (fun v hv => hu v (by
        filter_upwards [hv] with x hx hxR using hx fun hxρ => hxR (hball j hxρ)))
      (by positivity) ih
      (fun s hs hsρ => hext s hs (hsρ.trans (div_le_self hR.le (one_le_pow₀ (by norm_num)))))
    rw [show R / 8 ^ (j + 1) = R / 8 ^ j / 8 by rw [pow_succ]; ring]
    -- The datum on the smaller ball has norm at most `N`.
    have hNj : (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
        ball x₀ (R / 8 ^ j)))).toReal ≤ N :=
      ENNReal.toReal_mono hF.eLpNorm_ne_top (eLpNorm_mono_measure _
        (Measure.restrict_mono (inter_subset_inter_right _ (hball j)) le_rfl))
    filter_upwards [hst] with x hx
    exact hx.trans (mul_pow_mul_add_le_pow_succ_mul (le_max_left _ _) (ht0.le.trans
      (le_max_right _ _)) hδ0.le hM (by positivity) (mul_div_pow_rpow_mul_div_le j hK.le hR.le
        hlam.le hδ0 ENNReal.toReal_nonneg hNj (le_max_right _ _)))

/-- **Power decay at the boundary with a datum in divergence form (De Giorgi).** Let `n ≥ 1` be
the dimension, fix a proportion `θ > 0` and an exponent `q > 2` with `q > n`. There are `β > 0` and
`C > 0`, depending only on `λ`, `Λ`, `θ`, `n`, `q` and the normalization of the additive Haar
measure `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω`
with constants `λ, Λ`, let `F ∈ L^q(Ω ∩ B(x₀, R); ℝⁿ)`, and let `u ∈ H¹₀(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω ∩ B(x₀, R)`: `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`
vanishing off `B(x₀, R)`. If `|u| ≤ M` almost everywhere on `Ω ∩ B(x₀, R)` and the complement of
`Ω` fills the proportion `θ` of every ball `B(x₀, s)`, `0 < s ≤ R`, then for `ρ ≤ R`, almost
everywhere on `Ω ∩ B(x₀, ρ)`

`|u| ≤ C (ρ / R)^β (M + R^(1 - n/q) ‖F‖_{L^q(Ω ∩ B(x₀, R))} / λ)`.

No regularity of `∂Ω` is assumed. For `F = 0` this is the power form of the geometric decay
`TauCeti.PDE.exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`. -/
theorem exists_ae_abs_value_le_mul_div_rpow_mul_add_of_mul_measureReal_le_divergence
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ β C : ℝ, 0 < β ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      u ∈ w1p0Submodule mu Omega 2 →
      MemLp F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, x ∉ ball x₀ R → W1p.value (v : W1p mu Omega 2) x = 0) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R),
        |W1p.value u x| ≤ M) →
      (∀ s, 0 < s → s ≤ R →
        θ * mu.real (ball x₀ s) ≤ mu.real (ball x₀ s \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ρ ≤ R →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ),
        |W1p.value u x| ≤ C * (ρ / R) ^ β * (M + R ^ (1 - (Fintype.card ι : ℝ) / q) *
          (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal /
            lam) := by
  obtain ⟨σ, D, hσ0, hσ1, hD, hdecay⟩ :=
    exists_ae_abs_value_le_pow_mul_add (mu := mu) (lam := lam) (Lam := Lam) hθ hq hqn
  -- The ratio `σ` of the geometric decay along the radii `R / 8ʲ` is `8^(-β)`.
  set β := -Real.logb 8 σ
  have hβ : 0 < β := neg_pos.2 (Real.logb_neg (by norm_num) hσ0 hσ1)
  have h8β : (8 : ℝ) ^ (-β) = σ := by
    rw [neg_neg]
    exact Real.rpow_logb (by norm_num) (by norm_num) hσ0
  refine ⟨β, 8 ^ β * max 1 D, hβ, by positivity, ?_⟩
  intro Omega a F u x₀ R M ρ h ha hu0 hF hu hle hext hρR
  -- For `ρ ≤ 0` the ball is empty.
  rcases le_or_gt ρ 0 with hρ0 | hρ
  · simp [ball_eq_empty.2 hρ0]
  have hR : 0 < R := hρ.trans_le hρR
  set B := R ^ (1 - (Fintype.card ι : ℝ) / q) *
    (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal / lam
  have hB : 0 ≤ B := by have := h.pos; positivity
  rcases lt_or_ge M 0 with hM | hM
  · -- `|u| ≤ M < 0` almost everywhere forces `Ω ∩ B(x₀, R)` to be null.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_right _ (ball_subset_ball hρR)) hle] with x hx
    exact absurd (abs_nonneg (W1p.value u x)) (by linarith)
  -- With `L = log₈ (R / ρ)` and `j = ⌊L⌋`, `ρ ≤ R / 8ʲ` and `σʲ ≤ 8^β (ρ / R)^β`.
  set L := Real.logb 8 (R / ρ)
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) ((one_le_div hρ).2 hρR)
  have h8L : (8 : ℝ) ^ L = R / ρ := Real.rpow_logb (by norm_num) (by norm_num) (div_pos hR hρ)
  set j := ⌊L⌋₊
  have hjL : (j : ℝ) ≤ L := Nat.floor_le hL
  have hLj : L < j + 1 := Nat.lt_floor_add_one L
  have hρj : ρ ≤ R / 8 ^ j := by
    rw [le_div_iff₀ (by positivity), ← Real.rpow_natCast]
    calc ρ * (8 : ℝ) ^ (j : ℝ) ≤ ρ * 8 ^ L :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hjL) hρ.le
      _ = R := by rw [h8L]; field_simp
  have hσj : σ ^ j ≤ 8 ^ β * (ρ / R) ^ β := by
    have hρR' : ρ / R = (8 : ℝ) ^ (-L) := by rw [Real.rpow_neg (by norm_num), h8L, inv_div]
    rw [← h8β, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hρR',
      ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hY : M + D * B ≤ max 1 D * (M + B) := by
    nlinarith [le_max_left 1 D, le_max_right 1 D]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (inter_subset_inter_right _ (ball_subset_ball hρj)) (hdecay h ha hu0 hF hu hR hle hext j)]
    with x hx
  refine hx.trans ?_
  calc σ ^ j * (M + D * R ^ (1 - (Fintype.card ι : ℝ) / q) *
        (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal / lam)
      = σ ^ j * (M + D * B) := by simp only [B]; ring
    _ ≤ (8 ^ β * (ρ / R) ^ β) * (max 1 D * (M + B)) :=
        mul_le_mul hσj hY (by positivity) (by positivity)
    _ = _ := by simp only [B]; ring

end PDE

end TauCeti
