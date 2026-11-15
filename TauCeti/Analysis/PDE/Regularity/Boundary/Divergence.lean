/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.Oscillation
import TauCeti.Analysis.SpecialFunctions.Log.Base
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
and the normalization of the Haar measure. The theorem, in the namespace `TauCeti.PDE`, is
`exists_ae_abs_value_le_mul_div_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence`

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

Everything after the splitting depends only on its outcome: at every scale `s ≤ R`, `u` lies
within `s^γ A` of a solution in `H¹₀(Ω)` of the homogeneous equation near `x₀`, for some `γ > 0`.
The iteration is proved under this hypothesis alone, as in the interior case, so that any datum
which can be split off with a Morrey gain `γ > 0` gives the same decay.

## Main declarations

All in the namespace `TauCeti.PDE`.

* `exists_ae_abs_value_le_mul_div_rpow_mul_add_of_forall_ae_abs_sub_le`: the power decay of `|u|`
  at a point of positive exterior density, for `u` within `s^γ A` of a solution of the
  homogeneous equation vanishing on `∂Ω` at every scale `s ≤ R`.
* The power decay of `|u|` at a point of positive exterior density, for a datum in divergence form:
`exists_ae_abs_value_le_mul_div_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence`

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

/-- **One step of the boundary decay near a solution of the homogeneous equation.** Let `n ≥ 1`
and `θ > 0`. There is `δ > 0`, depending only on `λ`, `Λ`, `θ`, `n` and the normalization of `mu`,
such that the following holds. Let `g ∈ H¹₀(Ω)` solve the homogeneous equation against the test
functions vanishing off `B(x₀, ρ/2)`, let `|u - g| ≤ E` on `Ω ∩ B(x₀, ρ/2)`, and let the complement
of `Ω` fill the proportion `θ` of every ball `B(x₀, s)`, `0 < s ≤ ρ`. If `|u| ≤ M` on
`Ω ∩ B(x₀, ρ)`, then `|u| ≤ (1 - δ) M + 2 E` on `Ω ∩ B(x₀, ρ/8)`. -/
private theorem exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le [Nonempty ι] {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u g : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι}
      {ρ M E : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      g ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, x ∉ ball x₀ (ρ / 2) → W1p.value (v : W1p mu Omega 2) x = 0) →
          energyFormH1 a 0 0 g (v : W1p mu Omega 2) = 0) →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (ρ / 2)),
        |W1p.value u x - W1p.value g x| ≤ E) →
      0 < ρ → 0 ≤ E →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ),
        |W1p.value u x| ≤ M) →
      (∀ s, 0 < s → s ≤ ρ →
        θ * mu.real (ball x₀ s) ≤ mu.real (ball x₀ s \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (ρ / 8)),
        |W1p.value u x| ≤ (1 - δ) * M + 2 * E := by
  obtain ⟨δ, hδ0, -, hdecay⟩ :=
    exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hθ
  refine ⟨δ, hδ0, ?_⟩
  intro Omega a u g x₀ ρ M E h ha hg0 hg hug hρ hE hle hext
  -- `|g| ≤ |u| + |u - g| ≤ M + E` on `Ω ∩ B(x₀, ρ/2)`.
  have hbound : ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (ρ / 2)),
      |W1p.value g x| ≤ M + E := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (inter_subset_inter_right _ (ball_subset_ball (by linarith))) hle, hug] with x h1 h2
    calc |W1p.value g x| ≤ |W1p.value u x| + |W1p.value u x - W1p.value g x| := by
          simpa using abs_sub (W1p.value u x) (W1p.value u x - W1p.value g x)
      _ ≤ M + E := add_le_add h1 h2
  have hdec := hdecay (R := ρ / 2) h ha hg0 hg (by positivity) hbound
    (fun s hs hsρ => hext s hs (by linarith)) 1
  rw [show ρ / 2 / 4 ^ 1 = ρ / 8 by ring, pow_one] at hdec
  -- `|u| ≤ |u - g| + |g| ≤ E + (1 - δ) (M + E) ≤ (1 - δ) M + 2 E`.
  filter_upwards [hdec, ae_restrict_of_ae_restrict_of_subset
    (inter_subset_inter_right _ (ball_subset_ball (by linarith))) hug] with x h1 h2
  have htri : |W1p.value u x| ≤ |W1p.value u x - W1p.value g x| + |W1p.value g x| := by
    simpa using abs_add_le (W1p.value u x - W1p.value g x) (W1p.value g x)
  nlinarith

/-- The error on the ball of radius `R / 8ʲ`: since `(R / 8ʲ)^γ = R^γ (8^(-γ))ʲ`, if
`8^(-γ) ≤ σ`, then `2 (R / 8ʲ)^γ A ≤ (δ/2) σʲ ((4/δ) R^γ A)`. -/
private theorem two_mul_div_pow_rpow_mul_le {R γ δ σ A : ℝ} (j : ℕ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hσ : (8 : ℝ) ^ (-γ) ≤ σ) :
    2 * ((R / 8 ^ j) ^ γ * A) ≤ δ / 2 * σ ^ j * (4 / δ * R ^ γ * A) := by
  have hR8 : (R / 8 ^ j) ^ γ = R ^ γ * ((8 : ℝ) ^ (-γ)) ^ j := by
    rw [Real.div_rpow hR (by positivity), Real.rpow_pow_comm (by norm_num),
      Real.rpow_neg (by positivity), div_eq_mul_inv]
  have hσj : ((8 : ℝ) ^ (-γ)) ^ j ≤ σ ^ j := pow_le_pow_left₀ (by positivity) hσ j
  rw [hR8]
  calc _ ≤ 2 * (R ^ γ * σ ^ j * A) := by gcongr
    _ = δ / 2 * σ ^ j * (4 / δ * R ^ γ * A) := by field_simp; ring

/-- The arithmetic of one step of the iteration: if `1 - δ/2 ≤ σ` and the error `E` is at most
`(δ/2) σʲ B`, then `(1 - δ) σʲ (M + B) + E ≤ σʲ⁺¹ (M + B)` for `M, B ≥ 0`. -/
private theorem mul_pow_mul_add_le_pow_succ_mul {δ σ M B E : ℝ} {j : ℕ} (hσ : 1 - δ / 2 ≤ σ)
    (hσ0 : 0 ≤ σ) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hB : 0 ≤ B) (hE : E ≤ δ / 2 * σ ^ j * B) :
    (1 - δ) * (σ ^ j * (M + B)) + E ≤ σ ^ (j + 1) * (M + B) := by
  have h1 : δ / 2 * σ ^ j * B ≤ δ / 2 * σ ^ j * (M + B) := by gcongr; linarith
  have h2 := mul_le_mul_of_nonneg_right hσ (mul_nonneg (pow_nonneg hσ0 j) (add_nonneg hM hB))
  rw [pow_succ]
  linarith

/-- **Geometric decay at the boundary near solutions of the homogeneous equation.** Let `n ≥ 1`,
`θ > 0` and `γ > 0`. There are `σ ∈ (0, 1)` and `D > 0`, depending only on `λ`, `Λ`, `θ`, `n`, `γ`
and the normalization of `mu`, such that the following holds. Let `u ∈ H¹(Ω)` lie within `s^γ A`
of a solution `g ∈ H¹₀(Ω)` of the homogeneous equation near `x₀`, for every `0 < s ≤ R`: `g` solves
it against the test functions vanishing off `B(x₀, s/2)` and `|u - g| ≤ s^γ A` on
`Ω ∩ B(x₀, s/2)`. Let the complement of `Ω` fill the proportion `θ` of every ball `B(x₀, s)`,
`0 < s ≤ R`. If `|u| ≤ M` on `Ω ∩ B(x₀, R)`, then for every `j`, on `Ω ∩ B(x₀, R / 8ʲ)`

`|u| ≤ σʲ (M + D R^γ A)`. -/
private theorem exists_ae_abs_value_le_pow_mul_add_of_forall_ae_abs_sub_le [Nonempty ι]
    {θ γ : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) :
    ∃ σ D : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι}
      {R M A : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ s, 0 < s → s ≤ R → ∃ g : W1p mu Omega 2, g ∈ w1p0Submodule mu Omega 2 ∧
        (∀ v : W1p0 mu Omega 2,
          (∀ᵐ x ∂mu.restrict Omega, x ∉ ball x₀ (s / 2) → W1p.value (v : W1p mu Omega 2) x = 0) →
            energyFormH1 a 0 0 g (v : W1p mu Omega 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (s / 2)),
          |W1p.value u x - W1p.value g x| ≤ s ^ γ * A) →
      0 < R → 0 ≤ A →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R),
        |W1p.value u x| ≤ M) →
      (∀ s, 0 < s → s ≤ R →
        θ * mu.real (ball x₀ s) ≤ mu.real (ball x₀ s \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 8 ^ j)),
        |W1p.value u x| ≤ σ ^ j * (M + D * R ^ γ * A) := by
  obtain ⟨δ, hδ0, hstep⟩ :=
    exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le (mu := mu) (lam := lam) (Lam := Lam) hθ
  -- The error terms decay like `tʲ`, `t = 8^(-γ) < 1`; the ratio is `σ = max (1 - δ/2) t`.
  set t : ℝ := (8 : ℝ) ^ (-γ)
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨max (1 - δ / 2) t, 4 / δ, lt_max_of_lt_right ht0, max_lt (by linarith) ht1,
    by positivity, ?_⟩
  intro Omega a u x₀ R M A h ha happrox hR hA hle hext j
  set σ := max (1 - δ / 2) t
  have hjR (j : ℕ) : R / 8 ^ j ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  rcases lt_or_ge M 0 with hM | hM
  · -- `|u| ≤ M < 0` almost everywhere forces `Ω ∩ B(x₀, R)` to be null.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_right _ (ball_subset_ball (hjR j))) hle] with x hx
    exact absurd (abs_nonneg (W1p.value u x)) (by linarith)
  induction j with
  | zero =>
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_right _ (ball_subset_ball (hjR 0))) hle] with x hx
    have : 0 ≤ 4 / δ * R ^ γ * A := by positivity
    rw [pow_zero, one_mul]
    linarith
  | succ j ih =>
    -- One step from `B(x₀, R / 8ʲ)` to `B(x₀, R / 8ʲ⁺¹)`.
    obtain ⟨g, hg0, hg, hug⟩ := happrox (R / 8 ^ j) (by positivity) (hjR j)
    have hst := hstep (ρ := R / 8 ^ j) (M := σ ^ j * (M + 4 / δ * R ^ γ * A)) h ha hg0 hg hug
      (by positivity) (by positivity) ih (fun s hs hsρ => hext s hs (hsρ.trans (hjR j)))
    rw [show R / 8 ^ (j + 1) = R / 8 ^ j / 8 by rw [pow_succ]; ring]
    filter_upwards [hst] with x hx
    exact hx.trans (mul_pow_mul_add_le_pow_succ_mul (le_max_left _ _)
      (ht0.le.trans (le_max_right _ _)) hδ0.le hM (by positivity)
      (two_mul_div_pow_rpow_mul_le j hR.le hA hδ0 (le_max_right _ _)))

/-- **Power decay at the boundary near solutions of the homogeneous equation (De Giorgi).** Let
`n ≥ 1` be the dimension, fix a proportion `θ > 0` and an exponent `γ > 0`. There are `β > 0` and
`C > 0`, depending only on `λ`, `Λ`, `θ`, `n`, `γ` and the normalization of the additive Haar
measure `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω`
with constants `λ, Λ`, let `A ≥ 0`, and let `u ∈ H¹(Ω)` lie within `s^γ A` of a solution of the
homogeneous equation vanishing on `∂Ω`, near `x₀` at every scale `0 < s ≤ R`: there is `g ∈ H¹₀(Ω)`
with `a(g, v) = 0` for every `v ∈ H¹₀(Ω)` vanishing off `B(x₀, s/2)` and `|u - g| ≤ s^γ A`
almost everywhere on `Ω ∩ B(x₀, s/2)`. If `|u| ≤ M` almost everywhere on `Ω ∩ B(x₀, R)` and the
complement of `Ω` fills the proportion `θ` of every ball `B(x₀, s)`, `0 < s ≤ R`, then for
`ρ ≤ R`, almost everywhere on `Ω ∩ B(x₀, ρ)`

`|u| ≤ C (ρ / R)^β (M + R^γ A)`.

Splitting off a right-hand side at every scale supplies the hypothesis, with `γ` the Morrey gain
of the datum and `A` a multiple of its norm. For `A = 0` this is the power form of the geometric
decay `TauCeti.PDE.exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`. -/
theorem exists_ae_abs_value_le_mul_div_rpow_mul_add_of_forall_ae_abs_sub_le [Nonempty ι]
    {θ γ : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) :
    ∃ β C : ℝ, 0 < β ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι}
      {R M ρ A : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ s, 0 < s → s ≤ R → ∃ g : W1p mu Omega 2, g ∈ w1p0Submodule mu Omega 2 ∧
        (∀ v : W1p0 mu Omega 2,
          (∀ᵐ x ∂mu.restrict Omega, x ∉ ball x₀ (s / 2) → W1p.value (v : W1p mu Omega 2) x = 0) →
            energyFormH1 a 0 0 g (v : W1p mu Omega 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (s / 2)),
          |W1p.value u x - W1p.value g x| ≤ s ^ γ * A) →
      0 ≤ A →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R),
        |W1p.value u x| ≤ M) →
      (∀ s, 0 < s → s ≤ R →
        θ * mu.real (ball x₀ s) ≤ mu.real (ball x₀ s \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ρ ≤ R →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ),
        |W1p.value u x| ≤ C * (ρ / R) ^ β * (M + R ^ γ * A) := by
  obtain ⟨σ, D, hσ0, hσ1, hD, hdecay⟩ :=
    exists_ae_abs_value_le_pow_mul_add_of_forall_ae_abs_sub_le (mu := mu) (lam := lam)
      (Lam := Lam) hθ hγ
  -- The ratio `σ` of the geometric decay along the radii `R / 8ʲ` is `8^(-β)`.
  set β := -Real.logb 8 σ
  have hβ : 0 < β := neg_pos.2 (Real.logb_neg (by norm_num) hσ0 hσ1)
  have h8β : (8 : ℝ) ^ (-β) = σ := by
    rw [neg_neg]
    exact Real.rpow_logb (by norm_num) (by norm_num) hσ0
  refine ⟨β, 8 ^ β * max 1 D, hβ, by positivity, ?_⟩
  intro Omega a u x₀ R M ρ A h ha happrox hA hle hext hρR
  -- For `ρ ≤ 0` the ball is empty.
  rcases le_or_gt ρ 0 with hρ0 | hρ
  · simp [ball_eq_empty.2 hρ0]
  have hR : 0 < R := hρ.trans_le hρR
  rcases lt_or_ge M 0 with hM | hM
  · -- `|u| ≤ M < 0` almost everywhere forces `Ω ∩ B(x₀, R)` to be null.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_right _ (ball_subset_ball hρR)) hle] with x hx
    exact absurd (abs_nonneg (W1p.value u x)) (by linarith)
  -- With `j = ⌊log₈ (R / ρ)⌋`, `8ʲ ≤ R / ρ < 8ʲ⁺¹`, so `ρ ≤ R / 8ʲ` and
  -- `σʲ = 8^β σʲ⁺¹ ≤ 8^β (ρ / R)^β`.
  set j := ⌊Real.logb 8 (R / ρ)⌋₊
  have hρj : ρ ≤ R / 8 ^ j := by
    rw [le_div_iff₀ (by positivity), mul_comm, ← le_div_iff₀ hρ]
    exact Real.pow_natFloor_logb_le_self (by norm_num) ((one_le_div hρ).2 hρR)
  have hσj : σ ^ j ≤ 8 ^ β * (ρ / R) ^ β := by
    have hσ1 : σ ^ (j + 1) ≤ (ρ / R) ^ β := by
      rw [← h8β, Real.rpow_pow_comm (by norm_num), ← inv_div, Real.inv_rpow (by positivity),
        ← Real.rpow_neg (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (Real.lt_pow_natFloor_logb_add_one (by norm_num) (div_pos hR hρ)).le (by linarith)
    calc σ ^ j = 8 ^ β * σ ^ (j + 1) := by
          rw [pow_succ, ← h8β, mul_comm, mul_assoc, ← Real.rpow_add (by norm_num), neg_add_cancel,
            Real.rpow_zero, mul_one]
      _ ≤ 8 ^ β * (ρ / R) ^ β := by gcongr
  have hY : M + D * R ^ γ * A ≤ max 1 D * (M + R ^ γ * A) := by
    have : 0 ≤ R ^ γ * A := by positivity
    nlinarith [le_max_left 1 D, le_max_right 1 D]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (inter_subset_inter_right _ (ball_subset_ball hρj))
    (hdecay h ha happrox hR hA hle hext j)] with x hx
  refine hx.trans ?_
  calc σ ^ j * (M + D * R ^ γ * A) ≤ (8 ^ β * (ρ / R) ^ β) * (max 1 D * (M + R ^ γ * A)) :=
        mul_le_mul hσj hY (by positivity) (by positivity)
    _ = _ := by ring

/-- **Splitting off the datum at every scale.** Let `n ≥ 1` and `q > 2` with `q > n`. There is
`K > 0`, depending only on `n`, `q` and the normalization of `mu`, such that the following holds.
Let `u ∈ H¹₀(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` against the test functions vanishing off `B(x₀, R)`,
with `F ∈ L^q(Ω ∩ B(x₀, R))`. Then for every `0 < s ≤ R` there is `g ∈ H¹₀(Ω)` solving the
homogeneous equation against the test functions vanishing off `B(x₀, s/2)` with
`|u - g| ≤ s^(1 - n/q) K ‖F‖_{L^q(Ω ∩ B(x₀, R))} / λ` on `Ω ∩ B(x₀, s/2)`. -/
private theorem exists_forall_exists_ae_abs_sub_le_divergence [Nonempty ι] {q : ℝ≥0}
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      u ∈ w1p0Submodule mu Omega 2 →
      MemLp F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, x ∉ ball x₀ R → W1p.value (v : W1p mu Omega 2) x = 0) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      ∀ s, 0 < s → s ≤ R → ∃ g : W1p mu Omega 2, g ∈ w1p0Submodule mu Omega 2 ∧
        (∀ v : W1p0 mu Omega 2,
          (∀ᵐ x ∂mu.restrict Omega, x ∉ ball x₀ (s / 2) → W1p.value (v : W1p mu Omega 2) x = 0) →
            energyFormH1 a 0 0 g (v : W1p mu Omega 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (s / 2)),
          |W1p.value u x - W1p.value g x| ≤ s ^ (1 - (Fintype.card ι : ℝ) / q) * (K *
            (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal /
              lam) := by
  obtain ⟨K, hK, hsplit⟩ :=
    exists_ae_abs_value_le_and_energyFormH1_sub_eq_zero (mu := mu) (lam := lam) (Lam := Lam) hq
      hqn
  refine ⟨K, hK, fun {Omega a F u x₀ R} h ha hu0 hF hu s hs hsR => ?_⟩
  have hlam : 0 < lam := h.pos
  have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ s ⊆
      (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R :=
    inter_subset_inter_right _ (ball_subset_ball hsR)
  -- `W` splits off the datum on `Ω ∩ B(x₀, s)`, and `g = u - W`.
  obtain ⟨W, hWb, hW⟩ := hsplit h ha (hF.mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun v hv => hu v (by
      filter_upwards [hv] with x hx hxR using hx fun hxs => hxR (ball_subset_ball hsR hxs)))
    hs
  -- The datum on the smaller ball has norm at most that on `B(x₀, R)`.
  have hNs : (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
      ball x₀ s))).toReal ≤
        (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal :=
    ENNReal.toReal_mono hF.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
  refine ⟨u - (W : W1p mu Omega 2), (w1p0Submodule mu Omega 2).toSubmodule.sub_mem hu0 W.2,
    hW, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hWb,
    ae_restrict_of_ae_restrict_of_subset inter_subset_left
      (W1p.value_sub_ae u (W : W1p mu Omega 2))] with x h1 h2
  rw [h2, Pi.sub_apply, sub_sub_cancel]
  refine h1.trans ?_
  calc _ ≤ K * s ^ (1 - (Fintype.card ι : ℝ) / q) *
      (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal /
        lam := by gcongr
    _ = _ := by ring

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

No regularity of `∂Ω` is assumed. This is
`TauCeti.PDE.exists_ae_abs_value_le_mul_div_rpow_mul_add_of_forall_ae_abs_sub_le` with
`γ = 1 - n/q`, the approximating solutions coming from splitting off the datum at every scale. -/
theorem
exists_ae_abs_value_le_mul_div_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff_divergence
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
  set γ : ℝ := 1 - (Fintype.card ι : ℝ) / q
  have hγ : 0 < γ := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hqn
  obtain ⟨K, hK, hsplit⟩ :=
    exists_forall_exists_ae_abs_sub_le_divergence (mu := mu) (lam := lam) (Lam := Lam) hq hqn
  obtain ⟨β, C, hβ, hC, hdecay⟩ :=
    exists_ae_abs_value_le_mul_div_rpow_mul_add_of_forall_ae_abs_sub_le
      (mu := mu) (lam := lam) (Lam := Lam) hθ hγ
  refine ⟨β, C * max 1 K, hβ, by positivity, ?_⟩
  intro Omega a F u x₀ R M ρ h ha hu0 hF hu hle hext hρR
  set N := (eLpNorm F q (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal
  have hlam : 0 < lam := h.pos
  -- For `ρ ≤ 0` the ball is empty.
  rcases le_or_gt ρ 0 with hρ0 | hρ
  · simp [ball_eq_empty.2 hρ0]
  have hR : 0 < R := hρ.trans_le hρR
  rcases lt_or_ge M 0 with hM | hM
  · -- `|u| ≤ M < 0` almost everywhere forces `Ω ∩ B(x₀, R)` to be null.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_right _ (ball_subset_ball hρR)) hle] with x hx
    exact absurd (abs_nonneg (W1p.value u x)) (by linarith)
  filter_upwards [hdecay h ha (hsplit h ha hu0 hF hu) (by positivity) hle hext hρR] with x hx
  refine hx.trans ?_
  have hY : M + R ^ γ * (K * N / lam) ≤ max 1 K * (M + R ^ γ * N / lam) := by
    rw [show R ^ γ * (K * N / lam) = K * (R ^ γ * N / lam) by ring]
    have : 0 ≤ R ^ γ * N / lam := by positivity
    nlinarith [le_max_left 1 K, le_max_right 1 K]
  calc C * (ρ / R) ^ β * (M + R ^ γ * (K * N / lam))
      ≤ C * (ρ / R) ^ β * (max 1 K * (M + R ^ γ * N / lam)) := by gcongr
    _ = _ := by ring

end PDE

end TauCeti
