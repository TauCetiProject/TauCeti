/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.DirichletProblem
public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.PDE.Regularity.Interior.Families
import TauCeti.Analysis.Sobolev.Wkp.Measurable
import TauCeti.Topology.Instances.Matrix

/-!
# Interior `H²` regularity in space for parabolic equations

Let `Ω ⊆ ℝⁿ` be open and let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` have time-independent coefficients,
with `a` uniformly elliptic on `Ω` and symmetric, and `b`, `c` bounded and measurable. Let `u` be a
weak solution of

`∂ₜu + L u = F` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, `u(t₀) = u₀`,

with `F ∈ L²(t₀, t₁; L²(Ω))` and `u₀ ∈ H¹₀(Ω)`. By
`TauCeti.PDE.exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm`, the time derivative
`∂ₜu` lies in `L²(t₀, t₁; L²(Ω))`. This file proves that `u` gains one more derivative in space
where `a` is Lipschitz, in two forms:

* on every ball `B(x₀, r)` with `B(x₀, 2 r) ⊆ Ω` on which `a` is Lipschitz,
  `u ∈ L²(t₀, t₁; H²(B(x₀, r)))`
  (`TauCeti.PDE.exists_memLp_lowerOrder_eq_restrictL_ball_of_isSymm`), where `a` need not be
  Lipschitz away from the ball;
* if `a` is locally Lipschitz on `Ω`, then `u ∈ L²(t₀, t₁; H²_loc(Ω))`: on every open `V` whose
  closure is compact and contained in `Ω`, `u ∈ L²(t₀, t₁; H²(V))`
  (`TauCeti.PDE.exists_memLp_lowerOrder_eq_restrictL_of_isSymm`). With the time regularity above,
  this is the interior form of the improved regularity of Evans, §7.1.3, Theorem 5: the solution
  lies in `L^∞(t₀, t₁; H¹₀(Ω)) ∩ L²(t₀, t₁; H²_loc(Ω))` with `∂ₜu ∈ L²(t₀, t₁; L²(Ω))`.

No regularity of `∂Ω`, no boundedness of `Ω` and no sign condition on `c` is needed.

## The argument

For almost every `t`, the weak equation says that `u(t)` is a weak solution of the elliptic
equation

`-∂ᵢ(aⁱʲ ∂ⱼu(t)) + bⁱ ∂ᵢu(t) + c u(t) = F(t) - ∂ₜu(t)` in `Ω`,

whose right-hand side lies in `L²(Ω)`.

On balls, the interior `H²` estimate
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_ball_and_norm_le`) then puts the
restriction of `u(t)` to `B(x₀, r)` in `W^{2,2}(B(x₀, r))`, with norm at most a constant times
`‖F(t)‖ + ‖∂ₜu(t)‖ + ‖u(t)‖`, which is square integrable in `t`. These elements are chosen
measurably in `t`: their values in `L²(B(x₀, r))` are those of the restrictions of `u(t)`, which
depend measurably on `t`, and an element of `W^{2,2}(B(x₀, r))` is determined by its value
(`TauCeti.Wkp.aestronglyMeasurable_of_ae_value_eq`).

On a general `V`, the passage from a weak solution `(u, f)` of `L u = f` to its `H²(V)` extension
is a bounded linear operator by the closed graph theorem, and applying it to the pairs
`(u(t), F(t) - ∂ₜu(t))` gives the family
(`TauCeti.PDE.UniformlyEllipticOn.exists_memLp_lowerOrder_eq_restrictL_of_locallyLipschitzOn`).

The Lipschitz hypothesis on `a` cannot be dropped: a time-independent weak solution of the
elliptic equation is a weak solution of the parabolic one with `∂ₜu = 0`, and for the coefficient
with a jump of `TauCeti.Analysis.PDE.Regularity.JumpCoefficient` such solutions need not lie in
`H²` near the jump.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.3, Theorem 5, which proves global
  `H²` regularity for smooth coefficients and a smooth boundary from the same elliptic estimate,
  applied at almost every time.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace Filter
open scoped InnerProductSpace NNReal Topology ENNReal

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

variable {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {t₀ t₁ lam Lam beta gamma : ℝ}

/-- At every time at which the time derivative of a weak solution of `∂ₜu + L u = F` is the
function `d(t) ∈ L²(Ω)`, the solution is a weak solution of the elliptic equation
`L u(t) = F(t) - d(t)`. -/
private theorem energyFormH1_eq_integral_sub {F d : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p0 mu Omega 2} {u' : StrongDual ℝ (W1p0 mu Omega 2)}
    (heq : ∀ v : W1p0 mu Omega 2,
      u' v + energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        ⟪F, W1p0.valueL v⟫_ℝ)
    (hd : ∀ v : W1p0 mu Omega 2, u' v = ⟪d, W1p0.valueL v⟫_ℝ) (v : W1p0 mu Omega 2) :
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      ∫ x in Omega, (F - d) x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  have h : energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      ⟪F - d, W1p0.valueL v⟫_ℝ := by
    rw [inner_sub_left, ← hd v, ← heq v]
    ring
  rw [h, W1p0.valueL_apply, ← dirichletForcing_apply, dirichletForcing_apply_eq_setIntegral]

/-- **Interior `H²` regularity in space for the parabolic Dirichlet problem.** Let the coefficients
of `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be independent of time, with `a` uniformly elliptic on `Ω`
and symmetric almost everywhere, and `b`, `c` bounded and measurable. Let `u` be a weak solution of
`∂ₜu + L u = F` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, with forcing
`F ∈ L²(t₀, t₁; L²(Ω))`, whose continuous `L²(Ω)`-valued representative starts at `u₀ ∈ H¹₀(Ω)`.
If `B(x₀, 2 r) ⊆ Ω` and `x ↦ a(x)` is Lipschitz on `B(x₀, 2 r)` in the operator norm of its
bilinear forms, then `u ∈ L²(t₀, t₁; H²(B(x₀, r)))`: there is a square integrable curve `U` in
`W^{2,2}(B(x₀, r))` whose first-order part at almost every time `t` is the restriction of `u(t)`.

No regularity of `∂Ω`, no boundedness of `Ω` and no sign condition on `c` is assumed. -/
theorem exists_memLp_lowerOrder_eq_restrictL_ball_of_isSymm [DecidableEq ι]
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hell : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hsymm : ∀ᵐ x ∂mu.restrict Omega, (a x).IsSymm)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    {x₀ : EuclideanSpace ℝ ι} {r : ℝ} {K : ℝ≥0} (hr : 0 < r)
    (hball : Metric.ball x₀ (2 * r) ⊆ Omega)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) (Metric.ball x₀ (2 * r)))
    {F : ℝ → Lp ℝ 2 (mu.restrict Omega)} (hF : MemLp F 2 (volume.restrict (Ioo t₀ t₁)))
    {u₀ : W1p0 mu Omega 2} {u : ℝ → W1p0 mu Omega 2} {u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)}
    {w : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (h : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo t₀ t₁)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 a b c (u t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        ⟪F t, W1p0.valueL v⟫_ℝ)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w)
    (h₀ : w t₀ = W1p0.valueL u₀) :
    ∃ U : ℝ → Wkp mu ⟨Metric.ball x₀ r, Metric.isOpen_ball⟩ 2 2,
      MemLp U 2 (volume.restrict (Ioo t₀ t₁)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), Wkp.lowerOrder 1 (U t) = W1p.restrictL
        (SetLike.coe_subset_coe.mp ((Metric.ball_subset_ball (by linarith : r ≤ 2 * r)).trans
          hball)) (u t : W1p mu Omega 2) := by
  classical
  set B : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ r, Metric.isOpen_ball⟩
  set hBΩ : B ≤ Omega :=
    SetLike.coe_subset_coe.mp ((Metric.ball_subset_ball (by linarith : r ≤ 2 * r)).trans hball)
  -- The time derivative `d ∈ L²(t₀, t₁; L²(Ω))`.
  obtain ⟨d, hd, -, hu'd, -⟩ := exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm ha
    hb hc hell hsymm hb_bound hc_bound hF h hu hu' heq hw hae h₀
  -- At almost every time, the interior `H²` estimate on `B(x₀, r)` for `L u(t) = F(t) - d(t)`.
  obtain ⟨C, -, hH2⟩ := UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_ball_and_norm_le (ι := ι)
  set A := beta + 2 * K + C * Lam / r
  set A' := gamma + C * K / r + C * Lam / r ^ 2
  set bound : ℝ → ℝ := fun t => ‖(u t : W1p mu Omega 2)‖ + Fintype.card ι ^ 2 *
    ((‖F t - d t‖ + A * ‖(u t : W1p mu Omega 2)‖ + A' * ‖(u t : W1p mu Omega 2)‖) / lam)
  have hex : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∃ U : Wkp mu B 2 2,
      Wkp.lowerOrder 1 U = W1p.restrictL hBΩ (u t : W1p mu Omega 2) ∧ ‖U‖ ≤ bound t := by
    filter_upwards [heq, hu'd] with t ht hdt
    exact hH2 mu hr hball (hell.mono_set hball) hK
      (memLp_top_of_bound hb beta (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hb_bound))
      (memLp_top_of_bound hc gamma (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hc_bound))
      (ae_restrict_of_forall_mem measurableSet_ball fun x hx => hb_bound x (hball hx))
      (ae_restrict_of_forall_mem measurableSet_ball fun x hx =>
        (Real.norm_eq_abs (c x)).symm.trans_le (hc_bound x (hball hx)))
      (energyFormH1_eq_integral_sub ht hdt)
  -- A choice of these elements at every time, with the defining property almost everywhere.
  have hchoice : ∀ t, ∃ U : Wkp mu B 2 2, (∃ V : Wkp mu B 2 2,
      Wkp.lowerOrder 1 V = W1p.restrictL hBΩ (u t : W1p mu Omega 2) ∧ ‖V‖ ≤ bound t) →
      Wkp.lowerOrder 1 U = W1p.restrictL hBΩ (u t : W1p mu Omega 2) ∧ ‖U‖ ≤ bound t := fun t =>
    if hV : ∃ V : Wkp mu B 2 2, Wkp.lowerOrder 1 V = W1p.restrictL hBΩ (u t : W1p mu Omega 2) ∧
      ‖V‖ ≤ bound t then ⟨hV.choose, fun _ => hV.choose_spec⟩ else ⟨0, fun h' => absurd h' hV⟩
  choose U hU using hchoice
  replace hU : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
      Wkp.lowerOrder 1 (U t) = W1p.restrictL hBΩ (u t : W1p mu Omega 2) ∧ ‖U t‖ ≤ bound t :=
    hex.mono fun t ht => hU t ht
  refine ⟨U, MemLp.of_le (g := bound) ?_ ?_ (hU.mono fun t ht => ht.2.trans (Real.le_norm_self _)),
    hU.mono fun t ht => ht.1⟩
  · -- The bound is square integrable in time.
    have hu1 : MemLp (fun t => ‖(u t : W1p mu Omega 2)‖) 2 (volume.restrict (Ioo t₀ t₁)) :=
      ((w1p0Submodule mu Omega 2).toSubmodule.subtypeL.comp_memLp' hu).norm
    refine (hu1.add ((((hF.sub hd).norm.add (hu1.const_mul A)).add (hu1.const_mul A')).const_mul
      ((Fintype.card ι : ℝ) ^ 2 / lam))).ae_eq (.of_forall fun t => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, bound]
    ring
  · -- Measurability: the values of `U` are those of the restrictions of `u`.
    have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
    refine Wkp.aestronglyMeasurable_of_ae_value_eq ((W1p.valueL.comp ((W1p.restrictL hBΩ).comp
      (w1p0Submodule mu Omega 2).toSubmodule.subtypeL)).continuous.comp_aestronglyMeasurable
        hu.aestronglyMeasurable) ?_
    filter_upwards [hU] with t ht
    rw [Wkp.value_succ, ht.1]
    exact (Wkp.value_one (mu := mu) (Omega := B) (p := 2) _).trans (by simp)

/-- **Interior `H²` regularity in space for the parabolic Dirichlet problem** (Evans, §7.1.3,
Theorem 5, in its interior form). Let the coefficients of `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be
independent of time, with `a` uniformly elliptic on `Ω`, symmetric almost everywhere and locally
Lipschitz on `Ω` in the operator norm of its bilinear forms, and `b`, `c` bounded and measurable.
Let `u` be a weak solution of `∂ₜu + L u = F` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, with
forcing `F ∈ L²(t₀, t₁; L²(Ω))`, whose continuous `L²(Ω)`-valued representative starts at
`u₀ ∈ H¹₀(Ω)`. Then `u ∈ L²(t₀, t₁; H²_loc(Ω))`: on every open `V` whose closure is compact and
contained in `Ω` there is a family `t ↦ U(t) ∈ W^{2,2}(V)` in `L²(t₀, t₁)` whose first-order part
is the restriction of `u(t)` to `V` for almost every `t`. No regularity of `∂Ω`, no boundedness
of `Ω` and no sign condition on `c` is needed. -/
theorem exists_memLp_lowerOrder_eq_restrictL_of_isSymm [DecidableEq ι]
    (hell : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LocallyLipschitzOn (Omega : Set (EuclideanSpace ℝ ι)) fun x => matrixBilinearForm (a x))
    (hsymm : ∀ᵐ x ∂mu.restrict Omega, (a x).IsSymm)
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    {F : ℝ → Lp ℝ 2 (mu.restrict Omega)} (hF : MemLp F 2 (volume.restrict (Ioo t₀ t₁)))
    {u₀ : W1p0 mu Omega 2} {u : ℝ → W1p0 mu Omega 2} {u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)}
    {w : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (h : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo t₀ t₁)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 a b c (u t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        ⟪F t, W1p0.valueL v⟫_ℝ)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w)
    (h₀ : w t₀ = W1p0.valueL u₀)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ U : ℝ → Wkp mu V 2 2, MemLp U 2 (volume.restrict (Ioo t₀ t₁)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), Wkp.lowerOrder 1 (U t) =
        W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ))
          (u t : W1p mu Omega 2) := by
  have ha : AEStronglyMeasurable a (mu.restrict Omega) :=
    (continuousOn_of_continuousOn_matrixBilinearForm hK.continuousOn).aestronglyMeasurable
      Omega.isOpen.measurableSet
  -- The time derivative `d ∈ L²(t₀, t₁; L²(Ω))`; then `L u(t) = F(t) - d(t)` at almost every time.
  obtain ⟨d, hd, -, hu'd, -⟩ := exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm ha hb
    hc hell hsymm hb_bound hc_bound hF h hu hu' heq hw hae h₀
  have hbm : MemLp b ⊤ (mu.restrict Omega) := memLp_top_of_bound hb beta
    (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hb_bound)
  have hcm : MemLp c ⊤ (mu.restrict Omega) := memLp_top_of_bound hc gamma
    (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hc_bound)
  refine hell.exists_memLp_lowerOrder_eq_restrictL_of_locallyLipschitzOn hK hbm hcm
    (((w1p0Submodule mu Omega 2).toSubmodule.subtypeL).comp_memLp' hu) (hF.sub hd) ?_ hV hVΩ
  filter_upwards [heq, hu'd] with t ht ht' v
  rw [← dirichletForcing_apply_eq_setIntegral]
  simp only [Function.comp_apply, Submodule.subtypeL_apply, Pi.sub_apply, dirichletForcing_apply,
    inner_sub_left, W1p0.valueL_apply] at ht ht' ⊢
  linarith [ht v, ht' v]

end PDE

end TauCeti
