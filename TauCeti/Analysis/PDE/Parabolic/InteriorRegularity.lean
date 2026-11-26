/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.DirichletProblem
public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.Sobolev.Wkp.Gluing
import TauCeti.Analysis.Sobolev.Wkp.Measurable
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.Sets.Opens

/-!
# Interior `H²` regularity in space for parabolic equations

Let `Ω ⊆ ℝⁿ` be open and let `L(t) u = -∂ᵢ(aⁱʲ(t, ·) ∂ⱼu) + bⁱ(t, ·) ∂ᵢu + c(t, ·) u`, with
`a(t, ·)` uniformly elliptic on `Ω` and symmetric for every time `t ∈ [t₀, t₁]`, Lipschitz in
time (`|ηᵀ (a(t, x) - a(s, x)) ξ| ≤ L |t - s| ‖η‖ ‖ξ‖`, as when `∂ₜa` is bounded), and `b`, `c`
bounded and jointly measurable. Let `u` be a weak solution of

`∂ₜu + L(t) u = F` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, `u(t₀) = u₀`,

with `F ∈ L²(t₀, t₁; L²(Ω))` and `u₀ ∈ H¹₀(Ω)`. By
`TauCeti.PDE.exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm_of_lipschitz`, the time
derivative `∂ₜu` lies in `L²(t₀, t₁; L²(Ω))`. This file proves that `u` gains one more derivative
in space where `a` is Lipschitz in space uniformly in time, in two forms:

* on every ball `B(x₀, r)` with `B(x₀, 2 r) ⊆ Ω` on which every `a(t, ·)` is `K`-Lipschitz,
  `u ∈ L²(t₀, t₁; H²(B(x₀, r)))`
  (`TauCeti.PDE.exists_memLp_lowerOrder_eq_restrictL_ball_of_isSymm_of_lipschitz`), where `a`
  need not be Lipschitz in space away from the ball;
* if every point of `Ω` has a neighbourhood on which every `a(t, ·)` is `K`-Lipschitz, for one
  `K`, then `u ∈ L²(t₀, t₁; H²_loc(Ω))`: on every open `V` whose closure is compact and contained
  in `Ω`, `u ∈ L²(t₀, t₁; H²(V))`
  (`TauCeti.PDE.exists_memLp_lowerOrder_eq_restrictL_of_isSymm_of_lipschitz`). With the time
  regularity above, this is the interior form of the improved regularity of Evans, §7.1.3,
  Theorem 5: the solution lies in `L^∞(t₀, t₁; H¹₀(Ω)) ∩ L²(t₀, t₁; H²_loc(Ω))` with
  `∂ₜu ∈ L²(t₀, t₁; L²(Ω))`.

Time-independent coefficients are the case `L = 0`
(`TauCeti.PDE.exists_memLp_lowerOrder_eq_restrictL_ball_of_isSymm`,
`TauCeti.PDE.exists_memLp_lowerOrder_eq_restrictL_of_isSymm`), where the hypothesis on `a` is
local Lipschitz continuity on `Ω`.

No regularity of `∂Ω`, no boundedness of `Ω` and no sign condition on `c` is needed.

## The argument

For almost every `t`, the weak equation says that `u(t)` is a weak solution of the elliptic
equation

`-∂ᵢ(aⁱʲ(t, ·) ∂ⱼu(t)) + bⁱ(t, ·) ∂ᵢu(t) + c(t, ·) u(t) = F(t) - ∂ₜu(t)` in `Ω`,

whose right-hand side lies in `L²(Ω)`.

On balls, the interior `H²` estimate
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_ball_and_norm_le`) then puts the
restriction of `u(t)` to `B(x₀, r)` in `W^{2,2}(B(x₀, r))`, with norm at most a constant times
`‖F(t)‖ + ‖∂ₜu(t)‖ + ‖u(t)‖`. The constant depends on `a(t, ·)` only through `λ`, `Λ` and `K`,
so it is uniform in `t`, and the bound is square integrable in `t`. These elements are chosen
measurably in `t`: their values in `L²(B(x₀, r))` are those of the restrictions of `u(t)`, which
depend measurably on `t`, and an element of `W^{2,2}(B(x₀, r))` is determined by its value
(`TauCeti.Wkp.aestronglyMeasurable_of_ae_value_eq`).

On a general `V`, finitely many such balls cover the compact set `closure V`, and at almost every
time the elements of `W^{2,2}` on the balls glue to one on `V` (`TauCeti.Wkp.exists_glue`), with
norm at most the sum of theirs.

The Lipschitz hypothesis on `a` cannot be dropped: a time-independent weak solution of the
elliptic equation is a weak solution of the parabolic one with `∂ₜu = 0`, and for the coefficient
with a jump of `TauCeti.Analysis.PDE.Regularity.JumpCoefficient` such solutions need not lie in
`H²` near the jump.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.3, Theorem 5, which proves global
  `H²` regularity for smooth time-independent coefficients and a smooth boundary from the same
  elliptic estimate, applied at almost every time.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace Filter
open scoped InnerProductSpace NNReal Topology ENNReal Matrix

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {t₀ t₁ lam Lam beta gamma : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-- At every time at which the time derivative of a weak solution of `∂ₜu + L u = F` is the
function `d(t) ∈ L²(Ω)`, the solution is a weak solution of the elliptic equation
`L u(t) = F(t) - d(t)`. -/
private theorem energyFormH1_eq_integral_sub {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    {F d : Lp ℝ 2 (mu.restrict Omega)}
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

/-- If at almost every time some `U ∈ W^{2,2}(V)` extends the restriction of `u(t)` to `V`, with
norm at most `g(t)` for a square integrable `g`, then such elements can be chosen as a square
integrable family in time. -/
private theorem exists_memLp_of_ae_exists_norm_le {V : Opens (EuclideanSpace ℝ ι)}
    (hVΩ : V ≤ Omega) {u : ℝ → W1p0 mu Omega 2} (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    {g : ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (Ioo t₀ t₁)))
    (hex : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∃ U : Wkp mu V 2 2,
      Wkp.lowerOrder 1 U = W1p.restrictL hVΩ (u t : W1p mu Omega 2) ∧ ‖U‖ ≤ g t) :
    ∃ U : ℝ → Wkp mu V 2 2, MemLp U 2 (volume.restrict (Ioo t₀ t₁)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
        Wkp.lowerOrder 1 (U t) = W1p.restrictL hVΩ (u t : W1p mu Omega 2) := by
  classical
  -- A choice of these elements at every time, with the defining property almost everywhere.
  have hchoice : ∀ t, ∃ U : Wkp mu V 2 2, (∃ U' : Wkp mu V 2 2,
      Wkp.lowerOrder 1 U' = W1p.restrictL hVΩ (u t : W1p mu Omega 2) ∧ ‖U'‖ ≤ g t) →
      Wkp.lowerOrder 1 U = W1p.restrictL hVΩ (u t : W1p mu Omega 2) ∧ ‖U‖ ≤ g t := fun t =>
    if hU : ∃ U' : Wkp mu V 2 2, Wkp.lowerOrder 1 U' = W1p.restrictL hVΩ (u t : W1p mu Omega 2) ∧
      ‖U'‖ ≤ g t then ⟨hU.choose, fun _ => hU.choose_spec⟩ else ⟨0, fun h' => absurd h' hU⟩
  choose U hU using hchoice
  replace hU : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
      Wkp.lowerOrder 1 (U t) = W1p.restrictL hVΩ (u t : W1p mu Omega 2) ∧ ‖U t‖ ≤ g t :=
    hex.mono fun t ht => hU t ht
  refine ⟨U, MemLp.of_le hg ?_ (hU.mono fun t ht => ht.2.trans (Real.le_norm_self _)),
    hU.mono fun t ht => ht.1⟩
  -- Measurability: the values of `U` are those of the restrictions of `u`.
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  refine Wkp.aestronglyMeasurable_of_ae_value_eq ((W1p.valueL.comp ((W1p.restrictL hVΩ).comp
    (w1p0Submodule mu Omega 2).toSubmodule.subtypeL)).continuous.comp_aestronglyMeasurable
      hu.aestronglyMeasurable) ?_
  filter_upwards [hU] with t ht
  rw [Wkp.value_succ, ht.1]
  exact (Wkp.value_one (mu := mu) (Omega := V) (p := 2) _).trans (by simp)

section TimeDependent

variable {a : ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : ℝ → EuclideanSpace ℝ ι → ℝ}

/-- **Interior `H²` regularity in space on balls, for time-dependent coefficients.** Let the
coefficients of `L(t) u = -∂ᵢ(aⁱʲ(t, ·) ∂ⱼu) + bⁱ(t, ·) ∂ᵢu + c(t, ·) u` satisfy, for every
`t ∈ [t₀, t₁]`: `a(t, ·)` is measurable, uniformly elliptic on `Ω` and symmetric almost
everywhere, and `a` is `L`-Lipschitz in time; and let `b`, `c` be bounded and jointly measurable.
Let `u` be a weak solution of `∂ₜu + L(t) u = F` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`,
with forcing `F ∈ L²(t₀, t₁; L²(Ω))`, whose continuous `L²(Ω)`-valued representative starts at
`u₀ ∈ H¹₀(Ω)`. If `B(x₀, 2 r) ⊆ Ω` and every `x ↦ a(t, x)` is `K`-Lipschitz on `B(x₀, 2 r)` in
the operator norm of its bilinear forms, then `u ∈ L²(t₀, t₁; H²(B(x₀, r)))`: there is a square
integrable curve `U` in `W^{2,2}(B(x₀, r))` whose first-order part at almost every time `t` is
the restriction of `u(t)`.

No regularity of `∂Ω`, no boundedness of `Ω` and no sign condition on `c` is assumed. -/
theorem exists_memLp_lowerOrder_eq_restrictL_ball_of_isSymm_of_lipschitz [DecidableEq ι] {L : ℝ}
    (ha : ∀ t ∈ Icc t₀ t₁, AEStronglyMeasurable (a t) (mu.restrict Omega))
    (hell : ∀ t ∈ Icc t₀ t₁, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (a t) lam Lam)
    (hsymm : ∀ t ∈ Icc t₀ t₁, ∀ᵐ x ∂mu.restrict Omega, (a t x).IsSymm)
    (hLip : ∀ s ∈ Icc t₀ t₁, ∀ t ∈ Icc t₀ t₁, ∀ᵐ x ∂mu.restrict Omega,
      ∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ ((a t x - a s x) *ᵥ ξ)| ≤ L * |t - s| * ‖η‖ * ‖ξ‖)
    (hb : AEStronglyMeasurable (Function.uncurry b)
      ((volume.restrict (Ioo t₀ t₁)).prod (mu.restrict Omega)))
    (hc : AEStronglyMeasurable (Function.uncurry c)
      ((volume.restrict (Ioo t₀ t₁)).prod (mu.restrict Omega)))
    (hb_bound : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
      ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b t x‖ ≤ beta)
    (hc_bound : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
      ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c t x‖ ≤ gamma)
    {x₀ : EuclideanSpace ℝ ι} {r : ℝ} {K : ℝ≥0} (hr : 0 < r)
    (hball : Metric.ball x₀ (2 * r) ⊆ Omega)
    (hK : ∀ t ∈ Icc t₀ t₁,
      LipschitzOnWith K (fun x => matrixBilinearForm (a t x)) (Metric.ball x₀ (2 * r)))
    {F : ℝ → Lp ℝ 2 (mu.restrict Omega)} (hF : MemLp F 2 (volume.restrict (Ioo t₀ t₁)))
    {u₀ : W1p0 mu Omega 2} {u : ℝ → W1p0 mu Omega 2} {u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)}
    {w : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (h : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo t₀ t₁)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 (a t) (b t) (c t) (u t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        ⟪F t, W1p0.valueL v⟫_ℝ)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w)
    (h₀ : w t₀ = W1p0.valueL u₀) :
    ∃ U : ℝ → Wkp mu ⟨Metric.ball x₀ r, Metric.isOpen_ball⟩ 2 2,
      MemLp U 2 (volume.restrict (Ioo t₀ t₁)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), Wkp.lowerOrder 1 (U t) = W1p.restrictL
        (SetLike.coe_subset_coe.mp ((Metric.ball_subset_ball (by linarith : r ≤ 2 * r)).trans
          hball)) (u t : W1p mu Omega 2) := by
  -- The time derivative `d ∈ L²(t₀, t₁; L²(Ω))`.
  obtain ⟨d, hd, -, hu'd, -⟩ :=
    exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm_of_lipschitz ha hell hsymm hLip
      hb hc hb_bound hc_bound hF h hu hu' heq hw hae h₀
  -- At almost every time, the interior `H²` estimate on `B(x₀, r)` for `L(t) u(t) = F(t) - d(t)`,
  -- with a constant independent of `t`.
  obtain ⟨C, -, hH2⟩ := UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_ball_and_norm_le (ι := ι)
  set A := beta + 2 * K + C * Lam / r
  set A' := gamma + C * K / r + C * Lam / r ^ 2
  have hI : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), t ∈ Icc t₀ t₁ :=
    (ae_restrict_mem measurableSet_Ioo).mono fun _ ht => Ioo_subset_Icc_self ht
  have hu1 : MemLp (fun t => ‖(u t : W1p mu Omega 2)‖) 2 (volume.restrict (Ioo t₀ t₁)) :=
    ((w1p0Submodule mu Omega 2).toSubmodule.subtypeL.comp_memLp' hu).norm
  refine exists_memLp_of_ae_exists_norm_le _ hu (g := fun t => ‖(u t : W1p mu Omega 2)‖ +
      Fintype.card ι ^ 2 * ((‖F t - d t‖ + A * ‖(u t : W1p mu Omega 2)‖ +
        A' * ‖(u t : W1p mu Omega 2)‖) / lam)) ?_ ?_
  · -- The bound is square integrable in time.
    refine (hu1.add ((((hF.sub hd).norm.add (hu1.const_mul A)).add (hu1.const_mul A')).const_mul
      ((Fintype.card ι : ℝ) ^ 2 / lam))).ae_eq (.of_forall fun t => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  filter_upwards [heq, hu'd, hI, hb.prodMk_left, hc.prodMk_left, hb_bound, hc_bound]
    with t ht hdt htI hbt hct hbt' hct'
  exact hH2 mu hr hball ((hell t htI).mono_set hball) (hK t htI)
    (memLp_top_of_bound hbt beta (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hbt'))
    (memLp_top_of_bound hct gamma (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hct'))
    (ae_restrict_of_forall_mem measurableSet_ball fun x hx => hbt' x (hball hx))
    (ae_restrict_of_forall_mem measurableSet_ball fun x hx =>
      (Real.norm_eq_abs (c t x)).symm.trans_le (hct' x (hball hx)))
    (energyFormH1_eq_integral_sub ht hdt)

/-- **Interior `H²` regularity in space for the parabolic Dirichlet problem with time-dependent
coefficients** (Evans, §7.1.3, Theorem 5, in its interior form). Let the coefficients of
`L(t) u = -∂ᵢ(aⁱʲ(t, ·) ∂ⱼu) + bⁱ(t, ·) ∂ᵢu + c(t, ·) u` satisfy, for every `t ∈ [t₀, t₁]`:
`a(t, ·)` is uniformly elliptic on `Ω` and symmetric almost everywhere, `a` is `L`-Lipschitz in
time, and `a` is locally Lipschitz in space uniformly in time: every point of `Ω` has a
neighbourhood on which every `x ↦ a(t, x)` is `K`-Lipschitz, for one `K`, in the operator norm of
its bilinear forms. Let `b`, `c` be bounded and jointly measurable. Let `u` be a weak solution of
`∂ₜu + L(t) u = F` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, with forcing
`F ∈ L²(t₀, t₁; L²(Ω))`, whose continuous `L²(Ω)`-valued representative starts at
`u₀ ∈ H¹₀(Ω)`. Then `u ∈ L²(t₀, t₁; H²_loc(Ω))`: on every open `V` whose closure is compact and
contained in `Ω` there is a family `t ↦ U(t) ∈ W^{2,2}(V)` in `L²(t₀, t₁)` whose first-order part
is the restriction of `u(t)` to `V` for almost every `t`. No regularity of `∂Ω`, no boundedness
of `Ω` and no sign condition on `c` is needed. -/
theorem exists_memLp_lowerOrder_eq_restrictL_of_isSymm_of_lipschitz [DecidableEq ι] {L : ℝ}
    (hell : ∀ t ∈ Icc t₀ t₁, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (a t) lam Lam)
    (hK : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ∃ K : ℝ≥0, ∃ s ∈ 𝓝 x, ∀ t ∈ Icc t₀ t₁,
      LipschitzOnWith K (fun y => matrixBilinearForm (a t y)) s)
    (hsymm : ∀ t ∈ Icc t₀ t₁, ∀ᵐ x ∂mu.restrict Omega, (a t x).IsSymm)
    (hLip : ∀ s ∈ Icc t₀ t₁, ∀ t ∈ Icc t₀ t₁, ∀ᵐ x ∂mu.restrict Omega,
      ∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ ((a t x - a s x) *ᵥ ξ)| ≤ L * |t - s| * ‖η‖ * ‖ξ‖)
    (hb : AEStronglyMeasurable (Function.uncurry b)
      ((volume.restrict (Ioo t₀ t₁)).prod (mu.restrict Omega)))
    (hc : AEStronglyMeasurable (Function.uncurry c)
      ((volume.restrict (Ioo t₀ t₁)).prod (mu.restrict Omega)))
    (hb_bound : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
      ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b t x‖ ≤ beta)
    (hc_bound : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
      ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c t x‖ ≤ gamma)
    {F : ℝ → Lp ℝ 2 (mu.restrict Omega)} (hF : MemLp F 2 (volume.restrict (Ioo t₀ t₁)))
    {u₀ : W1p0 mu Omega 2} {u : ℝ → W1p0 mu Omega 2} {u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)}
    {w : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (h : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo t₀ t₁)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 (a t) (b t) (c t) (u t : W1p mu Omega 2) (v : W1p mu Omega 2) =
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
  classical
  -- Each `a(t, ·)` is locally Lipschitz, hence continuous and measurable, on `Ω`.
  have ha : ∀ t ∈ Icc t₀ t₁, AEStronglyMeasurable (a t) (mu.restrict Omega) := fun t ht =>
    (continuousOn_of_continuousOn_matrixBilinearForm (LocallyLipschitzOn.continuousOn
      fun x hx => let ⟨K, s, hs, hKs⟩ := hK x hx
        ⟨K, s, mem_nhdsWithin_of_mem_nhds hs, hKs t ht⟩)).aestronglyMeasurable
      Omega.isOpen.measurableSet
  -- Around each point of `closure V`, a ball of twice the radius lies in `Ω` and in a neighbourhood
  -- where `a` is Lipschitz in space uniformly in time.
  have hloc : ∀ x ∈ closure (V : Set (EuclideanSpace ℝ ι)), ∃ r > 0, ∃ K : ℝ≥0,
      Metric.ball x (2 * r) ⊆ Omega ∧ ∀ t ∈ Icc t₀ t₁,
        LipschitzOnWith K (fun y => matrixBilinearForm (a t y)) (Metric.ball x (2 * r)) := by
    intro x hx
    obtain ⟨K, s, hs, hKs⟩ := hK x (hVΩ hx)
    obtain ⟨ε, hε, hεs⟩ :=
      Metric.mem_nhds_iff.1 (Filter.inter_mem hs (Omega.isOpen.mem_nhds (hVΩ hx)))
    have h2 : 2 * (ε / 2) = ε := by ring
    refine ⟨ε / 2, by positivity, K, ?_, fun t ht => (hKs t ht).mono ?_⟩ <;> rw [h2]
    exacts [hεs.trans inter_subset_right, hεs.trans inter_subset_left]
  choose! r hr K hball hKr using hloc
  -- Finitely many of the balls `B(x, r(x))` cover `closure V`.
  obtain ⟨T, hT⟩ := hV.elim_nhds_subcover' (fun x _ => Metric.ball x (r x))
    fun x hx => Metric.ball_mem_nhds x (hr x hx)
  set B : T → Opens (EuclideanSpace ℝ ι) := fun i =>
    ⟨Metric.ball i.val.val (r i.val.val), Metric.isOpen_ball⟩
  have hcov : V ≤ ⨆ i, B i := Opens.le_iSup_iff_subset_iUnion.2 fun x hx =>
    let ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hT (subset_closure hx))
    mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  -- On each ball, `u ∈ L²(t₀, t₁; H²)`.
  choose U hUL hU using fun i : T =>
    exists_memLp_lowerOrder_eq_restrictL_ball_of_isSymm_of_lipschitz ha hell hsymm hLip hb hc
      hb_bound hc_bound (hr _ i.val.property) (hball _ i.val.property) (hKr _ i.val.property) hF
      h hu hu' heq hw hae h₀
  -- At almost every time, the elements of `W^{2,2}` on the balls glue to one on `V`.
  refine exists_memLp_of_ae_exists_norm_le _ hu (g := fun t => ∑ i, ‖U i t‖)
    (memLp_finsetSum _ fun i _ => (hUL i).norm) ?_
  filter_upwards [ae_all_iff.2 hU] with t ht
  obtain ⟨v, hv, hvn⟩ := Wkp.exists_lowerOrder_eq_restrictL_of_forall_lowerOrder_eq_restrictL
    (k := 1) _ _ hcov (u t : W1p mu Omega 2) (fun i => U i t) fun i => by
      rw [Wkp.restrictL_one]
      exact ht i
  rw [Wkp.restrictL_one] at hv
  exact ⟨v, hv, hvn⟩

end TimeDependent

section TimeIndependent

variable {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

/-- **Interior `H²` regularity in space on balls for the parabolic Dirichlet problem.** Let the
coefficients of `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be independent of time, with `a` uniformly
elliptic on `Ω` and symmetric almost everywhere, and `b`, `c` bounded and measurable. Let `u` be a
weak solution of `∂ₜu + L u = F` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, with forcing
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
          hball)) (u t : W1p mu Omega 2) :=
  exists_memLp_lowerOrder_eq_restrictL_ball_of_isSymm_of_lipschitz (a := fun _ => a)
    (b := fun _ => b) (c := fun _ => c) (L := 0) (fun _ _ => ha) (fun _ _ => hell)
    (fun _ _ => hsymm) (fun _ _ _ _ => ae_of_all _ fun _ _ _ => by simp)
    hb.comp_snd hc.comp_snd (ae_of_all _ fun _ => hb_bound) (ae_of_all _ fun _ => hc_bound) hr
    hball (fun _ _ => hK) hF h hu hu' heq hw hae h₀

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
          (u t : W1p mu Omega 2) :=
  exists_memLp_lowerOrder_eq_restrictL_of_isSymm_of_lipschitz (a := fun _ => a)
    (b := fun _ => b) (c := fun _ => c) (L := 0) (fun _ _ => hell)
    (fun x hx => let ⟨K, s, hs, hKs⟩ := hK hx
      ⟨K, s, nhdsWithin_eq_nhds.2 (Omega.isOpen.mem_nhds hx) ▸ hs, fun _ _ => hKs⟩)
    (fun _ _ => hsymm) (fun _ _ _ _ => ae_of_all _ fun _ _ _ => by simp)
    hb.comp_snd hc.comp_snd (ae_of_all _ fun _ => hb_bound) (ae_of_all _ fun _ => hc_bound) hF h
    hu hu' heq hw hae h₀ hV hVΩ

end TimeIndependent

end PDE

end TauCeti
