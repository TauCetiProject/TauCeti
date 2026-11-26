/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.LowerOrder
public import TauCeti.Analysis.PDE.Parabolic.Existence
import TauCeti.Analysis.PDE.Parabolic.EnergyEstimate.Basic
import TauCeti.Analysis.PDE.Parabolic.Rothe
import TauCeti.Analysis.PDE.Parabolic.TimeRegularity
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Pettis
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Existence and uniqueness for the parabolic Dirichlet problem in divergence form

Let `Ω ⊆ ℝⁿ` be open and let `L(t)` be the divergence-form operator

`L(t) u = -∂ᵢ(aⁱʲ(t, ·) ∂ⱼu) + bⁱ(t, ·) ∂ᵢu + c(t, ·) u`

with bounded measurable coefficients depending on time, uniformly elliptic with constants
`λ, Λ` for almost every `t`. This file solves the initial-boundary value problem

`∂ₜu + L(t) u = f` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, `u(t₀) = u₀`,

in its variational form: there is `u ∈ L²(t₀, t₁; H¹₀(Ω))` with

`∫_{t₀}^{t₁} (a_t(u(t), φ(t)) - ∫_Ω u(t) ∂ₜφ(t)) dt = ∫_{t₀}^{t₁} f(t)(φ(t)) dt + ∫_Ω u₀ φ(t₀)`

for every `C¹` curve `φ : ℝ → H¹₀(Ω)` with `φ(t₁) = 0`, where `a_t` is the energy form
`TauCeti.PDE.energyFormH1` of `L(t)`. The initial value enters only through the term
`∫_Ω u₀ φ(t₀)`; since the values of `H¹₀(Ω)` functions are dense in `L²(Ω)`
(`TauCeti.W1p0.denseRange_valueL_two`), this term determines `u₀`. As for the stationary problem
(`TauCeti/Analysis/PDE/DirichletProblem.lean`), the boundary condition is membership in
`H¹₀(Ω)`, so no regularity of `∂Ω` is assumed, and `Ω` need not be bounded.

The proof instantiates the abstract existence theorem
`TauCeti.exists_memLp_forall_setIntegral_eq_add_inner`, in the form
`TauCeti.exists_memLp_forall_setIntegral_eq_add_inner_of_ae_eq`, for `V = H¹₀(Ω)`,
`H = L²(Ω)`, with the value map `TauCeti.W1p0.valueL` as `V → H` and the bundled energy form
`TauCeti.PDE.energyFormH1L0` of `L(t)` as `A(t)`. Three hypotheses of that theorem have to be
checked.

* **Weak measurability in time.** For fixed `u, v ∈ H¹₀(Ω)`, the map `t ↦ a_t(u, v)` is the
  integral over `Ω` of a function of `(t, x)` that is jointly a.e. strongly measurable as soon
  as the coefficients are, so it is a.e. strongly measurable by Fubini's measurability
  statement `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`
  (`TauCeti.PDE.aestronglyMeasurable_energyFormH1`). This is why the
  coefficients are assumed jointly measurable in `(t, x)` rather than measurable in `x` for
  each `t`; no strong measurability of `t ↦ A(t)` in operator norm is needed, and in general it
  fails for `L^∞` coefficients.
* **Boundedness.** `‖a_t(u, v)‖ ≤ (Λ + |β| + |γ|) ‖u‖ ‖v‖`, from
  `TauCeti.PDE.UniformlyEllipticOn.norm_energyFormH1_le`.
* **Gårding's inequality.** With `-|γ| ≤ c`, the mass-floor form of Gårding's inequality,
  `TauCeti.PDE.UniformlyEllipticOn.garding_energyFormH1_self_of_mass_lower_bound`, gives
  `TauCeti.PDE.UniformlyEllipticOn.garding_energyFormH1_self_norm_of_norm_le`:

  `(λ/2) ‖u‖²_{H¹} - (λ/2 + |γ| + β²/(2λ)) ‖u‖²_{L²} ≤ a_t(u, u)`.

  No sign condition on `c` and no Poincaré inequality is needed: the abstract theorem absorbs
  the negative `L²` term by the substitution `u = e^{μ(t - t₀)} w`.

The forcing term may be any `f ∈ L²(t₀, t₁; H⁻¹(Ω))`, written as a square-integrable curve in
the dual of `H¹₀(Ω)`, and the initial value any `u₀ ∈ L²(Ω)`.

The variational solution is a **weak solution** in the sense of Evans, §7.1.1: its image in
`H⁻¹(Ω)` has a weak time derivative `u' ∈ L²(t₀, t₁; H⁻¹(Ω))` with

`u'(t)(v) + a_t(u(t), v) = f(t)(v)` for all `v ∈ H¹₀(Ω)` and almost every `t`,

and `t ↦ u(t) ∈ L²(Ω)` has a representative continuous on `[t₀, t₁]` taking the value `u₀` at
`t₀`. This is the abstract theorem `TauCeti.exists_hasWeakLineDerivOn_gelfandDual_of_ae_eq` for
the Gelfand triple `H¹₀(Ω) ↪ L²(Ω) ↪ H⁻¹(Ω)`. It needs two further facts: `H¹₀(Ω)` is
separable, as a subspace of the second-countable space of `L²` value-gradient jets
(`MeasureTheory.Lp.SecondCountableTopology`), and the value map has dense range
(`TauCeti.W1p0.denseRange_valueL_two`), so that the initial value is attained exactly. The weak
solution is **unique**: Gårding's inequality above holds with a nonnegative `L²` constant, so the
energy estimate `TauCeti.HasWeakLineDerivOn.norm_sq_add_mul_integral_le_of_gelfandDual` applies to
the difference of two weak solutions with the same initial value.

## Time regularity

When the coefficients do not depend on time and `a` is symmetric, a forcing in
`L²(t₀, t₁; L²(Ω))` and an initial value in `H¹₀(Ω)` give a solution with `∂ₜu ∈ L²(t₀, t₁; L²(Ω))`
that is continuous on `[t₀, t₁]` with values in `H¹₀(Ω)`, so in particular essentially bounded
there; Evans, §7.1.3, Theorem 5, proves the bounds on `∂ₜu` and `sup_t ‖u(t)‖_{H¹₀}`. This is the
abstract theorem
`TauCeti.HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_symm` for the
symmetric coercive part `-∂ᵢ(aⁱʲ ∂ⱼ ·) + λ/2`; the lower-order terms `⟪b, ∇u⟫ + c u`, a bounded
operator `H¹₀(Ω) → L²(Ω)` (`TauCeti.PDE.lowerOrderL`), and the mass shift
`λ/2 u` are moved into the `L²` forcing.

When the principal coefficient depends on time, is symmetric, and is Lipschitz in time,
`|ηᵀ (a(t, x) - a(s, x)) ξ| ≤ L |t - s| ‖η‖ ‖ξ‖` (as when `∂ₜa` is bounded), the same data give
`∂ₜu ∈ L²(t₀, t₁; L²(Ω))` and `u ∈ L^∞(t₀, t₁; H¹₀(Ω))`. This is the abstract theorem
`TauCeti.HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_lipschitz`, proved by
Rothe's method, for the symmetric coercive parts `-∂ᵢ(aⁱʲ(t, ·) ∂ⱼ ·) + λ/2`, which inherit the
Lipschitz bound from `a` (`TauCeti.PDE.abs_energyFormH1_sub_energyFormH1_le`). The drift and mass
may depend on time, jointly measurably in `(t, x)`; their contribution `⟪b(t), ∇u(t)⟫ + c(t) u(t)`
to the `L²` forcing is square integrable in time by Pettis' theorem
(`MeasureTheory.MemLp.clm_apply_of_forall_aestronglyMeasurable`).

## Main declarations

* `TauCeti.PDE.exists_memLp_forall_setIntegral_energyFormH1_eq_add_inner`: existence of a
  variational solution of the parabolic Dirichlet problem.
* `TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`: existence of a weak solution.
* `TauCeti.PDE.eqOn_of_hasWeakLineDerivOn_gelfandDual_energyFormH1` and
  `TauCeti.PDE.ae_eq_of_hasWeakLineDerivOn_gelfandDual_energyFormH1`: uniqueness of weak
  solutions, for the continuous `L²(Ω)`-valued representative at every time and for the
  `H¹₀(Ω)`-valued solution almost everywhere.
* `TauCeti.PDE.exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm`: time regularity,
  `∂ₜu ∈ L²(t₀, t₁; L²(Ω))` and `u ∈ C([t₀, t₁]; H¹₀(Ω))`, for time-independent coefficients with
  symmetric principal part.
* `TauCeti.PDE.exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm_of_lipschitz`: time
  regularity, `∂ₜu ∈ L²(t₀, t₁; L²(Ω))` and `u ∈ L^∞(t₀, t₁; H¹₀(Ω))`, for a symmetric principal
  part Lipschitz in time.
* `TauCeti.PDE.norm_sq_add_two_mul_integral_energyFormH1_eq_of_hasWeakLineDerivOn_gelfandDual`:
  the energy identity `‖u(t)‖² + 2 ∫ₛᵗ a_r(u, u) = ‖u(s)‖² + 2 ∫ₛᵗ f(u)` for weak solutions, and
  its unforced case
  `norm_sq_add_two_mul_integral_energyFormH1_eq_norm_sq_of_hasWeakLineDerivOn_gelfandDual`,
  `‖u(t)‖² + 2 ∫ₛᵗ a_r(u, u) = ‖u(s)‖²`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.1 and §7.1.2, Theorems 3 and 4,
  which prove existence of weak solutions of this problem by the Galerkin method, and uniqueness
  by the energy estimate; §7.1.3, Theorem 5, for the time regularity.
* J. Kačur, *Method of Rothe in Evolution Equations*, Teubner-Texte zur Mathematik **80**, Teubner,
  Leipzig, 1985, Chapter 2, for time-dependent coefficients.
* J.-L. Lions, *Équations différentielles opérationnelles et problèmes aux limites*,
  Grundlehren **111**, Springer, 1961, whose representation theorem underlies the abstract
  existence theorem consumed here.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

variable {a : ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : ℝ → EuclideanSpace ℝ ι → ℝ}
  {t₀ t₁ lam Lam beta gamma : ℝ}

/-- Wherever the energy densities of `L(t)` are essentially bounded, the energy forms of `L(t)`
are the values of a single family of bounded operators `H¹₀(Ω) → H⁻¹(Ω)`. -/
private theorem exists_ae_apply_eq_energyFormH1 {ν : Measure ℝ} (hcoeff : ∀ᵐ t ∂ν,
      MemLp (fun x => energyIntegrand (a t x) (b t x) (c t x)) ⊤ (mu.restrict Omega)) :
    ∃ A : ℝ → W1p0 mu Omega 2 →L[ℝ] StrongDual ℝ (W1p0 mu Omega 2),
      ∀ᵐ t ∂ν, ∀ u v : W1p0 mu Omega 2,
        A t u v = energyFormH1 (a t) (b t) (c t) (u : W1p mu Omega 2) (v : W1p mu Omega 2) := by
  classical
  refine ⟨fun t => if h : MemLp (fun x => energyIntegrand (a t x) (b t x) (c t x)) ⊤
    (mu.restrict Omega) then energyFormH1L0 h else 0, ?_⟩
  filter_upwards [hcoeff] with t h u v
  simp only [h, ↓reduceDIte, energyFormH1L0_apply]

section StandingHypotheses

variable [DecidableEq ι] (ht : t₀ < t₁)
  (ha : AEStronglyMeasurable (Function.uncurry a)
    ((volume.restrict (Ioo t₀ t₁)).prod (mu.restrict Omega)))
  (hb : AEStronglyMeasurable (Function.uncurry b)
    ((volume.restrict (Ioo t₀ t₁)).prod (mu.restrict Omega)))
  (hc : AEStronglyMeasurable (Function.uncurry c)
    ((volume.restrict (Ioo t₀ t₁)).prod (mu.restrict Omega)))
  (hell : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
    UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (a t) lam Lam)
  (hb_bound : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
    ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b t x‖ ≤ beta)
  (hc_bound : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
    ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c t x‖ ≤ gamma)

include ha hb hc hell hb_bound hc_bound

/-- Under the standing hypotheses on the coefficients, the energy densities of `L(t)` are
essentially bounded for almost every `t`. -/
private theorem ae_memLp_energyIntegrand :
    ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
      MemLp (fun x => energyIntegrand (a t x) (b t x) (c t x)) ⊤ (mu.restrict Omega) := by
  filter_upwards [ha.prodMk_left, hb.prodMk_left, hc.prodMk_left, hell, hb_bound, hc_bound]
    with t hat hbt hct hellt hbt' hct'
  exact memLp_energyIntegrand_of_bounds hellt.upper_nonneg hat hbt hct
    (fun _x hx eta xi => hellt.upper_bound hx eta xi) hbt' hct'

omit ha hb hc in
/-- Under the standing hypotheses on the coefficients, the energy forms of `L(t)` are bounded on
`H¹₀(Ω)` by `Λ + |β| + |γ|` for almost every `t`. -/
private theorem ae_norm_energyFormH1_le :
    ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ u v : W1p0 mu Omega 2,
      ‖energyFormH1 (a t) (b t) (c t) (u : W1p mu Omega 2) (v : W1p mu Omega 2)‖ ≤
        (Lam + |beta| + |gamma|) * (‖u‖ * ‖v‖) := by
  filter_upwards [hell, hb_bound, hc_bound] with t hellt hbt hct u v
  exact hellt.norm_energyFormH1_le
    (fun x hx => (hbt x hx).trans (le_abs_self _))
    (fun x hx => (hct x hx).trans (le_abs_self _)) (u : W1p mu Omega 2) (v : W1p mu Omega 2)

/-- Under the standing hypotheses on the coefficients, the energy forms of `L(t)` satisfy
Gårding's inequality on `H¹₀(Ω)` with the constants `λ/2` and `λ/2 + |γ| + β²/(2λ)` for almost
every `t`. -/
theorem ae_garding_energyFormH1 :
    ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      lam / 2 * ‖v‖ ^ 2 - (lam / 2 + |gamma| + beta ^ 2 / (2 * lam)) * ‖W1p0.valueL v‖ ^ 2 ≤
        energyFormH1 (a t) (b t) (c t) (v : W1p mu Omega 2) (v : W1p mu Omega 2) := by
  filter_upwards [ha.prodMk_left, hb.prodMk_left, hc.prodMk_left, hell, hb_bound, hc_bound]
    with t hat hbt hct hellt hbt' hct' v
  rw [W1p0.valueL_apply]
  exact hellt.garding_energyFormH1_self_norm_of_norm_le hat hbt hct hbt'
    (fun x hx => (hct' x hx).trans (le_abs_self _)) _

include ht in
/-- Under the standing hypotheses on the coefficients on a nondegenerate interval, the ellipticity
constants satisfy `0 < λ` and `0 ≤ Λ`, and the energy forms of `L(t)` are the values of a single
family of bounded operators `H¹₀(Ω) → H⁻¹(Ω)` for almost every `t`. -/
theorem exists_ae_apply_eq_energyFormH1_of_lt :
    0 < lam ∧ 0 ≤ Lam ∧ ∃ A : ℝ → W1p0 mu Omega 2 →L[ℝ] StrongDual ℝ (W1p0 mu Omega 2),
      ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ u v : W1p0 mu Omega 2,
        A t u v = energyFormH1 (a t) (b t) (c t) (u : W1p mu Omega 2) (v : W1p mu Omega 2) := by
  have : (ae (volume.restrict (Ioo t₀ t₁))).NeBot := ae_restrict_neBot.2 (by simpa using ht)
  refine ⟨hell.exists.elim fun _ h => h.pos, hell.exists.elim fun _ h => h.upper_nonneg, ?_⟩
  exact exists_ae_apply_eq_energyFormH1 (mu := mu) (Omega := Omega) (a := a) (b := b) (c := c)
    (ae_memLp_energyIntegrand ha hb hc hell hb_bound hc_bound)

include ht in
/-- **Existence for the parabolic Dirichlet problem.** Let the coefficients `a, b, c` of
`L(t) u = -∂ᵢ(aⁱʲ(t, ·) ∂ⱼu) + bⁱ(t, ·) ∂ᵢu + c(t, ·) u` be jointly a.e. strongly measurable on
`(t₀, t₁) × Ω`, and for almost every `t ∈ (t₀, t₁)` let `a(t, ·)` be uniformly elliptic on `Ω`
with constants `λ, Λ`, `‖b(t, ·)‖ ≤ β` and `‖c(t, ·)‖ ≤ γ` on `Ω`. Then for every forcing term
`f ∈ L²(t₀, t₁; H⁻¹(Ω))` and initial value `u₀ ∈ L²(Ω)` there is `u ∈ L²(t₀, t₁; H¹₀(Ω))` with

`∫_{t₀}^{t₁} (a_t(u(t), φ(t)) - ⟪u(t), ∂ₜφ(t)⟫_{L²(Ω)}) dt
  = ∫_{t₀}^{t₁} f(t)(φ(t)) dt + ⟪u₀, φ(t₀)⟫_{L²(Ω)}`

for every `C¹` curve `φ` in `H¹₀(Ω)` with `φ(t₁) = 0`. This is the variational form of
`∂ₜu + L(t) u = f` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, `u(t₀) = u₀`. No sign
condition on `c` and no regularity or boundedness of `Ω` is assumed. -/
theorem exists_memLp_forall_setIntegral_energyFormH1_eq_add_inner
    {f : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} (hf : MemLp f 2 (volume.restrict (Ioo t₀ t₁)))
    (u₀ : Lp ℝ 2 (mu.restrict Omega)) :
    ∃ u : ℝ → W1p0 mu Omega 2, MemLp u 2 (volume.restrict (Ioo t₀ t₁)) ∧
      ∀ φ : ℝ → W1p0 mu Omega 2, ContDiff ℝ 1 φ → φ t₁ = 0 →
        ∫ t in Ioo t₀ t₁, (energyFormH1 (a t) (b t) (c t) (u t : W1p mu Omega 2)
            (φ t : W1p mu Omega 2) -
          ⟪W1p0.valueL (u t), W1p0.valueL (deriv φ t)⟫_ℝ) =
        (∫ t in Ioo t₀ t₁, f t (φ t)) + ⟪u₀, W1p0.valueL (φ t₀)⟫_ℝ := by
  -- The energy form of `L(t)`, as a bounded operator `H¹₀(Ω) → H⁻¹(Ω)` for almost every `t`.
  -- `have` then `obtain`: destructuring the application directly times out in elaboration.
  have hA := exists_ae_apply_eq_energyFormH1_of_lt ht ha hb hc hell hb_bound hc_bound
  obtain ⟨hlam, -, A, hA_apply⟩ := hA
  -- `by exact` postpones Gårding's inequality until the other arguments have fixed `B`, `α`
  -- and `ι`; elaborated eagerly as a plain term, it times out in unification.
  exact exists_memLp_forall_setIntegral_eq_add_inner_of_ae_eq W1p0.valueL ht.le hA_apply
    (fun u v => aestronglyMeasurable_energyFormH1 ha hb hc _ _)
    (ae_norm_energyFormH1_le (mu := mu) hell hb_bound hc_bound)
    (half_pos hlam) (by exact ae_garding_energyFormH1 ha hb hc hell hb_bound hc_bound) hf u₀

include ht in
/-- **Weak solutions of the parabolic Dirichlet problem.** Under the hypotheses of
`TauCeti.PDE.exists_memLp_forall_setIntegral_energyFormH1_eq_add_inner`, for every forcing term
`f ∈ L²(t₀, t₁; H⁻¹(Ω))` and initial value `u₀ ∈ L²(Ω)` there is a weak solution of
`∂ₜu + L(t) u = f` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, `u(t₀) = u₀`: a function
`u ∈ L²(t₀, t₁; H¹₀(Ω))` whose image in `H⁻¹(Ω)` has a weak time derivative
`u' ∈ L²(t₀, t₁; H⁻¹(Ω))` with

`u'(t)(v) + a_t(u(t), v) = f(t)(v)` for all `v ∈ H¹₀(Ω)`, for almost every `t`,

and such that `t ↦ u(t) ∈ L²(Ω)` has a representative `w` continuous on `[t₀, t₁]` with
`w(t₀) = u₀`. By `TauCeti.PDE.ae_eq_of_hasWeakLineDerivOn_gelfandDual_energyFormH1` this weak
solution is unique. -/
theorem exists_hasWeakLineDerivOn_gelfandDual_energyFormH1
    {f : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} (hf : MemLp f 2 (volume.restrict (Ioo t₀ t₁)))
    (u₀ : Lp ℝ 2 (mu.restrict Omega)) :
    ∃ u : ℝ → W1p0 mu Omega 2, ∃ u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2),
      ∃ w : ℝ → Lp ℝ 2 (mu.restrict Omega),
      MemLp u 2 (volume.restrict (Ioo t₀ t₁)) ∧ MemLp u' 2 (volume.restrict (Ioo t₀ t₁)) ∧
      HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
        (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
          (W1p0.valueL (u t))) u' 1 ∧
      (∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
        u' t v + energyFormH1 (a t) (b t) (c t) (u t : W1p mu Omega 2) (v : W1p mu Omega 2) =
          f t v) ∧
      ContinuousOn w (Icc t₀ t₁) ∧
      (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w ∧ w t₀ = u₀ := by
  -- `have` then `obtain`: destructuring the application directly times out in elaboration.
  have hA := exists_ae_apply_eq_energyFormH1_of_lt ht ha hb hc hell hb_bound hc_bound
  obtain ⟨hlam, -, A, hA_apply⟩ := hA
  -- With `2 ≠ ∞` registered, instance search finds that `H¹₀(Ω)` is separable, as a subspace
  -- of a second-countable `L²` space; this makes `t ↦ A(t) u(t)` strongly measurable.
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  exact exists_hasWeakLineDerivOn_gelfandDual_of_ae_eq W1p0.denseRange_valueL_two ht.le hA_apply
    (fun u v => aestronglyMeasurable_energyFormH1 ha hb hc _ _)
    (ae_norm_energyFormH1_le (mu := mu) hell hb_bound hc_bound)
    (half_pos hlam)
    (ae_garding_energyFormH1 ha hb hc hell hb_bound hc_bound) hf u₀

include ht in
/-- Two weak solutions of the parabolic Dirichlet problem, in the form of
`TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`, satisfy the hypotheses of the
abstract uniqueness theorems `TauCeti.HasWeakLineDerivOn.eqOn_of_gelfandDual` and
`TauCeti.HasWeakLineDerivOn.ae_eq_of_gelfandDual` for operators `A(t)` representing the energy
forms, with the Gårding constants `λ/2 > 0` and `λ/2 + |γ| + β²/(2λ) ≥ 0`. -/
private theorem exists_garding_and_eq_of_energyFormH1
    {f : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} {u₁ u₂ : ℝ → W1p0 mu Omega 2}
    {u₁' u₂' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)}
    (heq₁ : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u₁' t v + energyFormH1 (a t) (b t) (c t) (u₁ t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        f t v)
    (heq₂ : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u₂' t v + energyFormH1 (a t) (b t) (c t) (u₂ t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        f t v) :
    ∃ A : ℝ → W1p0 mu Omega 2 →L[ℝ] StrongDual ℝ (W1p0 mu Omega 2),
      0 < lam / 2 ∧ 0 ≤ lam / 2 + |gamma| + beta ^ 2 / (2 * lam) ∧
      (∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
        lam / 2 * ‖v‖ ^ 2 - (lam / 2 + |gamma| + beta ^ 2 / (2 * lam)) * ‖W1p0.valueL v‖ ^ 2 ≤
          A t v v) ∧
      (∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), u₁' t + A t (u₁ t) = f t) ∧
      ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), u₂' t + A t (u₂ t) = f t := by
  -- `have` then `obtain`: destructuring the application directly times out in elaboration.
  have hA := exists_ae_apply_eq_energyFormH1_of_lt ht ha hb hc hell hb_bound hc_bound
  obtain ⟨hlam, -, A, hA_apply⟩ := hA
  refine ⟨A, half_pos hlam, by positivity, ?_, ?_, ?_⟩
  · filter_upwards [hA_apply, ae_garding_energyFormH1 ha hb hc hell hb_bound hc_bound]
      with t hAt hGt v
    rw [hAt]
    exact hGt v
  · filter_upwards [hA_apply, heq₁] with t hAt heqt
    ext v
    rw [add_apply, hAt, heqt]
  · filter_upwards [hA_apply, heq₂] with t hAt heqt
    ext v
    rw [add_apply, hAt, heqt]

/-- **Uniqueness for the parabolic Dirichlet problem, at every time.** Under the hypotheses on the
coefficients of `TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`, two weak
solutions of `∂ₜu + L(t) u = f`, `u = 0` on `(t₀, t₁) × ∂Ω`, whose continuous `L²(Ω)`-valued
representatives agree at `t₀` have the same continuous representative on all of `[t₀, t₁]`. No
sign condition on `c` is needed. -/
theorem eqOn_of_hasWeakLineDerivOn_gelfandDual_energyFormH1
    {f : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} {u₁ u₂ : ℝ → W1p0 mu Omega 2}
    {u₁' u₂' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} {w₁ w₂ : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (h₁ : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u₁ t))) u₁' 1)
    (h₂ : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u₂ t))) u₂' 1)
    (hu₁ : MemLp u₁ 2 (volume.restrict (Ioo t₀ t₁)))
    (hu₁' : MemLp u₁' 2 (volume.restrict (Ioo t₀ t₁)))
    (hu₂ : MemLp u₂ 2 (volume.restrict (Ioo t₀ t₁)))
    (hu₂' : MemLp u₂' 2 (volume.restrict (Ioo t₀ t₁)))
    (heq₁ : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u₁' t v + energyFormH1 (a t) (b t) (c t) (u₁ t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        f t v)
    (heq₂ : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u₂' t v + energyFormH1 (a t) (b t) (c t) (u₂ t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        f t v)
    (hw₁ : ContinuousOn w₁ (Icc t₀ t₁))
    (hae₁ : (fun t => W1p0.valueL (u₁ t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w₁)
    (hw₂ : ContinuousOn w₂ (Icc t₀ t₁))
    (hae₂ : (fun t => W1p0.valueL (u₂ t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w₂)
    (h₀ : w₁ t₀ = w₂ t₀) :
    EqOn w₁ w₂ (Icc t₀ t₁) := by
  rcases le_or_gt t₁ t₀ with h | ht
  · intro t hst
    rw [le_antisymm (hst.2.trans h) hst.1, h₀]
  obtain ⟨A, hα, hβ, hA, hA₁, hA₂⟩ :=
    exists_garding_and_eq_of_energyFormH1 ht ha hb hc hell hb_bound hc_bound heq₁ heq₂
  exact HasWeakLineDerivOn.eqOn_of_gelfandDual h₁ h₂ hu₁ hu₁' hu₂ hu₂' hα hβ hA hA₁ hA₂ hw₁ hae₁
    hw₂ hae₂ h₀

/-- **Uniqueness for the parabolic Dirichlet problem.** Under the hypotheses on the coefficients
of `TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`, two weak solutions of
`∂ₜu + L(t) u = f`, `u = 0` on `(t₀, t₁) × ∂Ω`, whose continuous `L²(Ω)`-valued representatives
agree at `t₀` agree as elements of `H¹₀(Ω)` for almost every `t ∈ (t₀, t₁)`. No sign condition on
`c` is needed. -/
theorem ae_eq_of_hasWeakLineDerivOn_gelfandDual_energyFormH1
    {f : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} {u₁ u₂ : ℝ → W1p0 mu Omega 2}
    {u₁' u₂' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} {w₁ w₂ : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (h₁ : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u₁ t))) u₁' 1)
    (h₂ : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u₂ t))) u₂' 1)
    (hu₁ : MemLp u₁ 2 (volume.restrict (Ioo t₀ t₁)))
    (hu₁' : MemLp u₁' 2 (volume.restrict (Ioo t₀ t₁)))
    (hu₂ : MemLp u₂ 2 (volume.restrict (Ioo t₀ t₁)))
    (hu₂' : MemLp u₂' 2 (volume.restrict (Ioo t₀ t₁)))
    (heq₁ : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u₁' t v + energyFormH1 (a t) (b t) (c t) (u₁ t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        f t v)
    (heq₂ : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u₂' t v + energyFormH1 (a t) (b t) (c t) (u₂ t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        f t v)
    (hw₁ : ContinuousOn w₁ (Icc t₀ t₁))
    (hae₁ : (fun t => W1p0.valueL (u₁ t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w₁)
    (hw₂ : ContinuousOn w₂ (Icc t₀ t₁))
    (hae₂ : (fun t => W1p0.valueL (u₂ t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w₂)
    (h₀ : w₁ t₀ = w₂ t₀) :
    u₁ =ᵐ[volume.restrict (Ioo t₀ t₁)] u₂ := by
  rcases le_or_gt t₁ t₀ with h | ht
  · simp [Ioo_eq_empty_of_le h, Filter.EventuallyEq]
  obtain ⟨A, hα, hβ, hA, hA₁, hA₂⟩ :=
    exists_garding_and_eq_of_energyFormH1 ht ha hb hc hell hb_bound hc_bound heq₁ heq₂
  exact HasWeakLineDerivOn.ae_eq_of_gelfandDual h₁ h₂ hu₁ hu₁' hu₂ hu₂' hα hβ hA hA₁ hA₂ hw₁ hae₁
    hw₂ hae₂ h₀

end StandingHypotheses

/-- **The energy identity for the parabolic Dirichlet problem.** Let `u` be a weak solution of
`∂ₜu + L(t) u = f` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, in the sense of
`TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`, with forcing
`f ∈ L²(t₀, t₁; H⁻¹(Ω))`, and let `w` be its continuous `L²(Ω)`-valued representative. Then for all
`s, t ∈ [t₀, t₁]`,

`‖w t‖² + 2 ∫ₛᵗ a_r(u(r), u(r)) dr = ‖w s‖² + 2 ∫ₛᵗ f(r)(u(r)) dr`,

where `a_r` is the energy form of `L(r)`. No hypothesis on the coefficients is needed beyond the
equation itself. This is the abstract energy identity
`TauCeti.HasWeakLineDerivOn.norm_sq_add_two_mul_integral_eq_of_gelfandDual` for the equation tested
with `u(r)`. -/
theorem norm_sq_add_two_mul_integral_energyFormH1_eq_of_hasWeakLineDerivOn_gelfandDual
    {f : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} {u : ℝ → W1p0 mu Omega 2}
    {u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} {w : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (hd : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo t₀ t₁)))
    (hf : MemLp f 2 (volume.restrict (Ioo t₀ t₁)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 (a t) (b t) (c t) (u t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        f t v)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w)
    {s t : ℝ} (hs : s ∈ Icc t₀ t₁) (ht : t ∈ Icc t₀ t₁) :
    ‖w t‖ ^ 2 + 2 * ∫ r in s..t,
        energyFormH1 (a r) (b r) (c r) (u r : W1p mu Omega 2) (u r : W1p mu Omega 2) =
      ‖w s‖ ^ 2 + 2 * ∫ r in s..t, f r (u r) := by
  refine hd.norm_sq_add_two_mul_integral_eq_of_gelfandDual hu hu' (hf.integrable_apply hu) ?_ hw
    hae hs ht
  -- Testing the equation with `u(r)` itself.
  filter_upwards [heq] with r hr using hr (u r)

/-- **The energy identity for the unforced parabolic Dirichlet problem.** Every weak solution of
`∂ₜu + L(t) u = 0` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, with continuous `L²(Ω)`-valued
representative `w`, satisfies `‖w t‖² + 2 ∫ₛᵗ a_r(u(r), u(r)) dr = ‖w s‖²` for all
`s, t ∈ [t₀, t₁]`. This is
`TauCeti.PDE.norm_sq_add_two_mul_integral_energyFormH1_eq_of_hasWeakLineDerivOn_gelfandDual` with
`f = 0`. -/
theorem norm_sq_add_two_mul_integral_energyFormH1_eq_norm_sq_of_hasWeakLineDerivOn_gelfandDual
    {u : ℝ → W1p0 mu Omega 2} {u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)}
    {w : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (hd : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo t₀ t₁)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 (a t) (b t) (c t) (u t : W1p mu Omega 2) (v : W1p mu Omega 2) = 0)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w)
    {s t : ℝ} (hs : s ∈ Icc t₀ t₁) (ht : t ∈ Icc t₀ t₁) :
    ‖w t‖ ^ 2 + 2 * ∫ r in s..t,
        energyFormH1 (a r) (b r) (c r) (u r : W1p mu Omega 2) (u r : W1p mu Omega 2) =
      ‖w s‖ ^ 2 := by
  have h := norm_sq_add_two_mul_integral_energyFormH1_eq_of_hasWeakLineDerivOn_gelfandDual
    (a := a) (b := b) (c := c) (f := fun _ => 0) hd hu hu'
    (memLp_const (0 : StrongDual ℝ (W1p0 mu Omega 2))) heq hw hae hs ht
  simpa using h

/-! ### Time regularity for time-independent symmetric principal coefficients -/

section TimeRegularity

variable {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

/-- Gårding's inequality for the symmetric part `-∂ᵢ(aⁱʲ ∂ⱼ ·) + λ/2`:
`λ/2 ‖v‖²_{H¹} ≤ ∫ ⟨a ∇v, ∇v⟩ + λ/2 ‖v‖²_{L²}` on `H¹₀(Ω)`. -/
private theorem le_energyFormH1_add_inner [DecidableEq ι]
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hell : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (v : W1p0 mu Omega 2) :
    lam / 2 * ‖v‖ ^ 2 ≤ energyFormH1 a 0 0 (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
      lam / 2 * ⟪W1p0.valueL v, W1p0.valueL v⟫_ℝ := by
  have hG := hell.garding_energyFormH1_self ha aestronglyMeasurable_const
    aestronglyMeasurable_const (b := 0) (c := 0) (beta := 0) (gamma := 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => le_rfl) (v : W1p mu Omega 2)
  have hn := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq (v : W1p mu Omega 2)
  have hi : ⟪W1p0.valueL v, W1p0.valueL v⟫_ℝ = ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, W1p0.valueL_apply]
  simp only [zero_pow two_ne_zero, zero_div, zero_mul, sub_zero] at hG
  rw [← Submodule.norm_coe v, hn, hi]
  linarith

/-- For a measurable principal coefficient, uniformly elliptic on `Ω` and symmetric almost
everywhere, the shifted principal part `A₀ = -∂ᵢ(aⁱʲ ∂ⱼ ·) + λ/2` is a bounded operator
`H¹₀(Ω) → H⁻¹(Ω)` that is symmetric and coercive with constant `λ/2`. -/
private theorem exists_principal_symm_coercive [DecidableEq ι]
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hell : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hsymm : ∀ᵐ x ∂mu.restrict Omega, (a x).IsSymm) :
    ∃ A₀ : W1p0 mu Omega 2 →L[ℝ] StrongDual ℝ (W1p0 mu Omega 2),
      (∀ v w : W1p0 mu Omega 2, A₀ v w = energyFormH1 a 0 0 (v : W1p mu Omega 2)
        (w : W1p mu Omega 2) + lam / 2 * ⟪W1p0.valueL v, W1p0.valueL w⟫_ℝ) ∧
      (∀ v w : W1p0 mu Omega 2, A₀ v w = A₀ w v) ∧
      ∀ v : W1p0 mu Omega 2, lam / 2 * ‖v‖ ^ 2 ≤ A₀ v v := by
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : W1p0 mu Omega 2 →L[ℝ] StrongDual ℝ (W1p0 mu Omega 2),
      ∀ v w : W1p0 mu Omega 2, A₀ v w = energyFormH1 a 0 0 (v : W1p mu Omega 2)
        (w : W1p mu Omega 2) + lam / 2 * ⟪W1p0.valueL v, W1p0.valueL w⟫_ℝ :=
    ⟨(lam / 2) • ((W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual ∘L
      W1p0.valueL) + energyFormH1L0 (hell.memLp_energyIntegrand_zero_zero ha), fun v w => by
        simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.gelfandDual_apply, energyFormH1L0_apply, smul_eq_mul, Pi.zero_def]
        ring⟩
  refine ⟨A₀, hA₀, fun v w => ?_, fun v => (le_energyFormH1_add_inner ha hell v).trans_eq
    (hA₀ v v).symm⟩
  exact (hA₀ v w).trans <| (congrArg₂ (· + ·)
    (energyFormH1_comm_of_isSymm_ae (c := 0) hsymm (v : W1p mu Omega 2) (w : W1p mu Omega 2))
    (congrArg (lam / 2 * ·) (real_inner_comm _ _))).trans (hA₀ w v).symm

/-- On `H¹₀(Ω)`, pointwise bounded measurable lower-order coefficients contribute the `L²`
pairing of `TauCeti.PDE.lowerOrderL`, restricted to `H¹₀(Ω)`, with the value. -/
private theorem exists_energyFormH1_eq_principal_add_inner
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) :
    ∃ M : W1p0 mu Omega 2 →L[ℝ] Lp ℝ 2 (mu.restrict Omega), ∀ v w : W1p0 mu Omega 2,
      energyFormH1 a b c (v : W1p mu Omega 2) (w : W1p mu Omega 2) =
        energyFormH1 a 0 0 (v : W1p mu Omega 2) (w : W1p mu Omega 2) +
          ⟪M v, W1p0.valueL w⟫_ℝ := by
  have hbm : MemLp b ⊤ (mu.restrict Omega) := memLp_top_of_bound hb beta
    (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hb_bound)
  have hcm : MemLp c ⊤ (mu.restrict Omega) := memLp_top_of_bound hc gamma
    (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hc_bound)
  exact ⟨(lowerOrderL hbm hcm).comp (w1p0Submodule mu Omega 2).toSubmodule.subtypeL,
    fun v w => energyFormH1_eq_principal_add_inner_lowerOrderL ha hbm hcm _ w⟩

/-- **Time regularity for the parabolic Dirichlet problem** (Evans, §7.1.3, Theorem 5). Let the
coefficients of `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be independent of time, with `a` uniformly
elliptic on `Ω` and symmetric almost everywhere, and `b`, `c` bounded and measurable. Let `u` be a
weak solution of `∂ₜu + L u = F` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, with forcing
`F ∈ L²(t₀, t₁; L²(Ω))`, whose continuous `L²(Ω)`-valued representative starts at `u₀ ∈ H¹₀(Ω)`.
Then `∂ₜu ∈ L²(t₀, t₁; L²(Ω))`: the `L²(Ω)`-valued map `t ↦ u(t)` has a weak time derivative
`d ∈ L²(t₀, t₁; L²(Ω))`, which represents `u'` through the `L²(Ω)` pairing, and `u` has a
representative continuous on `[t₀, t₁]` with values in `H¹₀(Ω)` that starts at `u₀`; in particular
`u ∈ L^∞(t₀, t₁; H¹₀(Ω))`. No regularity of `∂Ω`, no continuity of `a`, no boundedness of `Ω` and
no sign condition on `c` is needed. -/
theorem exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm [DecidableEq ι]
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hell : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hsymm : ∀ᵐ x ∂mu.restrict Omega, (a x).IsSymm)
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
    (h₀ : w t₀ = W1p0.valueL u₀) :
    ∃ d : ℝ → Lp ℝ 2 (mu.restrict Omega), MemLp d 2 (volume.restrict (Ioo t₀ t₁)) ∧
      HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩ (fun t => W1p0.valueL (u t)) d 1 ∧
      (∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
        u' t v = ⟪d t, W1p0.valueL v⟫_ℝ) ∧
      ∃ v : ℝ → W1p0 mu Omega 2, ContinuousOn v (Icc t₀ t₁) ∧
        u =ᵐ[volume.restrict (Ioo t₀ t₁)] v ∧ v t₀ = u₀ := by
  have hlam : 0 < lam := hell.pos
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega) :=
    hell.memLp_energyIntegrand_zero_zero ha
  -- The symmetric coercive part `A₀ = -div(a ∇ ·) + λ/2`; the rest goes into the forcing.
  obtain ⟨A₀, hA₀, hsymm₀, hcoer⟩ := exists_principal_symm_coercive ha hell hsymm
  -- The lower-order terms, moved into the `L²` forcing `g = F - (⟪b, ∇u⟫ + c u) + (λ/2) u`.
  obtain ⟨M, hM⟩ := exists_energyFormH1_eq_principal_add_inner hcoeff hb hc hb_bound hc_bound
  have hinj : Function.Injective (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)) :=
    fun v w hvw => Subtype.ext (W1p.ext_value (by simpa only [W1p0.valueL_apply] using hvw))
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have hg : MemLp (fun t => F t - M (u t) + (lam / 2) • W1p0.valueL (u t)) 2
      (volume.restrict (Ioo t₀ t₁)) :=
    (hF.sub (M.comp_memLp' hu)).add
      (((W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).comp_memLp' hu).const_smul (lam / 2))
  -- The equation for the symmetric part, with the lower-order terms in the forcing.
  have heq₀ : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), u' t + A₀ (u t) =
      (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (F t - M (u t) + (lam / 2) • W1p0.valueL (u t)) := by
    filter_upwards [heq] with t ht
    ext v
    simp only [add_apply, ContinuousLinearMap.gelfandDual_apply, inner_add_left, inner_sub_left,
      real_inner_smul_left, hA₀]
    linarith [ht v, hM (u t) v]
  obtain ⟨d, v, hd, hdd, hu'd, hv, huv, hv₀, -⟩ :=
    HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_symm
      hinj hsymm₀ (half_pos hlam) hcoer hg h hu hu' heq₀ hw hae h₀
  refine ⟨d, hd, hdd, ?_, v, hv, huv, hv₀⟩
  filter_upwards [hu'd] with t ht φ
  exact (DFunLike.congr_fun ht φ).trans (ContinuousLinearMap.gelfandDual_apply _ _ _)

end TimeRegularity

/-! ### Time regularity for time-dependent symmetric principal coefficients -/

section TimeDependent

open scoped Matrix

attribute [local instance] W1p0.instStrongDualNormedAddCommGroup W1p0.instStrongDualNormedSpace

/-- With drift and mass jointly measurable in `(t, x)` and bounded by `β` and `γ`, the lower-order
parts of the energy forms of `L(t)` are, for almost every `t`, the `L²(Ω)` pairings with the value
of a single family of bounded operators `M(t) : H¹₀(Ω) → L²(Ω)`, and `t ↦ M(t) u(t)` is square
integrable whenever `u` is. -/
private theorem exists_lowerOrder_memLp_apply {ν : Measure ℝ}
    (ha : ∀ᵐ t ∂ν, MemLp (fun x => energyIntegrand (a t x) 0 0) ⊤ (mu.restrict Omega))
    (hb : AEStronglyMeasurable (Function.uncurry b) (ν.prod (mu.restrict Omega)))
    (hc : AEStronglyMeasurable (Function.uncurry c) (ν.prod (mu.restrict Omega)))
    (hb_bound : ∀ᵐ t ∂ν, ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b t x‖ ≤ beta)
    (hc_bound : ∀ᵐ t ∂ν, ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c t x‖ ≤ gamma)
    {u : ℝ → W1p0 mu Omega 2} (hu : MemLp u 2 ν) :
    ∃ M : ℝ → W1p0 mu Omega 2 →L[ℝ] Lp ℝ 2 (mu.restrict Omega),
      (∀ᵐ t ∂ν, ∀ v w : W1p0 mu Omega 2,
        energyFormH1 (a t) (b t) (c t) (v : W1p mu Omega 2) (w : W1p mu Omega 2) =
          energyFormH1 (a t) 0 0 (v : W1p mu Omega 2) (w : W1p mu Omega 2) +
            ⟪M t v, W1p0.valueL w⟫_ℝ) ∧
      MemLp (fun t => M t (u t)) 2 ν := by
  classical
  have hΩ := Omega.isOpen.measurableSet
  -- For almost every `t`, the drift and the mass are essentially bounded on `Ω`.
  have hbc : ∀ᵐ t ∂ν, MemLp (b t) ⊤ (mu.restrict Omega) ∧ MemLp (c t) ⊤ (mu.restrict Omega) := by
    filter_upwards [hb.prodMk_left, hc.prodMk_left, hb_bound, hc_bound] with t hbt hct hbt' hct'
    exact ⟨memLp_top_of_bound hbt beta (ae_restrict_of_forall_mem hΩ hbt'),
      memLp_top_of_bound hct gamma (ae_restrict_of_forall_mem hΩ hct')⟩
  set M : ℝ → W1p0 mu Omega 2 →L[ℝ] Lp ℝ 2 (mu.restrict Omega) := fun t =>
    if h : MemLp (b t) ⊤ (mu.restrict Omega) ∧ MemLp (c t) ⊤ (mu.restrict Omega) then
      (lowerOrderL h.1 h.2).comp (w1p0Submodule mu Omega 2).toSubmodule.subtypeL
    else 0 with hM
  -- The operators are bounded uniformly in time.
  set Λ := (|beta| + |gamma|) *
    ‖(jetLpL : W1p mu Omega 2 →L[ℝ] Lp (ℝ × EuclideanSpace ℝ ι) 2 (mu.restrict Omega))‖
  have hMΛ : ∀ᵐ t ∂ν, ‖M t‖ ≤ Λ := by
    filter_upwards [hbc, hb_bound, hc_bound] with t h hbt hct
    simp only [hM, h]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_of_le_one_right (norm_nonneg _) (Submodule.norm_subtypeL_le _)).trans ?_
    exact norm_lowerOrderL_le h.1 h.2 (ae_restrict_of_forall_mem hΩ hbt)
      (ae_restrict_of_forall_mem hΩ hct)
  refine ⟨M, ?_, ?_⟩
  · filter_upwards [ha, hbc] with t hat h v w
    simp only [hM, h]
    exact energyFormH1_eq_principal_add_inner_lowerOrderL hat h.1 h.2 _ w
  -- Measurability in time: `t ↦ ⟪M(t) v, y⟫` is the integral over `Ω` of a function jointly
  -- measurable in `(t, x)`, and Pettis' theorem passes to `t ↦ M(t) u(t)`.
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have hB : MemLp (fun t => (innerSL ℝ).comp (M t) (u t)) 2 ν := by
    refine hu.clm_apply_of_forall_aestronglyMeasurable (Λ := Λ) (fun v y => ?_) ?_
    · have hint := (((hb.inner (Lp.aestronglyMeasurable
          (W1p.gradient (v : W1p mu Omega 2))).comp_snd).add
        (hc.mul (Lp.aestronglyMeasurable (W1p.value (v : W1p mu Omega 2))).comp_snd)).mul
          (Lp.aestronglyMeasurable y).comp_snd).integral_prod_right'
      refine hint.congr ?_
      filter_upwards [hbc] with t h
      simp only [hM, h, and_self, ↓reduceDIte, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply, innerSL_apply_apply, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [lowerOrderL_apply_ae h.1 h.2 (v : W1p mu Omega 2)] with x hx
      rw [hx, RCLike.inner_apply, conj_trivial]
      simp only [Pi.mul_apply, Pi.add_apply, Function.uncurry_apply_pair]
      ring
    · filter_upwards [hMΛ] with t ht
      refine ContinuousLinearMap.opNorm_le_bound _ ((M t).opNorm_nonneg.trans ht) fun v => ?_
      rw [ContinuousLinearMap.comp_apply, innerSL_apply_norm]
      exact ((M t).le_opNorm v).trans (by gcongr)
  refine hu.of_le_mul (c := Λ) ((aestronglyMeasurable_iff_forall_inner (𝕜 := ℝ)).2 fun y => ?_) ?_
  · refine (hB.aestronglyMeasurable.apply_continuousLinearMap y).congr (ae_of_all _ fun t => ?_)
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm]
  · filter_upwards [hMΛ] with t ht
    exact ((M t).le_opNorm (u t)).trans (by gcongr)

/-- For a principal coefficient that is, at every `t ∈ [t₀, t₁]`, measurable, uniformly elliptic
and symmetric, and that is Lipschitz in time with constant `L`, the symmetric coercive parts
`A(t) = -∂ᵢ(aⁱʲ(t, ·) ∂ⱼ ·) + λ/2` of the energy forms are bounded operators
`H¹₀(Ω) → H⁻¹(Ω)` that are symmetric, coercive with constant `λ/2` and Lipschitz in time with
constant `max L 0`. -/
private theorem exists_principal_symm_coercive_lipschitz [DecidableEq ι] {L : ℝ}
    (ha : ∀ t ∈ Icc t₀ t₁, AEStronglyMeasurable (a t) (mu.restrict Omega))
    (hell : ∀ t ∈ Icc t₀ t₁, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (a t) lam Lam)
    (hsymm : ∀ t ∈ Icc t₀ t₁, ∀ᵐ x ∂mu.restrict Omega, (a t x).IsSymm)
    (hLip : ∀ s ∈ Icc t₀ t₁, ∀ t ∈ Icc t₀ t₁, ∀ᵐ x ∂mu.restrict Omega,
      ∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ ((a t x - a s x) *ᵥ ξ)| ≤ L * |t - s| * ‖η‖ * ‖ξ‖) :
    ∃ A : ℝ → W1p0 mu Omega 2 →L[ℝ] StrongDual ℝ (W1p0 mu Omega 2),
      (∀ t ∈ Icc t₀ t₁, ∀ v w : W1p0 mu Omega 2, A t v w = energyFormH1 (a t) 0 0
        (v : W1p mu Omega 2) (w : W1p mu Omega 2) + lam / 2 * ⟪W1p0.valueL v, W1p0.valueL w⟫_ℝ) ∧
      (∀ t ∈ Icc t₀ t₁, ∀ v w : W1p0 mu Omega 2, A t v w = A t w v) ∧
      (∀ t ∈ Icc t₀ t₁, ∀ v : W1p0 mu Omega 2, lam / 2 * ‖v‖ ^ 2 ≤ A t v v) ∧
      ∀ s ∈ Icc t₀ t₁, ∀ t ∈ Icc t₀ t₁, ‖A t - A s‖ ≤ max L 0 * |t - s| := by
  have hcoeff (t : ℝ) (ht : t ∈ Icc t₀ t₁) := (hell t ht).memLp_energyIntegrand_zero_zero (ha t ht)
  -- At each `t ∈ [t₀, t₁]`, `A(t)` is the symmetric coercive part of the time-independent case.
  have hex (t : ℝ) : ∃ A₀ : W1p0 mu Omega 2 →L[ℝ] StrongDual ℝ (W1p0 mu Omega 2), t ∈ Icc t₀ t₁ →
      (∀ v w : W1p0 mu Omega 2, A₀ v w = energyFormH1 (a t) 0 0 (v : W1p mu Omega 2)
        (w : W1p mu Omega 2) + lam / 2 * ⟪W1p0.valueL v, W1p0.valueL w⟫_ℝ) ∧
      (∀ v w : W1p0 mu Omega 2, A₀ v w = A₀ w v) ∧
      ∀ v : W1p0 mu Omega 2, lam / 2 * ‖v‖ ^ 2 ≤ A₀ v v := by
    by_cases ht : t ∈ Icc t₀ t₁
    · exact (exists_principal_symm_coercive (ha t ht) (hell t ht) (hsymm t ht)).imp
        fun _ h _ => h
    · exact ⟨0, fun h => absurd h ht⟩
  choose A hA using hex
  refine ⟨A, fun t ht => (hA t ht).1, fun t ht => (hA t ht).2.1, fun t ht => (hA t ht).2.2,
    fun s hs t ht => ?_⟩
  -- The difference `A(t) - A(s)` is the energy form of `a(t, ·) - a(s, ·)`.
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v v' => ?_
  rw [sub_apply, sub_apply, (hA t ht).1 v v', (hA s hs).1 v v', add_sub_add_right_eq_sub,
    Real.norm_eq_abs, ← Submodule.norm_coe v, ← Submodule.norm_coe v']
  have hL : L * |t - s| ≤ max L 0 * |t - s| :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  have := abs_energyFormH1_sub_energyFormH1_le (hcoeff t ht) (hcoeff s hs)
    (by positivity : 0 ≤ max L 0 * |t - s|) (b := 0) (b' := 0) (c := 0) (c' := 0)
    (beta := 0) (gamma := 0) ?_ (ae_of_all _ fun _ => by simp) (ae_of_all _ fun _ => by simp)
    (v : W1p mu Omega 2) (v' : W1p mu Omega 2)
  · simpa using this
  · filter_upwards [hLip s hs t ht] with x hx η ξ
    exact (hx η ξ).trans (by gcongr)

/-- **Time regularity for the parabolic Dirichlet problem with time-dependent coefficients**
(Evans, §7.1.3, Theorem 5, there for time-independent coefficients). Let
`L(t) u = -∂ᵢ(aⁱʲ(t, ·) ∂ⱼu) + bⁱ(t, ·) ∂ᵢu + c(t, ·) u`, where for every `t ∈ [t₀, t₁]` the
principal coefficient `a(t, ·)` is measurable, uniformly elliptic on `Ω` with constants `λ, Λ` and
symmetric almost everywhere, and `a` is Lipschitz in time with constant `L`:
`|ηᵀ (a(t, x) - a(s, x)) ξ| ≤ L |t - s| ‖η‖ ‖ξ‖` for almost every `x ∈ Ω`, as when `∂ₜa` is
bounded by `L`. Let `b` and `c` be jointly measurable on `(t₀, t₁) × Ω`, with `‖b(t, ·)‖ ≤ β` and
`|c(t, ·)| ≤ γ` on `Ω` for almost every `t`. Let `u` be a weak solution of `∂ₜu + L(t) u = F` in
`(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, with forcing `F ∈ L²(t₀, t₁; L²(Ω))`, whose continuous
`L²(Ω)`-valued representative starts at `u₀ ∈ H¹₀(Ω)`. Then `∂ₜu ∈ L²(t₀, t₁; L²(Ω))`: the
`L²(Ω)`-valued map `t ↦ u(t)` has a weak time derivative `d ∈ L²(t₀, t₁; L²(Ω))`, which represents
`u'` through the `L²(Ω)` pairing; and `u ∈ L^∞(t₀, t₁; H¹₀(Ω))`. No regularity of `∂Ω`, no
continuity of `a` in space, no boundedness of `Ω` and no sign condition on `c` is needed.
For coefficients independent of time,
`TauCeti.PDE.exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm` moreover gives a
representative continuous with values in `H¹₀(Ω)`. -/
theorem exists_memLp_hasWeakLineDerivOn_valueL_energyFormH1_of_isSymm_of_lipschitz
    [DecidableEq ι] {L : ℝ}
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
    ∃ d : ℝ → Lp ℝ 2 (mu.restrict Omega), MemLp d 2 (volume.restrict (Ioo t₀ t₁)) ∧
      HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩ (fun t => W1p0.valueL (u t)) d 1 ∧
      (∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
        u' t v = ⟪d t, W1p0.valueL v⟫_ℝ) ∧
      MemLp u ⊤ (volume.restrict (Ioo t₀ t₁)) := by
  rcases lt_or_ge t₁ t₀ with ht | ht
  · -- On an empty interval of times every statement is vacuous.
    have h0 : volume.restrict (Ioo t₀ t₁) = 0 := by
      rw [Ioo_eq_empty_of_le ht.le, Measure.restrict_empty]
    refine ⟨0, MemLp.zero, hasWeakLineDerivOn_iff_locally.2 fun x hx => ?_, by simp [h0],
      by simp [h0]⟩
    exact absurd (hx.1.trans hx.2) ht.not_gt
  have hI : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), t ∈ Icc t₀ t₁ :=
    (ae_restrict_mem measurableSet_Ioo).mono fun _ ht => Ioo_subset_Icc_self ht
  have hlam : 0 < lam := (hell t₀ (left_mem_Icc.2 ht)).pos
  -- The symmetric coercive parts `A(t) = -div(a(t, ·) ∇ ·) + λ/2`; the rest goes into the forcing.
  obtain ⟨A, hA, hsymm₀, hcoer, hLipA⟩ :=
    exists_principal_symm_coercive_lipschitz (L := L) ha hell hsymm hLip
  -- The lower-order terms and the mass shift, moved into the `L²` forcing.
  obtain ⟨M, hMsplit, hMu⟩ := exists_lowerOrder_memLp_apply
    (hI.mono fun t ht => (hell t ht).memLp_energyIntegrand_zero_zero (ha t ht)) hb hc hb_bound
    hc_bound hu
  have hg : MemLp (fun t => F t - M t (u t) + (lam / 2) • W1p0.valueL (u t)) 2
      (volume.restrict (Ioo t₀ t₁)) :=
    (hF.sub hMu).add
      (((W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).comp_memLp' hu).const_smul (lam / 2))
  have heq₀ : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), u' t + A t (u t) =
      (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (F t - M t (u t) + (lam / 2) • W1p0.valueL (u t)) := by
    filter_upwards [heq, hMsplit, hI] with t ht hsplit htI
    ext v
    simp only [add_apply, ContinuousLinearMap.gelfandDual_apply, inner_add_left, inner_sub_left,
      real_inner_smul_left, hA t htI]
    linarith [ht v, hsplit (u t) v]
  obtain ⟨d, hd, hdd, hu'd, hE, -⟩ :=
    HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_lipschitz
      ht hsymm₀ (half_pos hlam) hcoer hLipA hg h hu hu' heq₀ hw hae h₀
  refine ⟨d, hd, hdd, ?_, ?_⟩
  · filter_upwards [hu'd] with t ht φ
    exact (DFunLike.congr_fun ht φ).trans (ContinuousLinearMap.gelfandDual_apply _ _ _)
  -- The energy bound `λ/2 ‖u(t)‖² ≤ A(t) u(t) u(t) ≤ K` makes `u` essentially bounded.
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), A t (u t) (u t) ≤ K := ⟨_, hE⟩
  refine memLp_top_of_bound hu.aestronglyMeasurable (√(K / (lam / 2))) ?_
  filter_upwards [hK, hI] with t hKt htI
  refine Real.le_sqrt_of_sq_le ?_
  rw [le_div_iff₀ (half_pos hlam), mul_comm]
  exact (hcoer t htI (u t)).trans hKt

end TimeDependent

end PDE

end TauCeti
