/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.GelfandTriple
public import TauCeti.Analysis.PDE.Parabolic.Semigroup
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.PDE.Parabolic.EnergyEstimate
import TauCeti.Analysis.PDE.Parabolic.Existence
import TauCeti.Analysis.Semigroups.Generator.Invariance
import TauCeti.Analysis.Semigroups.Generator.OrbitDerivative
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Weak solutions of autonomous parabolic equations are semigroup orbits

Let `V ↪ H ↪ V*` be a Gelfand triple, given by a continuous linear map `J : V →L[ℝ] H` with dense
range between real Hilbert spaces, and let `B` be a bounded coercive bilinear form on `V`. The
operator `𝒜` associated with `B` (`B u v = ⟪𝒜 (J u), J v⟫`) is the negative of the generator of the
contraction semigroup `e^{-t𝒜} = IsCoercive.formSemigroup`. The autonomous parabolic equation

`u' + B u = 0` on `(a, b)`

has two solution concepts: the weak solutions of the Gelfand-triple theory, `u ∈ L²(a, b; V)`
whose image in `V*` has weak time derivative `u' = -B u ∈ L²(a, b; V*)`, and the orbits
`t ↦ e^{-(t - a)𝒜} u₀` of the semigroup. This file shows that they agree: the continuous
`H`-valued representative `w` of a weak solution is the orbit of its initial value,

`w t = e^{-(t - a)𝒜} (w a)` for `t ∈ [a, b]`

(`TauCeti.HasWeakLineDerivOn.eqOn_realOperator_formSemigroup_of_gelfandDual`), and for every
`u₀ ∈ H` the orbit is the continuous representative of a weak solution with initial value `u₀`
(`IsCoercive.exists_hasWeakLineDerivOn_gelfandDual_ae_eq_realOperator_formSemigroup`).

For the parabolic Dirichlet problem

`∂ₜu + L u = 0` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, `u(t₀) = u₀`

with time-independent coefficients whose energy form is coercive on `H¹₀(Ω)`, the continuous
`L²(Ω)`-valued representative of every weak solution is the orbit `t ↦ e^{-(t - t₀)L} u₀` of the
Dirichlet semigroup `TauCeti.PDE.dirichletSemigroup`
(`TauCeti.PDE.eqOn_realOperator_dirichletSemigroup_of_hasWeakLineDerivOn_gelfandDual`). In
particular this applies to the weak solution of
`TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1` for uniformly elliptic
coefficients. For `L = -Δ` on a bounded domain this is the heat equation with zero boundary
values.

## The argument

* **Orbits of the domain.** For `x` in the domain of the generator, the orbit
  `X t = e^{-(t - a)𝒜} x` is differentiable with derivative `-e^{-(t - a)𝒜} 𝒜 x`, and
  `X t = J (U t)` for the continuous curve `U t = -S (e^{-(t - a)𝒜} 𝒜' x)` in `V`, where `S` is the
  Lax–Milgram solution map of `B` and `𝒜' = -𝒜` the generator: the generator commutes with the
  semigroup and `S` inverts it. Tested against `v ∈ V`, the derivative of `J.gelfandDual ∘ X` is
  `⟪-e^{-(t - a)𝒜} 𝒜 x, J v⟫ = -B (U t) v`, so `U` is a weak solution, continuous in time
  (`IsCoercive.exists_continuous_hasWeakLineDerivOn_realOperator_formSemigroup`).
* **Density.** For an arbitrary weak solution and `x` in the domain, the difference with `U` is a
  weak solution of the same equation, so the energy estimate
  (`TauCeti.HasWeakLineDerivOn.norm_sq_add_mul_integral_le_of_gelfandDual`, with Gårding constants
  `α > 0` from coercivity and `β = 0`) gives `‖w t - e^{-(t - a)𝒜} x‖ ≤ ‖w a - x‖`. Both sides are
  continuous in `x`, and the domain of the generator is dense, so the inequality holds for
  `x = w a`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.4.3 (second-order parabolic
  equations by semigroup theory).
* W. Arendt, C. J. K. Batty, M. Hieber, F. Neubrander, *Vector-valued Laplace Transforms and Cauchy
  Problems*, 2nd ed., Birkhäuser, 2011, §5.2 (forms and the associated semigroups).
* J.-L. Lions, *Équations différentielles opérationnelles et problèmes aux limites*, Springer,
  1961, Chapter III.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace TauCeti.Semigroups
open scoped InnerProductSpace

namespace TauCeti

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {B : V →L[ℝ] V →L[ℝ] ℝ} {J : V →L[ℝ] H} {a b : ℝ}

/-- **Orbits of the domain are weak solutions.** Let `B` be a bounded coercive form on a real
Hilbert space `V` and `J : V →L[ℝ] H` a continuous linear map with dense range into a real Hilbert
space. For `x` in the domain of the generator of the semigroup of the form, there is a curve `U` in
`V`, continuous in the norm of `V`, with `J (U t) = e^{-(t - a)𝒜} x` for every `t`, which is a weak
solution of `u' + B u = 0` on `(a, b)`: the image of `U` in `V*` has weak derivative `-B U`. -/
theorem _root_.IsCoercive.exists_continuous_hasWeakLineDerivOn_realOperator_formSemigroup
    (hB : IsCoercive B) (hJ : DenseRange J) {x : H} (hx : x ∈ (hB.formGenerator J).domain) :
    ∃ U : ℝ → V, Continuous U ∧
      (∀ t, J (U t) = (hB.formSemigroup hJ).realOperator (t - a) x) ∧
      HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ J.gelfandDual (J (U t)))
        (fun t ↦ -B (U t)) 1 := by
  set S := (hB.formSemigroup hJ).toStronglyContinuousSemigroup
  have hxS : x ∈ S.domain := by rwa [hB.formSemigroup_domain hJ]
  have hxg : x ∈ S.generator.domain := by rwa [S.generator_domain]
  set g := S.generator ⟨x, hxg⟩
  set U : ℝ → V := fun t ↦ -hB.formSolutionMap J (S.realOperator (t - a) g)
  have hU : Continuous U := ((hB.formSolutionMap J).continuous.comp
    ((S.continuous_realOperator_apply g).comp (continuous_sub_right a))).neg
  -- The generator commutes with the semigroup, and the solution map inverts it.
  have hJU : ∀ t, J (U t) = S.realOperator (t - a) x := by
    intro t
    have hy : S.realOperator (t - a) x ∈ S.generator.domain := by
      rw [S.generator_domain]
      exact S.realOperator_mem_domain hxS
    have hy' : S.realOperator (t - a) x ∈ (hB.formGenerator J).domain := by
      rwa [← hB.formSemigroup_generator hJ]
    have hgen : S.generator ⟨_, hy⟩ = S.realOperator (t - a) g :=
      S.realOperator_generator_map ⟨x, hxS⟩
    rw [hB.formSemigroup_generator_apply hJ ⟨_, hy⟩ hy'] at hgen
    have hsol := hB.formSolutionOperator_formGenerator hJ ⟨_, hy'⟩
    rw [hgen, IsCoercive.formSolutionOperator_apply] at hsol
    simp only [U, map_neg, hsol, neg_neg]
  refine ⟨U, hU, hJU, hasWeakLineDerivOn_of_hasLineDerivAt
    (((J.gelfandDual.continuous.comp J.continuous).comp hU).continuousOn.locallyIntegrableOn
      measurableSet_Ioo)
    ((B.continuous.comp hU).neg.continuousOn.locallyIntegrableOn measurableSet_Ioo)
    fun t ht ↦ ?_⟩
  -- At `t ∈ (a, b)` the orbit `s ↦ e^{-(s - a)𝒜} x` is differentiable, since `t - a > 0`.
  have hpos : 0 < t - a := sub_pos.2 ht.1
  have hderiv : HasDerivAt (fun s ↦ S.realOperator (s - a) x) (S.realOperator (t - a) g) t := by
    refine HasDerivAt.comp_sub_const (f := fun s ↦ S.realOperator s x) t a ?_
    have h := S.realOperator_hasDerivWithinAt_Ici ⟨x, hxS⟩ hpos.le
    rw [S.realOperator_generator_map ⟨x, hxS⟩] at h
    exact h.hasDerivAt (Ici_mem_nhds hpos)
  have hderiv' := J.gelfandDual.hasFDerivAt.comp_hasDerivAt t hderiv
  have hfun : (fun s ↦ J.gelfandDual (J (U s))) =
      J.gelfandDual ∘ fun s ↦ S.realOperator (s - a) x :=
    funext fun s ↦ by rw [Function.comp_apply, hJU s]
  have hval : J.gelfandDual (S.realOperator (t - a) g) = -B (U t) := by
    ext v
    simp [U, ContinuousLinearMap.gelfandDual_apply]
  rw [hfun]
  simpa [hval] using hderiv'.hasFDerivAt.hasLineDerivAt 1

/-- **The energy estimate against an orbit of the domain.** A weak solution `u` of `u' + B u = 0`,
with continuous representative `w`, stays within `‖w a - x‖` of the semigroup orbit of any `x` in
the domain of the generator: the difference with the weak solution of
`IsCoercive.exists_continuous_hasWeakLineDerivOn_realOperator_formSemigroup` is again a weak
solution, and coercivity is Gårding's inequality with the constants `α > 0` and `0`. -/
private theorem norm_sub_realOperator_formSemigroup_le_of_gelfandDual {u : ℝ → V}
    {u' : ℝ → StrongDual ℝ V} {w : ℝ → H}
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ J.gelfandDual (J (u t))) u' 1)
    (hB : IsCoercive B) (hJ : DenseRange J) (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo a b)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo a b), u' t + B (u t) = 0)
    (hw : ContinuousOn w (Icc a b)) (hae : (fun t ↦ J (u t)) =ᵐ[volume.restrict (Ioo a b)] w)
    {x : H} (hx : x ∈ (hB.formGenerator J).domain) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖w t - (hB.formSemigroup hJ).realOperator (t - a) x‖ ≤ ‖w a - x‖ := by
  obtain ⟨α, hα, hcoer⟩ := id hB
  obtain ⟨U, hU, hJU, hdU⟩ := hB.exists_continuous_hasWeakLineDerivOn_realOperator_formSemigroup
    (a := a) (b := b) hJ hx
  have hUL : MemLp U 2 (volume.restrict (Ioo a b)) :=
    hU.continuousOn.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo
      Ioo_subset_Icc_self 2
  have hd : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun s ↦ J.gelfandDual (J ((u - U) s))) (u' - fun s ↦ -B (U s)) 1 := by
    convert h.sub hdU using 1
    funext s
    simp only [Pi.sub_apply, map_sub]
  have hX : ContinuousOn (fun s ↦ (hB.formSemigroup hJ).realOperator (s - a) x) (Icc a b) :=
    ((hB.formSemigroup hJ).continuous_realOperator_apply x).comp
      (continuous_sub_right a) |>.continuousOn
  have hE := hd.norm_sq_add_mul_integral_le_of_gelfandDual (A := fun _ ↦ B) (f := 0)
    (w := w - fun s ↦ (hB.formSemigroup hJ).realOperator (s - a) x)
    (hu.sub hUL) (hu'.sub (B.comp_memLp' hUL).neg)
    (MemLp.zero (ε := StrongDual ℝ V)) hα le_rfl
    (Eventually.of_forall fun _ v ↦ by
      rw [zero_mul, sub_zero, sq, ← mul_assoc]
      exact hcoer v)
    (by
      filter_upwards [heq] with s hs
      rw [Pi.sub_apply, Pi.sub_apply, map_sub, Pi.zero_apply, ← hs]
      abel)
    (hw.sub hX)
    (by
      filter_upwards [hae] with s hs
      rw [Pi.sub_apply, map_sub, hs, hJU s, Pi.sub_apply]) ht
  have hint : 0 ≤ ∫ s in a..t, ‖(u - U) s‖ ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 fun _ _ ↦ sq_nonneg _
  simp only [Pi.sub_apply, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, intervalIntegral.integral_zero, mul_zero, add_zero, zero_mul,
    Real.exp_zero, one_mul, sub_self, (hB.formSemigroup hJ).realOperator_zero_apply] at hE
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.1 <|
    (le_add_of_nonneg_right (mul_nonneg hα.le hint)).trans hE

/-- **Weak solutions are semigroup orbits.** Let `B` be a bounded coercive form on a real Hilbert
space `V` and `J : V →L[ℝ] H` a continuous linear map with dense range into a real Hilbert space.
Let `u ∈ L²(a, b; V)` be a weak solution of the autonomous equation `u' + B u = 0`: the image
`t ↦ J.gelfandDual (J (u t))` of `u` in `V*` has weak derivative `u'` with `u' t + B (u t) = 0` for
almost every `t ∈ (a, b)`, so that `u' = -B u ∈ L²(a, b; V*)`. Let `w` be continuous on `[a, b]` and
equal to `J ∘ u` almost everywhere on `(a, b)`. Then `w` is the orbit of its initial value under the
semigroup of the form: `w t = e^{-(t - a)𝒜} (w a)` for every `t ∈ [a, b]`. -/
theorem HasWeakLineDerivOn.eqOn_realOperator_formSemigroup_of_gelfandDual {u : ℝ → V}
    {u' : ℝ → StrongDual ℝ V} {w : ℝ → H}
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ J.gelfandDual (J (u t))) u' 1)
    (hB : IsCoercive B) (hJ : DenseRange J) (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo a b), u' t + B (u t) = 0)
    (hw : ContinuousOn w (Icc a b)) (hae : (fun t ↦ J (u t)) =ᵐ[volume.restrict (Ioo a b)] w) :
    EqOn w (fun t ↦ (hB.formSemigroup hJ).realOperator (t - a) (w a)) (Icc a b) := by
  intro t ht
  -- The equation gives `u' = -B u ∈ L²(a, b; V*)`.
  have hu' : MemLp u' 2 (volume.restrict (Ioo a b)) :=
    (B.comp_memLp' hu).neg.ae_eq (heq.mono fun _ hs ↦ (eq_neg_of_add_eq_zero_left hs).symm)
  -- The estimate against orbits of the domain is continuous in `x`, and the domain is dense.
  have hall := (hB.dense_formGenerator_domain hJ).induction
    (P := fun x ↦ ‖w t - (hB.formSemigroup hJ).realOperator (t - a) x‖ ≤ ‖w a - x‖)
    (fun _ hx ↦ norm_sub_realOperator_formSemigroup_le_of_gelfandDual h hB hJ hu hu' heq hw hae
      hx ht)
    (isClosed_le (continuous_const.sub ((hB.formSemigroup hJ).realOperator (t - a)).continuous).norm
      (continuous_const.sub continuous_id).norm) (w a)
  rwa [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] at hall

/-- **The semigroup orbit is the weak solution.** Let `B` be a bounded coercive form on a separable
real Hilbert space `V` and `J : V →L[ℝ] H` a continuous linear map with dense range into a real
Hilbert space. For every `u₀ ∈ H` there is a weak solution `u ∈ L²(a, b; V)` of `u' + B u = 0`
(with weak derivative `-B u ∈ L²(a, b; V*)` of its image in `V*`) whose image `J ∘ u` agrees almost
everywhere on `(a, b)` with the orbit `t ↦ e^{-(t - a)𝒜} u₀` of the semigroup of the form. The
orbit is continuous, so it is the continuous representative of the solution, with initial value
`u₀`; by `TauCeti.HasWeakLineDerivOn.eqOn_realOperator_formSemigroup_of_gelfandDual` every weak
solution with initial value `u₀` has it as continuous representative. -/
theorem _root_.IsCoercive.exists_hasWeakLineDerivOn_gelfandDual_ae_eq_realOperator_formSemigroup
    [SeparableSpace V] (hB : IsCoercive B) (hJ : DenseRange J) (u₀ : H) :
    ∃ u : ℝ → V, MemLp u 2 (volume.restrict (Ioo a b)) ∧
      MemLp (fun t ↦ -B (u t)) 2 (volume.restrict (Ioo a b)) ∧
      HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ J.gelfandDual (J (u t)))
        (fun t ↦ -B (u t)) 1 ∧
      (fun t ↦ J (u t)) =ᵐ[volume.restrict (Ioo a b)]
        fun t ↦ (hB.formSemigroup hJ).realOperator (t - a) u₀ := by
  rcases lt_or_ge b a with hba | hab
  · -- For `b < a` the interval `(a, b)` is empty, and any weak solution will do.
    obtain ⟨U, hU, -, hdU⟩ := hB.exists_continuous_hasWeakLineDerivOn_realOperator_formSemigroup
      (a := a) (b := b) hJ (Submodule.zero_mem _)
    have hUL : MemLp U 2 (volume.restrict (Ioo a b)) :=
      hU.continuousOn.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo
        Ioo_subset_Icc_self 2
    refine ⟨U, hUL, (B.comp_memLp' hUL).neg, hdU, ?_⟩
    simp [EventuallyEq, Ioo_eq_empty_of_le hba.le]
  obtain ⟨α, hα, hcoer⟩ := id hB
  obtain ⟨u, w, hu, hu', hd, hw, hae, hw₀⟩ :=
    exists_hasWeakLineDerivOn_gelfandDual (A := fun _ ↦ B) (f := 0) (Λ := ‖B‖) (β := 0) hJ hab
      (fun _ _ ↦ aestronglyMeasurable_const) (Eventually.of_forall fun _ ↦ le_rfl) hα
      (Eventually.of_forall fun _ v ↦ by
        rw [zero_mul, sub_zero, sq, ← mul_assoc]
        exact hcoer v)
      (MemLp.zero (ε := StrongDual ℝ V)) u₀
  have hfun : (fun t ↦ (0 : ℝ → StrongDual ℝ V) t - B (u t)) = fun t ↦ -B (u t) :=
    funext fun _ ↦ zero_sub _
  rw [hfun] at hu' hd
  have horbit := hd.eqOn_realOperator_formSemigroup_of_gelfandDual hB hJ hu
    (Eventually.of_forall fun _ ↦ neg_add_cancel _) hw hae
  refine ⟨u, hu, hu', hd, hae.trans ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [horbit (Ioo_subset_Icc_self ht), hw₀]

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} {t₀ t₁ : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

variable (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  (hcoercive : IsCoercive (energyFormH1L0 hcoeff))

/-- **Weak solutions of the autonomous parabolic Dirichlet problem are orbits of the Dirichlet
semigroup.** Let the time-independent coefficients of `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` on an
open set `Ω` have a bounded energy form that is coercive on `H¹₀(Ω)`. Let `u ∈ L²(t₀, t₁; H¹₀(Ω))`
be a weak solution of `∂ₜu + L u = 0` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`: its image in
`H⁻¹(Ω)` has a weak time derivative `u'` with `u'(t)(v) + a(u(t), v) = 0` for every `v ∈ H¹₀(Ω)` and
almost every `t`, where `a` is the energy form of `L`. Let `w` be a
representative of `t ↦ u(t) ∈ L²(Ω)` continuous on `[t₀, t₁]`. Then `w t = e^{-(t - t₀)L} (w t₀)`
for every `t ∈ [t₀, t₁]`, where `e^{-tL}` is the Dirichlet semigroup
`TauCeti.PDE.dirichletSemigroup`. -/
theorem eqOn_realOperator_dirichletSemigroup_of_hasWeakLineDerivOn_gelfandDual
    {u : ℝ → W1p0 mu Omega 2} {u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)}
    {w : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (h : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 a b c (u t : W1p mu Omega 2) (v : W1p mu Omega 2) = 0)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w) :
    EqOn w (fun t => (dirichletSemigroup hcoeff hcoercive).realOperator (t - t₀) (w t₀))
      (Icc t₀ t₁) := by
  rw [dirichletSemigroup_def]
  refine h.eqOn_realOperator_formSemigroup_of_gelfandDual hcoercive W1p0.denseRange_valueL_two hu
    ?_ hw hae
  filter_upwards [heq] with t ht
  ext v
  simpa [energyFormH1L0_apply] using ht v

end PDE

end TauCeti
