/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.GelfandTriple
public import TauCeti.Analysis.Semigroups.Generation.Form
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.PDE.Parabolic.Duhamel
import TauCeti.Analysis.PDE.Parabolic.Existence
import TauCeti.Analysis.Semigroups.Generator.Invariance
import TauCeti.Analysis.Semigroups.Generator.OrbitDerivative
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Semigroup orbits are weak solutions of autonomous parabolic equations

Let `V ↪ H ↪ V*` be a Gelfand triple, given by a continuous linear map `J : V →L[ℝ] H` with dense
range between real Hilbert spaces, and let `B` be a bounded coercive bilinear form on `V`. The
operator `𝒜` associated with `B` (`B u v = ⟪𝒜 (J u), J v⟫`) is the negative of the generator of the
contraction semigroup `e^{-t𝒜} = IsCoercive.formSemigroup`. The autonomous parabolic equation

`u' + B u = 0` on `(a, b)`

has two solution concepts: the weak solutions of the Gelfand-triple theory, `u ∈ L²(a, b; V)`
whose image in `V*` has weak time derivative `u' = -B u ∈ L²(a, b; V*)`, and the orbits
`t ↦ e^{-(t - a)𝒜} u₀` of the semigroup. By Duhamel's formula with zero forcing
(`TauCeti.HasWeakLineDerivOn.eqOn_formSemigroup_add_setIntegral_of_gelfandDual`), the continuous
`H`-valued representative `w` of a weak solution is the orbit of its initial value,
`w t = e^{-(t - a)𝒜} (w a)` for `t ∈ [a, b]`. This file proves the converse: when `V` is
separable, for every `u₀ ∈ H` the orbit is the continuous representative of a weak solution with
initial value `u₀`
(`IsCoercive.exists_hasWeakLineDerivOn_gelfandDual_ae_eq_realOperator_formSemigroup`).

For the parabolic Dirichlet problem

`∂ₜu + L u = 0` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, `u(t₀) = u₀`

with time-independent coefficients whose energy form is coercive on `H¹₀(Ω)`, the Dirichlet
semigroup `TauCeti.PDE.dirichletSemigroup` is a form semigroup, so its orbits are the continuous
`L²(Ω)`-valued representatives of the weak solutions. For `L = -Δ` on a bounded domain this is the
heat equation with zero boundary values.

## The argument

* **Orbits of the domain.** For `x` in the domain of the generator, the orbit
  `X t = e^{-(t - a)𝒜} x` is differentiable with derivative `-e^{-(t - a)𝒜} 𝒜 x`, and
  `X t = J (U t)` for the continuous curve `U t = -S (e^{-(t - a)𝒜} 𝒜' x)` in `V`, where `S` is the
  Lax–Milgram solution map of `B` and `𝒜' = -𝒜` the generator: the generator commutes with the
  semigroup and `S` inverts it. Tested against `v ∈ V`, the derivative of `J.gelfandDual ∘ X` is
  `⟪-e^{-(t - a)𝒜} 𝒜 x, J v⟫ = -B (U t) v`, so `U` is a weak solution, continuous in time
  (`IsCoercive.exists_continuous_hasWeakLineDerivOn_realOperator_formSemigroup`).
* **Arbitrary initial values.** For `u₀ ∈ H` the existence theorem
  `TauCeti.exists_hasWeakLineDerivOn_gelfandDual` (with Gårding constants `α > 0` from coercivity
  and `0`) gives a weak solution with initial value `u₀`, and Duhamel's formula identifies its
  continuous representative with the orbit of `u₀`.

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

omit [CompleteSpace V] [CompleteSpace H] in
/-- Coercivity of `B` is Gårding's inequality for `B` with the constants `α > 0` and `0`, in the
form taken by the existence theorem for the Gelfand triple of `J`. -/
private theorem _root_.IsCoercive.exists_garding_zero (hB : IsCoercive B) (J : V →L[ℝ] H) :
    ∃ α, 0 < α ∧ ∀ v, α * ‖v‖ ^ 2 - 0 * ‖J v‖ ^ 2 ≤ B v v := by
  obtain ⟨α, hα, hcoer⟩ := hB
  refine ⟨α, hα, fun v ↦ ?_⟩
  rw [zero_mul, sub_zero, sq, ← mul_assoc]
  exact hcoer v

/-- **The semigroup orbit is the weak solution.** Let `B` be a bounded coercive form on a separable
real Hilbert space `V` and `J : V →L[ℝ] H` a continuous linear map with dense range into a real
Hilbert space. For every `u₀ ∈ H` there is a weak solution `u ∈ L²(a, b; V)` of `u' + B u = 0`
(with weak derivative `-B u ∈ L²(a, b; V*)` of its image in `V*`) whose image `J ∘ u` agrees almost
everywhere on `(a, b)` with the orbit `t ↦ e^{-(t - a)𝒜} u₀` of the semigroup of the form. The
orbit is continuous, so it is the continuous representative of the solution, with initial value
`u₀`; by `TauCeti.HasWeakLineDerivOn.eqOn_formSemigroup_add_setIntegral_of_gelfandDual` every
weak solution with initial value `u₀` has it as continuous representative. -/
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
  obtain ⟨α, hα, hcoer⟩ := hB.exists_garding_zero J
  obtain ⟨u, w, hu, hu', hd, hw, hae, hw₀⟩ :=
    exists_hasWeakLineDerivOn_gelfandDual (A := fun _ ↦ B) (f := 0) (Λ := ‖B‖) (β := 0) hJ hab
      (fun _ _ ↦ aestronglyMeasurable_const) (Eventually.of_forall fun _ ↦ le_rfl) hα
      (Eventually.of_forall fun _ ↦ hcoer) (MemLp.zero (ε := StrongDual ℝ V)) u₀
  have hfun : (fun t ↦ (0 : ℝ → StrongDual ℝ V) t - B (u t)) = fun t ↦ -B (u t) :=
    funext fun _ ↦ zero_sub _
  rw [hfun] at hu' hd
  have horbit := hd.eqOn_formSemigroup_add_setIntegral_of_gelfandDual (g := 0) hB hJ
    (hu.integrable one_le_two) integrableOn_zero
    (Eventually.of_forall fun _ ↦ by rw [Pi.zero_apply, map_zero, neg_add_cancel]) hw hae
  refine ⟨u, hu, hu', hd, hae.trans ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simp only [horbit (Ioo_subset_Icc_self ht), hw₀, Pi.zero_apply, map_zero, integral_zero, add_zero]

end TauCeti
