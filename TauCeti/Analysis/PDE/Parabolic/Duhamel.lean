/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.DirichletProblem
public import TauCeti.Analysis.PDE.Parabolic.Semigroup
public import TauCeti.Analysis.Semigroups.CauchyProblem.Inhomogeneous

/-!
# Duhamel's formula for the parabolic Dirichlet problem

Let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` have time-independent coefficients on an open set
`Ω ⊆ ℝⁿ`, with an energy form that is bounded and coercive on `H¹₀(Ω)`, and let `e^{-tL}` be its
Dirichlet semigroup on `L²(Ω)` (`TauCeti.PDE.dirichletSemigroup`). For a forcing term
`F ∈ L¹(0, T; L²(Ω))`, let `u ∈ L²(0, T; H¹₀(Ω))` be a weak solution of

`∂ₜu + L u = F` in `(0, T) × Ω`, `u = 0` on `(0, T) × ∂Ω`,

in the sense of `TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`: its image in
`H⁻¹(Ω)` has a weak time derivative `u' ∈ L²(0, T; H⁻¹(Ω))` with `u'(t)(v) + a(u(t), v) = ⟪F t, v⟫`
for all `v ∈ H¹₀(Ω)` and almost every `t`, where `a` is the energy form of `L`. This file proves
that the continuous `L²(Ω)`-valued representative `w` of `u` is given by **Duhamel's formula**

`w t = e^{-tL} w(0) + ∫_{(0,t]} e^{-(t-s)L} F(s) ds` for every `t ∈ [0, T]`

(`TauCeti.PDE.eqOn_dirichletSemigroup_add_duhamel`), and in particular `w t = e^{-tL} w(0)` without
forcing (`TauCeti.PDE.eqOn_dirichletSemigroup`). So the variational solution of the parabolic
Dirichlet problem and the semigroup solution coincide: the orbit `t ↦ e^{-tL} u₀` is the weak
solution with initial value `u₀`, whenever the latter exists.

## The argument

Integrating the weak equation in time against a fixed `v ∈ H¹₀(Ω)` over `(0, t)` gives
`⟪w t - w 0, v⟫ + a(∫_{(0,t]} u, v) = ⟪∫_{(0,t]} F, v⟫`: the time derivative integrates to the
increment of `w` by the integration-by-parts formula of the Gelfand triple
(`TauCeti.HasWeakLineDerivOn.inner_sub_inner_eq_integral_of_gelfandDual`), and the bounded energy
form commutes with the Bochner integral. So `∫_{(0,t]} u ∈ H¹₀(Ω)` is a weak solution of the
stationary problem `L U = ∫_{(0,t]} F - (w t - w 0)`, which by the description of the Dirichlet
realization (`TauCeti.PDE.mem_graph_dirichletOperator_iff`) says that `∫_{(0,t]} w` lies in the
domain of the generator `-L` of the semigroup, with

`-L (∫_{(0,t]} w) = w t - w 0 - ∫_{(0,t]} F`.

This is the integrated (mild) form of the abstract Cauchy problem `w' = -L w + F` on `[0, T]`,
whose only solution is Duhamel's formula
(`TauCeti.Semigroups.StronglyContinuousSemigroup.eqOn_realOperator_add_duhamel_Icc`).

## Main declarations

* `TauCeti.PDE.eqOn_dirichletSemigroup_add_duhamel`: Duhamel's formula for the weak solution.
* `TauCeti.PDE.eqOn_dirichletSemigroup`: without forcing, the weak solution is the orbit of its
  initial value under the Dirichlet semigroup.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1 (weak solutions of parabolic
  equations) and §7.4.3 (second-order parabolic equations by semigroup theory).
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Section 4.2 (mild solutions of the inhomogeneous Cauchy problem).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace TauCeti.Semigroups
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
  {T : ℝ} {F : ℝ → Lp ℝ 2 (mu.restrict Omega)} {u : ℝ → W1p0 mu Omega 2}
  {u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} {w : ℝ → Lp ℝ 2 (mu.restrict Omega)}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-- **The time integral of a weak solution solves a stationary problem.** If `u` is a weak solution
of `∂ₜu + L u = F` on `(0, T)` with continuous `L²(Ω)`-valued representative `w`, then for every
`s ∈ [0, T]` the time integral `∫_{(0,s]} u ∈ H¹₀(Ω)` is a weak solution of
`L U = ∫_{(0,s]} F - (w s - w 0)`. -/
private theorem isWeakSolutionDirichlet_setIntegral
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hF : IntegrableOn F (Ioc 0 T))
    (h : HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T))) (hu' : MemLp u' 2 (volume.restrict (Ioo 0 T)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 a b c (u t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        dirichletForcing (F t) v)
    (hw : ContinuousOn w (Icc 0 T))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w) {s : ℝ}
    (hs : s ∈ Icc 0 T) :
    IsWeakSolutionDirichlet a b c ((∫ r in Ioc 0 s, F r) - (w s - w 0))
      (∫ r in Ioc 0 s, u r) := by
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hsub : Ioo 0 s ⊆ Ioo 0 T := Ioo_subset_Ioo_right hs.2
  have hui : IntegrableOn u (Ioo 0 s) := IntegrableOn.mono_set (hu.integrable one_le_two) hsub
  have hFi : IntegrableOn F (Ioo 0 s) := hF.mono_set (hsub.trans Ioo_subset_Ioc_self)
  refine (isWeakSolutionDirichlet_iff_inner _ _).2 fun v => ?_
  rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  -- The time derivative integrates to the increment of `w`, tested against `v`.
  have hinc : ∫ r in Ioo 0 s, u' r v = ⟪w s, W1p.value (v : W1p mu Omega 2)⟫_ℝ -
      ⟪w 0, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
    have hz := h.inner_sub_inner_eq_integral_of_gelfandDual (z := fun _ => v) (z' := fun _ => 0)
      (hasWeakLineDerivOn_const _) hu hu' (memLp_const v) (memLp_const 0) hw
      (continuousOn_const (c := W1p0.valueL v)) hae (Filter.Eventually.of_forall fun _ => rfl)
      ⟨le_rfl, hs.1.trans hs.2⟩ hs
    simp only [W1p0.valueL_apply, zero_apply, add_zero] at hz
    rw [hz, intervalIntegral.integral_of_le hs.1, integral_Ioc_eq_integral_Ioo]
  -- The weak equation, integrated over `(0, s)`.
  have hform : ∫ r in Ioo 0 s, energyFormH1 a b c (u r : W1p mu Omega 2) (v : W1p mu Omega 2) =
      ∫ r in Ioo 0 s, (⟪W1p.value (v : W1p mu Omega 2), F r⟫_ℝ - u' r v) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub heq] with r hr
    rw [real_inner_comm, ← dirichletForcing_apply, ← hr v]
    ring
  -- The energy form commutes with the time integral.
  have hcomm : energyFormH1 a b c ((∫ r in Ioo 0 s, u r : W1p0 mu Omega 2) : W1p mu Omega 2)
      (v : W1p mu Omega 2) =
      ∫ r in Ioo 0 s, energyFormH1 a b c (u r : W1p mu Omega 2) (v : W1p mu Omega 2) := by
    have hL := ((energyFormH1L0 hcoeff).flip v).integral_comp_comm hui
    simp only [ContinuousLinearMap.flip_apply, energyFormH1L0_apply] at hL
    exact hL.symm
  have hFi' : Integrable F (volume.restrict (Ioo 0 s)) := hFi
  have hu'v : IntegrableOn (fun r => u' r v) (Ioo 0 s) :=
    IntegrableOn.mono_set (hu'.integrable_apply (q := 2) (memLp_const v)) hsub
  rw [hcomm, hform, integral_sub (hFi'.const_inner (W1p.value (v : W1p mu Omega 2))) hu'v,
    integral_inner hFi', hinc, inner_sub_left, inner_sub_left,
    real_inner_comm (W1p.value (v : W1p mu Omega 2)) (∫ r in Ioo 0 s, F r)]

/-- The value of the time integral of `u` is the time integral of its continuous `L²(Ω)`-valued
representative `w`. -/
private theorem value_setIntegral (hu : MemLp u 2 (volume.restrict (Ioo 0 T)))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w) {s : ℝ}
    (hs : s ∈ Icc 0 T) :
    W1p.value ((∫ r in Ioc 0 s, u r : W1p0 mu Omega 2) : W1p mu Omega 2) =
      ∫ r in Ioc 0 s, w r := by
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hsub : Ioo 0 s ⊆ Ioo 0 T := Ioo_subset_Ioo_right hs.2
  rw [← W1p0.valueL_apply, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    ← W1p0.valueL.integral_comp_comm (IntegrableOn.mono_set (hu.integrable one_le_two) hsub)]
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub hae)

/-- **Duhamel's formula for the parabolic Dirichlet problem.** Let the energy form of
`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be bounded and coercive on `H¹₀(Ω)`, and let
`u ∈ L²(0, T; H¹₀(Ω))` be a weak solution of `∂ₜu + L u = F` with `F ∈ L¹(0, T; L²(Ω))`: the image
of `u` in `H⁻¹(Ω)` has the weak time derivative `u' ∈ L²(0, T; H⁻¹(Ω))`, and
`u'(t)(v) + a(u(t), v) = ⟪F t, v⟫` for every `v ∈ H¹₀(Ω)` and almost every `t ∈ (0, T)`. Then the
continuous `L²(Ω)`-valued representative `w` of `u` is given on `[0, T]` by Duhamel's formula
`w t = e^{-tL} w(0) + ∫_{(0,t]} e^{-(t-s)L} F(s) ds`, with the Dirichlet semigroup `e^{-tL}`. -/
theorem eqOn_dirichletSemigroup_add_duhamel
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (hF : IntegrableOn F (Ioc 0 T))
    (h : HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T))) (hu' : MemLp u' 2 (volume.restrict (Ioo 0 T)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 a b c (u t : W1p mu Omega 2) (v : W1p mu Omega 2) =
        dirichletForcing (F t) v)
    (hw : ContinuousOn w (Icc 0 T))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w) :
    EqOn w (fun t => (dirichletSemigroup hcoeff hcoercive).realOperator t (w 0) +
      (dirichletSemigroup hcoeff hcoercive).duhamel F t) (Icc 0 T) := by
  refine (dirichletSemigroup hcoeff hcoercive).eqOn_realOperator_add_duhamel_Icc
    hF hw rfl fun s hs => ?_
  -- `∫_{(0,s]} w` lies on the graph of the Dirichlet realization, with value
  -- `∫_{(0,s]} F - (w s - w 0)`.
  have hgraph : ((∫ r in Ioc 0 s, w r), (∫ r in Ioc 0 s, F r) - (w s - w 0)) ∈
      (dirichletOperator hcoeff hcoercive).graph :=
    (mem_graph_dirichletOperator_iff hcoeff hcoercive).2 ⟨_, value_setIntegral hu hae hs,
      isWeakSolutionDirichlet_setIntegral hcoeff hF h hu hu' heq hw hae hs⟩
  rw [dirichletSemigroup_generator]
  refine ⟨by rw [LinearPMap.neg_domain]; exact LinearPMap.mem_domain_of_mem_graph hgraph, ?_⟩
  rw [LinearPMap.neg_apply, ← (LinearPMap.image_iff _).2 hgraph]
  abel

/-- **The Dirichlet semigroup solves the parabolic Dirichlet problem.** Under the hypotheses of
`TauCeti.PDE.eqOn_dirichletSemigroup_add_duhamel` without forcing, the continuous `L²(Ω)`-valued
representative `w` of a weak solution of `∂ₜu + L u = 0` is the orbit `w t = e^{-tL} w(0)` of its
initial value on `[0, T]`. -/
theorem eqOn_dirichletSemigroup
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (h : HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T))) (hu' : MemLp u' 2 (volume.restrict (Ioo 0 T)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 a b c (u t : W1p mu Omega 2) (v : W1p mu Omega 2) = 0)
    (hw : ContinuousOn w (Icc 0 T))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w) :
    EqOn w (fun t => (dirichletSemigroup hcoeff hcoercive).realOperator t (w 0)) (Icc 0 T) := by
  intro t ht
  have h0 := eqOn_dirichletSemigroup_add_duhamel hcoeff hcoercive (F := 0) integrableOn_zero h hu
    hu' (by simpa using heq) hw hae ht
  simpa using h0

end PDE

end TauCeti
