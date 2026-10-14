/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.PDE.Regularity.HolderContinuity
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Sobolev.W1p.Extension

/-!
# De Giorgi's theorem for a coefficient with a jump

This file runs the energy method and De Giorgi's theorem on an explicit equation whose coefficient
is discontinuous, so that no regularity theory for continuous coefficients applies to it.

The coefficient field is `TauCeti.PDE.jumpCoefficient n`, the matrix `κ(x) I` on `ℝⁿ⁺¹` with
`κ(x) = 1` on the open half-space `{x₀ > 0}` and `κ(x) = 2` on its complement. It is measurable
and uniformly elliptic with constants `1` and `2`, and it is discontinuous at every point of the
hyperplane `{x₀ = 0}` (`TauCeti.PDE.not_continuousAt_jumpCoefficient`), in particular inside the
unit ball.

On a bounded nonempty open set `Ω`, consider the Dirichlet problem

`-div(κ ∇u) = 0` in `Ω`, `u = x₀` on `∂Ω`,

in its weak form: `u ∈ H¹(Ω)`, `u - g ∈ H¹₀(Ω)` for a function `g ∈ H¹(Ω)` equal to the
coordinate `x₀` almost everywhere, and `∫_Ω κ ∇u · ∇v = 0` for every `v ∈ H¹₀(Ω)`.
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_jumpCoefficient` proves:

* the problem has exactly one weak solution, by Lax–Milgram; a priori it is only known to lie in
  `H¹(Ω)`;
* the solution is not constant, since a constant minus `x₀` is not in `H¹₀(Ω)`
  (`TauCeti.W1p0.setIntegral_inner_gradient_eq_zero`);
* by De Giorgi's theorem its precise representative is Hölder continuous on every compact subset
  of `Ω`, with an exponent `α ∈ (0, 1]` depending only on the dimension.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino (1957).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.3 and Theorem 8.24.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped NNReal Topology Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- The coefficient field `κ(x) I` on `ℝⁿ⁺¹` with `κ(x) = 1` where `x₀ > 0` and `κ(x) = 2`
elsewhere: a uniformly elliptic matrix field with a jump across the hyperplane `{x₀ = 0}`. -/
def jumpCoefficient (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (if 0 < x 0 then 1 else 2 : ℝ) • 1

/-- Unfolding `TauCeti.PDE.jumpCoefficient`. -/
theorem jumpCoefficient_apply (x : EuclideanSpace ℝ (Fin (n + 1))) :
    jumpCoefficient n x = (if 0 < x 0 then 1 else 2 : ℝ) • 1 :=
  (rfl)

/-- The jump coefficient is uniformly elliptic with constants `1` and `2` on every set. -/
theorem uniformlyEllipticOn_jumpCoefficient (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) :
    UniformlyEllipticOn Ω (jumpCoefficient n) 1 2 :=
  uniformlyEllipticOn_smul_one Ω _ one_pos one_le_two fun x _ => by
    split_ifs <;> norm_num

/-- The jump coefficient is strongly measurable. -/
theorem stronglyMeasurable_jumpCoefficient : StronglyMeasurable (jumpCoefficient n) :=
  (Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) measurable_const
    measurable_const).stronglyMeasurable.smul_const _

/-- The jump coefficient is discontinuous at every point of the hyperplane `{x₀ = 0}`. -/
theorem not_continuousAt_jumpCoefficient {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x 0 = 0) :
    ¬ ContinuousAt (jumpCoefficient n) x := by
  intro hcont
  -- Approach `x` from the side `{x₀ > 0}`, where the coefficient is the identity.
  let γ : ℝ → EuclideanSpace ℝ (Fin (n + 1)) := fun t => x + t • EuclideanSpace.single 0 1
  have hγ : Filter.Tendsto γ (𝓝[>] 0) (𝓝 x) := by
    have : Continuous γ := by fun_prop
    simpa [γ] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := ((continuous_id.matrix_elem 0 0).continuousAt.comp hcont).tendsto.comp hγ
  have hval : ∀ᶠ t in 𝓝[>] (0 : ℝ), jumpCoefficient n (γ t) 0 0 = 1 :=
    eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => by
      simp [jumpCoefficient, γ, hx, ht]
  have := tendsto_nhds_unique (hlim.congr' hval) tendsto_const_nhds
  simp [jumpCoefficient, hx] at this

/-- The coordinate function `x₀` on a bounded open set, as an element of `H¹(Ω)` whose weak
gradient is `e₀`. -/
private theorem exists_value_ae_eq_apply_zero {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    ∃ g : W1p volume Omega 2,
      W1p.value g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        (fun x => x 0) ∧
      ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
        ⟪W1p.gradient g x, EuclideanSpace.single 0 1⟫_ℝ = 1 := by
  have hK : IsCompact (closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    hb.isCompact_closure
  have hx₀ : ContDiffOn ℝ 1 (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x 0) univ := by fun_prop
  have hg : ∃ g : W1p volume Omega 2,
      W1p.value g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        (fun x => x 0) ∧
      W1p.gradient g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        ∇ (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x 0) :=
    W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact isOpen_univ hx₀ hK subset_closure
      (subset_univ _)
  obtain ⟨g, hgv, hgg⟩ := hg
  refine ⟨g, hgv, ?_⟩
  have hf : (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y 0) =
      EuclideanSpace.proj (0 : Fin (n + 1)) := by
    ext y
    simp
  filter_upwards [hgg] with x hx
  rw [hx, ← InnerProductSpace.toDual_apply_apply, toDual_gradient, hf, ContinuousLinearMap.fderiv]
  simp

/-- On a bounded nonempty open set, a function of `H¹(Ω)` with the boundary values of a function
`g` whose gradient has component `1` along `e₀` is not constant. -/
private theorem not_exists_value_ae_eq_const {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hne : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).Nonempty) {u g : W1p volume Omega 2}
    (hg : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ⟪W1p.gradient g x, EuclideanSpace.single 0 1⟫_ℝ = 1)
    (hug : u - g ∈ w1p0Submodule volume Omega 2) :
    ¬ ∃ c : ℝ, W1p.value u =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
      fun _ => c := by
  rintro ⟨c, hc⟩
  have hfin : volume (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) < ⊤ := hb.measure_lt_top
  have : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hfin.ne
  -- A constant has zero gradient, so `∫_Ω ⟪∇(u - g), e₀⟫ = -|Ω|`, which is not zero.
  have hgu : W1p.gradient u = 0 := by
    rw [W1p.ext_value (Lp.ext (hc.trans (by rw [W1p.value_const]; exact
      (Lp.coeFn_const _ _ c).symm))), W1p.gradient_const]
  have hsub : W1p.gradient (u - g) = W1p.gradient u - W1p.gradient g := by
    rw [← W1p.gradientL_apply, map_sub, W1p.gradientL_apply, W1p.gradientL_apply]
  have hgrad : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ⟪W1p.gradient (u - g) x, EuclideanSpace.single 0 1⟫_ℝ = -1 := by
    filter_upwards [hg, Lp.coeFn_sub (W1p.gradient u) (W1p.gradient g),
      Lp.coeFn_zero (EuclideanSpace ℝ (Fin (n + 1))) 2
        (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))]
      with x hgx hsx hzx
    rw [hsub, hsx, Pi.sub_apply, hgu, hzx, Pi.zero_apply, zero_sub, inner_neg_left, hgx]
  have hint : ∫ x in Omega, ⟪W1p.gradient (u - g) x, EuclideanSpace.single 0 1⟫_ℝ = 0 :=
    W1p0.setIntegral_inner_gradient_eq_zero hb ⟨u - g, hug⟩ (EuclideanSpace.single 0 1)
  rw [integral_congr_ae hgrad] at hint
  have hpos : 0 < volume.real (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    ENNReal.toReal_pos (Omega.isOpen.measure_pos volume hne).ne' hfin.ne
  simp at hint
  linarith

/-- The Dirichlet problem for the jump coefficient: on a bounded open set and for every
`g ∈ H¹(Ω)`, the weak solution of `-div(κ ∇u) = 0` in `Ω`, `u = g` on `∂Ω` exists and is
unique, by Lax–Milgram. -/
private theorem existsUnique_jumpCoefficient
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) :
    ∃! u : W1p volume Omega 2, u - g ∈ w1p0Submodule volume Omega 2 ∧
      ∀ v : W1p0 volume Omega 2,
        energyFormH1 (jumpCoefficient n) 0 0 u (v : W1p volume Omega 2) = 0 := by
  have hRb := hb.subset_ball_lt 0 (0 : EuclideanSpace ℝ (Fin (n + 1)))
  obtain ⟨R, hR, hball⟩ := hRb
  have hzero : ∀ v : W1p0 volume Omega 2, ∫ x in Omega,
      (0 : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) x *
        W1p.value (v : W1p volume Omega 2) x = 0 := fun v => by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))] with x hx
    rw [Pi.zero_apply, hx, Pi.zero_apply, zero_mul]
  have hexu :=
    UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
      (b := 0) (c := 0) (uniformlyEllipticOn_jumpCoefficient _)
      stronglyMeasurable_jumpCoefficient.aestronglyMeasurable aestronglyMeasurable_const
      aestronglyMeasurable_const le_rfl (fun _ _ => by simp) (gamma := 0) (fun _ _ => by simp)
      (fun _ _ => le_rfl) hR.le hball (by simp) 0 g
  simpa only [hzero] using hexu

/-- **De Giorgi's theorem on an equation with a discontinuous coefficient.** There is
`α ∈ (0, 1]`, depending only on the dimension, such that the following holds on every bounded
nonempty open set `Ω ⊆ ℝⁿ⁺¹`. Let `g ∈ H¹(Ω)` be the coordinate function `x₀`. The Dirichlet
problem `-div(κ ∇u) = 0` in `Ω`, `u = x₀` on `∂Ω`, for the coefficient
`κ I = TauCeti.PDE.jumpCoefficient n` with a jump across `{x₀ = 0}`, has exactly one weak solution
`u ∈ H¹(Ω)`, that is `u - g ∈ H¹₀(Ω)` and `∫_Ω κ ∇u · ∇v = 0` for every `v ∈ H¹₀(Ω)`. This
solution is not constant, and its precise representative is Hölder continuous with exponent `α`
on every compact subset of `Ω`. -/
theorem exists_holderOnWith_preciseRepresentative_jumpCoefficient (n : ℕ) :
    ∃ α : ℝ≥0, 0 < α ∧ α ≤ 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))},
      Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
      (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).Nonempty →
      ∃ g : W1p volume Omega 2,
        W1p.value g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
          (fun x => x 0) ∧
        (∃! u : W1p volume Omega 2, u - g ∈ w1p0Submodule volume Omega 2 ∧
          ∀ v : W1p0 volume Omega 2,
            energyFormH1 (jumpCoefficient n) 0 0 u (v : W1p volume Omega 2) = 0) ∧
        ∀ u : W1p volume Omega 2, (u - g ∈ w1p0Submodule volume Omega 2 ∧
          ∀ v : W1p0 volume Omega 2,
            energyFormH1 (jumpCoefficient n) 0 0 u (v : W1p volume Omega 2) = 0) →
          (¬ ∃ c : ℝ,
            W1p.value u =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
              fun _ => c) ∧
          ∀ K : Set (EuclideanSpace ℝ (Fin (n + 1))), IsCompact K →
            K ⊆ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
            ∃ C : ℝ≥0, HolderOnWith C α (preciseRepresentative volume (W1p.value u)) K := by
  obtain ⟨α, hα, hα1, hDG⟩ := exists_holderOnWith_preciseRepresentative_of_isCompact
    (ι := Fin (n + 1)) (mu := volume) (lam := 1) (Lam := 2)
  refine ⟨α, hα, hα1, fun {Omega} hb hne => ?_⟩
  have hg := exists_value_ae_eq_apply_zero hb
  obtain ⟨g, hgv, hgg⟩ := hg
  refine ⟨g, hgv, existsUnique_jumpCoefficient hb g, fun u hu => ⟨?_, fun K hK hKΩ => ?_⟩⟩
  · exact not_exists_value_ae_eq_const hb hne hgg hu.1
  · exact hDG (uniformlyEllipticOn_jumpCoefficient _)
      stronglyMeasurable_jumpCoefficient.aestronglyMeasurable hu.2 hK hKΩ

end PDE

end TauCeti
