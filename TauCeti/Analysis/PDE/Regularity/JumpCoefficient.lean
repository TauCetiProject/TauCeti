/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.PDE.Regularity.HolderContinuity
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.Analysis.Sobolev.W1p.ChainRule
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.W1p.LevelSet
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv

/-!
# De Giorgi's theorem and failure of `H²` regularity for a coefficient with a jump

This file runs the energy method and De Giorgi's theorem on an explicit equation whose coefficient
is discontinuous, so that no regularity theory for continuous coefficients applies to it, and shows
that interior `H²` regularity fails for the same coefficient.

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
  (`TauCeti.W1p0.not_exists_value_ae_eq_const_of_inner_gradient_eq_one`);
* by De Giorgi's theorem its precise representative is Hölder continuous on every compact subset
  of `Ω`, with an exponent `α ∈ (0, 1]` depending only on the dimension.

For this coefficient De Giorgi's theorem gives Hölder continuity, but `H²` regularity fails near
the jump: weak solutions need not lie in `H²`. The function `u(x) = κ(x)⁻¹ x₀`
(`TauCeti.PDE.jumpSolution`), equal to `x₀` where `x₀ > 0` and to `x₀ / 2` elsewhere, has the
constant flux `κ ∇u = e₀`, so on every bounded open set it is a weak solution of
`-div(κ ∇u) = 0` (`TauCeti.PDE.energyFormH1_jumpCoefficient_eq_zero`). Its weak derivative
`∂₀u = κ⁻¹` jumps across the hyperplane, and no element of `W^{2,p}(V)`, for any `1 ≤ p < ∞`,
agrees with `u` on an open set `V` meeting the hyperplane
(`TauCeti.PDE.not_exists_wkp_two_value_ae_eq_jumpSolution`). Together
(`TauCeti.PDE.exists_energyFormH1_jumpCoefficient_eq_zero_not_exists_wkp_two`) this shows that the
interior `H²` regularity theorem for Lipschitz coefficients
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`) does not
extend to bounded measurable ones. In dimension one this is the coefficient `1 + 1_{x ≤ 0}` on an
interval around `0`.

The proof that `u` is not in `W^{2,p}` uses no explicit second derivative. If it were, `∂₀u` would
be a `W^{1,p}` function on a ball centred on the hyperplane taking only the values `1` and `1 / 2`.
The weak gradient of a Sobolev function vanishes almost everywhere on each level set
(`TauCeti.W1p.gradient_ae_eq_zero_on_level_set`), so `∂₀u` would be constant on the ball
(`TauCeti.W1p.exists_value_ae_eq_const_of_gradient_eq_zero`), which it is not.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino (1957).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.3, Theorem 8.8 (interior `H²` regularity) and Theorem 8.24.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped NNReal ENNReal Topology Gradient InnerProductSpace

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

/-- The coordinate function `x₀` on a bounded open set, as an element of `W^{1,p}(Ω)` with weak
gradient `e₀`; this specializes `TauCeti.W1p.exists_value_gradient_ae_eq_continuousLinearMap` to
the coordinate functional. -/
private theorem exists_value_ae_eq_apply_zero {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    ∃ g : W1p volume Omega p,
      W1p.value g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        (fun x => x 0) ∧
      W1p.gradient g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        fun _ => EuclideanSpace.single 0 1 := by
  obtain ⟨g, hgv, hgg⟩ := W1p.exists_value_gradient_ae_eq_continuousLinearMap (mu := volume)
    (p := p) hb (EuclideanSpace.proj (0 : Fin (n + 1)))
  -- The gradient of the coordinate function `x₀` is `e₀`.
  have he₀ : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm
      (EuclideanSpace.proj (0 : Fin (n + 1))) = EuclideanSpace.single 0 1 :=
    ext_inner_right ℝ fun y => by
      simp [InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_left]
  rw [he₀] at hgg
  refine ⟨g, ?_, hgg⟩
  filter_upwards [hgv] with x hx
  simp [hx]

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
  obtain ⟨R, hball⟩ := hb.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
  have hexu :=
    UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
      (b := 0) (c := 0) (uniformlyEllipticOn_jumpCoefficient _)
      stronglyMeasurable_jumpCoefficient.aestronglyMeasurable aestronglyMeasurable_const
      aestronglyMeasurable_const (beta := 0) (fun _ _ => by simp) (gamma := 0)
      (fun _ _ => by simp) (fun _ _ => le_rfl) hball (by simp) 0 g
  simpa only [zero_apply] using hexu

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
  have hg := exists_value_ae_eq_apply_zero (p := 2) hb
  obtain ⟨g, hgx, hgg⟩ := hg
  refine ⟨g, hgx, existsUnique_jumpCoefficient hb g, fun u hu => ⟨?_, fun K hK hKΩ => ?_⟩⟩
  · refine W1p0.not_exists_value_ae_eq_const_of_inner_gradient_eq_one
      (w := EuclideanSpace.single 0 1) hb hne ?_ hu.1
    filter_upwards [hgg] with x hx
    rw [hx, EuclideanSpace.inner_single_left]
    simp
  · exact hDG (uniformlyEllipticOn_jumpCoefficient _)
      stronglyMeasurable_jumpCoefficient.aestronglyMeasurable hu.2 hK hKΩ

/-! ### An explicit weak solution that is not in `H²` -/

/-- **The explicit solution for the jump coefficient**, `u(x) = κ(x)⁻¹ x₀`: it is `x₀` where
`x₀ > 0` and `x₀ / 2` elsewhere. Its flux `κ ∇u` is the constant vector `e₀`, so it solves
`-div(κ ∇u) = 0` (`TauCeti.PDE.energyFormH1_jumpCoefficient_eq_zero`), while its gradient jumps
across the hyperplane `{x₀ = 0}`. -/
def jumpSolution (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  (if 0 < x 0 then 1 else 2 : ℝ)⁻¹ * x 0

/-- Unfolding `TauCeti.PDE.jumpSolution`. -/
theorem jumpSolution_apply (x : EuclideanSpace ℝ (Fin (n + 1))) :
    jumpSolution n x = (if 0 < x 0 then 1 else 2 : ℝ)⁻¹ * x 0 :=
  (rfl)

/-- **The explicit solution is a Sobolev function.** On a bounded open set and for
`1 ≤ p < ∞`, `TauCeti.PDE.jumpSolution` lies in `W^{1,p}(Ω)`, with weak gradient `κ(x)⁻¹ e₀`.
It is the midpoint of `x₀` and its positive part. -/
theorem exists_w1p_value_gradient_ae_eq_jumpSolution {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    ∃ u : W1p volume Omega p,
      W1p.value u =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        jumpSolution n ∧
      W1p.gradient u =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        fun x => (if 0 < x 0 then 1 else 2 : ℝ)⁻¹ • EuclideanSpace.single 0 1 := by
  obtain ⟨g, hgv', hgg⟩ := exists_value_ae_eq_apply_zero (p := p) hb
  refine ⟨midpoint ℝ g (W1p.posPart hp g), ?_, ?_⟩
  · filter_upwards [W1p.value_midpoint_ae g (W1p.posPart hp g), Lp.coeFn_posPart (W1p.value g),
      hgv'] with x hm hpos hx
    rw [hm, W1p.value_posPart, hpos, hx, jumpSolution_apply]
    split_ifs with h
    · rw [max_eq_left h.le]
      ring
    · rw [max_eq_right (not_lt.1 h)]
      ring
  · rw [W1p.gradient_midpoint, midpoint_eq_smul_add]
    filter_upwards [Lp.coeFn_smul (⅟2 : ℝ) (W1p.gradient g + W1p.gradient (W1p.posPart hp g)),
      Lp.coeFn_add (W1p.gradient g) (W1p.gradient (W1p.posPart hp g)),
      W1p.gradient_posPart_ae hp g, hgg, hgv'] with x hs ha hpos hg hx
    rw [hs, Pi.smul_apply, ha, Pi.add_apply, hpos, hg]
    split_ifs with h
    · rw [Set.indicator_of_mem (by simpa [hx] using h), hg, ← two_smul ℝ, smul_smul]
      norm_num
    · rw [Set.indicator_of_notMem (by simpa [hx] using h), add_zero]
      norm_num

/-- The flux of `TauCeti.PDE.jumpSolution`: the jump coefficient applied to `κ(x)⁻¹ e₀` is `e₀`. -/
private theorem matrixBilinearForm_jumpCoefficient_smul_single
    (x η : EuclideanSpace ℝ (Fin (n + 1))) :
    matrixBilinearForm (jumpCoefficient n x) η
      ((if 0 < x 0 then 1 else 2 : ℝ)⁻¹ • EuclideanSpace.single 0 1) =
      ⟪η, EuclideanSpace.single 0 1⟫_ℝ := by
  have hc0 : (if 0 < x 0 then 1 else 2 : ℝ) ≠ 0 := by split_ifs <;> norm_num
  rw [jumpCoefficient_apply]
  generalize (if 0 < x 0 then 1 else 2 : ℝ) = c at hc0 ⊢
  rw [matrixBilinearForm_smul_one_apply, EuclideanSpace.inner_single_right]
  simp [hc0]

/-- **The explicit solution is a weak solution.** On a bounded open set `Ω`, every `u ∈ H¹(Ω)`
equal to `TauCeti.PDE.jumpSolution` almost everywhere solves `-div(κ ∇u) = 0` weakly:
`∫_Ω κ ∇u · ∇v = 0` for every `v ∈ H¹₀(Ω)`. Its flux `κ ∇u` is the constant `e₀`. -/
theorem energyFormH1_jumpCoefficient_eq_zero {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (u : W1p volume Omega 2)
    (hu : W1p.value u =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
      jumpSolution n)
    (v : W1p0 volume Omega 2) :
    energyFormH1 (jumpCoefficient n) 0 0 u (v : W1p volume Omega 2) = 0 := by
  obtain ⟨w, hwv, hwg⟩ := exists_w1p_value_gradient_ae_eq_jumpSolution (n := n) (p := 2)
    ENNReal.ofNat_ne_top hb
  have huw : u = w := W1p.ext_value (Lp.ext (hu.trans hwv.symm))
  subst huw
  rw [energyFormH1_zero_zero_eq_setIntegral,
    ← W1p0.setIntegral_inner_gradient_eq_zero hb v (EuclideanSpace.single 0 1)]
  refine integral_congr_ae ?_
  filter_upwards [hwg] with x hx
  rw [hx, matrixBilinearForm_jumpCoefficient_smul_single]

/-- On a bounded open set, the weak derivative of `TauCeti.PDE.jumpSolution` along `e₀` is
`κ(x)⁻¹`. -/
private theorem hasWeakLineDerivOn_jumpSolution {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    HasWeakLineDerivOn volume Omega (jumpSolution n)
      (fun x => (if 0 < x 0 then 1 else 2 : ℝ)⁻¹) (EuclideanSpace.single 0 1) := by
  obtain ⟨w, hwv, hwg⟩ := exists_w1p_value_gradient_ae_eq_jumpSolution (n := n) hp hb
  refine (((W1p.hasWeakFDerivOn w).hasWeakLineDerivOn _).congr_ae hwv).congr_ae_deriv ?_
  filter_upwards [hwg] with x hx
  rw [innerSL_apply_apply, hx, real_inner_smul_left, EuclideanSpace.inner_single_left]
  simp

/-- The factor `κ(x)⁻¹` is not almost everywhere constant on a ball centred on the hyperplane
`{x₀ = 0}`: it is `1` on the open half ball where `x₀ > 0` and `1 / 2` on the one where `x₀ < 0`,
and both have positive measure. -/
private theorem not_ae_eq_const_inv_ite_ball {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z 0 = 0)
    {r : ℝ} (hr : 0 < r) (c : ℝ) :
    ¬ ∀ᵐ x ∂volume.restrict (ball z r), (if 0 < x 0 then 1 else 2 : ℝ)⁻¹ = c := by
  intro hc
  set e : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1 with he
  -- Every nonempty open subset of the ball contains a point where the factor is `c`.
  have hval {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hS : IsOpen S) (hSB : S ⊆ ball z r)
      (hne : S.Nonempty) : ∃ x ∈ S, (if 0 < x 0 then 1 else 2 : ℝ)⁻¹ = c := by
    have := ae_restrict_neBot.2 (hS.measure_ne_zero volume hne)
    obtain ⟨x, hxc, hxS⟩ :=
      ((ae_restrict_of_ae_restrict_of_subset hSB hc).and (ae_restrict_mem hS.measurableSet)).exists
    exact ⟨x, hxS, hxc⟩
  have hmem (t : ℝ) (ht : |t| < r) : z + t • e ∈ ball z r := by
    simpa [he, norm_smul] using ht
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin (n + 1)) => x 0 := by fun_prop
  obtain ⟨x, hx, hxc⟩ := hval (S := ball z r ∩ {x | 0 < x 0})
    (isOpen_ball.inter (isOpen_lt continuous_const hcont)) inter_subset_left
    ⟨z + (r / 2) • e, hmem _ (by rw [abs_of_pos (by positivity)]; linarith),
      by simp [he, hz, hr]⟩
  obtain ⟨y, hy, hyc⟩ := hval (S := ball z r ∩ {x | x 0 < 0})
    (isOpen_ball.inter (isOpen_lt hcont continuous_const)) inter_subset_left
    ⟨z + (-(r / 2)) • e, hmem _ (by rw [abs_neg, abs_of_pos (by positivity)]; linarith),
      by simp [he, hz, hr]⟩
  have hx0 : 0 < x 0 := hx.2
  have hy0 : y 0 < 0 := hy.2
  have h1 : c = 1 := by simpa [hx0] using hxc.symm
  have h2 : c = 2⁻¹ := by simpa [not_lt.2 hy0.le] using hyc.symm
  norm_num [h1] at h2

/-- **The explicit solution is not in `W^{2,p}` near the jump.** Let `1 ≤ p < ∞` and let `V` be an
open set containing a point of the hyperplane `{x₀ = 0}`. Then no element of `W^{2,p}(V)` agrees
almost everywhere with `TauCeti.PDE.jumpSolution` on `V`. -/
theorem not_exists_wkp_two_value_ae_eq_jumpSolution {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {V : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hzV : z ∈ V) (hz : z 0 = 0) :
    ¬ ∃ U : Wkp volume V p 2,
      Wkp.value 2 U =ᵐ[volume.restrict (V : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        jumpSolution n := by
  rintro ⟨U, hU⟩
  set κinv : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x => (if 0 < x 0 then 1 else 2 : ℝ)⁻¹
    with hκinv
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 V.isOpen z hzV
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball z r, isOpen_ball⟩
  have hBV : B ≤ V := hrV
  -- The weak derivative `∂₀u` of the value of `U` is a function `d ∈ W^{1,p}(V)`; on `B` it is
  -- the weak derivative `κ⁻¹` of the explicit solution.
  obtain ⟨d, hd, -⟩ :=
    Wkp.exists_hasWeakLineDerivOn_value_and_inner_gradient_ae_eq U (EuclideanSpace.single 0 1)
  have hdκ : W1p.value d =ᵐ[volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))] κinv :=
    ((hd.mono hBV).congr_ae (ae_restrict_of_ae_restrict_of_subset hrV hU)).ae_eq
      (hasWeakLineDerivOn_jumpSolution hp isBounded_ball)
  -- Its restriction to `B` takes the values `1` and `1 / 2` only, so its gradient vanishes.
  set dB := W1p.restrictL hBV d
  have hdBv : W1p.value dB =ᵐ[volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))] κinv :=
    (W1p.value_restrictL_ae hBV d).trans hdκ
  have hgrad : W1p.gradient dB = 0 := by
    refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [W1p.gradient_ae_eq_zero_on_level_set hp dB 1,
      W1p.gradient_ae_eq_zero_on_level_set hp dB 2⁻¹, hdBv] with x h1 h2 hx
    by_cases hx0 : 0 < x 0
    · exact h1 (by simp [hx, hκinv, hx0])
    · exact h2 (by simp [hx, hκinv, hx0])
  -- So it is constant on the connected ball, and so is `κ⁻¹`, which is impossible.
  obtain ⟨c, hc⟩ :=
    W1p.exists_value_ae_eq_const_of_gradient_eq_zero (convex_ball z r).isPreconnected hgrad
  refine not_ae_eq_const_inv_ite_ball hz hr c ?_
  filter_upwards [hc, hdBv] with x h1 h2
  rw [← h1, h2]

/-- **Interior `H²` regularity fails for a discontinuous coefficient.** On every bounded open set
`Ω ⊆ ℝⁿ⁺¹` there is a weak solution `u ∈ H¹(Ω)` of `-div(κ ∇u) = 0` for the jump coefficient
`κ I = TauCeti.PDE.jumpCoefficient n`, which is measurable and uniformly elliptic with constants `1`
and `2`, such that on no open `V ⊆ Ω` meeting the hyperplane `{x₀ = 0}` does `u` agree with an
element of `W^{2,p}(V)`, for any `1 ≤ p < ∞`; the same `u` works for every such `p`.

So the Lipschitz hypothesis on the coefficients of interior `H²` regularity
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`) cannot be
weakened to measurability, even with `b = 0`, `c = 0` and `f = 0`. For the same coefficient,
De Giorgi's theorem still gives Hölder continuity
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_jumpCoefficient`). -/
theorem exists_energyFormH1_jumpCoefficient_eq_zero_not_exists_wkp_two
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    ∃ u : W1p volume Omega 2,
      (∀ v : W1p0 volume Omega 2,
        energyFormH1 (jumpCoefficient n) 0 0 u (v : W1p volume Omega 2) = 0) ∧
      ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
        ∀ V : Opens (EuclideanSpace ℝ (Fin (n + 1))), V ≤ Omega → (∃ z ∈ V, z 0 = 0) →
          ¬ ∃ U : Wkp volume V p 2,
            Wkp.value 2 U =ᵐ[volume.restrict (V : Set (EuclideanSpace ℝ (Fin (n + 1))))]
              W1p.value u := by
  obtain ⟨u, hu, -⟩ := exists_w1p_value_gradient_ae_eq_jumpSolution (n := n) (p := 2)
    ENNReal.ofNat_ne_top hb
  refine ⟨u, energyFormH1_jumpCoefficient_eq_zero hb u hu,
    fun p _ hp V hV ⟨z, hzV, hz⟩ ⟨U, hU⟩ => ?_⟩
  exact not_exists_wkp_two_value_ae_eq_jumpSolution hp hzV hz
    ⟨U, hU.trans (ae_restrict_of_ae_restrict_of_subset hV hu)⟩

end PDE

end TauCeti
