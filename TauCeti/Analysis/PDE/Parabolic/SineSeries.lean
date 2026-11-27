/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Semigroup
public import TauCeti.Analysis.PDE.Spectrum.Interval

/-!
# The heat equation on an interval in the sine basis

Let `u : ℝ → H¹₀(a, b)` be a weak solution of the heat equation `∂ₜu - Δu = 0` in
`(t₀, t₁) × (a, b)` with zero boundary values: the image of `u` in `H⁻¹(a, b)` has a weak time
derivative `u'` with `u'(t)(v) + ∫_a^b ∂ₓu(t) ∂ₓv = 0` for every `v ∈ H¹₀(a, b)` and almost every
`t`, and `t ↦ u(t) ∈ L²(a, b)` has a representative `w` continuous on `[t₀, t₁]`. These are
hypotheses of the results below, and `u` need only be integrable in time, not square integrable.
The weak solutions of `TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1` (in
`TauCeti.Analysis.PDE.Parabolic.DirichletProblem`), which lie in `L²(t₀, t₁; H¹₀(a, b))`, satisfy
them.

In the sine basis `eₖ = √(2 / (b - a)) sin ((k + 1) π (x - a) / (b - a))` of `L²(a, b)`
(`TauCeti.PDE.sineHilbertBasis`), made of Dirichlet eigenfunctions with eigenvalues
`κₖ = ((k + 1) π / (b - a))²`, the heat flow is Fourier's separation of variables:

* each coefficient of the continuous representative decays at the rate of its eigenvalue,
  `⟪eₖ, w t⟫ = e^{-κₖ (t - t₀)} ⟪eₖ, w t₀⟫` for `t ∈ [t₀, t₁]`
  (`TauCeti.PDE.inner_sineHilbertBasis_eq_exp_mul_of_hasWeakLineDerivOn_gelfandDual`), since by
  Duhamel's formula `w t` is the Dirichlet semigroup applied to `w t₀`, and the semigroup is the
  eigenfunction expansion (`TauCeti.PDE.hasSum_dirichletSemigroup_apply`);
* for almost every `t`, the Dirichlet energy of `u` is
  `∫_a^b |∂ₓu(t)|² = ∑ₖ κₖ e^{-2 κₖ (t - t₀)} ⟪eₖ, w t₀⟫²`
  (`TauCeti.PDE.ae_hasSum_energyFormH1_of_hasWeakLineDerivOn_gelfandDual`), by Parseval's identity
  for the Dirichlet energy (`TauCeti.PDE.hasSum_energyFormH1_self_intervalDomain`).

The initial value `w t₀` lies in `H¹₀(a, b)` exactly when `∑ₖ κₖ ⟪eₖ, w t₀⟫² < ∞`
(`TauCeti.PDE.exists_value_eq_iff_summable_intervalDomain`), the value at `t = t₀` of the series
for the energy. The example `∑ₖ sin (k x) / k` on `(0, π)`, whose energy blows up as `t ↓ 0`, is
in `TauCeti.Examples.Analysis.PDE.Parabolic.SineSeries`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2 (the embedding of the energy space
  into `C([0, T]; L²)`) and §7.1 (weak solutions of second-order parabolic equations).
* G. B. Folland, *Fourier Analysis and its Applications*, §4.2 (the heat equation on an interval
  by sine series).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped Real InnerProductSpace

variable {a b : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup

section Heat

variable {t₀ t₁ : ℝ}

/-- **The heat equation on an interval in sine coefficients.** Let `u` be a weak solution of
`∂ₜu - Δu = 0` in `(t₀, t₁) × (a, b)` with zero boundary values, and `w` the continuous
`L²(a, b)`-valued representative of `u`. Then for `t ∈ [t₀, t₁]` each sine coefficient of `w t`
decays at the rate of its eigenvalue:
`⟪eₖ, w t⟫ = exp (-((k + 1) π / (b - a))² (t - t₀)) ⟪eₖ, w t₀⟫`, with `(eₖ)` the sine basis
`TauCeti.PDE.sineHilbertBasis`. Of `u` itself only integrability in time is assumed. -/
theorem inner_sineHilbertBasis_eq_exp_mul_of_hasWeakLineDerivOn_gelfandDual (hab : a < b)
    {u : ℝ → W1p0 volume (intervalDomain a b) 2}
    {u' : ℝ → StrongDual ℝ (W1p0 volume (intervalDomain a b) 2)}
    {w : ℝ → Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))}
    (hd : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain a b) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : IntegrableOn u (Ioo t₀ t₁))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 volume (intervalDomain a b) 2,
      u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain a b) 2)
        (v : W1p volume (intervalDomain a b) 2) = 0)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w)
    {t : ℝ} (ht : t ∈ Icc t₀ t₁) (k : ℕ) :
    ⟪sineHilbertBasis hab k, w t⟫_ℝ =
      Real.exp (-((((k : ℝ) + 1) * π / (b - a)) ^ 2 * (t - t₀))) *
        ⟪sineHilbertBasis hab k, w t₀⟫_ℝ := by
  obtain ⟨hcoeff, hcoercive⟩ := exists_isCoercive_laplacian_of_isBounded (n := 0)
    (isBounded_intervalDomain (a := a) (b := b))
  choose v hv using exists_value_eq_sineHilbertBasis hab
  exact inner_eq_exp_mul_of_hasWeakLineDerivOn_gelfandDual hcoeff hcoercive (sineHilbertBasis hab)
    (fun i => (hv i).1) (fun i => (hv i).2) hd hu heq hw hae ht k

/-- **The Dirichlet energy of the heat flow on an interval.** Let `u` be a weak solution of
`∂ₜu - Δu = 0` in `(t₀, t₁) × (a, b)` with zero boundary values, `w` its continuous
`L²(a, b)`-valued representative and `cₖ = ⟪eₖ, w t₀⟫` the sine coefficients of its initial value.
Then for almost every `t ∈ (t₀, t₁)`, with `κₖ = ((k + 1) π / (b - a))²`,

`∫_a^b |∂ₓu(t)|² = ∑ₖ κₖ exp (-2 κₖ (t - t₀)) cₖ²`.

Of `u` itself only integrability in time is assumed. -/
theorem ae_hasSum_energyFormH1_of_hasWeakLineDerivOn_gelfandDual (hab : a < b)
    {u : ℝ → W1p0 volume (intervalDomain a b) 2}
    {u' : ℝ → StrongDual ℝ (W1p0 volume (intervalDomain a b) 2)}
    {w : ℝ → Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))}
    (hd : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain a b) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : IntegrableOn u (Ioo t₀ t₁))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 volume (intervalDomain a b) 2,
      u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain a b) 2)
        (v : W1p volume (intervalDomain a b) 2) = 0)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w) :
    ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
      HasSum (fun k : ℕ => (((k : ℝ) + 1) * π / (b - a)) ^ 2 *
          Real.exp (-(2 * (((k : ℝ) + 1) * π / (b - a)) ^ 2 * (t - t₀))) *
            ⟪sineHilbertBasis hab k, w t₀⟫_ℝ ^ 2)
        (energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain a b) 2)
          (u t : W1p volume (intervalDomain a b) 2)) := by
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t h₁ h₂
  convert hasSum_energyFormH1_self_intervalDomain hab (u t) using 2 with k
  rw [← W1p0.valueL_apply, h₁, inner_sineHilbertBasis_eq_exp_mul_of_hasWeakLineDerivOn_gelfandDual
    hab hd hu heq hw hae (Ioo_subset_Icc_self h₂) k, mul_pow, sq (Real.exp _), ← Real.exp_add]
  ring_nf

end Heat

end PDE

end TauCeti
