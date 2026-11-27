/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.DirichletProblem
public import TauCeti.Analysis.PDE.Parabolic.Semigroup
public import TauCeti.Analysis.PDE.Spectrum.Interval
import Mathlib.Analysis.PSeries

/-!
# The heat equation on an interval in the sine basis

Let `u` be a weak solution of the heat equation `∂ₜu - Δu = 0` in `(t₀, t₁) × (a, b)` with zero
boundary values, in the sense of `TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`,
and let `w` be its continuous `L²(a, b)`-valued representative. In the sine basis
`eₖ = √(2 / (b - a)) sin ((k + 1) π (x - a) / (b - a))` of `L²(a, b)`
(`TauCeti.PDE.sineHilbertBasis`), made of Dirichlet eigenfunctions with eigenvalues
`κₖ = ((k + 1) π / (b - a))²`, the heat flow is Fourier's separation of variables:

* each coefficient decays at the rate of its eigenvalue,
  `⟪eₖ, w t⟫ = e^{-κₖ (t - t₀)} ⟪eₖ, w t₀⟫` for `t ∈ [t₀, t₁]`
  (`TauCeti.PDE.inner_sineHilbertBasis_eq_exp_mul_of_hasWeakLineDerivOn_gelfandDual`), since by
  Duhamel's formula `w t` is the Dirichlet semigroup applied to `w t₀`, and the semigroup is the
  eigenfunction expansion (`TauCeti.PDE.hasSum_dirichletSemigroup_apply`);
* for almost every `t`, the Dirichlet energy is
  `∫_a^b |∂ₓu(t)|² = ∑ₖ κₖ e^{-2 κₖ (t - t₀)} ⟪eₖ, w t₀⟫²`
  (`TauCeti.PDE.ae_hasSum_energyFormH1_of_hasWeakLineDerivOn_gelfandDual`), by Parseval's identity
  for the Dirichlet energy (`TauCeti.PDE.hasSum_energyFormH1_self_intervalDomain`);

The initial value lies in `H¹₀(a, b)` exactly when `∑ₖ κₖ ⟪eₖ, w t₀⟫² < ∞`
(`TauCeti.PDE.exists_value_eq_iff_summable_intervalDomain`), the value at `t = t₀` of the series
for the energy.

## The example `∑ₖ sin (k x) / k`

On `(0, π)` the eigenvalues are `k²` and the initial value `u₀ = ∑ₖ sin (k x) / k`, `k ≥ 1`, which
converges in `L²(0, π)` (`TauCeti.PDE.summable_inv_smul_of_ae_eq_sin`), is not in `H¹₀(0, π)`
(`TauCeti.PDE.not_exists_value_eq_of_hasSum_inv_smul_sin`): its coefficients `1 / k` against the
eigenvalues `k²` give `∑ₖ k² / k² = ∞`. The weak solution with this initial value is
`u(t) = ∑ₖ e^{-k² t} sin (k x) / k` (`TauCeti.PDE.hasSum_exp_div_smul_of_hasSum_inv_smul_sin`),
with Dirichlet energy `∫_0^π |∂ₓu(t)|² = (π / 2) ∑ₖ e^{-2 k² t}` for almost every `t`
(`TauCeti.PDE.ae_hasSum_energyFormH1_of_hasSum_inv_smul_sin`), which tends to infinity as `t ↓ 0`
(`TauCeti.PDE.tendsto_energyFormH1_atTop_of_hasSum_inv_smul_sin`). So `u` lies in
`L²(0, T; H¹₀(0, π))` and is continuous into `L²(0, π)`, but it is not continuous into
`H¹₀(0, π)`: `L²(0, π)`, not `H¹₀(0, π)`, is the space of initial values of the energy space.
Such a weak solution exists
for every `T > 0`, by `TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`.

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
open scoped Real InnerProductSpace Topology

variable {a b : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup

section Heat

variable {t₀ t₁ : ℝ}

/-- **The heat equation on an interval in sine coefficients.** Let `u` be a weak solution of
`∂ₜu - Δu = 0` in `(t₀, t₁) × (a, b)` with zero boundary values, and `w` the continuous
`L²(a, b)`-valued representative of `u`. Then for `t ∈ [t₀, t₁]` each sine coefficient of `w t`
decays at the rate of its eigenvalue:
`⟪eₖ, w t⟫ = exp (-((k + 1) π / (b - a))² (t - t₀)) ⟪eₖ, w t₀⟫`, with `(eₖ)` the sine basis
`TauCeti.PDE.sineHilbertBasis`. -/
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

`∫_a^b |∂ₓu(t)|² = ∑ₖ κₖ exp (-2 κₖ (t - t₀)) cₖ²`. -/
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

/-! ### The sine series `∑ₖ sin (k x) / k` on `(0, π)` -/

section SineSeries

variable {s : ℕ → Lp ℝ 2 (volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1))))}
  {f : Lp ℝ 2 (volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1))))}

/-- On `(0, π)` the eigenvalues `((k + 1) π / (π - 0))²` of the sine basis are `(k + 1)²`. -/
private theorem sq_mul_pi_div_pi_sub_zero (k : ℕ) :
    (((k : ℝ) + 1) * π / (π - 0)) ^ 2 = ((k : ℝ) + 1) ^ 2 := by
  rw [sub_zero, mul_div_assoc, div_self Real.pi_ne_zero, mul_one]

/-- The class of `sin ((k + 1) x)` is `√(π / 2)` times the `k`-th vector of the sine basis
of `L²(0, π)`. -/
private theorem eq_sqrt_smul_sineHilbertBasis_of_ae_eq_sin
    (hs : ∀ k : ℕ, s k =ᵐ[volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => Real.sin (((k : ℝ) + 1) * x 0)) (k : ℕ) :
    s k = √(π / 2) • sineHilbertBasis Real.pi_pos k := by
  refine Lp.ext ?_
  filter_upwards [hs k, sineHilbertBasis_ae_eq Real.pi_pos k,
    Lp.coeFn_smul (√(π / 2)) (sineHilbertBasis Real.pi_pos k)] with x h₁ h₂ h₃
  simp only [sub_zero] at h₂
  have hπ : π / 2 * (2 / π) = 1 := by field_simp
  rw [h₁, h₃, Pi.smul_apply, h₂, smul_eq_mul, ← mul_assoc, ← Real.sqrt_mul (by positivity), hπ,
    Real.sqrt_one, one_mul]
  congr 1
  field_simp

/-- **The series `∑ₖ sin (k x) / k` converges in `L²(0, π)`.** -/
theorem summable_inv_smul_of_ae_eq_sin
    (hs : ∀ k : ℕ, s k =ᵐ[volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => Real.sin (((k : ℝ) + 1) * x 0)) :
    Summable fun k : ℕ => ((k : ℝ) + 1)⁻¹ • s k := by
  have hg : Memℓp (fun k : ℕ => √(π / 2) * ((k : ℝ) + 1)⁻¹) 2 := by
    refine memℓp_gen ?_
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat, Real.rpow_two, sq_abs, mul_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ π / 2), inv_pow]
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
    exact_mod_cast this
  convert ((sineHilbertBasis Real.pi_pos).hasSum_repr_symm ⟨_, hg⟩).summable using 2 with k
  rw [eq_sqrt_smul_sineHilbertBasis_of_ae_eq_sin hs, smul_smul, mul_comm]

/-- The sine coefficients of `∑ₖ sin (k x) / k` are `⟪eₖ, f⟫ = √(π / 2) / (k + 1)`. -/
private theorem inner_sineHilbertBasis_of_hasSum_inv_smul_sin
    (hs : ∀ k : ℕ, s k =ᵐ[volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => Real.sin (((k : ℝ) + 1) * x 0))
    (hf : HasSum (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • s k) f) (k : ℕ) :
    ⟪sineHilbertBasis Real.pi_pos k, f⟫_ℝ = √(π / 2) / ((k : ℝ) + 1) := by
  have hk := hf.mapL (innerSL ℝ (sineHilbertBasis Real.pi_pos k))
  simp only [innerSL_apply_apply, eq_sqrt_smul_sineHilbertBasis_of_ae_eq_sin hs, inner_smul_right,
    orthonormal_iff_ite.1 (sineHilbertBasis Real.pi_pos).orthonormal k, mul_ite, mul_one,
    mul_zero] at hk
  rw [hk.unique (hasSum_single k fun j hj => ite_eq_right (Ne.symm hj)), ite_eq_left rfl]
  ring

/-- **`∑ₖ sin (k x) / k` is not in `H¹₀(0, π)`.** Its sine coefficients `√(π / 2) / k` against the
eigenvalues `k²` give `∑ₖ k² (π / 2) / k² = ∞`. -/
theorem not_exists_value_eq_of_hasSum_inv_smul_sin
    (hs : ∀ k : ℕ, s k =ᵐ[volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => Real.sin (((k : ℝ) + 1) * x 0))
    (hf : HasSum (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • s k) f) :
    ¬∃ v : W1p0 volume (intervalDomain 0 π) 2,
      W1p.value (v : W1p volume (intervalDomain 0 π) 2) = f := by
  rw [exists_value_eq_iff_summable_intervalDomain Real.pi_pos]
  simp only [inner_sineHilbertBasis_of_hasSum_inv_smul_sin hs hf, sq_mul_pi_div_pi_sub_zero]
  simp only [div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ π / 2)]
  rw [summable_congr fun k : ℕ => mul_div_cancel₀ (π / 2) (by positivity : ((k : ℝ) + 1) ^ 2 ≠ 0)]
  exact fun h => (by positivity : π / 2 ≠ 0) ((summable_const_iff _).1 h)

variable {T : ℝ} {u : ℝ → W1p0 volume (intervalDomain 0 π) 2}
  {u' : ℝ → StrongDual ℝ (W1p0 volume (intervalDomain 0 π) 2)}
  {w : ℝ → Lp ℝ 2 (volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1))))}

/-- **The heat flow of `∑ₖ sin (k x) / k` on `(0, π)`.** Let `u` be a weak solution of
`∂ₜu - Δu = 0` in `(0, T) × (0, π)` with zero boundary values whose continuous `L²(0, π)`-valued
representative `w` starts at `w 0 = ∑ₖ sin (k x) / k`. Then
`w t = ∑ₖ e^{-k² t} sin (k x) / k` in `L²(0, π)` for every `t ∈ [0, T]`. -/
theorem hasSum_exp_div_smul_of_hasSum_inv_smul_sin
    (hs : ∀ k : ℕ, s k =ᵐ[volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => Real.sin (((k : ℝ) + 1) * x 0))
    (hf : HasSum (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • s k) f)
    (hd : HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain 0 π) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : IntegrableOn u (Ioo 0 T))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 volume (intervalDomain 0 π) 2,
      u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
        (v : W1p volume (intervalDomain 0 π) 2) = 0)
    (hw : ContinuousOn w (Icc 0 T))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w) (h₀ : w 0 = f)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasSum (fun k : ℕ => (Real.exp (-(((k : ℝ) + 1) ^ 2 * t)) / ((k : ℝ) + 1)) • s k) (w t) := by
  convert (sineHilbertBasis Real.pi_pos).hasSum_repr (w t) using 2 with k
  rw [HilbertBasis.repr_apply_apply,
    inner_sineHilbertBasis_eq_exp_mul_of_hasWeakLineDerivOn_gelfandDual Real.pi_pos hd hu heq hw
      hae ht, h₀, inner_sineHilbertBasis_of_hasSum_inv_smul_sin hs hf,
    sq_mul_pi_div_pi_sub_zero, sub_zero, eq_sqrt_smul_sineHilbertBasis_of_ae_eq_sin hs, smul_smul]
  ring_nf

/-- **The Dirichlet energy of the heat flow of `∑ₖ sin (k x) / k`.** For the weak solution `u`
of `∂ₜu - Δu = 0` in `(0, T) × (0, π)` with zero boundary values and initial value
`∑ₖ sin (k x) / k`, for almost every `t ∈ (0, T)`

`∫_0^π |∂ₓu(t)|² = (π / 2) ∑ₖ e^{-2 k² t}`,

the sum running over `k ≥ 1`. -/
theorem ae_hasSum_energyFormH1_of_hasSum_inv_smul_sin
    (hs : ∀ k : ℕ, s k =ᵐ[volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => Real.sin (((k : ℝ) + 1) * x 0))
    (hf : HasSum (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • s k) f)
    (hd : HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain 0 π) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : IntegrableOn u (Ioo 0 T))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 volume (intervalDomain 0 π) 2,
      u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
        (v : W1p volume (intervalDomain 0 π) 2) = 0)
    (hw : ContinuousOn w (Icc 0 T))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w) (h₀ : w 0 = f) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      HasSum (fun k : ℕ => π / 2 * Real.exp (-(2 * ((k : ℝ) + 1) ^ 2 * t)))
        (energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
          (u t : W1p volume (intervalDomain 0 π) 2)) := by
  filter_upwards [ae_hasSum_energyFormH1_of_hasWeakLineDerivOn_gelfandDual Real.pi_pos hd hu heq hw
    hae] with t ht
  convert ht using 2 with k
  rw [h₀, inner_sineHilbertBasis_of_hasSum_inv_smul_sin hs hf, sq_mul_pi_div_pi_sub_zero, sub_zero,
    div_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- **The heat flow of `∑ₖ sin (k x) / k` is not continuous into `H¹₀(0, π)`.** For the weak
solution `u` of `∂ₜu - Δu = 0` in `(0, T) × (0, π)` with zero boundary values and initial value
`∑ₖ sin (k x) / k`, the energy `∫_0^π |∂ₓu(t)|² = (π / 2) ∑ₖ e^{-2 k² t}` tends to infinity as
`t ↓ 0`, outside a null set of times, although the weak solution of
`TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1` lies in `L²(0, T; H¹₀(0, π))`:
since `∑ₖ sin (k x) / k` is not in `H¹₀(0, π)`, the weak solution is not continuous into
`H¹₀(0, π)` at `t = 0`. Only `u ∈ L¹(0, T; H¹₀(0, π))` is assumed. -/
theorem tendsto_energyFormH1_atTop_of_hasSum_inv_smul_sin (hT : 0 < T)
    (hs : ∀ k : ℕ, s k =ᵐ[volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => Real.sin (((k : ℝ) + 1) * x 0))
    (hf : HasSum (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • s k) f)
    (hd : HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain 0 π) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : IntegrableOn u (Ioo 0 T))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 volume (intervalDomain 0 π) 2,
      u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
        (v : W1p volume (intervalDomain 0 π) 2) = 0)
    (hw : ContinuousOn w (Icc 0 T))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w) (h₀ : w 0 = f) :
    Tendsto (fun t => energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
      (u t : W1p volume (intervalDomain 0 π) 2)) (𝓝[>] 0 ⊓ ae volume) atTop := by
  have hae' := (ae_restrict_iff' measurableSet_Ioo).1
    (ae_hasSum_energyFormH1_of_hasSum_inv_smul_sin hs hf hd hu heq hw hae h₀)
  refine tendsto_atTop.2 fun M => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (M / (π / 2))
  -- The first `N` terms of `(π / 2) ∑ₖ e^{-2 k² t}` are continuous in `t` and sum to
  -- `N π / 2 > M` at `t = 0`.
  have hcont : Continuous fun t : ℝ => ∑ k ∈ Finset.range N,
      π / 2 * Real.exp (-(2 * ((k : ℝ) + 1) ^ 2 * t)) := by fun_prop
  have h0 : M < ∑ k ∈ Finset.range N, π / 2 * Real.exp (-(2 * ((k : ℝ) + 1) ^ 2 * 0)) := by
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    rwa [div_lt_iff₀ (by positivity)] at hN
  have hle : 𝓝[>] (0 : ℝ) ⊓ ae volume ≤ 𝓝 0 := inf_le_left.trans nhdsWithin_le_nhds
  filter_upwards [hle (hcont.continuousAt.eventually (lt_mem_nhds h0)),
    (inf_le_left : 𝓝[>] (0 : ℝ) ⊓ ae volume ≤ 𝓝[>] 0) (Ioo_mem_nhdsGT hT),
    (inf_le_right : 𝓝[>] (0 : ℝ) ⊓ ae volume ≤ ae volume) hae'] with t h₁ h₂ h₃
  exact h₁.le.trans (sum_le_hasSum _ (fun k _ => by positivity) (h₃ h₂))

end SineSeries

end Heat

end PDE

end TauCeti
