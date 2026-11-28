/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.DirichletProblem
public import TauCeti.Analysis.PDE.Parabolic.SineSeries
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.InnerProductSpace.Parseval

/-!
# The heat flow of the sine series `∑ₖ sin (k x) / k` on `(0, π)`

On `(0, π)` the Dirichlet eigenvalues of `-Δ` are `k²`, `k ≥ 1`, with eigenfunctions `sin (k x)`.
Let `sₖ` be the class of `x ↦ sin ((k + 1) x)` in `L²(0, π)` (`sinClass`), which is `√(π / 2)`
times the `k`-th vector of the orthonormal sine basis `TauCeti.PDE.sineHilbertBasis`. The series
`u₀ = ∑ₖ sin (k x) / k`, `k ≥ 1` (`sinSeries`), converges in `L²(0, π)`
(`summable_inv_smul_sinClass`); its coefficients in the orthonormal sine basis are `√(π / 2) / k`.
It is not in `H¹₀(0, π)` (`not_exists_value_eq_sinSeries`): against the eigenvalues `k²` its
coefficients give the divergent energy series `∑ₖ k² (π / 2) / k² = (π / 2) ∑ₖ 1`.

Let `u` be a weak solution of `∂ₜu - Δu = 0` in `(0, T) × (0, π)` with zero boundary values, `w`
its continuous `L²(0, π)`-valued representative, and `w 0 = u₀`. Then:

* `w t = ∑ₖ e^{-k² t} sin (k x) / k` in `L²(0, π)` for every `t ∈ [0, T]`
  (`hasSum_exp_div_smul_sinClass`);
* for almost every `t ∈ (0, T)` the Dirichlet energy of `u` is
  `∫_0^π |∂ₓu(t)|² = (π / 2) ∑ₖ e^{-2 k² t}` (`ae_hasSum_energyFormH1_sinSeries`);
* this energy tends to infinity as `t ↓ 0` outside a null set of times
  (`tendsto_energyFormH1_atTop_sinSeries`). So no representative of `u` is continuous into
  `H¹₀(0, π)` at `t = 0`, although `w` is continuous into `L²(0, π)`.

Such a weak solution exists for every `T > 0`, and it lies in `L²(0, T; H¹₀(0, π))`
(`exists_hasWeakLineDerivOn_gelfandDual_sinSeries`, from
`TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`): `L²(0, π)`, not `H¹₀(0, π)`,
is the space of initial values of the energy space.

## Main declarations

All declarations are in the namespace `TauCeti.Examples.HeatSineSeries`.

* `sinClass`, `sinClass_ae_eq`: the class of `sin ((k + 1) x)` in `L²(0, π)`.
* `sinSeries`, `hasSum_inv_smul_sinClass`: the initial value `∑ₖ sin (k x) / k`.
* `not_exists_value_eq_sinSeries`: it is not in `H¹₀(0, π)`.
* `hasSum_exp_div_smul_sinClass`, `ae_hasSum_energyFormH1_sinSeries`,
  `tendsto_energyFormH1_atTop_sinSeries`: the heat flow, its energy, and the blow-up.
* `exists_hasWeakLineDerivOn_gelfandDual_sinSeries`: the weak solution in the energy space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2 and §7.1.
* G. B. Folland, *Fourier Analysis and its Applications*, §4.2 (the heat equation on an interval
  by sine series).
-/

public section

noncomputable section

namespace TauCeti.Examples.HeatSineSeries

open Filter MeasureTheory Set TopologicalSpace TauCeti.PDE
open scoped Real InnerProductSpace Topology

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
  W1p0.instStrongDualNormedAddCommGroup

/-- The class of `x ↦ sin ((k + 1) x)` in `L²(0, π)`: `√(π / 2)` times the `k`-th vector of the
sine basis (`sinClass_ae_eq`). -/
def sinClass (k : ℕ) :
    Lp ℝ 2 (volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))) :=
  √(π / 2) • sineHilbertBasis Real.pi_pos k

/-- `sinClass k` is the class of `x ↦ sin ((k + 1) x)`. -/
theorem sinClass_ae_eq (k : ℕ) :
    sinClass k =ᵐ[volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => Real.sin (((k : ℝ) + 1) * x 0) := by
  filter_upwards [Lp.coeFn_smul (√(π / 2)) (sineHilbertBasis Real.pi_pos k),
    sineHilbertBasis_ae_eq Real.pi_pos k] with x h₁ h₂
  have hπ : π / 2 * (2 / π) = 1 := by field_simp
  rw [sinClass, h₁, Pi.smul_apply, h₂, smul_eq_mul, sub_zero, sub_zero, ← mul_assoc,
    ← Real.sqrt_mul (by positivity), hπ, Real.sqrt_one, one_mul]
  congr 1
  field_simp

/-- **The series `∑ₖ sin (k x) / k` converges in `L²(0, π)`.** -/
theorem summable_inv_smul_sinClass : Summable fun k : ℕ => ((k : ℝ) + 1)⁻¹ • sinClass k := by
  have hg : Memℓp (fun k : ℕ => √(π / 2) * ((k : ℝ) + 1)⁻¹) 2 := by
    refine memℓp_gen ?_
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat, Real.rpow_two, sq_abs, mul_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ π / 2), inv_pow]
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
    exact_mod_cast this
  convert ((sineHilbertBasis Real.pi_pos).hasSum_repr_symm ⟨_, hg⟩).summable using 2 with k
  rw [sinClass, smul_smul, mul_comm]

/-- The initial value `∑ₖ sin (k x) / k`, `k ≥ 1`, in `L²(0, π)`. -/
def sinSeries : Lp ℝ 2 (volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))) :=
  ∑' k : ℕ, ((k : ℝ) + 1)⁻¹ • sinClass k

/-- `sinSeries` is the sum of `∑ₖ sin (k x) / k` in `L²(0, π)`. -/
theorem hasSum_inv_smul_sinClass :
    HasSum (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • sinClass k) sinSeries :=
  summable_inv_smul_sinClass.hasSum

/-- On `(0, π)` the eigenvalues `((k + 1) π / (π - 0))²` of the sine basis are `(k + 1)²`. -/
private theorem sq_mul_pi_div_pi_sub_zero (k : ℕ) :
    (((k : ℝ) + 1) * π / (π - 0)) ^ 2 = ((k : ℝ) + 1) ^ 2 := by
  rw [sub_zero, mul_div_assoc, div_self Real.pi_ne_zero, mul_one]

/-- The coefficients of `∑ₖ sin (k x) / k` in the orthonormal sine basis are
`⟪eₖ, u₀⟫ = √(π / 2) / (k + 1)`. -/
private theorem inner_sineHilbertBasis_sinSeries (k : ℕ) :
    ⟪sineHilbertBasis Real.pi_pos k, sinSeries⟫_ℝ = √(π / 2) / ((k : ℝ) + 1) := by
  have h := hasSum_inv_smul_sinClass
  simp only [sinClass, smul_smul] at h
  rw [(sineHilbertBasis Real.pi_pos).orthonormal.inner_eq_of_hasSum h k]
  ring

/-- **`∑ₖ sin (k x) / k` is not in `H¹₀(0, π)`.** Its coefficients `√(π / 2) / k` in the
orthonormal sine basis against the eigenvalues `k²` give `∑ₖ k² (π / 2) / k² = ∞`. -/
theorem not_exists_value_eq_sinSeries :
    ¬∃ v : W1p0 volume (intervalDomain 0 π) 2,
      W1p.value (v : W1p volume (intervalDomain 0 π) 2) = sinSeries := by
  rw [exists_value_eq_iff_summable_intervalDomain Real.pi_pos]
  simp only [inner_sineHilbertBasis_sinSeries, sq_mul_pi_div_pi_sub_zero]
  simp only [div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ π / 2)]
  rw [summable_congr fun k : ℕ => mul_div_cancel₀ (π / 2) (by positivity : ((k : ℝ) + 1) ^ 2 ≠ 0)]
  exact fun h => (by positivity : π / 2 ≠ 0) ((summable_const_iff _).1 h)

variable {T : ℝ} {u : ℝ → W1p0 volume (intervalDomain 0 π) 2}
  {u' : ℝ → StrongDual ℝ (W1p0 volume (intervalDomain 0 π) 2)}
  {w : ℝ → Lp ℝ 2 (volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1))))}

/-- **The heat flow of `∑ₖ sin (k x) / k` on `(0, π)`.** Let `u` be a weak solution of
`∂ₜu - Δu = 0` in `(0, T) × (0, π)` with zero boundary values, integrable in time, whose
continuous `L²(0, π)`-valued representative `w` starts at `w 0 = ∑ₖ sin (k x) / k`. Then
`w t = ∑ₖ e^{-k² t} sin (k x) / k` in `L²(0, π)` for every `t ∈ [0, T]`. -/
theorem hasSum_exp_div_smul_sinClass
    (hd : HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain 0 π) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : IntegrableOn u (Ioo 0 T))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 volume (intervalDomain 0 π) 2,
      u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
        (v : W1p volume (intervalDomain 0 π) 2) = 0)
    (hw : ContinuousOn w (Icc 0 T))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w) (h₀ : w 0 = sinSeries)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasSum (fun k : ℕ => (Real.exp (-(((k : ℝ) + 1) ^ 2 * t)) / ((k : ℝ) + 1)) • sinClass k)
      (w t) := by
  convert (sineHilbertBasis Real.pi_pos).hasSum_repr (w t) using 2 with k
  rw [HilbertBasis.repr_apply_apply,
    inner_sineHilbertBasis_eq_exp_mul_of_hasWeakLineDerivOn_gelfandDual Real.pi_pos hd hu heq hw
      hae ht, h₀, inner_sineHilbertBasis_sinSeries, sq_mul_pi_div_pi_sub_zero, sub_zero, sinClass,
    smul_smul]
  ring_nf

/-- **The Dirichlet energy of the heat flow of `∑ₖ sin (k x) / k`.** For a weak solution `u` of
`∂ₜu - Δu = 0` in `(0, T) × (0, π)` with zero boundary values, integrable in time, whose continuous
`L²(0, π)`-valued representative starts at `∑ₖ sin (k x) / k`, for almost every `t ∈ (0, T)`

`∫_0^π |∂ₓu(t)|² = (π / 2) ∑ₖ e^{-2 k² t}`,

the sum running over `k ≥ 1`. -/
theorem ae_hasSum_energyFormH1_sinSeries
    (hd : HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain 0 π) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : IntegrableOn u (Ioo 0 T))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 volume (intervalDomain 0 π) 2,
      u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
        (v : W1p volume (intervalDomain 0 π) 2) = 0)
    (hw : ContinuousOn w (Icc 0 T))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w) (h₀ : w 0 = sinSeries) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      HasSum (fun k : ℕ => π / 2 * Real.exp (-(2 * ((k : ℝ) + 1) ^ 2 * t)))
        (energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
          (u t : W1p volume (intervalDomain 0 π) 2)) := by
  filter_upwards [ae_hasSum_energyFormH1_of_hasWeakLineDerivOn_gelfandDual Real.pi_pos hd hu heq hw
    hae] with t ht
  convert ht using 2 with k
  rw [h₀, inner_sineHilbertBasis_sinSeries, sq_mul_pi_div_pi_sub_zero, sub_zero, div_pow,
    Real.sq_sqrt (by positivity)]
  field_simp

/-- **The heat flow of `∑ₖ sin (k x) / k` is not continuous into `H¹₀(0, π)`.** For a weak
solution `u` of `∂ₜu - Δu = 0` in `(0, T) × (0, π)` with zero boundary values, integrable in time,
whose continuous `L²(0, π)`-valued representative starts at `∑ₖ sin (k x) / k`, the energy
`∫_0^π |∂ₓu(t)|² = (π / 2) ∑ₖ e^{-2 k² t}` tends to infinity as `t ↓ 0`, outside a null set of
times. So no representative of `u` is continuous into `H¹₀(0, π)` at `t = 0`, although the weak
solution of `exists_hasWeakLineDerivOn_gelfandDual_sinSeries` lies in `L²(0, T; H¹₀(0, π))`. -/
theorem tendsto_energyFormH1_atTop_sinSeries (hT : 0 < T)
    (hd : HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain 0 π) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : IntegrableOn u (Ioo 0 T))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 volume (intervalDomain 0 π) 2,
      u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
        (v : W1p volume (intervalDomain 0 π) 2) = 0)
    (hw : ContinuousOn w (Icc 0 T))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w) (h₀ : w 0 = sinSeries) :
    Tendsto (fun t => energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
      (u t : W1p volume (intervalDomain 0 π) 2)) (𝓝[>] 0 ⊓ ae volume) atTop := by
  have hae' := (ae_restrict_iff' measurableSet_Ioo).1
    (ae_hasSum_energyFormH1_sinSeries hd hu heq hw hae h₀)
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

/-- The zero forcing term lies in `L²(ℝ; H⁻¹(Ω))`. Stated for an arbitrary domain: on
`intervalDomain 0 π` itself, unifying the normed structures of the dual of `H¹₀(0, π)` times out. -/
private theorem memLp_zero_strongDual {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
    [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)} (ν : Measure ℝ) :
    MemLp (0 : ℝ → StrongDual ℝ (W1p0 mu Omega 2)) 2 ν :=
  MemLp.zero (ε := StrongDual ℝ (W1p0 mu Omega 2))

/-- **The heat flow of `∑ₖ sin (k x) / k` in the energy space.** For every `T > 0` there is a weak
solution `u ∈ L²(0, T; H¹₀(0, π))` of `∂ₜu - Δu = 0` in `(0, T) × (0, π)` with zero boundary values,
whose continuous `L²(0, π)`-valued representative `w` starts at `w 0 = ∑ₖ sin (k x) / k` and is
`w t = ∑ₖ e^{-k² t} sin (k x) / k` for `t ∈ [0, T]`, and whose Dirichlet energy tends to infinity
as `t ↓ 0`, outside a null set of times. -/
theorem exists_hasWeakLineDerivOn_gelfandDual_sinSeries (hT : 0 < T) :
    ∃ u : ℝ → W1p0 volume (intervalDomain 0 π) 2,
    ∃ u' : ℝ → StrongDual ℝ (W1p0 volume (intervalDomain 0 π) 2),
    ∃ w : ℝ → Lp ℝ 2 (volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))),
      MemLp u 2 (volume.restrict (Ioo 0 T)) ∧
      HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
        (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain 0 π) (p := 2)).gelfandDual
          (W1p0.valueL (u t))) u' 1 ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 volume (intervalDomain 0 π) 2,
        u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
          (v : W1p volume (intervalDomain 0 π) 2) = 0) ∧
      ContinuousOn w (Icc 0 T) ∧
      (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w ∧ w 0 = sinSeries ∧
      (∀ t ∈ Icc 0 T, HasSum
        (fun k : ℕ => (Real.exp (-(((k : ℝ) + 1) ^ 2 * t)) / ((k : ℝ) + 1)) • sinClass k)
        (w t)) ∧
      Tendsto (fun t => energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
        (u t : W1p volume (intervalDomain 0 π) 2)) (𝓝[>] 0 ⊓ ae volume) atTop := by
  have hell : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      UniformlyEllipticOn (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))
        ((fun _ _ => 1 : ℝ → EuclideanSpace ℝ (Fin 1) → Matrix (Fin 1) (Fin 1) ℝ) t) 1 1 :=
    ae_of_all _ fun _ => uniformlyEllipticOn_const_one_one _
  have hb : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      ∀ x ∈ (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1))),
        ‖(0 : ℝ → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) t x‖ ≤ 0 :=
    ae_of_all _ fun _ _ _ => by simp
  have hc : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      ∀ x ∈ (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1))),
        ‖(0 : ℝ → EuclideanSpace ℝ (Fin 1) → ℝ) t x‖ ≤ 0 :=
    ae_of_all _ fun _ _ _ => by simp
  -- `have` then `obtain`: destructuring the application directly times out in elaboration.
  have h := exists_hasWeakLineDerivOn_gelfandDual_energyFormH1 (mu := volume)
    (Omega := intervalDomain 0 π) hT aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const hell hb hc (memLp_zero_strongDual (ι := Fin 1) _) sinSeries
  obtain ⟨u, u', w, hu, -, hd, heq, hw, hae, h₀⟩ := h
  have heq' : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 volume (intervalDomain 0 π) 2,
      u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain 0 π) 2)
        (v : W1p volume (intervalDomain 0 π) 2) = 0 := by
    simpa only [Pi.zero_apply, zero_apply] using heq
  have hu₁ := hu.integrable one_le_two
  exact ⟨u, u', w, hu, hd, heq', hw, hae, h₀,
    fun t ht => hasSum_exp_div_smul_sinClass hd hu₁ heq' hw hae h₀ ht,
    tendsto_energyFormH1_atTop_sinSeries hT hd hu₁ heq' hw hae h₀⟩

end TauCeti.Examples.HeatSineSeries
