/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.MeyersExample

/-!
# Hopf's lemma fails for measurable divergence-form coefficients

Hopf's boundary-point lemma says that a supersolution of an elliptic equation which attains a
strict minimum at a boundary point admitting an interior ball leaves that minimum at a linear
rate: its inward difference quotients there are bounded below by a positive constant. For `C²`
subsolutions of operators in non-divergence form with bounded drift this holds with no regularity
of the principal coefficients
(`TauCeti.PDE.exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv`). For weak
solutions of divergence-form equations `div(a ∇u) = 0` the lemma needs some continuity of `a` at
the boundary point, such as the Hölder continuity assumed by Rosales. This file shows that
uniform ellipticity and measurability of `a` alone do not suffice, for every ellipticity ratio
`Λ > 1`.

For `s > 1` take Meyers' coefficient field `a = TauCeti.PDE.meyersCoefficient s`, which in polar
coordinates is `e_r ⊗ e_r + s² e_θ ⊗ e_θ`, and the function
`u = TauCeti.PDE.meyersSolution s`, `u(x) = ‖x‖ ^ (s - 1) x₀`, which is `r^s cos θ` with the
angle measured from `e₀`. Let `Ω` be a bounded open set in the half-plane `0 < x₀`, for instance
the half disc `{‖x‖ < 1, 0 < x₀}`, whose boundary point `0` has the interior disc of radius
`1 / 2` centred at `e₀ / 2`, with inward normal `e₀`. Then:

* `a` is uniformly elliptic with constants `1` and `s²`
  (`TauCeti.PDE.uniformlyEllipticOn_meyersCoefficient_of_one_le`);
* `u` lies in `H¹(Ω)` and is a weak solution of `div(a ∇u) = 0` on `Ω`
  (`TauCeti.PDE.energyFormH1_meyersCoefficient_eq_zero`);
* `u` is continuous, vanishes at `0` and is positive on `Ω`;
* but `u(t e₀) = t^s`, so the inward difference quotients `u(t e₀) / t` tend to `0`
  (`TauCeti.PDE.tendsto_meyersSolution_smul_single_zero_div`).

The coefficient is smooth away from the origin; what fails is its continuity at the boundary
point: it has no limit at `0` within the half-plane
(`TauCeti.PDE.not_exists_tendsto_meyersCoefficient`). Nor does the example contradict the
non-divergence lemma: on `Ω` the function `u` is smooth and `div(a ∇u) = aⁱʲ ∂ᵢ∂ⱼu + (div a) · ∇u`,
but the drift `div a = (1 - s²) x / ‖x‖²` is unbounded near the boundary point.

## Main declarations

* `TauCeti.PDE.not_exists_tendsto_meyersCoefficient`: for `μ² ≠ 1`, Meyers' coefficient has no
  limit at the origin within the half-plane `0 < x₀`.
* `TauCeti.PDE.tendsto_meyersSolution_smul_single_zero_div`: for `μ > 1`, the difference quotients
  of Meyers' solution at the origin in the direction `e₀` tend to `0`.
* `TauCeti.PDE.exists_uniformlyEllipticOn_energyFormH1_eq_zero_tendsto_div`: **Hopf's lemma fails
  for measurable coefficients**, for every ellipticity ratio `Λ > 1`.

## References

* E. Hopf, *A remark on linear elliptic differential equations of second order*, Proc. Amer.
  Math. Soc. 3 (1952), 791–793.
* L. Rosales, *Generalizing Hopf's boundary point lemma*, arXiv:1806.07003, Theorem 4.1.
* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa (3) 17 (1963), 189–206, §5 (the
  coefficient field).
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

namespace TauCeti

namespace PDE

variable {μ : ℝ}

/-- Along the ray through `(1, c)`, the entry `a₀₀` of Meyers' coefficient is the constant
`μ² + (1 - μ²) / (1 + c²)`. -/
private theorem meyersCoefficient_smul_apply_zero_zero (c : ℝ) {t : ℝ} (ht : t ≠ 0) :
    meyersCoefficient μ (t • WithLp.toLp 2 ![1, c]) 0 0 = μ ^ 2 + (1 - μ ^ 2) / (1 + c ^ 2) := by
  have hn : ‖t • WithLp.toLp 2 ![(1 : ℝ), c]‖ ^ 2 = t ^ 2 * (1 + c ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp only [PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
    ring
  rw [meyersCoefficient_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, hn]
  simp only [Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.vecMulVec_apply,
    PiLp.smul_apply, Matrix.cons_val_zero]
  have h1 : 1 + c ^ 2 ≠ 0 := by positivity
  field_simp

/-- **Meyers' coefficient is discontinuous at the origin.** For `μ² ≠ 1` it has no limit at the
origin within the half-plane `0 < x₀`: along the ray through `e₀` its entry `a₀₀` is `1`, and
along the ray through `e₀ + e₁` it is `(1 + μ²) / 2`. -/
theorem not_exists_tendsto_meyersCoefficient (hμ : μ ^ 2 ≠ 1) :
    ¬ ∃ L, Tendsto (meyersCoefficient μ) (𝓝[{x | 0 < x 0}] 0) (𝓝 L) := by
  rintro ⟨L, hL⟩
  have key : ∀ c : ℝ, L 0 0 = μ ^ 2 + (1 - μ ^ 2) / (1 + c ^ 2) := by
    intro c
    -- The ray `t ↦ t (1, c)`, `t > 0`, approaches the origin inside the half-plane.
    have hγ : Tendsto (fun t : ℝ => t • WithLp.toLp 2 ![(1 : ℝ), c]) (𝓝[>] 0)
        (𝓝[{x : EuclideanSpace ℝ (Fin 2) | 0 < x 0}] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using ((continuous_id.smul continuous_const).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ)))
          (f := fun t : ℝ => t • WithLp.toLp 2 ![(1 : ℝ), c])
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    have hent : Tendsto (fun t : ℝ => meyersCoefficient μ (t • WithLp.toLp 2 ![1, c]) 0 0)
        (𝓝[>] 0) (𝓝 (L 0 0)) :=
      ((continuous_id.matrix_elem 0 0).tendsto L).comp (hL.comp hγ)
    refine tendsto_nhds_unique hent (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (meyersCoefficient_smul_apply_zero_zero c (ne_of_gt ht)).symm
  have h := (key 0).symm.trans (key 1)
  norm_num at h
  exact hμ (by linarith)

/-- **Meyers' solution leaves the origin superlinearly.** For `μ > 1` the difference quotients
`u(t e₀) / t = t ^ (μ - 1)` of Meyers' solution at the origin in the direction `e₀` tend to `0`
as `t → 0⁺`. -/
theorem tendsto_meyersSolution_smul_single_zero_div (hμ : 1 < μ) :
    Tendsto (fun t : ℝ => meyersSolution μ (t • EuclideanSpace.single 0 1) / t) (𝓝[>] 0)
      (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => t ^ (μ - 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow (by linarith : μ - 1 ≠ 0)] using
      ((continuous_id.rpow_const fun _ => Or.inr (by linarith : 0 ≤ μ - 1)).tendsto
        (0 : ℝ)).mono_left nhdsWithin_le_nhds
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [meyersSolution_smul_single_zero ht, Real.rpow_sub_one (ne_of_gt ht)]

/-- **Hopf's lemma fails for measurable divergence-form coefficients.** Let `Λ > 1` and let
`Ω ⊆ ℝ²` be a bounded open set in the half-plane `0 < x₀`, for instance the half disc, whose
boundary point `0` has an interior disc with inward normal `e₀`. Then there is a strongly
measurable coefficient field `a`, uniformly elliptic on `Ω` with constants `1` and `Λ`, and a
weak solution `u ∈ H¹(Ω)` of `div(a ∇u) = 0` on `Ω` with a continuous representative `ū` that is
positive on `Ω` and vanishes at `0`, such that the inward difference quotients `ū(t e₀) / t`
tend to `0` as `t → 0⁺`. So the conclusion of Hopf's lemma, a positive lower bound for these
quotients, fails. The field is Meyers' coefficient with `s = √Λ`
(`TauCeti.PDE.meyersCoefficient`), which has no limit at `0` within the half-plane
(`TauCeti.PDE.not_exists_tendsto_meyersCoefficient`). -/
theorem exists_uniformlyEllipticOn_energyFormH1_eq_zero_tendsto_div {Λ : ℝ} (hΛ : 1 < Λ)
    {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2))))
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin 2))) ⊆ {x | 0 < x 0}) :
    ∃ a : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ, StronglyMeasurable a ∧
      UniformlyEllipticOn (Ω : Set (EuclideanSpace ℝ (Fin 2))) a 1 Λ ∧
      ∃ (u : W1p volume Ω 2) (ū : EuclideanSpace ℝ (Fin 2) → ℝ),
        W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))] ū ∧
        (∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) = 0) ∧
        Continuous ū ∧ ū 0 = 0 ∧ (∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin 2))), 0 < ū x) ∧
        Tendsto (fun t : ℝ => ū (t • EuclideanSpace.single 0 1) / t) (𝓝[>] 0) (𝓝 0) := by
  have hs : 1 < √Λ := by rwa [Real.lt_sqrt zero_le_one, one_pow]
  have hs0 : 0 < √Λ := zero_lt_one.trans hs
  obtain ⟨u, hu⟩ := exists_w1p_value_ae_eq_meyersSolution hs0 (p := 2) (by norm_num) hb
    (by simp only [ENNReal.toReal_ofNat]; linarith)
  refine ⟨meyersCoefficient √Λ, stronglyMeasurable_meyersCoefficient, ?_, u, meyersSolution √Λ,
    hu, energyFormH1_meyersCoefficient_eq_zero hs0 u hu, continuous_meyersSolution hs0,
    meyersSolution_zero, fun x hx => meyersSolution_pos (hΩ hx),
    tendsto_meyersSolution_smul_single_zero_div hs⟩
  simpa [Real.sq_sqrt (zero_le_one.trans hΛ.le)] using
    uniformlyEllipticOn_meyersCoefficient_of_one_le hs.le (Ω : Set (EuclideanSpace ℝ (Fin 2)))

end PDE

end TauCeti
