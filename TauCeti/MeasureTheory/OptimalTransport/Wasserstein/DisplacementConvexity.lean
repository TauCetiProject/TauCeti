/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Interpolation
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.InternalEnergy
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Geodesic
public import TauCeti.Analysis.GradientFlow.GeodesicConvex
import TauCeti.Analysis.Convex.FunctionTopology
import TauCeti.Analysis.Convex.McCannCondition
import TauCeti.Analysis.Matrix.MinkowskiDeterminant
import TauCeti.Data.ENNReal.Real
import TauCeti.MeasureTheory.OptimalTransport.Brenier
import TauCeti.MeasureTheory.OptimalTransport.Cost.Quadratic

/-!
# McCann's displacement convexity of internal energies

Let `E` be a real inner product space of finite dimension `n ≥ 1` with an additive Haar measure
`ρ`, and let `U : ℝ → ℝ` satisfy `U 0 = 0` and **McCann's condition**:

  `s ↦ sⁿ U(s⁻ⁿ)` is convex and nonincreasing on `(0, ∞)`.

For instance `U(r) = r log r`, `U(r) = rᵐ / (m - 1)` for `m > 1`, and, when `n ≥ 2`,
`U(r) = -r^{1 - 1/n}` satisfy it. **McCann's theorem** says that the internal energy
`𝓤(μ) = ∫ U(dμ/dρ) dρ + U'(∞) μˢ(E)` (`TauCeti.internalEnergy`) is convex along displacement
interpolations. Here, for a convex
`f : E → EReal` with real representative `F` and a σ-finite measure `μ ≪ ρ` carried by the interior
`D` of the effective domain of `f`, the interpolant at time `t ∈ [0, 1]` is `μₜ = (Tₜ)₊ μ` with
`Tₜ x = (1 - t) • x + t • ∇F x`, and

  `𝓤(μₜ) ≤ (1 - t) 𝓤(μ) + t 𝓤((∇F)₊ μ)`
  (`TauCeti.internalEnergy_map_smul_add_smul_gradient_le`),

provided neither endpoint energy `𝓤(μ)`, `𝓤((∇F)₊ μ)` is `⊥`.

When `∇F` is the Brenier map of `μ`, these interpolants form McCann's displacement interpolation,
the quadratic Wasserstein geodesic from `μ` to its target, so under the same restriction on the
endpoint energies the internal energy is convex along it
(`TauCeti.WassersteinSpace.exists_isGeodesicSegment_convexAlong_internalEnergy`). The target need
not be absolutely continuous: its singular part is charged at the recession constant `U'(∞)`, and
the theorem holds with that convention.

The proof moves the time dependence of `𝓤(μₜ)` into the Jacobian of `Tₜ`. Write `r` for the density
of `μ` and `H x` for the Alexandrov Hessian of `F`. For `t < 1` the interpolant is absolutely
continuous with `𝓤(μₜ) = ∫_D Jₜ U(r / Jₜ) dρ`, where `Jₜ x = det ((1 - t) • 1 + t • H x)`
(`TauCeti.internalEnergy_map_smul_add_smul_gradient`), by the change of variables of
`TauCeti.lintegral_comp_rnDeriv_map_smul_add_smul_gradient`. At `t = 1`, the gradient collapses the
degenerate set `{det (H x) = 0}` to a null set, which carries the singular part of `(∇F)₊ μ`
(`TauCeti.singularPart_map_gradient_apply_univ`), and `𝓤((∇F)₊ μ)` is the integral over `D` of
`J₁ U(r / J₁)`, or of `U'(∞) r` where `J₁ = 0` (`TauCeti.internalEnergy_map_gradient`).

Pointwise, `Jₜ U(r / Jₜ) = r φ(Jₜ^{1/n} r^{-1/n})` with `φ(s) = sⁿ U(s⁻ⁿ)`. By Minkowski's
determinant inequality `t ↦ Jₜ^{1/n}` is concave (`LinearMap.concaveOn_det_rpow`), and a convex
nonincreasing function of a concave function is convex. When `J₁ = 0`, the value `U'(∞) r` at
`t = 1` is the limit of `r φ(s)` as `s → 0⁺`; it suffices that it bounds `r φ` from above, which
holds because `U'(∞)` is the upper limit of `U(r) / r` as `r → ∞` and `U(r) / r = φ(r^{-1/n})`.

## Main statements

* `TauCeti.internalEnergy_map_smul_add_smul_gradient`: the internal energy of an interpolant at
  time `t < 1`, as an integral over the source.
* `TauCeti.internalEnergy_map_gradient`: the internal energy of the endpoint `(∇F)₊ μ`, as an
  integral over the source charging the degenerate set at the recession constant.
* `TauCeti.internalEnergy_map_smul_add_smul_gradient_le`: **McCann's displacement convexity** of
  the internal energy, when neither endpoint energy is `⊥`.
* `TauCeti.WassersteinSpace.exists_isGeodesicSegment_convexAlong_internalEnergy`: for laws of
  finite second moment, the first absolutely continuous, and neither of internal energy `⊥`, the
  internal energy is convex along a geodesic of the quadratic Wasserstein space joining them, the
  displacement interpolation of the Brenier map.

## References

* R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153–179,
  Theorem 2.2.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, American
  Mathematical Society, 2003, Theorem 5.15.
* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Proposition 9.3.9.
-/

public section

open MeasureTheory Measure Set Filter Module
open scoped ENNReal Topology Gradient

namespace TauCeti

section McCannCondition

variable {U : ℝ → ℝ} {n : ℕ}

/-- **McCann's pointwise inequality.** Let `U 0 = 0` and let `φ(s) = sⁿ U(s⁻ⁿ)` be convex and
nonincreasing on `(0, ∞)`, with `n ≠ 0`. If `a > 0` and `a₁ ≥ 0` satisfy the concavity bound
`(1 - t) + t a₁ ≤ a` for some `t ∈ [0, 1]`, then for every `r ≥ 0`,
`aⁿ U(r / aⁿ) ≤ (1 - t) U(r) + t a₁ⁿ U(r / a₁ⁿ)` when `a₁ > 0`, and
`aⁿ U(r / aⁿ) ≤ (1 - t) U(r) + t r L` when `a₁ = 0`, where `L` bounds `φ` above. -/
private theorem pow_mul_apply_div_pow_le (hn : n ≠ 0) (hU0 : U 0 = 0)
    (hc : ConvexOn ℝ (Ioi 0) fun s : ℝ => s ^ n * U (s ^ n)⁻¹)
    (ha : AntitoneOn (fun s : ℝ => s ^ n * U (s ^ n)⁻¹) (Ioi 0)) {r t a a₁ L : ℝ} (hr : 0 ≤ r)
    (ht : t ∈ Icc (0 : ℝ) 1) (hapos : 0 < a) (ha₁ : 0 ≤ a₁) (hle : 1 - t + t * a₁ ≤ a)
    (hL : a₁ = 0 → 0 < r → ∀ s ∈ Ioi (0 : ℝ), s ^ n * U (s ^ n)⁻¹ ≤ L) :
    a ^ n * U (r / a ^ n) ≤
      (1 - t) * U r + t * (if a₁ = 0 then r * L else a₁ ^ n * U (r / a₁ ^ n)) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [hU0]
  set φ : ℝ → ℝ := fun s => s ^ n * U (s ^ n)⁻¹
  set c := r⁻¹ ^ (n⁻¹ : ℝ)
  have hc0 : 0 < c := Real.rpow_pos_of_pos (inv_pos.2 hr) _
  have hU1 : U r = r * φ (c * 1) := by
    simpa using pow_mul_apply_div_pow_eq (U := U) hn hr one_pos
  rw [pow_mul_apply_div_pow_eq hn hr hapos, hU1, mul_one]
  split_ifs with ha₁0
  · -- The degenerate case: compare with `φ (c (1 - t))` and use the bound `L` at `0`.
    subst ha₁0
    have hφL := hL rfl hr
    rcases ht.2.eq_or_lt with rfl | ht₁
    · simpa using mul_le_mul_of_nonneg_left (hφL _ (mul_pos hc0 hapos)) hr.le
    have hb : 0 < 1 - t := sub_pos.2 ht₁
    have h₁ : φ (c * a) ≤ φ ((1 - t) * c) :=
      ha (mem_Ioi.2 (mul_pos hb hc0)) (mem_Ioi.2 (mul_pos hc0 hapos))
        (by nlinarith)
    have h₂ := hc.apply_mul_le_of_forall_le hφL hc0 hb (by linarith [ht.1])
    have := mul_le_mul_of_nonneg_left (h₁.trans h₂) hr.le
    linarith
  · have ha₁' : 0 < a₁ := lt_of_le_of_ne ha₁ (Ne.symm ha₁0)
    rw [pow_mul_apply_div_pow_eq hn hr ha₁']
    have hpos : 0 < 1 - t + t * a₁ := by
      rcases ht.2.eq_or_lt with rfl | ht₁
      · simpa using ha₁'
      · nlinarith [ht.1]
    have h₁ : φ (c * a) ≤ φ (c * (1 - t + t * a₁)) :=
      ha (mem_Ioi.2 (mul_pos hc0 hpos)) (mem_Ioi.2 (mul_pos hc0 hapos))
        (mul_le_mul_of_nonneg_left hle hc0.le)
    have h₂ : φ (c * (1 - t + t * a₁)) ≤ (1 - t) * φ c + t * φ (c * a₁) := by
      have := hc.2 (mem_Ioi.2 hc0) (mem_Ioi.2 (mul_pos hc0 ha₁')) (sub_nonneg.2 ht.2) ht.1
        (by ring)
      simp only [smul_eq_mul] at this
      convert this using 2
      ring
    have := mul_le_mul_of_nonneg_left (h₁.trans h₂) hr.le
    linarith

/-- **McCann's inequality at a positive operator.** Let `U 0 = 0` and let `φ(s) = sⁿ U(s⁻ⁿ)` be
convex and nonincreasing on `(0, ∞)`, where `n ≥ 1` is the dimension of `E`. For a positive operator
`A` on `E`, write `Jₛ = det ((1 - s) • 1 + s • A)`. For `0 < t < 1` and `r ≥ 0`,
`Jₜ U(r / Jₜ) ≤ (1 - t) U(r) + t J₁ U(r / J₁)` when `J₁ ≠ 0`, and
`Jₜ U(r / Jₜ) ≤ (1 - t) U(r) + t L r` when `J₁ = 0`, provided `L` then bounds `φ` above. The
concavity of `s ↦ Jₛ^{1/n}` is Minkowski's determinant inequality. -/
private theorem pointwise_mcCann {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] (hU0 : U 0 = 0)
    (hc : ConvexOn ℝ (Ioi 0) fun s : ℝ => s ^ finrank ℝ E * U (s ^ finrank ℝ E)⁻¹)
    (ha : AntitoneOn (fun s : ℝ => s ^ finrank ℝ E * U (s ^ finrank ℝ E)⁻¹) (Ioi 0))
    {A : E →L[ℝ] E} (hA : A.IsPositive) {r t L : ℝ} (hr : 0 ≤ r) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hL : A.det = 0 → 0 < r →
      ∀ s ∈ Ioi (0 : ℝ), s ^ finrank ℝ E * U (s ^ finrank ℝ E)⁻¹ ≤ L) :
    ((1 - t) • ContinuousLinearMap.id ℝ E + t • A).det *
        U (r / ((1 - t) • ContinuousLinearMap.id ℝ E + t • A).det) ≤
      (1 - t) * U r + t * (if A.det = 0 then L * r else A.det * U (r / A.det)) := by
  set n := finrank ℝ E
  have hn : n ≠ 0 := finrank_pos.ne'
  have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hn)
  have hA' := (ContinuousLinearMap.isPositive_toLinearMap_iff _).2 hA
  have hJ : 0 < ((1 - t) • ContinuousLinearMap.id ℝ E + t • A).det :=
    hA.det_one_sub_smul_id_add_smul_pos ht₀.le ht₁
  have hJ₁ : 0 ≤ A.det := hA'.det_nonneg
  -- Minkowski's determinant inequality: `s ↦ det ((1 - s) • 1 + s • A) ^ (1 / n)` is concave.
  have hle : 1 - t + t * A.det ^ (n⁻¹ : ℝ) ≤
      ((1 - t) • ContinuousLinearMap.id ℝ E + t • A).det ^ (n⁻¹ : ℝ) := by
    have := LinearMap.concaveOn_det_rpow.2 ((ContinuousLinearMap.isPositive_toLinearMap_iff _).2
      ContinuousLinearMap.isPositive_id) hA' (sub_nonneg.2 ht₁.le) ht₀.le (sub_add_cancel 1 t)
    simpa [ContinuousLinearMap.det, smul_eq_mul] using this
  have key := pow_mul_apply_div_pow_le hn hU0 hc ha (r := r) (L := L) hr ⟨ht₀.le, ht₁.le⟩
    (Real.rpow_pos_of_pos hJ _) (Real.rpow_nonneg hJ₁ _) hle
    fun ha₁ => hL ((Real.rpow_eq_zero hJ₁ hn').1 ha₁)
  rw [Real.rpow_inv_natCast_pow hJ.le hn, Real.rpow_inv_natCast_pow hJ₁ hn] at key
  simp only [Real.rpow_eq_zero hJ₁ hn'] at key
  refine key.trans_eq ?_
  split_ifs <;> ring

end McCannCondition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (ρ : Measure E) [ρ.IsAddHaarMeasure] {f : E → EReal}
  {U : ℝ → ℝ}

/-- **The internal energy along the interpolation of a convex gradient.** Let `f : E → EReal` be
convex (convex real epigraph, never `⊥`), with real representative `F` and `D` the interior of its
effective domain, and let `H x` be, for almost every `x ∈ D`, a first-order expansion of the
subdifferential of `f` at `x` (the Alexandrov Hessian). Let `μ` be an s-finite measure, absolutely
continuous with respect to an additive Haar measure `ρ` and carried by `D`, and let `U 0 = 0`. For
`0 ≤ t < 1`, the internal energy of the interpolant `μₜ = (Tₜ)₊ μ`,
`Tₜ x = (1 - t) • x + t • ∇F x`, is the potential energy against `ρ` of
`x ↦ Jₜ x * U(dμ/dρ (x) / Jₜ x)` on `D`, where `Jₜ x = det ((1 - t) • 1 + t • H x)`. -/
theorem internalEnergy_map_smul_add_smul_gradient (hU0 : U 0 = 0)
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {μ : Measure E} [SFinite μ] (hμ : μ ≪ ρ) (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    internalEnergy U ρ (μ.map fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x) =
      potentialEnergy ((interior {x | f x ≠ ⊤}).indicator fun x =>
        ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det *
          U ((μ.rnDeriv ρ x).toReal / ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det)) ρ := by
  set D := interior {x | f x ≠ ⊤}
  obtain ⟨S, -, -, hDS, hS, -⟩ :=
    exists_measurableSet_ae_eq_interior_subdifferential_eq_gradient ρ hf hbot hH
  -- The Jacobian is nonnegative almost everywhere on `D`.
  have hJ : ∀ᵐ x ∂ρ, x ∈ D → 0 ≤ ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det := by
    filter_upwards [hDS.mem_iff] with x hx hxD
    exact ((hS x (hx.1 hxD)).2.1.det_one_sub_smul_id_add_smul_pos ht₀ ht₁).le
  have hlint (ε : ℝ) :
      ∫⁻ y, ENNReal.ofReal (ε * U ((μ.map fun x => (1 - t) • x +
        t • (∇ fun x' => (f x').toReal) x).rnDeriv ρ y).toReal) ∂ρ =
      ∫⁻ x, ENNReal.ofReal (ε * D.indicator (fun x =>
        ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det *
          U ((μ.rnDeriv ρ x).toReal / ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det)) x)
        ∂ρ := by
    rw [lintegral_comp_rnDeriv_map_smul_add_smul_gradient ρ hf hbot hH hμ hμD ht₀ ht₁
      (Φ := fun a => ENNReal.ofReal (ε * U a.toReal)) (by simp [hU0]),
      ← lintegral_indicator measurableSet_interior]
    refine lintegral_congr_ae (hJ.mono fun x hx => ?_)
    dsimp only
    by_cases hxD : x ∈ D
    · rw [indicator_of_mem hxD, indicator_of_mem hxD,
        ENNReal.ofReal_mul_ofReal_apply_toReal_div (hx hxD) fun a => ε * U a, mul_left_comm]
    · rw [indicator_of_notMem hxD, indicator_of_notMem hxD, mul_zero, ENNReal.ofReal_zero]
  have hpos := hlint 1
  have hneg := hlint (-1)
  simp only [one_mul, neg_one_mul] at hpos hneg
  rw [internalEnergy_of_absolutelyContinuous
    (map_smul_add_smul_gradient_absolutelyContinuous ρ hf hbot hμ hμD ht₀ ht₁)]
  exact potentialEnergy_eq_of_lintegral_eq hpos hneg

/-- **The internal energy of the endpoint of the interpolation.** Under the hypotheses of
`internalEnergy_map_smul_add_smul_gradient`, with `μ` σ-finite, let `L` be the recession constant of
`U`, or any real number if `μ` gives no mass to the degenerate set `{x | det (H x) = 0}`. Then the
internal energy of `(∇F)₊ μ` is the potential energy against `ρ` of the function equal on `D` to
`det (H x) * U(dμ/dρ (x) / det (H x))` where `det (H x) ≠ 0`, and to `L * dμ/dρ (x)` where
`det (H x) = 0`. The degenerate set carries the singular part of `(∇F)₊ μ`
(`singularPart_map_gradient_apply_univ`), which the internal energy charges at the recession
constant. -/
theorem internalEnergy_map_gradient (hU0 : U 0 = 0) (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {μ : Measure E} [SigmaFinite μ] (hμ : μ ≪ ρ)
    (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤}) {L : ℝ}
    (hL : recessionConstant U = L ∨ μ {x | (H x).det = 0} = 0) :
    internalEnergy U ρ (μ.map (∇ fun x' => (f x').toReal)) =
      potentialEnergy ((interior {x | f x ≠ ⊤}).indicator fun x =>
        if (H x).det = 0 then L * (μ.rnDeriv ρ x).toReal
        else (H x).det * U ((μ.rnDeriv ρ x).toReal / (H x).det)) ρ := by
  set D := interior {x | f x ≠ ⊤}
  set G := ∇ fun x' => (f x').toReal
  obtain ⟨S, hSm, hSD, hDS, hS, H', hH'm, hHS⟩ :=
    exists_measurableSet_ae_eq_interior_subdifferential_eq_gradient ρ hf hbot hH
  set Z₀ := S ∩ {x | (H' x).det = 0}
  have hZ₀m : MeasurableSet Z₀ := hSm.inter (measurableSet_eq_fun
    (ContinuousLinearMap.continuous_det.measurable.comp hH'm) measurable_const)
  -- The degenerate set is `Z₀` up to a `μ`-null set, and it carries the singular part.
  have hμS : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [hμ.ae_le hDS.mem_iff, hμD] with x hx hxD
    exact hx.1 hxD
  have hZ₀ : μ {x | (H x).det = 0} = μ Z₀ :=
    measure_congr (eventuallyEqSet_iff.2 (hμS.mono fun x hx => by simp [Z₀, hx, hHS x hx]))
  have hσ := singularPart_map_gradient_apply_univ ρ hf hbot hH hμ hμD
  rw [hZ₀] at hσ hL
  -- The singular contribution `(± U'(∞)) μˢ(E)` is the integral of `(± L) dμ/dρ` over `Z₀`.
  have hsing (ε : ℝ) : (ε * recessionConstant U).toENNReal * (μ.map G).singularPart ρ univ =
      ∫⁻ x in Z₀, ENNReal.ofReal (ε * (L * (μ.rnDeriv ρ x).toReal)) ∂ρ := by
    rw [hσ]
    rcases hL with hL | hL
    · rw [hL, ← EReal.coe_mul, EReal.real_coe_toENNReal, ← setLIntegral_rnDeriv hμ Z₀,
        ← lintegral_const_mul _ (measurable_rnDeriv _ _)]
      refine setLIntegral_congr_fun_ae hZ₀m ((rnDeriv_ne_top μ ρ).mono fun x hx _ => ?_)
      rw [← mul_assoc, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]
    · rw [hL, mul_zero]
      have h0 := setLIntegral_rnDeriv hμ Z₀
      rw [hL, setLIntegral_eq_zero_iff hZ₀m (measurable_rnDeriv _ _)] at h0
      symm
      rw [setLIntegral_eq_zero_iff hZ₀m (by fun_prop)]
      filter_upwards [h0] with x hx hxZ
      simp [hx hxZ]
  -- The absolutely continuous part, by the change of variables along the gradient.
  have hac (ε : ℝ) : ∫⁻ y, ENNReal.ofReal (ε * U ((μ.map G).rnDeriv ρ y).toReal) ∂ρ =
      ∫⁻ x, ENNReal.ofReal (ε * D.indicator (fun x =>
        (H x).det * U ((μ.rnDeriv ρ x).toReal / (H x).det)) x) ∂ρ := by
    rw [lintegral_comp_rnDeriv_map_gradient ρ hf hbot hH hμ hμD
      (Φ := fun a => ENNReal.ofReal (ε * U a.toReal)) (by simp [hU0]),
      ← lintegral_indicator measurableSet_interior]
    refine lintegral_congr_ae (hDS.mem_iff.mono fun x hx => ?_)
    dsimp only
    by_cases hxD : x ∈ D
    · rw [indicator_of_mem hxD, indicator_of_mem hxD, ENNReal.ofReal_mul_ofReal_apply_toReal_div
        ((ContinuousLinearMap.isPositive_toLinearMap_iff _).2 (hS x (hx.1 hxD)).2.1).det_nonneg
        fun a => ε * U a, mul_left_comm]
    · rw [indicator_of_notMem hxD, indicator_of_notMem hxD, mul_zero, ENNReal.ofReal_zero]
  -- Both parts together give the claimed potential.
  have hsum (ε : ℝ) : ∫⁻ y, ENNReal.ofReal (ε * U ((μ.map G).rnDeriv ρ y).toReal) ∂ρ +
      (ε * recessionConstant U).toENNReal * (μ.map G).singularPart ρ univ =
      ∫⁻ x, ENNReal.ofReal (ε * D.indicator (fun x =>
        if (H x).det = 0 then L * (μ.rnDeriv ρ x).toReal
        else (H x).det * U ((μ.rnDeriv ρ x).toReal / (H x).det)) x) ∂ρ := by
    have hm : Measurable fun x => ENNReal.ofReal (ε * (L * (μ.rnDeriv ρ x).toReal)) := by
      fun_prop
    rw [hac, hsing, ← lintegral_indicator hZ₀m, ← lintegral_add_right _ (hm.indicator hZ₀m)]
    refine lintegral_congr_ae (hDS.mem_iff.mono fun x hx => ?_)
    dsimp only
    by_cases hxD : x ∈ D
    · have hxS := hx.1 hxD
      rw [indicator_of_mem hxD, indicator_of_mem hxD]
      by_cases h0 : (H x).det = 0
      · have hxZ : x ∈ Z₀ := ⟨hxS, by simpa [hHS x hxS] using h0⟩
        simp [h0, indicator_of_mem hxZ]
      · have hxZ : x ∉ Z₀ := fun hxZ => h0 (by simpa [hHS x hxS] using hxZ.2)
        simp [h0, indicator_of_notMem hxZ]
    · have hxZ : x ∉ Z₀ := fun hxZ => hxD (hSD hxZ.1)
      simp [indicator_of_notMem hxD, indicator_of_notMem hxZ]
  have hpos := hsum 1
  have hneg := hsum (-1)
  simp only [EReal.coe_one, EReal.coe_neg, one_mul, neg_one_mul] at hpos hneg
  rw [internalEnergy_def, hpos, hneg]
  by_cases h : ∫⁻ x, ENNReal.ofReal (D.indicator (fun x =>
      if (H x).det = 0 then L * (μ.rnDeriv ρ x).toReal
      else (H x).det * U ((μ.rnDeriv ρ x).toReal / (H x).det)) x) ∂ρ = ∞
  · simp only [h, ↓reduceIte, potentialEnergy_eq_top_iff.2 h]
  · simp only [h, ↓reduceIte, potentialEnergy_of_lintegral_ne_top h]

/-- **McCann's displacement convexity of internal energies.** Let `E` be a real inner product space
of finite dimension `n ≥ 1` with an additive Haar measure `ρ`, and let `U : ℝ → ℝ` satisfy
`U 0 = 0` and McCann's condition: `s ↦ sⁿ U(s⁻ⁿ)` is convex and nonincreasing on `(0, ∞)`. Let
`f : E → EReal` be convex (convex real epigraph, never `⊥`), with real representative `F`, and let
`μ` be a σ-finite measure, absolutely continuous with respect to `ρ` and carried by the interior of
the effective domain of `f`. Then the internal energy is convex along the interpolation
`μₜ = (Tₜ)₊ μ`, `Tₜ x = (1 - t) • x + t • ∇F x`:
`𝓤(μₜ) ≤ (1 - t) 𝓤(μ) + t 𝓤((∇F)₊ μ)` for `t ∈ [0, 1]`, provided neither endpoint has energy `⊥`.
The endpoint `(∇F)₊ μ` need not be absolutely continuous; its singular part is charged at the
recession constant `U'(∞)`. -/
theorem internalEnergy_map_smul_add_smul_gradient_le [Nontrivial E] (hU0 : U 0 = 0)
    (hc : ConvexOn ℝ (Ioi 0) fun s : ℝ => s ^ finrank ℝ E * U (s ^ finrank ℝ E)⁻¹)
    (ha : AntitoneOn (fun s : ℝ => s ^ finrank ℝ E * U (s ^ finrank ℝ E)⁻¹) (Ioi 0))
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {μ : Measure E}
    [SigmaFinite μ] (hμ : μ ≪ ρ) (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    (h₀ : internalEnergy U ρ μ ≠ ⊥)
    (h₁ : internalEnergy U ρ (μ.map (∇ fun x' => (f x').toReal)) ≠ ⊥) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    internalEnergy U ρ (μ.map fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x) ≤
      ((1 - t : ℝ) : EReal) * internalEnergy U ρ μ +
        (t : EReal) * internalEnergy U ρ (μ.map (∇ fun x' => (f x').toReal)) := by
  set D := interior {x | f x ≠ ⊤}
  set G := ∇ fun x' => (f x').toReal
  set n := finrank ℝ E
  have hn : n ≠ 0 := finrank_pos.ne'
  -- After the trivial endpoints `t = 0, 1` and the case where the endpoint has energy `⊤`, all
  -- three energies are potential energies against `ρ` of explicit functions on `D`
  -- (`internalEnergy_map_smul_add_smul_gradient`, `internalEnergy_map_gradient`), and the claim
  -- follows by integrating McCann's pointwise inequality (`pointwise_mcCann`).
  rcases ht.1.eq_or_lt with rfl | ht₀
  · simp [Measure.map_id']
  rcases ht.2.eq_or_lt with rfl | ht₁
  · simp
  obtain ⟨H, hH₀, -⟩ := exists_mongeAmpereMeasure_eq_singularPart_add_withDensity ρ hf hbot
  have hH : ∀ᵐ x ∂ρ, x ∈ D → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖ := by
    filter_upwards [hH₀] with x hx hxD
    exact ⟨_, (hx (interior_subset hxD)).2⟩
  -- If the recession constant is `⊤` and the degenerate set has positive mass, the endpoint has
  -- energy `⊤`.
  by_cases hA : recessionConstant U = ⊤ ∧ μ {x | (H x).det = 0} ≠ 0
  · have hσ : (μ.map G).singularPart ρ ≠ 0 := fun h => hA.2 (by
      rw [← singularPart_map_gradient_apply_univ ρ hf hbot hH hμ hμD, h, Measure.coe_zero,
        Pi.zero_apply])
    have h₀' : ((1 - t : ℝ) : EReal) * internalEnergy U ρ μ ≠ ⊥ :=
      (EReal.mul_ne_bot _ _).2 ⟨.inl (EReal.coe_ne_bot _), .inr h₀, .inl (EReal.coe_ne_top _),
        .inl (EReal.coe_nonneg.2 (sub_nonneg.2 ht₁.le))⟩
    rw [internalEnergy_eq_top_of_recessionConstant_eq_top hA.1 hσ, EReal.coe_mul_top_of_pos ht₀,
      EReal.add_top_of_ne_bot h₀']
    exact le_top
  -- Otherwise the endpoint is described by `internalEnergy_map_gradient` with a real `L`.
  set L := (recessionConstant U).toReal
  have hL : recessionConstant U = L ∨ μ {x | (H x).det = 0} = 0 := by
    by_cases htop : recessionConstant U = ⊤
    · exact .inr (not_not.1 fun h => hA ⟨htop, h⟩)
    · exact .inl (EReal.coe_toReal htop
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
          (pow_mul_apply_inv_pow_le_recessionConstant hn ha one_pos))).symm
  obtain ⟨S, hSm, hSD, hDS, hS, H', hH'm, hHS⟩ :=
    exists_measurableSet_ae_eq_interior_subdifferential_eq_gradient ρ hf hbot hH
  -- When the degenerate set is `μ`-null, the density vanishes almost everywhere on it.
  have hr0 : μ {x | (H x).det = 0} = 0 →
      ∀ᵐ x ∂ρ, x ∈ S → (H' x).det = 0 → μ.rnDeriv ρ x = 0 := by
    intro h0
    have hZ₀m : MeasurableSet (S ∩ {x | (H' x).det = 0}) := hSm.inter
      (measurableSet_eq_fun (ContinuousLinearMap.continuous_det.measurable.comp hH'm)
        measurable_const)
    have h := measure_mono_null (s := S ∩ {x | (H' x).det = 0})
      (fun x hx => by simpa [hHS x hx.1] using hx.2) h0
    rw [← setLIntegral_rnDeriv hμ, setLIntegral_eq_zero_iff hZ₀m (measurable_rnDeriv _ _)] at h
    filter_upwards [h] with x hx hxS hx0
    exact hx ⟨hxS, hx0⟩
  have hE₀ := internalEnergy_map_smul_add_smul_gradient ρ hU0 hf hbot hH hμ hμD le_rfl one_pos
  simp only [sub_zero, one_smul, zero_smul, add_zero, Measure.map_id', ContinuousLinearMap.det,
    ContinuousLinearMap.coe_id, LinearMap.det_id, div_one, one_mul] at hE₀
  rw [internalEnergy_map_smul_add_smul_gradient ρ hU0 hf hbot hH hμ hμD ht₀.le ht₁, hE₀,
    internalEnergy_map_gradient ρ hU0 hf hbot hH hμ hμD hL]
  rw [hE₀] at h₀
  rw [internalEnergy_map_gradient ρ hU0 hf hbot hH hμ hμD hL] at h₁
  have hUm := measurable_apply_max_of_convexOn hn hc
  have hr : Measurable fun x => (μ.rnDeriv ρ x).toReal := (measurable_rnDeriv _ _).ennreal_toReal
  have hdet : Measurable fun x => (H' x).det :=
    ContinuousLinearMap.continuous_det.measurable.comp hH'm
  have hV₀ : Measurable fun x => U (μ.rnDeriv ρ x).toReal := by
    convert hUm.comp hr using 2 with x
    simp
  have hV₁ : Measurable fun x => if (H' x).det = 0 then L * (μ.rnDeriv ρ x).toReal
      else (H' x).det * U (max ((μ.rnDeriv ρ x).toReal / (H' x).det) 0) :=
    Measurable.ite (measurableSet_eq_fun hdet measurable_const) (measurable_const.mul hr)
      (hdet.mul (hUm.comp (hr.div hdet)))
  have hr0' : ∀ᵐ x ∂ρ, x ∈ S → (H' x).det = 0 → recessionConstant U ≠ L →
      μ.rnDeriv ρ x = 0 := by
    rcases hL with h | h
    · exact ae_of_all _ fun x _ _ hne => (hne h).elim
    · filter_upwards [hr0 h] with x hx hxS hx0 _
      exact hx hxS hx0
  refine potentialEnergy_le_mul_add_mul (hV₀.indicator measurableSet_interior).aestronglyMeasurable
    ((hV₁.indicator hSm).aestronglyMeasurable.congr ?_) h₀ h₁ ⟨ht₀.le, ht₁.le⟩ ?_
  · -- Off a null set, `H` agrees with the measurable `H'`.
    filter_upwards [hDS.mem_iff] with x hx
    by_cases hxS : x ∈ S
    · have hdet0 : 0 ≤ (H' x).det := hHS x hxS ▸
        ((ContinuousLinearMap.isPositive_toLinearMap_iff _).2 (hS x hxS).2.1).det_nonneg
      simp [indicator_of_mem hxS, indicator_of_mem (hx.2 hxS), hHS x hxS,
        max_eq_left (div_nonneg ENNReal.toReal_nonneg hdet0)]
    · simp [indicator_of_notMem hxS, indicator_of_notMem (mt hx.1 hxS)]
  -- The pointwise inequality, from Minkowski's determinant inequality.
  filter_upwards [hDS.mem_iff, hr0'] with x hxS hr0x
  by_cases hxD : x ∈ D
  swap
  · rw [indicator_of_notMem hxD, indicator_of_notMem hxD, indicator_of_notMem hxD]
    simp
  have hxS' := hxS.1 hxD
  rw [indicator_of_mem hxD, indicator_of_mem hxD, indicator_of_mem hxD]
  refine pointwise_mcCann hU0 hc ha (hS x hxS').2.1 ENNReal.toReal_nonneg ht₀ ht₁
    fun h0 hr s hs => ?_
  -- The bound `φ ≤ L` is needed only where the density is positive and `det (H x) = 0`.
  by_cases hrec : recessionConstant U = L
  · exact EReal.coe_le_coe_iff.1 (hrec ▸ pow_mul_apply_inv_pow_le_recessionConstant hn ha hs)
  · rw [hHS x hxS'] at h0
    simp [hr0x hxS' h0 hrec] at hr

/-- **McCann's displacement convexity in the quadratic Wasserstein space.** Let `E` be a real
inner product space of finite dimension `n ≥ 1` with an additive Haar measure `ρ`, and let `U`
satisfy `U 0 = 0` and McCann's condition: `s ↦ sⁿ U(s⁻ⁿ)` is convex and nonincreasing on
`(0, ∞)`. For laws `μ, ν` of finite second moment with `μ ≪ ρ`, the internal energy is convex along
McCann's displacement interpolation, a geodesic of `P₂(E)` from `μ` to `ν`, provided neither
endpoint has energy `⊥`. -/
theorem WassersteinSpace.exists_isGeodesicSegment_convexAlong_internalEnergy [Nontrivial E]
    (hU0 : U 0 = 0)
    (hc : ConvexOn ℝ (Ioi 0) fun s : ℝ => s ^ finrank ℝ E * U (s ^ finrank ℝ E)⁻¹)
    (ha : AntitoneOn (fun s : ℝ => s ^ finrank ℝ E * U (s ^ finrank ℝ E)⁻¹) (Ioi 0))
    {μ ν : WassersteinSpace 2 E} (hμ : ((μ : ProbabilityMeasure E) : Measure E) ≪ ρ)
    (h₀ : internalEnergy U ρ ((μ : ProbabilityMeasure E) : Measure E) ≠ ⊥)
    (h₁ : internalEnergy U ρ ((ν : ProbabilityMeasure E) : Measure E) ≠ ⊥) :
    ∃ γ : ℝ → WassersteinSpace 2 E, IsGeodesicSegment γ μ ν ∧
      ConvexAlong 0 (fun ξ : WassersteinSpace 2 E =>
        internalEnergy U ρ ((ξ : ProbabilityMeasure E) : Measure E)) γ := by
  -- The Brenier map `∇u` from `μ` to `ν` induces an optimal plan for the squared distance.
  obtain ⟨u, hconv, -, hbot, hdiff, hT, hiff, -⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient hμ
      (transportCost_norm_sub_sq_div_two_ne_top μ ν)
  set G := ∇ fun x => (u x).toReal
  have hopt := (isOptimalCoupling_edist_rpow_iff measurable_edist two_ne_zero
    ENNReal.ofNat_ne_top).1 (isOptimalCoupling_edist_rpow_two_of_norm_sub_sq_div_two
      ((hiff (graphPlan G ((μ : ProbabilityMeasure E) : Measure E))).2 rfl))
  obtain ⟨γ, hγ, hγlaw⟩ := WassersteinSpace.exists_isGeodesicSegment_map_smul_add_smul hopt.1 hopt.2
  refine ⟨γ, hγ, hγ.convexAlong_iff.2 fun t ht => ?_⟩
  have hν : ((ν : ProbabilityMeasure E) : Measure E) =
      ((μ : ProbabilityMeasure E) : Measure E).map G :=
    hT.toHasLaw.map_eq.symm
  have hμD : ∀ᵐ x ∂((μ : ProbabilityMeasure E) : Measure E), x ∈ interior {x | u x ≠ ⊤} :=
    hdiff.mono fun x hx => mem_interior_iff_mem_nhds.2 hx.1
  have hG : Measurable fun x => (x, G x) := measurable_id'.prodMk (measurable_gradient _)
  rw [hγlaw t ht, graphPlan_def, Measure.map_map (by fun_prop) hG]
  simpa [hν, Function.comp_def] using internalEnergy_map_smul_add_smul_gradient_le ρ hU0 hc ha
    hconv hbot hμ hμD h₀ (hν ▸ h₁) ht

end TauCeti
