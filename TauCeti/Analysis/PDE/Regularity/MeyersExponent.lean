/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.MeyersExample

/-!
# The exponent in Meyers' theorem degenerates with the ellipticity ratio

Meyers' theorem (`TauCeti.PDE.exists_memLp_gradient_ball_divergence`) gives, for a bound `K` on
the ellipticity ratio, an exponent gain `ε₀ > 0` such that every weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` with measurable coefficients, uniformly elliptic with constants
`λ ≤ Λ ≤ K λ`, has gradient in `L^{2 + ε}` on half balls whenever `F` is, for `0 < ε ≤ ε₀`. This
file shows that in the plane every such gain satisfies

`ε (√K - 1) < 2`,

so the gain tends to `0` as the ellipticity ratio tends to infinity, and no higher integrability
exponent above `2` works for all measurable uniformly elliptic coefficients at once.

The witness is Meyers' example (`TauCeti.Analysis.PDE.Regularity.MeyersExample`). For `0 < μ ≤ 1`
the coefficient field `a = TauCeti.PDE.meyersCoefficient μ` on `ℝ^{n+2}` is uniformly elliptic
with constants `κ = μ (μ + n) / (n + 1)` and `1`, and `u(x) = ‖x‖ ^ (μ - 1) x₀` is a weak solution
of `div(a ∇u) = 0` lying in `H¹` of every bounded open set, whose gradient is `p`-integrable near
the origin only for `p (1 - μ) < n + 2`
(`TauCeti.PDE.toReal_mul_one_sub_lt_of_memLp_gradient_meyersSolution`). Take for `μ` the positive
root of `μ (μ + n) = (n + 1) λ / Λ` and the field `Λ a`, whose constants are `Λ κ = λ` and `Λ`.
This shows that an exponent `p` for which every weak solution has `p`-integrable gradient near the
origin satisfies `p (1 - μ) < n + 2`. In the plane, `n = 0`, the root is `μ = √(λ / Λ)`, and the
bound `p (1 - √(λ / Λ)) < 2` tends to `p ≤ 2` as `Λ / λ` tends to infinity. In higher dimensions the
point singularity of Meyers' example only bounds `p` by a quantity tending to the dimension.

## Main declarations

* `TauCeti.PDE.toReal_mul_one_sub_lt_of_forall_memLp_gradient`: if, on a bounded open set
  `Ω ⊆ ℝ^{n+2}` containing the origin, every weak solution with measurable coefficients, uniformly
  elliptic with constants `λ, Λ`, has gradient `p`-integrable on a fixed neighbourhood of the
  origin, then `p (1 - μ) < n + 2` whenever `μ > 0` and `μ (μ + n) / (n + 1) = λ / Λ`.
* `TauCeti.PDE.toReal_mul_one_sub_sqrt_lt_two_of_forall_memLp_gradient`: in the plane the bound
  reads `p (1 - √(λ / Λ)) < 2`.
* `TauCeti.PDE.mul_sqrt_sub_one_lt_two_of_forall_memLp_gradient_ball`: in the plane, every gain `ε`
  with the property stated by Meyers' theorem for the ratio bound `K` satisfies `ε (√K - 1) < 2`.
* `TauCeti.PDE.tendsto_atTop_nhds_zero_of_forall_memLp_gradient_ball`: in the plane, any choice of
  such gains `ε(K) ≥ 0` tends to `0` as `K` tends to infinity.

## References

* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa (3) 17 (1963), 189–206, Theorem 2 and §5
  (the coefficient field and the solution in the plane).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped NNReal ENNReal Topology InnerProductSpace Gradient

namespace TauCeti

namespace PDE

/-- **The integrability exponent of the gradient of weak solutions is bounded through Meyers'
example.** Let `0 < λ`, let `Ω ⊆ ℝ^{n+2}` be a bounded open set containing the origin and let
`s` be a neighbourhood of the origin. Suppose that for every measurable coefficient field `a`,
uniformly elliptic on `Ω` with constants `λ, Λ`, every weak solution `u ∈ H¹(Ω)` of
`-∂ᵢ(aⁱʲ ∂ⱼu) = 0` on `Ω` has `p`-integrable gradient on `s`. Then `p (1 - μ) < n + 2` for the
positive root `μ` of `μ (μ + n) / (n + 1) = λ / Λ`. If `λ > Λ` no coefficient field qualifies;
then every such `μ` is at least `1`, and the bound holds trivially.

The witness is Meyers' solution for the field `Λ a` with `a = TauCeti.PDE.meyersCoefficient μ`. Its
gradient is `p`-integrable on bounded sets for every `p` with `p (1 - μ) < n + 2`
(`TauCeti.PDE.exists_w1p_value_ae_eq_meyersSolution`), so this example yields no smaller bound. -/
theorem toReal_mul_one_sub_lt_of_forall_memLp_gradient {n : ℕ} {lam Lam : ℝ} (hlam : 0 < lam)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))))
    (h0 : (0 : EuclideanSpace ℝ (Fin (n + 2))) ∈ Ω) {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (hs : s ∈ 𝓝 0) {p : ℝ≥0∞}
    (h : ∀ (a : EuclideanSpace ℝ (Fin (n + 2)) → Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
      (u : W1p volume Ω 2),
      UniformlyEllipticOn (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))) a lam Lam →
      AEStronglyMeasurable a (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))) →
      (∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) = 0) →
      MemLp (W1p.gradient u) p (volume.restrict s))
    {μ : ℝ} (hμ0 : 0 < μ) (hμ : meyersEigenvalue n μ = lam / Lam) :
    p.toReal * (1 - μ) < n + 2 := by
  rcases le_or_gt 1 μ with hμ1 | hμ1
  · nlinarith [ENNReal.toReal_nonneg (a := p)]
  -- For `μ < 1` the ratio `λ / Λ = μ (μ + n) / (n + 1)` lies in `(0, 1)`, so `λ < Λ`.
  have hκ0 : 0 < lam / Lam := hμ ▸ meyersEigenvalue_pos hμ0
  have hκ1 : lam / Lam ≤ 1 := hμ ▸ meyersEigenvalue_le_one hμ0.le hμ1.le
  have hLam : lam ≤ Lam := by
    have hLam0 : 0 < Lam := (div_pos_iff_of_pos_left hlam).1 hκ0
    rwa [div_le_one hLam0] at hκ1
  -- Meyers' solution for the field `Λ a`, uniformly elliptic with constants `Λ κ = λ` and `Λ`.
  obtain ⟨u, hu⟩ := exists_w1p_value_ae_eq_meyersSolution hμ0 (p := 2) (by norm_num) hb
    (by simp only [ENNReal.toReal_ofNat]; nlinarith)
  have hmem := h _ u (uniformlyEllipticOn_smul_meyersCoefficient hμ0 hlam hLam hμ _)
    (stronglyMeasurable_meyersCoefficient.const_smul Lam).aestronglyMeasurable
    (energyFormH1_smul_meyersCoefficient_eq_zero hμ0 Lam u hu)
  -- On `s ∩ Ω` the weak gradient is the classical gradient of Meyers' solution.
  have hg : W1p.gradient u =ᵐ[volume.restrict (s ∩ Ω)] ∇ (meyersSolution μ) :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right
      (gradient_ae_eq_gradient_meyersSolution hμ0 u hu)
  exact toReal_mul_one_sub_lt_of_memLp_gradient_meyersSolution hμ0
    (inter_mem hs (Ω.isOpen.mem_nhds h0))
    ((hmem.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)).ae_eq hg)

/-- **The integrability exponent of the gradient of weak solutions in the plane.** Let
`0 < λ` and `0 < Λ`, let `Ω ⊆ ℝ²` be a bounded open set containing the origin and let `s` be a
neighbourhood of the origin. Suppose that for every measurable coefficient field `a`, uniformly
elliptic on `Ω` with constants `λ, Λ`, every weak solution `u ∈ H¹(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` on
`Ω` has `p`-integrable gradient on `s`. Then `p (1 - √(λ / Λ)) < 2`, that is
`p < 2 / (1 - √(λ / Λ))` when `λ < Λ`; this bound tends to `2` as `Λ / λ` tends to infinity. If
`λ > Λ` no coefficient field qualifies, and the bound holds trivially. -/
theorem toReal_mul_one_sub_sqrt_lt_two_of_forall_memLp_gradient {lam Lam : ℝ} (hlam : 0 < lam)
    (hLam : 0 < Lam) {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2))))
    (h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ Ω) {s : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : s ∈ 𝓝 0) {p : ℝ≥0∞}
    (h : ∀ (a : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ) (u : W1p volume Ω 2),
      UniformlyEllipticOn (Ω : Set (EuclideanSpace ℝ (Fin 2))) a lam Lam →
      AEStronglyMeasurable a (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 2)))) →
      (∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) = 0) →
      MemLp (W1p.gradient u) p (volume.restrict s)) :
    p.toReal * (1 - √(lam / Lam)) < 2 := by
  have hκ : 0 < lam / Lam := div_pos hlam hLam
  have := toReal_mul_one_sub_lt_of_forall_memLp_gradient (n := 0) hlam hb h0 hs h
    (Real.sqrt_pos.2 hκ) (by rw [meyersEigenvalue_zero, Real.sq_sqrt hκ.le])
  simpa only [Nat.cast_zero, zero_add] using this

/-- **The gain in Meyers' theorem degenerates with the ellipticity ratio.** In the plane, let
`ε ≥ 0` have the property stated by Meyers' theorem
(`TauCeti.PDE.exists_memLp_gradient_ball_divergence`) for the bound `K` on the ellipticity ratio:
for every open `Ω ⊆ ℝ²`, every measurable `a`, uniformly elliptic on `Ω` with constants
`λ ≤ Λ ≤ K λ`, every `F ∈ L²(Ω; ℝ²)` and every weak solution `u ∈ H¹(Ω)` of
`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ`, if `B(x₀, R) ⊆ Ω` and `F ∈ L^{2 + ε}(B(x₀, R))` then
`∇u ∈ L^{2 + ε}(B(x₀, R/2))`. Then `ε (√K - 1) < 2`, that is `ε < 2 / (√K - 1)` for `K > 1`. -/
theorem mul_sqrt_sub_one_lt_two_of_forall_memLp_gradient_ball {K ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ {Omega : Opens (EuclideanSpace ℝ (Fin 2))}
      {a : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
      {lam Lam : ℝ} {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
      {u : W1p volume Omega 2} {x₀ : EuclideanSpace ℝ (Fin 2)} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin 2))) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 2)))) →
      MemLp F 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 2)))) →
      (∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p volume Omega 2) x⟫_ℝ) →
      ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ (Fin 2))) →
      MemLp F (ENNReal.ofReal (2 + ε)) (volume.restrict (ball x₀ R)) →
      MemLp (W1p.gradient u) (ENNReal.ofReal (2 + ε)) (volume.restrict (ball x₀ (R / 2)))) :
    ε * (√K - 1) < 2 := by
  rcases le_or_gt K 1 with hK | hK
  · nlinarith [Real.sqrt_le_one.2 hK]
  -- Apply the local form with `λ = 1`, `Λ = K`, on `Ω = B(0, 2)` with `s = B(0, 1)` and `F = 0`.
  let Ω : Opens (EuclideanSpace ℝ (Fin 2)) := ⟨ball 0 2, isOpen_ball⟩
  have := toReal_mul_one_sub_sqrt_lt_two_of_forall_memLp_gradient one_pos (one_pos.trans hK)
    (Ω := Ω) isBounded_ball (mem_ball_self two_pos) (ball_mem_nhds 0 one_pos)
    (p := ENNReal.ofReal (2 + ε)) fun a u ha ham hu => by
      have := h (F := 0) (u := u) (x₀ := 0) (R := 2) ha (by rw [mul_one]) ham MemLp.zero
        (fun v => by simp [hu v]) subset_rfl MemLp.zero
      rwa [div_self two_ne_zero] at this
  rw [ENNReal.toReal_ofReal (by linarith), one_div, Real.sqrt_inv] at this
  -- Multiply `(2 + ε) (1 - 1/√K) < 2` by `√K > 0`.
  have ht : 0 < √K := Real.sqrt_pos.2 (one_pos.trans hK)
  have h1 : (2 + ε) * (1 - (√K)⁻¹) * √K = (2 + ε) * (√K - 1) := by
    field_simp
  nlinarith [mul_lt_mul_of_pos_right this ht]

/-- **The gain in Meyers' theorem tends to zero as the ellipticity ratio tends to infinity.** In
the plane, let `ε(K) ≥ 0` have, for every `K`, the property stated by Meyers' theorem
(`TauCeti.PDE.exists_memLp_gradient_ball_divergence`) for the bound `K` on the ellipticity ratio,
as in `TauCeti.PDE.mul_sqrt_sub_one_lt_two_of_forall_memLp_gradient_ball`. Then `ε(K) → 0` as
`K → ∞`. -/
theorem tendsto_atTop_nhds_zero_of_forall_memLp_gradient_ball {ε : ℝ → ℝ} (hε : ∀ K, 0 ≤ ε K)
    (h : ∀ K, ∀ {Omega : Opens (EuclideanSpace ℝ (Fin 2))}
      {a : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
      {lam Lam : ℝ} {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
      {u : W1p volume Omega 2} {x₀ : EuclideanSpace ℝ (Fin 2)} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin 2))) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 2)))) →
      MemLp F 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 2)))) →
      (∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p volume Omega 2) x⟫_ℝ) →
      ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ (Fin 2))) →
      MemLp F (ENNReal.ofReal (2 + ε K)) (volume.restrict (ball x₀ R)) →
      MemLp (W1p.gradient u) (ENNReal.ofReal (2 + ε K)) (volume.restrict (ball x₀ (R / 2)))) :
    Tendsto ε atTop (𝓝 0) := by
  -- `0 ≤ ε(K) < 2 / (√K - 1)` for `K > 1`, and the bound tends to `0`.
  have hbound : Tendsto (fun K : ℝ => 2 * (√K - 1)⁻¹) atTop (𝓝 0) := by
    have := ((tendsto_atTop_add_const_right _ (-1) Real.tendsto_sqrt_atTop).inv_tendsto_atTop
      ).const_mul 2
    simpa only [mul_zero, Pi.inv_apply, ← sub_eq_add_neg] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall hε) ?_
  filter_upwards [eventually_gt_atTop 1] with K hK
  have ht : 0 < √K - 1 := sub_pos.2 (Real.lt_sqrt zero_le_one |>.2 (by simpa using hK))
  rw [← div_eq_mul_inv, le_div_iff₀ ht]
  exact (mul_sqrt_sub_one_lt_two_of_forall_memLp_gradient_ball (hε K) (h K)).le

end PDE

end TauCeti
