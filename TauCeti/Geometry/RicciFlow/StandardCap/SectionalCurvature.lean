/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RicciFlow.StandardCap.Metric
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Sectional curvature of the standard cap

Every standard cap profile `f` gives a punctured cap `dr² + f(r)² g_(Sⁿ)` whose mixed
radial-spherical tangent planes have sectional curvature `-f''(r) / f(r)` and whose vertical
spherical tangent planes have sectional curvature `(1 - f'(r)²) / f(r)²`. Concavity controls the
radial Hessian, and the slope bound `0 ≤ f' ≤ 1` controls the vertical curvature correction to the
round sphere, so every tangent plane (including tilted planes) has nonnegative sectional curvature,
and near the missing tip the profile is `2 sin (r / 2)` and every tangent plane has sectional
curvature `1 / 4`, that of the round sphere of radius `2`.

Pulling back along the polar local Riemannian isometry
`isLocalRiemannianIsometry_toWithMetric_polar` transfers sectional curvature from the punctured cap
to `WithMetric (hf.metric V)` away from `0 ∈ V`, and continuity of sectional curvature along smooth
frames extends both constant sectional curvature `1 / 4` near the tip and global nonnegativity
across `0 ∈ V`.

## Main results

* `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_horizontal_vertical`,
  `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_vertical`: sectional curvature
  of mixed and vertical two-planes on the punctured cap.
* `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_nonneg`,
  `TauCeti.IsStandardCapProfile.exists_hasSectionalCurvatureAt_puncturedMetric_round`: nonnegativity
  and round-tip sectional curvature `1 / 4` on the punctured cap.
* `TauCeti.IsStandardCapProfile.exists_hasSectionalCurvatureAt_withMetric_round`: constant sectional
  curvature `1 / 4` near and at the tip `0` of `WithMetric (hf.metric V)`.
* `TauCeti.IsStandardCapProfile.sectionalCurvature_withMetric_nonneg`: nonnegativity of sectional
  curvature on every tangent two-plane of `WithMetric (hf.metric V)`, including at the tip `0`.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture* (2007), Definition 12.1.
* B. O'Neill, *Semi-Riemannian Geometry* (1983), Chapter 7, Proposition 42.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Metric Module Real Set
open TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.IsStandardCapProfile

section Punctured

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (Module.finrank ℝ V = n + 1)]
include hf

/-- Mixed radial-spherical tangent planes of the punctured standard cap have sectional
curvature `-f''(r) / f(r)`. Both spanning vectors must be nonzero. -/
theorem sectionalCurvature_puncturedMetric_horizontal_vertical
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1)
    (u : TangentSpace 𝓘(ℝ) p.1) (v : TangentSpace (𝓡 n) p.2) (hu : u ≠ 0) (hv : v ≠ 0) :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
        (standardCapRadialDomain × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p
      ((tangentSpaceProdEquiv p).symm (u, 0))
      ((tangentSpaceProdEquiv p).symm (0, v)) =
      -deriv (deriv f) p.1 / f p.1 := by
  rw [hf.puncturedMetric_def]
  exact sectionalCurvature_warpedProdTangentSpace_real_sphere_horizontal_vertical
    standardCapRadialDomain (hf.contDiff.contMDiff.comp contMDiff_subtypeVal)
    (fun r ↦ (hf.apply_pos r.property).ne') p u v hu hv

/-- Vertical spherical tangent planes of the punctured standard cap have sectional
curvature `(1 - f'(r)²) / f(r)²`. -/
theorem sectionalCurvature_puncturedMetric_vertical
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1)
    (v w : TangentSpace (𝓡 n) p.2) (hvw : LinearIndependent ℝ ![v, w]) :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
        (standardCapRadialDomain × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p
      ((tangentSpaceProdEquiv p).symm (0, v))
      ((tangentSpaceProdEquiv p).symm (0, w)) =
      (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 := by
  rw [hf.puncturedMetric_def]
  exact sectionalCurvature_warpedProdTangentSpace_real_sphere_vertical standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtypeVal)
    (fun r ↦ (hf.apply_pos r.property).ne') p v w hvw

/-- The punctured standard cap has nonnegative sectional curvature on every tangent
plane, in any sphere dimension. The assertion includes dependent spanning vectors. -/
theorem sectionalCurvature_puncturedMetric_nonneg
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1)
    (u v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    letI : RiemannianBundle (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    0 ≤ (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
      (standardCapRadialDomain × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p u v := by
  rw [hf.puncturedMetric_def]
  apply sectionalCurvature_warpedProdTangentSpace_real_sphere_nonneg (n := n)
    standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtypeVal)
    (fun r ↦ (hf.apply_pos r.property).ne') p
  · exact mul_nonpos_of_nonneg_of_nonpos (hf.apply_nonneg p.1.property.le)
      (hf.deriv_deriv_nonpos p.1.property.le)
  · have h₀ := hf.deriv_nonneg p.1.property.le
    have h₁ := hf.deriv_le_one p.1.property.le
    nlinarith

/-- Near its missing tip, the punctured standard cap has sectional curvature `1/4` on every
tangent plane, in any sphere dimension: there the profile is `2 sin (r / 2)`, and the metric is
that of the round sphere of radius `2`. -/
theorem exists_hasSectionalCurvatureAt_puncturedMetric_round :
    ∃ r₀ > 0, ∀ p : standardCapRadialDomain × Metric.sphere (0 : V) 1, (p.1 : ℝ) < r₀ →
      letI : RiemannianBundle (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
        ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
      (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
        (standardCapRadialDomain × Metric.sphere (0 : V) 1)).HasSectionalCurvatureAt
        (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p (1 / 4) := by
  obtain ⟨r₀, hr₀, h⟩ :=
    hf.exists_eq_two_mul_sin_and_deriv_eq_cos_and_deriv_deriv_eq_neg_sin_div_two
  refine ⟨r₀, hr₀, fun p hp ↦ ?_⟩
  obtain ⟨h₀, h₁, h₂⟩ := h p.1 ⟨p.1.property.le, hp⟩
  rw [hf.puncturedMetric_def]
  apply hasSectionalCurvatureAt_warpedProdTangentSpace_real_sphere (n := n)
    standardCapRadialDomain
  · rw [h₀, h₂]
    ring
  · rw [h₀, h₁]
    linear_combination Real.sin_sq_add_cos_sq ((p.1 : ℝ) / 2)

end Punctured

/-! ### Global sectional curvature across the tip -/

section Global

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
include hf

private theorem sectionalCurvature_withMetric_of_ne_zero {n : ℕ} [Fact (finrank ℝ V = n + 1)]
    {p : WithMetric (hf.metric V)} (hp : p.ofWithMetric ≠ 0) (X Y : TangentSpace 𝓘(ℝ, V) p) :
    letI : RiemannianBundle _ := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    ∃ (q : standardCapRadialDomain × sphere (0 : V) 1) (u v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) q),
      (q.1 : ℝ) = ‖p.ofWithMetric‖ ∧
      (LinearIndependent ℝ ![u, v] ↔ LinearIndependent ℝ ![X, Y]) ∧
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p X Y =
        (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
          (standardCapRadialDomain × sphere (0 : V) 1)).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) q u v := by
  let _ : RiemannianBundle _ := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  have hloc := hf.isLocalRiemannianIsometry_toWithMetric_polar (n := n) V
  set ψ : standardCapRadialDomain × sphere (0 : V) 1 → WithMetric (hf.metric V) :=
    fun z ↦ WithMetric.toWithMetric (hf.metric V) ((z.1 : ℝ) • (z.2 : V))
  obtain ⟨q, hq_norm, hψq⟩ : ∃ q : standardCapRadialDomain × sphere (0 : V) 1,
      (q.1 : ℝ) = ‖p.ofWithMetric‖ ∧ ψ q = p := by
    refine ⟨(radialSphereDiffeomorph (n := n) V).symm ⟨p.ofWithMetric, mem_puncturedSpace.2 hp⟩,
      by simp, ?_⟩
    have hcoe := congrArg Subtype.val ((radialSphereDiffeomorph (n := n) V).apply_symm_apply
      ⟨p.ofWithMetric, mem_puncturedSpace.2 hp⟩)
    rw [coe_radialSphereDiffeomorph_apply] at hcoe
    exact WithMetric.ext hcoe
  subst hψq
  obtain ⟨e, he⟩ := hloc.exists_linearIsometryEquiv_eq_mfderiv q
  obtain ⟨u, hu⟩ := (hloc.mfderiv_surjective q) X
  obtain ⟨v, hv⟩ := (hloc.mfderiv_surjective q) Y
  refine ⟨q, u, v, hq_norm, ?_, ?_⟩
  · have hcomp : ⇑e.toLinearEquiv.toLinearMap ∘ ![u, v] = ![X, Y] := by
      ext i; fin_cases i <;> simp [he, hu, hv]
    have hli := e.toLinearEquiv.toLinearMap.linearIndependent_iff (LinearEquiv.ker e.toLinearEquiv)
      (v := ![u, v])
    rw [hcomp] at hli
    exact hli.symm
  · have hsec := hloc.sectionalCurvature_mfderiv q u v
    rwa [hu, hv] at hsec

private theorem sectionalCurvature_withMetric_tip_limit
    {p₀ : WithMetric (hf.metric V)} (hp₀ : p₀.ofWithMetric = 0)
    {X Y : TangentSpace 𝓘(ℝ, V) p₀} (hXY : LinearIndependent ℝ ![X, Y])
    {s : Set (WithMetric (hf.metric V))} (hs : s ∈ 𝓝 p₀) {k : ℝ}
    (hk : ∀ q ∈ s, q.ofWithMetric ≠ 0 → ∀ u v : TangentSpace 𝓘(ℝ, V) q,
      LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) q u v = k) :
    (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p₀ X Y = k := by
  have hcard : 2 ≤ finrank ℝ V := by
    have h := hXY.fintype_card_le_finrank
    rwa [Fintype.card_fin, (tangentSpaceCastModel 𝓘(ℝ, V) p₀).toLinearEquiv.finrank_eq] at h
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (M := V) (by omega)
  have : Nontrivial (WithMetric (hf.metric V)) :=
    (WithMetric.equiv (hf.metric V)).surjective.nontrivial
  obtain ⟨u, hu, hu₀⟩ := FiberBundle.exists_contMDiff_section_eq 𝓘(ℝ, V) V ∞ X
  obtain ⟨v, hv, hv₀⟩ := FiberBundle.exists_contMDiff_section_eq 𝓘(ℝ, V) V ∞ Y
  have hcont :=
    ((leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).contMDiffAt_sectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) (n := (⊤ : ℕ∞)) (hu p₀) (hv p₀)
      (by rwa [hu₀, hv₀])).continuousAt
  have hdet_cont : Continuous fun q ↦
      inner ℝ (u q) (u q) * inner ℝ (v q) (v q) - inner ℝ (u q) (v q) ^ 2 :=
    ((hu.continuous.inner_bundle hu.continuous).mul (hv.continuous.inner_bundle hv.continuous)).sub
      ((hu.continuous.inner_bundle hv.continuous).pow 2)
  have hdet₀ : inner ℝ (u p₀) (u p₀) * inner ℝ (v p₀) (v p₀) - inner ℝ (u p₀) (v p₀) ^ 2 ≠ 0 := by
    rw [hu₀, hv₀, ← Matrix.real_det_gram_fin_two]
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hXY
  have hev : ∀ᶠ q in 𝓝[≠] p₀,
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) q (u q) (v q) = k := by
    filter_upwards [nhdsWithin_le_nhds (inter_mem hs (hdet_cont.continuousAt.eventually_ne hdet₀)),
      self_mem_nhdsWithin] with q ⟨hqs, hqdet⟩ hqne
    exact hk q hqs (fun h ↦ hqne (WithMetric.ext (h.trans hp₀.symm))) (u q) (v q)
      (Matrix.det_gram_ne_zero_iff_linearIndependent.mp (by rwa [Matrix.real_det_gram_fin_two]))
  have : (𝓝[≠] p₀).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [closure_compl_singleton]; trivial)
  simpa [hu₀, hv₀] using tendsto_nhds_unique
    ((hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev) tendsto_const_nhds

/-- **Near the tip (including at `0`), the standard cap has constant sectional curvature
`1 / 4`.** -/
theorem exists_hasSectionalCurvatureAt_withMetric_round :
    ∃ r₀ > 0, ∀ p : WithMetric (hf.metric V), ‖p.ofWithMetric‖ < r₀ →
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).HasSectionalCurvatureAt
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p (1 / 4) := by
  rcases Nat.eq_zero_or_pos (finrank ℝ V) with hd0 | hdpos
  · refine ⟨1, one_pos, fun p _ ↦
      (leviCivitaConnection 𝓘(ℝ, V)
        (WithMetric (hf.metric V))).hasSectionalCurvatureAt_of_finrank_le_one
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p (1 / 4) ?_⟩
    rw [(tangentSpaceCastModel 𝓘(ℝ, V) p).toLinearEquiv.finrank_eq, hd0]
    exact Nat.zero_le 1
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hdpos.ne'
    let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
    obtain ⟨r₀, hr₀, hpunct⟩ :=
      hf.exists_hasSectionalCurvatureAt_puncturedMetric_round (n := n) (V := V)
    have haway : ∀ q : WithMetric (hf.metric V), ‖q.ofWithMetric‖ < r₀ → q.ofWithMetric ≠ 0 →
        ∀ X Y : TangentSpace 𝓘(ℝ, V) q, LinearIndependent ℝ ![X, Y] →
        (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) q X Y = 1 / 4 := by
      intro q hqr hq0 X Y hXY
      obtain ⟨z, u, v, hz, hli, hsec⟩ :=
        hf.sectionalCurvature_withMetric_of_ne_zero (n := n) hq0 X Y
      let _ : RiemannianBundle (fun w : standardCapRadialDomain × sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) w) := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
      exact hsec.trans ((hpunct z (hz.trans_lt hqr)).sectionalCurvature_eq u v (hli.2 hXY))
    refine ⟨r₀, hr₀, fun p hp ↦ (hasSectionalCurvatureAt_iff _ _ _ _).2 fun X Y hXY ↦ ?_⟩
    rcases eq_or_ne p.ofWithMetric 0 with hp0 | hp0
    · exact hf.sectionalCurvature_withMetric_tip_limit hp0 hXY
        (s := WithMetric.ofWithMetric ⁻¹' Metric.ball (0 : V) r₀)
        ((Metric.isOpen_ball.preimage WithMetric.continuous_ofWithMetric).mem_nhds
          (by simp [hp0, hr₀]))
        fun q hq hq0 u v huv ↦ haway q (by simpa using hq) hq0 u v huv
    · exact haway p hp hp0 X Y hXY

/-- **Every tangent two-plane of the standard cap (including at the tip) has nonnegative sectional
curvature.** -/
theorem sectionalCurvature_withMetric_nonneg (p : WithMetric (hf.metric V))
    (X Y : TangentSpace 𝓘(ℝ, V) p) :
    0 ≤ (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p X Y := by
  by_cases hXY : LinearIndependent ℝ ![X, Y]
  · rcases eq_or_ne p.ofWithMetric 0 with hp0 | hp0
    · obtain ⟨r₀, hr₀, hround⟩ := hf.exists_hasSectionalCurvatureAt_withMetric_round (V := V)
      rw [(hround p (by simp [hp0, hr₀])).sectionalCurvature_eq X Y hXY]
      norm_num
    · have hdpos : 0 < finrank ℝ V := by
        have h := hXY.fintype_card_le_finrank
        rw [Fintype.card_fin, (tangentSpaceCastModel 𝓘(ℝ, V) p).toLinearEquiv.finrank_eq] at h
        omega
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hdpos.ne'
      let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
      obtain ⟨z, u, v, -, -, hsec⟩ := hf.sectionalCurvature_withMetric_of_ne_zero (n := n) hp0 X Y
      rw [hsec]
      exact hf.sectionalCurvature_puncturedMetric_nonneg (n := n) z u v
  · rw [sectionalCurvature_apply,
      not_not.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr hXY), div_zero]

end Global

end TauCeti.IsStandardCapProfile
