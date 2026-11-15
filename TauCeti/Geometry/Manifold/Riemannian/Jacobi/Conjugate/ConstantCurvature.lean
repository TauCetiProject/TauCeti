/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Conjugate.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Model
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Conjugate multiplicity in constant curvature

Along a radial geodesic in constant curvature, each nonzero zero of the model sine
has conjugate multiplicity `dim M - 1`, as computed by
`conjugateMultiplicity_eq_ite_curvatureSine`. Initial covariant differentiation identifies
the endpoint-zero Jacobi fields with the orthogonal complement of the velocity:
the radial exponential variation supplies a field for every normal initial derivative.
Away from model zeros the endpoint-zero space is trivial, even for geodesics that
have not been presented as radial exponential curves.

All parameter sets and exponential domains are explicit. No completeness or
unit-speed hypothesis is imposed. In dimension one the normal space is zero, so
even the positive-curvature model times are not conjugate. In dimension at least two,
`isConjugateOn_iff_exists_int_mul_pi_div_sqrt` identifies the positive-curvature
conjugate parameters with integer multiples of `π / √(κ c²)`.

The construction uses the radial fields of `isJacobiFieldOn_mfderiv_riemannianExp`
and the model norm formula `IsJacobiFieldOn.norm_eq_abs_curvatureSine_mul_norm`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (Jacobi fields and conjugate points in constant curvature).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ} {a b κ : ℝ}

/-- Away from zeros of the constant-curvature model sine, an endpoint-zero Jacobi field
vanishes identically. This includes constant geodesics and all signs of curvature. -/
theorem endpointJacobiFieldSpace_eq_bot_of_curvatureSine_ne_zero
    (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    (ha : a ∈ s) (hb : b ∈ s)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (γ t) κ)
    (hS : curvatureSine (κ * ‖curveVelocityWithin I γ s a‖ ^ 2) (b - a) ≠ 0) :
    endpointJacobiFieldSpace hγ a b = ⊥ := by
  apply (Submodule.eq_bot_iff _).2
  intro V hV
  have hab : a ≠ b := by
    rintro rfl
    exact hS (by simp)
  let W : endpointJacobiFieldSpace hγ a b := ⟨V, hV⟩
  obtain ⟨hVa, hVb⟩ := (mem_endpointJacobiFieldSpace hγ V).1 hV
  have hnorm := (isJacobiFieldOn_of_mem_jacobiFieldSpace V).norm_eq_abs_curvatureSine_mul_norm
    hs ha hκ hVa (inner_endpointJacobiFieldSpace_deriv_velocity_eq_zero W hs ha hb hab) hb
  rw [hVb, norm_zero] at hnorm
  have hD : endpointJacobiInitialDerivative hγ ha b W = 0 := by
    simpa only [endpointJacobiInitialDerivative_apply, norm_eq_zero] using
      (mul_eq_zero.1 hnorm.symm).resolve_left (abs_ne_zero.2 hS)
  have hW : W = 0 := endpointJacobiInitialDerivative_injective hγ hs ha
    (hD.trans (map_zero _).symm)
  exact congrArg Subtype.val hW

variable [I.Boundaryless] {p : M} {v : TangentSpace I p}
  {hγ : IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s}

/-- At a nonzero model zero along a radial geodesic, the range of initial differentiation
on endpoint-zero Jacobi fields is exactly the normal space to the initial velocity. -/
theorem range_endpointJacobiInitialDerivative_of_curvatureSine_eq_zero
    (hs : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v)
    (h0 : (0 : ℝ) ∈ s) (hb : b ∈ s) (hb0 : b ≠ 0)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (t • v)) κ)
    (hS : curvatureSine
      (κ * ‖curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0‖ ^ 2) b = 0) :
    LinearMap.range (endpointJacobiInitialDerivative hγ h0 b) =
      (ℝ ∙ curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0)ᗮ := by
  ext w
  constructor
  · rintro ⟨V, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.2
      (by simpa using inner_endpointJacobiFieldSpace_deriv_velocity_eq_zero V hs h0 hb hb0.symm)
  · intro hw
    -- The initial fibre is identified with `T_p M` by `exp_p 0 = p`; the underlying
    -- tangent-space carrier is `E` in both fibres.
    let w₀ : TangentSpace I p := w
    have hJ := (isJacobiFieldOn_mfderiv_riemannianExp p v w₀).mono
      hγ.uniqueDiffOn hsub
    have hD : alongCurveWithin (leviCivitaConnection I M)
        (fun t : ℝ ↦ riemannianExp I M p (t • v))
        (fun t ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w₀))
        s 0 = w := by
      rw [(isJacobiFieldOn_mfderiv_riemannianExp p v w₀).alongCurveWithin_subset
        (hγ.uniqueDiffOn 0 h0) hsub h0, alongCurveWithin_mfderiv_riemannianExp_zero]
    have hJ0 : mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p)
        ((0 : ℝ) • v) ((0 : ℝ) • w₀) = 0 := by
      rw [zero_smul ℝ w₀]
      exact map_zero _
    have hJb : mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (b • v) (b • w₀) = 0 := by
      have hn := hJ.norm_eq_abs_curvatureSine_mul_norm hs h0 hκ hJ0
        (by rw [hD]; exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 hw) hb
      simpa only [sub_zero, hS, abs_zero, zero_mul, norm_eq_zero] using hn
    let V : endpointJacobiFieldSpace hγ 0 b :=
      ⟨hJ.toJacobiFieldSpace, by simpa only [mem_endpointJacobiFieldSpace,
        hJ.toJacobiFieldSpace_apply h0, hJ.toJacobiFieldSpace_apply hb] using ⟨hJ0, hJb⟩⟩
    refine ⟨V, ?_⟩
    simpa only [endpointJacobiInitialDerivative_apply] using
      (hJ.alongCurveWithin_toJacobiFieldSpace h0).trans hD

/-- Every nonzero model zero has multiplicity `dim M - 1` along a nonconstant radial
geodesic in constant curvature. The parameter set may be a closed interval. -/
theorem conjugateMultiplicity_eq_finrank_sub_one_of_curvatureSine_eq_zero
    (hs : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v)
    (h0 : (0 : ℝ) ∈ s) (hb : b ∈ s) (hb0 : b ≠ 0)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (t • v)) κ)
    (hS : curvatureSine
      (κ * ‖curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0‖ ^ 2) b = 0) :
    conjugateMultiplicity hγ hs h0 b = Module.finrank ℝ E - 1 := by
  have hv : curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0 ≠ 0 := by
    intro hv
    exact hb0 (by simpa only [hv, norm_zero, zero_pow two_ne_zero, mul_zero,
      curvatureSine_zero_left] using hS)
  have hrange := range_endpointJacobiInitialDerivative_of_curvatureSine_eq_zero
    (hγ := hγ) hs hsub h0 hb hb0 hκ hS
  have hinj := endpointJacobiInitialDerivative_injective hγ hs h0 (b := b)
  have hdim := (ℝ ∙ curveVelocityWithin I
    (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hv, TauCeti.finrank_tangentSpace] at hdim
  rw [conjugateMultiplicity_eq_finrank, ← LinearMap.finrank_range_of_inj hinj, hrange]
  omega

/-- The complete multiplicity formula along a radial constant-curvature geodesic.
The zero-speed and one-dimensional cases have multiplicity zero. -/
theorem conjugateMultiplicity_eq_ite_curvatureSine
    (hs : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v)
    (h0 : (0 : ℝ) ∈ s) (hb : b ∈ s) (hb0 : b ≠ 0)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (t • v)) κ) :
    conjugateMultiplicity hγ hs h0 b =
      if curvatureSine
        (κ * ‖curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0‖ ^ 2) b = 0
      then Module.finrank ℝ E - 1 else 0 := by
  split_ifs with hS
  · exact conjugateMultiplicity_eq_finrank_sub_one_of_curvatureSine_eq_zero
      hs hsub h0 hb hb0 hκ hS
  · have hbot := endpointJacobiFieldSpace_eq_bot_of_curvatureSine_ne_zero
      hγ hs h0 hb hκ (by simpa only [sub_zero] using hS)
    rw [conjugateMultiplicity_eq_finrank, hbot]
    exact finrank_bot ℝ _

/-- In dimension at least two, the nonzero conjugate times of a radial geodesic in
constant curvature are exactly the zeros of the model sine at its actual speed. -/
theorem isConjugateOn_iff_curvatureSine_eq_zero
    (hγ : IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s)
    (hs : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v)
    (h0 : (0 : ℝ) ∈ s) (hb : b ∈ s) (hb0 : b ≠ 0)
    (hn : 2 ≤ Module.finrank ℝ E)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (t • v)) κ) :
    IsConjugateOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0 b ↔
      curvatureSine
        (κ * ‖curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0‖ ^ 2) b = 0 := by
  rw [← conjugateMultiplicity_pos_iff hγ hs h0 hb hb0.symm,
    conjugateMultiplicity_eq_ite_curvatureSine hs hsub h0 hb hb0 hκ]
  split_ifs <;> simp_all only [lt_self_iff_false, iff_true]
  omega

/-- In positive constant curvature and dimension at least two, conjugate parameters
are the integer multiples of `π / √(κ c²)`, where `c` is the initial speed.
Only multiples belonging to the prescribed geodesic parameter set are considered. -/
theorem isConjugateOn_iff_exists_int_mul_pi_div_sqrt
    (hγ : IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s)
    (hs : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v)
    (h0 : (0 : ℝ) ∈ s) (hb : b ∈ s) (hb0 : b ≠ 0)
    (hn : 2 ≤ Module.finrank ℝ E) (hκpos : 0 < κ)
    (hκ : ∀ t ∈ s, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (t • v)) κ) :
    IsConjugateOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0 b ↔
      ∃ n : ℤ, b = (n : ℝ) * Real.pi /
        √(κ * ‖curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0‖ ^ 2) := by
  rw [isConjugateOn_iff_curvatureSine_eq_zero hγ hs hsub h0 hb hb0 hn hκ]
  by_cases hv : curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0 = 0
  · simp [hv, hb0]
  have hc := mul_pos hκpos (sq_pos_of_ne_zero (norm_ne_zero_iff.2 hv))
  have hroot := (Real.sqrt_pos.2 hc).ne'
  rw [curvatureSine_of_pos hc, div_eq_zero_iff, or_iff_left hroot, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (eq_div_iff hroot).2 (by simpa only [mul_comm] using hn.symm)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa only [mul_comm] using ((eq_div_iff hroot).1 hn).symm⟩

end TauCeti.Manifold
