/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Convexity
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Norm comparison for Jacobi fields in nonpositive curvature

The norm-convexity theorem
`IsJacobiFieldOn.convexOn_norm_of_sectionalCurvature_nonpos` applies to the radial
Jacobi field `J(t) = d(exp_p)_(tv)(tw)`. Convexity and `J(0) = 0`
show that `|J(t)| / t` cannot decrease for positive time. Continuity of `d(exp_p)` at the
origin then gives `norm_le_norm_mfderiv_riemannianExp_of_sectionalCurvature_nonpos`:
`|d(exp_p)_v(w)| ≥ |w|` on the natural exponential domain.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 10–12 (Jacobi comparison and the Cartan–Hadamard theorem).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold InnerProductSpace Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {s : Set ℝ}

/-- In nonpositive sectional curvature along the radial segment from `0` to `v`, the
exponential differential does not decrease any tangent norm. The segment lies in the natural
exponential domain; completeness, unit speed and orthogonality to the radial vector are not
required. -/
theorem norm_le_norm_mfderiv_riemannianExp_of_sectionalCurvature_nonpos [I.Boundaryless]
    {p : M} {v : TangentSpace I p} (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u z : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ ![u, z] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (riemannianExp I M p (t • v)) u z ≤ 0)
    (w : TangentSpace I p) :
    ‖w‖ ≤ ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ := by
  have hsub : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.1 hv)
  have hJ := (isJacobiFieldOn_mfderiv_riemannianExp p v w).mono
    (uniqueDiffOn_Icc zero_lt_one) hsub
  have hc := hJ.convexOn_norm_of_sectionalCurvature_nonpos isPreconnected_Icc hK
  have hle : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) w‖ ≤
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ := by
    intro t ht
    have h := hc.2 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
      (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
    -- The source tangent space is canonically the original vector space. Apply linearity
    -- before rewriting the parameters, since the target fibre norms depend on those parameters.
    have hnorm (r : ℝ) :
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) (r • w)‖ =
          |r| * ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) w‖ := by
      calc
        _ = ‖r • mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) w‖ :=
          congrArg norm ((mfderiv 𝓘(ℝ, TangentSpace I p) I
            (riemannianExp I M p) (r • v)).map_smul r w)
        _ = _ := norm_smul r _
    simp_rw [hnorm] at h
    have htcoord : (1 - t) • (0 : ℝ) + t • (1 : ℝ) = t := by simp
    rw [htcoord] at h
    simp only [abs_zero, abs_one, zero_mul, one_mul, smul_eq_mul, abs_of_pos ht.1] at h
    rw [mul_zero, zero_add, one_smul] at h
    exact (mul_le_mul_iff_right₀ ht.1).1 h
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
    (F := E) (V := fun x : M ↦ TangentSpace I x)
  have hcont := ((contMDiffOn_riemannianExp p).continuousOn_norm_mfderiv
    (by simp) (isOpen_expDomain p) w).continuousAt
      ((isOpen_expDomain p).mem_nhds (zero_mem_expDomain p))
  have hsmul : Tendsto (fun t : ℝ ↦ t • v) (𝓝[>] 0) (𝓝 0) :=
    ((by fun_prop : Continuous (fun t : ℝ ↦ t • v)).tendsto' 0 0
      (zero_smul ℝ v)).mono_left nhdsWithin_le_nhds
  have hlim := hcont.tendsto.comp hsmul
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds zero_lt_one).filter_mono
      nhdsWithin_le_nhds] with t ht h1
    exact ⟨ht, h1⟩
  have hbound := le_of_tendsto hlim (hevent.mono fun t ht ↦ hle t ht)
  rw [mfderiv_riemannianExp_apply_zero, riemannianExp_zero] at hbound
  exact hbound

end TauCeti.Manifold
