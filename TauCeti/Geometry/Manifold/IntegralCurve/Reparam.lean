/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Topology.Instances.Sign
import TauCeti.Analysis.Calculus.IntervalIntegral.Periodic
import TauCeti.Topology.VectorBundle.Smul

/-!
# Reparametrizing periodic integral curves

Let `γ` be a `T`-periodic integral curve of a vector field `X` on a manifold, and let `Y` be a
second vector field which is a nonzero multiple of `X` along `γ`: `Y (γ t) = h t • X (γ t)` with
`h t ≠ 0`, for a continuous `T`-periodic function `h`. Then `γ` traces a periodic integral curve of
`Y` after a change of time. If `h` is positive, the new time is `θ t = ∫₀ᵗ 1 / h`, and `γ ∘ θ⁻¹` is
an integral curve of `Y`, since `(θ⁻¹)' = h ∘ θ⁻¹`. Periodicity of `h` makes
`θ - (θ T / T) • id` periodic, so `θ` is a homeomorphism of `ℝ` and `γ ∘ θ⁻¹` has period `θ T`.
If `h` is negative, the time is reversed.

When `X` does not vanish along `γ`, the factor `h t` is uniquely determined by
`Y (γ t) = h t • X (γ t)`; since `γ (t + T) = γ t`, uniqueness forces `h` to be `T`-periodic. If
moreover `X` and `Y` are continuous along `γ`, then `h` is continuous, so only the pointwise
proportionality has to be checked.

This is how one closed orbit of a line field, the closed characteristic of a hypersurface in a
symplectic manifold, is traced by the periodic orbits of different vector fields spanning the line
field, each with its own period.

## Main results

* `IsMIntegralCurve.exists_homeomorph_isMIntegralCurve_comp_of_periodic`: reparametrization by a
  given continuous, periodic, nonvanishing factor.
* `IsMIntegralCurve.exists_homeomorph_isMIntegralCurve_comp`: reparametrization when `Y` is
  pointwise a nonzero multiple of `X` along `γ`, with both fields continuous along `γ`.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 1.1 (closed characteristics and their parametrizations by Hamiltonian flows).
-/

public section

noncomputable section

open Bundle Function Set
open scoped Manifold Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {γ : ℝ → M} {X Y : (x : M) → TangentSpace I x} {T : ℝ} {h : ℝ → ℝ}

namespace IsMIntegralCurve

/-- The reparametrization for a positive factor `h`, by the time change
`Function.Periodic.exists_homeomorph_hasDerivAt_of_pos`. -/
private theorem exists_homeomorph_isMIntegralCurve_comp_of_pos (hγ : IsMIntegralCurve γ X)
    (hT : T ≠ 0) (hper : Periodic γ T) (hh : Continuous h) (hpos : ∀ t, 0 < h t)
    (hhT : Periodic h T) (hY : ∀ t, Y (γ t) = h t • X (γ t)) :
    ∃ ψ : ℝ ≃ₜ ℝ, ψ 0 = 0 ∧ ∃ T', T' ≠ 0 ∧ Periodic (γ ∘ ψ) T' ∧
      IsMIntegralCurve (γ ∘ ψ) Y := by
  -- Replacing `T` by `-T` if necessary, the common period of `γ` and `h` is positive.
  obtain ⟨T₀, hT₀, hper₀, hhT₀⟩ : ∃ T₀, 0 < T₀ ∧ Periodic γ T₀ ∧ Periodic h T₀ := by
    rcases hT.lt_or_gt with hT | hT
    exacts [⟨-T, neg_pos.2 hT, hper.neg, hhT.neg⟩, ⟨T, hT, hper, hhT⟩]
  obtain ⟨ψ, hψ0, ⟨T', hT', hψT'⟩, hψd⟩ := hhT₀.exists_homeomorph_hasDerivAt_of_pos hT₀ hh hpos
  refine ⟨ψ, hψ0, T', hT', fun s ↦ by simp only [comp_apply, hψT', hper₀ (ψ s)], fun s ↦ ?_⟩
  have hcomp := (hγ (ψ s)).comp s (hψd s).hasFDerivAt.hasMFDerivAt
  have heq : (1 : ℝ →L[ℝ] ℝ).smulRight (Y ((γ ∘ ψ) s)) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (X (γ (ψ s))) ∘L .toSpanSingleton ℝ (h (ψ s)) := by
    ext
    simp [hY]
  rw [heq]
  exact hcomp

/-- **Reparametrizing a periodic integral curve.** Let `γ` be an integral curve of `X` of nonzero
period `T`, and let `Y (γ t) = h t • X (γ t)` for a continuous, `T`-periodic, nowhere vanishing
function `h`. Then, for a homeomorphism `ψ` of `ℝ` fixing `0`, the curve `γ ∘ ψ` is a periodic
integral curve of `Y`, of nonzero period. -/
theorem exists_homeomorph_isMIntegralCurve_comp_of_periodic
    (hγ : IsMIntegralCurve γ X) (hT : T ≠ 0) (hper : Periodic γ T) (hh : Continuous h)
    (hh0 : ∀ t, h t ≠ 0) (hhT : Periodic h T) (hY : ∀ t, Y (γ t) = h t • X (γ t)) :
    ∃ ψ : ℝ ≃ₜ ℝ, ψ 0 = 0 ∧ ∃ T', T' ≠ 0 ∧ Periodic (γ ∘ ψ) T' ∧
      IsMIntegralCurve (γ ∘ ψ) Y := by
  -- A continuous nonvanishing function on `ℝ` has the constant sign of its value at `0`.
  have hsign : ∀ t, SignType.sign (h t) = SignType.sign (h 0) := fun t ↦
    isPreconnected_univ.sign_eq_of_continuousOn hh.continuousOn (fun t _ ↦ hh0 t) trivial trivial
  rcases (hh0 0).lt_or_gt with hneg0 | hpos0
  swap
  · exact exists_homeomorph_isMIntegralCurve_comp_of_pos hγ hT hper hh
      (fun t ↦ sign_eq_one_iff.1 ((hsign t).trans (sign_pos hpos0))) hhT hY
  have hneg : ∀ t, h t < 0 := fun t ↦ sign_eq_neg_one_iff.1 ((hsign t).trans (sign_neg hneg0))
  -- For a negative factor, reparametrize along `-Y` with the factor `-h`, then reverse time.
  obtain ⟨ψ, hψ0, T', hT', hper', hψ⟩ :=
    exists_homeomorph_isMIntegralCurve_comp_of_pos (Y := fun x ↦ -Y x) hγ hT hper hh.neg
      (fun t ↦ neg_pos.2 (hneg t)) (fun t ↦ by simp [hhT t])
      fun t ↦ by rw [hY, Pi.neg_apply, neg_smul]
  refine ⟨(Homeomorph.neg ℝ).trans ψ, by simp [hψ0], T', hT', fun s ↦ ?_, ?_⟩
  · have := hper'.sub_eq (-s)
    simp only [comp_apply, Homeomorph.trans_apply, Homeomorph.coe_neg, neg_add,
      ← sub_eq_add_neg] at this ⊢
    exact this
  · have hrev := (isMIntegralCurve_comp_mul_ne_zero (γ := γ ∘ ψ) (v := fun x ↦ -Y x)
      (neg_ne_zero.2 one_ne_zero)).2 hψ
    have hYY : ((-1 : ℝ) • fun x ↦ -Y x) = Y := by
      funext x
      simp
    rw [hYY] at hrev
    convert hrev using 1
    funext s
    simp

/-- **Reparametrizing a periodic integral curve along a proportional field.** Let `γ` be an
integral curve of `X` of nonzero period `T`, along which `X` does not vanish and both `X` and `Y`
are continuous. If `Y (γ t)` is a nonzero multiple of `X (γ t)` for every `t`, then, for a
homeomorphism `ψ` of `ℝ` fixing `0`, the curve `γ ∘ ψ` is a periodic integral curve of `Y`, of
nonzero period. -/
theorem exists_homeomorph_isMIntegralCurve_comp [IsManifold I 1 M] (hγ : IsMIntegralCurve γ X)
    (hT : T ≠ 0) (hper : Periodic γ T) (hX : ∀ t, ContinuousAt (T% X) (γ t))
    (hY : ∀ t, ContinuousAt (T% Y) (γ t)) (hX0 : ∀ t, X (γ t) ≠ 0)
    (hYX : ∀ t, ∃ a : ℝ, a ≠ 0 ∧ Y (γ t) = a • X (γ t)) :
    ∃ ψ : ℝ ≃ₜ ℝ, ψ 0 = 0 ∧ ∃ T', T' ≠ 0 ∧ Periodic (γ ∘ ψ) T' ∧
      IsMIntegralCurve (γ ∘ ψ) Y := by
  choose a ha0 ha using hYX
  have hcont : Continuous a := continuous_iff_continuousAt.2 fun t ↦
    TauCeti.VectorBundle.continuousAt_of_eventually_eq_smul (φ := fun t ↦ T% X (γ t))
      (ψ := fun t ↦ T% Y (γ t)) ((hX t).comp hγ.continuous.continuousAt)
      ((hY t).comp hγ.continuous.continuousAt) (Filter.Eventually.of_forall fun s ↦ by
        simp only [TotalSpace.mk', ha s]) (hX0 t)
  -- The factor is determined by `X (γ t) ≠ 0`, so it inherits the period of `γ`.
  have haT : Periodic a T := fun t ↦ smul_left_injective ℝ (hX0 t) <| by
    have h1 := ha (t + T)
    rw [hper t] at h1
    exact h1.symm.trans (ha t)
  exact hγ.exists_homeomorph_isMIntegralCurve_comp_of_periodic hT hper hcont ha0 haT ha

end IsMIntegralCurve
