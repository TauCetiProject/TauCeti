/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import TauCeti.Analysis.ODE.DysonSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# Frame trivialization of nonautonomous linear ODEs

To analyze `ξ' = S_t ξ` on a Banach space `V` via operators on a model space `F` (such as circle
Sobolev spaces), a frame `Φ : ℝ → F →L[ℝ] V` pulls `ξ(t) = Φ(t) ζ(t)` back to `F` by replacing `S`
with `S_Φ(t) = Φ(t)⁻¹ (S(t) Φ(t) - Φ'(t))` (`TauCeti.trivializedCoeff`), feeding
`TauCeti/Geometry/Symplectic/FrameTrivialization.lean` and
`TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator/Trivialization.lean`. When `Φ, ζ` are
differentiable at `t` and `Φ t` is invertible, `Φ t` intertwines `ζ' - S_Φ(t) ζ` with `ξ' - S_t ξ`;
`trivializedCoeff Φ S` is `C^n` for complete `F`, `C^(n+1)` invertible `Φ` and `C^n` `S` (in
particular continuous for `C¹` `Φ` and continuous `S`), inherits `T`-periodicity, and sends
`S_t - δ • K_t` to `S_Φ(t) - δ • K₀`. The propagator of `ζ' = S_Φ(t) ζ` is that of
`ξ' = S_t ξ` read in the frame (`TauCeti.dysonSeriesLeft_trivializedCoeff_apply`), so for a frame
with `Φ d = Φ 0` the two return maps at time `d` are conjugate and `1` minus either has the same
determinant (`TauCeti.det_one_sub_dysonSeriesLeft_trivializedCoeff`). Adapts
`TauCeti.frameConnection`
(`TauCeti/Geometry/Symplectic/JHolomorphic/OrbitTorus/Trivialization.lean`).

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2, §2.2.
-/

public section

noncomputable section

open ContinuousLinearMap Function

namespace TauCeti

variable {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- The trivialized ODE coefficient `S_Φ(t) = Φ(t)⁻¹ (S(t) Φ(t) - Φ'(t))` along `Φ`. -/
def trivializedCoeff (Φ : ℝ → F →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) : F →L[ℝ] F :=
  (Φ t).inverse ∘L (S t ∘L Φ t - deriv Φ t)

/-- Operator-level unfolding of `trivializedCoeff`. -/
theorem trivializedCoeff_def (Φ : ℝ → F →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) :
    trivializedCoeff Φ S t = (Φ t).inverse ∘L (S t ∘L Φ t - deriv Φ t) := (rfl)

/-- Pointwise evaluation of `trivializedCoeff`. -/
@[simp] theorem trivializedCoeff_apply (Φ : ℝ → F →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) (v : F) :
    trivializedCoeff Φ S t v = (Φ t).inverse (S t (Φ t v) - deriv Φ t v) := (rfl)

/-- Trivializing along the constant identity frame leaves the ODE coefficient unchanged. -/
@[simp] theorem trivializedCoeff_const_id (S : ℝ → F →L[ℝ] F) (t : ℝ) :
    trivializedCoeff (fun _ ↦ ContinuousLinearMap.id ℝ F) S t = S t :=
  ContinuousLinearMap.ext fun _ ↦ by simp [trivializedCoeff_apply]

/-- Trivializing along a constant continuous linear equivalence conjugates `S_t`. -/
@[simp] theorem trivializedCoeff_const_equiv (e : F ≃L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) :
    trivializedCoeff (fun _ ↦ (e : F →L[ℝ] V)) S t =
      (e.symm : V →L[ℝ] F) ∘L S t ∘L (e : F →L[ℝ] V) :=
  ContinuousLinearMap.ext fun _ ↦ by simp [trivializedCoeff_apply]

/-- If `Φ` and `ζ` are differentiable at `t` and `Φ t` is invertible, `Φ t` maps
`deriv ζ t - trivializedCoeff Φ S t (ζ t)` to `deriv (fun r ↦ Φ r (ζ r)) t - S t (Φ t (ζ t))`. -/
theorem deriv_clm_apply_sub_eq_apply_deriv_sub_trivializedCoeff {Φ : ℝ → F →L[ℝ] V}
    {S : ℝ → V →L[ℝ] V} {ζ : ℝ → F} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t)
    (hΦ : (Φ t).IsInvertible) (hζ : DifferentiableAt ℝ ζ t) :
    deriv (fun r ↦ Φ r (ζ r)) t - S t (Φ t (ζ t)) =
      Φ t (deriv ζ t - trivializedCoeff Φ S t (ζ t)) := by
  rw [(hΦd.hasDerivAt.clm_apply hζ.hasDerivAt).deriv, map_sub, trivializedCoeff_apply,
    hΦ.self_apply_inverse]
  abel

/-- When `Φ` and `ζ` are differentiable at `t` and `Φ t` is invertible, `r ↦ Φ r (ζ r)` solves
`ξ' = S_t ξ` at `t` iff `ζ` solves `ζ' = S_Φ(t) ζ` at `t`. -/
theorem hasDerivAt_clm_apply_iff_hasDerivAt_trivializedCoeff {Φ : ℝ → F →L[ℝ] V}
    {S : ℝ → V →L[ℝ] V} {ζ : ℝ → F} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t)
    (hΦ : (Φ t).IsInvertible) (hζ : DifferentiableAt ℝ ζ t) :
    HasDerivAt (fun r ↦ Φ r (ζ r)) (S t (Φ t (ζ t))) t ↔
      HasDerivAt ζ (trivializedCoeff Φ S t (ζ t)) t := by
  have hd := hΦd.hasDerivAt.clm_apply hζ.hasDerivAt
  refine ⟨fun h ↦ ?_, fun h ↦ (hΦd.hasDerivAt.clm_apply h).congr_deriv ?_⟩
  · have hsub : Φ t (deriv ζ t - trivializedCoeff Φ S t (ζ t)) = 0 := by
      rw [map_sub, trivializedCoeff_apply, hΦ.self_apply_inverse, ← hd.unique h]; abel
    exact (sub_eq_zero.1 (hΦ.injective (hsub.trans (map_zero (Φ t)).symm))) ▸ hζ.hasDerivAt
  · rw [trivializedCoeff_apply, hΦ.self_apply_inverse]; abel

/-- For complete `F`, a `C^(n+1)` frame `Φ` with invertible values and a `C^n` coefficient `S`,
`trivializedCoeff Φ S` is `C^n`. -/
theorem contDiff_trivializedCoeff [CompleteSpace F] {n : ℕ} {Φ : ℝ → F →L[ℝ] V}
    {S : ℝ → V →L[ℝ] V} (hΦ : ContDiff ℝ (n + 1) Φ) (hinv : ∀ t, (Φ t).IsInvertible)
    (hS : ContDiff ℝ n S) : ContDiff ℝ n (trivializedCoeff Φ S) := by
  have hΦn : ContDiff ℝ n Φ := hΦ.of_le (by norm_cast; omega)
  have hderiv : ContDiff ℝ n (deriv Φ) := (contDiff_succ_iff_deriv.1 hΦ).2.2
  exact (hΦn.clm_inverse hinv).clm_comp ((hS.clm_comp hΦn).sub hderiv)

/-- For complete `F`, `C¹` `Φ` with invertible values, and continuous `S`, `trivializedCoeff Φ S`
is continuous. -/
theorem continuous_trivializedCoeff [CompleteSpace F] {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V}
    (hΦ : ContDiff ℝ 1 Φ) (hinv : ∀ t, (Φ t).IsInvertible) (hS : Continuous S) :
    Continuous (trivializedCoeff Φ S) :=
  (contDiff_trivializedCoeff (n := 0) (by simpa using hΦ) hinv (contDiff_zero.2 hS)).continuous

/-- Periodicity of `Φ` and `S` passes to `trivializedCoeff Φ S`. -/
theorem periodic_trivializedCoeff {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V} {T : ℝ}
    (hΦ : Periodic Φ T) (hS : Periodic S T) : Periodic (trivializedCoeff Φ S) T := fun t ↦ by
  simp only [trivializedCoeff_def, hΦ t, hS t, hΦ.deriv t]

/-- Subtracting `δ • K_t` from `S_t`, where `K_t` intertwines `K₀` through invertible `Φ t`,
subtracts `δ • K₀` from `trivializedCoeff Φ S t`. -/
theorem trivializedCoeff_sub_smul {Φ : ℝ → F →L[ℝ] V} {S K : ℝ → V →L[ℝ] V} {K₀ : F →L[ℝ] F}
    {t : ℝ} (hΦ : (Φ t).IsInvertible) (hK : ∀ v, K t (Φ t v) = Φ t (K₀ v)) (δ : ℝ) :
    trivializedCoeff Φ (fun r ↦ S r - δ • K r) t = trivializedCoeff Φ S t - δ • K₀ := by
  ext v
  simp only [trivializedCoeff_apply, sub_apply, smul_apply, hK, sub_right_comm _ (δ • Φ t (K₀ v)),
    map_sub, map_smul, hΦ.inverse_apply_self]

section Propagator

variable [CompleteSpace F] [CompleteSpace V]

/-- **The propagator in a frame.** For a `C¹` frame `Φ` with invertible values and a continuous
coefficient `S`, the propagator of the trivialized equation `ζ' = S_Φ(t) ζ` is that of
`ξ' = S_t ξ` read in the frame: `Ψ_Φ(t) v = Φ(t)⁻¹ (Ψ(t) (Φ(0) v))`. -/
theorem dysonSeriesLeft_trivializedCoeff_apply {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V}
    (hΦ : ContDiff ℝ 1 Φ) (hinv : ∀ t, (Φ t).IsInvertible) (hS : Continuous S) (t : ℝ) (v : F) :
    dysonSeriesLeft (trivializedCoeff Φ S) t v =
      (Φ t).inverse (dysonSeriesLeft S t (Φ 0 v)) := by
  have hΦd := hΦ.differentiable one_ne_zero
  have hΨd : Differentiable ℝ fun t ↦ (Φ t).inverse :=
    ((hΦ.clm_inverse hinv).differentiable one_ne_zero)
  -- `ζ(r) = Φ(r)⁻¹ (Ψ(r) (Φ(0) v))` solves the trivialized equation, since `Φ ζ` solves `ξ' = S ξ`.
  set ζ : ℝ → F := fun r ↦ (Φ r).inverse (dysonSeriesLeft S r (Φ 0 v))
  have hζd : Differentiable ℝ ζ := hΨd.clm_apply fun r ↦
    (hasDerivAt_dysonSeriesLeft_apply hS (Φ 0 v) r).differentiableAt
  have hζ (r : ℝ) : HasDerivAt ζ (trivializedCoeff Φ S r (ζ r)) r := by
    refine (hasDerivAt_clm_apply_iff_hasDerivAt_trivializedCoeff (hΦd r) (hinv r) (hζd r)).1 ?_
    simp only [ζ, (hinv _).self_apply_inverse]
    exact hasDerivAt_dysonSeriesLeft_apply hS (Φ 0 v) r
  have h0 : ζ 0 = v := by simp [ζ, dysonSeriesLeft_zero, (hinv 0).inverse_apply_self]
  have h := (eq_dysonSeriesLeft_apply (continuous_trivializedCoeff hΦ hinv hS) hζ t).symm
  rwa [h0] at h

/-- **The return map in a frame.** For a `C¹` frame `Φ` with invertible values and `Φ d = Φ 0`,
and a continuous coefficient `S`, the return map at time `d` of the trivialized equation
`ζ' = S_Φ(t) ζ` is conjugate by `Φ 0` to that of `ξ' = S_t ξ`, so `1` minus either has the same
determinant. -/
theorem det_one_sub_dysonSeriesLeft_trivializedCoeff {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V}
    (hΦ : ContDiff ℝ 1 Φ) (hinv : ∀ t, (Φ t).IsInvertible) (hS : Continuous S) {d : ℝ}
    (hd : Φ d = Φ 0) :
    LinearMap.det ((1 - dysonSeriesLeft (trivializedCoeff Φ S) d : F →L[ℝ] F) : F →ₗ[ℝ] F) =
      LinearMap.det ((1 - dysonSeriesLeft S d : V →L[ℝ] V) : V →ₗ[ℝ] V) := by
  obtain ⟨e, he⟩ := hinv 0
  have h : ((1 - dysonSeriesLeft (trivializedCoeff Φ S) d : F →L[ℝ] F) : F →ₗ[ℝ] F) =
      (e.symm.toLinearEquiv : V →ₗ[ℝ] F) ∘ₗ ((1 - dysonSeriesLeft S d : V →L[ℝ] V) : V →ₗ[ℝ] V) ∘ₗ
        (e.symm.toLinearEquiv.symm : F →ₗ[ℝ] V) := by
    refine LinearMap.ext fun v ↦ ?_
    have hinv' : (Φ d).inverse = (e.symm : V →L[ℝ] F) := by
      rw [hd, ← he, ContinuousLinearMap.inverse_equiv]
    simp [dysonSeriesLeft_trivializedCoeff_apply hΦ hinv hS, hinv', ← he]
  rw [h, LinearMap.det_conj]

end Propagator

end TauCeti
