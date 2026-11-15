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
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# Frame trivialization of nonautonomous linear ODEs

To analyze a nonautonomous linear ODE `ξ' = S_t ξ` on a Banach space `V` using operators defined on
a fixed model space `F` (such as Fourier-series Sobolev spaces on the circle), a moving frame
`Φ : ℝ → F →L[ℝ] V` pulls paths `ξ(t) = Φ(t) ζ(t)` back to `F` at the cost of a connection term
`-Φ(t)⁻¹ Φ'(t)`, replacing `S : ℝ → V →L[ℝ] V` by the trivialized coefficient
`S_Φ(t) = Φ(t)⁻¹ (S(t) Φ(t) - Φ'(t))` (`TauCeti.trivializedCoeff`). This feeds symplectic frame
preservation in `TauCeti/Geometry/Symplectic/FrameTrivialization.lean` and the trivialization of
linearized Hamiltonian Floer operators in
`TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator/Trivialization.lean`.

When `Φ` and `ζ` are differentiable at `t` and `Φ t` is invertible, `Φ t` intertwines
`ζ' - S_Φ(t) ζ` with `ξ' - S_t ξ` (`deriv_clm_apply_sub_eq_apply_deriv_sub_trivializedCoeff`,
`hasDerivAt_clm_apply_iff_hasDerivAt_trivializedCoeff`). Moreover, `trivializedCoeff Φ S` is
continuous when `F` is complete, `Φ` is `C¹` with invertible values, and `S` is continuous
(`continuous_trivializedCoeff`), inherits `T`-periodicity from `Φ` and `S`
(`periodic_trivializedCoeff`), and maps perturbations `S_t - δ • K_t` intertwining a model operator
`K₀` through `Φ t` to `S_Φ(t) - δ • K₀` (`trivializedCoeff_sub_smul`). Adapts
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
@[simp]
theorem trivializedCoeff_apply (Φ : ℝ → F →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) (v : F) :
    trivializedCoeff Φ S t v = (Φ t).inverse (S t (Φ t v) - deriv Φ t v) := (rfl)

/-- Trivializing along the constant identity frame leaves the ODE coefficient unchanged. -/
@[simp]
theorem trivializedCoeff_const_id (S : ℝ → F →L[ℝ] F) (t : ℝ) :
    trivializedCoeff (fun _ ↦ ContinuousLinearMap.id ℝ F) S t = S t :=
  ContinuousLinearMap.ext fun _ ↦ by simp [trivializedCoeff_apply]

/-- Trivializing along a constant continuous linear equivalence conjugates `S_t`. -/
@[simp]
theorem trivializedCoeff_const_equiv (e : F ≃L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) :
    trivializedCoeff (fun _ ↦ (e : F →L[ℝ] V)) S t =
      (e.symm : V →L[ℝ] F) ∘L S t ∘L (e : F →L[ℝ] V) :=
  ContinuousLinearMap.ext fun _ ↦ by simp [trivializedCoeff_apply]

/-- **Pulling back `ξ' - S_t ξ` along a differentiable frame:** if `Φ` and `ζ` are differentiable at
`t` and `Φ t` is invertible, `Φ t` maps `deriv ζ t - trivializedCoeff Φ S t (ζ t)` to
`deriv (fun r ↦ Φ r (ζ r)) t - S t (Φ t (ζ t))`. -/
theorem deriv_clm_apply_sub_eq_apply_deriv_sub_trivializedCoeff {Φ : ℝ → F →L[ℝ] V}
    {S : ℝ → V →L[ℝ] V} {ζ : ℝ → F} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t)
    (hΦ : (Φ t).IsInvertible) (hζ : DifferentiableAt ℝ ζ t) :
    deriv (fun r ↦ Φ r (ζ r)) t - S t (Φ t (ζ t)) =
      Φ t (deriv ζ t - trivializedCoeff Φ S t (ζ t)) := by
  rw [(hΦd.hasDerivAt.clm_apply hζ.hasDerivAt).deriv, map_sub, trivializedCoeff_apply,
    hΦ.self_apply_inverse]
  abel

/-- **Classical ODE correspondence under a frame:** when `Φ` and `ζ` are differentiable at `t` and
`Φ t` is invertible, `r ↦ Φ r (ζ r)` solves `ξ' = S_t ξ` at `t` iff `ζ` solves `ζ' = S_Φ(t) ζ` at
`t`. -/
theorem hasDerivAt_clm_apply_iff_hasDerivAt_trivializedCoeff {Φ : ℝ → F →L[ℝ] V}
    {S : ℝ → V →L[ℝ] V} {ζ : ℝ → F} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t)
    (hΦ : (Φ t).IsInvertible) (hζ : DifferentiableAt ℝ ζ t) :
    HasDerivAt (fun r ↦ Φ r (ζ r)) (S t (Φ t (ζ t))) t ↔
      HasDerivAt ζ (trivializedCoeff Φ S t (ζ t)) t := by
  have hd := hΦd.hasDerivAt.clm_apply hζ.hasDerivAt
  refine ⟨fun h ↦ ?_, fun h ↦ (hΦd.hasDerivAt.clm_apply h).congr_deriv ?_⟩
  · have hsub : Φ t (deriv ζ t - trivializedCoeff Φ S t (ζ t)) = 0 := by
      rw [map_sub, trivializedCoeff_apply, hΦ.self_apply_inverse, ← hd.unique h]
      abel
    exact (sub_eq_zero.1 (hΦ.injective (hsub.trans (map_zero (Φ t)).symm))) ▸ hζ.hasDerivAt
  · rw [trivializedCoeff_apply, hΦ.self_apply_inverse]
    abel

/-- If `F` is complete, `Φ` is `C¹` with invertible values, and `S` is continuous,
`trivializedCoeff Φ S` is continuous. -/
theorem continuous_trivializedCoeff [CompleteSpace F] {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V}
    (hΦ : ContDiff ℝ 1 Φ) (hinv : ∀ t, (Φ t).IsInvertible) (hS : Continuous S) :
    Continuous (trivializedCoeff Φ S) := by
  have hderiv : Continuous (deriv Φ) := contDiff_zero.1 (contDiff_succ_iff_deriv.1 hΦ).2.2
  have hinverse : Continuous fun t ↦ (Φ t).inverse := continuous_iff_continuousAt.2 fun t ↦
    ((hinv t).contDiffAt_map_inverse (n := 0)).continuousAt.comp hΦ.continuous.continuousAt
  exact hinverse.clm_comp ((hS.clm_comp hΦ.continuous).sub hderiv)

/-- Periodicity of `Φ` and `S` passes to `trivializedCoeff Φ S`. -/
theorem periodic_trivializedCoeff {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V} {T : ℝ}
    (hΦ : Periodic Φ T) (hS : Periodic S T) : Periodic (trivializedCoeff Φ S) T := fun t ↦ by
  simp only [trivializedCoeff_def, hΦ t, hS t, hΦ.deriv t]

/-- **Perturbation compatibility:** subtracting `δ • K_t` from `S_t`, where `K_t` intertwines with
`K₀` through an invertible frame value `Φ t`, subtracts `δ • K₀` from `trivializedCoeff Φ S t`. -/
theorem trivializedCoeff_sub_smul {Φ : ℝ → F →L[ℝ] V} {S K : ℝ → V →L[ℝ] V} {K₀ : F →L[ℝ] F}
    {t : ℝ} (hΦ : (Φ t).IsInvertible) (hK : ∀ v, K t (Φ t v) = Φ t (K₀ v)) (δ : ℝ) :
    trivializedCoeff Φ (fun r ↦ S r - δ • K r) t = trivializedCoeff Φ S t - δ • K₀ := by
  ext v
  simp only [trivializedCoeff_apply, sub_apply, smul_apply, hK, sub_right_comm _ (δ • Φ t (K₀ v)),
    map_sub, map_smul, hΦ.inverse_apply_self]

end TauCeti
