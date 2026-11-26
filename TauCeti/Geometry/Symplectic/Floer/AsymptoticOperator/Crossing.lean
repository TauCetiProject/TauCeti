/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DysonSeries.Parameter
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator

/-!
# Crossing forms of families of asymptotic operators and of their return maps

Let `(V, ω)` be a finite-dimensional symplectic vector space and `S μ r` a family of linearized
Hamiltonian fields depending on a real parameter `μ`, with `S μ r` infinitesimally symplectic,
`ω(S v, w) + ω(v, S w) = 0`. For each `μ` let `Ψ_μ = TauCeti.dysonSeriesLeft (S μ)` be the
propagator of `ζ' = S μ r ζ`, a path of symplectic maps, and `A_μ ζ = J_r (ζ' - S μ r ζ)` the
asymptotic operator (`TauCeti.Floer.asymptoticOperator`). A loop `ζ` lies in the kernel of `A_μ`
exactly when `ζ r = Ψ_μ(r) v` with `v = ζ 0`, and it closes up at time `t` exactly when
`Ψ_μ(t) v = v` (`TauCeti.Floer.exists_ne_zero_asymptoticOperator_eq_zero_iff_det_eq_zero`).

As `μ` varies, two families can cross the degenerate locus: the self-adjoint operators `A_μ`,
whose crossings are governed by the crossing form `ζ ↦ ∫ g_r(ζ, ∂_μ A_μ ζ) dr` on their kernel,
with `g_r = ω(·, J_r ·)`, and the path of symplectic return maps `μ ↦ Ψ_μ(t)`, whose crossings are
governed by the crossing form `v ↦ ω(v, ∂_μ Ψ_μ(t) v)` on the fixed vectors of `Ψ_μ(t)`. The
first enters the spectral flow of `A_μ`, the second the Conley–Zehnder index of the return maps.
This file proves that the two forms agree under `ζ = Ψ_μ(·) v`:

* **The return map.** For `Ψ_μ(t) v = v`,
  `ω(v, ∂_μ Ψ_μ(t) v) = ∫₀ᵗ ω(Ψ_μ(r) v, ∂_μ S μ r (Ψ_μ(r) v)) dr`
  (`TauCeti.Floer.apply_deriv_dysonSeriesLeft_apply_eq_integral`). By
  `TauCeti.hasDerivAt_dysonSeriesLeft_parameter`, `∂_μ Ψ_μ(t) = Ψ_μ(t) ∫₀ᵗ Ψ_μ(r)⁻¹ ∂_μ S Ψ_μ(r)`,
  and since `Ψ_μ(t)` and `Ψ_μ(r)` preserve `ω` and `Ψ_μ(t) v = v`, the outer `Ψ_μ(t)` and the
  inverse `Ψ_μ(r)⁻¹` move to the first slot of `ω`
  (`TauCeti.apply_dysonSeries_neg_apply`).
* **The operators.** The parameter derivative of the asymptotic operator is
  `∂_μ A_μ ζ = -J_r ∂_μ S ζ` (`TauCeti.Floer.hasDerivAt_asymptoticOperator_parameter`), and
  `g_r(ζ, -J_r w) = ω(ζ, w)` since `J_r² = -1`. Hence the crossing form of the operators at the
  kernel element `ζ = Ψ_μ(·) v` is the crossing form of the return maps at `v`
  (`TauCeti.Floer.apply_deriv_dysonSeriesLeft_apply_eq_integral_associatedBilinForm`). No
  compatibility, continuity or periodicity of `J` is needed for this identity; for a one-periodic
  family `S μ` and `t = 1`, the loop `ζ` is one-periodic.
* **Weights.** For the weighted fields `S r - δ J_r`, whose asymptotic operators are `A - δ`
  (`TauCeti.Floer.asymptoticOperator_sub_smul`), the crossing form of the return maps is
  `ω(v, ∂_δ Ψ_δ(t) v) = -∫₀ᵗ ω(ζ r, J_r ζ r) dr`
  (`TauCeti.Floer.apply_deriv_dysonSeriesLeft_sub_smul_apply_eq_neg_integral`). For compatible
  `J` and `t > 0` it is negative definite
  (`TauCeti.Floer.apply_deriv_dysonSeriesLeft_sub_smul_apply_neg`): every weight at which a
  fixed vector appears is a regular crossing of the return maps, just as `δ ↦ A - δ` crosses each
  eigenvalue of `A` regularly, with crossing form `-∫ g(ζ, ζ)`.

The sign conventions are those of the forms: the Conley–Zehnder crossing form of
`TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Crossing` and the spectral crossing form of
`TauCeti.Analysis.Fredholm.Spectral.RegularCrossings` are read off from them after fixing the
standard symplectic form in coordinates.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  27 (1995), 1–33, Section 4 (the crossing forms of the operators `∂_t - S` and of their
  fundamental solutions).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

open Function Set intervalIntegral

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V}

/-- **The crossing form of a family of return maps.** Let `S μ r` be jointly continuous with a
jointly continuous parameter derivative `S' μ r`, and let `S μ r` be infinitesimally symplectic
at the parameter `μ`. If `v` is a fixed vector of the propagator `Ψ_μ(t)` of `ζ' = S μ r ζ`, then
`ω(v, ∂_μ Ψ_μ(t) v) = ∫₀ᵗ ω(Ψ_μ(r) v, S' μ r (Ψ_μ(r) v)) dr`. -/
theorem apply_deriv_dysonSeriesLeft_apply_eq_integral {S S' : ℝ → ℝ → V →L[ℝ] V}
    (hS : Continuous (uncurry S)) (hS' : Continuous (uncurry S'))
    (hd : ∀ μ r, HasDerivAt (fun μ ↦ S μ r) (S' μ r) μ) {μ t : ℝ}
    (hskew : ∀ r u w, ω (S μ r u) w + ω u (S μ r w) = 0) {v : V}
    (hv : dysonSeriesLeft (S μ) t v = v) :
    ω v (deriv (fun ν ↦ dysonSeriesLeft (S ν) t) μ v) =
      ∫ r in 0..t, ω (dysonSeriesLeft (S μ) r v) (S' μ r (dysonSeriesLeft (S μ) r v)) := by
  have hSμ : Continuous (S μ) := hS.comp (Continuous.prodMk_right μ)
  set B := ω.toBilinForm.toContinuousBilinearMap
  have hB (u w : V) : B u w = ω u w := LinearMap.toContinuousBilinearMap_apply _ _ _
  have hskew' (r : ℝ) (u w : V) : B (S μ r u) w + B u (S μ r w) = 0 := by
    simpa only [hB] using hskew r u w
  have hc : Continuous fun r ↦ dysonSeries (-S μ) r * S' μ r * dysonSeriesLeft (S μ) r :=
    ((continuous_dysonSeries hSμ.neg).mul (hS'.comp (Continuous.prodMk_right μ))).mul
      (continuous_dysonSeriesLeft hSμ)
  -- Move the outer `Ψ_μ(t)` and the inverses `Ψ_μ(r)⁻¹` into the first slot of `ω`.
  have hrhs : (∫ r in 0..t, ω (dysonSeriesLeft (S μ) r v) (S' μ r (dysonSeriesLeft (S μ) r v))) =
      ∫ r in 0..t, B v ((dysonSeries (-S μ) r * S' μ r * dysonSeriesLeft (S μ) r) v) :=
    integral_congr fun r _ ↦ by
      simp only [mul_apply_eq_comp, apply_dysonSeries_neg_apply hSμ B hskew', hB]
  calc ω v (deriv (fun ν ↦ dysonSeriesLeft (S ν) t) μ v)
      = B (dysonSeriesLeft (S μ) t v) (dysonSeriesLeft (S μ) t
          ((∫ r in 0..t, dysonSeries (-S μ) r * S' μ r * dysonSeriesLeft (S μ) r) v)) := by
        rw [hB, hv, (hasDerivAt_dysonSeriesLeft_parameter hS hS' hd μ t).deriv, mul_apply_eq_comp]
    _ = _ := by
      rw [apply_dysonSeriesLeft_apply_dysonSeriesLeft hSμ B hskew', hrhs,
        ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 t),
        (B v).intervalIntegral_comp_comm ((hc.clm_apply continuous_const).intervalIntegrable 0 t)]

/-- **The parameter derivative of the asymptotic operator.** If `ν ↦ S ν t` has the derivative
`S'` at `μ`, then at a fixed loop `ζ` the asymptotic operators `A_ν ζ (t)` of `S ν` have the
derivative `-J_t (S' (ζ t))` at `μ`. -/
theorem hasDerivAt_asymptoticOperator_parameter {J : ℝ → AlmostComplexStructure V}
    {S : ℝ → ℝ → V →L[ℝ] V} {S' : V →L[ℝ] V} {ζ : ℝ → V} {μ t : ℝ}
    (hd : HasDerivAt (fun ν ↦ S ν t) S' μ) :
    HasDerivAt (fun ν ↦ asymptoticOperator J (S ν) ζ t) (-J t (S' (ζ t))) μ := by
  have h : HasDerivAt (fun ν ↦ deriv ζ t - S ν t (ζ t)) (-S' (ζ t)) μ := by
    simpa using (hd.clm_apply (hasDerivAt_const μ (ζ t))).const_sub (deriv ζ t)
  have hJ := (LinearMap.toContinuousLinearMap (J t).toLinearMap).hasFDerivAt.comp_hasDerivAt μ h
  rw [funext fun ν ↦ asymptoticOperator_def J (S ν) ζ t]
  simpa only [comp_def, LinearMap.coe_toContinuousLinearMap', map_neg] using hJ

/-- **The crossing forms of the asymptotic operators and of their return maps agree.** Under the
hypotheses of `TauCeti.Floer.apply_deriv_dysonSeriesLeft_apply_eq_integral`, for every family
`J` of almost complex structures, the crossing form `ω(v, ∂_μ Ψ_μ(t) v)` of the return maps at a
fixed vector `v` of `Ψ_μ(t)` is the crossing form `∫₀ᵗ g_r(ζ, ∂_μ A_μ ζ) dr` of the asymptotic
operators `A_μ` at the kernel element `ζ = Ψ_μ(·) v`, with `g_r = ω(·, J_r ·)`. -/
theorem apply_deriv_dysonSeriesLeft_apply_eq_integral_associatedBilinForm
    (J : ℝ → AlmostComplexStructure V) {S S' : ℝ → ℝ → V →L[ℝ] V}
    (hS : Continuous (uncurry S)) (hS' : Continuous (uncurry S'))
    (hd : ∀ μ r, HasDerivAt (fun μ ↦ S μ r) (S' μ r) μ) {μ t : ℝ}
    (hskew : ∀ r u w, ω (S μ r u) w + ω u (S μ r w) = 0) {v : V}
    (hv : dysonSeriesLeft (S μ) t v = v) :
    ω v (deriv (fun ν ↦ dysonSeriesLeft (S ν) t) μ v) =
      ∫ r in 0..t, ω.associatedBilinForm (J r) (dysonSeriesLeft (S μ) r v)
        (deriv (fun ν ↦ asymptoticOperator J (S ν) (fun r ↦ dysonSeriesLeft (S μ) r v) r) μ) := by
  rw [apply_deriv_dysonSeriesLeft_apply_eq_integral hS hS' hd hskew hv]
  refine integral_congr fun r _ ↦ ?_
  rw [(hasDerivAt_asymptoticOperator_parameter (hd μ r)).deriv,
    SymplecticForm.associatedBilinForm_apply, map_neg, AlmostComplexStructure.apply_apply, neg_neg]

section Weight

variable {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V}

/-- **The crossing form of the weighted return maps.** For continuous families `S` and `J`, with
`S r` infinitesimally symplectic and `J r` preserving `ω`, let `Ψ_δ` be the propagator of
`ζ' = (S r - δ J_r) ζ`, the field of the weighted asymptotic operator `A - δ`. If `v` is a fixed
vector of `Ψ_δ(t)`, then `ω(v, ∂_δ Ψ_δ(t) v) = -∫₀ᵗ ω(ζ r, J_r ζ r) dr` with `ζ r = Ψ_δ(r) v`. -/
theorem apply_deriv_dysonSeriesLeft_sub_smul_apply_eq_neg_integral (hSc : Continuous S)
    (hJc : Continuous J) (hJ : ∀ r, ω.Invariant (J r))
    (hskew : ∀ r u w, ω (S r u) w + ω u (S r w) = 0) {δ t : ℝ} {v : V}
    (hv : dysonSeriesLeft (fun r ↦ S r - δ • LinearMap.toContinuousLinearMap (J r).toLinearMap)
      t v = v) :
    ω v (deriv (fun ε ↦ dysonSeriesLeft
        (fun r ↦ S r - ε • LinearMap.toContinuousLinearMap (J r).toLinearMap) t) δ v) =
      -∫ r in 0..t, ω (dysonSeriesLeft
          (fun r ↦ S r - δ • LinearMap.toContinuousLinearMap (J r).toLinearMap) r v)
        (J r (dysonSeriesLeft
          (fun r ↦ S r - δ • LinearMap.toContinuousLinearMap (J r).toLinearMap) r v)) := by
  set Jc : ℝ → V →L[ℝ] V := fun r ↦ LinearMap.toContinuousLinearMap (J r).toLinearMap
  have hJc' : Continuous Jc := AlmostComplexStructure.continuous_iff.1 hJc
  have hd (ε r : ℝ) : HasDerivAt (fun ε ↦ S r - ε • Jc r) (-Jc r) ε := by
    simpa using ((hasDerivAt_id ε).smul_const (Jc r)).const_sub (S r)
  rw [apply_deriv_dysonSeriesLeft_apply_eq_integral (S' := fun _ r ↦ -Jc r)
    ((hSc.comp continuous_snd).sub (continuous_fst.smul (hJc'.comp continuous_snd)))
    (hJc'.comp continuous_snd).neg hd
    (fun r ↦ sub_smul_apply_add_apply_eq_zero (hJ r) (hskew r) δ) hv, ← integral_neg]
  simp [Jc]

/-- **Weight crossings of the return maps are negative definite.** For continuous families `S`
and `J`, with `S r` infinitesimally symplectic and `J r` compatible with `ω`, and for `t > 0`,
the crossing form of the weighted return maps `δ ↦ Ψ_δ(t)` is negative at every nonzero fixed
vector `v` of `Ψ_δ(t)`: `ω(v, ∂_δ Ψ_δ(t) v) < 0`. -/
theorem apply_deriv_dysonSeriesLeft_sub_smul_apply_neg (hSc : Continuous S)
    (hJc : Continuous J) (hJ : ∀ r, ω.Compatible (J r))
    (hskew : ∀ r u w, ω (S r u) w + ω u (S r w) = 0) {δ t : ℝ} (ht : 0 < t) {v : V}
    (hv₀ : v ≠ 0)
    (hv : dysonSeriesLeft (fun r ↦ S r - δ • LinearMap.toContinuousLinearMap (J r).toLinearMap)
      t v = v) :
    ω v (deriv (fun ε ↦ dysonSeriesLeft
        (fun r ↦ S r - ε • LinearMap.toContinuousLinearMap (J r).toLinearMap) t) δ v) < 0 := by
  set M : ℝ → V →L[ℝ] V := fun r ↦ S r - δ • LinearMap.toContinuousLinearMap (J r).toLinearMap
  have hJc' := AlmostComplexStructure.continuous_iff.1 hJc
  have hM : Continuous M := hSc.sub (hJc'.const_smul δ)
  have hζ : Continuous fun r ↦ dysonSeriesLeft M r v :=
    (continuous_dysonSeriesLeft hM).clm_apply continuous_const
  rw [apply_deriv_dysonSeriesLeft_sub_smul_apply_eq_neg_integral hSc hJc (fun r ↦ (hJ r).invariant)
    hskew hv, neg_lt_zero]
  refine intervalIntegral_pos_of_pos_on ?_ (fun r _ ↦ (hJ r).associated_pos fun h ↦ hv₀ ?_) ht
  · have hc := (ω.toBilinForm.toContinuousBilinearMap.continuous.comp hζ).clm_apply
      (hJc'.clm_apply hζ)
    simpa only [comp_apply, LinearMap.toContinuousBilinearMap_apply,
      LinearMap.coe_toContinuousLinearMap'] using hc.intervalIntegrable 0 t
  · -- The propagator is invertible, so it does not send `v ≠ 0` to `0`.
    rw [← one_apply_eq_self (F := V →L[ℝ] V) v, ← dysonSeries_neg_mul_dysonSeriesLeft hM r,
      mul_apply_eq_comp, h, map_zero]

end Weight

end Floer

end TauCeti
