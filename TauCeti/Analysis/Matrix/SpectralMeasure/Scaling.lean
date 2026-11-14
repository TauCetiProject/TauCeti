/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map

/-!
# Scaling spectral measures and their weak limits

Multiplying a Hermitian matrix by a real scalar pushes its spectral measure forward by the
same multiplication. Consequently rescaling a matrix family by scalars tending to one
preserves its weak spectral limits in both directions. No bound on the matrix norms or
moments is required, and finitely many zero rescaling factors cause no difficulty.

These statements allow variance normalizations to be removed in global spectral laws.

## References

* Z. Bai, J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices* (2010),
  §3.3 (standardization of sample covariance entries).
-/

public section

open MeasureTheory Filter Topology TauCeti.Probability
open scoped ComplexOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [Nonempty n]

/-- Scaling a Hermitian matrix scales its empirical spectral measure, including for negative
and zero scalars. -/
theorem map_spectralMeasure_mul (A : Matrix n n 𝕜) (hA : A.IsHermitian) (c : ℝ) :
    (A.spectralMeasure hA).map (fun x ↦ c * x) =
      (c • A).spectralMeasure (hA.smul (IsSelfAdjoint.all c)) := by
  let d : n → ℝ := fun i ↦ c * hA.eigenvalues i
  have hd : (diagonal (fun i ↦ (d i : 𝕜))).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hdiag : c • A =
      Unitary.conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
        (diagonal (fun i ↦ (d i : 𝕜))) := by
    have heq : diagonal (fun i ↦ (d i : 𝕜)) =
        (c : 𝕜) • diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
      simp [d, ← diagonal_smul, Pi.smul_def, Function.comp_def]
    rw [heq, map_smul, ← hA.spectral_theorem, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  have hchar : (c • A).charpoly = (diagonal (fun i ↦ (d i : 𝕜))).charpoly := by
    rw [hdiag, Unitary.conjStarAlgAut_apply, charpoly_mul_comm, ← Matrix.mul_assoc]
    simp
  rw [spectralMeasure_eq_of_charpoly_eq (hA.smul (IsSelfAdjoint.all c)) hd hchar,
    spectralMeasure_diagonal, spectralMeasure_def,
    map_empiricalMeasureOfFintype (by fun_prop)]
  rfl

variable {ι : Type*} {m : ι → Type*} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)] {l : Filter ι}

/-- Scalars tending to one preserve weak spectral limits in both directions. The scalars
may vanish away from an eventual set, and no matrix moment bounds are needed. -/
theorem tendsto_spectralMeasure_smul_iff (A : (i : ι) → Matrix (m i) (m i) 𝕜)
    (hA : ∀ i, (A i).IsHermitian) {c : ι → ℝ} (hc : Tendsto c l (𝓝 1))
    {μ : ProbabilityMeasure ℝ} :
    Tendsto (fun i ↦ (c i • A i).spectralMeasure ((hA i).smul (IsSelfAdjoint.all _))) l (𝓝 μ) ↔
      Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ) := by
  have hcont := ProbabilityMeasure.continuous_map_of_continuous_uncurry
    (f := fun c x : ℝ ↦ c * x) (by fun_prop)
  have hid : μ.map (fun x ↦ x) = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    simp [ProbabilityMeasure.toMeasure_map]
  constructor
  · intro h
    have hi : Tendsto (fun i ↦ (c i)⁻¹) l (𝓝 1) := by
      simpa using hc.inv₀ one_ne_zero
    have ht := (hcont.tendsto (1, μ)).comp (hi.prodMk_nhds h)
    have hne : ∀ᶠ i in l, c i ≠ 0 := hc.eventually_ne one_ne_zero
    simp only [Function.comp_def, one_mul, hid] at ht
    exact ht.congr' (hne.mono fun i hi ↦ by
      rw [map_spectralMeasure_mul]
      simp [smul_smul, hi])
  · intro h
    have ht := (hcont.tendsto (1, μ)).comp (hc.prodMk_nhds h)
    simpa only [Function.comp_def, one_mul, hid, map_spectralMeasure_mul] using ht

end Matrix
