/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Dimension and homothety checks for relative volume density

The relative density of any two metrics is one in dimension zero. Multiplying a metric by
the square of a positive constant multiplies its density by that constant to the dimension.
The associated homothety polynomial has the expected first two derivatives at the identity.
-/

public noncomputable section

open Bundle Manifold
open scoped ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n n' : ℕ∞ω}

/-- In dimension zero, every relative volume density is one. -/
theorem relativeVolumeDensity_finrank_zero
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (hE : Module.finrank ℝ E = 0) (x : M) : relativeVolumeDensity g g' x = 1 := by
  have hdim : Module.finrank ℝ (TangentSpace I x) = 0 := hE
  rw [(Module.finBasis ℝ (TangentSpace I x)).relativeVolumeDensity_eq_sqrt_div]
  simp [hdim]

/-- Both parameter derivatives of relative density vanish in dimension zero, for any family
of metrics. -/
theorem deriv_relativeVolumeDensity_finrank_zero
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (G : ℝ → ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (hE : Module.finrank ℝ E = 0) (x : M) (t : ℝ) :
    deriv (fun s ↦ relativeVolumeDensity g (G s) x) t = 0 ∧
      deriv (deriv (fun s ↦ relativeVolumeDensity g (G s) x)) t = 0 := by
  have h : (fun s ↦ relativeVolumeDensity g (G s) x) = fun _ ↦ 1 := by
    funext s
    exact relativeVolumeDensity_finrank_zero g (G s) hE x
  rw [h]
  simp

/-- Rescaling a metric by `c²` multiplies its volume density by `c^dim` for `c > 0`. -/
theorem relativeVolumeDensity_homothety
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x : M) :
    relativeVolumeDensity g
      (g.rescale (fun _ : M ↦ c ^ 2) contMDiff_const (fun _ ↦ pow_pos hc 2)) x =
      c ^ Module.finrank ℝ E := by
  rw [relativeVolumeDensity_rescale]
  rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le,
    ← Real.rpow_natCast c (Module.finrank ℝ E)]
  congr 1
  ring

/-- Along positive homothety factors `1+t`, the relative density is the dimension-th
power of `1+t`. -/
theorem relativeVolumeDensity_homothety_parameter
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {t : ℝ} (ht : -1 < t) (x : M) :
    relativeVolumeDensity g
      (g.rescale (fun _ : M ↦ (1 + t) ^ 2) contMDiff_const
        (fun _ ↦ pow_pos (by linarith : 0 < 1 + t) 2)) x =
      (1 + t) ^ Module.finrank ℝ E :=
  relativeVolumeDensity_homothety g (by linarith) x

/-- The first derivative of the homothety density at the identity is the dimension. -/
theorem hasDerivAt_homothetyDensity_zero (m : ℕ) :
    HasDerivAt (fun t : ℝ ↦ (1 + t) ^ m) m 0 := by
  convert (((hasDerivAt_id (0 : ℝ)).const_add 1).pow m) using 1
  · funext t
    rfl
  · simp

/-- The second derivative of the homothety density at the identity is `m(m-1)`. -/
theorem deriv_deriv_homothetyDensity_zero (m : ℕ) :
    deriv (deriv (fun t : ℝ ↦ (1 + t) ^ m)) 0 = (m : ℝ) * ((m : ℝ) - 1) := by
  cases m with
  | zero => simp
  | succ k =>
      have hderiv : deriv (fun t : ℝ ↦ (1 + t) ^ (k + 1)) =
          fun t ↦ (k + 1 : ℝ) * (1 + t) ^ k := by
        funext t
        convert (((hasDerivAt_id t).const_add 1).pow (k + 1)).deriv using 1
        · congr 1
        · simp
      rw [hderiv]
      convert (((((hasDerivAt_id (0 : ℝ)).const_add 1).pow k).const_mul
        (k + 1 : ℝ)).deriv) using 1 <;> simp [Nat.cast_add]

end Bundle.ContMDiffRiemannianMetric
