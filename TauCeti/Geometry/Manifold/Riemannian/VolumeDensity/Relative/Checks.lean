/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Checks for the relative volume density of a family of metrics

The relative density `J_t` of a family of metrics `g_t` with respect to a fixed metric `g` is
tested on three families, through the first two parameter derivatives at `t = 0`:

* the constant family `g_t = g`: `J_t = 1`, and both derivatives vanish;
* the homothety family `g_t = (1 + t)² g`, `|t| < 1`, the metrics induced by the Euclidean
  homotheties `F_t = (1 + t) f` of an immersion `f`, in dimension `m`: `J_t = (1 + t)^m`,
  `J'_0 = m` and `J''_0 = m (m - 1)`. The Gram determinant ratio without its square root is
  `(1 + t)^(2m)`, whose first derivative `2m` is twice `J'_0`;
* dimension zero: the relative density of any two metrics is one, so both parameter derivatives
  vanish for every family of metrics.
-/

public noncomputable section

open Bundle Manifold Filter Set Topology
open scoped ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n n' : ℕ∞ω}

/- Both parameter derivatives of relative density vanish in dimension zero, for any family
of metrics. -/
example
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (G : ℝ → ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (hE : Module.finrank ℝ E = 0) (x : M) (t : ℝ) :
    deriv (fun s ↦ relativeVolumeDensity g (G s) x) t = 0 ∧
      deriv (deriv (fun s ↦ relativeVolumeDensity g (G s) x)) t = 0 := by
  simp [hE]

/- For the constant family `g_t = g`, the relative density is `1` and both parameter derivatives
vanish. -/
example
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (G : ℝ → ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (hG : ∀ t x, (G t).inner x = g.inner x) (x : M) :
    (∀ t, relativeVolumeDensity g (G t) x = 1) ∧
      deriv (fun t ↦ relativeVolumeDensity g (G t) x) 0 = 0 ∧
      deriv (deriv fun t ↦ relativeVolumeDensity g (G t) x) 0 = 0 := by
  have h : ∀ t, relativeVolumeDensity g (G t) x = 1 := fun t ↦ by
    rw [relativeVolumeDensity_congr g (G t) (g₁ := g) (g₂ := g) rfl (hG t x),
      relativeVolumeDensity_self]
  simp [h]

/- For the homothety family `g_t = (1 + t)² g`, `|t| < 1`, in dimension `m`: `J_t = (1 + t)^m`,
`J'_0 = m` and `J''_0 = m (m - 1)`, while the Gram determinant ratio, without the square root, has
first derivative `2m`. -/
example
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (G : ℝ → ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (hG : ∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x, (G t).inner x = (1 + t) ^ 2 • g.inner x) (x : M) :
    (∀ t ∈ Ioo (-1 : ℝ) 1, relativeVolumeDensity g (G t) x = (1 + t) ^ Module.finrank ℝ E) ∧
      deriv (fun t ↦ relativeVolumeDensity g (G t) x) 0 = Module.finrank ℝ E ∧
      deriv (deriv fun t ↦ relativeVolumeDensity g (G t) x) 0 =
        Module.finrank ℝ E * (Module.finrank ℝ E - 1 : ℝ) ∧
      deriv (fun t ↦ (g.inner x).toBilinForm.detRatio ((G t).inner x).toBilinForm) 0 =
        2 * Module.finrank ℝ E := by
  set m := Module.finrank ℝ E
  have hJ : ∀ t ∈ Ioo (-1 : ℝ) 1, relativeVolumeDensity g (G t) x = (1 + t) ^ m :=
    fun t ht ↦ relativeVolumeDensity_eq_pow_of_inner_eq_sq_smul g (G t)
      (by linarith [ht.1]) (hG t ht x)
  have hnhds : Ioo (-1 : ℝ) 1 ∈ 𝓝 0 := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hev : (fun t ↦ relativeVolumeDensity g (G t) x) =ᶠ[𝓝 0] fun t ↦ (1 + t) ^ m :=
    eventually_of_mem hnhds hJ
  -- The derivatives of `t ↦ (1 + t)^k`.
  have hpow : ∀ k : ℕ, deriv (fun t : ℝ ↦ (1 + t) ^ k) = fun t ↦ (k : ℝ) * (1 + t) ^ (k - 1) := by
    intro k
    funext t
    simpa using (((hasDerivAt_id' t).const_add 1).fun_pow k).deriv
  refine ⟨hJ, ?_, ?_, ?_⟩
  · rw [hev.deriv_eq, hpow]
    simp
  · rw [hev.deriv.deriv_eq, hpow, deriv_const_mul_field', hpow]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · simp [Nat.cast_sub hm]
  · have hdet : (fun t ↦ (g.inner x).toBilinForm.detRatio ((G t).inner x).toBilinForm) =ᶠ[𝓝 0]
        fun t ↦ (1 + t) ^ (2 * m) := by
      filter_upwards [hnhds] with t ht
      rw [← relativeVolumeDensity_sq, hJ t ht, ← pow_mul, mul_comm]
    rw [hdet.deriv_eq, hpow]
    simp

end Bundle.ContMDiffRiemannianMetric
