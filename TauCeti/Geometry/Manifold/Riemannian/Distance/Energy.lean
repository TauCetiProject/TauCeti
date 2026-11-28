/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.ArcLength
public import TauCeti.Geometry.Manifold.Riemannian.Distance
import TauCeti.Topology.MetricSpace.Holder

/-!
# Distance controlled by curve energy

The distance between the endpoints of a `C¹` curve is at most the square root of twice its
energy times the length of the parameter interval. This combines the distance–length comparison
with the Cauchy–Schwarz bound for length and energy, and applies on every compact interval
contained in the curve's smoothness domain. A continuous curve on a closed interval which is
`C¹` only in its interior also has a square-root modulus controlled by its total kinetic energy.

## Main results

* `TauCeti.IsRiemannianManifold.dist_le_sqrt_two_mul_energy`: the endpoint distance is bounded
  by `√(2 * (b - a) * energy I γ a b)` when `a ≤ b`.
* `TauCeti.IsRiemannianManifold.dist_le_sqrt_mul_sqrt_abs_sub_of_two_mul_energy_le`: a
  square-root modulus on the closed interval for curves continuous there and `C¹` in its interior.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §12.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Bundle Filter MeasureTheory Set
open scoped Manifold

namespace TauCeti.IsRiemannianManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- The endpoint distance of a `C¹` curve is at most the square root of twice its energy
times the length of the parameter interval. -/
theorem dist_le_sqrt_two_mul_energy {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ s) :
    dist (γ a) (γ b) ≤ Real.sqrt (2 * (b - a) * Manifold.energy I γ a b) := by
  apply (edist_le_ofReal (Real.sqrt_nonneg _)).mp
  exact (edist_le_pathELength (hγ.mono hsub) hab).trans
    (hγ.pathELength_le_ofReal_sqrt_energy hsub)

/-- Finite kinetic energy controls every increment of a continuous curve which is `C¹` only in
its open parameter interval. Endpoint derivatives are unnecessary. -/
theorem dist_le_sqrt_mul_sqrt_abs_sub_of_two_mul_energy_le {γ : ℝ → M} {a b C : ℝ}
    (hγ : ContinuousOn γ (Icc a b))
    (hreg : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Ioo a b))
    (hE : IntervalIntegrable (fun r ↦ ‖Manifold.curveVelocity I γ r‖ ^ 2) volume a b)
    (hbound : 2 * Manifold.energy I γ a b ≤ C) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      dist (γ s) (γ t) ≤ Real.sqrt C * Real.sqrt |t - s| := by
  by_cases hab : a < b
  swap
  · intro s hs t ht
    have : s = t := by grind
    simp [this]
  have hordered (s t : ℝ) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (hst : s ≤ t) :
      dist (γ s) (γ t) ≤ Real.sqrt C * Real.sqrt (t - s) := by
    have hsub : Icc s t ⊆ Ioo a b := Icc_subset_Ioo hs.1 ht.2
    have hpart := (mul_le_mul_of_nonneg_left
      (Manifold.energy_mono_interval (I := I) γ hs.1.le hst ht.2.le hE)
      (by norm_num : (0 : ℝ) ≤ 2)).trans hbound
    calc
      dist (γ s) (γ t) ≤ Real.sqrt (2 * (t - s) * Manifold.energy I γ s t) :=
        dist_le_sqrt_two_mul_energy (hreg.mono hsub) hst (Subset.refl _)
      _ ≤ Real.sqrt ((t - s) * C) := Real.sqrt_le_sqrt (by nlinarith [sub_nonneg.mpr hst])
      _ = Real.sqrt C * Real.sqrt (t - s) := by
        rw [Real.sqrt_mul (sub_nonneg.mpr hst), mul_comm]
  have hopen (s : ℝ) (hs : s ∈ Ioo a b) (t : ℝ) (ht : t ∈ Ioo a b) :
      dist (γ s) (γ t) ≤ Real.sqrt C * Real.sqrt |t - s| := by
    rcases le_total s t with hst | hts
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hordered s t hs ht hst
    · simpa only [dist_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)] using
        hordered t s ht hs hts
  let K : NNReal := ⟨Real.sqrt C, Real.sqrt_nonneg C⟩
  have hK : (K : ℝ) = Real.sqrt C := (rfl)
  have hhalf : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
  have hholder : HolderOnWith K (1 / 2) γ (Ioo a b) :=
    HolderOnWith.of_dist_le fun s hs t ht ↦ by
      simpa only [hK, hhalf, ← Real.sqrt_eq_rpow, Real.dist_eq, abs_sub_comm] using hopen s hs t ht
  have hclosed : HolderOnWith K (1 / 2) γ (Icc a b) :=
    hholder.of_subset_closure (by rw [closure_Ioo hab.ne])
      (fun s hs ↦ (hγ s hs).mono Ioo_subset_Icc_self)
  intro s hs t ht
  simpa only [hK, hhalf, ← Real.sqrt_eq_rpow, Real.dist_eq, abs_sub_comm] using
    hclosed.dist_le hs ht

end TauCeti.IsRiemannianManifold
