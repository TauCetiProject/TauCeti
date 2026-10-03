/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.AEEqFun.Basic
import TauCeti.Combinatorics.DenseGraphLimits.Kernel.Pullback

/-!
# The cut distance to a constant graphon

The cut distance is an infimum over couplings, and in general no single coupling attains it. Against
a **constant** graphon the infimum is trivial: the overlaid difference only reads the other graphon
through its own coordinate, so every coupling contributes the same value, and

`δ□(U, p) = ‖U - p‖□`,

the cut norm of `U - p` on the carrier of `U`, whatever the carrier of the constant graphon is
(`cutDist_const_right`). In particular two constant graphons are at cut distance `|p - q|`
(`cutDist_const_const`).

A graphon on a **point mass** `(Ω, δ_b)` is almost everywhere the constant graphon at its value at
`(b, b)` (`Graphon.ae_eq_const_of_dirac`), so the same formula computes the cut distance to it
(`cutDist_dirac_right`), and two point-mass graphons are at cut distance `|U a a - W b b|`
(`cutDist_dirac_dirac`).

These are the cases where the cut distance can be evaluated exactly on atomic carriers, which makes
them the reference values for checking any other description of the cut distance there.

## Main results

* `cutDist_const_right`, `cutDist_const_left` — the cut distance to a constant graphon on an
  arbitrary probability carrier is the cut norm of the difference with that constant;
* `cutDist_const_const` — two constant graphons are at cut distance `|p - q|`;
* `cutDist_dirac_right`, `cutDist_dirac_left`, `cutDist_dirac_dirac` — the corresponding values
  for graphons on point masses.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §8.2.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), §6.
-/

public section

noncomputable section

open MeasureTheory TauCeti.MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- **The cut distance to a constant graphon is a cut norm.** For a graphon `U` on `(Ω₁, μ₁)` and
the constant graphon `p` on an arbitrary probability carrier `(Ω₂, μ₂)`,
`δ□(U, p) = ‖U - p‖□`, the cut norm being taken on `(Ω₁, μ₁)`.

No coupling does better than another here: along any coupling the overlaid difference is the
pullback of `U - p` along the first coordinate, so every coupling contributes this same value. -/
theorem cutDist_const_right (U : Graphon Ω₁ μ₁) (p : I) :
    cutDist U (Graphon.const μ₂ p) =
      cutNorm μ₁ (U.toSymmKernel - (Graphon.const μ₁ p).toSymmKernel) := by
  have hval (π : Measure (Ω₁ × Ω₂)) (hπ : IsCoupling μ₁ μ₂ π) :
      @cutNorm _ _ π hπ.isFiniteMeasure (overlayDiff U (Graphon.const μ₂ p) π) =
        cutNorm μ₁ (U.toSymmKernel - (Graphon.const μ₁ p).toSymmKernel) := by
    let _ := hπ.isFiniteMeasure
    have hdiff : overlayDiff U (Graphon.const μ₂ p) π =
        (U.toSymmKernel - (Graphon.const μ₁ p).toSymmKernel).comap Prod.fst
          hπ.measurePreserving_fst.measurable π := by
      ext x y
      simp
    rw [hdiff, cutNorm_comap hπ.measurePreserving_fst]
  have hprod := isCoupling_prod μ₁ μ₂
  exact le_antisymm ((cutDist_le U _ hprod).trans_eq (hval _ hprod))
    (le_cutDist U _ fun π hπ => (hval π hπ).ge)

/-- **The cut distance from a constant graphon is a cut norm**: `δ□(p, W) = ‖p - W‖□`, the cut
norm being taken on the carrier of `W`, for an arbitrary probability carrier of the constant
graphon. This is `cutDist_const_right` by symmetry. -/
theorem cutDist_const_left (p : I) (W : Graphon Ω₂ μ₂) :
    cutDist (Graphon.const μ₁ p) W =
      cutNorm μ₂ ((Graphon.const μ₂ p).toSymmKernel - W.toSymmKernel) := by
  rw [cutDist_comm, cutDist_const_right, cutNorm_sub_rev]

/-- **Two constant graphons are at cut distance `|p - q|`**, on arbitrary probability carriers. -/
@[simp]
theorem cutDist_const_const (p q : I) :
    cutDist (Graphon.const μ₁ p) (Graphon.const μ₂ q) = |(p : ℝ) - q| := by
  rw [cutDist_const_right]
  exact cutNorm_eq_abs_of_forall_eq μ₁ fun x y => by simp

/-- **The cut distance to a graphon on a point mass** `(Ω₂, δ_b)` is the cut norm of the difference
with the constant `W b b`, taken on the carrier of the other graphon. -/
theorem cutDist_dirac_right {b : Ω₂} (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ (Measure.dirac b)) :
    cutDist U W =
      cutNorm μ₁ (U.toSymmKernel - (Graphon.const μ₁ ⟨W b b, W.mem_Icc b b⟩).toSymmKernel) := by
  rw [cutDist_congr_ae_right W.ae_eq_const_of_dirac, cutDist_const_right]

/-- **The cut distance from a graphon on a point mass** `(Ω₁, δ_a)` is the cut norm of the
difference of the constant `U a a` with the other graphon, taken on the carrier of that graphon. -/
theorem cutDist_dirac_left {a : Ω₁} (U : Graphon Ω₁ (Measure.dirac a)) (W : Graphon Ω₂ μ₂) :
    cutDist U W =
      cutNorm μ₂ ((Graphon.const μ₂ ⟨U a a, U.mem_Icc a a⟩).toSymmKernel - W.toSymmKernel) := by
  rw [cutDist_congr_ae_left U.ae_eq_const_of_dirac, cutDist_const_left]

/-- **Two graphons on point masses are at cut distance `|U a a - W b b|`.** -/
@[simp]
theorem cutDist_dirac_dirac {a : Ω₁} {b : Ω₂} (U : Graphon Ω₁ (Measure.dirac a))
    (W : Graphon Ω₂ (Measure.dirac b)) : cutDist U W = |U a a - W b b| := by
  rw [cutDist_congr_ae_left U.ae_eq_const_of_dirac, cutDist_congr_ae_right W.ae_eq_const_of_dirac,
    cutDist_const_const]

end DenseGraphLimits

end TauCeti
