/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
public import TauCeti.Geometry.Manifold.Riemannian.Gradient
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The negative gradient as an adapted pseudo-gradient

Let `f` be a smooth function on a boundaryless manifold `M` with a smooth Riemannian metric. If
near each critical point `x` of `f` the metric is the Euclidean metric of the coordinates of a
Morse chart (`TauCeti.MorseChart.IsEuclidean`), then the negative gradient `-grad f` is a
pseudo-gradient field adapted to `f`. In such a chart `f = f x + (1/2) Σᵢ wᵢ zᵢ²`, so the
gradient reads `z ↦ (wᵢ zᵢ)ᵢ` and the negative gradient is the linear field `z ↦ (-wᵢ zᵢ)ᵢ` of the
chart (`TauCeti.MorseChart.IsEuclidean.neg_riemannianGradient_eq_field`). Away from the critical
points, `df(-grad f) = -‖grad f‖² < 0`.

The results on the flows of adapted pseudo-gradients therefore apply to the negative gradient flow
of such a metric.

## Main declarations

* `TauCeti.MorseChart.IsEuclidean`: the metric is Euclidean in the coordinates of a Morse chart.
* `TauCeti.MorseChart.IsEuclidean.neg_riemannianGradient_eq_field`: in such a chart the negative
  gradient is the linear field of the chart.
* `TauCeti.isAdaptedPseudoGradient_neg_riemannianGradient`: the negative gradient is an adapted
  pseudo-gradient.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.2.
-/

public section

open Bundle Set TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  {f : M → ℝ} {x : M}

namespace MorseChart

variable (φ : MorseChart E f x)

/-- The metric is **Euclidean in the Morse chart** `φ` when, on the source of the chart, it is the
dot product of the coordinates `L (dψ v)` of tangent vectors. -/
def IsEuclidean : Prop :=
  ∀ y ∈ φ.toChart.source, ∀ v w : TangentSpace 𝓘(ℝ, E) y,
    inner ℝ v w = φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y v) ⬝ᵥ
      φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y w)

variable {φ}

/-- **In a Morse chart in which the metric is Euclidean, the negative gradient is the linear field
of the chart**, `z ↦ (-wᵢ zᵢ)ᵢ`. -/
theorem IsEuclidean.neg_riemannianGradient_eq_field (hφ : φ.IsEuclidean) {y : M}
    (hy : y ∈ φ.toChart.source) : -riemannianGradient 𝓘(ℝ, E) f y = φ.field y := by
  have h : -φ.field y = riemannianGradient 𝓘(ℝ, E) f y := eq_riemannianGradient_iff.2 fun v ↦ by
    have hdf : mvfderiv 𝓘(ℝ, E) f y v =
        ∑ i, φ.weight i * φ.coord (φ.toChart y) i *
          φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y v) i := by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y v = _
      rw [mfderiv_eq_fderiv_comp_of_eqOn φ.mem_maximalAtlas φ.eqOn_quadratic hy
        (φ.differentiableAt_quadratic _)]
      exact φ.fderiv_quadratic_apply _ _
    have hX : φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (-φ.field y)) =
        fun i ↦ φ.weight i * φ.coord (φ.toChart y) i := by
      -- `dψ` acts on tangent spaces and `L` on `E`; negation goes through each separately.
      have hneg : φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (-φ.field y)) =
          -φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (φ.field y)) :=
        (congrArg φ.coord (map_neg _ _)).trans (map_neg _ _)
      rw [hneg, φ.coord_mfderiv_field hy]
      ext i
      simp
    rw [hφ y hy, hdf, hX]
    rfl
  rw [← h, neg_neg]

end MorseChart

/-- **The negative gradient is an adapted pseudo-gradient** for a smooth function `f` and a smooth
metric that is Euclidean in a Morse chart at each critical point of `f`. -/
theorem isAdaptedPseudoGradient_neg_riemannianGradient
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hφ : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 → ∃ φ : MorseChart E f x, φ.IsEuclidean) :
    IsAdaptedPseudoGradient f fun y ↦ -riemannianGradient 𝓘(ℝ, E) f y where
  contMDiff := by
    have : IsManifold 𝓘(ℝ, E) (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
    have h := contMDiff_riemannianGradient (I := 𝓘(ℝ, E)) (n := ∞) (f := -f) hf.neg
    simpa only [riemannianGradient_neg] using h
  mvfderiv_apply_lt_zero y hy := by
    have hg : riemannianGradient 𝓘(ℝ, E) f y ≠ 0 := by
      rwa [ne_eq, riemannianGradient_eq_zero_iff, mvfderiv_eq_zero_iff]
    have h : mvfderiv 𝓘(ℝ, E) f y (-riemannianGradient 𝓘(ℝ, E) f y) =
        -inner ℝ (riemannianGradient 𝓘(ℝ, E) f y) (riemannianGradient 𝓘(ℝ, E) f y) :=
      (map_neg _ _).trans (congrArg Neg.neg mvfderiv_apply_riemannianGradient)
    rw [h, neg_lt_zero]
    exact real_inner_self_pos.2 hg
  exists_morseChart x hx := by
    obtain ⟨φ, hφ⟩ := hφ x hx
    exact ⟨φ, fun y hy ↦ by rw [hφ.neg_riemannianGradient_eq_field hy, φ.coord_mfderiv_field hy]⟩

end TauCeti
