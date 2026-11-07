/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.UniqueExtremum
public import TauCeti.Geometry.Manifold.Morse.Sphere.Prod
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The mod-two Morse complex of the standard Morse function on the torus

On the torus `T² = S¹ × S¹`, a product of unit circles in two-dimensional real inner product
spaces, the sum `sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd` of two height functions is
the standard Morse function (`TauCeti.isMorse_sphereHeight_comp_fst_add_comp_snd`). Its critical
points are the four pairs of poles: the maximum `(v, w)` of index `2`, the saddles `(v, -w)` and
`(-v, w)` of index `1`, and the minimum `(-v, -w)` of index `0`.

This file computes its mod-two Morse complex: for every adapted pseudo-gradient satisfying the
Morse–Smale condition, the mod-two Morse boundary vanishes. Each saddle receives two trajectories,
both from the maximum, and emits two, both to the minimum, so every coefficient is even
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_eq_zero_of_finrank_eq_two`). The
complex is therefore the free `ZMod 2`-module on the four critical points with zero differential,
whose homology, of ranks `1`, `2` and `1` in degrees `0`, `1` and `2`, is the mod-two homology of
the torus. Unlike the height function on the sphere
(`TauCeti.IsAdaptedPseudoGradient.isMorseSmale_sphereHeight`), this function has critical points of
intermediate index, so the Morse–Smale condition is a hypothesis.

The Morse complex is defined for manifolds modelled on a normed space `F` with the model
`𝓘(ℝ, F)`. Mathlib's product charts on `S¹ × S¹` take values in the type synonym `ModelProd`, with
the product model `(𝓡 1).prod (𝓡 1)`. This file reads the same charts on the normed space
`EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)` (`TauCeti.torusProdChartedSpace`), and
transports the Morse data along Mathlib's `modelWithCornersSelf_prod`. These differ from the charts
`TauCeti.torusChartedSpace` on `Circle × Circle`, which take values in `EuclideanSpace ℝ (Fin 2)`.

## Main declarations

* `TauCeti.torusProdChartedSpace` and `TauCeti.isManifold_torusProdChartedSpace`: the product
  charts of `S¹ × S¹` on the normed space `EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)`,
  and their smooth compatibility. They are local instances in this file.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_sphereHeight_comp_fst_add_comp_snd`:
  its mod-two Morse boundary vanishes.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the torus).
-/

public section

open Metric Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [Fact (finrank ℝ E = 1 + 1)]
  [Fact (finrank ℝ E' = 1 + 1)]

/-- The product charts of the torus `S¹ × S¹`, read on the normed space
`EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)` rather than on Mathlib's type synonym
`ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))`. -/
noncomputable abbrev torusProdChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphere (0 : E) 1 × sphere (0 : E') 1) :=
  prodChartedSpace _ _ _ _

attribute [local instance] torusProdChartedSpace

/-- The product charts of the torus are smoothly compatible for the model
`𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))`. -/
theorem isManifold_torusProdChartedSpace :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ∞
      (sphere (0 : E) 1 × sphere (0 : E') 1) := by
  rw [modelWithCornersSelf_prod]
  exact (inferInstance : IsManifold ((𝓡 1).prod (𝓡 1)) ∞ (sphere (0 : E) 1 × sphere (0 : E') 1))

attribute [local instance] isManifold_torusProdChartedSpace

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {v : sphere (0 : E) 1}
  {w : sphere (0 : E') 1} {X : (z : sphere (0 : E) 1 × sphere (0 : E') 1) →
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) z}
  {hX : IsAdaptedPseudoGradient (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) X}

/-- **The mod-two Morse boundary of the standard Morse function on the torus is zero.** For every
Morse–Smale pseudo-gradient adapted to the sum of two height functions on `S¹ × S¹`, the mod-two
Morse complex is the free `ZMod 2`-module on the four pairs of poles with zero differential. The
Morse hypothesis `hf` follows from `TauCeti.isMorse_sphereHeight_comp_fst_add_comp_snd` by
rewriting along `modelWithCornersSelf_prod`. -/
@[simp]
theorem morseBoundary_sphereHeight_comp_fst_add_comp_snd (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd)) :
    h.morseBoundary hf = 0 := by
  -- The only critical point of index `2` is `(v, w)`, and the only one of index `0` is `(-v, -w)`.
  have hcrit {z : sphere (0 : E) 1 × sphere (0 : E') 1} {k : ℕ}
      (hz : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ)
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) z = 0)
      (hk : manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) z = k) :
      (k = 2 → z = (v, w)) ∧ (k = 0 → z = (-v, -w)) := by
    obtain ⟨x, y⟩ := z
    rw [← mvfderiv_eq_zero_iff, modelWithCornersSelf_prod,
      mvfderiv_sphereHeight_comp_fst_add_comp_snd_eq_zero_iff] at hz
    rw [modelWithCornersSelf_prod, manifoldMorseIndex_sphereHeight_comp_fst_add_comp_snd] at hk
    rcases hz with ⟨rfl | rfl, rfl | rfl⟩ <;>
      simp only [manifoldMorseIndex_sphereHeight_self,
        manifoldMorseIndex_sphereHeight_neg] at hk <;>
      subst hk <;> simp
  refine h.morseBoundary_eq_zero_of_finrank_eq_two hf (by simp) ?_ ?_
  · exact subsingleton_singleton.anti fun z hz ↦ (hcrit hz.1 hz.2).1 rfl
  · exact subsingleton_singleton.anti fun z hz ↦ (hcrit hz.1 hz.2).2 rfl

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
