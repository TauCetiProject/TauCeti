/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.Prod
public import TauCeti.Geometry.Manifold.Morse.Boundary.UniqueExtremum
public import TauCeti.Geometry.Manifold.Morse.Sphere.Prod
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Orientation.Prod
import TauCeti.Geometry.Manifold.Orientation.Sphere

/-!
# The Morse boundary and trajectory signs of the standard Morse function on the torus

On the torus `T² = S¹ × S¹`, a product of unit circles in two-dimensional real inner product
spaces, the sum `sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd` of two height functions is
the standard Morse function (`TauCeti.isMorse_sphereHeight_comp_fst_add_comp_snd`). Its critical
points are the four pairs of poles: the maximum `(v, w)` of index `2`, the saddles `(v, -w)` and
`(-v, w)` of index `1`, and the minimum `(-v, -w)` of index `0`.

This file computes its mod-two Morse complex and its signed trajectory counts: for every adapted
pseudo-gradient satisfying the Morse–Smale condition, both the mod-two Morse boundary and every
signed trajectory count vanish. Each saddle receives two trajectories from the maximum `(v, w)`
carrying opposite signs `+1` and `-1` (since `S¹ × S¹` is orientable), and emits two trajectories
to the minimum `(-v, -w)` carrying opposite signs `+1` and `-1`
(`IsMorseSmale.exists_trajectorySign_eq_one_and_eq_neg_one_of_finrank_eq_two`,
`IsMorseSmale.signedTrajectoryCount_eq_zero_of_finrank_eq_two`).
Thus all differentials vanish over `ℤ` as well as over `ZMod 2`, recovering the integral and
mod-two homology ranks `1`, `2` and `1` of the torus in degrees `0`, `1` and `2`. Unlike the height
function on the sphere (`TauCeti.IsAdaptedPseudoGradient.isMorseSmale_sphereHeight`), this function
has critical points of intermediate index, so the Morse–Smale condition is a hypothesis.

The Morse complex is defined for manifolds modelled on a normed space `F` with the model
`𝓘(ℝ, F)`. Mathlib's product charts on `S¹ × S¹` take values in the type synonym `ModelProd`, with
the product model `(𝓡 1).prod (𝓡 1)`. This file reads the same charts on the normed space
`EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)` (`TauCeti.chartedSpaceProd` and
`TauCeti.isManifold_chartedSpaceProd`, local instances), and transports the Morse data along
Mathlib's `modelWithCornersSelf_prod`. These differ from the charts `TauCeti.torusChartedSpace` on
`Circle × Circle`, which take values in `EuclideanSpace ℝ (Fin 2)`.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `morseBoundary_sphereHeight_comp_fst_add_comp_snd`: its mod-two Morse boundary vanishes.
* `exists_trajectorySign_sphereHeight_comp_fst_add_comp_snd_eq_one_and_eq_neg_one`: between any
  consecutive-index critical points (from `(v, w)` to either saddle, or from either saddle to
  `(-v, -w)`), the two trajectories carry opposite signs `+1` and `-1`.
* `signedTrajectoryCount_sphereHeight_comp_fst_add_comp_snd`: every signed trajectory count
  between consecutive-index critical points on `S¹ × S¹` vanishes.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the torus).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and signed trajectory counts on the torus).
-/

public section

open Metric Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [Fact (finrank ℝ E = 1 + 1)]
  [Fact (finrank ℝ E' = 1 + 1)]

attribute [local instance low] chartedSpaceProd

attribute [local instance] isManifold_chartedSpaceProd

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {v : sphere (0 : E) 1}
  {w : sphere (0 : E') 1} {X : (z : sphere (0 : E) 1 × sphere (0 : E') 1) →
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) z}
  {hX : IsAdaptedPseudoGradient (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) X}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
private theorem eq_poles_of_mfderiv_eq_zero {z : sphere (0 : E) 1 × sphere (0 : E') 1} {k : ℕ}
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

/-- **The mod-two Morse boundary of the standard Morse function on the torus is zero.** For every
Morse–Smale pseudo-gradient adapted to the sum of two height functions on `S¹ × S¹`, the mod-two
Morse complex is the free `ZMod 2`-module on the four pairs of poles with zero differential. The
Morse hypothesis `hf` follows from `TauCeti.isMorse_sphereHeight_comp_fst_add_comp_snd` by
rewriting along `modelWithCornersSelf_prod`. -/
@[simp]
theorem morseBoundary_sphereHeight_comp_fst_add_comp_snd (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd)) :
    h.morseBoundary hf = 0 :=
  h.morseBoundary_eq_zero_of_finrank_eq_two hf (by simp)
    (subsingleton_singleton.anti fun _ hz ↦ (eq_poles_of_mfderiv_eq_zero hz.1 hz.2).1 rfl)
    (subsingleton_singleton.anti fun _ hz ↦ (eq_poles_of_mfderiv_eq_zero hz.1 hz.2).2 rfl)

/-- **Opposite trajectory signs at every saddle of the torus.** For every Morse–Smale
pseudo-gradient adapted to `sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd` on `S¹ × S¹`,
between any critical points `p` and `q` of consecutive index (from `(v, w)` to either saddle
`(v, -w)` or `(-v, w)`, or from either saddle to `(-v, -w)`), the two trajectories carry opposite
signs `+1` and `-1`. -/
theorem exists_trajectorySign_sphereHeight_comp_fst_add_comp_snd_eq_one_and_eq_neg_one
    (h : hX.IsMorseSmale) {p q : sphere (0 : E) 1 × sphere (0 : E') 1}
    {φp : MorseChart (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) p}
    {φq : MorseChart (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) q}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) p =
      manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) q + 1) :
    ∃ y₁ ∈ hX.morseTrajectorySlice p q, ∃ y₂ ∈ hX.morseTrajectorySlice p q,
      hX.trajectorySign φp φq op oq hpq y₁ = 1 ∧ hX.trajectorySign φp φq op oq hpq y₂ = -1 := by
  have hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) := by
    rw [modelWithCornersSelf_prod]
    exact isMorse_sphereHeight_comp_fst_add_comp_snd v w
  have : Orientable (𝓡 1) (sphere (0 : E) 1) := orientable_sphere
  have : Orientable (𝓡 1) (sphere (0 : E') 1) := orientable_sphere
  have : Orientable 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphere (0 : E) 1 × sphere (0 : E') 1) := orientable_chartedSpaceProd
  exact h.exists_trajectorySign_eq_one_and_eq_neg_one_of_finrank_eq_two hf (by simp)
    (subsingleton_singleton.anti fun _ hz ↦ (eq_poles_of_mfderiv_eq_zero hz.1 hz.2).1 rfl)
    (subsingleton_singleton.anti fun _ hz ↦ (eq_poles_of_mfderiv_eq_zero hz.1 hz.2).2 rfl)
    hφp hφq op oq hpq

/-- **Signed trajectory counts of the standard Morse function on the torus vanish.** For every
Morse–Smale pseudo-gradient adapted to `sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd` on
`S¹ × S¹`, every signed count of trajectories between critical points of consecutive index is
zero. -/
theorem signedTrajectoryCount_sphereHeight_comp_fst_add_comp_snd (h : hX.IsMorseSmale)
    {p q : sphere (0 : E) 1 × sphere (0 : E') 1}
    {φp : MorseChart (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) p}
    {φq : MorseChart (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) q}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) p =
      manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) q + 1) :
    hX.signedTrajectoryCount φp φq op oq hpq = 0 := by
  have hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) := by
    rw [modelWithCornersSelf_prod]
    exact isMorse_sphereHeight_comp_fst_add_comp_snd v w
  have : Orientable (𝓡 1) (sphere (0 : E) 1) := orientable_sphere
  have : Orientable (𝓡 1) (sphere (0 : E') 1) := orientable_sphere
  have : Orientable 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphere (0 : E) 1 × sphere (0 : E') 1) := orientable_chartedSpaceProd
  exact h.signedTrajectoryCount_eq_zero_of_finrank_eq_two hf (by simp)
    (subsingleton_singleton.anti fun _ hz ↦ (eq_poles_of_mfderiv_eq_zero hz.1 hz.2).1 rfl)
    (subsingleton_singleton.anti fun _ hz ↦ (eq_poles_of_mfderiv_eq_zero hz.1 hz.2).2 rfl)
    hφp hφq op oq hpq

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
