/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.Prod
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedUniqueExtremum
public import TauCeti.Geometry.Manifold.Morse.Boundary.UniqueExtremum
public import TauCeti.Geometry.Manifold.Morse.Sphere.Prod
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Orientation.Prod
import TauCeti.Geometry.Manifold.Orientation.Sphere

/-!
# The Morse complexes and trajectory signs of the standard Morse function on the torus

On the torus `T² = S¹ × S¹`, a product of unit circles in two-dimensional real inner product
spaces, the sum `sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd` of two height functions is
the standard Morse function (`TauCeti.isMorse_sphereHeight_comp_fst_add_comp_snd`). Its critical
points are the four pairs of poles: the maximum `(v, w)` of index `2`, the saddles `(v, -w)` and
`(-v, w)` of index `1`, and the minimum `(-v, -w)` of index `0`.

This file computes its mod-two and its integral Morse complexes and its signed trajectory counts:
for every adapted pseudo-gradient satisfying the Morse–Smale condition, both Morse boundaries and
every signed trajectory count vanish. Each saddle receives two trajectories, both from the maximum
`(v, w)`, and emits two, both to the minimum `(-v, -w)`, so every coefficient is even
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_eq_zero_of_finrank_eq_two`).
Over `ℤ` the two trajectories into each saddle carry opposite signs `+1` and `-1` because `S¹ × S¹`
is orientable, and the two trajectories out of each saddle carry opposite signs `+1` and `-1`
because the minimum is unique
(`IsMorseSmale.exists_trajectorySign_eq_one_and_eq_neg_one_of_finrank_eq_two`,
`IsMorseSmale.signedTrajectoryCount_eq_zero_of_finrank_eq_two`,
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundary_eq_zero_of_finrank_eq_two`),
whatever the orientations of the unstable manifolds. So both complexes are free on the four
critical points, of which one has index `0`, two have index `1` and one has index `2`
(`TauCeti.criticalCount_sphereHeight_comp_fst_add_comp_snd`), with zero differential. Their
homologies, of ranks `1`, `2` and `1` in degrees `0`, `1` and `2`, are the mod-two and the integral
homology of the torus. Unlike the height function on the sphere
(`TauCeti.IsAdaptedPseudoGradient.isMorseSmale_sphereHeight`), this function has critical points of
intermediate index, so the Morse–Smale condition is a hypothesis.

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
* `signedMorseBoundary_sphereHeight_comp_fst_add_comp_snd`: its integral Morse boundary vanishes,
  with coefficients in any ring.
* `exists_trajectorySign_sphereHeight_comp_fst_add_comp_snd_eq_one_and_eq_neg_one`: between any
  consecutive-index critical points (from `(v, w)` to either saddle, or from either saddle to
  `(-v, -w)`), the two trajectories carry opposite signs `+1` and `-1`.
* `signedTrajectoryCount_sphereHeight_comp_fst_add_comp_snd`: every signed trajectory count
  between consecutive-index critical points on `S¹ × S¹` vanishes.
* `free_homology_signedMorseComplex_sphereHeight_comp_fst_add_comp_snd` and
  `finrank_homology_signedMorseComplex_sphereHeight_comp_fst_add_comp_snd`: its integral Morse
  homology is free of ranks `1`, `2` and `1` in degrees `0`, `1` and `2`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the torus).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations, and the integral Morse complex of the
  torus).
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
/-- The only critical point of index `2` of the standard Morse function on the torus is `(v, w)`,
and the only one of index `0` is `(-v, -w)`. -/
private theorem eq_of_mfderiv_eq_zero_of_manifoldMorseIndex_eq
    {z : sphere (0 : E) 1 × sphere (0 : E') 1} {k : ℕ}
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

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The standard Morse function on the torus has at most one critical point of index `2`. -/
private theorem subsingleton_setOf_manifoldMorseIndex_eq_two :
    {z : sphere (0 : E) 1 × sphere (0 : E') 1 |
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ)
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) z = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) z = 2}.Subsingleton :=
  subsingleton_singleton.anti fun _ hz ↦
    (eq_of_mfderiv_eq_zero_of_manifoldMorseIndex_eq hz.1 hz.2).1 rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The standard Morse function on the torus has at most one critical point of index `0`. -/
private theorem subsingleton_setOf_manifoldMorseIndex_eq_zero :
    {z : sphere (0 : E) 1 × sphere (0 : E') 1 |
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ)
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) z = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) z = 0}.Subsingleton :=
  subsingleton_singleton.anti fun _ hz ↦
    (eq_of_mfderiv_eq_zero_of_manifoldMorseIndex_eq hz.1 hz.2).2 rfl

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
    subsingleton_setOf_manifoldMorseIndex_eq_two subsingleton_setOf_manifoldMorseIndex_eq_zero

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The sum of two height functions on `S¹ × S¹` is Morse in the product model. -/
private theorem isMorse_sphereHeight_prod (v : sphere (0 : E) 1) (w : sphere (0 : E') 1) :
    IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) := by
  rw [modelWithCornersSelf_prod]
  exact isMorse_sphereHeight_comp_fst_add_comp_snd v w

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The product `S¹ × S¹` is orientable in the product model. -/
private theorem orientable_sphereProd :
    Orientable 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphere (0 : E) 1 × sphere (0 : E') 1) :=
  have := orientable_sphere (E := E) (n := 1)
  have := orientable_sphere (E := E') (n := 1)
  orientable_chartedSpaceProd

/-- **The integral Morse boundary of the standard Morse function on the torus is zero.** For every
Morse–Smale pseudo-gradient adapted to the sum of two height functions on `S¹ × S¹` and every
choice of orientations of the unstable manifolds, the integral Morse complex, with coefficients in
any ring, is the free module on the four pairs of poles with zero differential. Its homology is
free of ranks `1`, `2` and `1` in degrees `0`, `1` and `2`. -/
@[simp]
theorem signedMorseBoundary_sphereHeight_comp_fst_add_comp_snd (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd))
    (𝔬 : MorseOrientation (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) X)
    (R : Type*) [Ring R] : hX.signedMorseBoundary 𝔬 hf R = 0 :=
  have := orientable_sphereProd (E := E) (E' := E')
  h.signedMorseBoundary_eq_zero_of_finrank_eq_two hf 𝔬 (by simp)
    subsingleton_setOf_manifoldMorseIndex_eq_two subsingleton_setOf_manifoldMorseIndex_eq_zero R

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
      hX.trajectorySign φp φq op oq hpq y₁ = 1 ∧ hX.trajectorySign φp φq op oq hpq y₂ = -1 :=
  have := orientable_sphereProd (E := E) (E' := E')
  h.exists_trajectorySign_eq_one_and_eq_neg_one_of_finrank_eq_two (isMorse_sphereHeight_prod v w)
    (by simp) subsingleton_setOf_manifoldMorseIndex_eq_two
    subsingleton_setOf_manifoldMorseIndex_eq_zero hφp hφq op oq hpq

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
    hX.signedTrajectoryCount φp φq op oq hpq = 0 :=
  have := orientable_sphereProd (E := E) (E' := E')
  h.signedTrajectoryCount_eq_zero_of_finrank_eq_two (isMorse_sphereHeight_prod v w) (by simp)
    subsingleton_setOf_manifoldMorseIndex_eq_two subsingleton_setOf_manifoldMorseIndex_eq_zero
    hφp hφq op oq hpq

/-- **The integral Morse homology of the torus is free.** For every Morse–Smale pseudo-gradient
adapted to the sum of two height functions on `S¹ × S¹` and every choice of orientations, the
integral Morse homology, with coefficients in any ring, is a free module in each degree, since the
integral Morse boundary vanishes. -/
theorem free_homology_signedMorseComplex_sphereHeight_comp_fst_add_comp_snd (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd))
    (𝔬 : MorseOrientation (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) X)
    {R : Type*} [Ring R]
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) (n : ℕ) :
    Module.Free R ((hX.signedMorseComplex 𝔬 hf R hsq).homology n) :=
  free_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero hsq
    (h.signedMorseBoundary_sphereHeight_comp_fst_add_comp_snd hf 𝔬 R) n

/-- **The integral Morse homology of the torus.** For every Morse–Smale pseudo-gradient adapted to
the sum of two height functions on `S¹ × S¹` and every choice of orientations of the unstable
manifolds, the integral Morse homology, with coefficients in any ring with the strong rank
condition such as `ℤ`, has rank `1`, `2` and `1` in degrees `0`, `1` and `2`, and vanishes above:
over `ℤ` it is `ℤ`, `ℤ²`, `ℤ`, the integral homology of the torus. -/
theorem finrank_homology_signedMorseComplex_sphereHeight_comp_fst_add_comp_snd
    (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd))
    (𝔬 : MorseOrientation (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) X)
    {R : Type*} [Ring R] [StrongRankCondition R]
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) (n : ℕ) :
    finrank R ((hX.signedMorseComplex 𝔬 hf R hsq).homology n) =
      if n = 1 then 2 else if n ≤ 2 then 1 else 0 := by
  rw [finrank_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero hsq
      (h.signedMorseBoundary_sphereHeight_comp_fst_add_comp_snd hf 𝔬 R),
    modelWithCornersSelf_prod, criticalCount_sphereHeight_comp_fst_add_comp_snd]
  rcases n with _ | _ | _ | n <;> simp [one_add_one_eq_two]

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
