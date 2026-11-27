/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.Prod
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedUniqueExtremum
public import TauCeti.Geometry.Manifold.Morse.Sphere.Prod.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Orientation.Prod
import TauCeti.Geometry.Manifold.Orientation.Sphere

/-!
# The Morse complexes of the sum of two height functions on a product of spheres

On the product `Sⁿ × Sᵐ` of two unit spheres, with `n` and `m` positive, the sum
`f = sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd` of two height functions is a Morse
function (`TauCeti.isMorse_sphereHeight_comp_fst_add_comp_snd`). Its critical points are the four
pairs of poles: the maximum `(v, w)` of index `n + m` and value `2`, the points `(v, -w)` and
`(-v, w)` of indices `n` and `m` and value `0`, and the minimum `(-v, -w)` of index `0` and value
`-2`. For `n = m = 1` this is the standard Morse function on the torus `T² = S¹ × S¹`, with one
maximum, two saddles and one minimum.

Every pseudo-gradient adapted to `f` is Morse–Smale
(`TauCeti.IsAdaptedPseudoGradient.isMorseSmale_sphereHeight_comp_fst_add_comp_snd`): the only
distinct critical points whose indices are neither `0` nor `n + m` are `(v, -w)` and `(-v, w)`,
and since they have the same value no trajectory joins them.

This file computes the mod-two and the integral Morse complexes of `f`: for every adapted
pseudo-gradient and every choice `𝔬` of orientations of the unstable manifolds, both Morse
boundaries vanish. A coefficient of the integral boundary from `p` to `q` can only be nonzero when
the index drops by one and the value strictly decreases, and each such pair is excluded:

* if `p` is the maximum, it is the only critical point of index `n + m`, the dimension of the
  orientable manifold `Sⁿ × Sᵐ`, so its integral boundary vanishes
  (`IsMorseSmale.signedMorseBoundaryCoeff_eq_zero_of_unique_index_finrank`);
* if `q` is the minimum, it is the only critical point of index `0`, so the integral boundary never
  reaches it (`IsMorseSmale.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero`);
* otherwise `p` and `q` are the two middle critical points, which have the same value `0`
  (`IsAdaptedPseudoGradient.signedMorseBoundaryCoeff_eq_zero_of_value_le`).

The mod-two boundary is the reduction of the integral one
(`IsMorseSmale.signedMorseBoundary_eq_morseBoundary`). So both complexes are free on the four
critical points with zero differential, and the integral Morse homology, with coefficients in any
ring with the strong rank condition, has rank equal to the number of pairs of poles of each index:
over `ℤ` it is the integral homology of `Sⁿ × Sᵐ`, free of rank one in degrees `0`, `n`, `m` and
`n + m` (counted twice in degree `n` when `n = m`). For the torus these are the ranks `1`, `2` and
`1` in degrees `0`, `1` and `2`.

The arguments use that `n` and `m` are positive: on `S⁰ × Sᵐ`, the disjoint union of two copies of
`Sᵐ`, there are two critical points of each of the indices `0` and `m`, so neither extremum is
unique.

The Morse complex is defined for manifolds modelled on a normed space `F` with the model
`𝓘(ℝ, F)`. Mathlib's product charts on `Sⁿ × Sᵐ` take values in the type synonym `ModelProd`, with
the product model `(𝓡 n).prod (𝓡 m)`. This file reads the same charts on the normed space
`EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)` (`TauCeti.chartedSpaceProd` and
`TauCeti.isManifold_chartedSpaceProd`, local instances), and transports the Morse data along
Mathlib's `modelWithCornersSelf_prod`. For the torus these differ from the charts
`TauCeti.torusChartedSpace` on `Circle × Circle`, which take values in `EuclideanSpace ℝ (Fin 2)`.

The Morse hypothesis `hf` of the Morse complexes, for the model of these charts, is
`(isMorse_sphereHeight v).comp_fst_add_comp_snd_chartedSpaceProd (isMorse_sphereHeight w)`
(`TauCeti.IsMorse.comp_fst_add_comp_snd_chartedSpaceProd`).

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `isMorseSmale_sphereHeight_comp_fst_add_comp_snd`: every pseudo-gradient adapted to the sum of
  two height functions is Morse–Smale.
* `signedMorseBoundaryCoeff_sphereHeight_comp_fst_add_comp_snd` and
  `signedMorseBoundary_sphereHeight_comp_fst_add_comp_snd`: its integral Morse boundary vanishes,
  with coefficients in any ring.
* `IsMorseSmale.morseBoundary_sphereHeight_comp_fst_add_comp_snd`: so does its mod-two Morse
  boundary.
* `free_homology_signedMorseComplex_sphereHeight_comp_fst_add_comp_snd` and
  `finrank_homology_signedMorseComplex_sphereHeight_comp_fst_add_comp_snd`: its integral Morse
  homology is free, with one generator for each pair of poles of the given index.

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
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {n m : ℕ} [Fact (finrank ℝ E = n + 1)]
  [Fact (finrank ℝ E' = m + 1)]

attribute [local instance low] chartedSpaceProd

attribute [local instance] isManifold_chartedSpaceProd

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {v : sphere (0 : E) 1}
  {w : sphere (0 : E') 1} {X : (z : sphere (0 : E) 1 × sphere (0 : E') 1) →
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) z}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- For positive `n` and `m`, the only critical point of index `n + m` of the sum of two height
functions on `Sⁿ × Sᵐ` is `(v, w)`, the only one of index `0` is `(-v, -w)`, and every other
critical point has value `0`. -/
private theorem eq_and_value_eq_zero_of_mfderiv_eq_zero (hn : n ≠ 0) (hm : m ≠ 0)
    {z : sphere (0 : E) 1 × sphere (0 : E') 1} {k : ℕ}
    (hz : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) 𝓘(ℝ)
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) z = 0)
    (hk : manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) z = k) :
    (k = n + m → z = (v, w)) ∧ (k = 0 → z = (-v, -w)) ∧
      (k ≠ n + m → k ≠ 0 → sphereHeight v z.1 + sphereHeight w z.2 = 0) := by
  obtain ⟨x, y⟩ := z
  rw [← mvfderiv_eq_zero_iff, modelWithCornersSelf_prod,
    mvfderiv_sphereHeight_comp_fst_add_comp_snd_eq_zero_iff] at hz
  rw [modelWithCornersSelf_prod, manifoldMorseIndex_sphereHeight_comp_fst_add_comp_snd] at hk
  -- The index `0` of the minimum `(-v, -w)` is not `n + m`.
  have h0 : 0 ≠ n + m := by omega
  rcases hz with ⟨rfl | rfl, rfl | rfl⟩ <;>
    simp only [manifoldMorseIndex_sphereHeight_self, manifoldMorseIndex_sphereHeight_neg] at hk <;>
    subst hk <;> simp [hn, hm, h0]

/-- **The sum of two height functions is Morse–Smale for every pseudo-gradient.** On a product
`Sⁿ × Sᵐ` of spheres of positive dimensions, every pseudo-gradient adapted to the sum of two height
functions satisfies the Morse–Smale condition. The only distinct critical points whose indices are
neither `0` nor `n + m` are `(v, -w)` and `(-v, w)`, which have the same value `0`, so no trajectory
joins them. -/
theorem isMorseSmale_sphereHeight_comp_fst_add_comp_snd (hn : n ≠ 0) (hm : m ≠ 0)
    (hX : IsAdaptedPseudoGradient (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) X) :
    hX.IsMorseSmale := by
  have hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) :=
    (isMorse_sphereHeight v).comp_fst_add_comp_snd_chartedSpaceProd (isMorse_sphereHeight w)
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) = n + m := by simp
  refine IsMorseSmale.of_forall_ne_of_manifoldMorseIndex_ne hf
    fun a b y ha hb hab ha0 han hb0 hbn hy ↦ ?_
  -- The value strictly decreases from `a` to `b`, but both values are `0`.
  have hy' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hab hy
  have hav := (eq_and_value_eq_zero_of_mfderiv_eq_zero hn hm ha rfl).2.2 (hfin ▸ han) ha0
  have hbv := (eq_and_value_eq_zero_of_mfderiv_eq_zero hn hm hb rfl).2.2 (hfin ▸ hbn) hb0
  simp only [Pi.add_apply, Function.comp_apply, mem_Ioo, hav, hbv] at hy'
  exact absurd (hy'.1.trans hy'.2) (lt_irrefl 0)

variable {hX : IsAdaptedPseudoGradient (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) X}
  (𝔬 : MorseOrientation (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) X)

/-- Every coefficient of the integral Morse boundary of the sum of two height functions on a
product `Sⁿ × Sᵐ` of spheres of positive dimensions vanishes, for every adapted pseudo-gradient and
whatever the orientations of the unstable manifolds. -/
@[simp]
theorem signedMorseBoundaryCoeff_sphereHeight_comp_fst_add_comp_snd (hn : n ≠ 0) (hm : m ≠ 0)
    (p q : criticalPoints 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd)) :
    hX.signedMorseBoundaryCoeff 𝔬 p q = 0 := by
  have := orientable_sphere (E := E) (n := n)
  have := orientable_sphere (E := E') (n := m)
  have := orientable_chartedSpaceProd (E := EuclideanSpace ℝ (Fin n))
    (E' := EuclideanSpace ℝ (Fin m)) (N := sphere (0 : E) 1) (N' := sphere (0 : E') 1)
  have h := isMorseSmale_sphereHeight_comp_fst_add_comp_snd hn hm hX
  have hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) :=
    (isMorse_sphereHeight v).comp_fst_add_comp_snd_chartedSpaceProd (isMorse_sphereHeight w)
  set ι := manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
    (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd)
  by_cases hind : ι p = ι q + 1
  swap
  · exact signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hind
  have hp := eq_and_value_eq_zero_of_mfderiv_eq_zero (k := ι p) hn hm
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property) rfl
  have hq := eq_and_value_eq_zero_of_mfderiv_eq_zero (k := ι q) hn hm
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property) rfl
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) = n + m := by simp
  by_cases hpmax : ι p = n + m
  · -- The maximum is the only critical point of index `n + m`.
    refine h.signedMorseBoundaryCoeff_eq_zero_of_unique_index_finrank hf 𝔬 (hfin ▸ hpmax)
      (fun y hy hyk ↦ ?_) q
    rw [(eq_and_value_eq_zero_of_mfderiv_eq_zero hn hm hy (hyk.trans hfin)).1 rfl, hp.1 hpmax]
  by_cases hqmin : ι q = 0
  · -- The minimum is the only critical point of index `0`.
    refine h.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero hf 𝔬 (fun y hy hy0 ↦ ?_) p
    rw [(eq_and_value_eq_zero_of_mfderiv_eq_zero hn hm hy hy0).2.1 rfl, hq.2.1 hqmin]
  -- Otherwise `p` and `q` are the two middle critical points, both of value `0`.
  have hle : ι p ≤ n + m := hfin ▸ manifoldMorseIndex_le_finrank
  refine signedMorseBoundaryCoeff_eq_zero_of_value_le (le_of_eq ?_)
  simp only [Pi.add_apply, Function.comp_apply]
  rw [hp.2.2 hpmax (by omega), hq.2.2 (by omega) hqmin]

/-- **The integral Morse boundary of the sum of two height functions on a product of spheres is
zero.** For every pseudo-gradient adapted to the sum of two height functions on a product `Sⁿ × Sᵐ`
of spheres of positive dimensions, such as the torus `S¹ × S¹`, and every choice of orientations of
the unstable manifolds, the integral Morse complex, with coefficients in any ring, is the free
module on the four pairs of poles with zero differential. -/
@[simp]
theorem signedMorseBoundary_sphereHeight_comp_fst_add_comp_snd (hn : n ≠ 0) (hm : m ≠ 0)
    (hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd))
    (R : Type*) [Ring R] : hX.signedMorseBoundary 𝔬 hf R = 0 := by
  ext p q
  simp [hn, hm]

/-- **The integral Morse homology of a product of spheres is free.** For every pseudo-gradient
adapted to the sum of two height functions on a product `Sⁿ × Sᵐ` of spheres of positive dimensions
and every choice of orientations, the integral Morse homology, with coefficients in any ring, is a
free module in each degree, since the integral Morse boundary vanishes. -/
theorem free_homology_signedMorseComplex_sphereHeight_comp_fst_add_comp_snd (hn : n ≠ 0)
    (hm : m ≠ 0)
    (hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd)) {R : Type*} [Ring R]
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) (k : ℕ) :
    Module.Free R ((hX.signedMorseComplex 𝔬 hf R hsq).homology k) :=
  free_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero hsq
    (signedMorseBoundary_sphereHeight_comp_fst_add_comp_snd 𝔬 hn hm hf R) k

/-- **The integral Morse homology of a product of spheres.** For every pseudo-gradient adapted to
the sum of two height functions on a product `Sⁿ × Sᵐ` of spheres of positive dimensions and every
choice of orientations of the unstable manifolds, the integral Morse homology in degree `k`, with
coefficients in any ring with the strong rank condition such as `ℤ`, has rank the number of the
indices `n + m`, `n`, `m` and `0` equal to `k`. Over `ℤ` it is the integral homology of `Sⁿ × Sᵐ`;
for the torus `S¹ × S¹` it is `ℤ`, `ℤ²`, `ℤ` in degrees `0`, `1` and `2`. -/
theorem finrank_homology_signedMorseComplex_sphereHeight_comp_fst_add_comp_snd (hn : n ≠ 0)
    (hm : m ≠ 0)
    (hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd))
    {R : Type*} [Ring R] [StrongRankCondition R]
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) (k : ℕ) :
    finrank R ((hX.signedMorseComplex 𝔬 hf R hsq).homology k) =
      (if n + m = k then 1 else 0) + (if n = k then 1 else 0) + (if m = k then 1 else 0) +
        if 0 = k then 1 else 0 := by
  rw [finrank_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero hsq
      (signedMorseBoundary_sphereHeight_comp_fst_add_comp_snd 𝔬 hn hm hf R),
    modelWithCornersSelf_prod, criticalCount_sphereHeight_comp_fst_add_comp_snd]
  split_ifs <;> norm_num

/-- **The mod-two Morse boundary of the sum of two height functions on a product of spheres is
zero.** For every pseudo-gradient adapted to the sum of two height functions on a product
`Sⁿ × Sᵐ` of spheres of positive dimensions, such as the torus `S¹ × S¹`, the mod-two Morse complex
is the free `ZMod 2`-module on the four pairs of poles with zero differential. The Morse–Smale
hypothesis `h` holds by `isMorseSmale_sphereHeight_comp_fst_add_comp_snd`, and the Morse
hypothesis `hf` by `TauCeti.IsMorse.comp_fst_add_comp_snd_chartedSpaceProd` applied to
`isMorse_sphereHeight`. -/
@[simp]
theorem IsMorseSmale.morseBoundary_sphereHeight_comp_fst_add_comp_snd (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd)) (hn : n ≠ 0) (hm : m ≠ 0) :
    h.morseBoundary hf = 0 := by
  obtain ⟨𝔬⟩ := hX.nonempty_morseOrientation
  rw [← h.signedMorseBoundary_eq_morseBoundary hf (𝔬 := 𝔬),
    signedMorseBoundary_sphereHeight_comp_fst_add_comp_snd 𝔬 hn hm hf]

end IsAdaptedPseudoGradient

end TauCeti
