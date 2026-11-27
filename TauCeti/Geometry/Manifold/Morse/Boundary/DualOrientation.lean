/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
public import TauCeti.Geometry.Manifold.Morse.Boundary.ReversedSign

/-!
# The integral Morse boundary of the opposite function

Let `f` be a Morse function on a compact boundaryless manifold `M`, oriented by `oM`, and `X` a
Morse–Smale pseudo-gradient adapted to `f`. Then `-X` is a Morse–Smale pseudo-gradient adapted to
`-f`, with the same critical points and the trajectories of `X` run backwards. Over `ℤ` the Morse
boundary of `-f` is the dual of that of `f` up to signs, once orientation data for `-f` are chosen
compatibly with those of `f`. This file makes that choice and computes the signs.

At a critical point `x`, a Morse chart splits the coordinates into those of negative weight, the
unstable directions `V⁻` of `X`, and those of positive weight, the unstable directions `V⁺` of
`-X`. Given an orientation `op` of `V⁻`, there is exactly one orientation of `V⁺` such that `op`
followed by it is the orientation of `M` at `x`
(`TauCeti.IsAdaptedPseudoGradient.complementaryOrientation`, read through the exact sequence
`0 → V⁻ → T_x M → V⁺ → 0` of `TauCeti.IsAdaptedPseudoGradient.unstableFrameOrientation`). Doing
this at every critical point turns orientation data `𝔬` for `X` into **dual orientation data**
`𝔬.dual hX hf oM` for `-X` (`TauCeti.MorseOrientation.dual`), in the negated Morse charts.

With these orientations each trajectory of `X` from `p` to `q`, with `ind p = ind q + 1`, counts
for `-f` with `(-1) ^ ind_f p` times its sign for `f`
(`TauCeti.IsAdaptedPseudoGradient.neg_trajectorySign_of_unstableFrameOrientation`). So the
coefficient of `p` in the integral Morse boundary of `q` for `-f` is `(-1) ^ ind_f p` times the
coefficient of `q` in the boundary of `p` for `f`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundaryCoeff_dual`). Identifying the
chains of `-f` with the cochains of `f` through the basis of critical points, the boundary of `-f`
is the dual map of the boundary of `f` precomposed with the sign change `p ↦ (-1) ^ ind_f p • p`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.toDual_comp_signedMorseBoundary_dual`). Since a
critical point of index `k` for `-f` has index `n - k` for `f`, this matches the integral chains
of `-f` in degree `k` with the integral cochains of `f` in degree `n - k`. This is the integral
form, on an oriented manifold, of the comparison of boundary maps that underlies the Morse-theoretic
proof of Poincaré duality; its mod-two form is
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.toDual_comp_morseBoundary_neg`. The results here are
identities of boundary maps only. In particular the coefficients of `∂ ∘ ∂` for `-f` are those of
`∂ ∘ ∂` for `f`, transposed and negated (in the namespace `TauCeti.IsAdaptedPseudoGradient`,
`IsMorseSmale.signedMorseBoundary_dual_signedMorseBoundary_dual_single_apply`), so the relation
`∂ ∘ ∂ = 0` holds for `-f` exactly when it holds for `f`; the integral relation `∂ ∘ ∂ = 0`
itself, needed to speak of an integral Morse complex and its homology, is not proved here.

## Main definitions

* `TauCeti.MorseOrientation.neg`: orientation data for `-X` in the negated Morse charts of `𝔬`, with
  chosen orientations.
* `TauCeti.MorseOrientation.dual`: orientation data for `-X` dual to orientation data for `X`, the
  case of `TauCeti.MorseOrientation.neg` at the complementary orientations.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.signedMorseBoundaryCoeff_dual`,
  `IsMorseSmale.signedMorseBoundary_dual_single_apply`: the boundary coefficients of `-f` are those
  of `f`, transposed, times `(-1) ^ ind_f p`.
* `IsMorseSmale.toDual_comp_signedMorseBoundary_dual`: the boundary of `-f` is the signed dual
  map of the boundary of `f`.
* `IsMorseSmale.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_iff`: the Morse
  boundary of `-f` squares to zero exactly when that of `f` does.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations) and §3, Exercise 5 (the Morse complex of
  `-f` and Poincaré duality).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseOrientation

section Neg

variable (𝔬 : MorseOrientation f X) (hf : IsMorse 𝓘(ℝ, E) f)

/-- **Orientation data for `-X` with chosen orientations.** The negated Morse charts of `𝔬`, in
which `-X` is linear, with the orientations `o' p` of their coordinates of negative weight, the
unstable directions of `-X`. On an oriented manifold, choosing for `o' p` the orientation that
completes `𝔬.orientation p` to the orientation of `M` gives the dual orientation data
(`TauCeti.MorseOrientation.dual`); without an orientation there is no preferred choice. -/
-- The body is exposed: the type of `orientation` depends on `chart`, and stating
-- `neg_orientation` needs `(𝔬.neg hf o').chart` to reduce to the negated chart.
@[expose]
noncomputable def neg (o' : ∀ p : criticalPoints 𝓘(ℝ, E) (-f),
      Orientation ℝ ({i // ((𝔬.chart (Set.equivOfEq criticalPoints_neg p)).neg
        (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
          (Set.equivOfEq criticalPoints_neg p).property)).weight i < 0} → ℝ)
        (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) p))) :
    MorseOrientation (-f) (-X) where
  chart p := (𝔬.chart (Set.equivOfEq criticalPoints_neg p)).neg
    (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg p).property)
  coord_mfderiv_chart _ := (𝔬.chart _).coord_mfderiv_neg (𝔬.coord_mfderiv_chart _) _
  orientation := o'

variable (o' : ∀ p : criticalPoints 𝓘(ℝ, E) (-f),
  Orientation ℝ ({i // ((𝔬.chart (Set.equivOfEq criticalPoints_neg p)).neg
    (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg p).property)).weight i < 0} → ℝ)
    (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) p)))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- The charts of `𝔬.neg hf o'` are the negated charts of `𝔬`. -/
@[simp]
theorem neg_chart (p : criticalPoints 𝓘(ℝ, E) (-f)) :
    (𝔬.neg hf o').chart p = (𝔬.chart (Set.equivOfEq criticalPoints_neg p)).neg
      (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        (Set.equivOfEq criticalPoints_neg p).property) :=
  rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- The orientations of `𝔬.neg hf o'` are the chosen orientations `o'`. -/
@[simp]
theorem neg_orientation (p : criticalPoints 𝓘(ℝ, E) (-f)) :
    (𝔬.neg hf o').orientation p = o' p :=
  rfl

end Neg

variable (𝔬 : MorseOrientation f X) (hX : IsAdaptedPseudoGradient f X) (hf : IsMorse 𝓘(ℝ, E) f)
  (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)))

/-- **Dual orientation data.** Orientation data for `-X`, built from orientation data `𝔬` for `X`
and an orientation `oM` of `M`: at each critical point, the negated Morse chart of `𝔬`, in which
`-X` is linear, and the complementary orientation of its coordinates of negative weight, so that
the orientation of the unstable manifold of `X` followed by that of the unstable manifold of `-X`
is the orientation of `M`. It is `𝔬.neg hf` at these complementary orientations. -/
-- The body is exposed: the type of `orientation` depends on `chart`, and stating `dual_orientation`
-- needs `(𝔬.dual hX hf oM).chart` to reduce to the negated charts of `𝔬`.
@[expose]
noncomputable def dual : MorseOrientation (-f) (-X) :=
  𝔬.neg hf fun p ↦ hX.complementaryOrientation (𝔬.coord_mfderiv_chart _) hf
    (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg p).property) oM
    (𝔬.orientation (Set.equivOfEq criticalPoints_neg p))

/-- The charts of the dual orientation data are the negated charts. -/
@[simp]
theorem dual_chart (p : criticalPoints 𝓘(ℝ, E) (-f)) :
    (𝔬.dual hX hf oM).chart p = (𝔬.chart (Set.equivOfEq criticalPoints_neg p)).neg
      (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        (Set.equivOfEq criticalPoints_neg p).property) :=
  𝔬.neg_chart hf _ p

/-- The orientations of the dual orientation data are the complementary orientations. -/
@[simp]
theorem dual_orientation (p : criticalPoints 𝓘(ℝ, E) (-f)) :
    (𝔬.dual hX hf oM).orientation p =
      hX.complementaryOrientation (𝔬.coord_mfderiv_chart _) hf
        (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
          (Set.equivOfEq criticalPoints_neg p).property) oM
        (𝔬.orientation (Set.equivOfEq criticalPoints_neg p)) :=
  𝔬.neg_orientation hf _ p

end MorseOrientation

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} (𝔬 : MorseOrientation f X) (hf : IsMorse 𝓘(ℝ, E) f)
  (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)))

/-- **The boundary coefficients of the opposite function.** For the dual orientation data, the
coefficient of `p` in the integral Morse boundary of `q` for `-f` is `(-1) ^ ind_f p` times the
coefficient of `q` in the integral Morse boundary of `p` for `f`. -/
theorem IsMorseSmale.signedMorseBoundaryCoeff_dual (hMS : hX.IsMorseSmale)
    (q p : criticalPoints 𝓘(ℝ, E) (-f)) :
    (hX.neg hf).signedMorseBoundaryCoeff (𝔬.dual hX hf oM) q p =
      (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p *
        hX.signedMorseBoundaryCoeff 𝔬 (Set.equivOfEq criticalPoints_neg p)
          (Set.equivOfEq criticalPoints_neg q) := by
  have hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p :=
    hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg p).property
  have hq : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f q :=
    hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg q).property
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one
      (hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq),
      signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq]
    exact neg_signedTrajectoryCount_of_unstableFrameOrientation (𝔬.coord_mfderiv_chart _)
      (𝔬.coord_mfderiv_chart _) hf hp hq oM _ ((𝔬.dual hX hf oM).orientation p) _
      ((𝔬.dual hX hf oM).orientation q)
      (reindex_unstableFrameOrientation_complementaryOrientation _ hf hp oM _)
      (reindex_unstableFrameOrientation_complementaryOrientation _ hf hq oM _) hMS hpq
  · have hq' : manifoldMorseIndex 𝓘(ℝ, E) (-f) q ≠ manifoldMorseIndex 𝓘(ℝ, E) (-f) p + 1 := by
      have := hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
      have := hq.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
      omega
    rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hq',
      signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hpq, mul_zero]

section Ring

variable {R : Type*} [Ring R]

/-- **The boundary of the opposite function on a critical point.** For the dual orientation data,
the coefficient of `p` in the boundary of `a • q` for `-f` is `(-1) ^ ind_f p` times the coefficient
of `q` in the boundary of `a • p` for `f`. -/
theorem IsMorseSmale.signedMorseBoundary_dual_single_apply (hMS : hX.IsMorseSmale)
    (q p : criticalPoints 𝓘(ℝ, E) (-f)) (a : R) :
    (hX.neg hf).signedMorseBoundary (𝔬.dual hX hf oM) hf.neg R (Finsupp.single q a) p =
      (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p *
        hX.signedMorseBoundary 𝔬 hf R (Finsupp.single (Set.equivOfEq criticalPoints_neg p) a)
          (Set.equivOfEq criticalPoints_neg q) := by
  rw [signedMorseBoundary_single_apply, signedMorseBoundary_single_apply,
    hMS.signedMorseBoundaryCoeff_dual 𝔬 hf oM]
  push_cast
  rw [← mul_assoc, ← mul_assoc, ((Commute.neg_one_right a).pow_right _).eq]

/-- **`∂ ∘ ∂` for the opposite function.** For the dual orientation data, the coefficient of `p` in
the boundary of the boundary of `r` for `-f` is minus the coefficient of `r` in the boundary of the
boundary of `p` for `f`. Each intermediate critical point `q` contributes the product of the signs
`(-1) ^ ind_f q` and `(-1) ^ ind_f p`, which is `-1` since `ind_f p = ind_f q + 1`. -/
theorem IsMorseSmale.signedMorseBoundary_dual_signedMorseBoundary_dual_single_apply
    (hMS : hX.IsMorseSmale) (r p : criticalPoints 𝓘(ℝ, E) (-f)) :
    (hX.neg hf).signedMorseBoundary (𝔬.dual hX hf oM) hf.neg R
        ((hX.neg hf).signedMorseBoundary (𝔬.dual hX hf oM) hf.neg R (Finsupp.single r 1)) p =
      -hX.signedMorseBoundary 𝔬 hf R
        (hX.signedMorseBoundary 𝔬 hf R (Finsupp.single (Set.equivOfEq criticalPoints_neg p) 1))
          (Set.equivOfEq criticalPoints_neg r) := by
  have := hf.finite_criticalPoints.to_subtype
  have := hf.neg.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) (-f))
  rw [signedMorseBoundary_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    signedMorseBoundary_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]
  simp_rw [signedMorseBoundary_single_apply, one_mul, hMS.signedMorseBoundaryCoeff_dual 𝔬 hf oM,
    ← Int.cast_mul, ← Int.cast_sum, ← Int.cast_neg, ← Finset.sum_neg_distrib]
  congr 1
  -- Reindex by the critical points of `f`, and compare the summands at each `q`.
  refine Fintype.sum_equiv (Set.equivOfEq criticalPoints_neg) _ _ fun q ↦ ?_
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · simp only [Set.equivOfEq_apply, hpq, pow_succ]
    rcases neg_one_pow_eq_or ℤ (manifoldMorseIndex 𝓘(ℝ, E) f q) with h | h <;> rw [h] <;> ring
  · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (p := Set.equivOfEq _ p)
      (q := Set.equivOfEq _ q) (by simpa using hpq)]
    simp

/-- **`∂² = 0` for `-f` exactly when `∂² = 0` for `f`.** For the dual orientation data, the Morse
boundary of `-f` with coefficients in a ring `R` squares to zero exactly when the Morse boundary of
`f` with coefficients in `R` does. In particular, the integral Morse complex of `-f` is defined
whenever that of `f` is. -/
theorem IsMorseSmale.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_iff
    (hMS : hX.IsMorseSmale) :
    (hX.neg hf).signedMorseBoundary (𝔬.dual hX hf oM) hf.neg R ∘ₗ
        (hX.neg hf).signedMorseBoundary (𝔬.dual hX hf oM) hf.neg R = 0 ↔
      hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0 := by
  -- Compare the two maps on the basis: by the transposition identity, the coefficient of `p` in
  -- `∂∂r` for `-f` is minus the coefficient of `r` in `∂∂p` for `f`.
  refine ⟨fun h ↦ Finsupp.basisSingleOne.ext fun p ↦ Finsupp.ext fun r ↦ ?_,
    fun h ↦ Finsupp.basisSingleOne.ext fun r ↦ Finsupp.ext fun p ↦ ?_⟩
  · simpa [hMS.signedMorseBoundary_dual_signedMorseBoundary_dual_single_apply 𝔬 hf oM] using
      congr($h (Finsupp.single ((Set.equivOfEq criticalPoints_neg).symm r) 1)
        ((Set.equivOfEq criticalPoints_neg).symm p))
  · simpa [hMS.signedMorseBoundary_dual_signedMorseBoundary_dual_single_apply 𝔬 hf oM] using
      congr($h (Finsupp.single (Set.equivOfEq criticalPoints_neg p) 1)
        (Set.equivOfEq criticalPoints_neg r))

end Ring

/-- **The boundary of the opposite function is the signed dual map.** Identify a chain of `-f`
with a cochain of `f`, sending each critical point to the dual basis vector of the same critical
point (`Module.Basis.toDual` for the standard basis of finitely supported functions). For the dual
orientation data, the integral Morse boundary of `-f` for `-X` is then the dual map of the boundary
of `f` for `X` precomposed with the sign change `p ↦ (-1) ^ ind_f p • p` (`Finsupp.signEquiv`). A
critical point of index `k` for `-f` has index `n - k` for `f`, where `n` is the dimension, so this
matches the chains of `-f` in index `k` with the cochains of `f` in index `n - k`. -/
theorem IsMorseSmale.toDual_comp_signedMorseBoundary_dual {R : Type*} [CommRing R]
    (hMS : hX.IsMorseSmale) [DecidableEq (criticalPoints 𝓘(ℝ, E) f)] :
    Finsupp.basisSingleOne.toDual ∘ₗ
        (Finsupp.domLCongr (Set.equivOfEq criticalPoints_neg)).toLinearMap ∘ₗ
          (hX.neg hf).signedMorseBoundary (𝔬.dual hX hf oM) hf.neg R =
      (hX.signedMorseBoundary 𝔬 hf R ∘ₗ
          (Finsupp.signEquiv R fun p : criticalPoints 𝓘(ℝ, E) f ↦
            (-1 : ℤˣ) ^ manifoldMorseIndex 𝓘(ℝ, E) f p).toLinearMap).dualMap ∘ₗ
        Finsupp.basisSingleOne.toDual ∘ₗ
          (Finsupp.domLCongr (Set.equivOfEq criticalPoints_neg)).toLinearMap := by
  refine Finsupp.basisSingleOne.ext fun q ↦ Finsupp.basisSingleOne.ext fun p ↦ ?_
  have hq : Finsupp.domLCongr (M := R) (R := R) (Set.equivOfEq criticalPoints_neg)
      (Finsupp.basisSingleOne q) = Finsupp.basisSingleOne (Set.equivOfEq criticalPoints_neg q) := by
    simp only [Finsupp.coe_basisSingleOne, Finsupp.domLCongr_single]
  -- Both sides are `(-1) ^ ind_f p` times the coefficient of `q` in the boundary of `p` for `f`.
  simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe, hq,
    Module.Basis.toDual_apply_left, Module.Basis.toDual_apply_right,
    Finsupp.basisSingleOne_repr]
  simp only [LinearEquiv.refl_apply, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, Finsupp.coe_basisSingleOne, Finsupp.signEquiv_single,
    signedMorseBoundary_single_apply, hMS.signedMorseBoundaryCoeff_dual 𝔬 hf oM,
    Equiv.apply_symm_apply]
  simp only [Set.equivOfEq_symm_apply]
  push_cast
  ring

end IsAdaptedPseudoGradient

end TauCeti
