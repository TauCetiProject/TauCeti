/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.ChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.Opposite

/-!
# Duality for mod-two Morse homology

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n` and `X` a
Morse–Smale pseudo-gradient adapted to `f`, so that `-X` is a Morse–Smale pseudo-gradient adapted
to `-f`. The two functions have the same critical points, and a critical point of index `k` for
`-f` has index `n - k` for `f`. The trajectories of `-X` are those of `X` run backwards, so the
mod-two Morse boundary of `-f` is the transpose of the boundary of `f`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.toDual_comp_morseBoundary_neg`).

This file carries that comparison through the grading of the mod-two Morse chain complex
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplex`. The differential of the complex of
`-f` from degree `k + 1` to degree `k` is, in the bases of critical points, the transpose of the
differential of the complex of `f` from degree `n - k` to degree `n - k - 1`: the complex of `-f`
is the dual of the complex of `f`, with degrees reversed. Over the field `ZMod 2` a linear map and
its transpose have the same rank, so the two differentials have the same rank
(`IsMorseSmale.finrank_range_morseComplex_d_neg`).

The dimension of the homology in each degree is determined by the dimension of the chains and the
ranks of the two differentials at that degree. The chains of `-f` in degree `k` and those of `f`
in degree `n - k` have the same dimension, the number of critical points of `f` of index `n - k`,
so the mod-two Morse homology of `-f` in degree `k` has the dimension of that of `f` in degree
`n - k` (`IsMorseSmale.finrank_homology_morseComplex_neg`). This is the mod-two form of the
Morse-theoretic proof of Poincaré duality. With integral coefficients the comparison also involves
orientations of the unstable manifolds, which are not treated here.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `finrank_range_morseComplex_d_neg`: for `k + 1 + m = n`, the differential of the Morse complex
  of `-f` from degree `k + 1` and that of `f` from degree `m + 1` have the same rank.
* `finrank_homology_morseComplex_neg`: for `k ≤ n`, the mod-two Morse homology of `-f` in degree
  `k` has the dimension of the mod-two Morse homology of `f` in degree `n - k`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 5 (the Morse complex of `-f` is the dual complex
  and Poincaré duality).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex).
-/

public section

open Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

/-- The critical points of index `k` of `-f` are the critical points of index `m` of `f`, when
`k + m` is the dimension. -/
private noncomputable def negIndexEquiv {k m : ℕ} (hkm : k + m = finrank ℝ E) :
    {p : criticalPoints 𝓘(ℝ, E) (-f) // manifoldMorseIndex 𝓘(ℝ, E) (-f) p = k} ≃
      {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = m} :=
  (Set.equivOfEq criticalPoints_neg).subtypeEquiv fun p ↦ by
    -- At each critical point the Morse indices of `-f` and `f` add up to the dimension.
    have := (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (by simpa using p.2)).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    simp only [Set.equivOfEq_apply]
    omega

/-- **The graded boundary of `-f` is the transpose of the graded boundary of `f`.** Identify the
chains of `-f` in degree `k` with the cochains of `f` in degree `m + 1`, and those in degree
`k + 1` with the cochains in degree `m`, where `k + 1 + m = n`. Then the graded boundary of `-f`
from degree `k + 1` is the dual map of the graded boundary of `f` from degree `m + 1`. -/
private theorem toDual_comp_morseBoundaryAt_neg {k m : ℕ} (hkm : k + 1 + m = finrank ℝ E)
    [DecidableEq {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = m}]
    [DecidableEq {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = m + 1}] :
    (Finsupp.basisSingleOne.toDual ∘ₗ
        (Finsupp.domLCongr (negIndexEquiv hf (by omega : k + (m + 1) = finrank ℝ E))).toLinearMap)
          ∘ₗ (h.neg hf).morseBoundaryAt hf.neg k =
      (h.morseBoundaryAt hf m).dualMap ∘ₗ (Finsupp.basisSingleOne.toDual ∘ₗ
        (Finsupp.domLCongr (negIndexEquiv hf hkm)).toLinearMap) := by
  refine Finsupp.basisSingleOne.ext fun q ↦ Finsupp.basisSingleOne.ext fun p ↦ ?_
  have hq : Finsupp.domLCongr (M := ZMod 2) (R := ZMod 2) (negIndexEquiv hf hkm)
      (Finsupp.basisSingleOne q) = Finsupp.basisSingleOne (negIndexEquiv hf hkm q) := by
    simp only [Finsupp.coe_basisSingleOne, Finsupp.domLCongr_single]
  simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe, hq,
    Basis.toDual_apply_left, Basis.toDual_apply_right, Finsupp.basisSingleOne_repr,
    LinearEquiv.refl_apply]
  simp only [Finsupp.coe_basisSingleOne, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, morseBoundaryAt_single_apply, one_mul]
  -- Both sides are the coefficient of `q` in the boundary of `p` for `f`.
  rw [h.morseBoundaryCoeff_neg hf]
  -- The critical points on the two sides agree as points of `M`, by definition of
  -- `negIndexEquiv` and `Set.equivOfEq`.
  rfl

/-- The rank of the differential of the Morse complex from degree `k + 1` is the rank of the
graded Morse boundary from degree `k + 1`. -/
private theorem finrank_range_morseComplex_d (k : ℕ) :
    finrank (ZMod 2) (LinearMap.range ((h.morseComplex hf).d (k + 1) k).hom) =
      finrank (ZMod 2) (LinearMap.range (h.morseBoundaryAt hf k)) := by
  rw [morseComplex_d]
  -- `ModuleCat.Hom.hom (ModuleCat.ofHom g)` is `g` by definition (`ModuleCat.hom_ofHom` is proved
  -- by `rfl`); rewriting with it is blocked because the terms of the complex are only
  -- definitionally the free modules on critical points.
  rfl

/-- **The differentials of the Morse complexes of `f` and `-f` have the same rank** in
complementary degrees. For `k + 1 + m = n`, the differential of the mod-two Morse complex of `-f`
from degree `k + 1` to degree `k` is the transpose of the differential of the complex of `f` from
degree `m + 1` to degree `m`, so the two have the same rank. -/
theorem finrank_range_morseComplex_d_neg {k m : ℕ} (hkm : k + 1 + m = finrank ℝ E) :
    finrank (ZMod 2) (LinearMap.range (((h.neg hf).morseComplex hf.neg).d (k + 1) k).hom) =
      finrank (ZMod 2) (LinearMap.range ((h.morseComplex hf).d (m + 1) m).hom) := by
  classical
  have := hf.finite_criticalPoints.to_subtype
  rw [finrank_range_morseComplex_d, finrank_range_morseComplex_d,
    ← LinearMap.finrank_range_dualMap_eq_finrank_range (h.morseBoundaryAt hf m)]
  -- Composing on the right with the surjection onto the cochains of degree `m` does not change
  -- the range, and composing on the left with the injection into the cochains of degree `m + 1`
  -- does not change its dimension.
  have hsurj : LinearMap.range (Finsupp.basisSingleOne.toDual ∘ₗ
      (Finsupp.domLCongr (M := ZMod 2) (R := ZMod 2) (negIndexEquiv hf hkm)).toLinearMap) = ⊤ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Basis.toDual_range]
  have hinj : Function.Injective (Finsupp.basisSingleOne.toDual ∘ₗ
      (Finsupp.domLCongr (M := ZMod 2) (R := ZMod 2)
        (negIndexEquiv hf (by omega : k + (m + 1) = finrank ℝ E))).toLinearMap) :=
    Finsupp.basisSingleOne.toDual_injective.comp (Finsupp.domLCongr _).injective
  rw [← LinearMap.range_comp_of_range_eq_top (h.morseBoundaryAt hf m).dualMap hsurj,
    ← h.toDual_comp_morseBoundaryAt_neg hf hkm, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq

/-- A differential of the Morse complex leaving a degree above the dimension has rank zero. -/
private theorem finrank_range_morseComplex_d_eq_zero {i j : ℕ} (hi : finrank ℝ E < i) :
    finrank (ZMod 2) (LinearMap.range ((h.morseComplex hf).d i j).hom) = 0 := by
  refine Nat.eq_zero_of_le_zero ((LinearMap.finrank_range_le _).trans_eq ?_)
  rw [finrank_morseComplex_X, criticalCount_eq_zero_of_finrank_lt hi, ENat.toNat_zero]

/-- The chains of `-f` in degree `k` and those of `f` in degree `n - k` have the same dimension,
the number of critical points of `f` of index `n - k`. -/
private theorem finrank_morseComplex_X_neg {k : ℕ} (hk : k ≤ finrank ℝ E) :
    finrank (ZMod 2) (((h.neg hf).morseComplex hf.neg).X k) =
      finrank (ZMod 2) ((h.morseComplex hf).X (finrank ℝ E - k)) := by
  rw [finrank_morseComplex_X, finrank_morseComplex_X, hf.criticalCount_neg hk]

/-- **Duality for mod-two Morse homology.** On a compact boundaryless manifold of dimension `n`,
the mod-two Morse homology of `-f` for `-X` in degree `k ≤ n` has the dimension of the mod-two
Morse homology of `f` for `X` in degree `n - k`. -/
theorem finrank_homology_morseComplex_neg {k : ℕ} (hk : k ≤ finrank ℝ E) :
    finrank (ZMod 2) (((h.neg hf).morseComplex hf.neg).homology k) =
      finrank (ZMod 2) ((h.morseComplex hf).homology (finrank ℝ E - k)) := by
  have hX := h.finrank_morseComplex_X_neg hf hk
  -- Each homology dimension is the chain dimension minus the ranks of the two differentials at
  -- that degree; the ranks match by `finrank_range_morseComplex_d_neg`, and the ranks of the
  -- differentials leaving degrees above the dimension vanish.
  rcases k with _ | j
  · rw [((h.neg hf).morseComplex hf.neg).finrank_X_zero] at hX
    rw [Nat.sub_zero] at hX ⊢
    have h₀ := (h.neg hf).finrank_range_morseComplex_d_eq_zero hf.neg (i := 1) (j := 0)
    rcases hn : finrank ℝ E with _ | m
    · rw [hn, (h.morseComplex hf).finrank_X_zero] at hX
      have h₁ := h.finrank_range_morseComplex_d_eq_zero hf (i := 1) (j := 0) (by omega)
      have := h₀ (by omega)
      omega
    · rw [hn, (h.morseComplex hf).finrank_X_succ m] at hX
      have hK := h.finrank_range_morseComplex_d_neg hf (k := 0) (m := m) (by omega)
      rw [zero_add] at hK
      have h₁ := h.finrank_range_morseComplex_d_eq_zero hf (i := m + 2) (j := m + 1) (by omega)
      omega
  · rw [((h.neg hf).morseComplex hf.neg).finrank_X_succ j] at hX
    rcases hm : finrank ℝ E - (j + 1) with _ | m
    · rw [hm, (h.morseComplex hf).finrank_X_zero] at hX
      have hK := h.finrank_range_morseComplex_d_neg hf (k := j) (m := 0) (by omega)
      rw [zero_add] at hK
      have h₁ := (h.neg hf).finrank_range_morseComplex_d_eq_zero hf.neg (i := j + 2)
        (j := j + 1) (by omega)
      omega
    · rw [hm, (h.morseComplex hf).finrank_X_succ m] at hX
      have hK₁ := h.finrank_range_morseComplex_d_neg hf (k := j) (m := m + 1) (by omega)
      have hK₂ := h.finrank_range_morseComplex_d_neg hf (k := j + 1) (m := m) (by omega)
      rw [show m + 1 + 1 = m + 2 by omega] at hK₁
      rw [show j + 1 + 1 = j + 2 by omega] at hK₂
      omega

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
