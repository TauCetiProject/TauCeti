/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.ChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.Opposite
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Poincaré duality for mod-two Morse homology

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `m` and `X` a
Morse–Smale pseudo-gradient adapted to `f`. Then `-X` is a Morse–Smale pseudo-gradient adapted to
`-f`, the two functions have the same critical points, and a critical point of index `k` for `f`
has index `m - k` for `-f` (`TauCeti.IsMorse.criticalPointsIndexNegEquiv`). The mod-two Morse
boundary of `-f` is the transpose of that of `f`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.toDual_comp_morseBoundary_neg`). This file refines
it to the graded complexes: identifying the chains of `-f` of index `k` with the cochains of `f`
of index `m - k`, the differential of the Morse complex of `-f` from degree `j + 1` to degree `j`
is the dual map of the differential of the Morse complex of `f` from degree `n + 1` to degree `n`,
where `j + n + 1 = m`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.toDual_comp_morseBoundaryAt_neg`). So the Morse
complex of `-f` is the dual of the Morse complex of `f`, read with the complementary grading. The
consequence for Morse homology is Poincaré duality for mod-two Morse homology: the mod-two Morse
homology of `-f` in degree `k ≤ m` has the dimension of the mod-two Morse homology of `f` in
degree `m - k` (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.finrank_homology_morseComplex_neg`).

The homology statement is linear algebra on the two chain complexes. A linear map and its dual map
have the same rank, so the differentials of `-f` and `f` exchanged by the identification have the
same rank (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.finrank_range_morseBoundaryAt_neg`). By
rank–nullity (`ChainComplex.finrank_X`), the dimension of the homology in degree `k` is the number
of critical points of index `k` minus the ranks of the differentials out of and into degree `k`.
Under `k ↦ m - k` the numbers of critical points agree (`TauCeti.IsMorse.criticalCount_neg`) and
the two ranks are exchanged.

Over the integers the corresponding comparison of the Morse complex of `-f` with the dual of the
integral Morse complex of `f` involves the orientations of the unstable manifolds, and is not
treated here.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `toDual_comp_morseBoundaryAt_neg`: identifying the chains of `-f` of index `k` with the cochains
  of `f` of index `m - k`, the graded boundary of `-f` is the dual map of the graded boundary of
  `f`.
* `finrank_range_morseBoundaryAt_neg`: the graded boundary of `-f` from index `j + 1` to `j` has
  the rank of the graded boundary of `f` from index `n + 1` to `n`, when `j + n + 1 = m`.
* `finrank_homology_morseComplex_neg`: the mod-two Morse homology of `-f` in degree `k ≤ m` has
  the dimension of the mod-two Morse homology of `f` in degree `m - k`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 5 (the Morse complex of `-f` is the dual complex
  and Poincaré duality).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex).
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

/-- **The graded Morse complex of `-f` is the dual of that of `f`, with the complementary
grading.** Let `j + n + 1` be the dimension of `M`. The critical points of index `j` and `j + 1`
for `-f` are those of index `n + 1` and `n` for `f`
(`TauCeti.IsMorse.criticalPointsIndexNegEquiv`). Identify a mod-two chain of `-f` of index `j`
(resp. `j + 1`) with a cochain of `f` of index `n + 1` (resp. `n`), sending each critical point to
the dual basis vector of the same critical point. Under these identifications the graded boundary
of `-f` from index `j + 1` to index `j` is the dual map of the graded boundary of `f` from index
`n + 1` to index `n`, that is, the graded Morse coboundary of `f`. -/
theorem toDual_comp_morseBoundaryAt_neg [DecidableEq (criticalPoints 𝓘(ℝ, E) f)] {j n : ℕ}
    (hjn : j + n + 1 = finrank ℝ E) :
    Finsupp.basisSingleOne.toDual ∘ₗ
        (Finsupp.domLCongr (hf.criticalPointsIndexNegEquiv (j := j) (k := n + 1)
          (by omega))).toLinearMap ∘ₗ (h.neg hf).morseBoundaryAt hf.neg j =
      (h.morseBoundaryAt hf n).dualMap ∘ₗ Finsupp.basisSingleOne.toDual ∘ₗ
        (Finsupp.domLCongr (hf.criticalPointsIndexNegEquiv (j := j + 1) (k := n)
          (by omega))).toLinearMap := by
  refine Finsupp.basisSingleOne.ext fun q ↦ Finsupp.basisSingleOne.ext fun p ↦ ?_
  obtain ⟨p, rfl⟩ := (hf.criticalPointsIndexNegEquiv (j := j) (k := n + 1) (by omega)).surjective p
  have hq {i k : ℕ} (hik : i + k = finrank ℝ E) (q) :
      Finsupp.domLCongr (M := ZMod 2) (R := ZMod 2) (hf.criticalPointsIndexNegEquiv hik)
        (Finsupp.basisSingleOne q) =
        Finsupp.basisSingleOne (hf.criticalPointsIndexNegEquiv hik q) := by
    simp only [Finsupp.coe_basisSingleOne, Finsupp.domLCongr_single]
  -- Both sides are the coefficient of `q` in the boundary of `p` for `f`.
  simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe, hq,
    Basis.toDual_apply_left, Basis.toDual_apply_right, Finsupp.basisSingleOne_repr]
  simp only [Finsupp.coe_basisSingleOne, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    LinearEquiv.refl_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
    morseBoundaryAt_single_apply, one_mul, h.morseBoundaryCoeff_neg hf]
  congr 1 <;> ext <;> simp

/-- **The graded boundaries of `f` and `-f` have the same ranks.** If `j + n + 1` is the dimension
of `M`, the graded mod-two Morse boundary of `-f` from index `j + 1` to index `j` has the rank of
the graded boundary of `f` from index `n + 1` to index `n`. -/
theorem finrank_range_morseBoundaryAt_neg {j n : ℕ} (hjn : j + n + 1 = finrank ℝ E) :
    finrank (ZMod 2) (LinearMap.range ((h.neg hf).morseBoundaryAt hf.neg j)) =
      finrank (ZMod 2) (LinearMap.range (h.morseBoundaryAt hf n)) := by
  classical
  have := hf.finite_criticalPoints.to_subtype
  -- The identifications of `toDual_comp_morseBoundaryAt_neg` are linear equivalences, under which
  -- the boundary of `-f` is the dual map of the boundary of `f`, which has the same rank.
  let e (i k : ℕ) (hik : i + k = finrank ℝ E) :=
    (Finsupp.domLCongr (M := ZMod 2) (R := ZMod 2) (hf.criticalPointsIndexNegEquiv hik)).trans
      Finsupp.basisSingleOne.toDualEquiv
  have key : (e j (n + 1) (by omega)).toLinearMap ∘ₗ (h.neg hf).morseBoundaryAt hf.neg j =
      (h.morseBoundaryAt hf n).dualMap ∘ₗ (e (j + 1) n (by omega)).toLinearMap :=
    h.toDual_comp_morseBoundaryAt_neg hf hjn
  rw [← LinearEquiv.finrank_map_eq (e j (n + 1) (by omega)), ← LinearMap.range_comp, key,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearMap.finrank_range_dualMap_eq_finrank_range]

/-- The differential of the Morse chain complex out of degree `n + 1` has the rank of the graded
boundary `morseBoundaryAt`. -/
private theorem finrank_range_morseComplex_d (n : ℕ) :
    finrank (ZMod 2) (LinearMap.range ((h.morseComplex hf).d (n + 1) n).hom) =
      finrank (ZMod 2) (LinearMap.range (h.morseBoundaryAt hf n)) := by
  have hd : ((h.morseComplex hf).d (n + 1) n).hom = h.morseBoundaryAt hf n :=
    LinearMap.ext (h.morseComplex_d_apply hf n)
  rw [hd]
  -- The two sides differ only in how the codomain of the boundary is written.
  rfl

/-- A differential of the Morse chain complex out of a degree above the dimension of `M` has rank
zero, since its source vanishes. -/
private theorem finrank_range_morseComplex_d_of_finrank_lt {i j : ℕ} (hi : finrank ℝ E < i) :
    finrank (ZMod 2) (LinearMap.range ((h.morseComplex hf).d i j).hom) = 0 := by
  rw [(h.isZero_morseComplex_X_of_finrank_lt hf hi).eq_of_src ((h.morseComplex hf).d i j) 0,
    ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]

/-- The differential of the Morse chain complex from degree `0` to degree `0` is zero. -/
private theorem finrank_range_morseComplex_d_zero :
    finrank (ZMod 2) (LinearMap.range ((h.morseComplex hf).d 0 0).hom) = 0 := by
  rw [(h.morseComplex hf).shape 0 0 (by simp), ModuleCat.hom_zero, LinearMap.range_zero,
    finrank_bot]

/-- The differential of the Morse complex of `-f` out of degree `k` has the rank of the
differential of the Morse complex of `f` into degree `m - k`. -/
private theorem finrank_range_morseComplex_neg_d_succ {k : ℕ} (hk : k ≤ finrank ℝ E) :
    finrank (ZMod 2) (LinearMap.range (((h.neg hf).morseComplex hf.neg).d (k + 1) k).hom) =
      finrank (ZMod 2) (LinearMap.range
        ((h.morseComplex hf).d (finrank ℝ E - k) (finrank ℝ E - k - 1)).hom) := by
  obtain rfl | hk := hk.eq_or_lt
  · rw [finrank_range_morseComplex_d_of_finrank_lt (h.neg hf) hf.neg (Nat.lt_succ_self _),
      Nat.sub_self, Nat.zero_sub, finrank_range_morseComplex_d_zero h hf]
  · obtain ⟨n, hn⟩ : ∃ n, finrank ℝ E - k = n + 1 := ⟨finrank ℝ E - k - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel, finrank_range_morseComplex_d (h.neg hf) hf.neg,
      finrank_range_morseComplex_d h hf, h.finrank_range_morseBoundaryAt_neg hf (n := n) (by omega)]

/-- The differential of the Morse complex of `-f` into degree `k` has the rank of the
differential of the Morse complex of `f` out of degree `m - k`. -/
private theorem finrank_range_morseComplex_neg_d {k : ℕ} (hk : k ≤ finrank ℝ E) :
    finrank (ZMod 2) (LinearMap.range (((h.neg hf).morseComplex hf.neg).d k (k - 1)).hom) =
      finrank (ZMod 2) (LinearMap.range
        ((h.morseComplex hf).d (finrank ℝ E - k + 1) (finrank ℝ E - k)).hom) := by
  cases k with
  | zero =>
    rw [Nat.zero_sub, finrank_range_morseComplex_d_zero (h.neg hf) hf.neg, Nat.sub_zero,
      finrank_range_morseComplex_d_of_finrank_lt h hf (Nat.lt_succ_self _)]
  | succ k =>
    rw [Nat.add_sub_cancel, finrank_range_morseComplex_d (h.neg hf) hf.neg,
      finrank_range_morseComplex_d h hf,
      h.finrank_range_morseBoundaryAt_neg hf (n := finrank ℝ E - (k + 1)) (by omega)]

/-- **Poincaré duality for mod-two Morse homology.** On a compact boundaryless manifold of
dimension `m`, for `k ≤ m`, the mod-two Morse homology of `-f` and `-X` in degree `k` has the
dimension of the mod-two Morse homology of `f` and `X` in degree `m - k`. -/
theorem finrank_homology_morseComplex_neg {k : ℕ} (hk : k ≤ finrank ℝ E) :
    finrank (ZMod 2) (((h.neg hf).morseComplex hf.neg).homology k) =
      finrank (ZMod 2) ((h.morseComplex hf).homology (finrank ℝ E - k)) := by
  -- Rank–nullity in degree `k` for `-f` and in degree `m - k` for `f`: the numbers of critical
  -- points agree, and the ranks of the differentials out of and into the degree are exchanged.
  have h₁ := ((h.neg hf).morseComplex hf.neg).finrank_X k
  have h₂ := (h.morseComplex hf).finrank_X (finrank ℝ E - k)
  rw [finrank_morseComplex_X (h.neg hf) hf.neg, hf.criticalCount_neg hk,
    finrank_range_morseComplex_neg_d_succ h hf hk, finrank_range_morseComplex_neg_d h hf hk] at h₁
  rw [finrank_morseComplex_X h hf] at h₂
  omega

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
