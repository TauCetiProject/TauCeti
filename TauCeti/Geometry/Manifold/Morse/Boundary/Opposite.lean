/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Square
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# The mod-two Morse boundary of the opposite function

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n` and `X` a
Morse–Smale pseudo-gradient adapted to `f`. Then `-X` is a Morse–Smale pseudo-gradient adapted to
`-f` (`TauCeti.IsAdaptedPseudoGradient.neg`, `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.neg`).
The two functions have the same critical points, and at a critical point their Morse indices add
up to `n`. The flow of `-X` is the flow of `X` run backwards, so the trajectories of `-X` from `q`
to `p` are the trajectories of `X` from `p` to `q`
(`TauCeti.IsAdaptedPseudoGradient.neg_morseTrajectorySlice`).

Consequently the mod-two Morse boundary of `-f` is the transpose of that of `f`: the coefficient
of `p` in the boundary of `q` for `-f` is the coefficient of `q` in the boundary of `p` for `f`.
Identifying the chains of `-f` with the cochains of `f` through the basis of critical points, the
boundary of `-f` is the dual map of the boundary of `f`, the Morse coboundary. Since a critical
point of index `k` for `-f` has index `n - k` for `f`, this matches the chains of `-f` in index `k`
with the cochains of `f` in index `n - k`. This is the
mod-two form of the comparison between the Morse complex of `-f` and the dual of the Morse complex
of `f`, which underlies the Morse-theoretic proof of Poincaré duality. With integral coefficients
the comparison also involves orientations of the unstable manifolds, which are not treated here.

Reversing broken trajectories in the same way, `∂ ∘ ∂ = 0` holds for `-f` exactly when it holds
for `f`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `mem_morseBrokenTrajectorySet_neg`, `ncard_morseBrokenTrajectorySet_neg`: the broken
  trajectories of `-X` from `r` to `p` are those of `X` from `p` to `r`, with their two components
  exchanged.
* `IsMorseSmale.morseBoundaryCoeff_neg`, `IsMorseSmale.morseBoundary_neg_single_apply`: the
  coefficient of `p` in the boundary of `q` for `-f` is the coefficient of `q` in the boundary of
  `p` for `f`.
* `IsMorseSmale.toDual_comp_morseBoundary_neg`: the boundary of `-f` is the dual map of the
  boundary of `f`.
* `IsMorseSmale.morseBoundary_neg_comp_morseBoundary_neg_eq_zero_iff`: the boundary of `-f`
  squares to zero exactly when the boundary of `f` does.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 5 (the Morse complex of `-f` is the dual complex
  and Poincaré duality).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex).
-/

public section

open Set Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) (hf : IsMorse 𝓘(ℝ, E) f)

/-- **Reversed broken trajectories.** A triple `(q, z₁, z₂)` is a broken trajectory of `-X` from
`r` to `p` exactly when `(q, z₂, z₁)` is a broken trajectory of `X` from `p` to `r`: reversing the
flow reverses each component and the order in which they are traversed. -/
theorem mem_morseBrokenTrajectorySet_neg {p r : criticalPoints 𝓘(ℝ, E) f}
    {x : criticalPoints 𝓘(ℝ, E) (-f) × M × M} :
    x ∈ (hX.neg hf).morseBrokenTrajectorySet r p ↔
      (Set.equivOfEq criticalPoints_neg x.1, x.2.2, x.2.1) ∈ hX.morseBrokenTrajectorySet p r := by
  -- At each critical point the Morse indices of `-f` and `f` add up to the dimension.
  have hp := (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
    p.2).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  have hr := (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
    r.2).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  have hq := (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
    (by simpa using x.1.2)).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  simp only [mem_morseBrokenTrajectorySet, Set.equivOfEq_apply]
  rw [hX.neg_morseTrajectorySlice hf, hX.neg_morseTrajectorySlice hf]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨by omega, by omega, h₄, h₃⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨by omega, by omega, h₄, h₃⟩

/-- There are as many broken trajectories of `-X` from `r` to `p` as broken trajectories of `X`
from `p` to `r`. -/
theorem ncard_morseBrokenTrajectorySet_neg (p r : criticalPoints 𝓘(ℝ, E) f) :
    ((hX.neg hf).morseBrokenTrajectorySet r p).ncard = (hX.morseBrokenTrajectorySet p r).ncard := by
  let e := (Set.equivOfEq (criticalPoints_neg (I := 𝓘(ℝ, E)) (f := f))).prodCongr
    (Equiv.prodComm M M)
  have hpre : (hX.neg hf).morseBrokenTrajectorySet r p = e ⁻¹' hX.morseBrokenTrajectorySet p r := by
    ext x
    exact hX.mem_morseBrokenTrajectorySet_neg hf
  rw [hpre, ncard_preimage_of_injective_subset_range e.injective (by simp [e.range_eq_univ])]

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale)

/-- **The boundary coefficients of the opposite function.** The coefficient of `p` in the mod-two
Morse boundary of `q` for `-f` and `-X` is the coefficient of `q` in the boundary of `p` for `f`
and `X`. Both count, modulo two, the trajectories of `X` from `p` to `q`, and the index condition
`ind_{-f} q = ind_{-f} p + 1` is the condition `ind_f p = ind_f q + 1`. -/
theorem morseBoundaryCoeff_neg (q p : criticalPoints 𝓘(ℝ, E) (-f)) :
    (h.neg hf).morseBoundaryCoeff hf.neg q p =
      h.morseBoundaryCoeff hf (Set.equivOfEq criticalPoints_neg p)
        (Set.equivOfEq criticalPoints_neg q) := by
  -- At each critical point the Morse indices of `-f` and `f` add up to the dimension.
  have hp := (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
    (by simpa using p.2)).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  have hq := (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
    (by simpa using q.2)).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  simp only [Set.equivOfEq_apply]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [(h.neg hf).morseBoundaryCoeff_eq_ncard hf.neg (by omega),
      h.morseBoundaryCoeff_eq_ncard hf hind, hX.neg_morseTrajectorySlice hf]
  · rw [(h.neg hf).morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf.neg (by omega),
      h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf hind]

/-- The coefficient of `p` in the mod-two Morse boundary of `a • q` for `-f` and `-X` is the
coefficient of `q` in the boundary of `a • p` for `f` and `X`. -/
theorem morseBoundary_neg_single_apply (q p : criticalPoints 𝓘(ℝ, E) (-f)) (a : ZMod 2) :
    (h.neg hf).morseBoundary hf.neg (Finsupp.single q a) p =
      h.morseBoundary hf (Finsupp.single (Set.equivOfEq criticalPoints_neg p) a)
        (Set.equivOfEq criticalPoints_neg q) := by
  rw [morseBoundary_single_apply, morseBoundary_single_apply, h.morseBoundaryCoeff_neg hf]

/-- **The boundary of the opposite function is the Morse coboundary.** Identify a mod-two chain of
`-f` with a cochain of `f`, sending each critical point to the dual basis vector of the same
critical point (`Module.Basis.toDual` for the standard basis of finitely supported functions).
Under this identification the mod-two Morse boundary of `-f` for `-X` is the dual map of the
boundary of `f` for `X`. A critical point of index `k` for `-f` has index `n - k` for `f`, where
`n` is the dimension, so this matches the chains of `-f` in index `k` with the cochains of `f` in
index `n - k`. -/
theorem toDual_comp_morseBoundary_neg [DecidableEq (criticalPoints 𝓘(ℝ, E) f)] :
    Finsupp.basisSingleOne.toDual ∘ₗ
        (Finsupp.domLCongr (Set.equivOfEq criticalPoints_neg)).toLinearMap ∘ₗ
          (h.neg hf).morseBoundary hf.neg =
      (h.morseBoundary hf).dualMap ∘ₗ Finsupp.basisSingleOne.toDual ∘ₗ
        (Finsupp.domLCongr (Set.equivOfEq criticalPoints_neg)).toLinearMap := by
  refine Finsupp.basisSingleOne.ext fun q ↦ Finsupp.basisSingleOne.ext fun p ↦ ?_
  have hq : Finsupp.domLCongr (M := ZMod 2) (R := ZMod 2) (Set.equivOfEq criticalPoints_neg)
      (Finsupp.basisSingleOne q) = Finsupp.basisSingleOne (Set.equivOfEq criticalPoints_neg q) := by
    simp only [Finsupp.coe_basisSingleOne, Finsupp.domLCongr_single]
  -- Both sides are the coefficient of `q` in the boundary of `p` for `f`.
  simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe, hq,
    Basis.toDual_apply_left, Basis.toDual_apply_right, Finsupp.basisSingleOne_repr]
  simp [h.morseBoundary_neg_single_apply hf]

/-- **`∂² = 0` for the opposite function.** The mod-two Morse boundary of `-f` for `-X` squares to
zero exactly when the boundary of `f` for `X` does: both conditions say that the broken
index-two trajectories of `X` between any two critical points are even in number. -/
theorem morseBoundary_neg_comp_morseBoundary_neg_eq_zero_iff :
    (h.neg hf).morseBoundary hf.neg ∘ₗ (h.neg hf).morseBoundary hf.neg = 0 ↔
      h.morseBoundary hf ∘ₗ h.morseBoundary hf = 0 := by
  rw [(h.neg hf).morseBoundary_comp_morseBoundary_eq_zero_iff hf.neg,
    h.morseBoundary_comp_morseBoundary_eq_zero_iff hf]
  refine ⟨fun H p r ↦ ?_, fun H r p ↦ ?_⟩
  · simpa [hX.ncard_morseBrokenTrajectorySet_neg hf p r] using
      H ((Set.equivOfEq criticalPoints_neg).symm r) ((Set.equivOfEq criticalPoints_neg).symm p)
  · have hn := hX.ncard_morseBrokenTrajectorySet_neg hf (Set.equivOfEq criticalPoints_neg p)
      (Set.equivOfEq criticalPoints_neg r)
    simp only [Set.equivOfEq_apply] at hn
    simpa [hn] using H (Set.equivOfEq criticalPoints_neg p) (Set.equivOfEq criticalPoints_neg r)

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
