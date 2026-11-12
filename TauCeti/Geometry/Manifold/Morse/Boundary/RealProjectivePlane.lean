/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.UniqueExtremum
public import TauCeti.Geometry.Manifold.Morse.Projectivization

/-!
# The mod-two Morse complex of the real projective plane

On the real projective plane `ℝℙ² = ℙ ℝ (Fin 3 → ℝ)`, the moment function
`[v] ↦ (∑ i, w i * v i ^ 2) / ∑ i, v i ^ 2` with three distinct weights `w` is a Morse function
(`TauCeti.isMorse_projectiveMomentFunction`) with one critical point of each index `0`, `1` and
`2` (`TauCeti.criticalCount_projectiveMomentFunction_real`): a minimum, a saddle and a maximum.
This file computes the trajectories between them and the mod-two Morse complex, for every
pseudo-gradient `X` adapted to this function.

* `X` is Morse–Smale, whatever its choice. The saddle is the only critical point whose index is
  neither `0` nor `2`, so `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.of_subsingleton` applies.
* There are exactly two trajectories from the maximum to the saddle and exactly two from the
  saddle to the minimum. The stable manifold of the saddle is a line, whose two halves both come
  from the only critical point of index `2`; its unstable manifold is a line, whose two halves both
  go to the only critical point of index `0`.
* So the mod-two Morse boundary vanishes, and the mod-two Morse complex is `𝔽₂ → 𝔽₂ → 𝔽₂` with
  zero differentials, whose homology is the mod-two homology of `ℝℙ²`.

Over `ℤ` the same two pairs of trajectories give the differentials `±2` from the maximum to the
saddle and `0` from the saddle to the minimum, recovering `H₁(ℝℙ²; ℤ) = ℤ/2`: the two trajectories
into the saddle carry the same sign and the two out of it opposite signs. Those signs come from
orientations of the unstable manifolds, which the mod-two complex does not see.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `isMorseSmale_projectiveMomentFunction_real`: every pseudo-gradient adapted to the moment
  function on `ℝℙ²` is Morse–Smale.
* `ncard_morseTrajectorySlice_projectiveMomentFunction_real`: between critical points whose indices
  differ by one there are exactly two trajectories.
* `IsMorseSmale.morseBoundary_projectiveMomentFunction_real`: the mod-two Morse boundary is zero.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the real projective plane).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the Morse complex of `ℝℙ²`).
-/

public section

open Function
open scoped LinearAlgebra.Projectivization Manifold

namespace TauCeti

variable {w : Fin 3 → ℝ}

namespace IsAdaptedPseudoGradient

variable {X : (x : ℙ ℝ (Fin 3 → ℝ)) → TangentSpace 𝓘(ℝ, Fin 2 → ℝ) x}

/-- **The moment function on `ℝℙ²` is Morse–Smale for every pseudo-gradient.** For distinct
weights, every pseudo-gradient adapted to the moment function on the real projective plane
satisfies the Morse–Smale condition: its saddle is its only critical point of index neither `0`
nor `2`. -/
theorem isMorseSmale_projectiveMomentFunction_real (hw : Injective w)
    (hX : IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X) : hX.IsMorseSmale := by
  refine IsMorseSmale.of_subsingleton (isMorse_projectiveMomentFunction hw)
    ((subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw 1).anti ?_)
  rintro x ⟨hx, hx0, hx2⟩
  have hle : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) x ≤ 2 :=
    manifoldMorseIndex_le_finrank.trans_eq (Module.finrank_fin_fun ℝ)
  rw [Module.finrank_fin_fun] at hx2
  exact ⟨hx, by omega⟩

/-- **Two trajectories between consecutive indices on `ℝℙ²`.** For distinct weights and every
pseudo-gradient adapted to the moment function on the real projective plane, there are exactly two
trajectories from a critical point `p` to a critical point `q` of index one less: from the maximum
to the saddle, and from the saddle to the minimum. -/
theorem ncard_morseTrajectorySlice_projectiveMomentFunction_real (hw : Injective w)
    (hX : IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X) {p q : ℙ ℝ (Fin 3 → ℝ)}
    (hp : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ) (projectiveMomentFunction ℝ w) p = 0)
    (hq : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ) (projectiveMomentFunction ℝ w) q = 0)
    (hpq : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p =
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q + 1) :
    (hX.morseTrajectorySlice p q).ncard = 2 := by
  have h := hX.isMorseSmale_projectiveMomentFunction_real hw
  have hf := isMorse_projectiveMomentFunction (𝕜 := ℝ) hw
  have hsub := subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw
  have hle : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p ≤ 2 :=
    manifoldMorseIndex_le_finrank.trans_eq (Module.finrank_fin_fun ℝ)
  -- Either `p` is the maximum and `q` the saddle, or `q` is the minimum and `p` the saddle.
  obtain hp2 | hq0 : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = 2 ∨
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q = 0 := by omega
  · refine h.ncard_morseTrajectorySlice_eq_two_of_unique_index_finrank hf hq
      (by rw [Module.finrank_fin_fun]; omega) fun y hy hy2 ↦ hsub 2 ⟨hy, ?_⟩ ⟨hp, hp2⟩
    rwa [Module.finrank_fin_fun] at hy2
  · exact h.ncard_morseTrajectorySlice_eq_two_of_unique_index_zero hf hp (by omega)
      fun y hy hy0 ↦ hsub 0 ⟨hy, hy0⟩ ⟨hq, hq0⟩

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X} (h : hX.IsMorseSmale)
  (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))

/-- **The mod-two Morse boundary of `ℝℙ²` is zero.** For every pseudo-gradient adapted to the
moment function on the real projective plane, the mod-two Morse complex is the free
`ZMod 2`-module on the minimum, the saddle and the maximum, with zero differential. -/
@[simp]
theorem morseBoundary_projectiveMomentFunction_real : h.morseBoundary hf = 0 := by
  have hw := isMorse_projectiveMomentFunction_iff.1 hf
  exact h.morseBoundary_eq_zero_of_finrank_eq_two hf (Module.finrank_fin_fun ℝ)
    (subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw 2)
    (subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw 0)

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
