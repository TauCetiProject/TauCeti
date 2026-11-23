/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
import TauCeti.Geometry.Manifold.Morse.Boundary.Augmentation
import TauCeti.Geometry.Manifold.Morse.Stable.Frontier
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice

/-!
# One trajectory from each of two critical points of top index

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, and `X` a
pseudo-gradient adapted to `f`. Let `q` be a critical point of index `n - 1` such that every other
critical point has index `0` or `n`, and suppose that `M` minus its critical points of index `0` is
connected. Then `X` is Morse–Smale, and the stable manifold `W^s(q)` is `q` together with two
trajectories, each coming from a critical point of index `n`
(`IsMorseSmale.exists_morseTrajectorySlice_eq_image_of_add_one_eq_finrank`). Every critical point
of index `n` sends one of them (`exists_mem_unstableSet_inter_stableSet_ne_of_isPreconnected`).
So if `f` has two critical points of index `n`, exactly one trajectory runs from each of them to
`q`. This is the trajectory count behind the Morse complex of the sphere with two maxima, a saddle
and a minimum, where each maximum has boundary `±` the saddle. With a single critical point of
index `n`, both trajectories come from it
(`IsMorseSmale.ncard_morseTrajectorySlice_eq_two_of_unique_index_finrank`).

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `ncard_morseTrajectorySlice_eq_one_of_isPreconnected`: with two critical points of index `n`,
  exactly one trajectory runs from each of them to `q`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the Morse complex of the sphere with two maxima, a saddle
  and a minimum).
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

variable (hX : IsAdaptedPseudoGradient f X)

/-- **One trajectory from each of two critical points of top index.** Let `q` be a critical point
of index `n - 1` such that every other critical point has index `0` or `n`, suppose that `M` minus
its critical points of index `0` is connected, and let `m₁ ≠ m₂` be critical points of index `n`.
Then exactly one trajectory runs from `m₁` to `q`: the stable manifold `W^s(q)` is `q` together with
two trajectories, and each of `m₁` and `m₂` sends one of them to `q`. -/
theorem ncard_morseTrajectorySlice_eq_one_of_isPreconnected (hf : IsMorse 𝓘(ℝ, E) f)
    {q m₁ m₂ : M} (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hqind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E)
    (hcrit : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → y ≠ q →
      manifoldMorseIndex 𝓘(ℝ, E) f y = 0 ∨ manifoldMorseIndex 𝓘(ℝ, E) f y = finrank ℝ E)
    (hconn : IsPreconnected {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f y = 0}ᶜ)
    (hm₁ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f m₁ = 0)
    (hm₁ind : manifoldMorseIndex 𝓘(ℝ, E) f m₁ = finrank ℝ E)
    (hm₂ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f m₂ = 0)
    (hm₂ind : manifoldMorseIndex 𝓘(ℝ, E) f m₂ = finrank ℝ E) (hm : m₁ ≠ m₂) :
    (hX.morseTrajectorySlice m₁ q).ncard = 1 := by
  -- `q` is the only critical point of index neither `0` nor `n`, so `X` is Morse–Smale.
  have h : hX.IsMorseSmale := IsMorseSmale.of_subsingleton hf
    (subsingleton_singleton (a := q) |>.anti fun y ⟨hy, hy0, hyn⟩ ↦
      mem_singleton_iff.2 (by_contra fun hyq ↦ (hcrit y hy hyq).elim hy0 hyn))
  obtain ⟨w, a, -, -, -, -, hslice⟩ :=
    h.exists_morseTrajectorySlice_eq_image_of_add_one_eq_finrank hf hq hqind
  -- Each critical point `m` of index `n` sends a trajectory to `q`, so it is one of the `a i`.
  have hrange {m : M} (hm : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f m = 0)
      (hmind : manifoldMorseIndex 𝓘(ℝ, E) f m = finrank ℝ E) : m ≠ q ∧ ∃ i, a i = m := by
    have hmq : m ≠ q := by
      rintro rfl
      omega
    obtain ⟨y, hy, -⟩ := hX.exists_mem_unstableSet_inter_stableSet_ne_of_isPreconnected hf hq
      hqind hcrit hconn hm hmind
    obtain ⟨τ, hτ, -⟩ := hX.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet hmq hy
    have hmem : hX.flow τ y ∈ hX.morseTrajectorySlice m q :=
      (mem_morseTrajectorySlice _).2 ⟨(Flow.apply_mem_unstableSet_iff _ τ).2 hy.1,
        (Flow.apply_mem_stableSet_iff _ τ).2 hy.2, hτ⟩
    rw [hslice m hmq] at hmem
    obtain ⟨i, hi, -⟩ := hmem
    exact ⟨hmq, i, hi⟩
  obtain ⟨hm₁q, i₁, hi₁⟩ := hrange hm₁ hm₁ind
  obtain ⟨-, i₂, hi₂⟩ := hrange hm₂ hm₂ind
  -- The other trajectory comes from `m₂`, so only the `i₁`-th one comes from `m₁`.
  have hsingle : {i | a i = m₁} = {i₁} := by
    refine eq_singleton_iff_unique_mem.2 ⟨hi₁, fun j hj ↦ ?_⟩
    have hij : i₁ ≠ i₂ := fun he ↦ hm (hi₁.symm.trans (he ▸ hi₂))
    by_contra hji
    have hj₂ : j = i₂ := by omega
    exact hm (hj.symm.trans (hj₂ ▸ hi₂))
  rw [hslice m₁ hm₁q, hsingle, image_singleton, ncard_singleton]

end IsAdaptedPseudoGradient

end TauCeti
