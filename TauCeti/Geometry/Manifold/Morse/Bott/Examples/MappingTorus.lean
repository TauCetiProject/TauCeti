/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.MappingTorus
public import TauCeti.Geometry.Manifold.Morse.Sphere.Prod

/-!
# A Morse–Bott function with four critical circles on a mapping torus of `Sⁿ × Sᵐ`

On the product `Sⁿ × Sᵐ` of unit spheres, with unit vectors `v` and `w` and a real `ε > 0`, the
function

`g (x, y) = ⟪x, v⟫ + ε ⟪y, w⟫`

(the height `TauCeti.sphereHeight v` on the first factor plus `ε` times the height on the second)
is a Morse function (`TauCeti.isMorse_sphereHeight_comp_fst_add_mul_comp_snd`, in
`TauCeti.Geometry.Manifold.Morse.Sphere.Prod`). Its critical points are the four pairs of poles
`(±v, ±w)` (`TauCeti.criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd`), with Morse indices
`n + m`, `n`, `m` and `0` at `(v, w)`, `(v, -w)`, `(-v, w)` and `(-v, -w)`
(`TauCeti.manifoldMorseIndex_sphereHeight_comp_fst_add_mul_comp_snd`, together with
`TauCeti.manifoldMorseIndex_sphereHeight_self` and `TauCeti.manifoldMorseIndex_sphereHeight_neg`).

Let `φ` be a diffeomorphism of `Sⁿ × Sᵐ` preserving the two heights, for instance the product of
the restrictions of linear isometries `r` and `r'` fixing `v` and `w`
(`TauCeti.sphereHeight_unitSphereDiffeomorph`). Then `φ` preserves `g` and fixes its four
critical points
(`TauCeti.apply_eq_self_of_mem_criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd`), so `g`
descends to the mapping torus `Y_φ` of `φ`, where it is a Morse–Bott function whose critical
submanifolds are the four circles `t ↦ [t, (±v, ±w)]`
(`TauCeti.isMorseBottFamily_lift_sphereHeight_comp_fst_add_mul_comp_snd`), of indices `n + m`,
`n`, `m` and `0` (`TauCeti.manifoldMorseIndex_lift_sphereHeight_comp_fst_add_mul_comp_snd`).

For `n = 2`, `m = 1`, `v` the north pole of `S² ⊆ ℝ³` and `w = (1, 0)` on `S¹ ⊆ ℝ²`, so that
`g (p, e^{iθ}) = z(p) + ε cos θ`, and `r`, `r'` the reflections `(x, y, z) ↦ (x, -y, z)` and
`(x, y) ↦ (x, -y)`, this is the four-manifold `X = ([0, 1] × S² × S¹) / ((1, q) ∼ (0, τ q))`
with `τ ((x, y, z), e^{iθ}) = ((x, -y, z), e^{-iθ})`: the critical circles through `(N, 0)`,
`(N, π)`, `(S, 0)` and `(S, π)` have indices `3`, `2`, `1` and `0`. This example is meant for
orientation questions, which are not treated in this file: along the circle through `(N, π)` the
negative normal space is the tangent plane of `S²` at the north pole, on which `τ` acts by
`diag(1, -1)`, of determinant `-1`, while `τ` preserves the orientation of `S² × S¹`.

## Main results

* `TauCeti.sphereHeight_comp_fst_add_mul_comp_snd_apply_apply_eq`: a diffeomorphism preserving
  both heights preserves `g`.
* `TauCeti.apply_eq_self_of_mem_criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd`: it fixes
  the four critical points of `g`.
* `TauCeti.isMorseBottFamily_lift_sphereHeight_comp_fst_add_mul_comp_snd`: on the mapping torus of
  a diffeomorphism preserving both heights, the four critical circles exhibit the induced function
  as a Morse–Bott function.
* `TauCeti.manifoldMorseIndex_lift_sphereHeight_comp_fst_add_mul_comp_snd`: the indices of the
  four critical circles.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (orientations of Morse–Bott trajectory spaces).
-/

public section

open Set Function Metric Module
open scoped Manifold ContDiff

namespace TauCeti

open SmoothMappingTorus

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {n m : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ E' = m + 1)]
  {v : sphere (0 : E) 1} {w : sphere (0 : E') 1} {ε : ℝ}
  {φ : (sphere (0 : E) 1 × sphere (0 : E') 1) ≃ₘ⟮(𝓡 n).prod (𝓡 m), (𝓡 n).prod (𝓡 m)⟯
    (sphere (0 : E) 1 × sphere (0 : E') 1)}
  (hφ₁ : ∀ p, sphereHeight v (φ p).1 = sphereHeight v p.1)
  (hφ₂ : ∀ p, sphereHeight w (φ p).2 = sphereHeight w p.2)
include hφ₁ hφ₂

/-- A diffeomorphism preserving both heights preserves `(x, y) ↦ ⟪x, v⟫ + ε ⟪y, w⟫`. -/
theorem sphereHeight_comp_fst_add_mul_comp_snd_apply_apply_eq (ε : ℝ)
    (p : sphere (0 : E) 1 × sphere (0 : E') 1) :
    (sphereHeight v ∘ Prod.fst + ((ε * ·) ∘ sphereHeight w) ∘ Prod.snd :
        sphere (0 : E) 1 × sphere (0 : E') 1 → ℝ) (φ p) =
      (sphereHeight v ∘ Prod.fst + ((ε * ·) ∘ sphereHeight w) ∘ Prod.snd :
        sphere (0 : E) 1 × sphere (0 : E') 1 → ℝ) p := by
  simp only [Pi.add_apply, comp_apply, hφ₁, hφ₂]

/-- A diffeomorphism preserving both heights fixes the four critical points of
`(x, y) ↦ ⟪x, v⟫ + ε ⟪y, w⟫`: it preserves the levels `±1` of each height, which are the poles. -/
theorem apply_eq_self_of_mem_criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd (hε : ε ≠ 0)
    {p : sphere (0 : E) 1 × sphere (0 : E') 1}
    (hp : p ∈ criticalPoints ((𝓡 n).prod (𝓡 m))
      (sphereHeight v ∘ Prod.fst + ((ε * ·) ∘ sphereHeight w) ∘ Prod.snd)) :
    φ p = p := by
  rw [criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd v w hε] at hp
  obtain ⟨hx, hy⟩ := hp
  refine Prod.ext ?_ ?_
  · rcases hx with hx | hx
    · rw [hx, ← sphereHeight_eq_one_iff, hφ₁, hx, sphereHeight_self]
    · rw [hx, ← sphereHeight_eq_neg_one_iff, hφ₁, hx, sphereHeight_neg_self]
  · rcases hy with hy | hy
    · rw [hy, ← sphereHeight_eq_one_iff, hφ₂, hy, sphereHeight_self]
    · rw [hy, ← sphereHeight_eq_neg_one_iff, hφ₂, hy, sphereHeight_neg_self]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- The circles `ℝ / ℤ` are the sources of the critical submanifolds below: each critical point is
fixed, so its closed orbit has period `1`. -/
local instance : Fact (0 < ((1 : ℕ) : ℝ)) := ⟨Nat.cast_pos.2 one_pos⟩

/-- **The four critical circles are Morse–Bott.** Let `φ` be a diffeomorphism of `Sⁿ × Sᵐ`
preserving the heights `⟪x, v⟫` and `⟪y, w⟫`, and `ε ≠ 0`. On the mapping torus of `φ`, the
function induced by `(x, y) ↦ ⟪x, v⟫ + ε ⟪y, w⟫` is a Morse–Bott function, whose critical
submanifolds are the four closed orbits `t ↦ [t, p]` of the suspension flow through the pairs of
poles `p`, each a fixed point of `φ`. -/
theorem isMorseBottFamily_lift_sphereHeight_comp_fst_add_mul_comp_snd (hε : ε ≠ 0) :
    IsMorseBottFamily
      (fun p : criticalPoints ((𝓡 n).prod (𝓡 m))
          (sphereHeight v ∘ Prod.fst + ((ε * ·) ∘ sphereHeight w) ∘ Prod.snd) ↦
        SmoothEmbedding.ofIsSmoothEmbedding _
          ((isSmoothEmbedding_closedOrbit_iff (d := 1)
            (IsFixedPt.isPeriodicPt
              (apply_eq_self_of_mem_criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd
                hφ₁ hφ₂ hε p.2) 1) (by simp)).2
            (minimalPeriod_eq_one_iff_isFixedPt.2
              (apply_eq_self_of_mem_criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd
                hφ₁ hφ₂ hε p.2))))
      (lift φ _ (sphereHeight_comp_fst_add_mul_comp_snd_apply_apply_eq hφ₁ hφ₂ ε)) := by
  have hmorse := isMorse_sphereHeight_comp_fst_add_mul_comp_snd (n := n) (m := m) v w hε
  have hfix := fun p : criticalPoints ((𝓡 n).prod (𝓡 m))
      (sphereHeight v ∘ Prod.fst + ((ε * ·) ∘ sphereHeight w) ∘ Prod.snd) ↦
    apply_eq_self_of_mem_criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd hφ₁ hφ₂ hε p.2
  refine isMorseBottFamily_lift φ _ hmorse.contMDiff
    (fun p ↦ minimalPeriod_eq_one_iff_isFixedPt.2 (hfix p))
    (fun p ↦ hmorse.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints p.2)
    (fun p q hpq ⟨j, hj⟩ ↦ hpq (Subtype.ext ?_)) fun y hy ↦ ⟨⟨y, hy⟩, 0, rfl⟩
  rw [← hj, IsFixedPt.iterate (hfix p) j]

/-- **The indices of the four critical circles.** With `φ` as above and `ε > 0`, the Morse index
of the induced function on the mapping torus at a point `[t, (x, y)]` of the critical circle
through a pair of poles `(x, y)` is the sum of the indices of the two heights at `x` and `y`: it
is `n + m`, `n`, `m` and `0` along the circles through `(v, w)`, `(v, -w)`, `(-v, w)` and
`(-v, -w)`. -/
theorem manifoldMorseIndex_lift_sphereHeight_comp_fst_add_mul_comp_snd (hε : 0 < ε) (t : ℝ)
    {x : sphere (0 : E) 1} {y : sphere (0 : E') 1} (hx : x = v ∨ x = -v) (hy : y = w ∨ y = -w) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 n).prod (𝓡 m)))
        (lift φ _ (sphereHeight_comp_fst_add_mul_comp_snd_apply_apply_eq hφ₁ hφ₂ ε))
        (mk φ t (x, y)) =
      manifoldMorseIndex (𝓡 n) (sphereHeight v) x +
        manifoldMorseIndex (𝓡 m) (sphereHeight w) y := by
  have hmorse := isMorse_sphereHeight_comp_fst_add_mul_comp_snd (n := n) (m := m) v w hε.ne'
  rw [manifoldMorseIndex_lift_mk φ _ (by simp) ((hmorse.contMDiff _).of_le (by simp))
    (by rw [criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd v w hε.ne']; exact ⟨hx, hy⟩),
    manifoldMorseIndex_sphereHeight_comp_fst_add_mul_comp_snd v x w hε hy]

end TauCeti
