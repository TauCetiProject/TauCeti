/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.MinCriticalCount
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Morse.Sphere.Degenerate
public import TauCeti.Geometry.Manifold.Morse.Torus
public import TauCeti.Topology.Homotopy.LusternikSchnirelmann.RealProjective
public import TauCeti.Topology.Homotopy.LusternikSchnirelmann.Sphere

/-!
# The Lusternik–Schnirelmann bound on small manifolds

On a nonempty compact boundaryless manifold `M`, every smooth function `f` and every commutative
ring `R` satisfy

`lsCupLength M R + 1 ≤ lsCategoryCount M univ ≤ totalCriticalCount I f`

(`TauCeti.lsCupLength_add_one_le_lsCategoryCount_univ` and
`TauCeti.lsCategoryCount_univ_le_totalCriticalCount`). These examples evaluate the three terms on
small manifolds and show which hypotheses and conventions the bounds need.

* **The circle.** Over `ℤ` the cup length is `1`, the category count `2`, and the height has the
  two poles as critical points: `2 ≥ 2 ≥ 1 + 1`, with equality throughout.
* **The torus `T²`.** Over `ℤ` the cup length is `2`, the category count `3`, and the cosine
  function `cos θ₁ + cos θ₂` has `4` critical points: `4 ≥ 3 ≥ 2 + 1`.
* **The real projective plane.** Over `ZMod 2` the cup length is `2`, so every smooth function has
  at least `3` critical points, and a moment function with distinct weights has exactly `3`. Over
  `ℚ` the cup length is `0` and the cup-length bound gives only `1`: the coefficient ring matters.
* **A constant function on the circle.** Every point is critical, so the critical count is `⊤` and
  the bound holds. With `Nat.card`, whose value on an infinite set is `0`, it would fail.
* **Two disjoint circles.** The category count is `2 + 2 = 4`, and heights on the two circles
  give `2 + 2 = 4` critical points, so the minimal critical count is `4`. The normalized category
  of the disjoint union is `3`, not `1 + 1`.
* **Minimal counts.** Every smooth function on the circle has at least two critical points.
* **The empty manifold.** The cup length and the category count are both `0`, so
  `lsCupLength M R + 1 ≤ lsCategoryCount M univ` fails: the cup-length bound needs `M` nonempty.
* **A point.** Every function has exactly one critical point, the category count is `1` and the
  cup length `0`: `1 ≥ 1 ≥ 0 + 1`.

## References

* F. Takens, *The minimal number of critical points of a function on a compact manifold and the
  Lusternik–Schnirelman category*, Inventiones Mathematicae 6 (1968), 197–244.
* J. Weber, *Conley pairs in geometry*, Theorem 1.1.
-/

public section

noncomputable section

open Function Metric Module Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace TauCeti.Examples

/-! ### The circle -/

section Circle

-- The circle `S¹` is the unit sphere of the Euclidean plane, a manifold modelled on `ℝ¹`.
attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- On the circle, over `ℤ`, the cup length is `1`, the Lusternik–Schnirelmann count is `2` and
the height has `2` critical points, so both bounds of `2 ≥ 2 ≥ 1 + 1` are equalities. -/
example (v : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    lsCupLength (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ℤ = 1 ∧
      lsCategoryCount (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) univ = 2 ∧
      totalCriticalCount (𝓡 1) (sphereHeight v) = 2 :=
  ⟨lsCupLength_sphere finrank_euclideanSpace_fin.ge ℤ, lsCategoryCount_univ_sphere,
    totalCriticalCount_sphereHeight v⟩

/-- A constant function on the circle has infinitely many critical points, so its critical count
is `⊤` and the Lusternik–Schnirelmann bound `2 ≤ ⊤` holds. -/
example (c : ℝ) :
    totalCriticalCount (𝓡 1) (fun _ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↦ c) = ⊤ ∧
      lsCategoryCount (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) univ ≤
        totalCriticalCount (𝓡 1) fun _ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↦ c :=
  ⟨totalCriticalCount_const_sphere one_ne_zero c,
    lsCategoryCount_univ_le_totalCriticalCount contMDiff_const⟩

/-- Counting the critical points of a constant function on the circle with `Nat.card`, whose value
on an infinite set is `0`, would break the Lusternik–Schnirelmann bound: the category count `2`
is not at most `0`. -/
example (c : ℝ) :
    Nat.card (criticalPoints (𝓡 1) fun _ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↦ c) = 0 ∧
      ¬lsCategoryCount (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) univ ≤
        Nat.card (criticalPoints (𝓡 1) fun _ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↦ c) := by
  have h := totalCriticalCount_const_sphere (E := EuclideanSpace ℝ (Fin 2)) one_ne_zero c
  rw [totalCriticalCount_def, encard_eq_top_iff] at h
  rw [h.card_eq_zero, lsCategoryCount_univ_sphere]
  exact ⟨rfl, by simp⟩

/-- Every smooth function on the circle has at least two critical points, since the minimal
critical count of the circle is `2`. -/
example {f : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℝ} (hf : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ f) :
    2 ≤ totalCriticalCount (𝓡 1) f :=
  minCriticalCount_sphere (E := EuclideanSpace ℝ (Fin 2)) (n := 1) ▸ minCriticalCount_le hf

/-- On two disjoint circles the Lusternik–Schnirelmann count is `2 + 2 = 4` and heights on the two
circles have `2 + 2 = 4` critical points, so the category bound is attained and the minimal
critical count is `4`. -/
example (v v' : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    lsCategoryCount
        (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊕ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) univ =
        4 ∧
      totalCriticalCount (𝓡 1) (Sum.elim (sphereHeight v) (sphereHeight v')) = 4 ∧
      minCriticalCount (𝓡 1)
        (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊕ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) =
        4 := by
  have hcat := lsCategoryCount_univ_sum_sphere (E := EuclideanSpace ℝ (Fin 2))
    (E' := EuclideanSpace ℝ (Fin 2))
  have hcount : totalCriticalCount (𝓡 1) (Sum.elim (sphereHeight v) (sphereHeight v')) = 4 := by
    rw [totalCriticalCount_sumElim, totalCriticalCount_sphereHeight,
      totalCriticalCount_sphereHeight]
    rfl
  refine ⟨hcat, hcount, le_antisymm ?_ (hcat ▸ lsCategoryCount_univ_le_minCriticalCount)⟩
  exact hcount ▸
    minCriticalCount_le ((contMDiff_sphereHeight v).sumElim (contMDiff_sphereHeight v'))

/-- The normalized category `lsCategoryCount - 1` is not additive over disjoint unions: each
circle has normalized category `1`, but two disjoint circles have `3`, not `1 + 1`. -/
example :
    normalizedLSCategory
        (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊕ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠
      normalizedLSCategory (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) +
        normalizedLSCategory (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  rw [normalizedLSCategory_sum_sphere, normalizedLSCategory_sphere]
  decide

end Circle

/-! ### The torus -/

/-- On the torus `T²`, over `ℤ`, the cup length is `2`, the product of the classes of the two
circle factors being nonzero; the Lusternik–Schnirelmann count is `3`; and the cosine function
`cos θ₁ + cos θ₂` has `4` critical points. So `4 ≥ 3 ≥ 2 + 1`: the cup-length bound is attained
by the category count, and the category bound is strict for this function. -/
example (p : Fin 2 → ℝ) [∀ i, Fact (0 < p i)] :
    lsCupLength (∀ i, AddCircle (p i)) ℤ = 2 ∧ lsCategoryCount (∀ i, AddCircle (p i)) univ = 3 ∧
      totalCriticalCount (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (torusCos p) = 4 := by
  simp only [lsCupLength_pi_addCircle, lsCategoryCount_univ_pi_addCircle,
    totalCriticalCount_torusCos, Fintype.card_fin]
  exact ⟨rfl, rfl, rfl⟩

/-! ### The real projective plane -/

/-- On the real projective plane, over `ZMod 2`, the cup length is `2`, so every smooth function
has at least `2 + 1 = 3` critical points; a moment function with distinct weights has exactly
`3`. -/
example {f : ℙ ℝ (Fin 3 → ℝ) → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ) ∞ f) :
    lsCupLength (ℙ ℝ (Fin 3 → ℝ)) (ZMod 2) = 2 ∧ 3 ≤ totalCriticalCount 𝓘(ℝ, Fin 2 → ℝ) f ∧
      totalCriticalCount 𝓘(ℝ, Fin 2 → ℝ)
        (projectiveMomentFunction ℝ fun i : Fin 3 ↦ (i : ℝ)) = 3 := by
  have : Nonempty (ℙ ℝ (Fin 3 → ℝ)) := ⟨Projectivization.mk ℝ (Pi.single 0 1) (by simp)⟩
  have hcup := lsCupLength_projectivization_real_fin_three_zmod_two
  refine ⟨hcup, ?_, ?_⟩
  · have h := lsCupLength_add_one_le_totalCriticalCount (ZMod 2) hf
    rwa [hcup] at h
  · rw [totalCriticalCount_projectiveMomentFunction fun _ _ h ↦ Fin.ext (by exact_mod_cast h)]
    rfl

/-- On the real projective plane, over `ℚ`, the cup length is `0`, so the cup-length bound gives
only one critical point, whereas over `ZMod 2` it gives three: the coefficient ring matters. -/
example :
    lsCupLength (ℙ ℝ (Fin 3 → ℝ)) ℚ = 0 ∧
      lsCupLength (ℙ ℝ (Fin 3 → ℝ)) ℚ ≠ lsCupLength (ℙ ℝ (Fin 3 → ℝ)) (ZMod 2) := by
  have h : lsCupLength (ℙ ℝ (Fin 3 → ℝ)) ℚ = 0 := by
    simpa [show ¬Odd 2 by decide] using
      lsCupLength_projectivization_real_of_isUnit_two (N := 2) (k := ℚ)
      (isUnit_iff_ne_zero.2 two_ne_zero)
  rw [h, lsCupLength_projectivization_real_fin_three_zmod_two]
  exact ⟨rfl, by simp⟩

/-! ### The empty manifold and a point -/

section Degenerate

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℝ E H) (f : M → ℝ)
  (R : Type) [CommRing R]

/-- On the empty manifold the cup length is `0`, the supremum of the empty collection, and the
Lusternik–Schnirelmann count and the critical count are `0`. So the cup-length bound
`lsCupLength M R + 1 ≤ totalCriticalCount I f` fails: it needs `M` nonempty. -/
example [IsEmpty M] :
    lsCupLength M R = 0 ∧ lsCategoryCount M univ = 0 ∧ totalCriticalCount I f = 0 ∧
      ¬lsCupLength M R + 1 ≤ totalCriticalCount I f := by
  rw [lsCupLength_of_isEmpty, univ_eq_empty_iff.2 ‹_›, lsCategoryCount_empty,
    totalCriticalCount_of_isEmpty]
  exact ⟨rfl, rfl, rfl, by simp⟩

/-- On a point, modelled on a zero-dimensional space, every function has exactly one critical
point, the Lusternik–Schnirelmann count is `1` and the cup length is `0`: `1 ≥ 1 ≥ 0 + 1`. -/
example [Subsingleton E] [Unique M] :
    totalCriticalCount I f = 1 ∧ lsCategoryCount M univ = 1 ∧ lsCupLength M R = 0 := by
  rw [← lsCategoryCount_univ_eq_totalCriticalCount_of_subsingleton,
    lsCategoryCount_univ_of_contractibleSpace, lsCupLength_of_contractibleSpace]
  exact ⟨rfl, rfl, rfl⟩

end Degenerate

end TauCeti.Examples
