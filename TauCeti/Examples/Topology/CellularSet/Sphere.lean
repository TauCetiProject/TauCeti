/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Sphere.Cell
import TauCeti.AlgebraicTopology.Sphere.Zero
import TauCeti.Analysis.InnerProductSpace.Hemisphere

/-!
# Examples: the two discs of a sphere covered by the complements of its poles

A compact Hausdorff space `X` covered by two open sets `U` and `V`, each homeomorphic to `ℝᵐ`
with `m > 0`, is homeomorphic to `Sᵐ`
(`TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`). Milnor's argument for it chooses,
in `U`-coordinates, a closed round ball `D` whose interior contains the compact set `X \ V`, and
lets `C = X \ int D`. Then `D` and `C` are closed discs covering `X` and meeting exactly in their
boundary spheres, and gluing two discs along their boundaries gives a sphere
(`TauCeti.nonempty_homeomorph_sphere_of_union_closedBall`).

The examples below carry this out on `X = Sⁿ`, the unit sphere of a real inner product space of
dimension `n + 1`, with `U` and `V` the complements of the north pole `p` and the south pole `-p`.
The `U`-coordinates are stereographic projection `σ` from `p`, which sends `-p` to the origin, so
`X \ V = {-p}`. Write `h = ⟪·, p⟫` for the height (`TauCeti.sphereHeight p`). For `-1 < a < 1`
and `R = √(4 (1 + a) / (1 - a))`:

* `D = σ⁻¹(closedBall 0 R)` is the closed polar cap `{h ≤ a}` around `-p`, and its interior,
  the open polar cap `{h < a}`, contains `X \ V`;
* `C = X \ int D` is the opposite closed polar cap `{h ≥ a}` around `p`, which is the closed
  round ball of radius `√(4 (1 - a) / (1 + a))` in the stereographic coordinates from `-p`, so it
  lies in `V`;
* `D ∩ C` is the parallel `{h = a}`, the sphere of radius `R` in `U`-coordinates;
* `D` and `C` are closed discs whose boundary spheres are both `D ∩ C`
  (`TauCeti.exists_homeomorph_sublevel_sphereHeight_disk`), and gluing them recovers `Sⁿ`;
* on the circle `S¹`, `U` and `V` are two open arcs, `D` and `C` are complementary closed arcs, and
  `D ∩ C` consists of their two common endpoints.

## References

* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Theorem 1 and Corollary 1.
-/

public section

open Metric Module Set

namespace TauCeti.Examples.TwoOpenCells

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {a : ℝ}

/-- `D ∩ C` is the parallel `{h = a}`. -/
private theorem inter_compl_interior_setOf_sphereHeight_le (v : sphere (0 : E) 1) (ha : -1 < a)
    (ha' : a < 1) :
    {x | sphereHeight v x ≤ a} ∩ (interior {x | sphereHeight v x ≤ a})ᶜ =
      {x | sphereHeight v x = a} := by
  rw [interior_setOf_sphereHeight_le v ha ha']
  ext x
  simp [le_antisymm_iff]

/-- `D` is the closed round ball of radius `√(4 (1 + a) / (1 - a))` in `U`-coordinates, the
stereographic coordinates from the north pole `p`; it is the closed polar cap `{h ≤ a}` around the
south pole `-p`. Its interior is the open polar cap `{h < a}`, which contains the south pole, the
only point outside `V`. -/
example (p : sphere (0 : E) 1) (ha : -1 < a) (ha' : a < 1) :
    (stereographic (norm_eq_of_mem_sphere p)).symm '' closedBall 0 √(4 * (1 + a) / (1 - a)) =
        {x | sphereHeight p x ≤ a} ∧
      interior {x | sphereHeight p x ≤ a} = {x | sphereHeight p x < a} ∧
      ({-p}ᶜ : Set (sphere (0 : E) 1))ᶜ ⊆ interior {x | sphereHeight p x ≤ a} := by
  refine ⟨stereographic_symm_image_closedBall p ha.le ha', interior_setOf_sphereHeight_le p ha ha',
    ?_⟩
  rw [compl_compl, singleton_subset_iff, interior_setOf_sphereHeight_le p ha ha', mem_ofPred_eq,
    sphereHeight_neg_self]
  exact ha

/-- `C = X \ int D` is the opposite closed polar cap `{h ≥ a}` around the north pole `p`. It is
the closed round ball of radius `√(4 (1 - a) / (1 + a))` in the stereographic coordinates from the
south pole `-p`, and it misses the south pole, so it lies in `V`. -/
example (p : sphere (0 : E) 1) (ha : -1 < a) (ha' : a < 1) :
    (interior {x | sphereHeight p x ≤ a})ᶜ = {x | a ≤ sphereHeight p x} ∧
      (interior {x | sphereHeight p x ≤ a})ᶜ =
        (stereographic (norm_eq_of_mem_sphere (-p))).symm ''
          closedBall 0 √(4 * (1 + -a) / (1 - -a)) ∧
      (interior {x | sphereHeight p x ≤ a})ᶜ ⊆ ({-p}ᶜ : Set (sphere (0 : E) 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [interior_setOf_sphereHeight_le p ha ha']
    ext x
    simp
  · rw [compl_interior_setOf_sphereHeight_le p ha ha',
      stereographic_symm_image_closedBall (-p) (by linarith) (by linarith)]
  · rw [compl_interior_setOf_sphereHeight_le p ha ha']
    rintro x hx rfl
    rw [mem_ofPred_eq, sphereHeight_self] at hx
    linarith

/-- `D ∩ C` is the parallel `{h = a}`, the sphere of radius `√(4 (1 + a) / (1 - a))` in
`U`-coordinates. -/
example (p : sphere (0 : E) 1) (ha : -1 < a) (ha' : a < 1) :
    {x | sphereHeight p x ≤ a} ∩ (interior {x | sphereHeight p x ≤ a})ᶜ =
      (stereographic (norm_eq_of_mem_sphere p)).symm '' sphere 0 √(4 * (1 + a) / (1 - a)) := by
  rw [inter_compl_interior_setOf_sphereHeight_le p ha ha',
    stereographic_symm_image_sphere p ha.le ha']

/-- **`D` and `C` are closed discs glued along their boundary spheres.** `D = {h ≤ a}` and
`C = X \ int D` are each homeomorphic to the closed unit ball of `ℝⁿ`, and each meets the other
exactly in its boundary sphere, the parallel `{h = a}`. With the cover `D ∪ C = X`, these are the
hypotheses of `TauCeti.nonempty_homeomorph_sphere_of_union_closedBall`. -/
theorem exists_homeomorph_closedBall_setOf_sphereHeight_le {n : ℕ}
    [Fact (finrank ℝ E = n + 1)] (p : sphere (0 : E) 1) (ha : -1 < a) (ha' : a < 1) :
    ∃ (eD : {x | sphereHeight p x ≤ a} ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
      (eC : ((interior {x | sphereHeight p x ≤ a})ᶜ : Set (sphere (0 : E) 1)) ≃ₜ
        closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
      (∀ x : {x | sphereHeight p x ≤ a},
        (x : sphere (0 : E) 1) ∈ (interior {x | sphereHeight p x ≤ a})ᶜ ↔
          ‖(eD x : EuclideanSpace ℝ (Fin n))‖ = 1) ∧
      ∀ x : ((interior {x | sphereHeight p x ≤ a})ᶜ : Set (sphere (0 : E) 1)),
        (x : sphere (0 : E) 1) ∈ {x | sphereHeight p x ≤ a} ↔
        ‖(eC x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  obtain ⟨eD, heD⟩ := exists_homeomorph_sublevel_sphereHeight_disk.{_, 0} (n := n) p ha ha'
  -- `C` is the sublevel `{h' ≤ -a}` of the height `h'` in the direction of `-p`, also a disc.
  have hC := compl_interior_setOf_sphereHeight_le p ha ha'
  obtain ⟨eC, heC⟩ := exists_homeomorph_sublevel_sphereHeight_disk.{_, 0} (n := n) (-p)
    (a := -a) (by linarith) (by linarith)
  have hDC := inter_compl_interior_setOf_sphereHeight_le p ha ha'
  refine ⟨eD.trans Homeomorph.ulift, ((Homeomorph.setCongr hC).trans eC).trans Homeomorph.ulift,
    fun x ↦ ?_, fun x ↦ ?_⟩
  · have hx := Set.ext_iff.1 hDC x
    rw [mem_inter_iff, and_iff_right x.property] at hx
    rw [hx, mem_ofPred_eq]
    -- `Homeomorph.ulift` is `ULift.down`.
    exact heD x
  · have hx := Set.ext_iff.1 hDC x
    rw [mem_inter_iff, and_iff_left x.property] at hx
    rw [hx, mem_ofPred_eq, ← neg_inj, ← Pi.neg_apply, ← sphereHeight_neg]
    -- `Homeomorph.setCongr` is the identity on points and `Homeomorph.ulift` is `ULift.down`.
    exact heC (Homeomorph.setCongr hC x)

/-- **Gluing `D` and `C` gives `Sⁿ`.** `D` and `C = X \ int D` cover the sphere, so the two discs
glue to `Sⁿ`. -/
example {n : ℕ} [Fact (finrank ℝ E = n + 1)] (p : sphere (0 : E) 1) (ha : -1 < a)
    (ha' : a < 1) :
    Nonempty (sphere (0 : E) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  obtain ⟨eD, eC, heD, heC⟩ :=
    exists_homeomorph_closedBall_setOf_sphereHeight_le (n := n) p ha ha'
  exact nonempty_homeomorph_sphere_of_union_closedBall (by simp)
    (isClosed_le (contMDiff_sphereHeight (n := n) (m := 0) p).continuous continuous_const)
    isOpen_interior.isClosed_compl
    (eq_univ_of_forall fun x ↦ (em (x ∈ interior _)).imp (interior_subset ·) id) eD eC heD heC

/-- **The circle.** On `S¹`, `U` and `V` are two open arcs, and `D = {h ≤ a}` and
`C = X \ int D` are two closed arcs meeting exactly in their two common endpoints. -/
example (hE : finrank ℝ E = 2) (p : sphere (0 : E) 1) (ha : -1 < a) (ha' : a < 1) :
    ({x | sphereHeight p x ≤ a} ∩ (interior {x | sphereHeight p x ≤ a})ᶜ).ncard = 2 := by
  have : Fact (finrank ℝ E = 1 + 1) := ⟨hE⟩
  have hdim : finrank ℝ (ℝ ∙ (p : E))ᗮ = 1 :=
    Submodule.finrank_orthogonal_span_singleton (n := 1) (ne_zero_of_mem_unit_sphere p)
  have : Nontrivial (ℝ ∙ (p : E))ᗮ := Module.nontrivial_of_finrank_eq_succ hdim
  have hR : 0 < √(4 * (1 + a) / (1 - a)) := Real.sqrt_pos.2 (div_pos (by linarith) (by linarith))
  obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := (0 : (ℝ ∙ (p : E))ᗮ))).2 hR.le
  rw [inter_compl_interior_setOf_sphereHeight_le p ha ha',
    ← stereographic_symm_image_sphere p ha.le ha',
    ncard_image_of_injective _ (isOpenEmbedding_stereographic_symm _).injective,
    sphere_eq_pair_of_finrank_eq_one hdim hw, ncard_pair]
  simpa [Subtype.ext_iff] using ne_neg_of_mem_sphere ℝ hR.ne' ⟨w, hw⟩

end TauCeti.Examples.TwoOpenCells
