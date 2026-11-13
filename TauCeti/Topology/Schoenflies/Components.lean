/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import TauCeti.Geometry.Manifold.LocallyFlat.Separation
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.ConnectedComponents

/-!
# The complementary domains of a bicollared sphere

Let `σ : Sᵐ⁻¹ → Sᵐ` be a continuous injection of the unit sphere of a finite-dimensional real
normed space `E` into the unit sphere of a real normed space `F` of dimension `dim E + 1`, and
write `Σ` for its image. By the Jordan–Brouwer separation theorem
(`TauCeti.natCard_connectedComponents_sphere_compl_range_eq_two`), `Sᵐ ∖ Σ` has exactly two
connected components. This file describes these components in the situation of M. Brown's
generalized Schoenflies theorem, where `σ` has a bicollar `b : Sᵐ⁻¹ × ℝ → Sᵐ`
(`TauCeti.IsBicollar`) and `m ≥ 2`.

* If a continuous function `φ` on `Sᵐ` vanishes exactly on `Σ` and takes both signs, then the two
  components are `{φ > 0}` and `{φ < 0}`
  (`TauCeti.connectedComponentIn_compl_range_eq_setOf_pos` and
  `TauCeti.connectedComponentIn_compl_range_eq_setOf_neg`). These two statements need no bicollar
  and hold in every dimension.
* The positive side `b (Sᵐ⁻¹ × (0, ∞))` of the bicollar lies in one component and the negative
  side `b (Sᵐ⁻¹ × (-∞, 0))` in the other
  (`TauCeti.IsBicollar.disjoint_connectedComponentIn_compl_range`). These components are open
  and path connected (`TauCeti.IsBicollar.exists_connectedComponentIn_eq`). That each side lies in a
  single component holds for any bicollar of a preconnected space
  (`TauCeti.IsBicollar.image_subset_connectedComponentIn`).
* The closure of each component `U` is `U ∪ Σ`, and its frontier is `Σ`
  (`TauCeti.IsBicollar.closure_connectedComponentIn_compl_range` and
  `TauCeti.IsBicollar.frontier_connectedComponentIn_compl_range`). In particular, for `φ` as
  above, the closure of `{φ > 0}` is `{φ ≥ 0}` (`TauCeti.IsBicollar.closure_setOf_pos` and
  `TauCeti.IsBicollar.closure_setOf_neg`).

Brown proves his theorem with a continuous surjection `g : Sᵐ → Sᵐ` which is a latitude map on the
collar and collapses the two pieces outside it to the poles `p` and `-p`
(`TauCeti.IsBicollar.exists_collapse`). Then `φ y = ⟪g y, p⟫` vanishes exactly on `Σ` and takes
both signs. So the closures of the two complementary domains of `Σ` are the preimages under `g` of
the two closed hemispheres, `{0 ≤ ⟪g y, p⟫}` and `{⟪g y, p⟫ ≤ 0}`, and their common frontier `Σ` is
the preimage of the equator. The two outer pieces are cellular, and collapsing them identifies each
preimage with a closed hemisphere; this is Brown's theorem
(`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`).

The hypothesis `m ≥ 2` makes `Sᵐ⁻¹` connected, so that each side of the bicollar is connected. For
`m = 1` the two sides of the bicollar of two points of the circle need not lie in different
components.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 5 and its proof.
-/

public section

namespace TauCeti

open Function Metric Module Set Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}

section Function

variable {φ : sphere (0 : F) 1 → ℝ}

/-- **The positive domain of a function vanishing exactly on an embedded sphere.** Let `σ` be a
continuous injection of the unit sphere of a real normed space `E` into the
unit sphere of a real normed space of dimension `dim E + 1`, and let `φ` be a continuous function
vanishing exactly on the image of `σ` and taking a negative value. Then the set where `φ` is
positive is the connected component of each of its points in the complement of that image. -/
theorem connectedComponentIn_compl_range_eq_setOf_pos (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hc : Continuous σ) (hi : Injective σ) (hφ : Continuous φ)
    (hφσ : ∀ y, φ y = 0 ↔ y ∈ range σ) {z : sphere (0 : F) 1} (hz : φ z < 0)
    {y : sphere (0 : F) 1} (hy : 0 < φ y) :
    connectedComponentIn (range σ)ᶜ y = {w | 0 < φ w} :=
  connectedComponentIn_eq_of_natCard_eq_two
    (natCard_connectedComponents_sphere_compl_range_eq_two hEF hc hi)
    (isOpen_lt continuous_const hφ) (isOpen_lt hφ continuous_const)
    (Ioi_disjoint_Iio_same.preimage φ)
    (show φ ⁻¹' Ioi 0 ∪ φ ⁻¹' Iio 0 = _ by
      rw [← preimage_union, union_comm, Iio_union_Ioi, preimage_compl,
        (Set.ext hφσ : φ ⁻¹' {0} = range σ)])
    ⟨z, hz⟩ hy

/-- **The negative domain of a function vanishing exactly on an embedded sphere.** Let `σ` be a
continuous injection of the unit sphere of a real normed space `E` into the
unit sphere of a real normed space of dimension `dim E + 1`, and let `φ` be a continuous function
vanishing exactly on the image of `σ` and taking a positive value. Then the set where `φ` is
negative is the connected component of each of its points in the complement of that image. -/
theorem connectedComponentIn_compl_range_eq_setOf_neg (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hc : Continuous σ) (hi : Injective σ) (hφ : Continuous φ)
    (hφσ : ∀ y, φ y = 0 ↔ y ∈ range σ) {z : sphere (0 : F) 1} (hz : 0 < φ z)
    {y : sphere (0 : F) 1} (hy : φ y < 0) :
    connectedComponentIn (range σ)ᶜ y = {w | φ w < 0} :=
  connectedComponentIn_eq_of_natCard_eq_two
    (natCard_connectedComponents_sphere_compl_range_eq_two hEF hc hi)
    (isOpen_lt hφ continuous_const) (isOpen_lt continuous_const hφ)
    (Ioi_disjoint_Iio_same.preimage φ).symm
    (show φ ⁻¹' Iio 0 ∪ φ ⁻¹' Ioi 0 = _ by
      rw [← preimage_union, Iio_union_Ioi, preimage_compl,
        (Set.ext hφσ : φ ⁻¹' {0} = range σ)])
    ⟨z, hz⟩ hy

end Function

namespace IsBicollar

variable {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}

/-- The two sides of a bicollar of a sphere `Sᵐ⁻¹` in `Sᵐ`, `m ≥ 2`, lie in two disjoint open
path-connected sets covering the complement of its image, which are the two connected
components of that complement. -/
theorem exists_connectedComponentIn_eq (hb : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : 1 < finrank ℝ E) :
    ∃ A B : Set (sphere (0 : F) 1), IsOpen A ∧ IsOpen B ∧ Disjoint A B ∧
      (range σ)ᶜ = A ∪ B ∧ IsPathConnected A ∧ IsPathConnected B ∧
      MapsTo b (univ ×ˢ Ioi 0) A ∧ MapsTo b (univ ×ˢ Iio 0) B ∧
      (∀ y ∈ A, connectedComponentIn (range σ)ᶜ y = A) ∧
      (∀ y ∈ B, connectedComponentIn (range σ)ᶜ y = B) := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : PreconnectedSpace (sphere (0 : E) 1) := Subtype.preconnectedSpace
    (isConnected_sphere (by rw [← finrank_eq_rank]; exact_mod_cast hE) 0 zero_le_one).2
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : PreconnectedSpace (sphere (0 : F) 1) := Subtype.preconnectedSpace
    (isConnected_sphere (by rw [← finrank_eq_rank]; exact_mod_cast (by omega : 1 < finrank ℝ F))
      0 zero_le_one).2
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨x⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  obtain ⟨A, B, hA, hB, hAB, hcompl, hpos, hneg⟩ := hb.exists_isOpen_compl_range_eq_union
    (not_isPreconnected_compl_range_sphere hEF hb.continuous hb.injective)
  have hcard := natCard_connectedComponents_sphere_compl_range_eq_two hEF hb.continuous
    hb.injective
  have hAx : b (x, 1) ∈ A := hpos ⟨mem_univ x, by norm_num⟩
  have hBx : b (x, -1) ∈ B := hneg ⟨mem_univ x, by norm_num⟩
  have hAc : ∀ y ∈ A, connectedComponentIn (range σ)ᶜ y = A := fun y hy ↦
    connectedComponentIn_eq_of_natCard_eq_two hcard hA hB hAB hcompl.symm ⟨_, hBx⟩ hy
  have hBc : ∀ y ∈ B, connectedComponentIn (range σ)ᶜ y = B := fun y hy ↦
    connectedComponentIn_eq_of_natCard_eq_two hcard hB hA hAB.symm
      (hcompl.trans (union_comm _ _)).symm ⟨_, hAx⟩ hy
  -- Transport local path connectedness from the Euclidean sphere.
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) = finrank ℝ E + 1) :=
    ⟨by simp⟩
  have := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (finrank ℝ E)))
    (sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1)
  have := (sphereHomeomorphOfFinrankEq (F := F)
    (E := EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) (by simp [hEF])).locallyPathConnectedSpace
  refine ⟨A, B, hA, hB, hAB, hcompl, ?_, ?_, hpos, hneg, hAc, hBc⟩
  · apply hA.isConnected_iff_isPathConnected.1
    rw [← hAc _ hAx]
    exact isConnected_connectedComponentIn_iff.2 (hcompl.ge (Or.inl hAx))
  · apply hB.isConnected_iff_isPathConnected.1
    rw [← hBc _ hBx]
    exact isConnected_connectedComponentIn_iff.2 (hcompl.ge (Or.inr hBx))

variable (hb : IsBicollar σ b) (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : 1 < finrank ℝ E)
include hb hEF hE

/-- **The two sides of a bicollar lie in different complementary domains.** Let `b` be a bicollar
of a map `σ` from the unit sphere `Sᵐ⁻¹` of a real normed space of dimension `m ≥ 2` into the
unit sphere `Sᵐ` of a real normed space of dimension `m + 1`. The connected components, in the
complement of the image of `σ`, of a point of the positive side of the collar and of a point of
its negative side are disjoint. -/
theorem disjoint_connectedComponentIn_compl_range (x x' : sphere (0 : E) 1) {t t' : ℝ}
    (ht : 0 < t) (ht' : t' < 0) :
    Disjoint (connectedComponentIn (range σ)ᶜ (b (x, t)))
      (connectedComponentIn (range σ)ᶜ (b (x', t'))) := by
  obtain ⟨A, B, -, -, hAB, -, -, -, hpos, hneg, hAc, hBc⟩ :=
    hb.exists_connectedComponentIn_eq hEF hE
  rw [hAc _ (hpos ⟨mem_univ x, mem_Ioi.2 ht⟩), hBc _ (hneg ⟨mem_univ x', mem_Iio.2 ht'⟩)]
  exact hAB

/-- **The closure of a complementary domain of a bicollared sphere.** Let `b` be a bicollar of a
map `σ` from the unit sphere `Sᵐ⁻¹` of a real normed space of dimension `m ≥ 2` into the unit
sphere `Sᵐ` of a real normed space of dimension `m + 1`. The closure of a connected component of
the complement of the image of `σ` is that component together with the image of `σ`. -/
theorem closure_connectedComponentIn_compl_range {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    closure (connectedComponentIn (range σ)ᶜ y) = connectedComponentIn (range σ)ᶜ y ∪ range σ := by
  obtain ⟨A, B, hA, hB, hAB, hcompl, -, -, hpos, hneg, hAc, hBc⟩ :=
    hb.exists_connectedComponentIn_eq hEF hE
  rcases (hcompl ▸ hy : y ∈ A ∪ B) with hyA | hyB
  · rw [hAc y hyA]
    exact hb.closure_eq_union_range hB hAB hcompl (by simp) hpos
  · rw [hBc y hyB]
    exact hb.closure_eq_union_range hA hAB.symm (hcompl.trans (union_comm _ _)) (by simp) hneg

/-- **The frontier of a complementary domain of a bicollared sphere.** Let `b` be a bicollar of a
map `σ` from the unit sphere `Sᵐ⁻¹` of a real normed space of dimension `m ≥ 2` into the unit
sphere `Sᵐ` of a real normed space of dimension `m + 1`. The frontier of a connected component of
the complement of the image of `σ` is the image of `σ`. -/
theorem frontier_connectedComponentIn_compl_range {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    frontier (connectedComponentIn (range σ)ᶜ y) = range σ := by
  obtain ⟨A, B, hA, hB, hAB, hcompl, -, -, hpos, hneg, hAc, hBc⟩ :=
    hb.exists_connectedComponentIn_eq hEF hE
  rcases (hcompl ▸ hy : y ∈ A ∪ B) with hyA | hyB
  · rw [hAc y hyA]
    exact hb.frontier_eq_range hA hB hAB hcompl (by simp) hpos
  · rw [hBc y hyB]
    exact hb.frontier_eq_range hB hA hAB.symm (hcompl.trans (union_comm _ _)) (by simp) hneg

variable {φ : sphere (0 : F) 1 → ℝ} (hφ : Continuous φ) (hφσ : ∀ y, φ y = 0 ↔ y ∈ range σ)
include hφ hφσ

/-- **The closed positive domain of a function vanishing exactly on a bicollared sphere.** Let `b`
be a bicollar of a map `σ` from the unit sphere `Sᵐ⁻¹` of a real normed space of dimension `m ≥ 2`
into the unit sphere `Sᵐ` of a real normed space of dimension `m + 1`, and let `φ` be a continuous
function on `Sᵐ` vanishing exactly on the image of `σ` and taking both signs. Then the closure of
the set where `φ` is positive is the set where it is nonnegative. -/
theorem closure_setOf_pos {y z : sphere (0 : F) 1} (hy : 0 < φ y) (hz : φ z < 0) :
    closure {w | 0 < φ w} = {w | 0 ≤ φ w} := by
  have hyσ : y ∉ range σ := fun h ↦ hy.ne' ((hφσ y).2 h)
  rw [← connectedComponentIn_compl_range_eq_setOf_pos hEF hb.continuous hb.injective hφ hφσ hz hy,
    hb.closure_connectedComponentIn_compl_range hEF hE hyσ,
    connectedComponentIn_compl_range_eq_setOf_pos hEF hb.continuous hb.injective hφ hφσ hz hy]
  ext w
  simp only [mem_union, mem_ofPred_eq, ← hφσ, le_iff_lt_or_eq, eq_comm]

/-- **The closed negative domain of a function vanishing exactly on a bicollared sphere.** Let `b`
be a bicollar of a map `σ` from the unit sphere `Sᵐ⁻¹` of a real normed space of dimension `m ≥ 2`
into the unit sphere `Sᵐ` of a real normed space of dimension `m + 1`, and let `φ` be a continuous
function on `Sᵐ` vanishing exactly on the image of `σ` and taking both signs. Then the closure of
the set where `φ` is negative is the set where it is nonpositive. -/
theorem closure_setOf_neg {y z : sphere (0 : F) 1} (hy : 0 < φ y) (hz : φ z < 0) :
    closure {w | φ w < 0} = {w | φ w ≤ 0} := by
  have hzσ : z ∉ range σ := fun h ↦ hz.ne ((hφσ z).2 h)
  rw [← connectedComponentIn_compl_range_eq_setOf_neg hEF hb.continuous hb.injective hφ hφσ hy hz,
    hb.closure_connectedComponentIn_compl_range hEF hE hzσ,
    connectedComponentIn_compl_range_eq_setOf_neg hEF hb.continuous hb.injective hφ hφσ hy hz]
  ext w
  simp only [mem_union, mem_ofPred_eq, ← hφσ, le_iff_lt_or_eq]

end IsBicollar

end TauCeti
