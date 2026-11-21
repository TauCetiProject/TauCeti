/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpringSystem.Tetrahedron.MatchingStabilizer
import TauCeti.RepresentationTheory.Invariants

/-!
# Fixed-space projectors of the spring tetrahedron

The symmetric group `S₄` acts orthogonally on the displacements `u ∈ ℝ¹²` of the spring
tetrahedron (`TauCeti.dotProduct_tetrahedronDisplacementRep`). For a subgroup `K` of `S₄`, the
average `P_K u = |K|⁻¹ ∑_{k ∈ K} k • u` (`Representation.averageMap`) is a projection onto the
`K`-fixed displacements. Because the action is orthogonal, `P_K` is self-adjoint for the standard
inner product, so it is the *orthogonal* projection: `P_K u` is the unique `K`-fixed displacement
`y` such that `u - y` is orthogonal to every `K`-fixed displacement.

When the fixed space is spanned by explicit, mutually orthogonal seeds, this turns `P_K` into a
closed formula, the sum of the orthogonal projections onto the lines of the seeds. This file does
so for the two subgroups whose fixed spaces are known:

* for the stabilizer `S₃` of a vertex `i`, the fixed space is spanned by the breathing mode `B`,
  the translation seed `Tᵢ` and the vibration seed `Vᵢ`
  (`TauCeti.invariants_tetrahedronDisplacementRep_comp_stabilizer`), of squared norms `3`, `3` and
  `3/8`, so
  `P_{S₃} u = ⅓ (u ⬝ B) B + ⅓ (u ⬝ Tᵢ) Tᵢ + ⁸⁄₃ (u ⬝ Vᵢ) Vᵢ`;
* for the stabilizer `D₄` of a perfect matching `m`, the fixed space is spanned by the breathing
  mode and the matching seed `Sₘ`
  (`TauCeti.invariants_tetrahedronDisplacementRep_comp_centralizer`), of squared norms `3` and `6`,
  so `P_{D₄} u = ⅓ (u ⬝ B) B + ⅙ (u ⬝ Sₘ) Sₘ`.

The three seeds lie in different eigenspaces of the force matrix, for the eigenvalues `-8`, `0`
and `-4`, and the two `D₄`-seeds in the eigenspaces for `-8` and `-2`; so each formula also splits
the projection according to the normal modes.

## Main results

* `TauCeti.dotProduct_averageMap_tetrahedronDisplacementRep_comp`: averaging over a subgroup is
  self-adjoint.
* `TauCeti.averageMap_tetrahedronDisplacementRep_comp_eq_iff`: the average of `u` is the fixed
  displacement `y` exactly when `u` and `y` have the same inner product with every fixed
  displacement, that is, averaging is the orthogonal projection onto the fixed space.
* `TauCeti.averageMap_tetrahedronDisplacementRep_comp_stabilizer`: the projector onto the
  displacements fixed by the stabilizer of a vertex.
* `TauCeti.averageMap_tetrahedronDisplacementRep_comp_centralizer`: the projector onto the
  displacements fixed by the stabilizer of a perfect matching.

## References

* A. Knutson, *Group theory in physics: an example*, tetrahedron handout for Math 261 (Cornell,
  2001), pp. 3–5.
-/

public section

namespace TauCeti

open Matrix

/-! ### Averaging over a subgroup -/

section Subgroup

variable (K : Subgroup (Equiv.Perm (Fin 4))) [Fintype K]

/-- **Averaging over a subgroup is self-adjoint** for the standard inner product on `ℝ¹²`, because
the displacement representation is orthogonal. -/
theorem dotProduct_averageMap_tetrahedronDisplacementRep_comp (u v : Fin 4 × Fin 3 → ℝ) :
    Representation.averageMap (tetrahedronDisplacementRep.comp K.subtype) u ⬝ᵥ v =
      u ⬝ᵥ Representation.averageMap (tetrahedronDisplacementRep.comp K.subtype) v := by
  simp only [Representation.averageMap_apply, smul_dotProduct, dotProduct_smul, sum_dotProduct,
    dotProduct_sum, MonoidHom.comp_apply, Subgroup.coe_subtype]
  congr 1
  rw [← Fintype.sum_equiv (Equiv.inv K) _ _ fun _ ↦ rfl]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← dotProduct_tetrahedronDisplacementRep k, Equiv.inv_apply, Subgroup.coe_inv,
    ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]

variable {K}

/-- Against a fixed displacement, the average of `u` has the same inner product as `u`. -/
theorem dotProduct_averageMap_tetrahedronDisplacementRep_comp_of_mem_invariants
    (u : Fin 4 × Fin 3 → ℝ) {w : Fin 4 × Fin 3 → ℝ}
    (hw : w ∈ Representation.invariants (tetrahedronDisplacementRep.comp K.subtype)) :
    Representation.averageMap (tetrahedronDisplacementRep.comp K.subtype) u ⬝ᵥ w = u ⬝ᵥ w := by
  rw [dotProduct_averageMap_tetrahedronDisplacementRep_comp, Representation.averageMap_id _ _ hw]

/-- **Averaging over a subgroup is the orthogonal projection onto the fixed displacements**: the
average of `u` is the fixed displacement `y` exactly when `u - y` is orthogonal to every fixed
displacement. -/
theorem averageMap_tetrahedronDisplacementRep_comp_eq_iff {u y : Fin 4 × Fin 3 → ℝ}
    (hy : y ∈ Representation.invariants (tetrahedronDisplacementRep.comp K.subtype)) :
    Representation.averageMap (tetrahedronDisplacementRep.comp K.subtype) u = y ↔
      ∀ w ∈ Representation.invariants (tetrahedronDisplacementRep.comp K.subtype),
        y ⬝ᵥ w = u ⬝ᵥ w := by
  refine ⟨fun h w hw ↦ h ▸ dotProduct_averageMap_tetrahedronDisplacementRep_comp_of_mem_invariants
    u hw, fun h ↦ ?_⟩
  -- The difference of the two candidates is fixed and orthogonal to every fixed displacement,
  -- in particular to itself.
  set z := Representation.averageMap (tetrahedronDisplacementRep.comp K.subtype) u - y
  have hz : z ∈ Representation.invariants (tetrahedronDisplacementRep.comp K.subtype) :=
    Submodule.sub_mem _ (Representation.averageMap_invariant _ u) hy
  have hzz : z ⬝ᵥ z = 0 := by
    rw [sub_dotProduct,
      dotProduct_averageMap_tetrahedronDisplacementRep_comp_of_mem_invariants u hz, h z hz,
      sub_self]
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hzz)

/-- To identify the average of `u` with a combination `y` of a spanning set `S` of the fixed
displacements, it suffices that `u` and `y` have the same inner product with each member of `S`. -/
theorem averageMap_tetrahedronDisplacementRep_comp_eq_of_span {S : Set (Fin 4 × Fin 3 → ℝ)}
    (hS : Representation.invariants (tetrahedronDisplacementRep.comp K.subtype) =
      Submodule.span ℝ S)
    {u y : Fin 4 × Fin 3 → ℝ} (hy : y ∈ Submodule.span ℝ S) (h : ∀ w ∈ S, y ⬝ᵥ w = u ⬝ᵥ w) :
    Representation.averageMap (tetrahedronDisplacementRep.comp K.subtype) u = y := by
  rw [averageMap_tetrahedronDisplacementRep_comp_eq_iff (hS ▸ hy), hS]
  exact fun w hw ↦
    LinearMap.eqOn_span' (f := dotProductBilin ℝ ℝ y) (g := dotProductBilin ℝ ℝ u) h hw

end Subgroup

/-! ### The vertex stabilizer and the matching stabilizer -/

/-- **The projector onto the displacements fixed by the stabilizer `S₃` of a vertex `i`**: the
average over `S₃` is the sum of the orthogonal projections onto the breathing mode, the
translation seed and the vibration seed of `i`, of squared norms `3`, `3` and `3/8`. -/
theorem averageMap_tetrahedronDisplacementRep_comp_stabilizer (i : Fin 4)
    [Fintype (MulAction.stabilizer (Equiv.Perm (Fin 4)) i)] (u : Fin 4 × Fin 3 → ℝ) :
    Representation.averageMap (tetrahedronDisplacementRep.comp
        (MulAction.stabilizer (Equiv.Perm (Fin 4)) i).subtype) u =
      (3⁻¹ * (u ⬝ᵥ tetrahedronBreathingMode)) • tetrahedronBreathingMode +
        (3⁻¹ * (u ⬝ᵥ tetrahedronTranslationSeed i)) • tetrahedronTranslationSeed i +
          (8 / 3 * (u ⬝ᵥ tetrahedronVibrationSeed i)) • tetrahedronVibrationSeed i := by
  refine averageMap_tetrahedronDisplacementRep_comp_eq_of_span
    (invariants_tetrahedronDisplacementRep_comp_stabilizer i) ?_ ?_
  · refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · rintro _ ⟨n, rfl⟩
    fin_cases n <;> simp [add_dotProduct] <;> ring

/-- **The projector onto the displacements fixed by the stabilizer `D₄` of a perfect matching
`m`**: the average over `D₄` is the sum of the orthogonal projections onto the breathing mode and
the seed of `m`, of squared norms `3` and `6`. -/
theorem averageMap_tetrahedronDisplacementRep_comp_centralizer (m : Fin 3)
    [Fintype (Subgroup.centralizer {symmetricGroupFourMatching m})] (u : Fin 4 × Fin 3 → ℝ) :
    Representation.averageMap (tetrahedronDisplacementRep.comp
        (Subgroup.centralizer {symmetricGroupFourMatching m}).subtype) u =
      (3⁻¹ * (u ⬝ᵥ tetrahedronBreathingMode)) • tetrahedronBreathingMode +
        (6⁻¹ * (u ⬝ᵥ tetrahedronMatchingSeed m)) • tetrahedronMatchingSeed m := by
  refine averageMap_tetrahedronDisplacementRep_comp_eq_of_span
    (invariants_tetrahedronDisplacementRep_comp_centralizer m) ?_ ?_
  · refine Submodule.add_mem _ ?_ ?_ <;>
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
  · rintro _ ⟨n, rfl⟩
    fin_cases n <;> simp [add_dotProduct] <;> ring

end TauCeti
