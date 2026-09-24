/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.NormLeOneLipschitz
public import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.Basic

/-!
# A Lipschitz parametrization of the frontier of the ray fundamental domain

`TauCeti.NumberTheory.GeometryOfNumbers.LatticePointCount` counts lattice points in a dilated
region with a power-saving error term, but only for regions whose frontier is Lipschitz
parametrizable in codimension one. `NormLeOneLipschitz` discharges that hypothesis for Mathlib's
`normLeOne K`, the norm-≤-one section of the fundamental cone. This file lifts it to the section
`rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}` of the ray fundamental domain of an
arbitrary modulus, which is the region whose lattice points count the algebraic integers in a
fixed ray class.

`rayFundamentalDomain_inter_normLeOne_eq` presents that section as `posRegion 𝔪 ∩ A`, where
`A = ⋃ q, rayUnitRepresentative 𝔪 q • normLeOne K` is a *finite* union of unit translates: the
unit action preserves the mixed norm, so it commutes with the norm condition.

The two factors are of opposite character. `A` is bounded, with a complicated boundary;
`posRegion 𝔪` is an unbounded finite intersection of open half spaces, with a boundary made of
hyperplanes. So the naive `frontier (A ∩ B) ⊆ frontier A ∪ frontier B` is useless here: the
frontier of `posRegion 𝔪` is unbounded, and a Lipschitz-parametrizable set is a finite union of
Lipschitz images of a compact cube, hence bounded — so that union is parametrizable in no
dimension whatsoever. Mathlib's sharp form `frontier_inter_subset` keeps each frontier paired
with the closure of the *other* factor, and that pairing is what makes the argument work:

* `frontier A ∩ closure (posRegion 𝔪)` lies in `frontier A`, which lies in the union of the
  frontiers of the finitely many translates; each `frontier (u • normLeOne K)` is a Lipschitz
  image of `frontier (normLeOne K)`, because a unit acts by a homeomorphism;
* `closure A ∩ frontier (posRegion 𝔪)` is a *bounded* subset of finitely many coordinate
  hyperplanes, and a bounded subset of a hyperplane is Lipschitz parametrizable in codimension
  one (`TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker`).

## Main results

* `TauCeti.GlobalNumberFields.isLipschitzParametrizable_frontier_rayFundamentalDomain`: the
  norm-≤-one section of the ray fundamental domain is bounded and measurable, and its frontier is
  Lipschitz parametrizable in dimension `finrank ℝ (mixedSpace K) - 1`, which is `[K:ℚ] - 1` by
  `mixedEmbedding.finrank`. These are exactly the three hypotheses the lattice-point count with a
  power-saving error consumes, so they are stated together;
* `TauCeti.GlobalNumberFields.isBounded_rayFundamentalDomain_inter_normLeOne` and
  `TauCeti.GlobalNumberFields.measurableSet_rayFundamentalDomain_inter_normLeOne`: the first two
  conclusions on their own, for callers that need only one of them;
* `TauCeti.GlobalNumberFields.rayFundamentalDomain_inter_normLeOne_eq`: that section is the
  positivity region cut by a finite union of unit translates of `normLeOne K`;
* `TauCeti.GlobalNumberFields.frontier_posRegion_subset`: the frontier of the positivity region
  lies in the coordinate hyperplanes prescribed by the infinite part of the modulus.

## References

* C. Birkbeck, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`, which carries out
  the same argument for a sign orthant cut out of a bounded region of `ι → ℝ`:
  `frontier_posRegion_subset` here is that file's `frontier_signOrthant_subset`, and
  `isLipschitzParametrizable_frontier_rayFundamentalDomain` follows its
  `exists_frontier_cover_inter_orthant`, including the use of `frontier_inter_subset` to pair each
  frontier with the other factor's closure. The bounded hyperplane pieces are handled here by the
  general `TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker` rather than by that
  file's explicit slab chart `exists_lipschitz_cube_cover_hyperplane_slab`.
-/

public section

open Module NumberField NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone
open scoped Pointwise

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The frontier of the positivity region lies in the prescribed coordinate hyperplanes.** The
region is cut out by finitely many strict inequalities, so a boundary point satisfies all of them
non-strictly yet must fail one of them: that coordinate vanishes. Mathlib's
`frontier_lt_subset_eq` is the single-inequality case; the content here is that a finite
intersection of such regions still confines its frontier to those level sets. -/
theorem frontier_posRegion_subset (𝔪 : Modulus K) :
    frontier (posRegion 𝔪) ⊆ ⋃ w ∈ 𝔪.infinitePart, {x : mixedSpace K | x.1 w = 0} := by
  intro x hx
  -- The closure side: each half space `0 ≤ · w` is closed and contains the region.
  have hx1 : ∀ w ∈ 𝔪.infinitePart, 0 ≤ x.1 w := fun w hw ↦
    closure_minimal (fun _ hy ↦ (mem_posRegion.mp hy w hw).le)
      (isClosed_le continuous_const ((continuous_apply w).comp continuous_fst))
      (frontier_subset_closure hx)
  -- The interior side: the region is open, so a boundary point misses it outright.
  rw [(isOpen_posRegion 𝔪).frontier_eq] at hx
  have hx2 : ¬ ∀ w ∈ 𝔪.infinitePart, 0 < x.1 w := fun h ↦ hx.2 (mem_posRegion.mpr h)
  push Not at hx2
  obtain ⟨w, hw, hle⟩ := hx2
  exact Set.mem_biUnion hw (hle.antisymm (hx1 w hw))

open scoped Classical in
/-- A bounded set of the mixed space on which one real coordinate vanishes is Lipschitz
parametrizable in codimension one: it lies in the kernel of the nonzero linear functional reading
that coordinate. -/
private theorem isLipschitzParametrizable_of_isBounded_of_fst_eq_zero
    (w : {w : InfinitePlace K // w.IsReal}) {S : Set (mixedSpace K)}
    (hS : Bornology.IsBounded S) (hSw : ∀ x ∈ S, x.1 w = 0) :
    TauCeti.IsLipschitzParametrizable (finrank ℝ (mixedSpace K) - 1) S :=
  TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker
    (f := (LinearMap.proj w).comp (LinearMap.fst ℝ _ _))
    (DFunLike.ne_iff.2 ⟨(Pi.single w 1, 0), by simp⟩) hS
    fun x hx ↦ LinearMap.mem_ker.mpr (hSw x hx)

open scoped Classical in
/-- The piece the positivity region contributes to a frontier, when paired with the closure of a
bounded set: `frontier_posRegion_subset` puts it inside finitely many coordinate hyperplanes, and
each of those slices is bounded, hence Lipschitz parametrizable in codimension one. -/
private theorem isLipschitzParametrizable_closure_inter_frontier_posRegion (𝔪 : Modulus K)
    {A : Set (mixedSpace K)} (hA : Bornology.IsBounded A) :
    TauCeti.IsLipschitzParametrizable (finrank ℝ (mixedSpace K) - 1)
      (closure A ∩ frontier (posRegion 𝔪)) := by
  refine .mono (.biUnion_finset 𝔪.infinitePart
    (A := fun w ↦ closure A ∩ {x : mixedSpace K | x.1 w = 0}) fun w _ ↦
      isLipschitzParametrizable_of_isBounded_of_fst_eq_zero w
        (hA.closure.subset Set.inter_subset_left) fun x hx ↦ hx.2) ?_
  rintro x ⟨hx1, hx2⟩
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.1 (frontier_posRegion_subset 𝔪 hx2)
  exact Set.mem_iUnion₂.2 ⟨w, hw, hx1, hxw⟩

/-- **The norm-≤-one section of the ray fundamental domain**, as the positivity region cut by a
finite union of unit translates of Mathlib's norm-≤-one region. The unit action preserves the
mixed norm, so it commutes with the norm condition. -/
theorem rayFundamentalDomain_inter_normLeOne_eq (𝔪 : Modulus K) :
    rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ 1} =
      posRegion 𝔪 ∩ ⋃ q : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroupSupTorsion 𝔪,
        rayUnitRepresentative 𝔪 q • normLeOne K := by
  ext x
  simp only [rayFundamentalDomain_eq_iUnion, Set.mem_inter_iff, Set.mem_iUnion,
    Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq, norm_unit_smul]
  tauto

open scoped Classical in
/-- A unit translate of Mathlib's norm-≤-one region is bounded, because the unit acts by a
Lipschitz map. -/
private theorem isBounded_unitSMul_normLeOne (u : (𝓞 K)ˣ) :
    Bornology.IsBounded (u • normLeOne K) := by
  -- the unit action *is* multiplication by `mixedEmbedding K u`, so Mathlib's bound applies
  have hC : LipschitzWith ‖mixedEmbedding K (u : K)‖₊ fun x : mixedSpace K ↦ u • x :=
    lipschitzWith_smul _
  rw [← Set.image_smul]
  exact hC.isBounded_image (isBounded_normLeOne K)

open scoped Classical in
/-- The frontier of a unit translate of Mathlib's norm-≤-one region is Lipschitz parametrizable in
codimension one: a unit acts by a homeomorphism, so this frontier is the Lipschitz image of
`frontier (normLeOne K)`. -/
private theorem isLipschitzParametrizable_frontier_unitSMul_normLeOne (u : (𝓞 K)ˣ) :
    TauCeti.IsLipschitzParametrizable (finrank ℝ (mixedSpace K) - 1)
      (frontier (u • normLeOne K)) := by
  have hC : LipschitzWith ‖mixedEmbedding K (u : K)‖₊ fun x : mixedSpace K ↦ u • x :=
    lipschitzWith_smul _
  refine .mono (.image hC (isLipschitzParametrizable_frontier_normLeOne K)) ?_
  rw [Set.image_smul]
  simp only [← Set.preimage_smul_inv]
  exact (continuous_const_mul _).frontier_preimage_subset _

open scoped Classical in
/-- **The norm-≤-one section of the ray fundamental domain is bounded.** It is carved out of a
finite union of unit translates of Mathlib's norm-≤-one region, and each translate is bounded
because the unit acts by a Lipschitz map. -/
theorem isBounded_rayFundamentalDomain_inter_normLeOne (𝔪 : Modulus K) :
    Bornology.IsBounded
      (rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ 1}) := by
  rw [rayFundamentalDomain_inter_normLeOne_eq]
  exact (Bornology.isBounded_iUnion.2 fun q ↦ isBounded_unitSMul_normLeOne _).subset
    Set.inter_subset_right

/-- **The norm-≤-one section of the ray fundamental domain is measurable**: the domain itself is
measurable and the mixed norm is continuous. -/
theorem measurableSet_rayFundamentalDomain_inter_normLeOne (𝔪 : Modulus K) :
    MeasurableSet (rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ 1}) :=
  (measurableSet_rayFundamentalDomain 𝔪).inter
    (measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const)

open scoped Classical in
/-- **The norm-≤-one section of the ray fundamental domain is bounded and measurable, and its
frontier is Lipschitz parametrizable in codimension one.** The first and third conclusions are
exactly the two hypotheses `hDb` and `hDfr` of
`TauCeti.exists_abs_ncard_smul_inter_vadd_sub_le`, the lattice-point count with a power-saving
error, applied to the region counting the algebraic integers of a fixed ray class; the second is
what gives that region a measure at all. This is the analogue, for an arbitrary modulus, of
`isLipschitzParametrizable_frontier_normLeOne` for the trivial one, whose ray fundamental domain
is Mathlib's fundamental cone.

The section is `posRegion 𝔪` intersected with finitely many unit translates of `normLeOne K`.
The translates are bounded and each has a frontier that is a Lipschitz image of
`frontier (normLeOne K)`; the positivity region is unbounded, but `frontier_inter_subset` pairs
its frontier with the *closure of the translates*, so the piece it contributes is a bounded subset
of the finitely many coordinate hyperplanes prescribed by the infinite part of `𝔪`. -/
theorem isLipschitzParametrizable_frontier_rayFundamentalDomain (𝔪 : Modulus K) :
    Bornology.IsBounded
        (rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ 1}) ∧
      MeasurableSet (rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ 1}) ∧
        TauCeti.IsLipschitzParametrizable (finrank ℝ (mixedSpace K) - 1)
          (frontier (rayFundamentalDomain 𝔪 ∩
            {x : mixedSpace K | mixedEmbedding.norm x ≤ 1})) := by
  refine ⟨isBounded_rayFundamentalDomain_inter_normLeOne 𝔪,
    measurableSet_rayFundamentalDomain_inter_normLeOne 𝔪, ?_⟩
  rw [rayFundamentalDomain_inter_normLeOne_eq, Set.inter_comm]
  set A : Set (mixedSpace K) := ⋃ q : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroupSupTorsion 𝔪,
    rayUnitRepresentative 𝔪 q • normLeOne K
  have hAbdd : Bornology.IsBounded A :=
    Bornology.isBounded_iUnion.2 fun q ↦ isBounded_unitSMul_normLeOne _
  have hAfr : TauCeti.IsLipschitzParametrizable (finrank ℝ (mixedSpace K) - 1) (frontier A) :=
    .mono (.iUnion fun q ↦ isLipschitzParametrizable_frontier_unitSMul_normLeOne _)
      (frontier_iUnion_subset _)
  exact .mono (.union (.mono hAfr Set.inter_subset_left)
    (isLipschitzParametrizable_closure_inter_frontier_posRegion 𝔪 hAbdd))
    (frontier_inter_subset A (posRegion 𝔪))

end TauCeti.GlobalNumberFields
