/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalDegree
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Involution
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Sphere
public import TauCeti.Topology.CWComplex.Classical.RealProjective

/-!
# The cellular differential of real projective space

Real projective space `RPᴺ` has one cell in each dimension `0, …, N`
(`TauCeti.RealProjectiveSpace.cwComplex`). This file computes the incidence numbers of its
cellular differential: the incidence coefficient of the `i`-cell in the boundary of the
`(i + 1)`-cell is `1 + (-1) ^ (i + 1)` times a unit of the coefficient ring. It is `0` when `i` is
even, and twice a unit when `i` is odd; over `ℤ` it is `±2`
(`TauCeti.RealProjectiveSpace.cellularIncidence_cwComplex_eq_two_or_eq_neg_two_of_odd`).

The attaching map of the `(i + 1)`-cell is the double cover `f : Sⁱ → RPⁱ`, `v ↦ [v]`. Let `x` be
the class of the pole `p = eᵢ` of `Sⁱ`, a point of the open `i`-cell. The incidence number is the
local degree of `f` at `x` (`TauCeti.singularHomologyπ_cellAttachingMap_eq_cellularIncidence_smul`).
The fibre of `f` over `x` is `{p, -p}`, and `f` is invariant under the antipodal map, which acts on
`Hᵢ(Sⁱ)` by `(-1) ^ (i + 1)` (`TauCeti.reducedSingularHomologyFunctor_map_diskBoundaryNeg`). So
the local degree at `x` is `1 + (-1) ^ (i + 1)` times the local degree of `f` near `p`
(`TopPair.comp_singularHomologyMap_ofSubsetMap_eq_one_add_smul`). On the open upper hemisphere
`U = {v | vᵢ > 0}` around `p`, the map `f` is an embedding onto the open `i`-cell, so by excision
the local degree near `p` is a unit.

The sign of that unit depends on the orientation conventions of the sphere generator and of the
characteristic maps, and is not computed here. It does not affect the cellular homology.

## Main results

* `TauCeti.RealProjectiveSpace.exists_cellularIncidence_cwComplex_eq_one_add_neg_one_pow_mul`:
  the incidence coefficient is `1 + (-1) ^ (i + 1)` times a unit.
* `TauCeti.RealProjectiveSpace.cellularIncidence_cwComplex_eq_zero_of_even` and
  `TauCeti.RealProjectiveSpace.exists_cellularIncidence_cwComplex_eq_two_mul_of_odd`: it is `0`
  for even `i` and twice a unit for odd `i`.
* `TauCeti.RealProjectiveSpace.cellularIncidence_cwComplex_eq_two_or_eq_neg_two_of_odd`: over
  `ℤ`, it is `±2` for odd `i`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Example 2.42.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

namespace TauCeti.RealProjectiveSpace

attribute [local instance] cwComplex

variable {N i : ℕ}

/-- The point of `Sᴺ` over a point `v` of the boundary sphere `Sⁱ` of the `(i + 1)`-disk: the
coordinates of `v`, followed by zeros. -/
private def sphereIncl (hi : i + 1 ≤ N) (v : TopCat.diskBoundary.{0} (i + 1)) :
    sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1 :=
  ⟨hemispherePoint N (v.down : EuclideanSpace ℝ (Fin (i + 1))),
    mem_sphere_zero_iff_norm.2 (norm_hemispherePoint hi (norm_eq_of_mem_sphere v.down).le)⟩

private lemma continuous_sphereIncl (hi : i + 1 ≤ N) : Continuous (sphereIncl hi) :=
  (continuous_hemispherePoint.comp (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _

/-- The attaching map of the `(i + 1)`-cell of `RPᴺ` is the double cover `Sⁱ → RPⁱ ⊆ RPᴺ`. -/
private lemma cellAttachingMap_apply_eq_mk (hi : i + 1 ≤ N)
    (c : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) (v : TopCat.diskBoundary.{0} (i + 1)) :
    (ConcreteCategory.hom (Y := TopCat.of (skeletonLT (univ : Set (RealProjectiveSpace N))
      (i + 1 : ℕ))) (cellAttachingMap c) v).1 = mk N (sphereIncl hi v) := by
  have hv : (EuclideanSpace.equiv (Fin (i + 1)) ℝ).unitBallHomeomorph v.down ∈ closedBall 0 1 :=
    mem_closedBall_zero_iff.2
      ((EuclideanSpace.equiv (Fin (i + 1)) ℝ).norm_unitBallHomeomorph_le_one_iff.2
        (norm_eq_of_mem_sphere v.down).le)
  rw [coe_cellAttachingMap_apply, coe_diskHomeomorphClosedBall_apply,
    map_cwComplex ⟨i + 1, by omega⟩ c, cellMap_apply _ hv]
  congr 2
  exact congrArg (hemispherePoint N) (Homeomorph.symm_apply_apply _ _)

/-- The attaching map of the `(i + 1)`-cell of `RPᴺ` is invariant under the antipodal map. -/
private lemma cellAttachingMap_diskBoundaryNeg (hi : i + 1 ≤ N)
    (c : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) (v : TopCat.diskBoundary.{0} (i + 1)) :
    cellAttachingMap c (diskBoundaryNeg (i + 1) v) = cellAttachingMap c v := by
  apply Subtype.ext
  rw [cellAttachingMap_apply_eq_mk hi, cellAttachingMap_apply_eq_mk hi, ← mk_neg]
  congr 1
  apply Subtype.ext
  simp only [sphereIncl, diskBoundaryNeg_apply_down, coe_neg_sphere,
    hemispherePoint_neg (norm_eq_of_mem_sphere v.down), neg_neg]

/-- The pole `eᵢ` of the boundary sphere `Sⁱ` of the `(i + 1)`-disk. -/
private def pole (i : ℕ) : TopCat.diskBoundary.{0} (i + 1) :=
  ULift.up ⟨EuclideanSpace.single (Fin.last i) 1, by simp⟩

private lemma coe_pole_down_last (i : ℕ) :
    ((pole i).down : EuclideanSpace ℝ (Fin (i + 1))) (Fin.last i) = 1 := by
  simp [pole]

private lemma diskBoundaryNeg_pole_ne (i : ℕ) : diskBoundaryNeg (i + 1) (pole i) ≠ pole i := by
  intro h
  have h' := congrArg (fun v : TopCat.diskBoundary.{0} (i + 1) ↦
    (v.down : EuclideanSpace ℝ (Fin (i + 1))) (Fin.last i)) h
  simp only [diskBoundaryNeg_apply_down, coe_neg_sphere, PiLp.neg_apply, coe_pole_down_last] at h'
  norm_num at h'

/-- The fibre of the attaching map of the `(i + 1)`-cell of `RPᴺ` over the class of the pole
consists of the pole and its antipode. -/
private lemma eq_pole_or_eq_of_cellAttachingMap_eq (hi : i + 1 ≤ N)
    (c : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) {v : TopCat.diskBoundary.{0} (i + 1)}
    (hv : cellAttachingMap c v = cellAttachingMap c (pole i)) :
    v = pole i ∨ v = diskBoundaryNeg (i + 1) (pole i) := by
  have hv' := congrArg Subtype.val hv
  rw [cellAttachingMap_apply_eq_mk hi, cellAttachingMap_apply_eq_mk hi, mk_eq_mk_iff] at hv'
  have hinj := hemispherePoint_injective (n := N) (k := i + 1) (by omega)
  rcases hv' with h | h
  · refine Or.inl (ULift.ext (Subtype.ext (hinj ?_)))
    exact congrArg Subtype.val h
  · refine Or.inr (ULift.ext (Subtype.ext (hinj ?_)))
    rw [diskBoundaryNeg_apply_down, coe_neg_sphere,
      hemispherePoint_neg (norm_eq_of_mem_sphere (pole i).down)]
    exact congrArg Subtype.val h

/-- The class of the pole lies in the open `i`-cell of `RPᴺ`. -/
private lemma cellAttachingMap_pole_mem_openCell (hi : i + 1 ≤ N)
    (c : cell (univ : Set (RealProjectiveSpace N)) i)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) :
    ((cellAttachingMap c' (pole i) : skeletonLT (univ : Set (RealProjectiveSpace N))
      (i + 1 : ℕ)) : RealProjectiveSpace N) ∈ Topology.RelCWComplex.openCell i c := by
  rw [Topology.RelCWComplex.openCell, map_cwComplex ⟨i, by omega⟩ c, image_cellMap_ball,
    cellAttachingMap_apply_eq_mk hi, mk_mem_openCell_iff]
  refine ⟨?_, fun j hj ↦ ?_⟩
  · rw [sphereIncl, hemispherePoint_apply_of_lt _ (j := ⟨i, by omega⟩) (Nat.lt_succ_self i)]
    exact (coe_pole_down_last i).trans_ne one_ne_zero
  · rcases (Nat.succ_le_of_lt (Fin.lt_def.1 hj)).lt_or_eq with h | h
    · exact hemispherePoint_apply_of_gt _ h
    · rw [sphereIncl, hemispherePoint_apply_of_eq _ h.symm, norm_eq_of_mem_sphere (pole i).down]
      simp

/-- The open upper hemisphere `{v | vᵢ > 0}` of the boundary sphere `Sⁱ` of the `(i + 1)`-disk,
an open neighbourhood of the pole. -/
private def upperHemisphere (i : ℕ) : Set (TopCat.diskBoundary.{0} (i + 1)) :=
  {v | 0 < (v.down : EuclideanSpace ℝ (Fin (i + 1))) (Fin.last i)}

private lemma mem_upperHemisphere_iff {v : TopCat.diskBoundary.{0} (i + 1)} :
    v ∈ upperHemisphere i ↔ 0 < (v.down : EuclideanSpace ℝ (Fin (i + 1))) (Fin.last i) :=
  Iff.rfl

private lemma isOpen_upperHemisphere (i : ℕ) : IsOpen (upperHemisphere i) :=
  isOpen_lt continuous_const
    ((PiLp.continuous_apply _ _ _).comp (continuous_subtype_val.comp continuous_uliftDown))

private lemma pole_mem_upperHemisphere (i : ℕ) : pole i ∈ upperHemisphere i := by
  rw [mem_upperHemisphere_iff, coe_pole_down_last]
  exact one_pos

private lemma diskBoundaryNeg_pole_notMem_upperHemisphere (i : ℕ) :
    diskBoundaryNeg (i + 1) (pole i) ∉ upperHemisphere i := by
  rw [mem_upperHemisphere_iff, diskBoundaryNeg_apply_down, coe_neg_sphere, PiLp.neg_apply,
    coe_pole_down_last]
  norm_num

/-- On the upper hemisphere, the attaching map of the `(i + 1)`-cell of `RPᴺ` is an embedding: the
quotient map `Sᴺ → RPᴺ` is an open embedding on the open set `{y | yᵢ > 0}`. -/
private lemma isEmbedding_cellAttachingMap_restrict (hi : i + 1 ≤ N)
    (c : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) :
    IsEmbedding ((upperHemisphere i).domRestrict (cellAttachingMap c)) := by
  rw [← IsEmbedding.subtypeVal.of_comp_iff]
  let V : Set (sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1) :=
    {y | 0 < (y : EuclideanSpace ℝ (Fin (N + 1))) ⟨i, by omega⟩}
  have hV : IsOpen V :=
    isOpen_lt continuous_const ((PiLp.continuous_apply _ _ _).comp continuous_subtype_val)
  have hmk : IsEmbedding fun y : V ↦ mk N y := by
    refine (IsOpenEmbedding.of_continuous_injective_isOpenMap
      ((continuous_mk N).comp continuous_subtype_val) (fun y y' h ↦ ?_)
      ((isOpenMap_mk N).comp hV.isOpenMap_subtype_val)).isEmbedding
    rcases (mk_eq_mk_iff N y y').1 h with h | h
    · exact Subtype.ext h
    · have hy : 0 < (y : EuclideanSpace ℝ (Fin (N + 1))) ⟨i, by omega⟩ := y.2
      have hy' : 0 < (y' : EuclideanSpace ℝ (Fin (N + 1))) ⟨i, by omega⟩ := y'.2
      rw [h, coe_neg_sphere, PiLp.neg_apply] at hy
      linarith
  have : CompactSpace (TopCat.diskBoundary.{0} (i + 1)) :=
    inferInstanceAs (CompactSpace (ULift (sphere (0 : EuclideanSpace ℝ (Fin (i + 1))) 1)))
  have hincl : IsEmbedding (sphereIncl hi) :=
    ((continuous_sphereIncl hi).isClosedEmbedding fun v w h ↦ ULift.ext (Subtype.ext
      (hemispherePoint_injective (by omega) (congrArg Subtype.val h)))).isEmbedding
  have hV' (u : upperHemisphere i) : sphereIncl hi u ∈ V := by
    have hu := mem_upperHemisphere_iff.1 u.2
    rwa [mem_ofPred_eq, sphereIncl,
      hemispherePoint_apply_of_lt _ (j := ⟨i, by omega⟩) (Nat.lt_succ_self i)]
  convert hmk.comp ((hincl.comp IsEmbedding.subtypeVal).codRestrict V hV') using 1
  funext u
  exact cellAttachingMap_apply_eq_mk hi c u

/-- The point of the upper hemisphere of the boundary sphere `Sⁱ` of the `(i + 1)`-disk over a
point `v` of the closed `i`-disk. -/
private def upperPoint {v : EuclideanSpace ℝ (Fin i)} (hv : ‖v‖ ≤ 1) :
    TopCat.diskBoundary.{0} (i + 1) :=
  ULift.up ⟨hemispherePoint i v, mem_sphere_zero_iff_norm.2 (norm_hemispherePoint le_rfl hv)⟩

private lemma coe_upperPoint_down {v : EuclideanSpace ℝ (Fin i)} (hv : ‖v‖ ≤ 1) :
    ((upperPoint hv).down : EuclideanSpace ℝ (Fin (i + 1))) = hemispherePoint i v :=
  (rfl)

/-- Every point of the open `i`-cell of `RPᴺ` is the image of a point of the upper hemisphere under
the attaching map of the `(i + 1)`-cell. -/
private lemma exists_mem_upperHemisphere_cellAttachingMap_eq (hi : i + 1 ≤ N)
    (c : cell (univ : Set (RealProjectiveSpace N)) i)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (i + 1))
    (z : skeletonLT (univ : Set (RealProjectiveSpace N)) (i + 1 : ℕ))
    (hz : (z : RealProjectiveSpace N) ∈ Topology.RelCWComplex.openCell i c) :
    ∃ u ∈ upperHemisphere i, cellAttachingMap c' u = z := by
  rw [Topology.RelCWComplex.openCell, map_cwComplex ⟨i, by omega⟩ c] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  set v := (EuclideanSpace.equiv (Fin i) ℝ).unitBallHomeomorph.symm w
  have hv : ‖v‖ < 1 :=
    (EuclideanSpace.equiv (Fin i) ℝ).norm_unitBallHomeomorph_symm_lt_one_iff.2
      (mem_ball_zero_iff.1 hw)
  refine ⟨upperPoint hv.le, ?_, Subtype.ext ?_⟩
  · rw [mem_upperHemisphere_iff, coe_upperPoint_down,
      hemispherePoint_apply_of_eq v (j := Fin.last i) (Fin.val_last i)]
    exact Real.sqrt_pos.2 (by nlinarith [norm_nonneg v])
  · rw [cellAttachingMap_apply_eq_mk hi, ← hwz, cellMap_apply _ (ball_subset_closedBall hw)]
    congr 1
    exact Subtype.ext ((congrArg (hemispherePoint N) (coe_upperPoint_down hv.le)).trans
      (hemispherePoint_hemispherePoint hv.le))

/-- The antipodal map preserves the complement of the pole and its antipode. -/
private lemma mapsTo_diskBoundaryNeg_compl_pole (i : ℕ) :
    MapsTo (diskBoundaryNeg.{0} (i + 1)) ({pole i}ᶜ ∩ {diskBoundaryNeg (i + 1) (pole i)}ᶜ)
      ({pole i}ᶜ ∩ {diskBoundaryNeg (i + 1) (pole i)}ᶜ) := fun v hv ↦
  ⟨fun h ↦ hv.2 ((diskBoundaryNeg_diskBoundaryNeg_apply v).symm.trans (congrArg _ h)),
    fun h ↦ hv.1 (Function.Involutive.injective diskBoundaryNeg_diskBoundaryNeg_apply h)⟩

/-- The attaching map of the `(i + 1)`-cell of `RPᴺ` sends the complement of the pole and its
antipode into the complement of the class of the pole. -/
private lemma mapsTo_cellAttachingMap_compl_pole (hi : i + 1 ≤ N)
    (c : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) :
    MapsTo (cellAttachingMap c) ({pole i}ᶜ ∩ {diskBoundaryNeg (i + 1) (pole i)}ᶜ)
      {cellAttachingMap c (pole i)}ᶜ := fun _ hv h ↦
  (eq_pole_or_eq_of_cellAttachingMap_eq hi c h).elim hv.1 hv.2

/-- The attaching map of the `(i + 1)`-cell of `RPᴺ` sends the upper hemisphere minus the pole
into the complement of the class of the pole. -/
private lemma mapsTo_cellAttachingMap_upperHemisphere_compl_pole (hi : i + 1 ≤ N)
    (c : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) :
    MapsTo (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C(upperHemisphere i, TopCat.diskBoundary.{0} (i + 1))) ≫ cellAttachingMap c)
      (Subtype.val ⁻¹' {pole i}ᶜ : Set (upperHemisphere i))
      {cellAttachingMap c (pole i)}ᶜ := fun u hu h ↦
  (eq_pole_or_eq_of_cellAttachingMap_eq hi c h).elim hu fun h' ↦
    diskBoundaryNeg_pole_notMem_upperHemisphere i (h' ▸ u.2)

/-- **Excision near the pole.** On the upper hemisphere, the attaching map of the `(i + 1)`-cell
of `RPᴺ` induces isomorphisms from `H(U, U ∖ {p})` to the local homology of the `i`-skeleton at the
class of the pole `p`. -/
private lemma isIso_singularHomologyMap_upperHemisphere {A : Type*} [Category A]
    [HasCoproducts.{0} A] [Abelian A] (R : A) (hi : i + 1 ≤ N)
    (c : cell (univ : Set (RealProjectiveSpace N)) i)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (i + 1))
    (hfU : MapsTo (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C(upperHemisphere i, TopCat.diskBoundary.{0} (i + 1))) ≫ cellAttachingMap c')
      (Subtype.val ⁻¹' {pole i}ᶜ : Set (upperHemisphere i))
      {cellAttachingMap c' (pole i)}ᶜ) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hfU) R n) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover R (TopPair.ofSubsetMap _ hfU) ?_ ?_
    (fun b : Bool ↦ bif b
      then (Subtype.val ⁻¹' Topology.RelCWComplex.openCell i c :
        Set (skeletonLT (univ : Set (RealProjectiveSpace N)) (i + 1 : ℕ)))
      else {cellAttachingMap c' (pole i)}ᶜ)
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) n
  · rw [TopPair.ofSubsetMap_fst]
    exact isEmbedding_cellAttachingMap_restrict hi c'
  · rintro u ⟨y, hy⟩
    refine ⟨⟨u, fun hu ↦ y.2 ?_⟩, rfl⟩
    refine hy.trans ?_
    rw [TopPair.ofSubsetMap_fst_apply]
    exact congrArg (cellAttachingMap c') hu
  · cases b
    · have : T1Space (skeletonLT (univ : Set (RealProjectiveSpace N)) (i + 1 : ℕ)) := inferInstance
      exact @isOpen_compl_singleton _ _ this _
    · exact isOpen_preimage_val_openCell i subset_rfl c
  · refine eq_univ_of_forall fun z ↦ mem_iUnion.2 ?_
    by_cases hz : z = cellAttachingMap c' (pole i)
    · exact ⟨true, hz ▸ cellAttachingMap_pole_mem_openCell hi c c'⟩
    · exact ⟨false, hz⟩
  · cases b
    · exact Or.inl TopPair.range_ofSubset_map.symm.subset
    · refine Or.inr fun z hz ↦ ?_
      obtain ⟨u, hu, rfl⟩ := exists_mem_upperHemisphere_cellAttachingMap_eq hi c c' z hz
      exact ⟨⟨u, hu⟩, TopPair.ofSubsetMap_fst_apply _ _ _⟩

section Ring

variable (R : Type) [Ring R]

/-- The incidence coefficient of the `i`-cell in the boundary of the `(i + 1)`-cell of `RPᴺ` is
`1 + (-1) ^ (i + 1)` times the local degree `μ` of the attaching map near the pole, and `μ` is a
unit when `i > 0`. -/
private lemma exists_cellularIncidence_cwComplex_eq_mul (hi : i + 1 ≤ N)
    (c : cell (univ : Set (RealProjectiveSpace N)) i)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) :
    ∃ μ : R, cellularIncidence univ R i c c' = (1 + (-1) ^ (i + 1)) * μ ∧ (0 < i → IsUnit μ) := by
  -- Let `s` be the sphere generator in `Hᵢ(Sⁱ, Sⁱ ∖ {p, -p})` and `t` its contribution near the
  -- pole `p`, in `Hᵢ(U, U ∖ {p})`. The attaching map sends `s` to `[c' : c]` times the local class
  -- of `c` (`singularHomologyπ_cellAttachingMap_eq_cellularIncidence_smul`), and to
  -- `1 + (-1) ^ (i + 1)` times the image `μ` of `t` (by the involution lemma). For `i > 0` both
  -- `t` and the map it is pushed along are isomorphisms, so `μ` is a unit.
  have : T1Space (TopCat.diskBoundary.{0} (i + 1)) :=
    inferInstanceAs (T1Space (ULift (sphere (0 : EuclideanSpace ℝ (Fin (i + 1))) 1)))
  have hx := cellAttachingMap_pole_mem_openCell hi c c'
  have ha : Function.Involutive (diskBoundaryNeg.{0} (i + 1)) :=
    diskBoundaryNeg_diskBoundaryNeg_apply
  have hapU := diskBoundaryNeg_pole_notMem_upperHemisphere i
  have haP := mapsTo_diskBoundaryNeg_compl_pole i
  have hfP := mapsTo_cellAttachingMap_compl_pole hi c'
  have hfU := mapsTo_cellAttachingMap_upperHemisphere_compl_pole hi c'
  have := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    (isOpen_upperHemisphere i) isClosed_singleton
    (singleton_subset_iff.2 (pole_mem_upperHemisphere i)) i
  have := isIso_singularHomologyMap_upperHemisphere (ModuleCat.of R R) hi c c' hfU i
  -- The sphere generator in `Hᵢ(Sⁱ, Sⁱ ∖ {p, -p})`, and its contribution near the pole.
  obtain ⟨s, hs⟩ : ∃ s, s = diskBoundaryFundamentalClass (ModuleCat.of R R)
      ({pole i}ᶜ ∩ {diskBoundaryNeg (i + 1) (pole i)}ᶜ) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = s ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _)
      inter_subset_left) (ModuleCat.of R R) i ≫ inv (TopPair.singularHomologyMap
        (TopPair.excisionMap (upperHemisphere i) {pole i}ᶜ) (ModuleCat.of R R) i) := ⟨_, rfl⟩
  have hmain := TopPair.comp_singularHomologyMap_ofSubsetMap_eq_one_add_smul (ModuleCat.of R R) ha
    (diskBoundaryNeg_pole_ne i) hapU (cellAttachingMap c')
    (cellAttachingMap_diskBoundaryNeg hi c') hfP i ((-1) ^ (i + 1)) s
    (hs ▸ diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap_diskBoundaryNeg
      (ModuleCat.of R R) haP) t
    (by rw [ht, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id])
  -- The image of `s` under the attaching map is the image of the sphere generator in the local
  -- homology of the skeleton at the class of the pole.
  have hloc := singularHomologyπ_cellAttachingMap_eq_cellularIncidence_smul univ R
    (cellAttachingMap c' (pole i)) hx c'
  have hs1 : (s ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hfP) (ModuleCat.of R R) i) 1 =
      cellularIncidence univ R i c c' • cellLocalClass univ (ModuleCat.of R R)
        (cellAttachingMap c' (pole i)) hx 1 := by
    rw [hs, diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap]
    exact hloc
  set μ := inv (cellLocalClass univ (ModuleCat.of R R) (cellAttachingMap c' (pole i)) hx)
    ((t ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hfU) (ModuleCat.of R R) i) 1)
    with hμ
  refine ⟨μ, ?_, fun hi0 ↦ ?_⟩
  · have h := congrArg (inv (cellLocalClass univ (ModuleCat.of R R)
      (cellAttachingMap c' (pole i)) hx)) (hs1.symm.trans (congrArg (fun g ↦ g 1) hmain))
    have hz (n : ℤ) {X : ModuleCat R} (g : ModuleCat.of R R ⟶ X) (y : R) : (n • g) y = n • g y := by
      simp
    rw [map_smul, IsIso.hom_inv_id_apply, smul_eq_mul, mul_one, hz, map_zsmul, ← hμ,
      zsmul_eq_mul] at h
    rw [h]
    push_cast
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have := isIso_diskBoundaryFundamentalClass_compl_singleton (ModuleCat.of R R) k (pole (k + 1))
    have : IsIso t := by
      rw [ht, ← Category.assoc, hs,
        diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap_id _
          (B' := {pole (k + 1)}ᶜ) inter_subset_left]
      infer_instance
    -- An automorphism of `R` as a module over itself is right multiplication by a unit.
    have hbij := ConcreteCategory.bijective_of_isIso (t ≫ TopPair.singularHomologyMap
      (TopPair.ofSubsetMap _ hfU) (ModuleCat.of R R) _ ≫ inv (cellLocalClass univ
        (ModuleCat.of R R) (cellAttachingMap c' (pole _)) hx))
    exact (((Module.End.isUnit_iff _).2 hbij).map (RingEquiv.moduleEndSelf R).symm).unop

/-- **The cellular incidence numbers of real projective space.** The incidence coefficient of the
`i`-cell in the cellular boundary of the `(i + 1)`-cell of `RPᴺ`, with coefficients in a ring `R`,
is `1 + (-1) ^ (i + 1)` times a unit of `R`. -/
theorem exists_cellularIncidence_cwComplex_eq_one_add_neg_one_pow_mul
    (c : cell (univ : Set (RealProjectiveSpace N)) i)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) :
    ∃ u : Rˣ, cellularIncidence univ R i c c' = (1 + (-1) ^ (i + 1)) * u := by
  obtain ⟨μ, hμ, hunit⟩ :=
    exists_cellularIncidence_cwComplex_eq_mul R (le_of_cell_cwComplex c') c c'
  rcases Nat.even_or_odd i with he | ho
  · refine ⟨1, ?_⟩
    rw [hμ, he.add_one.neg_one_pow, add_neg_cancel, zero_mul, zero_mul]
  · obtain ⟨u, hu⟩ := hunit ho.pos
    exact ⟨u, hu ▸ hμ⟩

/-- For even `i`, the `i`-cell does not occur in the cellular boundary of the `(i + 1)`-cell of
`RPᴺ`. -/
@[simp]
theorem cellularIncidence_cwComplex_eq_zero_of_even (he : Even i)
    (c : cell (univ : Set (RealProjectiveSpace N)) i)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) :
    cellularIncidence univ R i c c' = 0 := by
  obtain ⟨u, hu⟩ := exists_cellularIncidence_cwComplex_eq_one_add_neg_one_pow_mul R c c'
  rw [hu, he.add_one.neg_one_pow, add_neg_cancel, zero_mul]

/-- For odd `i`, the incidence coefficient of the `i`-cell in the cellular boundary of the
`(i + 1)`-cell of `RPᴺ` is twice a unit. -/
theorem exists_cellularIncidence_cwComplex_eq_two_mul_of_odd (ho : Odd i)
    (c : cell (univ : Set (RealProjectiveSpace N)) i)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) :
    ∃ u : Rˣ, cellularIncidence univ R i c c' = 2 * u := by
  obtain ⟨u, hu⟩ := exists_cellularIncidence_cwComplex_eq_one_add_neg_one_pow_mul R c c'
  refine ⟨u, ?_⟩
  rw [hu, ho.add_one.neg_one_pow, one_add_one_eq_two]

end Ring

/-- Over `ℤ`, for odd `i`, the incidence number of the `i`-cell in the cellular boundary of the
`(i + 1)`-cell of `RPᴺ` is `±2`. -/
theorem cellularIncidence_cwComplex_eq_two_or_eq_neg_two_of_odd (ho : Odd i)
    (c : cell (univ : Set (RealProjectiveSpace N)) i)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (i + 1)) :
    cellularIncidence univ ℤ i c c' = 2 ∨ cellularIncidence univ ℤ i c c' = -2 := by
  obtain ⟨u, hu⟩ := exists_cellularIncidence_cwComplex_eq_two_mul_of_odd ℤ ho c c'
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact Or.inl (by rw [hu]; rfl)
  · exact Or.inr (by rw [hu]; rfl)

end TauCeti.RealProjectiveSpace
