/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Analysis.Normed.Module.Ball.Radial.PuncturedBall
public import TauCeti.Topology.CWComplex.Classical.OpenCells
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Neighborhood

/-!
# A skeleton punctured at the centre of a top cell

Let `C` be a relative CW complex, `Xⁿ = skeletonLT C (n + 1)` its `n`-skeleton and `j` an
`n`-cell with characteristic map `χ = map n j` and centre `b = χ 0`. Removing the centre from
`Xⁿ` leaves `TauCeti.skeletonDiffCenter j`, and removing the whole inner half `χ(ball 0 2⁻¹)` of
the open cell leaves the smaller set `TauCeti.skeletonDiffCore j`. The first deforms into the
second relative to the second (`TauCeti.skeletonDiffCenterHomotopyRel`): inside the open cell,
read through `χ`, a point `y ≠ 0` of norm less than `2⁻¹` moves along its ray out to the sphere
of radius `2⁻¹` (`TauCeti.puncturedBallPush`), and every other point stays fixed.

When `j` is the only `n`-cell, `TauCeti.skeletonDiffCore j` is the neighbourhood
`TauCeti.skeletonNeighborhood C n` of the `(n-1)`-skeleton
(`TauCeti.skeletonDiffCore_eq_skeletonNeighborhood`), which in turn deforms onto `Xⁿ⁻¹ =
skeletonLT C n` relative to `Xⁿ⁻¹` (`TauCeti.skeletonNeighborhoodHomotopyRel`). Together these
say that the `n`-skeleton punctured at the centre of its only `n`-cell deforms onto its
`(n-1)`-skeleton. This is the topological input of the identification, for a fibration over a CW
complex with a single top cell, of the homology relative to the part over the `(n-1)`-skeleton
with the local homology along the fibre over the centre of the top cell.

The radial push is defined only off the centre, so it cannot be read through `χ` on the whole
closed cell, as `TauCeti.cellDeformation` does. It is continuous on the punctured skeleton
because it is the identity outside the closed core `χ(closedBall 0 2⁻¹)`, which is compact, while
on the open cell, which is open in every subset of `Xⁿ` (`TauCeti.isOpen_preimage_val_openCell`),
the inverse of `χ` is continuous.

## Main definitions

* `TauCeti.skeletonDiffCenter j`: the `n`-skeleton with the centre of the `n`-cell `j` removed.
* `TauCeti.skeletonDiffCore j`: the `n`-skeleton with the inner half of the `n`-cell `j` removed.
* `TauCeti.skeletonDiffCenterEndpoint j`: the endpoint of the deformation.
* `TauCeti.skeletonDiffCenterHomotopyRel j`: the deformation of `TauCeti.skeletonDiffCenter j`
  into `TauCeti.skeletonDiffCore j`, relative to `TauCeti.skeletonDiffCore j`.

## Main results

* `TauCeti.skeletonDiffCenterHomotopyRel_map`, `TauCeti.skeletonDiffCenterEndpoint_map`: inside
  the open cell, read through its characteristic map, the deformation is the radial push.
* `TauCeti.skeletonDiffCenterEndpoint_mem`: the endpoint takes values in
  `TauCeti.skeletonDiffCore j`.
* `TauCeti.skeletonDiffCore_eq_skeletonNeighborhood`: for a single `n`-cell, the complement of the
  inner half of the cell is `TauCeti.skeletonNeighborhood C n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2 and the Appendix "Topology of Cell Complexes".
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex unitInterval

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {D : Set X} {C : Set X} [RelCWComplex C D]
  {n : ℕ}

/-! ### The punctured skeleton and its deformation -/

variable (j : cell C n)

/-- The `n`-skeleton `skeletonLT C (n + 1)` with the centre `map n j 0` of the `n`-cell `j`
removed. -/
def skeletonDiffCenter : Set X :=
  (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) \ {map n j 0}

/-- The `n`-skeleton `skeletonLT C (n + 1)` with the inner half `map n j '' ball 0 2⁻¹` of the
`n`-cell `j` removed. -/
def skeletonDiffCore : Set X :=
  (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) \ map n j '' ball 0 2⁻¹

/-- A point lies in the punctured skeleton when it lies in the `n`-skeleton and is not the centre
of the cell `j`. -/
lemma mem_skeletonDiffCenter {x : X} :
    x ∈ skeletonDiffCenter j ↔
      x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) ∧ x ≠ map n j 0 :=
  Iff.rfl

/-- A point lies in the complement of the inner half of the cell `j` when it lies in the
`n`-skeleton and is not the image of a vector of norm less than `2⁻¹`. -/
lemma mem_skeletonDiffCore {x : X} :
    x ∈ skeletonDiffCore j ↔ x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) ∧
      ∀ y : Fin n → ℝ, ‖y‖ < 2⁻¹ → map n j y ≠ x := by
  simp [skeletonDiffCore]

/-- The complement of the inner half of the cell lies in the complement of its centre. -/
lemma skeletonDiffCore_subset_skeletonDiffCenter : skeletonDiffCore j ⊆ skeletonDiffCenter j :=
  sdiff_subset_sdiff_right <| singleton_subset_iff.2 ⟨0, mem_ball_self (by norm_num), rfl⟩

/-- The `(n-1)`-skeleton lies in the complement of the inner half of the `n`-cell `j`. -/
lemma skeletonLT_subset_skeletonDiffCore : (skeletonLT C n : Set X) ⊆ skeletonDiffCore j := by
  refine fun x hx ↦ ⟨skeletonLT_mono (mod_cast n.le_succ) hx, ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact map_notMem_skeletonLT j ((mem_ball_zero_iff.1 hy).trans (by norm_num)) hx

/-- The `(n-1)`-skeleton lies in the complement of the centre of the `n`-cell `j`. -/
lemma skeletonLT_subset_skeletonDiffCenter : (skeletonLT C n : Set X) ⊆ skeletonDiffCenter j :=
  (skeletonLT_subset_skeletonDiffCore j).trans (skeletonDiffCore_subset_skeletonDiffCenter j)

/-- **For a single `n`-cell, removing the inner half of the cell is removing the inner halves of
all `n`-cells**: the complement of the inner half of `j` is `TauCeti.skeletonNeighborhood C n`. -/
lemma skeletonDiffCore_eq_skeletonNeighborhood [Subsingleton (cell C n)] :
    skeletonDiffCore j = skeletonNeighborhood C n := by
  ext x
  simp only [skeletonDiffCore, mem_sdiff, mem_skeletonNeighborhood, mem_image, mem_ball_zero_iff,
    not_exists, not_and]
  refine and_congr_right fun _ ↦ ⟨fun h i y hy ↦ Subsingleton.elim i j ▸ h y hy, fun h ↦ h j⟩

omit [T2Space X] in
/-- A point of the open cell `j` that lies outside the inner half of the cell has coordinates of
norm at least `2⁻¹`. -/
private lemma le_norm_map_symm {x : X} (hx : x ∈ openCell (C := C) n j)
    (hxc : x ∉ map n j '' ball 0 2⁻¹) : (2 : ℝ)⁻¹ ≤ ‖(map n j).symm x‖ :=
  not_lt.1 fun h ↦ hxc ⟨_, mem_ball_zero_iff.2 h, map_map_symm n hx⟩

/-- The push of the punctured ball of radius `2⁻¹` stays in the open unit ball. -/
private lemma norm_puncturedBallPush_lt_one (t : I) {y : Fin n → ℝ} (hy : ‖y‖ < 1) :
    ‖puncturedBallPush 2⁻¹ t y‖ < 1 :=
  (norm_puncturedBallPush_le _ t y).trans_lt (max_lt hy (by norm_num))

/-- The radial push read through the characteristic map of `j` on its open cell, and the identity
elsewhere. -/
private def pushFun (q : I × X) : X :=
  open Classical in
  if q.2 ∈ openCell (C := C) n j then map n j (puncturedBallPush 2⁻¹ q.1 ((map n j).symm q.2))
  else q.2

omit [T2Space X] in
private lemma pushFun_of_mem {t : I} {x : X} (hx : x ∈ openCell (C := C) n j) :
    pushFun j (t, x) = map n j (puncturedBallPush 2⁻¹ t ((map n j).symm x)) := by
  simp [pushFun, hx]

omit [T2Space X] in
private lemma pushFun_of_notMem {t : I} {x : X} (hx : x ∉ openCell (C := C) n j) :
    pushFun j (t, x) = x := by
  simp [pushFun, hx]

omit [T2Space X] in
/-- Outside the inner half of the cell, the push is the identity. -/
private lemma pushFun_of_notMem_image (t : I) {x : X} (hx : x ∉ map n j '' ball 0 2⁻¹) :
    pushFun j (t, x) = x := by
  by_cases hxo : x ∈ openCell (C := C) n j
  · rw [pushFun_of_mem j hxo, puncturedBallPush_of_le_norm t (le_norm_map_symm j hxo hx),
      map_map_symm n hxo]
  · exact pushFun_of_notMem j hxo

private lemma pushFun_mem_skeletonDiffCenter (t : I) {x : X} (hx : x ∈ skeletonDiffCenter j) :
    pushFun j (t, x) ∈ skeletonDiffCenter j := by
  by_cases hxo : x ∈ openCell (C := C) n j
  · have hy := map_symm_mem_ball n hxo
    have hy0 := map_symm_ne_zero n hxo hx.2
    have hz := norm_puncturedBallPush_lt_one t (mem_ball_zero_iff.1 hy)
    rw [pushFun_of_mem j hxo]
    refine ⟨map_mem_skeletonLT_succ j hz.le, fun h ↦ puncturedBallPush_ne_zero 2⁻¹ t hy0 ?_⟩
    exact ((map_eq_map_iff hz (by simp)).1 h).2
  · rwa [pushFun_of_notMem j hxo]

private lemma continuous_pushFun :
    Continuous fun q : I × skeletonDiffCenter j ↦ pushFun j (q.1, q.2) := by
  refine continuous_iff_continuousAt.2 fun ⟨t, x⟩ ↦ ?_
  -- The open cell is open in the punctured skeleton.
  have hU : IsOpen (Subtype.val ⁻¹' openCell (C := C) n j : Set (skeletonDiffCenter j)) :=
    isOpen_preimage_val_openCell n sdiff_subset j
  by_cases hxo : (x : X) ∈ openCell (C := C) n j
  · -- On the open cell, the push is the radial push read through the characteristic map.
    have hsymm₀ : ContinuousAt (fun z : skeletonDiffCenter j ↦ (map n j).symm z) x :=
      ((continuousOn_symm n j).comp continuous_subtypeVal.continuousOn
        fun z hz ↦ by rwa [target_map_eq_openCell]).continuousAt (hU.mem_nhds hxo)
    have hsymm : ContinuousAt (fun q : I × skeletonDiffCenter j ↦ (map n j).symm q.2) (t, x) :=
      ContinuousAt.comp (g := fun z : skeletonDiffCenter j ↦ (map n j).symm z) hsymm₀
        continuous_snd.continuousAt
    have hy := map_symm_mem_ball n hxo
    have hpush : ContinuousAt (fun q : I × skeletonDiffCenter j ↦
        puncturedBallPush 2⁻¹ q.1 ((map n j).symm q.2)) (t, x) :=
      ContinuousAt.comp (f := fun q : I × skeletonDiffCenter j ↦ (q.1, (map n j).symm q.2))
        (continuousAt_puncturedBallPush 2⁻¹ (map_symm_ne_zero n (x := (x : X)) hxo x.property.2))
        (continuous_fst.continuousAt.prodMk hsymm)
    have hmap : ContinuousAt (map n j) (puncturedBallPush 2⁻¹ t ((map n j).symm x)) :=
      (continuousOn n j).continuousAt <| Filter.mem_of_superset (isOpen_ball.mem_nhds
        (mem_ball_zero_iff.2 (norm_puncturedBallPush_lt_one t (mem_ball_zero_iff.1 hy))))
        ball_subset_closedBall
    refine (ContinuousAt.comp (x := (t, x))
      (f := fun q : I × skeletonDiffCenter j ↦ puncturedBallPush 2⁻¹ q.1 ((map n j).symm q.2))
      hmap
      hpush).congr ?_
    filter_upwards [prod_mem_nhds Filter.univ_mem (hU.mem_nhds hxo)] with q hq
    exact (pushFun_of_mem j hq.2).symm
  · -- Off the closed inner half of the cell, the push is the identity.
    have hK : IsClosed (map n j '' closedBall (0 : Fin n → ℝ) 2⁻¹) :=
      ((isCompact_closedBall 0 _).image_of_continuousOn
        ((continuousOn n j).mono (closedBall_subset_closedBall (by norm_num)))).isClosed
    have hxK : (x : X) ∉ map n j '' closedBall 0 2⁻¹ := fun ⟨y, hy, hyx⟩ ↦
      hxo (hyx ▸ ⟨y, mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hy).trans_lt
        (by norm_num)), rfl⟩)
    refine (continuous_subtypeVal.comp continuous_snd).continuousAt.congr ?_
    filter_upwards [prod_mem_nhds Filter.univ_mem
      ((hK.isOpen_compl.preimage continuous_subtypeVal).mem_nhds hxK)] with q hq
    exact (pushFun_of_notMem_image j q.1 fun ⟨y, hy, hyx⟩ ↦
      hq.2 ⟨y, ball_subset_closedBall hy, hyx⟩).symm

/-- The radial push off the centre of the `n`-cell `j`, as a homotopy of the punctured
skeleton. -/
private def pushMap : C(I × skeletonDiffCenter j, skeletonDiffCenter j) :=
  ⟨fun q ↦ ⟨pushFun j (q.1, q.2), pushFun_mem_skeletonDiffCenter j q.1 q.2.property⟩,
    (continuous_pushFun j).subtype_mk _⟩

private lemma pushMap_apply (q : I × skeletonDiffCenter j) :
    (pushMap j q : X) = pushFun j (q.1, q.2) :=
  rfl

/-- The endpoint of `TauCeti.skeletonDiffCenterHomotopyRel`: inside the open `n`-cell `j`, read
through its characteristic map, it sends a point `y ≠ 0` of norm less than `2⁻¹` to `(2 ‖y‖)⁻¹ • y`
on the sphere of radius `2⁻¹`, and it fixes every other point. It takes values in
`TauCeti.skeletonDiffCore j`. -/
def skeletonDiffCenterEndpoint : C(skeletonDiffCenter j, skeletonDiffCenter j) :=
  (pushMap j).curry 1

/-- **The `n`-skeleton punctured at the centre of an `n`-cell deforms into the complement of the
inner half of the cell, relative to that complement.** Inside the open cell `j`, read through its
characteristic map, a point `y ≠ 0` with `‖y‖ < 2⁻¹` moves along its ray at time `t` to
`(1 - t + t (2 ‖y‖)⁻¹) • y`; every other point stays fixed. -/
def skeletonDiffCenterHomotopyRel :
    (ContinuousMap.id (skeletonDiffCenter j)).HomotopyRel (skeletonDiffCenterEndpoint j)
      (Subtype.val ⁻¹' skeletonDiffCore j) where
  toContinuousMap := pushMap j
  map_zero_left x := Subtype.ext <| by
    rw [ContinuousMap.toFun_eq_coe, ContinuousMap.id_apply, pushMap_apply]
    by_cases hxo : (x : X) ∈ openCell (C := C) n j
    · rw [pushFun_of_mem j hxo, puncturedBallPush_zero, map_map_symm n hxo]
    · exact pushFun_of_notMem j hxo
  map_one_left _ := rfl
  prop' t x hx := Subtype.ext (pushFun_of_notMem_image j t hx.2)

private lemma coe_skeletonDiffCenterHomotopyRel_apply (t : I) (x : skeletonDiffCenter j) :
    (skeletonDiffCenterHomotopyRel j (t, x) : X) = pushFun j (t, x) :=
  rfl

/-- Inside the open cell `j`, read through its characteristic map, the deformation at time `t` is
the radial push `TauCeti.puncturedBallPush 2⁻¹ t`. -/
lemma skeletonDiffCenterHomotopyRel_map (t : I) {y : Fin n → ℝ} (hy : ‖y‖ < 1)
    (x : skeletonDiffCenter j) (hx : (x : X) = map n j y) :
    (skeletonDiffCenterHomotopyRel j (t, x) : X) = map n j (puncturedBallPush 2⁻¹ t y) := by
  have hy' : y ∈ (map n j).source := by rw [source_eq]; exact mem_ball_zero_iff.2 hy
  rw [coe_skeletonDiffCenterHomotopyRel_apply,
    pushFun_of_mem j (hx ▸ mem_image_of_mem _ (mem_ball_zero_iff.2 hy)), hx,
    (map n j).left_inv hy']

/-- Inside the open cell `j`, read through its characteristic map, the endpoint of the
deformation is the radial push `TauCeti.puncturedBallPush 2⁻¹ 1`. -/
lemma skeletonDiffCenterEndpoint_map {y : Fin n → ℝ} (hy : ‖y‖ < 1)
    (x : skeletonDiffCenter j) (hx : (x : X) = map n j y) :
    (skeletonDiffCenterEndpoint j x : X) = map n j (puncturedBallPush 2⁻¹ 1 y) := by
  rw [← (skeletonDiffCenterHomotopyRel j).apply_one, skeletonDiffCenterHomotopyRel_map j 1 hy x hx]

/-- The deformation fixes every point outside the inner half of the cell `j`. -/
@[simp]
lemma skeletonDiffCenterHomotopyRel_apply_of_notMem (t : I) (x : skeletonDiffCenter j)
    (hx : (x : X) ∉ map n j '' ball 0 2⁻¹) : skeletonDiffCenterHomotopyRel j (t, x) = x :=
  Subtype.ext ((coe_skeletonDiffCenterHomotopyRel_apply j t x).trans
    (pushFun_of_notMem_image j t hx))

/-- The endpoint of the deformation fixes every point outside the inner half of the cell `j`. -/
@[simp]
lemma skeletonDiffCenterEndpoint_apply_of_notMem (x : skeletonDiffCenter j)
    (hx : (x : X) ∉ map n j '' ball 0 2⁻¹) : skeletonDiffCenterEndpoint j x = x := by
  rw [← (skeletonDiffCenterHomotopyRel j).apply_one,
    skeletonDiffCenterHomotopyRel_apply_of_notMem j 1 x hx]

/-- The endpoint of the deformation takes values in the complement of the inner half of the
cell. -/
lemma skeletonDiffCenterEndpoint_mem (x : skeletonDiffCenter j) :
    (skeletonDiffCenterEndpoint j x : X) ∈ skeletonDiffCore j := by
  refine ⟨(skeletonDiffCenterEndpoint j x).property.1, ?_⟩
  rw [skeletonDiffCenterEndpoint, ContinuousMap.curry_apply, pushMap_apply]
  by_cases hxo : (x : X) ∈ openCell (C := C) n j
  · have hy0 := map_symm_ne_zero n (x := (x : X)) hxo x.property.2
    have hz := norm_puncturedBallPush_lt_one 1 (mem_ball_zero_iff.1 (map_symm_mem_ball n hxo))
    rw [pushFun_of_mem j hxo]
    rintro ⟨y, hy, h⟩
    rw [mem_ball_zero_iff] at hy
    obtain rfl := ((map_eq_map_iff (hy.trans (by norm_num)) hz).1 h).2
    exact (le_norm_puncturedBallPush_one 2⁻¹ hy0).not_gt hy
  · rw [pushFun_of_notMem j hxo]
    rintro ⟨y, hy, hyx⟩
    exact hxo (hyx ▸ ⟨y, ball_subset_ball (by norm_num) hy, rfl⟩)

end TauCeti
