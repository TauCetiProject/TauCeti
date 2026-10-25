/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.TietzeExtension
public import TauCeti.Topology.CWComplex.Classical.CellAction
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Induction

/-!
# Orbit spaces of free cellular actions are Hausdorff

Let a group `G` act on a Hausdorff CW complex `E` by homeomorphisms, such that each element of
`G` carries every open `n`-cell onto an open `n`-cell, and `g` carries an open cell onto itself
only when `g = 1`. This file proves that the orbit space `E / G` is Hausdorff.

The orbit space is not Hausdorff for a general free action by homeomorphisms, even when the orbit
map is a covering map, so the cellular hypotheses are essential. Nor does a classical CW structure
on the orbit space suffice by itself: Mathlib's classical CW complexes need not be Hausdorff.

The proof constructs, for two points `x` and `y` in different orbits, a continuous `G`-invariant
function `f : E → ℝ` with `f x = 1` and `f y = 0`
(`TauCeti.exists_invariant_continuousMap_one_zero`). It is built skeleton by skeleton. Choose a
representative cell in each `G`-orbit of `n`-cells. On a representative, extend the function
already built on its boundary sphere over the closed ball by the Tietze extension theorem,
prescribing the value `1` at the (at most one) interior point of the orbit of `x` and `0` at that
of `y`. Then transport this extension to the other cells of the orbit by the unique group element
carrying the representative to them. The function descends to a continuous function on the orbit
space separating the images of `x` and `y`.

## Main results

* `TauCeti.exists_invariant_continuousMap_one_zero`: points in different orbits are separated by
  a continuous `G`-invariant real function.
* `TauCeti.t2Space_orbitRel_quotient`: the orbit space `MulAction.orbitRel.Quotient G E` is
  Hausdorff.
* `IsQuotientCoveringMap.t2Space_of_cwComplex`: the base of the quotient covering map of such an
  action is Hausdorff.

## References

* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1 (free `G`-CW complexes
  and their orbit spaces).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Proposition A.3 (CW complexes are normal, by extending functions cell by cell).
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex
open scoped Pointwise

universe u

namespace TauCeti

variable {E : Type u} [TopologicalSpace E] [CWComplex (univ : Set E)]
  {G : Type*} [Group G] [MulAction G E]

section Cells

variable (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)

include hcell in
/-- Translation by a group element that permutes the open cells preserves every skeleton. -/
lemma smul_mem_skeletonLT [T2Space E] (g : G) {n : ℕ∞} {z : E}
    (hz : z ∈ (skeletonLT (univ : Set E) n : Set E)) :
    g • z ∈ (skeletonLT (univ : Set E) n : Set E) := by
  rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hz ⊢
  simp only [mem_iUnion] at hz ⊢
  obtain ⟨m, hm, i, hi⟩ := hz
  obtain ⟨j, hj⟩ := hcell g m i
  exact ⟨m, hm, j, hj ▸ smul_mem_smul_set hi⟩

variable (G) in
/-- Two `n`-cells are related when a group element carries the open cell of one onto the open
cell of the other. -/
def cellOrbitSetoid (n : ℕ) : Setoid (cell (univ : Set E) n) where
  r i j := ∃ g : G, g • openCell n i = openCell n j
  iseqv :=
    { refl _ := ⟨1, one_smul G _⟩
      symm := fun ⟨g, h⟩ ↦ ⟨g⁻¹, by rw [← h, inv_smul_smul]⟩
      trans := fun ⟨g, h⟩ ⟨g', h'⟩ ↦ ⟨g' * g, by rw [mul_smul, h, h']⟩ }

variable (G) in
/-- The chosen representative of the orbit of an `n`-cell. -/
def cellRep {n : ℕ} (j : cell (univ : Set E) n) : cell (univ : Set E) n :=
  (Quotient.mk (cellOrbitSetoid G n) j).out

lemma exists_smul_openCell_cellRep {n : ℕ} (j : cell (univ : Set E) n) :
    ∃ g : G, g • openCell n (cellRep G j) = openCell n j :=
  Quotient.mk_out (s := cellOrbitSetoid G n) j

variable (G) in
/-- A group element carrying the representative of the orbit of `j` onto `j`. -/
def cellElt {n : ℕ} (j : cell (univ : Set E) n) : G :=
  (exists_smul_openCell_cellRep j).choose

lemma cellElt_smul_openCell {n : ℕ} (j : cell (univ : Set E) n) :
    cellElt G j • openCell n (cellRep G j) = openCell n j :=
  (exists_smul_openCell_cellRep j).choose_spec

lemma cellRep_eq_of_smul_openCell {n : ℕ} {g : G} {i j : cell (univ : Set E) n}
    (h : g • openCell n i = openCell n j) : cellRep G i = cellRep G j :=
  congrArg Quotient.out (Quotient.sound (s := cellOrbitSetoid G n) ⟨g, h⟩)

include hfree in
/-- The element carrying the representative onto a cell is the only one doing so. -/
lemma eq_cellElt_of_smul_openCell {n : ℕ} {g : G} {j : cell (univ : Set E) n}
    (h : g • openCell n (cellRep G j) = openCell n j) : g = cellElt G j := by
  have : ((cellElt G j)⁻¹ * g) • openCell n (cellRep G j) = openCell n (cellRep G j) := by
    rw [mul_smul, h, inv_smul_eq_iff, cellElt_smul_openCell]
  exact (inv_mul_eq_one.1 (hfree _ n _ this)).symm

/-- A point of an open `n`-cell is the translate, by the chosen element, of a point of the open
cell of the representative. -/
lemma exists_cellElt_smul_map {n : ℕ} {z : E} {j : cell (univ : Set E) n}
    (hz : z ∈ openCell n j) :
    ∃ u : Fin n → ℝ, ‖u‖ < 1 ∧ cellElt G j • map n (cellRep G j) u = z := by
  rw [← cellElt_smul_openCell (G := G) j] at hz
  obtain ⟨w, ⟨u, hu, rfl⟩, rfl⟩ := hz
  exact ⟨u, mem_ball_zero_iff.1 hu, rfl⟩

include hcell hfree in
/-- The preimage in an open cell of any orbit contains at most one point. -/
private lemma subsingleton_openCell_inter_orbit {n : ℕ} (r : cell (univ : Set E) n) (a : E) :
    {v : Fin n → ℝ | ‖v‖ < 1 ∧ map n r v ∈ MulAction.orbit G a}.Subsingleton := by
  rintro v ⟨hv, hvo⟩ w ⟨hw, hwo⟩
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hvo
  obtain ⟨g', hg'⟩ := MulAction.mem_orbit_iff.1 hwo
  have h1 : (g' * g⁻¹) • map n r v = map n r w := by rw [← hg, ← hg', mul_smul, inv_smul_smul]
  have hw' : (g' * g⁻¹) • map n r v ∈ openCell n r := by
    rw [h1]
    exact ⟨w, mem_ball_zero_iff.2 hw, rfl⟩
  have h2 : g' * g⁻¹ = 1 :=
    eq_one_of_mem_openCell_of_smul_mem hcell hfree ⟨v, mem_ball_zero_iff.2 hv, rfl⟩ hw'
  rw [h2, one_smul] at h1
  exact ((map_eq_map_iff hv hw).1 h1).2

variable [T2Space E]

/-- A translation carrying an open cell onto an open cell carries the closed cell onto the
closed cell. -/
lemma smul_closedCell_of_smul_openCell [ContinuousConstSMul G E] {n : ℕ} {g : G}
    {i j : cell (univ : Set E) n} (h : g • openCell n i = openCell n j) :
    g • closedCell n i = closedCell n j := by
  rw [← closure_openCell_eq_closedCell, ← closure_openCell_eq_closedCell, ← closure_smul, h]

variable (G) in
/-- A stage of the construction of a separating invariant function: a continuous function on the
`n`-skeleton, invariant under the translations that preserve the skeleton, equal to `1` at `x`
and to `0` at `y` when these lie in the skeleton. -/
private structure SepStage (x y : E) (n : ℕ) where
  /-- The function on the `n`-skeleton. -/
  toFun : C(Unit × (skeletonLT (univ : Set E) n : Set E), ℝ)
  apply_smul (g : G) (z : E) (hz : z ∈ (skeletonLT (univ : Set E) n : Set E))
    (hgz : g • z ∈ (skeletonLT (univ : Set E) n : Set E)) :
    toFun ((), ⟨g • z, hgz⟩) = toFun ((), ⟨z, hz⟩)
  apply_left (hx : x ∈ (skeletonLT (univ : Set E) n : Set E)) : toFun ((), ⟨x, hx⟩) = 1
  apply_right (hy : y ∈ (skeletonLT (univ : Set E) n : Set E)) : toFun ((), ⟨y, hy⟩) = 0

/-- The empty `0`-skeleton carries the zero function. -/
private def SepStage.zero (x y : E) : SepStage G x y 0 where
  toFun := 0
  apply_smul _ _ hz := by simp [CWComplex.skeletonLT_zero_eq_empty] at hz
  apply_left hx := by simp [CWComplex.skeletonLT_zero_eq_empty] at hx
  apply_right hy := by simp [CWComplex.skeletonLT_zero_eq_empty] at hy

variable {x y : E}

include hcell hfree in
/-- The extension over the closed ball of an `n`-cell `r`: it restricts to the stage on the
boundary sphere and takes the value `1`, respectively `0`, at an interior point mapped into the
orbit of `x`, respectively of `y`. -/
private lemma SepStage.exists_extension (hxy : y ∉ MulAction.orbit G x) {n : ℕ}
    (S : SepStage G x y n) (r : cell (univ : Set E) n) :
    ∃ ψ : C(Fin n → ℝ, ℝ),
      (∀ v (hv : v ∈ sphere (0 : Fin n → ℝ) 1),
        ψ v = S.toFun ((), ⟨map n r v, cellFrontier_subset_skeletonLT n r ⟨v, hv, rfl⟩⟩)) ∧
      (∀ v, ‖v‖ < 1 → map n r v ∈ MulAction.orbit G x → ψ v = 1) ∧
      (∀ v, ‖v‖ < 1 → map n r v ∈ MulAction.orbit G y → ψ v = 0) := by
  classical
  set A := {v : Fin n → ℝ | ‖v‖ < 1 ∧ map n r v ∈ MulAction.orbit G x}
  set B := {v : Fin n → ℝ | ‖v‖ < 1 ∧ map n r v ∈ MulAction.orbit G y}
  -- The prescribed values on the closed set `sphere 0 1 ∪ (A ∪ B)`.
  let fn : E → ℝ := fun z ↦
    if hz : z ∈ (skeletonLT (univ : Set E) n : Set E) then S.toFun ((), ⟨z, hz⟩) else 0
  let h : (Fin n → ℝ) → ℝ := fun v ↦
    if v ∈ sphere (0 : Fin n → ℝ) 1 then fn (map n r v) else if v ∈ A then 1 else 0
  have hfn : ContinuousOn fn (skeletonLT (univ : Set E) n) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (S.toFun.continuous.comp
      (by fun_prop : Continuous fun z : (skeletonLT (univ : Set E) n : Set E) ↦ ((), z))).congr
      fun z ↦ by simp [fn, Set.domRestrict]
  have hsph : ContinuousOn h (sphere 0 1) :=
    (hfn.comp ((continuousOn n r).mono sphere_subset_closedBall)
      fun v hv ↦ cellFrontier_subset_skeletonLT n r ⟨v, hv, rfl⟩).congr fun v hv ↦ ite_eq_left hv
  have hA : A.Subsingleton := subsingleton_openCell_inter_orbit hcell hfree r x
  have hB : B.Subsingleton := subsingleton_openCell_inter_orbit hcell hfree r y
  have hAB : IsClosed (A ∪ B) := hA.isClosed.union hB.isClosed
  have hcont : ContinuousOn h (sphere 0 1 ∪ (A ∪ B)) :=
    hsph.union_of_isClosed ((hA.continuousOn h).union_of_isClosed
      (hB.continuousOn h) hA.isClosed hB.isClosed) isClosed_sphere hAB
  obtain ⟨ψ, hψ⟩ := ContinuousMap.exists_restrict_eq (isClosed_sphere.union hAB)
    ⟨_, hcont.domRestrict⟩
  have hψh (v) (hv : v ∈ sphere (0 : Fin n → ℝ) 1 ∪ (A ∪ B)) : ψ v = h v :=
    DFunLike.congr_fun hψ ⟨v, hv⟩
  have hns {v : Fin n → ℝ} (hv : ‖v‖ < 1) : v ∉ sphere (0 : Fin n → ℝ) 1 := fun hs ↦
    (mem_sphere_zero_iff_norm.1 hs ▸ hv).false
  refine ⟨ψ, fun v hv ↦ ?_, fun v hv hvx ↦ ?_, fun v hv hvy ↦ ?_⟩
  · rw [hψh v (.inl hv)]
    simp only [h, fn, ite_eq_left hv,
      dite_eq_left (cellFrontier_subset_skeletonLT n r ⟨v, hv, rfl⟩)]
  · have hvA : v ∈ A := ⟨hv, hvx⟩
    rw [hψh v (.inr (.inl hvA))]
    simp only [h, ite_eq_right (hns hv), ite_eq_left hvA]
  · -- A point mapped into both orbits would put `y` in the orbit of `x`.
    have hvA : v ∉ A := fun ⟨_, hvx⟩ ↦ by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hvx
      obtain ⟨g', hg'⟩ := MulAction.mem_orbit_iff.1 hvy
      refine hxy (MulAction.mem_orbit_iff.2 ⟨g'⁻¹ * g, ?_⟩)
      rw [mul_smul, hg, ← hg', inv_smul_smul]
    rw [hψh v (.inr (.inr ⟨hv, hvy⟩))]
    simp only [h, ite_eq_right (hns hv), ite_eq_right hvA]

include hfree in
/-- On an open cell, the glued successor map is the extension on the representative cell. -/
private lemma apply_gluedMap_openCell {n : ℕ}
    (ψ : cell (univ : Set E) n → C(Fin n → ℝ, ℝ))
    (L : (r : cell (univ : Set E) n) → C(closedCell n r, ℝ))
    (hL : ∀ (r : cell (univ : Set E) n) (v : closedBall (0 : Fin n → ℝ) 1),
      L r ⟨map n r v, v, v.2, rfl⟩ = ψ r v)
    (hmem : ∀ (j : cell (univ : Set E) n) (v : closedBall (0 : Fin n → ℝ) 1),
      (cellElt G j)⁻¹ • map n j v ∈ closedCell n (cellRep G j))
    (F : C(Unit × (skeletonLT (univ : Set E) ((n + 1 : ℕ) : ℕ∞) : Set E), ℝ))
    (hFK : ∀ (j : cell (univ : Set E) n) (z : Unit)
      (v : closedBall (0 : Fin n → ℝ) 1),
      F (z, ⟨map n j v, map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 v.2)⟩) =
        L (cellRep G j) ⟨(cellElt G j)⁻¹ • map n j v, hmem j v⟩)
    (j r : cell (univ : Set E) n) (hr : cellRep G j = r) (g : G)
    (hg : g • openCell n r = openCell n j) (u : Fin n → ℝ) (hu : ‖u‖ < 1)
    (hu' : g • map n r u ∈ (skeletonLT (univ : Set E) ((n + 1 : ℕ) : ℕ∞) : Set E)) :
    F ((), ⟨g • map n r u, hu'⟩) = ψ r u := by
  subst hr
  obtain rfl := eq_cellElt_of_smul_openCell hfree hg
  have hw : cellElt G j • map n (cellRep G j) u ∈ openCell n j :=
    hg ▸ smul_mem_smul_set ⟨u, mem_ball_zero_iff.2 hu, rfl⟩
  have hv := ball_subset_closedBall (map_symm_mem_ball n hw)
  have hF_eq :
      F ((), ⟨cellElt G j • map n (cellRep G j) u, hu'⟩) =
        F ((), ⟨map n j ((map n j).symm (cellElt G j • map n (cellRep G j) u)),
          map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 hv)⟩) :=
    congrArg F (Prod.ext rfl (Subtype.ext (map_map_symm n hw).symm))
  rw [hF_eq, hFK j () ⟨_, hv⟩,
    ← hL (cellRep G j) ⟨u, ball_subset_closedBall (mem_ball_zero_iff.2 hu)⟩]
  exact congrArg (L _) (Subtype.ext (by simp [map_map_symm n hw]))

include hcell hfree in
/-- **The inductive step.** A stage on the `n`-skeleton extends to a stage on the
`(n + 1)`-skeleton. -/
private theorem SepStage.exists_succ [ContinuousConstSMul G E] (hxy : y ∉ MulAction.orbit G x)
    {n : ℕ} (S : SepStage G x y n) :
    ∃ S' : SepStage G x y (n + 1), ∀ (z : E) (hz : z ∈ (skeletonLT (univ : Set E) n : Set E)),
      S'.toFun ((), ⟨z, skeletonLT_mono (by exact_mod_cast n.le_succ) hz⟩) =
        S.toFun ((), ⟨z, hz⟩) := by
  -- Extend over the closed ball of every `n`-cell, descend each extension to the closed cell, and
  -- read the cell `j` through the representative of its orbit. The glued map is invariant because
  -- translating an open `n`-cell does not change the representative and composes the elements.
  choose ψ hψs hψx hψy using S.exists_extension hcell hfree hxy
  -- The extension `ψ r` descends to the closed cell of `r` along its characteristic map.
  let f : C((skeletonLT (univ : Set E) n : Set E), ℝ) :=
    S.toFun.comp ⟨fun z ↦ ((), z), by fun_prop⟩
  choose L hL using fun r ↦ exists_continuousMap_closedCell_comp_map r (ψ r) f
    fun v hv ↦ hψs r v hv
  -- On the closed cell of `j`, read the descended extension of the representative.
  have hmem (j : cell (univ : Set E) n) (v : closedBall (0 : Fin n → ℝ) 1) :
      (cellElt G j)⁻¹ • map n j v ∈ closedCell n (cellRep G j) := by
    rw [← mem_smul_set_iff_inv_smul_mem,
      smul_closedCell_of_smul_openCell (cellElt_smul_openCell j)]
    exact ⟨v, v.2, rfl⟩
  let K (j : cell (univ : Set E) n) : C(Unit × closedBall (0 : Fin n → ℝ) 1, ℝ) :=
    (L (cellRep G j)).comp ⟨fun p ↦ ⟨(cellElt G j)⁻¹ • map n j p.2, hmem j p.2⟩,
      ((continuous_const_smul _).comp
        ((continuous_map_closedBall j).comp continuous_snd)).subtype_mk _⟩
  have hK (j : cell (univ : Set E) n) (z : Unit) (v : closedBall (0 : Fin n → ℝ) 1)
      (hv : (v : Fin n → ℝ) ∈ sphere 0 1) :
      K j (z, v) = S.toFun (z, ⟨map n j v, cellFrontier_subset_skeletonLT n j ⟨v, hv, rfl⟩⟩) := by
    have hz : map n j v ∈ (skeletonLT (univ : Set E) n : Set E) :=
      cellFrontier_subset_skeletonLT n j ⟨v, hv, rfl⟩
    obtain ⟨u, hu, hu'⟩ := hmem j v
    -- The point of the representative lies on its boundary sphere, since it is in the skeleton.
    have hus : u ∈ sphere (0 : Fin n → ℝ) 1 := by
      rcases (mem_closedBall_zero_iff.1 hu).lt_or_eq with hu1 | hu1
      · refine absurd ?_ (map_notMem_skeletonLT (cellRep G j) hu1)
        rw [hu']
        exact smul_mem_skeletonLT hcell _ hz
      · exact mem_sphere_zero_iff_norm.2 hu1
    let vu : closedBall (0 : Fin n → ℝ) 1 := ⟨u, hu⟩
    have hKL : K j (z, v) =
        L (cellRep G j) ⟨map n (cellRep G j) vu, vu, vu.2, rfl⟩ :=
      congrArg (L _) (Subtype.ext hu'.symm)
    cases z
    rw [hKL, hL, hψs _ u hus,
      ← S.apply_smul (cellElt G j)⁻¹ _ hz (smul_mem_skeletonLT hcell _ hz)]
    simp only [hu']
  obtain ⟨F, hF, hFK⟩ := exists_continuousMap_prod_skeletonLT_succ S.toFun K hK
  have hFKL (j : cell (univ : Set E) n) (z : Unit)
      (v : closedBall (0 : Fin n → ℝ) 1) :
      F (z, ⟨map n j v, map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 v.2)⟩) =
        L (cellRep G j) ⟨(cellElt G j)⁻¹ • map n j v, hmem j v⟩ := by
    rw [hFK]
    rfl
  have hFeq {a b : E} (ha : a ∈ (skeletonLT (univ : Set E) ((n + 1 : ℕ) : ℕ∞) : Set E))
      (hb : b ∈ (skeletonLT (univ : Set E) ((n + 1 : ℕ) : ℕ∞) : Set E)) (hab : a = b) :
      F ((), ⟨a, ha⟩) = F ((), ⟨b, hb⟩) := by
    subst hab; rfl
  have hFopen := apply_gluedMap_openCell hfree ψ L hL hmem F hFKL
  -- A point of the `(n + 1)`-skeleton outside the `n`-skeleton is in an open `n`-cell.
  have hcases {z : E} (hz : z ∈ (skeletonLT (univ : Set E) ((n + 1 : ℕ) : ℕ∞) : Set E)) :
      z ∈ (skeletonLT (univ : Set E) n : Set E) ∨ ∃ j : cell (univ : Set E) n, ∃ u, ‖u‖ < 1 ∧
        cellElt G j • map n (cellRep G j) u = z := by
    refine (mem_skeletonLT_or_exists_map hz).imp_right fun ⟨j, v, hv, hvz⟩ ↦ ⟨j, ?_⟩
    exact exists_cellElt_smul_map ⟨v, mem_ball_zero_iff.2 hv, hvz⟩
  refine ⟨⟨F, fun g z hz hgz ↦ ?_, fun hx ↦ ?_, fun hy ↦ ?_⟩, hF ()⟩
  · rcases hcases hz with hzn | ⟨j, u, hu, rfl⟩
    · rw [hF () z hzn, ← S.apply_smul g z hzn (smul_mem_skeletonLT hcell g hzn),
        ← hF () _ (smul_mem_skeletonLT hcell g hzn)]
    · obtain ⟨j', hj'⟩ := hcell g n j
      have hg' : (g * cellElt G j) • openCell n (cellRep G j) = openCell n j' := by
        rw [mul_smul, cellElt_smul_openCell, hj']
      rw [hFeq hgz (by rwa [← mul_smul] at hgz) (mul_smul g _ _).symm,
        hFopen j' _ (cellRep_eq_of_smul_openCell hj').symm _ hg' u hu,
        hFopen j _ rfl _ (cellElt_smul_openCell j) u hu]
  · rcases hcases hx with hxn | ⟨j, u, hu, hux⟩
    · rw [hF () x hxn, S.apply_left hxn]
    · subst hux
      rw [hFopen j _ rfl _ (cellElt_smul_openCell j) u hu]
      exact hψx _ u hu (MulAction.mem_orbit_iff.2 ⟨(cellElt G j)⁻¹, inv_smul_smul _ _⟩)
  · rcases hcases hy with hyn | ⟨j, u, hu, huy⟩
    · rw [hF () y hyn, S.apply_right hyn]
    · subst huy
      rw [hFopen j _ rfl _ (cellElt_smul_openCell j) u hu]
      exact hψy _ u hu (MulAction.mem_orbit_iff.2 ⟨(cellElt G j)⁻¹, inv_smul_smul _ _⟩)

variable [ContinuousConstSMul G E]

variable (x y) in
/-- The stages on the successive skeleta, each extending the previous one. -/
private def sepSeq (hxy : y ∉ MulAction.orbit G x) : (n : ℕ) → SepStage G x y n
  | 0 => SepStage.zero x y
  | n + 1 => ((sepSeq hxy n).exists_succ hcell hfree hxy).choose

include hcell hfree in
/-- **Invariant separating functions.** Let `G` act on a Hausdorff CW complex `E` by homeomorphisms
so that every element carries each open `n`-cell onto an open `n`-cell, and only `1` carries an open
cell onto itself. Then two points `x` and `y` in different orbits are separated by a continuous
`G`-invariant function `f : E → ℝ` with `f x = 1` and `f y = 0`. -/
theorem exists_invariant_continuousMap_one_zero (hxy : y ∉ MulAction.orbit G x) :
    ∃ f : C(E, ℝ), (∀ (g : G) (z : E), f (g • z) = f z) ∧ f x = 1 ∧ f y = 0 := by
  obtain ⟨F, hF⟩ := exists_continuousMap_prod_complex_of_skeletonLT (k := 0)
    (fun j ↦ (sepSeq hcell hfree x y hxy (0 + j)).toFun)
    fun j _ z hz ↦ ((sepSeq hcell hfree x y hxy (0 + j)).exists_succ hcell hfree hxy).choose_spec
      z hz
  let f : C(E, ℝ) := F.comp ⟨fun z ↦ ((), ⟨z, mem_univ z⟩), by fun_prop⟩
  have hf (z : E) (j : ℕ) (hz : z ∈ (skeletonLT (univ : Set E) ((0 + j : ℕ) : ℕ∞) : Set E)) :
      f z = (sepSeq hcell hfree x y hxy (0 + j)).toFun ((), ⟨z, hz⟩) :=
    hF j () z hz
  refine ⟨f, fun g z ↦ ?_, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add 0 (mem_univ z)
    rw [hf z j hj, hf _ j (smul_mem_skeletonLT hcell g hj), SepStage.apply_smul]
  · obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add 0 (mem_univ x)
    rw [hf x j hj, SepStage.apply_left]
  · obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add 0 (mem_univ y)
    rw [hf y j hj, SepStage.apply_right]

include hcell hfree in
/-- A quotient map of `E` whose fibres are the orbits has Hausdorff target. -/
private theorem t2Space_of_isQuotientMap {B : Type*} [TopologicalSpace B] {p : E → B}
    (hp : IsQuotientMap p) (hpG : ∀ a b, p a = p b ↔ a ∈ MulAction.orbit G b) : T2Space B := by
  refine ⟨fun b b' hbb' ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hp.surjective b
  obtain ⟨y, rfl⟩ := hp.surjective b'
  obtain ⟨f, hf, hfx, hfy⟩ := exists_invariant_continuousMap_one_zero hcell hfree
    (x := x) (y := y) fun h ↦ hbb' ((hpG x y).2 (MulAction.mem_orbit_symm.1 h))
  have hfp : Function.FactorsThrough f p := fun a b hab ↦ by
    obtain ⟨g, rfl⟩ := (hpG a b).1 hab
    exact hf g b
  let p' : C(E, B) := ⟨p, hp.continuous⟩
  have hlift (z : E) : hp.lift (f := p') f hfp (p z) = f z :=
    DFunLike.congr_fun (hp.lift_comp (f := p') f hfp) z
  exact separated_by_continuous (hp.lift (f := p') f hfp).continuous (by simp [hlift, hfx, hfy])

include hcell hfree in
/-- **The orbit space of a free cellular action is Hausdorff.** Let `G` act on a Hausdorff CW
complex `E` by homeomorphisms so that every element carries each open `n`-cell onto an open
`n`-cell, and only `1` carries an open cell onto itself. Then the orbit space is Hausdorff. -/
theorem t2Space_orbitRel_quotient : T2Space (MulAction.orbitRel.Quotient G E) :=
  t2Space_of_isQuotientMap hcell hfree isQuotientMap_quotient_mk'
    fun _ _ ↦ Quotient.eq''.trans MulAction.orbitRel_apply

end Cells

end TauCeti

/-- **The base of the quotient covering map of a free cellular action is Hausdorff.** Let `G` act
on a Hausdorff CW complex `E` so that every element carries each open `n`-cell onto an open
`n`-cell, and only `1` carries an open cell onto itself. If `p : E → B` is the quotient covering
map of the action, then `B` is Hausdorff. -/
theorem IsQuotientCoveringMap.t2Space_of_cwComplex {E B : Type*} [TopologicalSpace E]
    [T2Space E] [CWComplex (univ : Set E)] [TopologicalSpace B] {G : Type*} [Group G]
    [MulAction G E] {p : E → B} (hp : IsQuotientCoveringMap p G)
    (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
      ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
    (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
      g • openCell n i = openCell n i → g = 1) :
    T2Space B :=
  have := hp.toContinuousConstSMul
  TauCeti.t2Space_of_isQuotientMap hcell hfree hp.toIsQuotientMap
    fun _ _ ↦ hp.apply_eq_iff_mem_orbit
