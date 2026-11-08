/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.CharacteristicMap
public import TauCeti.AlgebraicTopology.Singular.Fibration.Skeleton

/-!
# The skeletal filtration of a Serre fibration over the cells

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta
`Xⁿ = skeletonLT C (n + 1)`. The terms `Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` of the first page of the spectral
sequence of the filtration `Eₙ = p⁻¹(Xⁿ)` are computed over the `n`-cells. Pull `p` back along the
characteristic maps of the `n`-cells, assembled into one map `χ : ∐ⱼ Dⁿ ⟶ B`
(`TauCeti.sigmaCellMap`), to get a Serre fibration `P ⟶ ∐ⱼ Dⁿ`; let `∂P` be its part over
the boundary spheres. The projection of `P` to `E` is a map of pairs
`(P, ∂P) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` (`TauCeti.TopCat.cellPullbackPairMap`), and it induces
isomorphisms on relative singular homology in every degree
(`TauCeti.TopCat.isIso_singularHomologyMap_cellPullbackPairMap`). For the identity fibration this
recovers the computation `TauCeti.isIso_singularHomologyMap_characteristicPairMap` of the cellular
chain groups, and the proof follows that one.

Both pairs are first thickened. In the base, `Xⁿ⁻¹` is replaced by its neighbourhood
`TauCeti.skeletonNeighborhood C n` in `Xⁿ`, and the boundary spheres by the shells
`2⁻¹ ≤ ‖y‖ ≤ 1`. The deformations retracting the thickened subspaces back do not lift to `E`, but
they do not have to: a Serre fibration pulls back a pair which deforms into its subspace, relative
to that subspace, to a pair with vanishing relative homology
(`TauCeti.TopCat.isZero_singularHomology_preimage_of_homotopyRel`), so by the long exact sequence
of a triple the thickening does not change relative homology. After thickening, the part of `P`
over the boundary spheres and the part of `E` over `Xⁿ⁻¹` can be excised; what remains on both
sides is the part over the open cells relative to the part over their outer halves, and the
projection identifies these, because the characteristic maps are a homeomorphism from the open
balls onto the open cells (`TauCeti.iUnionOpenCellHomeomorph`).

## Main definitions and results

* `TauCeti.TopCat.cellPullbackPair`: the pair `(P, ∂P)` of the pullback of `p` to the disks of the
  `n`-cells, relative to the part over their boundary spheres.
* `TauCeti.TopCat.preimageSkeletonPair`: the pair `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))`.
* `TauCeti.TopCat.cellPullbackPairMap`: the projection `(P, ∂P) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))`.
* `TauCeti.TopCat.isIso_singularHomologyMap_cellPullbackPairMap`: the projection induces
  isomorphisms on relative singular homology, and
  `TauCeti.TopCat.preimageSkeletonPairSingularHomologyIso` is the resulting isomorphism
  `Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ≅ Hₖ(P, ∂P)`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34 and its proof.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Section 5.1.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex unitInterval

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B}

section Cells

variable [T2Space B] {C D : Set B} [RelCWComplex C D]

variable (p C) in
/-- The total space `P` of the pullback of `p` along `TauCeti.sigmaCellMap C n`: the pairs `(q, e)`
of a point `q` of the disk of an `n`-cell and a point `e` of `E` over its image. Its projection to
the disks is the Serre fibration `TopCat.pullbackFst (TopCat.ofHom (sigmaCellMap C n)) p` when `p`
is one. -/
abbrev cellPullback (n : ℕ) : _root_.TopCat.{u} :=
  _root_.TopCat.of
    {x : (Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1) × E // sigmaCellMap C n x.1 = p x.2}

variable (p C) in
/-- The pair `(P, ∂P)`: the pullback `TauCeti.TopCat.cellPullback p C n` of `p` to the disks of the
`n`-cells, relative to its part over their boundary spheres. -/
abbrev cellPullbackPair (n : ℕ) : TopPair.{u} :=
  TopPair.ofSubset (X := cellPullback p C n) {x | ‖(x.1.1.2 : Fin n → ℝ)‖ = 1}

variable (p C) in
/-- The pair `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` of consecutive stages of the filtration of `E` by the
preimages of the skeleta `Xⁿ = skeletonLT C (n + 1)`. -/
abbrev preimageSkeletonPair (n : ℕ) : TopPair.{u} :=
  TopPair.ofInclusion (X := E) (preimage_mono (f := p) (skeletonLT_subset_skeletonLT_succ C n))

/-- A point of the pullback lies over the `n`-skeleton. -/
lemma cellPullback_mem_preimage_skeletonLT {n : ℕ} (x : cellPullback p C n) :
    x.1.2 ∈ p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) := by
  rw [mem_preimage, ← x.2, sigmaCellMap_apply]
  exact map_mem_skeletonLT_succ _ (mem_closedBall_zero_iff.1 x.1.1.2.2)

/-- A point of the pullback over a boundary sphere lies over the `(n - 1)`-skeleton. -/
lemma cellPullback_mem_preimage_skeletonLT_of_norm_eq_one {n : ℕ} {x : cellPullback p C n}
    (hx : ‖(x.1.1.2 : Fin n → ℝ)‖ = 1) : x.1.2 ∈ p ⁻¹' (skeletonLT C n : Set B) := by
  rw [mem_preimage, ← x.2, sigmaCellMap_apply]
  exact cellFrontier_subset_skeletonLT n _ ⟨_, mem_sphere_zero_iff_norm.2 hx, rfl⟩

variable (p C) in
/-- **The projection to `E`** `(q, e) ↦ e` from the pullback `P` of `p` to the disks of the
`n`-cells, as a map of pairs `(P, ∂P) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))`. -/
def cellPullbackPairMap (n : ℕ) : cellPullbackPair p C n ⟶ preimageSkeletonPair p C n :=
  TopPair.ofHom (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.1.2, cellPullback_mem_preimage_skeletonLT x⟩,
      by fun_prop⟩)
    (_root_.TopCat.ofHom
      ⟨fun x ↦ ⟨x.1.1.2, cellPullback_mem_preimage_skeletonLT_of_norm_eq_one x.2⟩, by fun_prop⟩)
    rfl

@[simp]
lemma coe_cellPullbackPairMap_fst_apply (n : ℕ) (x : cellPullback p C n) :
    (ConcreteCategory.hom (Y := _root_.TopCat.of
      (p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)))
      (TopPair.Hom.fst (cellPullbackPairMap p C n)) x).1 = x.1.2 :=
  (rfl)

@[simp]
lemma coe_cellPullbackPairMap_snd_apply (n : ℕ) (x : (cellPullbackPair p C n).snd) :
    (ConcreteCategory.hom (Y := _root_.TopCat.of (p ⁻¹' (skeletonLT C n : Set B)))
      (TopPair.Hom.snd (cellPullbackPairMap p C n)) x).1 = x.1.1.2 :=
  (rfl)

/-! ### Thickening the subspaces -/

variable (p C) in
/-- The pullback relative to its part over the shells `2⁻¹ ≤ ‖y‖ ≤ 1`. -/
private abbrev cellPullbackShellPair (n : ℕ) : TopPair.{u} :=
  TopPair.ofSubset (X := cellPullback p C n) {x | 2⁻¹ ≤ ‖(x.1.1.2 : Fin n → ℝ)‖}

variable (p C) in
/-- The pair `(p⁻¹(Xⁿ), p⁻¹(N))` for the neighbourhood `N = TauCeti.skeletonNeighborhood C n` of
`Xⁿ⁻¹` in `Xⁿ`. -/
private abbrev preimageNeighborhoodPair (n : ℕ) : TopPair.{u} :=
  TopPair.ofInclusion (X := E)
    (preimage_mono (f := p) (skeletonNeighborhood_subset_skeletonLT_succ C n))

variable (C) in
/-- The radial deformation of the shells of the disks onto the boundary spheres, relative to the
spheres. -/
private def shellHomotopyRel (n : ℕ) :
    (ContinuousMap.id {q : Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1 |
      2⁻¹ ≤ ‖(q.2 : Fin n → ℝ)‖}).HomotopyRel
      ⟨fun q ↦ ⟨sigmaRadialHomotopy (cell C n) n (1, q.1),
        sigma_sphere_subset_shell _ n (norm_sigmaRadialHomotopy_one _ n q.2)⟩, by fun_prop⟩
      (Subtype.val ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1}) where
  toFun z := ⟨sigmaRadialHomotopy (cell C n) n (z.1, z.2.1),
    z.2.2.trans (norm_le_norm_sigmaRadialHomotopy _ n z.1 z.2.1)⟩
  continuous_toFun := by fun_prop
  map_zero_left q := Subtype.ext ((sigmaRadialHomotopy (cell C n) n).apply_zero q.1)
  map_one_left q := rfl
  prop' t q hq := Subtype.ext (sigmaRadialHomotopy_apply_of_norm_eq_one _ _ t hq)

variable (C) in
/-- The deformation of `N = TauCeti.skeletonNeighborhood C n` onto `Xⁿ⁻¹`, relative to `Xⁿ⁻¹`. -/
private def neighborhoodHomotopyRel (n : ℕ) :
    (ContinuousMap.id (skeletonNeighborhood C n)).HomotopyRel
      ⟨fun x ↦ ⟨skeletonNeighborhoodEndpoint C n ⟨x, skeletonNeighborhood_subset_skeletonLT_succ C n
          x.2⟩, skeletonLT_subset_skeletonNeighborhood n (skeletonNeighborhoodEndpoint_mem _ x.2)⟩,
        by fun_prop⟩
      (Subtype.val ⁻¹' (skeletonLT C n : Set B)) where
  toFun z := ⟨skeletonNeighborhoodHomotopy C n
      (z.1, ⟨z.2, skeletonNeighborhood_subset_skeletonLT_succ C n z.2.2⟩),
    skeletonNeighborhoodHomotopy_mem _ _ z.2.2⟩
  continuous_toFun := by fun_prop
  map_zero_left x := Subtype.ext <| by
    -- Read the deformation of `Xⁿ` on the points of `N`, as points of `B`.
    change (skeletonNeighborhoodHomotopy C n (0, _) : B) = x
    rw [ContinuousMap.Homotopy.apply_zero]
    rfl
  map_one_left x := Subtype.ext <| by
    -- As above, read the deformation on the points of `N`.
    change (skeletonNeighborhoodHomotopy C n (1, _) : B) = skeletonNeighborhoodEndpoint C n _
    rw [ContinuousMap.Homotopy.apply_one]
  prop' t x hx := Subtype.ext <| by
    -- As above, read the deformation on the points of `N`.
    change (skeletonNeighborhoodHomotopy C n (t, _) : B) = x
    rw [skeletonNeighborhoodHomotopy_apply_of_mem t
      ⟨x.1, skeletonNeighborhood_subset_skeletonLT_succ C n x.2⟩ (by exact hx)]

variable (p C) in
omit [T2Space B] in
private lemma cellPullbackSphere_subset_shell (n : ℕ) :
    {x : cellPullback p C n | ‖(x.1.1.2 : Fin n → ℝ)‖ = 1} ⊆
      {x | 2⁻¹ ≤ ‖(x.1.1.2 : Fin n → ℝ)‖} :=
  fun _ hx ↦ sigma_sphere_subset_shell _ n hx

variable (p C) in
/-- The inclusion `(P, ∂P) ⟶ (P, P over the shells)`. -/
private def cellPullbackPairToShellPair (n : ℕ) :
    cellPullbackPair p C n ⟶ cellPullbackShellPair p C n :=
  TopPair.ofSubsetMap (𝟙 _) fun _ hx ↦ cellPullbackSphere_subset_shell p C n hx

variable (p C) in
/-- The inclusion `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(N))`. -/
private def preimageSkeletonPairToNeighborhood (n : ℕ) :
    preimageSkeletonPair p C n ⟶ preimageNeighborhoodPair p C n :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.id _) fun _ hx ↦
    preimage_mono (f := p) (skeletonLT_subset_skeletonNeighborhood n) hx

variable (hp : serreFibrations p) (R : Type u) [Ring R]

variable (p C) in
/-- The projection `(q, e) ↦ e`, as a map of pairs `(P, P over the shells) ⟶ (p⁻¹(Xⁿ), p⁻¹(N))`. -/
private def cellPullbackShellPairMap (n : ℕ) :
    cellPullbackShellPair p C n ⟶ preimageNeighborhoodPair p C n :=
  TopPair.ofHom (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.1.2, cellPullback_mem_preimage_skeletonLT x⟩,
      by fun_prop⟩)
    (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.1.1.2, by
      rw [mem_preimage, ← x.1.2, sigmaCellMap_apply,
        map_mem_skeletonNeighborhood_iff _ (mem_closedBall_zero_iff.1 x.1.1.1.2.2)]
      exact x.2⟩, by fun_prop⟩)
    rfl

variable (p C) in
/-- The part of the pullback over the open balls, relative to its part over the open shells
`2⁻¹ ≤ ‖y‖ < 1`. -/
private abbrev cellPullbackOpenShellPair (n : ℕ) : TopPair.{u} :=
  TopPair.ofSubset (X := _root_.TopCat.of {x : cellPullback p C n // ‖(x.1.1.2 : Fin n → ℝ)‖ < 1})
    {x | 2⁻¹ ≤ ‖(x.1.1.1.2 : Fin n → ℝ)‖}

variable (p C) in
/-- The inclusion of the part over the open balls into the pullback, as a map of pairs. -/
private def cellPullbackOpenShellPairToShellPair (n : ℕ) :
    cellPullbackOpenShellPair p C n ⟶ cellPullbackShellPair p C n :=
  TopPair.ofHom (_root_.TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.1.1, x.2⟩, by fun_prop⟩) rfl

omit [T2Space B] in
private lemma continuous_norm_cellPullback (n : ℕ) :
    Continuous fun x : cellPullback p C n ↦ ‖(x.1.1.2 : Fin n → ℝ)‖ := by
  have h : Continuous fun q : Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1 ↦ ‖(q.2 : Fin n → ℝ)‖ :=
    continuous_sigma fun _ ↦ continuous_norm.comp continuous_subtype_val
  exact h.comp (continuous_fst.comp continuous_subtype_val)

variable (p C) in
omit [T2Space B] in
/-- **Excision of the part over the boundary spheres** from `(P, P over the shells)`. -/
private lemma isIso_singularHomologyMap_cellPullbackOpenShellPairToShellPair (n k : ℕ) :
    IsIso ((cellPullbackOpenShellPair p C n).singularHomologyMap
      (cellPullbackOpenShellPairToShellPair p C n) (ModuleCat.of R R) k) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover _ _ IsEmbedding.subtypeVal ?_
    (fun b : Bool ↦ bif b
      then {x : cellPullback p C n | ‖(x.1.1.2 : Fin n → ℝ)‖ < 1}
      else {x : cellPullback p C n | 2⁻¹ < ‖(x.1.1.2 : Fin n → ℝ)‖})
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · intro x hx
    rw [TopPair.range_ofSubset_map] at hx ⊢
    exact hx
  · cases b
    · exact isOpen_lt continuous_const (continuous_norm_cellPullback n)
    · exact isOpen_lt (continuous_norm_cellPullback n) continuous_const
  · refine eq_univ_of_forall fun (x : cellPullback p C n) ↦ mem_iUnion.2 ?_
    rcases lt_or_ge ‖(x.1.1.2 : Fin n → ℝ)‖ 1 with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, show 2⁻¹ < ‖(x.1.1.2 : Fin n → ℝ)‖ by linarith⟩
  · cases b
    · exact Or.inl fun (x : cellPullback p C n) (hx : 2⁻¹ < ‖(x.1.1.2 : Fin n → ℝ)‖) ↦
        ⟨⟨x, hx.le⟩, rfl⟩
    · exact Or.inr fun (x : cellPullback p C n) (hx : ‖(x.1.1.2 : Fin n → ℝ)‖ < 1) ↦ ⟨⟨x, hx⟩, rfl⟩

omit [T2Space B] in
/-- A point of the pullback over an open ball lies over an open `n`-cell. -/
private lemma cellPullback_mem_preimage_iUnion_openCell {n : ℕ}
    (x : {x : cellPullback p C n // ‖(x.1.1.2 : Fin n → ℝ)‖ < 1}) :
    x.1.1.2 ∈ p ⁻¹' ⋃ j : cell C n, openCell (C := C) n j := by
  rw [mem_preimage, ← x.1.2, sigmaCellMap_apply]
  exact mem_iUnion.2 ⟨x.1.1.1.1, x.1.1.1.2, mem_ball_zero_iff.2 x.2, rfl⟩

/-- Through `TauCeti.iUnionOpenCellHomeomorph`, a point of `E` over an open `n`-cell lies over the
image of a point of the open balls. -/
private lemma sigmaCellMap_iUnionOpenCellHomeomorph_symm {n : ℕ}
    (e : (p ⁻¹' ⋃ j : cell C n, openCell (C := C) n j : Set E)) :
    sigmaCellMap C n (Sigma.map id (fun _ ↦ inclusion ball_subset_closedBall)
      ((iUnionOpenCellHomeomorph (C := C) n).symm ⟨p e.1, e.2⟩)) = p e.1 := by
  have := congrArg Subtype.val ((iUnionOpenCellHomeomorph (C := C) n).apply_symm_apply ⟨p e.1, e.2⟩)
  rw [sigmaCellMap_apply]
  rwa [iUnionOpenCellHomeomorph_apply] at this

variable (p C) in
/-- The projection `(q, e) ↦ e` is a homeomorphism from the part of the pullback over the open balls
onto the part of `E` over the open `n`-cells, with inverse read through
`TauCeti.iUnionOpenCellHomeomorph`. -/
private def cellPullbackOpenHomeomorph (n : ℕ) :
    {x : cellPullback p C n // ‖(x.1.1.2 : Fin n → ℝ)‖ < 1} ≃ₜ
      (p ⁻¹' ⋃ j : cell C n, openCell (C := C) n j : Set E) where
  toFun x := ⟨x.1.1.2, cellPullback_mem_preimage_iUnion_openCell x⟩
  invFun e := ⟨⟨(Sigma.map id (fun _ ↦ inclusion ball_subset_closedBall)
      ((iUnionOpenCellHomeomorph (C := C) n).symm ⟨p e.1, e.2⟩), e.1),
    sigmaCellMap_iUnionOpenCellHomeomorph_symm e⟩,
    mem_ball_zero_iff.1 ((iUnionOpenCellHomeomorph (C := C) n).symm ⟨p e.1, e.2⟩).2.2⟩
  left_inv := by
    rintro ⟨⟨⟨⟨j, y⟩, e⟩, hye⟩, hy⟩
    have hs (h) : (iUnionOpenCellHomeomorph (C := C) n).symm ⟨p e, h⟩ =
        ⟨j, y, mem_ball_zero_iff.2 hy⟩ := by
      rw [Homeomorph.symm_apply_eq]
      rw [sigmaCellMap_apply] at hye
      exact Subtype.ext (by rw [iUnionOpenCellHomeomorph_apply]; exact hye.symm)
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
    dsimp only
    rw [hs]
    rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_snd.comp (continuous_subtype_val.comp
    continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    have hs : Continuous fun e : (p ⁻¹' ⋃ j : cell C n, openCell (C := C) n j : Set E) ↦
        (iUnionOpenCellHomeomorph (C := C) n).symm ⟨p e.1, e.2⟩ :=
      (iUnionOpenCellHomeomorph (C := C) n).symm.continuous.comp
        ((p.hom.continuous.comp continuous_subtype_val).subtype_mk _)
    refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk ?_
      continuous_subtype_val) _) _
    exact (continuous_sigma_map.2 fun _ ↦ continuous_inclusion ball_subset_closedBall).comp hs

private lemma coe_cellPullbackOpenHomeomorph_apply (n : ℕ)
    (x : {x : cellPullback p C n // ‖(x.1.1.2 : Fin n → ℝ)‖ < 1}) :
    (cellPullbackOpenHomeomorph p C n x : E) = x.1.1.2 :=
  (rfl)

private lemma coe_cellPullbackOpenShellPairMap_fst_apply (n : ℕ)
    (x : {x : cellPullback p C n // ‖(x.1.1.2 : Fin n → ℝ)‖ < 1}) :
    (ConcreteCategory.hom (Y := _root_.TopCat.of
      (p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)))
      (TopPair.Hom.fst (cellPullbackOpenShellPairToShellPair p C n ≫
        cellPullbackShellPairMap p C n)) x).1 = x.1.1.2 :=
  (rfl)

variable (p C) in
/-- On the part of the pullback over the open balls, the projection to `E` is an embedding, through
`cellPullbackOpenHomeomorph`. -/
private lemma isEmbedding_cellPullbackOpenShellPairMap (n : ℕ) :
    IsEmbedding (TopPair.Hom.fst
      (cellPullbackOpenShellPairToShellPair p C n ≫ cellPullbackShellPairMap p C n)) := by
  refine (IsEmbedding.of_comp_iff (IsEmbedding.subtypeVal
    (p := (· ∈ p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B))))).1 ?_
  have h : Subtype.val ∘ ⇑(ConcreteCategory.hom (TopPair.Hom.fst
      (cellPullbackOpenShellPairToShellPair p C n ≫ cellPullbackShellPairMap p C n))) =
      Subtype.val ∘ cellPullbackOpenHomeomorph p C n :=
    funext fun x ↦ (coe_cellPullbackOpenShellPairMap_fst_apply n x).trans
      (coe_cellPullbackOpenHomeomorph_apply n x).symm
  rw [h]
  exact IsEmbedding.subtypeVal.comp (cellPullbackOpenHomeomorph p C n).isEmbedding

variable (p C) in
/-- **Excision of the part over `Xⁿ⁻¹`** from `(p⁻¹(Xⁿ), p⁻¹(N))`, read through the projection of
the part of the pullback over the open balls. -/
private lemma isIso_singularHomologyMap_cellPullbackOpenShellPairMap (n k : ℕ) :
    IsIso ((cellPullbackOpenShellPair p C n).singularHomologyMap
      (cellPullbackOpenShellPairToShellPair p C n ≫ cellPullbackShellPairMap p C n)
      (ModuleCat.of R R) k) := by
  have hpc : Continuous fun x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) ↦ p x.1 :=
    p.hom.continuous.comp continuous_subtype_val
  refine TopPair.isIso_singularHomologyMap_of_open_cover _ _
    (isEmbedding_cellPullbackOpenShellPairMap p C n) ?_
    (fun b : Bool ↦ bif b
      then {x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) |
        p x.1 ∉ (skeletonLT C n : Set B)}
      else {x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) |
        p x.1 ∉ ⋃ j : cell C n, map n j '' closedBall 0 2⁻¹})
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · -- A point over `N` lies outside the inner halves of the cells.
    rintro ⟨⟨⟨⟨j, y⟩, e⟩, hye⟩, hy⟩ ⟨a, ha⟩
    have he : p e ∈ skeletonNeighborhood C n := by
      obtain ⟨a, ha'⟩ := a
      have : a = e := congrArg Subtype.val ha
      exact this ▸ ha'
    rw [← hye, sigmaCellMap_apply,
      map_mem_skeletonNeighborhood_iff _ (mem_closedBall_zero_iff.1 y.2)] at he
    rw [TopPair.range_ofSubset_map]
    exact he
  · cases b
    · exact ((isClosed_iUnion_map_closedBall (C := C) n (r := 2⁻¹) (by norm_num)).preimage
        hpc).isOpen_compl
    · exact ((skeletonLT C n).closed.preimage hpc).isOpen_compl
  · refine eq_univ_of_forall fun (x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)) ↦
      mem_iUnion.2 ?_
    by_cases hx : p x.1 ∈ (skeletonLT C n : Set B)
    · -- The inner halves of the cells do not meet `Xⁿ⁻¹`.
      refine ⟨false, fun h ↦ ?_⟩
      obtain ⟨j, z, hz, hzx⟩ := mem_iUnion.1 h
      exact map_notMem_skeletonLT j ((mem_closedBall_zero_iff.1 hz).trans_lt (by norm_num))
        (hzx ▸ hx)
    · exact ⟨true, hx⟩
  · cases b
    · -- Outside the inner halves of the cells, `Xⁿ` is `N`.
      refine Or.inl fun (x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)) hx ↦
        ⟨⟨x.1, mem_skeletonNeighborhood.2 ⟨x.2, fun j z hz h ↦ hx ?_⟩⟩, rfl⟩
      exact mem_iUnion.2 ⟨j, z, mem_closedBall_zero_iff.2 hz.le, h⟩
    · -- A point of `Xⁿ` outside `Xⁿ⁻¹` lies in an open `n`-cell.
      refine Or.inr fun (x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)) hx ↦ ?_
      obtain hx' | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.2
      · exact (hx hx').elim
      · exact ⟨⟨⟨⟨⟨j, y, mem_closedBall_zero_iff.2 hy.le⟩, x.1⟩,
          (sigmaCellMap_apply C n _).trans hxy⟩, hy⟩, rfl⟩

include hp

omit [T2Space B] in
private lemma isIso_singularHomologyMap_cellPullbackPairToShellPair (n k : ℕ) :
    IsIso ((cellPullbackPair p C n).singularHomologyMap (cellPullbackPairToShellPair p C n)
      (ModuleCat.of R R) k) := by
  -- The part of the pullback over the shells, relative to the part over the spheres, is acyclic.
  have hz (m : ℕ) := isZero_singularHomology_preimage_of_homotopyRel
    (mem_serreFibrations_pullbackFst hp (_root_.TopCat.ofHom (sigmaCellMap C n)))
    (sigma_sphere_subset_shell _ n) (shellHomotopyRel C n)
    (fun q ↦ norm_sigmaRadialHomotopy_one _ n q.2) R m
  have := TopTriple.isIso_singularHomologyMap_totalToOuter_of_isZero
    (TopTriple.ofSubset (X := cellPullback p C n) (cellPullbackSphere_subset_shell p C n)) _ k
    (hz k) fun m _ ↦ hz m
  rwa [TopTriple.totalToOuter_app_ofSubset] at this

private lemma isIso_singularHomologyMap_preimageSkeletonPairToNeighborhood (n k : ℕ) :
    IsIso ((preimageSkeletonPair p C n).singularHomologyMap
      (preimageSkeletonPairToNeighborhood p C n) (ModuleCat.of R R) k) := by
  -- The part of `E` over `N`, relative to the part over `Xⁿ⁻¹`, is acyclic.
  have hz (m : ℕ) := isZero_singularHomology_preimage_of_homotopyRel hp
    (skeletonLT_subset_skeletonNeighborhood (C := C) n) (neighborhoodHomotopyRel C n)
    (fun x ↦ skeletonNeighborhoodEndpoint_mem _ x.2) R m
  have := TopTriple.isIso_singularHomologyMap_totalToOuter_of_isZero
    (TopTriple.ofInclusions (X := E)
      (preimage_mono (f := p) (skeletonLT_subset_skeletonNeighborhood (C := C) n))
      (preimage_mono (f := p) (skeletonNeighborhood_subset_skeletonLT_succ C n))) _ k (hz k)
    fun m _ ↦ hz m
  rwa [TopTriple.totalToOuter_app_ofInclusions] at this

variable (C) in
/-- **The skeletal filtration of a Serre fibration over the cells.** For a Serre fibration
`p : E ⟶ B` and a relative CW complex `C ⊆ B` with skeleta `Xⁿ`, the projection
`(P, ∂P) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the pullback of `p` to the disks of the `n`-cells, relative to
its part over their boundary spheres, induces isomorphisms on relative singular homology in every
degree `k`. -/
theorem isIso_singularHomologyMap_cellPullbackPairMap (n k : ℕ) :
    IsIso ((cellPullbackPair p C n).singularHomologyMap (cellPullbackPairMap p C n)
      (ModuleCat.of R R) k) := by
  -- Thicken the subspaces on both sides: the square of pairs commutes, both thickenings are
  -- isomorphisms on homology, and so is the thickened projection, by excision on both sides.
  have hsq : cellPullbackPairMap p C n ≫ preimageSkeletonPairToNeighborhood p C n =
      cellPullbackPairToShellPair p C n ≫ cellPullbackShellPairMap p C n :=
    TopPair.hom_ext_of_fst _ <| by
      ext x
      exact (TopPair.ofInclusionMap_fst_apply _ _ _).trans (congrArg
        (TopPair.Hom.fst (cellPullbackShellPairMap p C n)) (TopPair.ofSubsetMap_fst_apply
          (𝟙 (cellPullback p C n)) (fun _ hx ↦ cellPullbackSphere_subset_shell p C n hx) x)).symm
  have := isIso_singularHomologyMap_cellPullbackOpenShellPairMap p C R n k
  rw [TopPair.singularHomologyMap_comp] at this
  have := isIso_singularHomologyMap_cellPullbackOpenShellPairToShellPair p C R n k
  have := IsIso.of_isIso_comp_left
    ((cellPullbackOpenShellPair p C n).singularHomologyMap
      (cellPullbackOpenShellPairToShellPair p C n) (ModuleCat.of R R) k)
    ((cellPullbackShellPair p C n).singularHomologyMap (cellPullbackShellPairMap p C n)
      (ModuleCat.of R R) k)
  have := isIso_singularHomologyMap_cellPullbackPairToShellPair (C := C) hp R n k
  have := isIso_singularHomologyMap_preimageSkeletonPairToNeighborhood (C := C) hp R n k
  have hcomp : IsIso ((cellPullbackPair p C n).singularHomologyMap
      (cellPullbackPairMap p C n ≫ preimageSkeletonPairToNeighborhood p C n)
      (ModuleCat.of R R) k) := by
    rw [hsq, TopPair.singularHomologyMap_comp]
    infer_instance
  rw [TopPair.singularHomologyMap_comp] at hcomp
  exact IsIso.of_isIso_comp_right _
    ((preimageSkeletonPair p C n).singularHomologyMap (preimageSkeletonPairToNeighborhood p C n)
      (ModuleCat.of R R) k)

variable (C) in
/-- The relative homology `Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` of consecutive stages of the skeletal filtration
of a Serre fibration is the relative homology of the pullback `(P, ∂P)` of `p` to the disks of the
`n`-cells; the inverse is induced by the projection `TauCeti.TopCat.cellPullbackPairMap`. -/
def preimageSkeletonPairSingularHomologyIso (n k : ℕ) :
    (preimageSkeletonPair p C n).singularHomology (ModuleCat.of R R) k ≅
      (cellPullbackPair p C n).singularHomology (ModuleCat.of R R) k :=
  have := isIso_singularHomologyMap_cellPullbackPairMap C hp R n k
  (asIso ((cellPullbackPair p C n).singularHomologyMap (cellPullbackPairMap p C n)
    (ModuleCat.of R R) k)).symm

@[simp]
lemma preimageSkeletonPairSingularHomologyIso_inv (n k : ℕ) :
    (preimageSkeletonPairSingularHomologyIso C hp R n k).inv =
      (cellPullbackPair p C n).singularHomologyMap (cellPullbackPairMap p C n)
        (ModuleCat.of R R) k :=
  (rfl)

end Cells

end TopCat

end TauCeti
