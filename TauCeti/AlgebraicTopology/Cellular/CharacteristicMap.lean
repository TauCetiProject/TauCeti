/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.SkeletonNeighborhood
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.Analysis.Normed.Module.Ball.RadialPush
public import TauCeti.Topology.CWComplex.Classical.OpenCells

/-!
# The characteristic maps of the `n`-cells induce isomorphisms on relative homology

For a relative CW complex, the characteristic maps of the `n`-cells assemble into a map of pairs
`TauCeti.characteristicPairMap C n : ∐ⱼ (Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)` from the disjoint union, over
the `n`-cells `j`, of copies of the closed unit ball of `Fin n → ℝ` relative to their boundary
spheres (`TauCeti.sigmaDiskPair`) to the skeletal pair.  This map induces isomorphisms on relative
singular homology in every degree; in degree `n` it identifies the cellular chain group
`Hₙ(Xⁿ, Xⁿ⁻¹)` with the relative homology of the disjoint union of the disk pairs, through maps
of pairs rather than abstract isomorphisms.

The proof compares both pairs with their versions in which the subspace has been thickened.
On the side of the complex, `TauCeti.isIso_singularHomologyMap_skeletonPairToNeighborhood`
replaces `Xⁿ⁻¹` by its neighbourhood `TauCeti.skeletonNeighborhood C n`, obtained by removing the
inner half of every open `n`-cell.  On the side of the disks, the radial deformation
`TauCeti.radialPush 2⁻¹` replaces the boundary spheres by the shells `2⁻¹ ≤ ‖y‖ ≤ 1`.  The
characteristic maps carry the thickened disk pairs to the thickened skeletal pair, and both
thickened pairs contain the disjoint union of the open balls relative to their open shells: in the
disks this is excision of the boundary spheres, and in the complex, where the open balls map
homeomorphically onto the open `n`-cells (`TauCeti.iUnionOpenCellHomeomorph`), it is excision of
`Xⁿ⁻¹`.

## Main definitions and results

* `TauCeti.sigmaDiskPair ι n`: the pair `∐ᵢ (Dⁿ, Sⁿ⁻¹)`.
* `TauCeti.characteristicPairMap C n`: the characteristic maps of the `n`-cells, as a map of pairs
  `∐ⱼ (Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)`.
* `TauCeti.isIso_singularHomologyMap_characteristicPairMap`: it induces isomorphisms on relative
  singular homology in every degree.
* `TauCeti.cellularChainGroupIsoSigmaDiskPair`: the resulting isomorphism from the cellular chain
  group `Hₙ(Xⁿ, Xⁿ⁻¹)` to the relative homology of `∐ⱼ (Dⁿ, Sⁿ⁻¹)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34 and its proof, and Proposition 2.22 for the comparison through good
  pairs.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex unitInterval

universe w v u

namespace TauCeti

section DiskPair

variable (ι : Type w) (n : ℕ)

/-- The pair `∐ᵢ (Dⁿ, Sⁿ⁻¹)`: the disjoint union, over `i : ι`, of copies of the closed unit
ball of `Fin n → ℝ`, relative to the disjoint union of their boundary spheres.  The closed unit
ball is the domain of the characteristic maps of the `n`-cells of a CW complex. -/
abbrev sigmaDiskPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (Σ _ : ι, closedBall (0 : Fin n → ℝ) 1))
    {p | ‖(p.2 : Fin n → ℝ)‖ = 1}

/-- The disks of `TauCeti.sigmaDiskPair` relative to the shells `2⁻¹ ≤ ‖y‖ ≤ 1`. -/
private abbrev sigmaShellPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (Σ _ : ι, closedBall (0 : Fin n → ℝ) 1))
    {p | 2⁻¹ ≤ ‖(p.2 : Fin n → ℝ)‖}

/-- The open balls inside the disks of `TauCeti.sigmaDiskPair`, relative to the open shells
`2⁻¹ ≤ ‖y‖ < 1`. -/
private abbrev sigmaOpenShellPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (Σ _ : ι, ball (0 : Fin n → ℝ) 1))
    {p | 2⁻¹ ≤ ‖(p.2 : Fin n → ℝ)‖}

private lemma continuous_norm_sigma_snd :
    Continuous fun p : Σ _ : ι, closedBall (0 : Fin n → ℝ) 1 ↦ ‖(p.2 : Fin n → ℝ)‖ :=
  continuous_sigma fun _ ↦ continuous_norm.comp continuous_subtype_val

private lemma radialPush_mem_closedBall (t : I) (y : closedBall (0 : Fin n → ℝ) 1) :
    radialPush 2⁻¹ t (y : Fin n → ℝ) ∈ closedBall (0 : Fin n → ℝ) 1 :=
  mem_closedBall_zero_iff.2 <|
    norm_radialPush_le_one (by norm_num) (by norm_num) t (mem_closedBall_zero_iff.1 y.2)

/-- The radial deformation `TauCeti.radialPush 2⁻¹`, applied in every disk. -/
private def sigmaRadialPush :
    C(I × (Σ _ : ι, closedBall (0 : Fin n → ℝ) 1), Σ _ : ι, closedBall (0 : Fin n → ℝ) 1) where
  toFun q := ⟨q.2.1, radialPush 2⁻¹ q.1 q.2.2, radialPush_mem_closedBall n q.1 q.2.2⟩
  continuous_toFun := by
    -- Move the time coordinate into the summands, where the deformation is continuous.
    refine (continuous_sigma_map (f₁ := id) (τ := fun _ : ι ↦ closedBall (0 : Fin n → ℝ) 1)
      (f₂ := fun _ (q : closedBall (0 : Fin n → ℝ) 1 × I) ↦
      (⟨radialPush 2⁻¹ q.2 q.1, radialPush_mem_closedBall n q.2 q.1⟩ :
        closedBall (0 : Fin n → ℝ) 1)) |>.2 fun _ ↦ ?_).comp
      ((Homeomorph.sigmaProdDistrib (ι := ι) (X := fun _ ↦ closedBall (0 : Fin n → ℝ) 1)
        (Y := I)).continuous.comp continuous_swap)
    exact Continuous.subtype_mk ((continuous_radialPush (by norm_num)).comp
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))) _

/-- The radial deformation of the disks, from the identity to the map pushing the shells onto the
boundary spheres. -/
private def sigmaRadialHomotopy :
    (ContinuousMap.id _).Homotopy ((sigmaRadialPush ι n).curry 1) where
  toContinuousMap := sigmaRadialPush ι n
  map_zero_left _ := Sigma.ext rfl (heq_of_eq (Subtype.ext (radialPush_zero _ _)))
  map_one_left _ := rfl

private lemma coe_sigmaRadialHomotopy_apply (t : I) (p : Σ _ : ι, closedBall (0 : Fin n → ℝ) 1) :
    ((sigmaRadialHomotopy ι n (t, p)).2 : Fin n → ℝ) = radialPush 2⁻¹ t (p.2 : Fin n → ℝ) :=
  (rfl)

private lemma mapsTo_sphere_shell :
    MapsTo (𝟙 (TopCat.of (Σ _ : ι, closedBall (0 : Fin n → ℝ) 1)))
      {p | ‖(p.2 : Fin n → ℝ)‖ = 1} {p | 2⁻¹ ≤ ‖(p.2 : Fin n → ℝ)‖} := by
  intro p (hp : ‖(p.2 : Fin n → ℝ)‖ = 1)
  change 2⁻¹ ≤ ‖(p.2 : Fin n → ℝ)‖  -- the identity of `TopCat` applied to `p` is `p`
  rw [hp]
  norm_num

private lemma mapsTo_shell_sphere :
    MapsTo (TopCat.ofHom (X := TopCat.of (Σ _ : ι, closedBall (0 : Fin n → ℝ) 1))
      (Y := TopCat.of (Σ _ : ι, closedBall (0 : Fin n → ℝ) 1)) ((sigmaRadialPush ι n).curry 1))
      {p | 2⁻¹ ≤ ‖(p.2 : Fin n → ℝ)‖} {p | ‖(p.2 : Fin n → ℝ)‖ = 1} :=
  fun _ hp ↦ norm_radialPush_one (by norm_num) hp

/-- The inclusion of pairs `∐ᵢ (Dⁿ, Sⁿ⁻¹) ⟶ ∐ᵢ (Dⁿ, shell)`. -/
private def sigmaDiskPairToShellPair : sigmaDiskPair ι n ⟶ sigmaShellPair ι n :=
  TopPair.ofSubsetMap _ (mapsTo_sphere_shell ι n)

/-- The end of the radial deformation, as a map of pairs `∐ᵢ (Dⁿ, shell) ⟶ ∐ᵢ (Dⁿ, Sⁿ⁻¹)`. -/
private def sigmaShellPairToDiskPair : sigmaShellPair ι n ⟶ sigmaDiskPair ι n :=
  TopPair.ofSubsetMap _ (mapsTo_shell_sphere ι n)

private lemma isIso_singularHomologyMap_sigmaDiskPairToShellPair
    {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Preadditive A]
    [CategoryWithHomology A] (R : A) (k : ℕ) :
    IsIso ((sigmaDiskPair ι n).singularHomologyMap (sigmaDiskPairToShellPair ι n) R k) := by
  -- Both composites are the end of the radial deformation, which is homotopic to the identity
  -- through `sigmaRadialHomotopy`.
  have h₁ : MapsTo (𝟙 _ ≫ TopCat.ofHom ((sigmaRadialPush ι n).curry 1))
      {p : Σ _ : ι, closedBall (0 : Fin n → ℝ) 1 | ‖(p.2 : Fin n → ℝ)‖ = 1}
      {p | ‖(p.2 : Fin n → ℝ)‖ = 1} :=
    fun _ hp ↦ mapsTo_shell_sphere ι n (mapsTo_sphere_shell ι n hp)
  have h₂ : MapsTo (TopCat.ofHom ((sigmaRadialPush ι n).curry 1) ≫ 𝟙 _)
      {p : Σ _ : ι, closedBall (0 : Fin n → ℝ) 1 | 2⁻¹ ≤ ‖(p.2 : Fin n → ℝ)‖}
      {p | 2⁻¹ ≤ ‖(p.2 : Fin n → ℝ)‖} :=
    fun _ hp ↦ mapsTo_sphere_shell ι n (mapsTo_shell_sphere ι n hp)
  refine TopPair.isIso_singularHomologyMap _ (sigmaShellPairToDiskPair ι n) ?_ ?_ R k
  · -- The deformation fixes the boundary spheres.
    rw [sigmaDiskPairToShellPair, sigmaShellPairToDiskPair, ← TopPair.ofSubsetMap_comp _ _ _ _ h₁,
      ← TopPair.ofSubsetMap_id (fun _ hx ↦ hx)]
    refine TopPair.ofSubsetHomotopy (sigmaRadialHomotopy ι n).symm fun t p hp ↦ ?_
    -- `ofSubsetHomotopy` sees the homotopy through the `TopCat` composite `𝟙 _ ≫ _`, so its
    -- `symm_apply` lemma does not match syntactically; restate the goal on the deformation.
    change ‖((sigmaRadialHomotopy ι n (σ t, p)).2 : Fin n → ℝ)‖ = 1
    rw [coe_sigmaRadialHomotopy_apply, radialPush_of_norm_eq_one (by norm_num) (by norm_num) _ hp]
    exact hp
  · -- The deformation does not decrease norms, so it keeps the shells inside themselves.
    rw [sigmaDiskPairToShellPair, sigmaShellPairToDiskPair, ← TopPair.ofSubsetMap_comp _ _ _ _ h₂,
      ← TopPair.ofSubsetMap_id (fun _ hx ↦ hx)]
    refine TopPair.ofSubsetHomotopy (sigmaRadialHomotopy ι n).symm fun t p hp ↦ ?_
    -- As above, restate the goal on the deformation itself.
    change 2⁻¹ ≤ ‖((sigmaRadialHomotopy ι n (σ t, p)).2 : Fin n → ℝ)‖
    rw [mem_ofPred_eq] at hp
    rw [coe_sigmaRadialHomotopy_apply]
    exact hp.trans <| norm_le_norm_radialPush (by norm_num) (by norm_num) _
      (mem_closedBall_zero_iff.1 p.2.2)

/-- The inclusion of the open balls into the disks, as a map of pairs
`∐ᵢ (open ball, open shell) ⟶ ∐ᵢ (Dⁿ, shell)`. -/
private def sigmaOpenShellPairToShellPair : sigmaOpenShellPair ι n ⟶ sigmaShellPair ι n :=
  TopPair.ofHom (TopCat.ofHom ⟨Sigma.map id fun _ ↦ inclusion ball_subset_closedBall,
      continuous_sigma_map.2 fun _ ↦ continuous_inclusion ball_subset_closedBall⟩)
    (TopCat.ofHom ⟨fun p ↦ ⟨Sigma.map id (fun _ ↦ inclusion ball_subset_closedBall) p.1, p.2⟩,
      (continuous_sigma_map.2 fun _ ↦ continuous_inclusion ball_subset_closedBall).comp
        continuous_subtype_val |>.subtype_mk _⟩)
    rfl

/-- **Excision of the boundary spheres** from `∐ᵢ (Dⁿ, shell)`. -/
private lemma isIso_singularHomologyMap_sigmaOpenShellPairToShellPair
    {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A) (k : ℕ) :
    IsIso ((sigmaOpenShellPair ι n).singularHomologyMap
      (sigmaOpenShellPairToShellPair ι n) R k) := by
  have hemb : IsEmbedding (@Sigma.map ι ι (fun _ ↦ ball (0 : Fin n → ℝ) 1)
      (fun _ ↦ closedBall (0 : Fin n → ℝ) 1) id fun _ ↦ inclusion ball_subset_closedBall) := by
    rw [isEmbedding_sigmaMap Function.injective_id]
    exact fun _ ↦ IsEmbedding.inclusion _
  refine TopPair.isIso_singularHomologyMap_of_open_cover R _ hemb ?_
    (fun b : Bool ↦ bif b
      then {p : Σ _ : ι, closedBall (0 : Fin n → ℝ) 1 | ‖(p.2 : Fin n → ℝ)‖ < 1}
      else {p : Σ _ : ι, closedBall (0 : Fin n → ℝ) 1 | 2⁻¹ < ‖(p.2 : Fin n → ℝ)‖})
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · rintro ⟨i, y⟩ ⟨⟨q, hqS⟩, hq⟩
    have hq' : q = ⟨i, inclusion ball_subset_closedBall y⟩ := hq
    have h : (2 : ℝ)⁻¹ ≤ ‖(y : Fin n → ℝ)‖ := by
      rw [hq'] at hqS
      exact hqS
    exact ⟨⟨⟨i, y⟩, h⟩, rfl⟩
  · cases b
    · exact isOpen_lt continuous_const (continuous_norm_sigma_snd ι n)
    · exact isOpen_lt (continuous_norm_sigma_snd ι n) continuous_const
  · refine eq_univ_of_forall fun (p : Σ _ : ι, closedBall (0 : Fin n → ℝ) 1) ↦ mem_iUnion.2 ?_
    rcases lt_or_ge ‖(p.2 : Fin n → ℝ)‖ 1 with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, show 2⁻¹ < ‖(p.2 : Fin n → ℝ)‖ by linarith⟩
  · cases b
    · exact Or.inl fun p (hp : 2⁻¹ < ‖(p.2 : Fin n → ℝ)‖) ↦ ⟨⟨p, hp.le⟩, rfl⟩
    · exact Or.inr fun p (hp : ‖(p.2 : Fin n → ℝ)‖ < 1) ↦
        ⟨⟨p.1, (p.2 : Fin n → ℝ), mem_ball_zero_iff.2 hp⟩, rfl⟩

end DiskPair

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

/-- The characteristic maps of the `n`-cells of a relative CW complex, assembled into a map from
the disjoint union of their closed unit balls to the `n`-skeleton `Xⁿ = skeletonLT C (n + 1)`. -/
private def sigmaCharacteristicMap (n : ℕ) :
    C(Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1, skeletonLT C ((n + 1 : ℕ) : ℕ∞)) where
  toFun p := ⟨map n p.1 p.2, map_mem_skeletonLT_succ p.1 (mem_closedBall_zero_iff.1 p.2.2)⟩
  continuous_toFun := continuous_sigma fun i ↦
    ((continuousOn n i).domRestrict).subtype_mk _

/-- **The characteristic maps of the `n`-cells, as a map of pairs** `∐ⱼ (Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)`
from `TauCeti.sigmaDiskPair` to the skeletal pair `TauCeti.skeletonPair C n`.  The boundary
sphere of each disk lands in `Xⁿ⁻¹ = skeletonLT C n` because the frontier of an `n`-cell does. -/
def characteristicPairMap (n : ℕ) : sigmaDiskPair (cell C n) n ⟶ skeletonPair C n :=
  TopPair.ofHom (TopCat.ofHom (sigmaCharacteristicMap C n))
    (TopCat.ofHom ⟨fun p ↦ ⟨map n p.1.1 p.1.2, cellFrontier_subset_skeletonLT n p.1.1
      ⟨p.1.2, mem_sphere_zero_iff_norm.2 p.2, rfl⟩⟩,
      (continuous_subtype_val.comp ((sigmaCharacteristicMap C n).continuous.comp
        continuous_subtype_val)).subtype_mk _⟩)
    rfl

@[simp]
lemma characteristicPairMap_fst_apply (n : ℕ)
    (p : Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1) :
    (TopPair.Hom.fst (characteristicPairMap C n) p).1 = map n p.1 p.2 :=
  (rfl)

@[simp]
lemma characteristicPairMap_snd_apply (n : ℕ)
    (p : {p : Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1 // ‖(p.2 : Fin n → ℝ)‖ = 1}) :
    (TopPair.Hom.snd (characteristicPairMap C n) p).1 = map n p.1.1 p.1.2 :=
  (rfl)

/-- The characteristic maps, as a map of pairs from the disks relative to their shells to the
`n`-skeleton relative to `TauCeti.skeletonNeighborhood C n`. -/
private def sigmaShellPairToNeighborhoodPair (n : ℕ) :
    sigmaShellPair (cell C n) n ⟶ skeletonNeighborhoodPair C n :=
  TopPair.ofHom (TopCat.ofHom (sigmaCharacteristicMap C n))
    (TopCat.ofHom ⟨fun p ↦ ⟨map n p.1.1 p.1.2, (map_mem_skeletonNeighborhood_iff p.1.1
      (mem_closedBall_zero_iff.1 p.1.2.2)).2 p.2⟩,
      (continuous_subtype_val.comp ((sigmaCharacteristicMap C n).continuous.comp
        continuous_subtype_val)).subtype_mk _⟩)
    rfl

/-- **Excision of `Xⁿ⁻¹`** from `(Xⁿ, TauCeti.skeletonNeighborhood C n)`, read through the
characteristic maps of the open `n`-cells. -/
private lemma isIso_singularHomologyMap_sigmaOpenShellPairToNeighborhoodPair
    {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A) (n k : ℕ) :
    IsIso ((sigmaOpenShellPair (cell C n) n).singularHomologyMap
      (sigmaOpenShellPairToShellPair (cell C n) n ≫ sigmaShellPairToNeighborhoodPair C n)
      R k) := by
  have hsub : (⋃ j : cell C n, openCell (C := C) n j) ⊆
      (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
    rw [← skeletonLT_succ_diff_skeletonLT n]
    exact sdiff_subset
  refine TopPair.isIso_singularHomologyMap_of_open_cover R _ ?_ ?_
    (fun b : Bool ↦ bif b then (Subtype.val ⁻¹' (skeletonLT C n : Set X))ᶜ else
      interior (Subtype.val ⁻¹' skeletonNeighborhood C n)) (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · -- On the open balls the characteristic maps are a homeomorphism onto the open `n`-cells.
    have h : ⇑(ConcreteCategory.hom (TopPair.Hom.fst
        (sigmaOpenShellPairToShellPair (cell C n) n ≫ sigmaShellPairToNeighborhoodPair C n))) =
        inclusion hsub ∘ iUnionOpenCellHomeomorph (C := C) n := by
      funext p
      exact Subtype.ext (iUnionOpenCellHomeomorph_apply n p).symm
    rw [h]
    exact (IsEmbedding.inclusion hsub).comp (iUnionOpenCellHomeomorph (C := C) n).isEmbedding
  · rintro ⟨j, y⟩ ⟨⟨q, hqN⟩, hq⟩
    have hy : map n j y ∈ skeletonNeighborhood C n := by
      have : q = map n j y := congrArg Subtype.val hq
      exact this ▸ hqN
    exact ⟨⟨⟨j, y⟩, (map_mem_skeletonNeighborhood_iff j (mem_ball_zero_iff.1 y.2).le).1 hy⟩, rfl⟩
  · cases b
    · exact isOpen_interior
    · exact ((skeletonLT C n).closed.preimage continuous_subtype_val).isOpen_compl
  · refine eq_univ_of_forall fun (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) ↦
      mem_iUnion.2 ?_
    by_cases hx : (x : X) ∈ (skeletonLT C n : Set X)
    · exact ⟨false, skeletonLT_subset_interior_skeletonNeighborhood C n hx⟩
    · exact ⟨true, hx⟩
  · cases b
    · exact Or.inl fun (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
        (hx : x ∈ interior (Subtype.val ⁻¹' skeletonNeighborhood C n)) ↦
          ⟨⟨x.1, interior_subset (s := Subtype.val ⁻¹' skeletonNeighborhood C n) hx⟩, rfl⟩
    · -- A point of `Xⁿ` outside `Xⁿ⁻¹` lies in an open `n`-cell.
      refine Or.inr fun (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) hx ↦ ?_
      obtain hx' | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.2
      · exact (hx hx').elim
      · exact ⟨⟨j, y, mem_ball_zero_iff.2 hy⟩, Subtype.ext hxy⟩

section

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **The characteristic maps of the `n`-cells induce isomorphisms
`Hₖ(∐ⱼ (Dⁿ, Sⁿ⁻¹)) ≅ Hₖ(Xⁿ, Xⁿ⁻¹)` on relative singular homology**, in every degree `k`. -/
instance isIso_singularHomologyMap_characteristicPairMap (n k : ℕ) :
    IsIso ((sigmaDiskPair (cell C n) n).singularHomologyMap (characteristicPairMap C n) R k) := by
  -- Thicken the subspaces on both sides: the square of pairs commutes, the thickening of the
  -- skeletal pair and of the disks are isomorphisms, and so is the thickened characteristic map,
  -- by excision on both sides.
  have hsq : characteristicPairMap C n ≫ skeletonPairToNeighborhood C n =
      sigmaDiskPairToShellPair (cell C n) n ≫ sigmaShellPairToNeighborhoodPair C n := by
    ext x : 2
    · obtain ⟨⟨j, y⟩, hy⟩ := x
      have ha :
          (TopPair.Hom.snd (sigmaDiskPairToShellPair (cell C n) n) ⟨⟨j, y⟩, hy⟩).1 = ⟨j, y⟩ :=
        TopPair.ofSubsetMap_snd_apply _ _ _
      exact Subtype.ext ((skeletonPairToNeighborhood_snd_apply C n _).trans (congrArg
        (fun p : Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1 ↦ map n p.1 p.2) ha.symm))
    · exact (skeletonPairToNeighborhood_fst_apply C n _).trans (congrArg
        (TopPair.Hom.fst (sigmaShellPairToNeighborhoodPair C n))
        (TopPair.ofSubsetMap_fst_apply _ (mapsTo_sphere_shell (cell C n) n) x)).symm
  have := isIso_singularHomologyMap_sigmaOpenShellPairToNeighborhoodPair C R n k
  rw [TopPair.singularHomologyMap_comp] at this
  have := isIso_singularHomologyMap_sigmaOpenShellPairToShellPair (cell C n) n R k
  have := IsIso.of_isIso_comp_left
    ((sigmaOpenShellPair (cell C n) n).singularHomologyMap
      (sigmaOpenShellPairToShellPair (cell C n) n) R k)
    ((sigmaShellPair (cell C n) n).singularHomologyMap (sigmaShellPairToNeighborhoodPair C n) R k)
  have := isIso_singularHomologyMap_sigmaDiskPairToShellPair (cell C n) n R k
  have := isIso_singularHomologyMap_skeletonPairToNeighborhood C R n k
  have hcomp : IsIso ((sigmaDiskPair (cell C n) n).singularHomologyMap
      (characteristicPairMap C n ≫ skeletonPairToNeighborhood C n) R k) := by
    rw [hsq, TopPair.singularHomologyMap_comp]
    infer_instance
  rw [TopPair.singularHomologyMap_comp] at hcomp
  exact IsIso.of_isIso_comp_right _
    ((skeletonPair C n).singularHomologyMap (skeletonPairToNeighborhood C n) R k)

/-- The cellular chain group `Hₙ(Xⁿ, Xⁿ⁻¹)` is the relative singular homology of the disjoint
union `∐ⱼ (Dⁿ, Sⁿ⁻¹)` of one disk pair for each `n`-cell; the inverse is induced by the
characteristic maps `TauCeti.characteristicPairMap C n`. -/
def cellularChainGroupIsoSigmaDiskPair (n : ℕ) :
    cellularChainGroup C R n ≅ (sigmaDiskPair (cell C n) n).singularHomology R n :=
  (asIso ((sigmaDiskPair (cell C n) n).singularHomologyMap (characteristicPairMap C n) R n)).symm

@[simp]
lemma cellularChainGroupIsoSigmaDiskPair_inv (n : ℕ) :
    (cellularChainGroupIsoSigmaDiskPair C R n).inv =
      (sigmaDiskPair (cell C n) n).singularHomologyMap (characteristicPairMap C n) R n :=
  (rfl)

end

end TauCeti
