/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.ChainComparison
public import TauCeti.AlgebraicTopology.ClassifyingSpace.StandardResolution

/-!
# Equivariant geometric cellular chains of Milnor's join

The cellular chains of `universalGSpace G`, with the simplicial CW structure, form a
projective resolution in `Rep k G`. The action is induced by actual translations of the
space, and the differential is the geometric cellular differential. This uses the original
simplicial characteristic maps, not a newly lifted CW structure.

The cellular-to-ordered chain comparison lifts to an isomorphism of complexes of
representations. Composing it with the explicit ordered join-to-bar comparison gives a
chain homotopy equivalence in `Rep k G`, before forgetting the action. Thus the inverse
and both chain homotopies are equivariant as well as the forward comparison.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections I.4 and II.4.
-/

public section

noncomputable section

open CategoryTheory Set Topology

namespace TauCeti

universe u

attribute [local instance] universalGSpaceVertexOrder

section ChainComplex

variable (k : Type u) [Ring k] (G : Type u) [Group G]

/-- The action on geometric cellular chains induced by translation of Milnor's join. -/
def universalGSpaceCellularRepresentation (n : ℕ) :
    Representation k G
      (cellularChainGroup (univ : Set (universalGSpace G)) (ModuleCat.of k k) n : ModuleCat k) where
  toFun g := (cellularChainGroupMap univ univ
    (isCellular_universalGSpaceCellularTranslation g) (ModuleCat.of k k) n).hom
  map_one' := (cellularChainBasis (univ : Set (universalGSpace G)) k n).ext fun c ↦ by
    simp only [cellularChainGroupMap_universalGSpaceCellularTranslation_cellularChainBasis,
      one_smul, one_apply_eq_self]
  map_mul' g h := (cellularChainBasis (univ : Set (universalGSpace G)) k n).ext fun c ↦ by
    simp only [mul_apply_eq_comp,
      cellularChainGroupMap_universalGSpaceCellularTranslation_cellularChainBasis, mul_smul]

/-- The representation acts by the actual cellular map of translation. -/
@[simp]
theorem universalGSpaceCellularRepresentation_apply (n : ℕ) (g : G) :
    universalGSpaceCellularRepresentation k G n g =
      (cellularChainGroupMap univ univ (isCellular_universalGSpaceCellularTranslation g)
        (ModuleCat.of k k) n).hom := (rfl)

/-- The geometric cellular differential is equivariant for translation. -/
def universalGSpaceCellularDifferential (n : ℕ) :
    Rep.of (universalGSpaceCellularRepresentation k G (n + 1)) ⟶
      Rep.of (universalGSpaceCellularRepresentation k G n) :=
  Rep.ofHom
    { toLinearMap := (cellularDifferential (univ : Set (universalGSpace G))
        (ModuleCat.of k k) n).hom
      isIntertwining' g := by
        simpa only [universalGSpaceCellularRepresentation_apply, ModuleCat.hom_comp] using
          congrArg ModuleCat.Hom.hom
            (cellularChainGroupMap_comp_cellularDifferential univ univ
              (isCellular_universalGSpaceCellularTranslation g) (ModuleCat.of k k) n) }

/-- Forgetting equivariance gives the geometric cellular differential. -/
@[simp]
theorem universalGSpaceCellularDifferential_hom_toLinearMap (n : ℕ) :
    (universalGSpaceCellularDifferential k G n).hom.toLinearMap =
      (cellularDifferential (univ : Set (universalGSpace G)) (ModuleCat.of k k) n).hom := (rfl)

/-- Geometric cellular chains of Milnor's join, retaining the translation action. -/
def universalGSpaceCellularComplex : ChainComplex (Rep k G) ℕ :=
  ChainComplex.of (fun n ↦ Rep.of (universalGSpaceCellularRepresentation k G n))
    (universalGSpaceCellularDifferential k G) fun n ↦ by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      simpa only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
        Rep.zero_hom, Representation.IntertwiningMap.zero_toLinearMap,
        universalGSpaceCellularDifferential_hom_toLinearMap, ModuleCat.hom_comp,
        ModuleCat.hom_zero] using congrArg ModuleCat.Hom.hom
          (cellularDifferential_comp_cellularDifferential
            (univ : Set (universalGSpace G)) (ModuleCat.of k k) n)

/-- The terms are the geometric cellular chain groups with the translation action. -/
@[simp]
theorem universalGSpaceCellularComplex_X (n : ℕ) :
    (universalGSpaceCellularComplex k G).X n =
      Rep.of (universalGSpaceCellularRepresentation k G n) := (rfl)

/-- The differential is the equivariant geometric cellular differential. -/
@[simp]
theorem universalGSpaceCellularComplex_d (n : ℕ) :
    (universalGSpaceCellularComplex k G).d (n + 1) n =
      eqToHom (universalGSpaceCellularComplex_X k G (n + 1)) ≫
        universalGSpaceCellularDifferential k G n ≫
      eqToHom (universalGSpaceCellularComplex_X k G n).symm := by
  have h : ∀ m, universalGSpaceCellularComplex_X k G m = rfl := fun _ ↦ Subsingleton.elim _ _
  rw [h (n + 1), h n]
  unfold universalGSpaceCellularComplex
  simp only [ChainComplex.of_d, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The scaled cellular-basis comparison is an isomorphism of representations, not merely
of underlying modules. -/
def universalGSpaceCellularRepIso (n : ℕ) :
    Rep.of (universalGSpaceCellularRepresentation k G n) ≅
      Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n) :=
  Rep.mkIso
    { __ := universalGSpaceCellularChainLinearEquiv k G n
      isIntertwining' g := LinearMap.ext fun x ↦
        universalGSpaceCellularChainLinearEquiv_translation k g n x }

/-- The equivariant comparison has the existing scaled cellular-to-ordered linear map. -/
@[simp]
theorem universalGSpaceCellularRepIso_hom_toLinearMap (n : ℕ) :
    (universalGSpaceCellularRepIso k G n).hom.hom.toLinearMap =
      (universalGSpaceCellularChainLinearEquiv k G n).toLinearMap := (rfl)

/-- Geometric and ordered cellular chains are isomorphic before forgetting the action. -/
def universalGSpaceCellularComplexIso :
    universalGSpaceCellularComplex k G ≅ universalGSpaceChainComplex k G :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ eqToIso (universalGSpaceCellularComplex_X k G n) ≪≫
      universalGSpaceCellularRepIso k G n ≪≫
      eqToIso (universalGSpaceChainComplex_X k G n).symm)
    fun i j hij ↦ by
      subst i
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      have h := (universalGSpaceCellularChainComplexIso k G).hom.comm (j + 1) j
      -- The underlying chain square uses transports from the cellular complex terms to
      -- cellular chain groups. Normalize its component formulas before comparing linear maps.
      simp only [universalGSpaceCellularChainComplexIso_hom_f,
        cellularChainComplex_d, Functor.mapHomologicalComplex_obj_d] at h
      dsimp only [universalGSpaceChainComplex] at h
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at h
      have h' := (cancel_epi (eqToHom (cellularChainComplex_X
        (univ : Set (universalGSpace G)) (ModuleCat.of k k) (j + 1)))).mp h
      simp only [universalGSpaceCellularComplex_d, universalGSpaceChainComplex_d,
        Iso.trans_hom, eqToIso.hom]
      have hc : ∀ m, universalGSpaceCellularComplex_X k G m = rfl :=
        fun _ ↦ Subsingleton.elim _ _
      have ht : ∀ m, universalGSpaceChainComplex_X k G m = rfl :=
        fun _ ↦ Subsingleton.elim _ _
      rw [hc (j + 1), hc j, ht (j + 1), ht j]
      -- Evaluate before normalizing the complex terms, retaining the bundled module instances.
      ext x
      have hv := ConcreteCategory.congr_hom h' x
      simp only [ChainComplex.of_d, Rep.forget₂_moduleCat_map,
        LinearEquiv.toModuleIso_hom] at hv
      unfold universalGSpaceCellularComplex at x ⊢
      unfold universalGSpaceCellularRepIso universalGSpaceCellularDifferential
      convert hv using 1
      rfl

/-- The component of the chain comparison is the equivariant scaled basis comparison. -/
@[simp]
theorem universalGSpaceCellularComplexIso_hom_f (n : ℕ) :
    (universalGSpaceCellularComplexIso k G).hom.f n =
      eqToHom (universalGSpaceCellularComplex_X k G n) ≫
        (universalGSpaceCellularRepIso k G n).hom ≫
      eqToHom (universalGSpaceChainComplex_X k G n).symm := (rfl)

end ChainComplex

section Resolution

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-- Each geometric cellular chain representation is projective, via its isomorphism
with the free ordered-chain representation. -/
instance (n : ℕ) : Projective ((universalGSpaceCellularComplex k G).X n) :=
  Projective.of_iso (HomologicalComplex.Hom.isoApp
    (universalGSpaceCellularComplexIso k G) n).symm
    ((universalGSpaceResolution k G).projective n)

/-- Geometric cellular chains with their translation action resolve the trivial module.
The augmentation is the cellular augmentation, expressed via ordered chains. -/
def universalGSpaceCellularResolution : ProjectiveResolution (Rep.trivial k G k) where
  complex := universalGSpaceCellularComplex k G
  π := (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G

/-- The resolution uses the geometric cellular complex. -/
@[simp]
theorem universalGSpaceCellularResolution_complex :
    (universalGSpaceCellularResolution k G).complex = universalGSpaceCellularComplex k G := (rfl)

/-- Its augmentation is the ordered augmentation after the equivariant cellular comparison. -/
@[simp]
theorem universalGSpaceCellularResolution_π :
    (universalGSpaceCellularResolution k G).π =
      eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G :=
  (Category.id_comp _).symm

/-- In degree zero the augmentation is the geometric cellular augmentation, not just
an abstract map to the trivial representation. -/
theorem universalGSpaceCellularResolution_π_f_zero_hom
    (x : (cellularChainGroup (univ : Set (universalGSpace G))
      (ModuleCat.of k k) 0 : ModuleCat k)) :
    ((eqToHom (universalGSpaceCellularResolution_complex k G).symm ≫
        (universalGSpaceCellularResolution k G).π).f 0).hom
      ((eqToHom (universalGSpaceCellularComplex_X k G 0).symm) x) =
      cellularAugmentation (univ : Set (universalGSpace G)) (ModuleCat.of k k) x := by
  -- Evaluation cancels the transports identifying the resolution's degree-zero term with
  -- its geometric cellular chain group.
  simp only [universalGSpaceCellularResolution_π, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, HomologicalComplex.comp_f, universalGSpaceCellularComplexIso_hom_f,
    universalGSpaceAugmentation_f_zero]
  unfold universalGSpaceCellularComplex universalGSpaceCellularRepIso
  convert ConcreteCategory.congr_hom
    (universalGSpaceCellularChainLinearEquiv_comp_permutationAugmentation k G) x using 1
  rfl

/-- The geometric cellular-to-bar comparison is a chain homotopy equivalence in `Rep k G`:
its inverse and both homotopies retain equivariance. -/
def universalGSpaceCellularStandardEquivariantHomotopyEquiv :
    HomotopyEquiv (universalGSpaceCellularComplex k G) (Rep.standardComplex k G) :=
  (HomotopyEquiv.ofIso (universalGSpaceCellularComplexIso k G)).trans
    (universalGSpaceStandardHomotopyEquiv k G)

/-- The equivariant comparison is the geometric-to-ordered map followed by the explicit
map forgetting the indices of the vertices. -/
@[simp]
theorem universalGSpaceCellularStandardEquivariantHomotopyEquiv_hom :
    (universalGSpaceCellularStandardEquivariantHomotopyEquiv k G).hom =
      (universalGSpaceCellularComplexIso k G).hom ≫
        universalGSpaceChainComplexToStandardComplex k G := by
  simp [universalGSpaceCellularStandardEquivariantHomotopyEquiv,
    HomotopyEquiv.trans, HomotopyEquiv.ofIso]

/-- A geometric cellular basis vector maps to its increasing-index tuple of labels,
scaled by the orientation unit of the simplicial cellular comparison. This is not a simp
lemma because `cellularChainBasis_apply` expands its argument first. -/
theorem universalGSpaceCellularStandardEquivariantHomotopyEquiv_cellularChainBasis {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    ((universalGSpaceCellularStandardEquivariantHomotopyEquiv k G).hom.f n).hom
        ((eqToHom (universalGSpaceCellularComplex_X k G n).symm)
          (cellularChainBasis (univ : Set (universalGSpace G)) k n
            ((AbstractSimplicialComplex.realizationCellEquiv _ n).symm c))) =
      MonoidAlgebra.single (universalGSpaceCellLabels c) (realizationChainScale k n : k) := by
  rw [universalGSpaceCellularStandardEquivariantHomotopyEquiv_hom]
  simp only [HomologicalComplex.comp_f, universalGSpaceCellularComplexIso_hom_f]
  -- The transports identify complex terms with the geometric chain groups and permutation
  -- modules; after evaluation the two successive transports cancel.
  have h := universalGSpaceCellularChainLinearEquiv_cellularChainBasis k G c
  have h' := universalGSpaceChainComplexToStandardComplex_f_hom_single k G c
    (realizationChainScale k n : k)
  convert h' using 1
  rw [← h]
  rfl

/-- The geometric cellular-to-bar map preserves augmentation. -/
@[reassoc]
theorem universalGSpaceCellularStandardEquivariantHomotopyEquiv_comp_π :
    (universalGSpaceCellularStandardEquivariantHomotopyEquiv k G).hom ≫
        (Rep.standardResolution k G).π =
      (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G := by
  rw [universalGSpaceCellularStandardEquivariantHomotopyEquiv_hom]
  exact (Category.assoc _ _ _).trans
    (congrArg ((universalGSpaceCellularComplexIso k G).hom ≫ ·)
      (universalGSpaceChainComplexToStandardComplex_comp_standardResolution_π k G))

/-- The explicit geometric cellular-to-bar map agrees up to equivariant chain homotopy
with Mathlib's abstract comparison of the two projective resolutions. -/
def universalGSpaceCellularStandardComparisonHomotopy :
    Homotopy (eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        (universalGSpaceCellularStandardEquivariantHomotopyEquiv k G).hom)
      (ProjectiveResolution.homotopyEquiv (universalGSpaceCellularResolution k G)
        (Rep.standardResolution k G)).hom :=
  ProjectiveResolution.homotopyOfComm (universalGSpaceCellularResolution k G)
    (Rep.standardResolution k G) _ (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (eqToHom (universalGSpaceCellularResolution_complex k G) ≫ ·)
          (universalGSpaceCellularStandardEquivariantHomotopyEquiv_comp_π k G)).trans
          (universalGSpaceCellularResolution_π k G).symm))

end Resolution

end TauCeti
