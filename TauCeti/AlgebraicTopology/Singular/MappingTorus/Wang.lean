/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Basic
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.FiberPair
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.CyclicCover
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# The Wang sequence of a mapping torus

The long exact sequence of the pair consisting of a mapping torus and one of its fibres gives
the Wang sequence.  The relative homology identification is the one in
`TauCeti.MappingTorus.singularHomologyFiberPairIso`.  The boundary morphism of the pair, under
this identification, is `id - φ_*` followed by the map induced by the fibre inclusion.  This file
records the exact portion around the homology of the mapping torus, with no restriction on the
coefficient object beyond those required for singular homology.

The construction is the mapping-torus sequence of Hatcher, *Algebraic Topology*, Section 2.2.

The full sequence is also obtained from the short exact sequence of singular chains of the
infinite cyclic cover `F × ℝ → T_φ` (`TauCeti.MappingTorus.cyclicCoverShortComplex_shortExact`),
transported to `F` along the projection `F × ℝ → F`.  This gives the connecting morphism
`TauCeti.MappingTorus.wangδ`, exactness at all three terms, and surjectivity of the fibre
inclusion on degree-zero homology.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w v u

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The map `Hₙ(F) ⟶ Hₙ(T)` on singular homology induced by the fibre inclusion
`MappingTorus.incl` of a mapping torus. -/
noncomputable def wangInclusion (n : ℕ) :
    ((singularHomologyFunctor A n).obj R).obj (TopCat.of F) ⟶
      ((singularHomologyFunctor A n).obj R).obj (TopCat.of (MappingTorus φ)) :=
  ((singularHomologyFunctor A n).obj R).map (TopCat.ofHom (incl φ))

/-- The Wang inclusion is induced by the fibre inclusion. -/
theorem wangInclusion_def (n : ℕ) :
    wangInclusion φ R n = ((singularHomologyFunctor A n).obj R).map (TopCat.ofHom (incl φ)) :=
  (rfl)

/-- The connecting map in the Wang sequence, obtained from the pair sequence and the relative
homology identification `Hₙ₊₁(T, F) ≅ Hₙ(F)`. -/
noncomputable def wangConnecting (n : ℕ) :
    ((singularHomologyFunctor A (n + 1)).obj R).obj (TopCat.of (MappingTorus φ)) ⟶
      ((singularHomologyFunctor A n).obj R).obj (TopCat.of F) :=
  (fiberPair φ).singularHomologyπ R (n + 1) ≫ (singularHomologyFiberPairIso φ R n).hom

/-- The Wang connecting map is the ambient-to-relative homology map followed by the relative
homology identification. -/
theorem wangConnecting_def (n : ℕ) :
    wangConnecting φ R n =
      (fiberPair φ).singularHomologyπ R (n + 1) ≫ (singularHomologyFiberPairIso φ R n).hom :=
  (rfl)

/-- The Wang inclusion factors through the homology of the subspace of `fiberPair φ`. -/
private lemma wangInclusion_eq (n : ℕ) :
    wangInclusion φ R n = ((singularHomologyFunctor A n).obj R).map (fiberPairIncl φ) ≫
      ((singularHomologyFunctor A n).obj R).map (fiberPair φ).map := by
  rw [wangInclusion, ← fiberPairIncl_comp_map]
  exact Functor.map_comp _ _ _

/-- The ambient-to-relative composite of the pair sequence of `fiberPair φ` vanishes. -/
@[reassoc (attr := simp)]
theorem map_comp_wangConnecting (n : ℕ) :
    ((singularHomologyFunctor A (n + 1)).obj R).map
      (TopCat.ofHom (ContinuousMap.subtypeVal (fiber φ))) ≫
      wangConnecting φ R n = 0 :=
  ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) ((fiberPair φ).homologyMap_comp_singularHomologyπ R (n + 1)))).trans
    zero_comp

/-- The map on homology induced by the fibre inclusion, followed by the Wang connecting map, is
zero. -/
@[reassoc (attr := simp)]
theorem wangInclusion_comp_wangConnecting (n : ℕ) :
    wangInclusion φ R (n + 1) ≫ wangConnecting φ R n = 0 := by
  rw [wangInclusion_eq]
  exact (Category.assoc _ _ _).trans
    ((congrArg _ (map_comp_wangConnecting φ R n)).trans comp_zero)

/-- The exact portion `Hₙ₊₁(F) → Hₙ₊₁(T) → Hₙ(F)` of the Wang sequence, transported from the
exactness of the pair sequence of `fiberPair φ` at ambient homology. -/
theorem wang_exact_total (n : ℕ) :
    (ShortComplex.mk (wangInclusion φ R (n + 1)) (wangConnecting φ R n)
      (wangInclusion_comp_wangConnecting φ R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ ((fiberPair φ).singularHomology_exact_space R (n + 1))
  exact ShortComplex.isoMk
    (((singularHomologyFunctor A (n + 1)).obj R).mapIso (asIso (fiberPairIncl φ))).symm
    (Iso.refl _) (singularHomologyFiberPairIso φ R n)
    ((congrArg _ (wangInclusion_eq φ R (n + 1))).trans
      ((((singularHomologyFunctor A (n + 1)).obj R).mapIso
        (asIso (fiberPairIncl φ))).inv_hom_id_assoc _ |>.trans (Category.comp_id _).symm))
    (Category.id_comp _)

variable (F) in
/-- The projection `F × ℝ → F` is an isomorphism on singular homology, with inverse the inclusion
at height zero. -/
def cylinderHomologyIso (n : ℕ) :
    (((singularChainComplexFunctor A).obj R).obj (TopCat.of (F × ℝ))).homology n ≅
      (((singularChainComplexFunctor A).obj R).obj (TopCat.of F)).homology n :=
  (cylinderHomotopyEquiv F).singularHomologyIso R n

variable (F) in
/-- The forward map of `cylinderHomologyIso` is induced by projection onto the fibre. -/
lemma cylinderHomologyIso_hom (n : ℕ) :
    (cylinderHomologyIso F R n).hom = homologyMap (((singularChainComplexFunctor A).obj R).map
      (TopCat.ofHom (cylinderHomotopyEquiv F).toFun)) n :=
  (cylinderHomotopyEquiv F).singularHomologyIso_hom R n

variable (F) in
/-- The inverse map of `cylinderHomologyIso` is induced by inclusion at height zero. -/
lemma cylinderHomologyIso_inv (n : ℕ) :
    (cylinderHomologyIso F R n).inv = homologyMap (((singularChainComplexFunctor A).obj R).map
      (TopCat.ofHom (cylinderHomotopyEquiv F).invFun)) n :=
  (cylinderHomotopyEquiv F).singularHomologyIso_inv R n

/-- On homology, the deck transformation of the cylinder corresponds to the monodromy under the
projection `F × ℝ → F`. -/
lemma homologyMap_deckChainMap_comp (n : ℕ) :
    homologyMap (deckChainMap φ R) n ≫ (cylinderHomologyIso F R n).hom =
      (cylinderHomologyIso F R n).hom ≫ homologyMap (monodromyChainMap φ R) n := by
  rw [cylinderHomologyIso_hom, deckChainMap_def, monodromyChainMap_def, ← homologyMap_comp,
    ← homologyMap_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  ext p
  simp

/-- On homology, the covering map is the projection `F × ℝ → F` followed by the fibre
inclusion. -/
lemma homologyMap_coverChainMap (n : ℕ) :
    homologyMap (coverChainMap φ R) n =
      (cylinderHomologyIso F R n).hom ≫ homologyMap (fibreInclusionChainMap φ R) n := by
  rw [← Iso.inv_comp_eq, cylinderHomologyIso_inv, coverChainMap_def, fibreInclusionChainMap_def,
    ← homologyMap_comp, ← Functor.map_comp]
  congr 2
  ext x
  simp

/-- The map `𝟙 - φ_*` on homology is the map `𝟙 - τ_*` of the cylinder, transported along the
projection. -/
lemma homologyMap_id_sub_deckChainMap_comp (n : ℕ) :
    homologyMap (𝟙 _ - deckChainMap φ R) n ≫ (cylinderHomologyIso F R n).hom =
      (cylinderHomologyIso F R n).hom ≫ homologyMap (wangEndomorphism φ R) n := by
  rw [wangEndomorphism_def, homologyMap_sub, homologyMap_sub, homologyMap_id, homologyMap_id,
    Preadditive.sub_comp, Preadditive.comp_sub, homologyMap_deckChainMap_comp]
  simp

/-- **The Wang connecting morphism** `Hₙ₊₁(T_φ) ⟶ Hₙ(F)` of the mapping torus of `φ`: the
connecting morphism of the short exact sequence of chains of the infinite cyclic cover, followed
by the projection `F × ℝ → F`. -/
def wangδ (n : ℕ) :
    (((singularChainComplexFunctor A).obj R).obj (TopCat.of (MappingTorus φ))).homology (n + 1) ⟶
      (((singularChainComplexFunctor A).obj R).obj (TopCat.of F)).homology n :=
  (cyclicCoverShortComplex_shortExact φ R).δ (n + 1) n (by simp) ≫ (cylinderHomologyIso F R n).hom

/-- The Wang connecting morphism is the connecting morphism of the cyclic cover followed by the
projection `F × ℝ → F`. -/
lemma wangδ_def (n : ℕ) :
    wangδ φ R n = (cyclicCoverShortComplex_shortExact φ R).δ (n + 1) n (by simp) ≫
      homologyMap (((singularChainComplexFunctor A).obj R).map
        (TopCat.ofHom (cylinderHomotopyEquiv F).toFun)) n := by
  rw [wangδ, cylinderHomologyIso_hom]

/-- The composite `Hₙ₊₁(T_φ) ⟶ Hₙ(F) ⟶ Hₙ(F)` of the Wang connecting morphism and `𝟙 - φ_*`
vanishes. -/
@[reassoc]
lemma wangδ_comp_homologyMap_wangEndomorphism (n : ℕ) :
    wangδ φ R n ≫ homologyMap (wangEndomorphism φ R) n = 0 := by
  rw [wangδ, Category.assoc, ← homologyMap_id_sub_deckChainMap_comp, ← Category.assoc,
    (cyclicCoverShortComplex_shortExact φ R).δ_comp, zero_comp]

/-- The composite `Hₙ₊₁(F) ⟶ Hₙ₊₁(T_φ) ⟶ Hₙ(F)` of the fibre inclusion and the Wang connecting
morphism vanishes. -/
@[reassoc (attr := simp)]
lemma homologyMap_fibreInclusionChainMap_comp_wangδ (n : ℕ) :
    homologyMap (fibreInclusionChainMap φ R) (n + 1) ≫ wangδ φ R n = 0 := by
  rw [← cancel_epi (cylinderHomologyIso F R (n + 1)).hom, ← reassoc_of% homologyMap_coverChainMap,
    wangδ, reassoc_of% (cyclicCoverShortComplex_shortExact φ R).comp_δ, zero_comp, comp_zero]

/-- **Exactness of the Wang sequence at `Hₙ(F)`, after the connecting morphism**:
`Hₙ₊₁(T_φ) ⟶ Hₙ(F) ⟶ Hₙ(F)`, with maps `wangδ` and `𝟙 - φ_*`. -/
theorem wang_exact₁ (n : ℕ) :
    (ShortComplex.mk _ _ (wangδ_comp_homologyMap_wangEndomorphism φ R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((cyclicCoverShortComplex_shortExact φ R).homology_exact₁ (n + 1) n (by simp))
  exact ShortComplex.isoMk (Iso.refl _) (cylinderHomologyIso F R n) (cylinderHomologyIso F R n)
    (by simp [wangδ]) (homologyMap_id_sub_deckChainMap_comp φ R n).symm

/-- **Exactness of the Wang sequence at `Hₙ(F)`, after `𝟙 - φ_*`**: `Hₙ(F) ⟶ Hₙ(F) ⟶ Hₙ(T_φ)`,
with maps `𝟙 - φ_*` and the fibre inclusion. -/
theorem wang_exact₂ (n : ℕ) :
    (ShortComplex.mk (homologyMap (wangEndomorphism φ R) n)
      (homologyMap (fibreInclusionChainMap φ R) n) (by simp)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((cyclicCoverShortComplex_shortExact φ R).homology_exact₂ n)
  exact ShortComplex.isoMk (cylinderHomologyIso F R n) (cylinderHomologyIso F R n) (Iso.refl _)
    (homologyMap_id_sub_deckChainMap_comp φ R n).symm
    (by simp [homologyMap_coverChainMap])

/-- **Exactness of the Wang sequence at `Hₙ₊₁(T_φ)`**: `Hₙ₊₁(F) ⟶ Hₙ₊₁(T_φ) ⟶ Hₙ(F)`, with maps
the fibre inclusion and `wangδ`. -/
theorem wang_exact₃ (n : ℕ) :
    (ShortComplex.mk _ _ (homologyMap_fibreInclusionChainMap_comp_wangδ φ R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((cyclicCoverShortComplex_shortExact φ R).homology_exact₃ (n + 1) n (by simp))
  exact ShortComplex.isoMk (cylinderHomologyIso F R (n + 1)) (Iso.refl _)
    (cylinderHomologyIso F R n) (by simp [homologyMap_coverChainMap]) (by simp [wangδ])

/-- The Wang sequence ends with `H₀(F) ⟶ H₀(T_φ) ⟶ 0`: the fibre inclusion is surjective on
`H₀`. -/
instance epi_homologyMap_fibreInclusionChainMap_zero :
    Epi (homologyMap (fibreInclusionChainMap φ R) 0) := by
  have := (cyclicCoverShortComplex_shortExact φ R).epi_g
  have : Epi (homologyMap (coverChainMap φ R) 0) :=
    epi_homologyMap_of_epi_of_not_rel _ 0 (by simp)
  rw [homologyMap_coverChainMap] at this
  exact epi_of_epi (cylinderHomologyIso F R 0).hom _

end TauCeti.MappingTorus

end
