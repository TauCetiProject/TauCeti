/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.FiberPair

/-!
# The Wang sequence of a mapping torus

The long exact sequence of the pair consisting of a mapping torus and one of its fibres gives
the Wang sequence.  The relative homology identification is the one in
`TauCeti.MappingTorus.singularHomologyFiberPairIso`.  The boundary morphism of the pair, under
this identification, is `id - φ_*` followed by the map induced by the fibre inclusion.  This file
records the exact portion around the homology of the mapping torus, with no restriction on the
coefficient object beyond those required for singular homology.

The construction is the mapping-torus sequence of Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

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

end TauCeti.MappingTorus

end
