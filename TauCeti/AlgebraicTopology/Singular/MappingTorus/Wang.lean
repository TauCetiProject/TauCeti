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
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Topology.Homotopy.HomotopyEquiv

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
inclusion on degree-zero homology.  When the monodromy acts trivially on `Hₙ(F)`, `wangδ` is
surjective onto `Hₙ(F)` (`TauCeti.MappingTorus.epi_wangδ_of_homologyMap_monodromyChainMap_eq_id`);
for a path-connected fibre this holds on `H₀(F)` (`TauCeti.MappingTorus.epi_wangδ_zero`).  With
coefficients in a commutative ring `k`, exactness identifies the cokernel of `𝟙 - φ_*` on
`Hₙ(F)` with the image of the fibre in `Hₙ(T_φ)` (`TauCeti.MappingTorus.wangCokernelEquiv`).
When the Wang connecting morphism `Hₙ₊₁(T_φ) ⟶ Hₙ(F)` is onto, this gives the Wang short exact
sequence `0 ⟶ Hₙ₊₁(F) ⧸ range (𝟙 - φ_*) ⟶ Hₙ₊₁(T_φ) ⟶ Hₙ(F) ⟶ 0`
(`TauCeti.MappingTorus.wangCokernelShortComplex_shortExact`). For every monodromy, the image of
the Wang connecting morphism is the kernel of `𝟙 - φ_*` on `Hₙ(F)`
(`TauCeti.MappingTorus.range_wangδ`), so the Wang sequence breaks into the short exact sequences
`0 ⟶ Hₙ₊₁(F) ⧸ range (𝟙 - φ_*) ⟶ Hₙ₊₁(T_φ) ⟶ ker (𝟙 - φ_*) ⟶ 0`
(`TauCeti.MappingTorus.wangKernelShortComplex_shortExact`).

When `𝟙 - φ_*` is a monomorphism on `Hₙ(F)`, the Wang connecting morphism `Hₙ₊₁(T_φ) ⟶ Hₙ(F)`
vanishes (`TauCeti.MappingTorus.wangδ_eq_zero`), so the fibre inclusion is an epimorphism on
`Hₙ₊₁` (`TauCeti.MappingTorus.epi_homologyMap_fibreInclusionChainMap_succ`). If moreover `φ_*` is
the identity on `Hₙ₊₁(F)`, the fibre inclusion is an isomorphism `Hₙ₊₁(F) ≅ Hₙ₊₁(T_φ)`
(`TauCeti.MappingTorus.isIso_homologyMap_fibreInclusionChainMap_succ`).

The Wang connecting morphism is natural for maps of infinite cyclic covers: if
`Φ : F × ℝ → G × ℝ` intertwines the deck transformations of `φ` and `ψ`, then `Φ` and the map
`T_φ → T_ψ` descended from it (`TauCeti.MappingTorus.descend`) form a morphism of the short exact
sequences of the infinite cyclic covers (`TauCeti.MappingTorus.cyclicCoverShortComplexMap`), so
`wangδ` takes the descended map to `g_*`, where `g x = (Φ (x, 0)).1` is the restriction of `Φ` to
height zero (`TauCeti.MappingTorus.singularHomologyMap_descend_comp_wangδ`). The map `g` need not
intertwine the monodromies, so this applies to maps of mapping tori that do not preserve the
fibres, such as the tori swept by loops of sections. For a map `g : F → G` with
`g ∘ φ = ψ ∘ g`, the map induced by `g` is descended from `g × 𝟙ℝ`, so `wangδ` commutes with the
induced maps on homology (`TauCeti.MappingTorus.singularHomologyMap_map_comp_wangδ`, and
`TauCeti.MappingTorus.wangδ_naturality` for the chain maps).
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
  (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.singularHomologyIso R n

variable (F) in
/-- The forward map of `cylinderHomologyIso` is induced by projection onto the fibre. -/
lemma cylinderHomologyIso_hom (n : ℕ) :
    (cylinderHomologyIso F R n).hom = homologyMap (((singularChainComplexFunctor A).obj R).map
      (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.toFun)) n :=
  (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.singularHomologyIso_hom R n

variable (F) in
/-- The inverse map of `cylinderHomologyIso` is induced by inclusion at height zero. -/
lemma cylinderHomologyIso_inv (n : ℕ) :
    (cylinderHomologyIso F R n).inv = homologyMap (((singularChainComplexFunctor A).obj R).map
      (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.invFun)) n :=
  (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.singularHomologyIso_inv R n

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
        (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.toFun)) n := by
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

/-- **The end of the Wang sequence** of a mapping torus with path-connected fibre:
`H₁(T_φ) ⟶ H₀(F) ⟶ 0`, that is, the Wang connecting morphism is an epimorphism in degree zero. -/
instance epi_wangδ_zero [PathConnectedSpace F] : Epi (wangδ φ R 0) :=
  (wang_exact₁ φ R 0).epi_f (by simp)

/-- If `𝟙 - φ_*` is a monomorphism on `Hₙ(F)`, the Wang connecting morphism `Hₙ₊₁(T_φ) ⟶ Hₙ(F)`
vanishes. -/
theorem wangδ_eq_zero (n : ℕ) [Mono (homologyMap (wangEndomorphism φ R) n)] :
    wangδ φ R n = 0 :=
  (wang_exact₁ φ R n).mono_g_iff.1 inferInstance

/-- If `𝟙 - φ_*` is a monomorphism on `Hₙ(F)`, the fibre inclusion `Hₙ₊₁(F) ⟶ Hₙ₊₁(T_φ)` is an
epimorphism. -/
instance epi_homologyMap_fibreInclusionChainMap_succ (n : ℕ)
    [Mono (homologyMap (wangEndomorphism φ R) n)] :
    Epi (homologyMap (fibreInclusionChainMap φ R) (n + 1)) :=
  (wang_exact₃ φ R n).epi_f (wangδ_eq_zero φ R n)

/-- If `𝟙 - φ_*` is a monomorphism on `Hₙ(F)` and `Hₙ₊₁(F)` vanishes, then `Hₙ₊₁(T_φ)` vanishes. -/
theorem isZero_homology_succ (n : ℕ) [Mono (homologyMap (wangEndomorphism φ R) n)]
    (h : IsZero ((((singularChainComplexFunctor A).obj R).obj (TopCat.of F)).homology (n + 1))) :
    IsZero ((((singularChainComplexFunctor A).obj R).obj
      (TopCat.of (MappingTorus φ))).homology (n + 1)) :=
  h.of_epi (homologyMap (fibreInclusionChainMap φ R) (n + 1))

/-- If the monodromy acts trivially on `Hₙ(F)`, the fibre inclusion `Hₙ(F) ⟶ Hₙ(T_φ)` is a
monomorphism. -/
theorem mono_homologyMap_fibreInclusionChainMap (n : ℕ)
    (hφ : homologyMap (monodromyChainMap φ R) n = 𝟙 _) :
    Mono (homologyMap (fibreInclusionChainMap φ R) n) :=
  (wang_exact₂ φ R n).mono_g (by simp [hφ])

/-- If the monodromy acts trivially on `Hₙ(F)`, the Wang connecting morphism `Hₙ₊₁(T_φ) ⟶ Hₙ(F)`
is an epimorphism. -/
theorem epi_wangδ_of_homologyMap_monodromyChainMap_eq_id (n : ℕ)
    (hφ : homologyMap (monodromyChainMap φ R) n = 𝟙 _) :
    Epi (wangδ φ R n) :=
  (wang_exact₁ φ R n).epi_f (by simp [hφ])

/-- If `𝟙 - φ_*` is a monomorphism on `Hₙ(F)` and the monodromy acts trivially on `Hₙ₊₁(F)`, the
fibre inclusion is an isomorphism `Hₙ₊₁(F) ≅ Hₙ₊₁(T_φ)`. -/
theorem isIso_homologyMap_fibreInclusionChainMap_succ (n : ℕ)
    [Mono (homologyMap (wangEndomorphism φ R) n)]
    (hφ : homologyMap (monodromyChainMap φ R) (n + 1) = 𝟙 _) :
    IsIso (homologyMap (fibreInclusionChainMap φ R) (n + 1)) :=
  have := mono_homologyMap_fibreInclusionChainMap φ R (n + 1) hφ
  isIso_of_mono_of_epi _

section Naturality

/-! ### Naturality of the Wang connecting morphism -/

variable {G : Type w} [TopologicalSpace G] (ψ : G ≃ₜ G) (Φ : C(F × ℝ, G × ℝ))
  (hΦ : Function.Semiconj Φ (deck φ) (deck ψ))

/-- The morphism of short exact sequences of chains of the infinite cyclic covers induced by a map
`Φ` of cylinders intertwining the deck transformations: `Φ` on the cylinders and the map of mapping
tori descended from it (`TauCeti.MappingTorus.descend`). -/
def cyclicCoverShortComplexMap : cyclicCoverShortComplex φ R ⟶ cyclicCoverShortComplex ψ R where
  τ₁ := ((singularChainComplexFunctor A).obj R).map (TopCat.ofHom Φ)
  τ₂ := ((singularChainComplexFunctor A).obj R).map (TopCat.ofHom Φ)
  τ₃ := ((singularChainComplexFunctor A).obj R).map (TopCat.ofHom (descend φ ψ Φ hΦ))
  comm₁₂ := by
    rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
      deckChainMap_def, deckChainMap_def, ← Functor.map_comp, ← Functor.map_comp]
    congr 2
    ext p
    · exact congrArg Prod.fst (hΦ p).symm
    · exact congrArg Prod.snd (hΦ p).symm
  comm₂₃ := by
    -- the second maps of the cyclic cover sequences are the cover chain maps, which `rw` does not
    -- see through the projection `ShortComplex.g`
    change _ ≫ coverChainMap ψ R = coverChainMap φ R ≫ _
    rw [coverChainMap_def, coverChainMap_def, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext p
    exact (DFunLike.congr_fun (descend_comp_coverMap φ Φ hΦ) p).symm

/-- On the chains of the source cylinder, the morphism of infinite cyclic cover sequences is
`Φ`. -/
@[simp]
lemma cyclicCoverShortComplexMap_τ₁ :
    (cyclicCoverShortComplexMap φ R ψ Φ hΦ).τ₁ =
      ((singularChainComplexFunctor A).obj R).map (TopCat.ofHom Φ) :=
  (rfl)

/-- On the chains of the middle cylinder, the morphism of infinite cyclic cover sequences is
`Φ`. -/
@[simp]
lemma cyclicCoverShortComplexMap_τ₂ :
    (cyclicCoverShortComplexMap φ R ψ Φ hΦ).τ₂ =
      ((singularChainComplexFunctor A).obj R).map (TopCat.ofHom Φ) :=
  (rfl)

/-- On the chains of the mapping tori, the morphism of infinite cyclic cover sequences is the chain
map induced by the descended map of mapping tori. -/
@[simp]
lemma cyclicCoverShortComplexMap_τ₃ :
    (cyclicCoverShortComplexMap φ R ψ Φ hΦ).τ₃ =
      ((singularChainComplexFunctor A).obj R).map (TopCat.ofHom (descend φ ψ Φ hΦ)) :=
  (rfl)

/-- **Naturality of the Wang connecting morphism for maps of infinite cyclic covers.** Let
`Φ : F × ℝ → G × ℝ` intertwine the deck transformations of `φ` and `ψ`, and let `g : F → G` be
its restriction to height zero, `g x = (Φ (x, 0)).1`. Then the Wang connecting morphisms
`Hₙ₊₁(T_φ) ⟶ Hₙ(F)` and `Hₙ₊₁(T_ψ) ⟶ Hₙ(G)` commute with the map induced by the descended map
of mapping tori and with `g_*`.

The map `g` need not intertwine the monodromies: on the homology of the cylinders `Φ` is `g`,
read through the zero section and the projection, which are mutually inverse there. -/
@[reassoc]
theorem singularHomologyMap_descend_comp_wangδ (g : C(F, G)) (hg : ∀ x, (Φ (x, 0)).1 = g x)
    (n : ℕ) :
    ((singularHomologyFunctor A (n + 1)).obj R).map (TopCat.ofHom (descend φ ψ Φ hΦ)) ≫
        wangδ ψ R n =
      wangδ φ R n ≫ ((singularHomologyFunctor A n).obj R).map (TopCat.ofHom g) := by
  -- Mathlib defines `singularHomologyFunctor A n` as `singularChainComplexFunctor A` followed by
  -- `homologyFunctor _ _ n`, so the maps on singular homology are `homologyMap`s of chain maps.
  change homologyMap _ (n + 1) ≫ _ = _ ≫ homologyMap _ n
  have hδ := HomologicalComplex.HomologySequence.δ_naturality
    (cyclicCoverShortComplexMap φ R ψ Φ hΦ) (cyclicCoverShortComplex_shortExact φ R)
    (cyclicCoverShortComplex_shortExact ψ R) (n + 1) n (by simp)
  -- On the homology of the cylinders, `Φ` followed by the projection is the projection followed
  -- by `g`, since the zero section inverts the projection there.
  have hcyl : homologyMap (cyclicCoverShortComplexMap φ R ψ Φ hΦ).τ₁ n ≫
        (cylinderHomologyIso G R n).hom =
      (cylinderHomologyIso F R n).hom ≫
        homologyMap (((singularChainComplexFunctor A).obj R).map (TopCat.ofHom g)) n := by
    rw [← Iso.inv_comp_eq, cylinderHomologyIso_inv, cylinderHomologyIso_hom,
      cyclicCoverShortComplexMap_τ₁, ← homologyMap_comp, ← homologyMap_comp, ← Functor.map_comp,
      ← Functor.map_comp]
    congr 2
    ext x
    simpa using hg x
  rw [wangδ, wangδ, ← Category.assoc, ← cyclicCoverShortComplexMap_τ₃ φ R ψ Φ hΦ, ← hδ,
    Category.assoc, hcyl, Category.assoc]

variable (g : C(F, G)) (h : Function.Semiconj g φ ψ)

/-- **Naturality of the Wang connecting morphism.** For a map `g : F → G` intertwining the
monodromies, `g ∘ φ = ψ ∘ g`, the Wang connecting morphisms `Hₙ₊₁(T_φ) ⟶ Hₙ(F)` and
`Hₙ₊₁(T_ψ) ⟶ Hₙ(G)` commute with the induced maps `Hₙ₊₁(T_φ) ⟶ Hₙ₊₁(T_ψ)` and
`Hₙ(F) ⟶ Hₙ(G)`. -/
@[reassoc]
theorem singularHomologyMap_map_comp_wangδ (n : ℕ) :
    ((singularHomologyFunctor A (n + 1)).obj R).map (TopCat.ofHom (map φ ψ g h)) ≫
        wangδ ψ R n =
      wangδ φ R n ≫ ((singularHomologyFunctor A n).obj R).map (TopCat.ofHom g) := by
  rw [← descend_prodMap φ h]
  exact singularHomologyMap_descend_comp_wangδ φ R ψ _ _ g (fun _ ↦ rfl) n

/-- **Naturality of the Wang connecting morphism**, stated with the chain maps induced by the map
of mapping tori and by `g`. -/
@[reassoc]
theorem wangδ_naturality (n : ℕ) :
    wangδ φ R n ≫ homologyMap (fibreChainMap R g) n =
      homologyMap (mappingTorusChainMap φ R ψ g h) (n + 1) ≫ wangδ ψ R n := by
  rw [fibreChainMap_def, mappingTorusChainMap_def, ← descend_prodMap φ h]
  exact (singularHomologyMap_descend_comp_wangδ φ R ψ _ _ g (fun _ ↦ rfl) n).symm

end Naturality

section ModuleCat

variable {k : Type w} [CommRing k]

/-- With coefficients in a module `R`, `𝟙 - φ_*` is a monomorphism on `Hₙ(F; R)` exactly when it is
injective as a linear map. -/
theorem mono_homologyMap_wangEndomorphism_iff (R : ModuleCat.{w} k) (n : ℕ) :
    Mono (homologyMap (wangEndomorphism φ R) n) ↔
      Function.Injective
        (LinearMap.id - (homologyMap (monodromyChainMap φ R) n).hom : _ →ₗ[k] _) := by
  simp [ModuleCat.mono_iff_injective]

/-- The kernel of the map `Hₙ(F) → Hₙ(T_φ)` induced by the fibre inclusion is the image of
`𝟙 - φ_*`. -/
theorem ker_homologyMap_fibreInclusionChainMap (n : ℕ) :
    LinearMap.ker (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) n).hom =
      LinearMap.range
        (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom) := by
  have := (wang_exact₂ φ (ModuleCat.of k k) n).moduleCat_range_eq_ker
  simp only [homologyMap_wangEndomorphism, ModuleCat.hom_sub, ModuleCat.hom_id] at this
  exact this.symm

/-- The image of the map `Hₙ₊₁(F) → Hₙ₊₁(T_φ)` induced by the fibre inclusion is the kernel of
the Wang connecting morphism `Hₙ₊₁(T_φ) → Hₙ(F)`. -/
theorem range_homologyMap_fibreInclusionChainMap (n : ℕ) :
    LinearMap.range (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 1)).hom =
      LinearMap.ker (wangδ φ (ModuleCat.of k k) n).hom :=
  (wang_exact₃ φ (ModuleCat.of k k) n).moduleCat_range_eq_ker

/-- **The Wang cokernel.** The cokernel of `𝟙 - φ_*` on `Hₙ(F)` is isomorphic, through the fibre
inclusion, to the image of `Hₙ(F)` in `Hₙ(T_φ)`. -/
def wangCokernelEquiv (n : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
        (TopCat.of F)).homology n ⧸ LinearMap.range
          (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom)) ≃ₗ[k]
      LinearMap.range (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) n).hom :=
  (Submodule.quotEquivOfEq _ _ (ker_homologyMap_fibreInclusionChainMap φ n).symm).trans
    (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) n).hom.quotKerEquivRange

/-- The Wang cokernel isomorphism sends the class of `x` to the image of `x` under the fibre
inclusion. -/
@[simp]
theorem coe_wangCokernelEquiv_mk (n : ℕ)
    (x : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of F)).homology n) :
    (wangCokernelEquiv φ n (Submodule.Quotient.mk x) : _) =
      (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) n).hom x :=
  (rfl)

/-- **The Wang short complex**
`Hₙ₊₁(F) ⧸ range (𝟙 - φ_*) ⟶ Hₙ₊₁(T_φ) ⟶ Hₙ(F)`: the map induced by the fibre inclusion on the
cokernel of `𝟙 - φ_*`, followed by the Wang connecting morphism. Its objects are exposed so that
`Ext` groups of `Hₙ₊₁(T_φ)` can be stated as `Ext` groups of its middle term. -/
@[expose] def wangCokernelShortComplex (n : ℕ) : ShortComplex (ModuleCat.{w} k) where
  X₁ := ModuleCat.of k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1) ⧸ LinearMap.range
        (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom))
  X₂ := (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)
  X₃ := (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology n
  f := ConcreteCategory.ofHom (Submodule.liftQ _
    (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 1)).hom
    (ker_homologyMap_fibreInclusionChainMap φ (n + 1)).ge)
  g := wangδ φ (ModuleCat.of k k) n
  zero := by
    ext x
    -- On the class of `x` the composite is `wangδ (ι_* x)`, which vanishes as `ι_* ≫ wangδ = 0`.
    simp [← ModuleCat.comp_apply, homologyMap_fibreInclusionChainMap_comp_wangδ]

/-- The first map of the Wang short complex sends the class of `x` to the image of `x` under the
fibre inclusion. -/
@[simp]
theorem wangCokernelShortComplex_f_mk (n : ℕ)
    (x : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of F)).homology (n + 1)) :
    (wangCokernelShortComplex φ n).f.hom (Submodule.Quotient.mk x) =
      (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 1)).hom x :=
  Submodule.liftQ_apply _ _ x

/-- The second map of the Wang short complex is the Wang connecting morphism. -/
@[simp]
theorem wangCokernelShortComplex_g (n : ℕ) :
    (wangCokernelShortComplex (k := k) φ n).g = wangδ φ (ModuleCat.of k k) n :=
  (rfl)

/-- The first map of the Wang short complex is injective: the fibre inclusion kills exactly the
range of `𝟙 - φ_*`. -/
instance mono_wangCokernelShortComplex_f (n : ℕ) : Mono (wangCokernelShortComplex (k := k) φ n).f :=
  (ModuleCat.mono_iff_injective _).2 <| LinearMap.ker_eq_bot.1 <|
    Submodule.ker_liftQ_eq_bot _ _ _ (ker_homologyMap_fibreInclusionChainMap φ (n + 1)).le

/-- **The Wang short exact sequence.** If the Wang connecting morphism `Hₙ₊₁(T_φ) ⟶ Hₙ(F)` is
onto, then `0 ⟶ Hₙ₊₁(F) ⧸ range (𝟙 - φ_*) ⟶ Hₙ₊₁(T_φ) ⟶ Hₙ(F) ⟶ 0` is short exact. -/
theorem wangCokernelShortComplex_shortExact (n : ℕ) [Epi (wangδ φ (ModuleCat.of k k) n)] :
    (wangCokernelShortComplex (k := k) φ n).ShortExact where
  exact := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).2 fun y hy ↦ by
    obtain ⟨x, rfl⟩ := (range_homologyMap_fibreInclusionChainMap φ n).ge hy
    exact ⟨Submodule.Quotient.mk x, wangCokernelShortComplex_f_mk φ n x⟩
  mono_f := inferInstance
  epi_g := by rw [wangCokernelShortComplex_g]; exact ‹Epi (wangδ φ (ModuleCat.of k k) n)›

/-- **The image of the Wang connecting morphism** `Hₙ₊₁(T_φ) ⟶ Hₙ(F)` is the kernel of `𝟙 - φ_*`
on `Hₙ(F)`. -/
theorem range_wangδ (n : ℕ) :
    LinearMap.range (wangδ φ (ModuleCat.of k k) n).hom =
      LinearMap.ker
        (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom) := by
  have := (wang_exact₁ φ (ModuleCat.of k k) n).moduleCat_range_eq_ker
  simpa only [homologyMap_wangEndomorphism, ModuleCat.hom_sub, ModuleCat.hom_id] using this

/-- **The Wang short complex with kernel**
`Hₙ₊₁(F) ⧸ range (𝟙 - φ_*) ⟶ Hₙ₊₁(T_φ) ⟶ ker (𝟙 - φ_*)`: the map induced by the fibre inclusion
on the cokernel of `𝟙 - φ_*` on `Hₙ₊₁(F)`, followed by the Wang connecting morphism, with values
in the kernel of `𝟙 - φ_*` on `Hₙ(F)`. Unlike `TauCeti.MappingTorus.wangCokernelShortComplex`, it
is short exact for every monodromy (`TauCeti.MappingTorus.wangKernelShortComplex_shortExact`). -/
@[expose] def wangKernelShortComplex (n : ℕ) : ShortComplex (ModuleCat.{w} k) where
  X₁ := ModuleCat.of k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1) ⧸ LinearMap.range
        (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom))
  X₂ := (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)
  X₃ := ModuleCat.of k (LinearMap.ker
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom))
  f := (wangCokernelShortComplex φ n).f
  g := ConcreteCategory.ofHom ((wangδ φ (ModuleCat.of k k) n).hom.codRestrict _
    fun y ↦ (range_wangδ φ n).le (LinearMap.mem_range_self _ y))
  zero := by
    ext x
    -- As for `wangCokernelShortComplex`, the composite is `wangδ (ι_* x) = 0`.
    exact (wangCokernelShortComplex φ n).moduleCat_zero_apply (Submodule.Quotient.mk x)

/-- The first map of the Wang short complex with kernel sends the class of `x` to the image of `x`
under the fibre inclusion. -/
@[simp]
theorem wangKernelShortComplex_f_mk (n : ℕ)
    (x : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of F)).homology (n + 1)) :
    (wangKernelShortComplex φ n).f.hom (Submodule.Quotient.mk x) =
      (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 1)).hom x :=
  wangCokernelShortComplex_f_mk φ n x

/-- The second map of the Wang short complex with kernel is the Wang connecting morphism. -/
@[simp]
theorem coe_wangKernelShortComplex_g_apply (n : ℕ)
    (y : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)) :
    Subtype.val ((wangKernelShortComplex φ n).g.hom y) = (wangδ φ (ModuleCat.of k k) n).hom y :=
  (rfl)

/-- **The Wang short exact sequence.** For every monodromy,
`0 ⟶ Hₙ₊₁(F) ⧸ range (𝟙 - φ_*) ⟶ Hₙ₊₁(T_φ) ⟶ ker (𝟙 - φ_*) ⟶ 0` is short exact, with `𝟙 - φ_*`
acting on `Hₙ₊₁(F)` and on `Hₙ(F)` respectively. -/
theorem wangKernelShortComplex_shortExact (n : ℕ) :
    (wangKernelShortComplex (k := k) φ n).ShortExact where
  exact := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).2 fun y hy ↦ by
    obtain ⟨x, rfl⟩ :=
      (range_homologyMap_fibreInclusionChainMap φ n).ge ((LinearMap.ker_codRestrict _ _ _).le hy)
    exact ⟨Submodule.Quotient.mk x, wangKernelShortComplex_f_mk φ n x⟩
  mono_f := mono_wangCokernelShortComplex_f φ n
  epi_g := (ModuleCat.epi_iff_surjective _).2 fun ⟨y, hy⟩ ↦ by
    obtain ⟨x, hx⟩ := (range_wangδ φ n).ge hy
    exact ⟨x, Subtype.ext hx⟩

end ModuleCat

end TauCeti.MappingTorus

end
