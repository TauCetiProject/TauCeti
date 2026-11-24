/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import TauCeti.AlgebraicTopology.Spectra.LevelFactorization
public import TauCeti.AlgebraicTopology.Spectra.Stabilization
public import TauCeti.AlgebraicTopology.Spectra.Tensor

import TauCeti.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Ω-spectra and stabilization mapping spaces

A symmetric spectrum `E` is an *Ω-spectrum* when every level `E_n` is a Kan complex and every
adjoint structure map `E_n ⟶ Ω E_(1+n)` is a weak equivalence of simplicial sets.

Using the free-spectrum mapping-space identifications `Map(F_n K, E) ≅ Map_*(K, E_n)`
(`SymmetricSpectrum.mappingSpaceFreeIso`) and `Map(F_n S⁰, E) ≅ E_n`
(`SymmetricSpectrum.mappingSpaceFreeZeroIso`) from `Spectra/MappingSpace.lean`, precomposition along
the stabilization map `freeStabilizationMap n K : F_(1+n)(S¹ ∧ K) ⟶ F_n K` agrees with
`Map_*(K, σ'_n) : Map_*(K, E_n) ⟶ Map_*(K, Ω E_(1+n))`, and for `K = S⁰` with the adjoint
structure map `σ'_n : E_n ⟶ Ω E_(1+n)` itself.

Consequently, `E` is an Ω-spectrum if and only if `E` is level fibrant (`E ⟶ ⊤` is a level
fibration, equivalently every `E_n` is a Kan complex) and every stabilization precomposition
`Map(F_n S⁰, E) ⟶ Map(F_(1+n)(S¹ ∧ S⁰), E)` is a weak equivalence of simplicial sets.

## Main definitions

* `SymmetricSpectrum.IsOmegaSpectrum`: the class of Ω-spectra.

## Main statements

* `SymmetricSpectrum.mappingSpace_freeStabilizationMap_eq`: precomposition along
  `freeStabilizationMap n K` identifies with `Map_*(K, E.smashPowAdjointStructureMap n)`.
* `SymmetricSpectrum.mappingSpace_freeStabilizationMap_unit_eq`: for `K = S⁰`, precomposition along
  `freeStabilizationMap n S⁰` identifies with `E.smashPowAdjointStructureMap n`.
* `SymmetricSpectrum.isOmegaSpectrum_iff_mappingSpace_freeStabilizationMap`: `E` is an Ω-spectrum
  precisely when every level is a Kan complex and precomposition along each
  `freeStabilizationMap n S⁰` is a weak equivalence on `Map(-, E)`.
* `SymmetricSpectrum.isOmegaSpectrum_iff_levelFibrations_and_mappingSpace`: `E` is an Ω-spectrum
  precisely when `E ⟶ ⊤` is a level fibration and precomposition along each
  `freeStabilizationMap n S⁰` is a weak equivalence on `Map(-, E)`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Definitions 1.2.5 and 3.4.3.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Limits HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace TauCeti

namespace SymmetricSpectrum

/-! ### Stabilization precomposition on mapping spaces -/

private lemma smashPowStructureMap_levelSmash_comp_aux (n : ℕ) {K L : PointedSSet.{0}}
    (X E : SymmetricSpectrum) (ι : K ⟶ (evaluation n).obj X)
    (ε : (levelSmash X).obj L ⟶ E) :
    ((PointedSSet.circle ◁ ι ≫ X.smashPowStructureMap n) ▷ L ≫
        SymmetricSequence.tensorFreeZeroι X.X L (1 + n)) ≫
      (evaluation (1 + n)).map ε =
      (α_ PointedSSet.circle K L).hom ≫
        PointedSSet.circle ◁ (ι ▷ L ≫
          SymmetricSequence.tensorFreeZeroι X.X L n ≫ (evaluation n).map ε) ≫
        E.smashPowStructureMap n := by
  have hε : ((levelSmash X).obj L).smashPowStructureMap n ≫ (evaluation (1 + n)).map ε =
      PointedSSet.circle ◁ (evaluation n).map ε ≫ E.smashPowStructureMap n :=
    Mod.smashPowStructureMap_hom ε n
  rw [comp_whiskerRight_assoc, tensorFreeZeroι_comp_levelSmash_smashPowStructureMap,
    Category.assoc, Category.assoc, Category.assoc, associator_naturality_middle_assoc]
  congr 1
  rw [hε, whiskerLeft_comp, whiskerLeft_comp, Category.assoc, Category.assoc]

private lemma evaluation_map_levelSmashRight_comp_aux (n : ℕ) {K L : PointedSSet.{0}}
    {X Y : SymmetricSpectrum} (E : SymmetricSpectrum) (f : X ⟶ Y)
    (ιX : PointedSSet.circle ⊗ K ⟶ (evaluation (1 + n)).obj X)
    (ιY : K ⟶ (evaluation n).obj Y)
    (hι : ιX ≫ (evaluation (1 + n)).map f =
      PointedSSet.circle ◁ ιY ≫ Y.smashPowStructureMap n)
    (ε : (levelSmash Y).obj L ⟶ E) :
    ιX ▷ L ≫ SymmetricSequence.tensorFreeZeroι X.X L (1 + n) ≫
        (evaluation (1 + n)).map ((levelSmashRight L).map f ≫ ε) =
      (α_ PointedSSet.circle K L).hom ≫
        PointedSSet.circle ◁ (ιY ▷ L ≫
          SymmetricSequence.tensorFreeZeroι Y.X L n ≫ (evaluation n).map ε) ≫
        E.smashPowStructureMap n := by
  rw [Functor.map_comp]
  dsimp only [levelSmashRight]
  have hnatL : ιX ▷ L ≫ SymmetricSequence.tensorFreeZeroι X.X L (1 + n) ≫
      (evaluation (1 + n)).map ((Mod.tensorRight ((SymmetricSequence.free 0).obj L)).map f) =
      (ιX ≫ (evaluation (1 + n)).map f) ▷ L ≫ SymmetricSequence.tensorFreeZeroι Y.X L (1 + n) := by
    rw [comp_whiskerRight, Category.assoc]
    congr 1
    exact (SymmetricSequence.tensorFreeZeroι_naturality_left f.hom L (1 + n)).symm
  have h1 : ιX ▷ L ≫ SymmetricSequence.tensorFreeZeroι X.X L (1 + n) ≫
      (evaluation (1 + n)).map ((Mod.tensorRight ((SymmetricSequence.free 0).obj L)).map f) ≫
        (evaluation (1 + n)).map ε =
      ((PointedSSet.circle ◁ ιY ≫ Y.smashPowStructureMap n) ▷ L ≫
        SymmetricSequence.tensorFreeZeroι Y.X L (1 + n)) ≫
      (evaluation (1 + n)).map ε := by
    rw [← Category.assoc _ _ ((evaluation (1 + n)).map ε), ← Category.assoc (ιX ▷ L)]
    congr 1
    rw [hnatL, hι]
  exact h1.trans (smashPowStructureMap_levelSmash_comp_aux n Y E ιY ε)

private lemma freeStabilizationMap_levelSmash_comp (n : ℕ) (K L : PointedSSet.{0})
    (E : SymmetricSpectrum) (ε : (levelSmash ((free n).obj K)).obj L ⟶ E) :
    freeι (1 + n) (PointedSSet.circle ⊗ K) ▷ L ≫
        SymmetricSequence.tensorFreeZeroι ((free (1 + n)).obj (PointedSSet.circle ⊗ K)).X L
          (1 + n) ≫
        (evaluation (1 + n)).map ((levelSmashRight L).map (freeStabilizationMap n K) ≫ ε) =
      (α_ PointedSSet.circle K L).hom ≫
        PointedSSet.circle ◁ (freeι n K ▷ L ≫
          SymmetricSequence.tensorFreeZeroι ((free n).obj K).X L n ≫ (evaluation n).map ε) ≫
        E.smashPowStructureMap n :=
  evaluation_map_levelSmashRight_comp_aux n E (freeStabilizationMap n K)
    (freeι (1 + n) (PointedSSet.circle ⊗ K)) (freeι n K) (freeι_stabilizationMap n K) ε

private lemma homEquiv_levelSmashRight_counit (n : ℕ) (K : PointedSSet.{0})
    (E : SymmetricSpectrum) :
    (levelSmashMappingSpaceAdjunction ((free (1 + n)).obj (PointedSSet.circle ⊗ K))).homEquiv
        ((mappingSpace ((free n).obj K)).obj E) E
        ((levelSmashRight ((mappingSpace ((free n).obj K)).obj E)).map
          (freeStabilizationMap n K) ≫
          (levelSmashMappingSpaceAdjunction ((free n).obj K)).counit.app E) =
      (mappingSpaceBifunctor.map (freeStabilizationMap n K).op).app E := by
  let ε : (levelSmashBifunctor.obj ((free n).obj K)).obj
      ((mappingSpace ((free n).obj K)).obj E) ⟶ E :=
    (levelSmashMappingSpaceAdjunction ((free n).obj K)).counit.app E
  let p : ((mappingSpace ((free n).obj K)).obj E) ⟶
      ((mappingSpace ((free (1 + n)).obj (PointedSSet.circle ⊗ K))).obj E) :=
    (mappingSpaceBifunctor.map (freeStabilizationMap n K).op).app E
  have h := levelSmashMappingSpaceAdjunction₂.homEquiv_naturality_one
    (freeStabilizationMap n K) ε
  dsimp only [ParametrizedAdjunction.homEquiv] at h
  rw [levelSmashMappingSpaceAdjunction₂_adj, levelSmashMappingSpaceAdjunction₂_adj] at h
  -- Express the `levelSmashMappingSpaceAdjunction₂` naturality RHS via `p` and `adj₀.counit.app`.
  change _ = (levelSmashMappingSpaceAdjunction ((free n).obj K)).homEquiv _ E
    ((levelSmashMappingSpaceAdjunction ((free n).obj K)).counit.app E) ≫ p at h
  rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components, Category.id_comp] at h
  exact h

/-- Under `mappingSpaceFreeIso` and `ihomCurryIso`, precomposition along
`freeStabilizationMap n K : F_(1+n)(S¹ ∧ K) ⟶ F_n K` agrees with
`Map_*(K, E.smashPowAdjointStructureMap n)`. -/
theorem mappingSpace_freeStabilizationMap_eq (n : ℕ) (K : PointedSSet.{0})
    (E : SymmetricSpectrum) :
    (mappingSpaceBifunctor.map (freeStabilizationMap n K).op).app E ≫
        (mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ K)).hom.app E ≫
        (MonoidalClosed.ihomCurryIso PointedSSet.circle K ((evaluation (1 + n)).obj E)).hom =
      (mappingSpaceFreeIso n K).hom.app E ≫
        (CategoryTheory.ihom K).map (E.smashPowAdjointStructureMap n) := by
  let L := (mappingSpace ((free n).obj K)).obj E
  let ε : (levelSmash ((free n).obj K)).obj L ⟶ E :=
    (levelSmashMappingSpaceAdjunction ((free n).obj K)).counit.app E
  erw [← Category.assoc, ← homEquiv_levelSmashRight_counit n K E]
  change (((levelSmashMappingSpaceAdjunction _).homEquiv L E _ ≫ _) ≫ _) = _
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_uncurry_comp_ihomCurryIso_hom,
    homEquiv_comp_mappingSpaceFreeIso_hom_app, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_natural_right, uncurry_mappingSpaceFreeIso_hom_app,
    MonoidalClosed.uncurry_natural_left, Mod.uncurry_smashPowAdjointStructureMap,
    ← cancel_epi (α_ PointedSSet.circle K L).hom, Iso.hom_inv_id_assoc]
  exact freeStabilizationMap_levelSmash_comp n K L E ε

/-- For `K = S⁰`, precomposition along `freeStabilizationMap n S⁰` agrees under
`mappingSpaceFreeZeroIso n` and `mappingSpaceFreeIso (1 + n) (S¹ ∧ S⁰)` with the adjoint
structure map `E.smashPowAdjointStructureMap n`. -/
theorem mappingSpace_freeStabilizationMap_unit_eq (n : ℕ) (E : SymmetricSpectrum) :
    (mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E ≫
        (mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
        (MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app ((evaluation (1 + n)).obj E) =
      (mappingSpaceFreeZeroIso n).hom.app E ≫ E.smashPowAdjointStructureMap n := by
  let p : (mappingSpace ((free n).obj (𝟙_ _))).obj E ⟶
      (mappingSpace ((free (1 + n)).obj (PointedSSet.circle ⊗ 𝟙_ _))).obj E :=
    (mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E
  -- Expose `(mappingSpaceBifunctor.map ...).app E` as `p` so
  -- `mappingSpace_freeStabilizationMap_eq` matches.
  change p ≫ _ = _
  have h : p ≫ (mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
      (MonoidalClosed.ihomCurryIso PointedSSet.circle (𝟙_ _) ((evaluation (1 + n)).obj E)).hom =
      (mappingSpaceFreeIso n (𝟙_ _)).hom.app E ≫
        (CategoryTheory.ihom (𝟙_ _)).map (E.smashPowAdjointStructureMap n) :=
    mappingSpace_freeStabilizationMap_eq n (𝟙_ _) E
  have h' := congrArg
    (· ≫ MonoidalClosed.unitNatIso.inv.app
      ((CategoryTheory.ihom PointedSSet.circle).obj ((evaluation (1 + n)).obj E))) h
  simp only [Category.assoc] at h'
  rw [MonoidalClosed.ihomCurryIso_hom_comp_unitNatIso_inv] at h'
  refine h'.trans ?_
  rw [mappingSpaceFreeZeroIso_hom_app]
  simp only [Category.assoc, MonoidalClosed.unitNatIso.inv.naturality, Functor.id_map]

/-! ### Ω-spectra -/

/-- A symmetric spectrum `E` is an *Ω-spectrum* when every level `E_n` is a Kan complex and every
adjoint structure map `σ'_n : E_n ⟶ Ω E_(1+n)` is a weak equivalence of simplicial sets. -/
@[mk_iff]
class IsOmegaSpectrum (E : SymmetricSpectrum) : Prop where
  kanComplex : ∀ n, SSet.KanComplex ((evaluation n).obj E).right
  weakEquivalence_adjointStructureMap :
    ∀ n, WeakEquivalence (E.smashPowAdjointStructureMap n).right

attribute [instance] IsOmegaSpectrum.kanComplex

/-- A symmetric spectrum `E` is an Ω-spectrum if and only if every level `E_n` is a Kan complex
and precomposition along every stabilization map `freeStabilizationMap n S⁰` is a weak
equivalence on `Map(-, E)`. -/
theorem isOmegaSpectrum_iff_mappingSpace_freeStabilizationMap (E : SymmetricSpectrum) :
    IsOmegaSpectrum E ↔
      (∀ n, SSet.KanComplex ((evaluation n).obj E).right) ∧
        ∀ n, WeakEquivalence
          ((mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E).right := by
  rw [isOmegaSpectrum_iff]
  refine and_congr_right fun _ ↦ forall_congr' fun n ↦ ?_
  have : IsIso ((MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app
      ((evaluation (1 + n)).obj E)) :=
    Iso.isIso_hom ((MonoidalClosed.internalHom.mapIso (ρ_ PointedSSet.circle).symm.op).app
      ((evaluation (1 + n)).obj E))
  let f : ((mappingSpace ((free n).obj (𝟙_ _))).obj E).right ⟶
      ((mappingSpace ((free (1 + n)).obj (PointedSSet.circle ⊗ 𝟙_ _))).obj E).right :=
    ((mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E).right
  let e₀ : ((mappingSpace ((free n).obj (𝟙_ _))).obj E).right ⟶ ((evaluation n).obj E).right :=
    ((mappingSpaceFreeZeroIso n).hom.app E).right
  let e₁ : ((mappingSpace ((free (1 + n)).obj (PointedSSet.circle ⊗ 𝟙_ _))).obj E).right ⟶
      ((CategoryTheory.ihom PointedSSet.circle).obj ((evaluation (1 + n)).obj E)).right :=
    ((mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
      (MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app ((evaluation (1 + n)).obj E)).right
  have heq : f ≫ e₁ = e₀ ≫ (E.smashPowAdjointStructureMap n).right :=
    congrArg PointedSSet.forgetBasepoint.map (mappingSpace_freeStabilizationMap_unit_eq n E)
  have : IsIso e₀ :=
    Functor.map_isIso PointedSSet.forgetBasepoint ((mappingSpaceFreeZeroIso n).hom.app E)
  have : IsIso e₁ :=
    Functor.map_isIso PointedSSet.forgetBasepoint
      ((mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
        (MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app ((evaluation (1 + n)).obj E))
  -- Fold the mapping-space precomposition map into `f` so `cancel_right_of_respectsIso` applies.
  change WeakEquivalence (E.smashPowAdjointStructureMap n).right ↔ WeakEquivalence f
  simp only [HomotopicalAlgebra.weakEquivalence_iff]
  have h1 : (weakEquivalences SSet.{0}) (E.smashPowAdjointStructureMap n).right ↔
      (weakEquivalences SSet.{0}) (e₀ ≫ (E.smashPowAdjointStructureMap n).right) :=
    ((weakEquivalences SSet.{0}).cancel_left_of_respectsIso e₀ _).symm
  have h2 : (weakEquivalences SSet.{0}) (f ≫ e₁) ↔ (weakEquivalences SSet.{0}) f :=
    (weakEquivalences SSet.{0}).cancel_right_of_respectsIso f e₁
  rw [h1, ← heq, h2]

/-- A symmetric spectrum `E` is an Ω-spectrum if and only if `E ⟶ ⊤` is a level fibration and
precomposition along every stabilization map `freeStabilizationMap n S⁰` is a weak equivalence
on `Map(-, E)`. -/
theorem isOmegaSpectrum_iff_levelFibrations_and_mappingSpace (E : SymmetricSpectrum) :
    IsOmegaSpectrum E ↔
      levelFibrations (terminal.from E) ∧
        ∀ n, WeakEquivalence
          ((mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E).right := by
  rw [isOmegaSpectrum_iff_mappingSpace_freeStabilizationMap, levelFibrations_terminal_from_iff]

end SymmetricSpectrum

end TauCeti
