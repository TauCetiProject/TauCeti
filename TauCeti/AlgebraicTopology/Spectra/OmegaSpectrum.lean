/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Spectra.LevelFactorization
public import TauCeti.AlgebraicTopology.Spectra.Stabilization

/-!
# Ω-spectra and stabilization mapping spaces

A symmetric spectrum `E` is an *Ω-spectrum* when every level `E_n` is a Kan complex and every
adjoint structure map `E_n ⟶ Ω E_(1+n)` is a weak equivalence of simplicial sets.

Using the identification `SymmetricSpectrum.mappingSpace_freeStabilizationMap_unit_eq` from
`Spectra/Stabilization.lean`, precomposition along `freeStabilizationMap n S⁰` identifies with
the adjoint structure map `σ'_n : E_n ⟶ Ω E_(1+n)` itself. Consequently, `E` is an Ω-spectrum if
and only if `E` is level fibrant (`E ⟶ ⊤` is a level fibration, equivalently every `E_n` is a Kan
complex) and every stabilization precomposition `Map(F_n S⁰, E) ⟶ Map(F_(1+n)(S¹ ∧ S⁰), E)` is a
weak equivalence of simplicial sets.

## Main definitions

* `SymmetricSpectrum.IsOmegaSpectrum`: the class of Ω-spectra.

## Main statements

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

/-! ### Ω-spectra -/

/-- A symmetric spectrum `E` is an *Ω-spectrum* when every level `E_n` is a Kan complex and every
adjoint structure map `σ'_n : E_n ⟶ Ω E_(1+n)` is a weak equivalence of simplicial sets. -/
@[mk_iff]
class IsOmegaSpectrum (E : SymmetricSpectrum) : Prop where
  kanComplex : ∀ n, SSet.KanComplex ((evaluation n).obj E).right
  weakEquivalence_adjointStructureMap :
    ∀ n, WeakEquivalence (E.smashPowAdjointStructureMap n).right

attribute [instance] IsOmegaSpectrum.kanComplex
  IsOmegaSpectrum.weakEquivalence_adjointStructureMap

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
  have heq :
      ((mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E).right ≫
        ((mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
          (MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app ((evaluation (1 + n)).obj E)).right =
      ((mappingSpaceFreeZeroIso n).hom.app E).right ≫
        (E.smashPowAdjointStructureMap n).right :=
    congrArg PointedSSet.forgetBasepoint.map (mappingSpace_freeStabilizationMap_unit_eq n E)
  have hIso0 : IsIso ((mappingSpaceFreeZeroIso n).hom.app E).right :=
    Functor.map_isIso PointedSSet.forgetBasepoint ((mappingSpaceFreeZeroIso n).hom.app E)
  have hIso1 :
      IsIso (((mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
        (MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app ((evaluation (1 + n)).obj E)).right) :=
    Functor.map_isIso PointedSSet.forgetBasepoint
      ((mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
        (MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app ((evaluation (1 + n)).obj E))
  simp only [HomotopicalAlgebra.weakEquivalence_iff]
  rw [← (weakEquivalences SSet.{0}).cancel_left_of_respectsIso
    ((mappingSpaceFreeZeroIso n).hom.app E).right, ← heq]
  exact @MorphismProperty.cancel_right_of_respectsIso _ _ (weakEquivalences SSet.{0}) _ _ _ _ _ _
    hIso1

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
