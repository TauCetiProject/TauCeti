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

* `SymmetricSpectrum.isOmegaSpectrum_iff_of_iso`: being an Ω-spectrum is invariant under
  isomorphism of symmetric spectra.
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

/-- Being an Ω-spectrum is invariant under isomorphism of symmetric spectra. -/
theorem isOmegaSpectrum_iff_of_iso {E F : SymmetricSpectrum} (e : E ≅ F) :
    IsOmegaSpectrum E ↔ IsOmegaSpectrum F := by
  rw [isOmegaSpectrum_iff, isOmegaSpectrum_iff]
  refine and_congr ?_ (forall_congr' fun n ↦ ?_)
  · simp only [← levelFibrations_terminal_from_iff]
    rw [← terminal.comp_from e.hom, levelFibrations.cancel_left_of_respectsIso]
  · have hnat :
        (PointedSSet.forgetBasepoint.mapIso ((evaluation n).mapIso e)).hom ≫
            (F.smashPowAdjointStructureMap n).right =
          (E.smashPowAdjointStructureMap n).right ≫
            (PointedSSet.forgetBasepoint.mapIso
              ((CategoryTheory.ihom PointedSSet.circle).mapIso
                ((evaluation (1 + n)).mapIso e))).hom := by
      rw [Functor.mapIso_hom, Functor.mapIso_hom, Functor.mapIso_hom, Functor.mapIso_hom]
      exact (congrArg PointedSSet.forgetBasepoint.map
        (Mod.smashPowAdjointStructureMap_hom e.hom n)).symm
    let a : Arrow.mk (E.smashPowAdjointStructureMap n).right ≅
        Arrow.mk (F.smashPowAdjointStructureMap n).right :=
      Arrow.isoMk' _ _
        (PointedSSet.forgetBasepoint.mapIso ((evaluation n).mapIso e))
        (PointedSSet.forgetBasepoint.mapIso
          ((CategoryTheory.ihom PointedSSet.circle).mapIso ((evaluation (1 + n)).mapIso e)))
        hnat
    simpa only [HomotopicalAlgebra.weakEquivalence_iff] using
      (weakEquivalences SSet.{0}).arrow_mk_iso_iff a

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
  have heq :
      ((mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E).right ≫
        ((mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
          (MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app ((evaluation (1 + n)).obj E)).right =
      ((mappingSpaceFreeZeroIso n).hom.app E).right ≫
        (E.smashPowAdjointStructureMap n).right :=
    congrArg PointedSSet.forgetBasepoint.map (mappingSpace_freeStabilizationMap_unit_eq n E)
  let e :
      Arrow.mk ((mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E).right ≅
        Arrow.mk (E.smashPowAdjointStructureMap n).right :=
    Arrow.isoMk' _ _
      (PointedSSet.forgetBasepoint.mapIso ((mappingSpaceFreeZeroIso n).app E))
      (PointedSSet.forgetBasepoint.mapIso
        ((mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).app E ≪≫
          (MonoidalClosed.internalHom.mapIso (ρ_ PointedSSet.circle).symm.op).app
            ((evaluation (1 + n)).obj E)))
      heq.symm
  simpa only [HomotopicalAlgebra.weakEquivalence_iff] using
    ((weakEquivalences SSet.{0}).arrow_mk_iso_iff e).symm

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
