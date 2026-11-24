/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.Projective
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.LinearAlgebra.SymmetricAlgebra.FiniteType
import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
import TauCeti.LinearAlgebra.SymmetricAlgebra.Kaehler
import TauCeti.RingTheory.Smooth.Retract

/-!
# Formal smoothness and smoothness of symmetric algebras

For a commutative ring `R` and an `R`-module `M`, the symmetric algebra `SymmetricAlgebra R M` is:
* formally smooth over `R` if and only if `M` is projective (`formallySmooth_iff`);
* smooth over `R` if and only if `M` is finite projective (`smooth_iff`).

Sufficiency uses functoriality of `SymmetricAlgebra`: a projective module is a direct summand of a
free module `F`, making `SymmetricAlgebra R M` an `R`-algebra retract of the polynomial algebra
`SymmetricAlgebra R F` (`Algebra.FormallySmooth.of_retract`); when `M` is also finite it is finitely
presented (`Module.finitePresentation_of_projective`), giving finite presentation of
`SymmetricAlgebra R M` (`TauCeti.SymmetricAlgebra.instFinitePresentation`).

Necessity uses `SymmetricAlgebra.kaehlerDifferentialEquiv` (`Ω[Sym M⁄R] ≃ Sym M ⊗[R] M`)
together with base change along the augmentation `SymmetricAlgebra.algebraMapInv : Sym M →ₐ[R] R` to
descend projectivity (`Module.Projective.tensorProduct`) and finiteness
(`Module.Finite.base_change`) of `Ω[Sym M⁄R]` over `Sym M` back to `M` over `R`.

## Main declarations

* `TauCeti.SymmetricAlgebra.instFormallySmooth`: `SymmetricAlgebra R M` is formally smooth over `R`
  when `M` is projective.
* `TauCeti.SymmetricAlgebra.instSmooth`: `SymmetricAlgebra R M` is smooth over `R` when `M` is
  finite projective.
* `TauCeti.SymmetricAlgebra.formallySmooth_iff`: `SymmetricAlgebra R M` is formally smooth over `R`
  iff `M` is projective over `R`.
* `TauCeti.SymmetricAlgebra.smooth_iff`: `SymmetricAlgebra R M` is smooth over `R` iff `M` is
  projective and finite over `R`.
-/

public section

open TensorProduct

namespace TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- The symmetric algebra of a projective module is formally smooth: it is an `R`-algebra retract
of the symmetric algebra of a free module, which is a polynomial algebra. -/
instance instFormallySmooth [Module.Projective R M] :
    Algebra.FormallySmooth R (SymmetricAlgebra R M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective R M›
  let b := Finsupp.basisSingleOne (R := R) (ι := M)
  have : Algebra.FormallySmooth R (SymmetricAlgebra R (M →₀ R)) :=
    .of_equiv (_root_.SymmetricAlgebra.equivMvPolynomial b).symm
  refine Algebra.FormallySmooth.of_retract
    (_root_.SymmetricAlgebra.map R s)
    (_root_.SymmetricAlgebra.map R (Finsupp.linearCombination R id)) ?_
  rw [_root_.SymmetricAlgebra.map_comp_map, hs, _root_.SymmetricAlgebra.map_id]

/-- The symmetric algebra of a finite projective module is smooth: it is formally smooth as a
retract of a polynomial algebra and finitely presented because finite projective modules are
finitely presented. -/
instance instSmooth [Module.Projective R M] [Module.Finite R M] :
    Algebra.Smooth R (SymmetricAlgebra R M) :=
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  ⟨inferInstance, inferInstance⟩

/-- Base change of `Ω[SymmetricAlgebra R M⁄R]` along the augmentation
`SymmetricAlgebra.algebraMapInv : SymmetricAlgebra R M →ₐ[R] R` recovers `M`. -/
private noncomputable def augKaehlerEquiv :
    letI : Algebra (SymmetricAlgebra R M) R :=
      (_root_.SymmetricAlgebra.algebraMapInv (R := R) (M := M)).toRingHom.toAlgebra
    R ⊗[SymmetricAlgebra R M] Ω[SymmetricAlgebra R M⁄R] ≃ₗ[R] M :=
  letI : Algebra (SymmetricAlgebra R M) R :=
    (_root_.SymmetricAlgebra.algebraMapInv (R := R) (M := M)).toRingHom.toAlgebra
  haveI : IsScalarTower R (SymmetricAlgebra R M) R :=
    .of_algebraMap_eq fun r ↦ (_root_.SymmetricAlgebra.algebraMap_leftInverse M r).symm
  LinearEquiv.baseChange (SymmetricAlgebra R M) R _ _
      (_root_.SymmetricAlgebra.kaehlerDifferentialEquiv R M) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R (SymmetricAlgebra R M) R R M ≪≫ₗ
    TensorProduct.lid R M

/-- `SymmetricAlgebra R M` is formally smooth over `R` if and only if `M` is projective over `R`. -/
theorem formallySmooth_iff :
    Algebra.FormallySmooth R (SymmetricAlgebra R M) ↔ Module.Projective R M := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  let : Algebra (SymmetricAlgebra R M) R :=
    (_root_.SymmetricAlgebra.algebraMapInv (R := R) (M := M)).toRingHom.toAlgebra
  exact .of_equiv (augKaehlerEquiv R M)

/-- `SymmetricAlgebra R M` is smooth over `R` if and only if `M` is projective and finite over
`R`. -/
theorem smooth_iff :
    Algebra.Smooth R (SymmetricAlgebra R M) ↔ Module.Projective R M ∧ Module.Finite R M := by
  refine ⟨fun h ↦ ⟨(formallySmooth_iff R M).mp h.formallySmooth, ?_⟩, fun ⟨_, _⟩ ↦ inferInstance⟩
  let : Algebra (SymmetricAlgebra R M) R :=
    (_root_.SymmetricAlgebra.algebraMapInv (R := R) (M := M)).toRingHom.toAlgebra
  exact .equiv (augKaehlerEquiv R M)

end TauCeti.SymmetricAlgebra
