/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.InvariantDerivation
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
public import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.Exponential
import TauCeti.Algebra.AlgebraicGroup.Representation.Kernel
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# Tangent matrices of representations

Differentiating a representation's coordinate morphism differentiates its coefficient matrix
entrywise. For an upper-unitriangular coefficient matrix, the tangent matrix is strictly upper
triangular and hence nilpotent. If the coordinate morphism is also surjective, local nilpotence
of the invariant derivation descends from the general-linear coordinate algebra, whether nilpotence
comes from an upper-unitriangular coefficient matrix or directly from nilpotence of the
differentiated comodule action. More generally, when the coordinate bialgebra is projective as a
module over the base ring, nilpotence of the differentiated action on every finitely generated
comodule suffices for local nilpotence of the left-invariant derivation.

These statements work over arbitrary commutative base rings. Tangent matrix entries may take
values in any commutative coefficient algebra. No reducedness or characteristic assumption is
needed.

## Main declarations

* `TauCeti.Comodule.differential_fgComoduleCatOf`: the differentiated action on `FGComoduleCat.of M`
  agrees with the differentiated action on `M`.
* `Derivation.tangentMatrix_derivationComp_coordinateBialgHom_apply`: tangent matrix entries
  are derivatives of coefficient-matrix entries.
* `tangentMatrix_derivationComp_coordinateBialgHom_apply_eq_zero_of_isUpperUnitriangular` in
  `Derivation`: the tangent matrix of an upper-unitriangular representation is strictly upper
  triangular.
* `Derivation.isNilpotent_tangentMatrix_derivationComp_coordinateBialgHom_of_isUpperUnitriangular`:
  that tangent matrix is nilpotent.
* `Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_isUpperUnitriangular`:
  a faithful upper-unitriangular representation gives locally nilpotent invariant derivations.
* `Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential`:
  a surjective coordinate representation with nilpotent differentiated action makes the invariant
  derivation locally nilpotent.
* `Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_forall_fgComodule`:
  on a projective bialgebra, nilpotence of the differentiated action on every finitely generated
  comodule makes the left-invariant derivation locally nilpotent.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 14.
-/

public section

namespace TauCeti.Comodule

universe u v w

/-- The differentiated action on `FGComoduleCat.of M` agrees as a linear endomorphism with the
differentiated action on `M`, even though `FGComoduleCat.of M` reconstructs its additive group from
its module structure. -/
@[simp]
theorem differential_fgComoduleCatOf
    {R : Type u} {H : Type v} {M : Type w} [CommRing R] [CommRing H] [Bialgebra R H]
    [AddCommGroup M] [Module R M] [Comodule R H M] [Module.Finite R M]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) :
    @differential R H (FGComoduleCat.of (R := R) (C := H) M) _ _ _
        (FGComoduleCat.instAddCommGroupCarrier _) _ _ d =
      differential (R := R) (H := H) (M := M) d := by
  ext m
  simp [differential_apply]

end TauCeti.Comodule

namespace Derivation

open TauCeti

section Monoid

variable {R H M B : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M] [CommRing B] [Algebra R B] {n : ℕ}

/-- Differentiating a representation's coordinate morphism differentiates each entry of its
coefficient matrix, with values in any commutative coefficient algebra. -/
-- The generic tangent-matrix and derivation computation rules already simplify its left side.
theorem tangentMatrix_derivationComp_coordinateBialgHom_apply
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) (b : Module.Basis (Fin n) R M)
    (i j : Fin n) :
    GeneralLinear.tangentMatrix n
        (derivationComp (Comodule.coordinateBialgHom (H := H) b) d) i j =
      Bialgebra.CounitAlgebra.algEquivSelf R H B (d (Comodule.coefficientMatrix b i j)) := by
  rw [GeneralLinear.tangentMatrix_apply, algEquivSelf_derivationComp_apply]
  -- The coordinate formula uses the bialgebra-hom coercion rather than its algebra-hom coercion.
  exact congrArg (fun h ↦ Bialgebra.CounitAlgebra.algEquivSelf R H B (d h))
    (Comodule.coordinateBialgHom_X b i j)

/-- Differentiating an upper-unitriangular representation gives zero entries on and below the
matrix diagonal, over any commutative coefficient algebra. -/
theorem tangentMatrix_derivationComp_coordinateBialgHom_apply_eq_zero_of_isUpperUnitriangular
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) (b : Module.Basis (Fin n) R M)
    (hb : (Comodule.coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (i j : Fin n) (hji : j ≤ i) :
    GeneralLinear.tangentMatrix n
      (derivationComp (Comodule.coordinateBialgHom (H := H) b) d) i j = 0 := by
  rw [d.tangentMatrix_derivationComp_coordinateBialgHom_apply b]
  rcases eq_or_lt_of_le hji with rfl | hji
  · rw [hb.apply_diag, d.map_one_eq_zero, map_zero]
  · rw [hb.isUpperTriangular hji, map_zero, map_zero]

/-- Differentiating an upper-unitriangular representation gives a nilpotent matrix over
any commutative coefficient algebra. No characteristic or reducedness assumption is needed. -/
theorem isNilpotent_tangentMatrix_derivationComp_coordinateBialgHom_of_isUpperUnitriangular
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) (b : Module.Basis (Fin n) R M)
    (hb : (Comodule.coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    IsNilpotent (GeneralLinear.tangentMatrix n
      (derivationComp (Comodule.coordinateBialgHom (H := H) b) d)) := by
  have hzero :=
    d.tangentMatrix_derivationComp_coordinateBialgHom_apply_eq_zero_of_isUpperUnitriangular b hb
  exact Matrix.isNilpotent_of_isUpperTriangular_of_diag_eq_zero
    (fun _ _ hji ↦ hzero _ _ hji.le) (fun i ↦ hzero i i le_rfl)

/-- A faithful upper-unitriangular representation makes every invariant tangent derivation
locally nilpotent on the coordinate ring, over any commutative base ring. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_isUpperUnitriangular
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M)
    (hb : (Comodule.coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (hf : Function.Surjective (Comodule.coordinateBialgHom (H := H) b)) :
    ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 :=
  BialgHom.exists_iterate_leftInvariantDerivation_eq_zero_of_surjective
    (Comodule.coordinateBialgHom (H := H) b) hf d
    (GeneralLinear.exists_iterate_leftInvariantDerivation_eq_zero n _
      (d.isNilpotent_tangentMatrix_derivationComp_coordinateBialgHom_of_isUpperUnitriangular b hb))

end Monoid

section Differential

section FGComodule

universe u v

/-- If `H` is projective as an `R`-module (for instance whenever `R` is a field, without any
finite-type assumption on `H`) and `d` acts nilpotently on every finitely generated `H`-comodule,
then the left-invariant derivation of `d` is locally nilpotent on `H`. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_forall_fgComodule
    {R : Type u} {H : Type v} [CommRing R] [CommRing H] [Bialgebra R H] [Module.Projective R H]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hdiff : ∀ M : FGComoduleCat.{u, v, v} R H,
      IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d)) :
    ∀ h : H, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 := by
  intro h
  obtain ⟨W, hWfin, hh⟩ := Subcomodule.exists_finite_subcomodule_mem (R := R) (C := H) h
  let _ : Module.Finite R W := hWfin
  have hm : IsNilpotent (Comodule.differential (R := R) (H := H) (M := W) d) := by
    simpa using hdiff (FGComoduleCat.of (R := R) (C := H) W)
  obtain ⟨m, hm⟩ := hm
  refine ⟨m, ?_⟩
  have hsemi : Function.Semiconj W.subtype
      (Comodule.differential (R := R) (H := H) (M := W) d)
      (Bialgebra.leftInvariantDerivation d) := fun w => by
    rw [W.subtype.map_differential d w, ← Derivation.coeFn_coe,
      Bialgebra.toLinearMap_leftInvariantDerivation]
  have hm0 : (⇑(Comodule.differential (R := R) (H := H) (M := W) d))^[m] ⟨h, hh⟩ = 0 := by
    simpa [pow_apply_eq_iterate] using LinearMap.congr_fun hm ⟨h, hh⟩
  have hiter := (hsemi.iterate_right m ⟨h, hh⟩).symm
  rwa [W.subtype_apply, Subtype.coe_mk, hm0, map_zero] at hiter

end FGComodule

variable {R H M : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M] {n : ℕ}

/-- **Nilpotence in a faithful representation forces local nilpotence of the invariant derivation.**
If the coordinate map of a finite basis `b` is surjective and `Comodule.differential d` is
nilpotent on `M`, then `Bialgebra.leftInvariantDerivation d` is locally nilpotent on `H`. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M)
    (hf : Function.Surjective (Comodule.coordinateBialgHom (H := H) b))
    (hd : IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d)) :
    ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 := by
  refine BialgHom.exists_iterate_leftInvariantDerivation_eq_zero_of_surjective
    (Comodule.coordinateBialgHom (H := H) b) hf d
    (GeneralLinear.exists_iterate_leftInvariantDerivation_eq_zero n _ ?_)
  rw [d.tangentMatrix_comp_coordinateBialgHom b]
  exact hd.map (LinearMap.toMatrixAlgEquiv b).toRingHom

end Differential

end Derivation
