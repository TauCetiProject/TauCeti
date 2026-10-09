/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Scalar
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BaseChange
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Connected
import TauCeti.Algebra.AlgebraicGroup.Representation.ClosedSubgroup
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The special linear group is semisimple

The group `SL_n` is semisimple over every field, including in characteristics dividing `n`.
A connected smooth normal solvable subgroup acts by scalars on the simple standard
representation. Determinant one restricts those scalars to the finite set of `n`th roots
of unity. A regular function with finite image on a reduced connected affine scheme is
constant, so the subgroup acts trivially. Faithfulness of the standard representation
identifies its defining ideal with the augmentation ideal.

The argument is `HopfIdeal.eq_augmentation_of_isFaithful_of_isNormal_of_isSolvable_of_pow_eq_one`
applied to the standard special-linear comodule. Reducedness of the subgroup is needed: this
does not assert triviality of nonreduced connected central subgroup schemes such as `μ_p` in
`SL_p`. The zero-rank case uses the faithful zero-dimensional representation separately.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 27.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 21.
-/

public section

namespace TauCeti.SpecialLinear

open CategoryTheory WithConv
open scoped TensorProduct Matrix

universe u

noncomputable section

attribute [local instance] standardComodule

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every connected reduced normal solvable closed subgroup of `SL_n` over an algebraically
closed field is trivial. Reducedness may be supplied by smoothness, but is the only subgroup
regularity needed here. -/
theorem eq_augmentation_of_isNormal_of_isSolvable
    (n : ℕ) (I : HopfIdeal k (coordinateHopfAlgebra k n)) (hI : I.IsNormal)
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    [ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I))]
    [Group.IsSolvable (WithConv
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I →ₐ[k] k))] :
    I = HopfIdeal.augmentation k (coordinateHopfAlgebra k n) := by
  cases n with
  | zero =>
    exact Comodule.eq_augmentation_of_isFaithful_of_subsingleton (M := Fin 0 → k) I
      (isFaithful_standardComodule k 0)
  | succ m =>
    let H := coordinateHopfAlgebra k (m + 1)
    let _ : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
    let _ : IsReduced H := isReduced_of_smooth k H
    let _ : ConnectedSpace (PrimeSpectrum H) :=
      geometricallyConnectedCommHopfAlgProperty.connectedSpace k H
        (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k (m + 1))
    -- Determinant one confines the scalars to `(m + 1)`-th roots of unity.
    exact HopfIdeal.eq_augmentation_of_isFaithful_of_isNormal_of_isSolvable_of_pow_eq_one
      (V := Fin (m + 1) → k) I hI (isFaithful_standardComodule k (m + 1)) (Nat.succ_pos m)
      fun g c hc ↦ scalar_pow_eq_one_of_basePointsRepresentation_eq_smul _ c hc

/-- **The special linear group is semisimple over every field and in every rank.** -/
theorem semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] (n : ℕ) :
    semisimpleCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k n) := by
  have hred := reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k n
  let K := AlgebraicClosure k
  let B := FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra k n)
  let G := coordinateHopfAlgebra K n
  let e : B.obj ≅ G :=
    (forget₂ (FiniteTypeCommHopfAlgCat K) (_root_.CommHopfAlgCat K)).mapIso
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso k K n) ≪≫
        eqToIso (finiteTypeCoordinateHopfAlgebra_obj K n)
  apply semisimpleCommHopfAlgProperty_of_geometricFiber_iso k _ G
    hred.smooth hred.geometricallyConnected e
  intro I hnormal hconnected hsmooth hsolvable
  let _ : Algebra.Smooth K (CommHopfAlgCat.quotient G I) := hsmooth
  let _ : IsReduced (CommHopfAlgCat.quotient G I) := isReduced_of_smooth K _
  let _ : ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient G I)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace K _ hconnected
  let _ : Group.IsSolvable
      (WithConv (CommHopfAlgCat.quotient G I →ₐ[K] AlgebraicClosure K)) :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff K _).mp hsolvable
  let φ : K →ₐ[K] AlgebraicClosure K := Algebra.ofId K (AlgebraicClosure K)
  let _ : Group.IsSolvable (WithConv (CommHopfAlgCat.quotient G I →ₐ[K] K)) :=
    Group.isSolvable_of_isSolvable_injective (AlgHom.mapValue_injective φ.injective)
  exact eq_augmentation_of_isNormal_of_isSolvable n I hnormal

end

end TauCeti.SpecialLinear
