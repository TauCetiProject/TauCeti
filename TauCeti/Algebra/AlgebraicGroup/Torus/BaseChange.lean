/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange

/-!
# Base change of tori

Scalar extension preserves both split tori (over arbitrary commutative rings) and general tori
(along arbitrary field extensions). For a torus `H` over `k` and a field extension `K / k`, an
algebraic embedding `AlgebraicClosure k →ₐ[k] AlgebraicClosure K` identifies the geometric fiber
of `K ⊗[k] H` over `AlgebraicClosure K` with the scalar extension of the split torus
`AlgebraicClosure k ⊗[k] H`.

## Main declarations

* `TauCeti.splitTorusCommHopfAlgProperty.baseChange`: scalar extension along a commutative ring
  homomorphism preserves split tori.
* `TauCeti.torusCommHopfAlgProperty.baseChange`: scalar extension along an arbitrary field
  extension preserves tori.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 12.17, p. 244.
-/

public section

namespace TauCeti

universe u

/-- Scalar extension along a commutative ring homomorphism preserves split tori. -/
theorem splitTorusCommHopfAlgProperty.baseChange
    {k K : Type u} [CommRing k] [CommRing K] [Algebra k K]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : splitTorusCommHopfAlgProperty k H) :
    splitTorusCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  obtain ⟨n, ⟨i⟩⟩ := (splitTorusCommHopfAlgProperty_iff k H).mp hH
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨n, ⟨(DiagonalizableGroup.baseChangeCoordinateRingIso k K
      (SplitTorus.characterGroup (ULift.{u} (Fin n)))).symm ≪≫
    (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := K)).mapIso i⟩⟩

/-- Scalar extension along an arbitrary field extension preserves tori. -/
theorem torusCommHopfAlgProperty.baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : torusCommHopfAlgProperty k H) :
    torusCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  let L := AlgebraicClosure K
  let φ : AlgebraicClosure k →ₐ[k] L := IsAlgClosed.lift
  let _ : Algebra (AlgebraicClosure k) L := φ.toAlgebra
  have : IsScalarTower k (AlgebraicClosure k) L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  have hsplit : splitTorusCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
    (splitTorusCommHopfAlgProperty_iff _ _).mpr ((torusCommHopfAlgProperty_iff k H).mp hH)
  let e : FiniteTypeCommHopfAlgCat.baseChange (K := L)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := L)
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) :=
    FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := AlgebraicClosure k) k L H ≪≫
      (FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := K) k L H).symm
  exact (torusCommHopfAlgProperty_iff K _).mpr <|
    (splitTorusCommHopfAlgProperty_iff L _).mp <|
      (splitTorusCommHopfAlgProperty L).prop_of_iso e (hsplit.baseChange (K := L))

end TauCeti
