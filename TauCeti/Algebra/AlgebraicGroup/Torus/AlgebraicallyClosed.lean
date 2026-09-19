/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange

/-!
# Tori over algebraically closed fields

Every torus over an algebraically closed field is split. This identifies the geometric torus
predicate with its split counterpart, so results proved for split tori apply to all tori over
such a field. In particular, it removes the splitting assumption from conjugacy of maximal
tori in general linear groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- Every torus over an algebraically closed field is split. -/
@[grind →]
theorem torusCommHopfAlgProperty.split
    (k : Type u) [Field k] [IsAlgClosed k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) : splitTorusCommHopfAlgProperty k H := by
  obtain ⟨n, ⟨i⟩⟩ := (torusCommHopfAlgProperty_iff k H).mp hH
  let e : k ≃ₐ[k] AlgebraicClosure k :=
    AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  let : Algebra (AlgebraicClosure k) k := e.symm.toRingHom.toAlgebra
  have : IsScalarTower k (AlgebraicClosure k) k :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (e.symm.commutes x).symm
  let G := SplitTorus.characterGroup (ULift.{u} (Fin n))
  let j : FiniteTypeCommHopfAlgCat.baseChange (K := k) H ≅ H :=
    ObjectProperty.isoMk _ (_root_.CommHopfAlgCat.isoMk
      (_root_.Bialgebra.TensorProduct.lid k H.obj))
  refine (splitTorusCommHopfAlgProperty_iff k H).mpr ⟨n, ⟨?_⟩⟩
  exact (DiagonalizableGroup.baseChangeCoordinateRingIso (AlgebraicClosure k) k G).symm ≪≫
    (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := k)).mapIso i ≪≫
    ObjectProperty.isoMk _ (CommHopfAlgCat.baseChangeTowerIso k k H.obj) ≪≫ j

/-- Over an algebraically closed field, the torus and split-torus predicates coincide. -/
theorem torusCommHopfAlgProperty_iff_split
    (k : Type u) [Field k] [IsAlgClosed k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    torusCommHopfAlgProperty k H ↔ splitTorusCommHopfAlgProperty k H :=
  ⟨torusCommHopfAlgProperty.split k H, splitTorusCommHopfAlgProperty.torus k H⟩

end TauCeti
