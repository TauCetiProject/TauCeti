/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.MonoidAlgebra.Reduced
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Geometric connectedness, reducedness and smoothness of diagonalizable groups

The coordinate ring of a diagonalizable group is a group algebra. When its character group has
the unique-product property, this group algebra is a domain over every field, so it is reduced and
has connected prime spectrum. In particular, this applies to the finite-rank free character group
of every split torus.

Geometric reducedness has an exact criterion: over a field of exponential characteristic `p`, the
group algebra of a commutative group is geometrically reduced precisely when the group has no
`p`-torsion. When the group is finitely generated, the coordinate ring of the diagonalizable
group is of finite type, so the same condition characterizes its smoothness.

## Main declarations

* `TauCeti.DiagonalizableGroup.connectedSpace_primeSpectrum_coordinateRing`: a diagonalizable
  coordinate ring that is a domain has connected prime spectrum.
* `TauCeti.DiagonalizableGroup.connectedSpace_primeSpectrum_baseChange_coordinateRing`:
  the base-changed coordinate ring has connected prime spectrum when `K[G]` is a domain.
* `TauCeti.DiagonalizableGroup.geometricallyConnected_coordinateRing`: the coordinate ring of a
  unique-product diagonalizable group is geometrically connected.
* `TauCeti.DiagonalizableGroup.geometricallyReduced_coordinateRing`: the coordinate ring of a
  unique-product diagonalizable group is geometrically reduced.
* `TauCeti.DiagonalizableGroup.geometricallyReduced_monoidAlgebra_iff`: the group algebra of a
  commutative group is geometrically reduced exactly when the group has no `p`-torsion, for `p`
  the exponential characteristic of the base field.
* `TauCeti.DiagonalizableGroup.geometricallyReduced_coordinateRing_iff`: the coordinate ring of a
  diagonalizable group is geometrically reduced exactly when its character group has no
  `p`-torsion.
* `TauCeti.DiagonalizableGroup.smooth_coordinateRing_iff`: the coordinate ring of a
  diagonalizable group is smooth exactly when its character group has no `p`-torsion.

## References

* J. S. Milne, *Algebraic Groups* (2017), Remark 12.5 and Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w

namespace DiagonalizableGroup

/-- The coordinate ring of a diagonalizable group has connected prime spectrum when it is a
domain. -/
theorem connectedSpace_primeSpectrum_coordinateRing
    (K : Type v) [CommRing K] (G : FGCommGrpCat.{w}) [IsDomain (MonoidAlgebra K G)] :
    ConnectedSpace (PrimeSpectrum (coordinateRing K G).obj) :=
  inferInstanceAs (ConnectedSpace (PrimeSpectrum (MonoidAlgebra K G)))

/-- The base change of a diagonalizable-group coordinate ring has connected prime spectrum when
the resulting group algebra is a domain. -/
theorem connectedSpace_primeSpectrum_baseChange_coordinateRing
    (k : Type u) (K : Type v) [CommRing k] [CommRing K] [Algebra k K]
    (G : FGCommGrpCat.{w}) [IsDomain (MonoidAlgebra K G)] :
    ConnectedSpace (PrimeSpectrum
      (CommHopfAlgCat.baseChange (K := K) (coordinateRing k G).obj)) := by
  let e := (MonoidAlgebra.scalarTensorBialgEquiv k K (G := G)).toAlgEquiv
  have := connectedSpace_primeSpectrum_coordinateRing K G
  exact e.toRingHom.connectedSpace_primeSpectrum_of_injective e.injective

/-- Scalar extension identifies a diagonalizable-group coordinate ring with the corresponding
group algebra over the extension field. -/
private noncomputable def coordinateRingBaseChangeEquiv
    (k : Type u) [Field k] (G : Type w) [CommGroup G]
    (K : Type v) [Field K] [Algebra k K] :
    MonoidAlgebra k G ⊗[k] K ≃+* MonoidAlgebra K G :=
  (Algebra.TensorProduct.comm k _ K).toRingEquiv.trans
    (MonoidAlgebra.scalarTensorBialgEquiv k K (G := G)).toAlgEquiv.toRingEquiv

/-- **The coordinate Hopf algebra of a unique-product diagonalizable group is geometrically
connected.** -/
theorem geometricallyConnected_coordinateRing
    (k : Type u) [Field k] (G : FGCommGrpCat.{w}) [UniqueProds G] :
    geometricallyConnectedCommHopfAlgProperty k
      (DiagonalizableGroup.coordinateRing k G).obj := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (coordinateRingBaseChangeEquiv k G K)).connectedSpace_iff.mpr inferInstance

/-- **The coordinate Hopf algebra of a unique-product diagonalizable group is geometrically
reduced.** -/
theorem geometricallyReduced_coordinateRing
    (k : Type u) [Field k] (G : FGCommGrpCat.{w}) [UniqueProds G] :
    geometricallyReducedCommHopfAlgProperty k
      (DiagonalizableGroup.coordinateRing k G).obj := by
  rw [geometricallyReducedCommHopfAlgProperty_iff]
  intro K _ _
  let φ := coordinateRingBaseChangeEquiv k G K
  exact isReduced_of_injective φ.toRingHom φ.injective

/-- **The group algebra of a commutative group over a field of exponential characteristic `p`
is geometrically reduced exactly when the group has no `p`-torsion.** In characteristic zero,
where `p = 1`, the condition is empty. The group need not be finitely generated. -/
theorem geometricallyReduced_monoidAlgebra_iff
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (G : Type w) [CommGroup G] :
    geometricallyReducedCommHopfAlgProperty k (CommHopfAlgCat.of k (MonoidAlgebra k G)) ↔
      ∀ g : G, g ^ p = 1 → g = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : IsReduced (MonoidAlgebra k G) := h.isReduced
    exact (MonoidAlgebra.isReduced_iff_forall_pow_eq_one_imp_eq_one k G p).mp this
  · rw [geometricallyReducedCommHopfAlgProperty_iff]
    intro K _ _
    have : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
    have : IsReduced (MonoidAlgebra K G) :=
      (MonoidAlgebra.isReduced_iff_forall_pow_eq_one_imp_eq_one K G p).mpr h
    let φ := coordinateRingBaseChangeEquiv k G K
    exact isReduced_of_injective φ.toRingHom φ.injective

/-- **The coordinate Hopf algebra of a diagonalizable group over a field of exponential
characteristic `p` is geometrically reduced exactly when its character group has no
`p`-torsion.** In characteristic zero, where `p = 1`, the condition is empty. -/
theorem geometricallyReduced_coordinateRing_iff
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (G : FGCommGrpCat.{w}) :
    geometricallyReducedCommHopfAlgProperty k (DiagonalizableGroup.coordinateRing k G).obj ↔
      ∀ g : G, g ^ p = 1 → g = 1 :=
  -- The coordinate ring of `D(G)` over `k` is, by definition, the group algebra `k[G]`.
  geometricallyReduced_monoidAlgebra_iff k p G

/-- **The coordinate Hopf algebra of a diagonalizable group over a field of exponential
characteristic `p` is smooth exactly when its character group has no `p`-torsion.** In
characteristic zero, where `p = 1`, the condition is empty. -/
theorem smooth_coordinateRing_iff
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (G : FGCommGrpCat.{w}) :
    smoothCommHopfAlgProperty k (coordinateRing k G).obj ↔ ∀ g : G, g ^ p = 1 → g = 1 :=
  (smoothCommHopfAlgProperty_iff_geometricallyReduced k (coordinateRing k G).obj).trans
    (geometricallyReduced_coordinateRing_iff k p G)

end DiagonalizableGroup

end TauCeti
