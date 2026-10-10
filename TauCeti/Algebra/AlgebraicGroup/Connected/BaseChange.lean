/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.TensorProduct.CommonOverfield
import TauCeti.RingTheory.Idempotents.Connected.ScalarExtension

/-!
# Geometric connectedness under base change

Geometric connectedness of a commutative Hopf algebra is preserved by and descends along extension
of the base field. In particular, `H` is geometrically connected over `k` if and only if the scalar
extension `K ⊗[k] H` is geometrically connected over any field extension `K / k`.
The base field, extension field, and coordinate algebra may lie in independent universes.

If `K` is algebraically closed, ordinary connectedness of `K ⊗[k] H` suffices. Thus geometric
connectedness can be checked over a single algebraically closed extension, such as the algebraic
closure of `k`, without a finite-type assumption.

Preservation compares an arbitrary further extension `L / K` with the original geometric
connectedness condition using the canonical algebra equivalence

```text
L ⊗[K] (K ⊗[k] H) ≃ L ⊗[k] H.
```

For descent, a common overfield of `K` and an arbitrary extension of `k` compares the
two scalar extensions, after which connectedness descends along an injective map.

## Main declarations

* `TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace_tensorProduct`: geometric
  connectedness gives connectedness after a field extension in any universe.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.baseChange`: geometric connectedness is
  preserved by extension of the base field.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.of_baseChange`: geometric connectedness
  descends from an extension of the base field.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.baseChange_iff`: geometric connectedness is
  equivalent before and after extension of the base field.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_baseChange`: geometric
  connectedness can be tested over any single algebraically closed extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.a.

This is base-change infrastructure for Layer 3, "Identity component and component group", of the
ReductiveGroups roadmap: connectedness there is geometric and is therefore used after extending
the ground field.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

/-- A geometrically connected commutative Hopf algebra has connected spectrum after every field
extension, including extensions in a different universe from the base field.
No finite-type assumption is needed. -/
theorem geometricallyConnectedCommHopfAlgProperty.connectedSpace_tensorProduct
    (k : Type u) (K : Type w) [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{v} k)
    (hH : geometricallyConnectedCommHopfAlgProperty k H) :
    ConnectedSpace (PrimeSpectrum ((H : Type v) ⊗[k] K)) := by
  let d := Algebra.TensorProduct.commonOverfield k (AlgebraicClosure k) K
  have hclosure :
      ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] (H : Type v))) :=
    hH.connectedSpace_algebraicClosureBaseChange
  have hextended : ConnectedSpace (PrimeSpectrum
      ((AlgebraicClosure k ⊗[k] (H : Type v)) ⊗[AlgebraicClosure k] d.Ω)) :=
    connectedSpace_primeSpectrum_tensorProduct_of_isAlgClosed
      (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] (H : Type v)) d.Ω
  have hΩ : ConnectedSpace (PrimeSpectrum ((H : Type v) ⊗[k] d.Ω)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (d.comparison H)).connectedSpace_iff.mp hextended
  exact connectedSpace_primeSpectrum_of_injective (d.map H).toRingHom (d.map_injective H)

/-- **Geometric connectedness is preserved by extension of the base field.**

For fields `k → K`, if the spectrum of `H ⊗[k] L` is connected for every field extension
`L / k`, then the spectrum of `(K ⊗[k] H) ⊗[K] L` is connected for every field extension
`L / K`. The two rings are identified by cancellation of successive scalar extensions. -/
theorem geometricallyConnectedCommHopfAlgProperty.baseChange
    (k : Type u) (K : Type w) [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{v} k)
    (hH : geometricallyConnectedCommHopfAlgProperty k H) :
    geometricallyConnectedCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro L _ _
  let _ : Algebra k L := Algebra.compHom L (algebraMap k K)
  let _ : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.baseChangeTowerRingEquiv k K H L)).connectedSpace_iff.mpr
      (hH.connectedSpace_tensorProduct k L H)

/-- **Geometric connectedness descends from an extension of the base field.**

If `K ⊗[k] H` is geometrically connected over a field extension `K / k`, then `H` is
geometrically connected over `k`. -/
theorem geometricallyConnectedCommHopfAlgProperty.of_baseChange
    (k : Type u) (K : Type w) [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{v} k)
    (hH : geometricallyConnectedCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H)) :
    geometricallyConnectedCommHopfAlgProperty k H := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro L _ _
  let d := Algebra.TensorProduct.commonOverfield k K L
  have hΩ : ConnectedSpace (PrimeSpectrum ((H : Type v) ⊗[k] d.Ω)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv (d.comparison H)).connectedSpace_iff.mp
      (hH.connectedSpace_tensorProduct K d.Ω (CommHopfAlgCat.baseChange (K := K) H))
  exact connectedSpace_primeSpectrum_of_injective (d.map H).toRingHom (d.map_injective H)

/-- Geometric connectedness is equivalent before and after extension of the base field. -/
theorem geometricallyConnectedCommHopfAlgProperty.baseChange_iff
    (k : Type u) (K : Type w) [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{v} k) :
    geometricallyConnectedCommHopfAlgProperty K
        (CommHopfAlgCat.baseChange (K := K) H) ↔
      geometricallyConnectedCommHopfAlgProperty k H :=
  ⟨geometricallyConnectedCommHopfAlgProperty.of_baseChange k K H,
    geometricallyConnectedCommHopfAlgProperty.baseChange k K H⟩

/-- Geometric connectedness can be tested by ordinary connectedness after a single algebraically
closed field extension. In particular, one may use the algebraic closure of the base field.
Neither a finite-type hypothesis nor a common universe for the fields and algebra is needed. -/
theorem geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_baseChange
    (k : Type u) (K : Type w) [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    (H : CommHopfAlgCat.{v} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      ConnectedSpace (PrimeSpectrum (K ⊗[k] (H : Type v))) :=
  (geometricallyConnectedCommHopfAlgProperty.baseChange_iff k K H).symm.trans
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace K
      (CommHopfAlgCat.baseChange (K := K) H)).trans
      (PrimeSpectrum.homeomorphOfRingEquiv
        (AlgEquiv.refl :
          (CommHopfAlgCat.baseChange (K := K) H : Type (max w v)) ≃ₐ[K]
            K ⊗[k] (H : Type v)).toRingEquiv).connectedSpace_iff)

end TauCeti
