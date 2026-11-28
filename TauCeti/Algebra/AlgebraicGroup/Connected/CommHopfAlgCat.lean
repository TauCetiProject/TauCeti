/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.Flat.Basic
import TauCeti.AlgebraicGeometry.Geometrically.Connected
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Geometric connectedness of commutative Hopf algebras

For a commutative Hopf algebra `H` over a field `k`, geometric connectedness means that after
every extension `K / k` of the base field, the base-changed coordinate ring `H ⊗[k] K` has
connected prime spectrum. This is equivalent to saying that every such base change has no
idempotents other than zero and one. The Hopf counit gives a rational point, so ordinary
connectedness already implies geometric connectedness over any field.

The condition is exposed as an `ObjectProperty` on the ambient Hopf-algebra category; consumers
can impose it without introducing a separate bundled category of connected objects.

## Main declarations

* `TauCeti.geometricallyConnectedCommHopfAlgProperty`: the coordinate-ring predicate.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff`: its connected-spectrum form.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_idempotent_eq_zero_or_one`: its
  idempotent form.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.of_injective`: it descends along injective
  algebra homomorphisms of coordinate rings.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace`: the coordinate ring itself
  has connected prime spectrum.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace`: over any field,
  geometric connectedness is equivalent to connectedness of the coordinate ring.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace_algebraicClosureBaseChange`:
  the geometric fibre `AlgebraicClosure k ⊗[k] H` has connected prime spectrum.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.a.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w

/-- A Hopf algebra remains nontrivial after extension of its base field. -/
private theorem nontrivial_tensorProduct
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k)
    (K : Type u) [Field K] [Algebra k K] :
    Nontrivial ((H : Type v) ⊗[k] K) := by
  let : Nontrivial (H : Type v) := Bialgebra.nontrivial k
  exact Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
    k H K (algebraMap k K).injective

/-- A commutative Hopf algebra over a field is geometrically connected when the spectrum of its
coordinate ring remains connected after every extension of the base field. -/
def geometricallyConnectedCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (CommHopfAlgCat.{v} k) :=
  fun H ↦ ∀ (K : Type u) [Field K] [Algebra k K],
    ConnectedSpace (PrimeSpectrum ((H : Type v) ⊗[k] K))

/-- Membership in the geometrically connected commutative-Hopf-algebra object property. -/
@[simp]
theorem geometricallyConnectedCommHopfAlgProperty_iff
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ConnectedSpace (PrimeSpectrum ((H : Type v) ⊗[k] K)) :=
  Iff.rfl

/-- A geometrically connected commutative Hopf algebra has connected prime spectrum. -/
theorem geometricallyConnectedCommHopfAlgProperty.connectedSpace
    {k : Type u} [Field k] {H : CommHopfAlgCat.{v} k}
    (h : geometricallyConnectedCommHopfAlgProperty k H) :
    ConnectedSpace (PrimeSpectrum (H : Type v)) :=
  (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.rid k k H).toRingEquiv).connectedSpace_iff.mp (h k)

open AlgebraicGeometry in
attribute [local instance] ULift.algebra' in
/-- Over any field, a commutative Hopf algebra is geometrically connected exactly when its
prime spectrum is connected. No finite-type assumption or common universe is needed. -/
theorem geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      ConnectedSpace (PrimeSpectrum H) := by
  constructor
  · exact geometricallyConnectedCommHopfAlgProperty.connectedSpace
  · intro h
    -- Work in a common universe without restricting the field or coordinate algebra.
    let k' := ULift.{v} k
    let H' := ULift.{u} H
    have : ConnectedSpace (PrimeSpectrum H') :=
      (PrimeSpectrum.homeomorphOfRingEquiv ULift.ringEquiv).connectedSpace_iff.mpr h
    have : ConnectedSpace (Spec (CommRingCat.of H') : Scheme) := ‹ConnectedSpace (PrimeSpectrum H')›
    let ε : H' →+* k' := ULift.ringEquiv.symm.toRingHom.comp
      ((Bialgebra.counitAlgHom k H).toRingHom.comp ULift.ringEquiv.toRingHom)
    have hs : CommRingCat.ofHom (algebraMap k' H') ≫ CommRingCat.ofHom ε =
        𝟙 (CommRingCat.of k') := by
      ext x
      exact (Bialgebra.counitAlgHom k H).commutes x.down
    have hg : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k' H'))) := by
      apply geometricallyConnected_of_section (k := k')
        (f := Spec.map (CommRingCat.ofHom (algebraMap k' H')))
        (s := Spec.map (CommRingCat.ofHom ε))
      rw [← Spec.map_comp, hs, Spec.map_id]
    rw [GeometricallyConnected.eq_geometrically,
      geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms] at hg
    intro K _ _
    have hc : ConnectedSpace (PrimeSpectrum (H' ⊗[k'] ULift.{v} K)) :=
      (pullbackSpecIso k' H' (ULift.{v} K)).hom.homeomorph.connectedSpace_iff.mp
        (hg (ULift.{v} K))
    let e : ULift.{max u v} ((H : Type v) ⊗[k] K) ≃+* H' ⊗[k'] ULift.{v} K :=
      (Algebra.TensorProduct.uliftEquiv k k H K).toRingEquiv
    exact (PrimeSpectrum.homeomorphOfRingEquiv
      (e.symm.trans ULift.ringEquiv)).connectedSpace_iff.mp hc

/-- The geometric fibre of a geometrically connected commutative Hopf algebra has connected prime
spectrum, written with the algebraic closure on the left. This is the orientation used by the
geometric character group. -/
theorem geometricallyConnectedCommHopfAlgProperty.connectedSpace_algebraicClosureBaseChange
    {k : Type u} [Field k] {H : CommHopfAlgCat.{v} k}
    (h : geometricallyConnectedCommHopfAlgProperty k H) :
    ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] (H : Type v))) :=
  let e := Algebra.TensorProduct.comm k (AlgebraicClosure k) (H : Type v)
  have _ := h (AlgebraicClosure k)
  e.toRingHom.connectedSpace_primeSpectrum_of_injective e.injective

/-- Geometric connectedness is invariant under isomorphisms of commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (geometricallyConnectedCommHopfAlgProperty k).IsClosedUnderIsomorphisms where
  of_iso e hH := by
    rw [geometricallyConnectedCommHopfAlgProperty_iff] at hH ⊢
    intro K _ _
    let eK := Algebra.TensorProduct.congr
      (CommHopfAlgCat.ofIso e).toAlgEquiv (AlgEquiv.refl : K ≃ₐ[k] K)
    exact (PrimeSpectrum.homeomorphOfRingEquiv eK.toRingEquiv).connectedSpace_iff.mp (hH K)

/-- **A commutative Hopf algebra is geometrically connected exactly when, after every extension
`K / k` of the base field, every idempotent of `H ⊗[k] K` is zero or one.** -/
theorem geometricallyConnectedCommHopfAlgProperty_iff_idempotent_eq_zero_or_one
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      ∀ (K : Type u) [Field K] [Algebra k K] (e : (H : Type v) ⊗[k] K),
        IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  constructor
  · intro h K _ _
    let := nontrivial_tensorProduct k H K
    exact connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mp (h K)
  · intro h K _ _
    let := nontrivial_tensorProduct k H K
    exact connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mpr (h K)

/-- **Geometric connectedness descends along injective algebra homomorphisms.** If the coordinate
ring of `H` embeds, as a `k`-algebra, into that of a geometrically connected `H'`, then `H` is
geometrically connected. The embedding need not respect the Hopf structures: geometrically, the
connected spectrum of `H'` maps dominantly onto that of `H` after every extension of the base
field. -/
theorem geometricallyConnectedCommHopfAlgProperty.of_injective
    {k : Type u} [Field k] {H : CommHopfAlgCat.{v} k} {H' : CommHopfAlgCat.{w} k}
    (f : (H : Type v) →ₐ[k] (H' : Type w)) (hf : Function.Injective f)
    (h : geometricallyConnectedCommHopfAlgProperty k H') :
    geometricallyConnectedCommHopfAlgProperty k H := by
  intro K _ _
  have := h K
  exact RingHom.connectedSpace_primeSpectrum_of_injective
    (Algebra.TensorProduct.map f (AlgHom.id k K)).toRingHom
    (Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf)

end TauCeti
