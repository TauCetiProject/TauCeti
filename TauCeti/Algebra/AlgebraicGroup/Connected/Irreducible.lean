/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import TauCeti.AlgebraicGeometry.Scheme.RegularLocalRing
import TauCeti.RingTheory.Smooth.Regular
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Connected affine groups over perfect fields are irreducible

Let `H` be a finite-type commutative Hopf algebra over a perfect field `k`. If the prime spectrum
of `H` is connected, it is irreducible.

Over a perfect field the reduced quotient `H ⧸ nilradical H` is again a Hopf algebra
(`TauCeti.HopfIdeal.reduction`): its tensor square is reduced. It is geometrically reduced, hence
smooth over `k` (`TauCeti.smoothCommHopfAlgProperty_of_geometricallyReduced`), so it is a regular
ring and the local rings of its spectrum are regular local rings, in particular domains. A
connected Noetherian scheme whose local rings are domains is irreducible
(`TauCeti.AlgebraicGeometry.irreducibleSpace_of_connected_of_isDomain_stalk`). Finally, the
quotient map by the nilradical induces a homeomorphism of prime spectra, which carries both
connectedness and irreducibility across.

Perfectness of `k` is used twice: to make the nilradical a Hopf ideal and to make the reduced
quotient geometrically reduced. It holds in particular over an algebraically closed field.

## Main declarations

* `TauCeti.CommHopfAlgCat.irreducibleSpace_primeSpectrum_of_connectedSpace`: a finite-type
  commutative Hopf algebra over a perfect field with connected prime spectrum has irreducible
  prime spectrum.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.irreducibleSpace`: the same conclusion for
  a geometrically connected finite-type commutative Hopf algebra over a perfect field.

## References

* M. Brion, *Some structure theorems for algebraic groups*, Proc. Sympos. Pure Math. 94 (2017),
  Theorem 2.4.1(3) and Proposition 2.1.12.
-/

public section

namespace TauCeti

universe u v

namespace CommHopfAlgCat

/-- A finite-type commutative Hopf algebra over a perfect field whose prime spectrum is connected
has irreducible prime spectrum: a connected affine group of finite type over a perfect field is
irreducible. -/
theorem irreducibleSpace_primeSpectrum_of_connectedSpace (k : Type u) [Field k] [PerfectField k]
    (H : _root_.CommHopfAlgCat.{v} k) [Algebra.FiniteType k H]
    [ConnectedSpace (PrimeSpectrum H)] : IrreducibleSpace (PrimeSpectrum H) := by
  let I := HopfIdeal.reduction k H
  have hI : I.toIdeal = nilradical H := HopfIdeal.reduction_toIdeal k H
  let e := (PrimeSpectrum.isHomeomorph_comap (Ideal.Quotient.mk I.toIdeal)
    (fun x ↦ ⟨1, one_pos, by simpa [RingHom.mem_range] using Ideal.Quotient.mk_surjective x⟩)
    (by simp [hI])).homeomorph
  have : ConnectedSpace (AlgebraicGeometry.Spec (.of (H ⧸ I.toIdeal))) :=
    e.connectedSpace_iff.mpr ‹_›
  have hsmooth : smoothCommHopfAlgProperty k (quotient H I) :=
    smoothCommHopfAlgProperty_of_geometricallyReduced k _
      ((geometricallyReducedCommHopfAlgProperty_iff k _).mpr fun _ _ _ ↦ inferInstance)
  have : Algebra.Smooth k (H ⧸ I.toIdeal) := (smoothCommHopfAlgProperty_iff _).mp hsmooth
  have : IsRegularRing (H ⧸ I.toIdeal) := IsRegularRing.of_smooth (R := k)
  have : IrreducibleSpace (AlgebraicGeometry.Spec (.of (H ⧸ I.toIdeal))) :=
    AlgebraicGeometry.irreducibleSpace_of_connected_of_isDomain_stalk _ fun _ ↦ inferInstance
  exact e.irreducibleSpace_iff.mp this

end CommHopfAlgCat

/-- A geometrically connected finite-type commutative Hopf algebra over a perfect field has
irreducible prime spectrum. -/
theorem geometricallyConnectedCommHopfAlgProperty.irreducibleSpace (k : Type u) [Field k]
    [PerfectField k] (H : CommHopfAlgCat.{v} k) [Algebra.FiniteType k H]
    (hH : geometricallyConnectedCommHopfAlgProperty k H) : IrreducibleSpace (PrimeSpectrum H) :=
  have := hH.connectedSpace k H
  CommHopfAlgCat.irreducibleSpace_primeSpectrum_of_connectedSpace k H

end TauCeti
