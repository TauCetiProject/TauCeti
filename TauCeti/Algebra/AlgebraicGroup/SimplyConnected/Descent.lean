/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SimplyConnected.Basic
import TauCeti.Algebra.AlgebraicGroup.Semisimple.Isogeny.Source
import TauCeti.RingTheory.TensorProduct.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Descent of simple connectivity

A semisimple affine group is simply connected if a scalar extension of it is simply connected.
The extension can be arbitrary: neither algebraicity nor separability is required. In particular,
one can establish simple connectivity over an algebraic closure and descend to the ground field.

For a central isogeny onto the original group, scalar extension preserves the central isogeny,
smoothness, and geometric connectedness of its source. The extended source is semisimple by
`semisimpleCommHopfAlgProperty.of_isIsogeny`, since its target is semisimple. Thus simple
connectivity of the extended group makes the coordinate map surjective, and faithful flatness
reflects surjectivity. This argument does not require a general preservation theorem for
semisimplicity under field extension.

The semisimplicity proof for the scalar extension is an explicit argument because the existing
simple-connectivity property is defined on the category of semisimple groups. It is part of
saying that the scalar extension is simply connected, rather than a condition on the test covers.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.4, simply connected semisimple groups.
* T. A. Springer, *Linear Algebraic Groups*, §9.6.

The proof uses the coordinate surjectivity criterion from `SimplyConnected.Basic`, preservation
of central isogenies under base change, and Mathlib's faithfully flat descent of surjectivity.
-/

public section

open CategoryTheory

namespace TauCeti.simplyConnectedSemisimpleCommHopfAlgProperty

universe u

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {H : SemisimpleCommHopfAlgCat.{u} k}

/-- **Simple connectivity descends along any field extension.** If the scalar extension of a
semisimple affine group is semisimple and simply connected, the original group is simply
connected. The semisimplicity proof supplies the object on which the extended simple-connectivity
property is evaluated and is inferred from that hypothesis. -/
theorem of_baseChange
    {hHL : semisimpleCommHopfAlgProperty L
      (FiniteTypeCommHopfAlgCat.baseChange (K := L) H.obj)}
    (hH : simplyConnectedSemisimpleCommHopfAlgProperty L
      ⟨FiniteTypeCommHopfAlgCat.baseChange (K := L) H.obj, hHL⟩) :
    simplyConnectedSemisimpleCommHopfAlgProperty k H := by
  apply (simplyConnectedSemisimpleCommHopfAlgProperty_iff_forall_surjective H).mpr
  intro G f hf
  let HL : SemisimpleCommHopfAlgCat L :=
    ⟨FiniteTypeCommHopfAlgCat.baseChange (K := L) H.obj, hHL⟩
  let Gₗ : FiniteTypeCommHopfAlgCat L := FiniteTypeCommHopfAlgCat.baseChange (K := L) G.obj
  have hfL := hf.baseChange (L := L)
  let _ : Algebra.Smooth k G.obj := G.property.smooth
  have hGL : semisimpleCommHopfAlgProperty L Gₗ :=
    hHL.of_isIsogeny (CommHopfAlgCat.baseChangeMap (K := L) f.hom.hom)
      hfL.isIsogeny (Algebra.Smooth.baseChange k G.obj L)
      (geometricallyConnectedCommHopfAlgProperty.baseChange k L G.obj.obj
        G.property.geometricallyConnected)
  let fL : HL ⟶ (⟨Gₗ, hGL⟩ : SemisimpleCommHopfAlgCat L) :=
    ObjectProperty.homMk (FiniteTypeCommHopfAlgCat.baseChangeMap (K := L) f.hom)
  have hsurjL := hH.surjective fL hfL
  apply RingHom.FaithfullyFlat.codescendsAlong_surjective.of_tensorProduct_map
    (S := L) f.hom.hom.hom.toAlgHom
  -- Both scalar structures give the same underlying tensor-product function. Surjectivity
  -- forgets those structures, so the bundled base-change map supplies this ring-map goal.
  exact hsurjL

end TauCeti.simplyConnectedSemisimpleCommHopfAlgProperty
