/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Finite
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Reductive
import TauCeti.Algebra.AlgebraicGroup.Center.Descent
import TauCeti.Algebra.AlgebraicGroup.Reductive.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Reductive
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Semisimple
import TauCeti.Algebra.AlgebraicGroup.Connected.Finite
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Semisimplicity and finiteness of the center

Over any field and in every characteristic, an affine group of finite type is semisimple if
and only if it is reductive and its scheme-theoretic center is finite. In particular, this
criterion distinguishes the semisimple part of reductive structure theory from central
torus factors. No splitting or algebraic-closedness assumption is imposed on the field.

For the converse, the geometric solvable radical of a reductive group is central. If the
center is finite, the radical is finite as well; being smooth and connected, it is trivial.
The proof uses the centrality theorem in `Solvable.Radical.Reductive` and the finite connected
reduced group theorem in `Connected.Finite`. The forward implication is the finite-center
theorem in `Semisimple.Center.Finite`.

## References

* A. Borel, *Linear Algebraic Groups*, §14.2.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 19 and 21.
-/

public section

namespace TauCeti

universe u

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A reductive affine group with finite scheme-theoretic center is semisimple, over an arbitrary
ground field and in every characteristic. -/
theorem reductiveCommHopfAlgProperty.semisimple_of_moduleFinite_centerCoordinate
    (hH : reductiveCommHopfAlgProperty k H)
    (hfinite : Module.Finite k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj)) :
    semisimpleCommHopfAlgProperty k H := by
  rw [semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation]
  refine ⟨hH.smooth, hH.geometricallyConnected, ?_⟩
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let R := FiniteTypeCommHopfAlgCat.solvableRadical G
  let I := FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal G
  have hG := hH.algebraicClosureBaseChange
  have hcentral : CommHopfAlgCat.centerDefiningIdeal G.obj ≤ I :=
    (CommHopfAlgCat.centerDefiningIdeal_le_iff G.obj I).mpr
      hG.isCentral_solvableRadicalDefiningIdeal
  let f := CommHopfAlgCat.quotientMapOfLe G.obj hcentral
  let _ : Module.Finite K (CommHopfAlgCat.centerCoordinateHopfAlgebra G.obj) :=
    (CommHopfAlgCat.moduleFinite_centerCoordinate_baseChange_iff H.obj).mpr hfinite
  let _ : Module.Finite K R := Module.Finite.of_surjective f.hom.toAlgHom.toLinearMap
    (CommHopfAlgCat.quotientMapOfLe_surjective G.obj hcentral)
  have hR := FiniteTypeCommHopfAlgCat.isSolvableRadicalCandidate_solvableRadicalDefiningIdeal G
  let _ : Algebra.Smooth K R := hR.smooth
  let _ : IsReduced R := isReduced_of_smooth K R
  let _ : ConnectedSpace (PrimeSpectrum R) :=
    hR.geometricallyConnected.connectedSpace K R.obj
  have htrivial : HopfIdeal.augmentation K R = ⊥ :=
    HopfIdeal.augmentation_eq_bot_of_moduleFinite
  apply le_antisymm (HopfIdeal.le_augmentation K G I)
  intro x hx
  have hxR : (CommHopfAlgCat.mkQuotient G.obj I).hom x ∈ HopfIdeal.augmentation K R := by
    rw [HopfIdeal.mem_augmentation, CoalgHomClass.counit_comp_apply]
    exact (HopfIdeal.mem_augmentation K G).mp hx
  rw [htrivial, HopfIdeal.mem_bot] at hxR
  exact (CommHopfAlgCat.mkQuotient_eq_zero_iff G.obj I x).mp hxR

/-- Semisimplicity is equivalent to reductivity together with finiteness of the full
scheme-theoretic center, in every characteristic. -/
theorem semisimpleCommHopfAlgProperty_iff_reductive_and_moduleFinite_centerCoordinate
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    semisimpleCommHopfAlgProperty k H ↔
      reductiveCommHopfAlgProperty k H ∧
        Module.Finite k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) :=
  ⟨fun hH ↦ ⟨hH.reductive, hH.moduleFinite_centerCoordinate⟩,
    fun ⟨hH, hfinite⟩ ↦ hH.semisimple_of_moduleFinite_centerCoordinate hfinite⟩

end TauCeti
