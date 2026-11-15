/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Flat
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.FiniteStability
import TauCeti.RingTheory.Flat.Descent
import TauCeti.RingTheory.TensorProduct.Descent
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Faithfully flat homomorphisms to geometrically reduced affine groups

A homomorphism between finite-type affine groups over an arbitrary field, with geometrically
reduced target, is faithfully flat exactly when its coordinate map is injective. Equivalently,
it is faithfully flat exactly when it is dominant. The source group may be nonreduced and the
homomorphism need not be finite. These criteria establish flatness of quotient projections
without assuming it as part of the input.

## References

* J. S. Milne, *Algebraic Groups* (2017), Propositions 1.65(a) and 1.70.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [Algebra.FiniteType k K]
  [Algebra.IsGeometricallyReduced k H]

/-- A homomorphism between finite-type affine groups with geometrically reduced target is
faithfully flat exactly when its coordinate map is injective, over any field. -/
theorem faithfullyFlat_iff_injective_of_isGeometricallyReduced (f : H ⟶ K) :
    f.hom.toAlgHom.toRingHom.FaithfullyFlat ↔ Function.Injective f.hom := by
  refine ⟨fun hf ↦ hf.injective, fun hinj ↦ ?_⟩
  -- The algebraic-closure/descent argument is adapted from the prior formalization of
  -- `TauCeti.CommHopfAlgCat.isIsogeny_iff_finite_and_dominant` in
  -- `TauCeti.Algebra.AlgebraicGroup.Isogeny.GeometricallyReduced`.
  let L := AlgebraicClosure k
  let fL := baseChangeMap (K := L) f
  have hdomL : DenseRange (PrimeSpectrum.comap fL.hom.toAlgHom.toRingHom) :=
    RingHom.denseRange_comap_of_injective _ (baseChangeMap_injective f hinj)
  have hflatL := faithfullyFlat_of_dominant fL hdomL
  apply RingHom.FaithfullyFlat.codescendsAlong_faithfullyFlat.of_tensorProduct_map
    (S := L) f.hom.toAlgHom
  have hmap : fL.hom.toAlgHom.toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id k L) f.hom.toAlgHom).toRingHom :=
    congrArg (fun g ↦ g.toAlgHom.toRingHom) (hom_baseChangeMap (K := L) f)
  exact hmap ▸ hflatL

/-- Dominance is equivalent to faithful flatness for a homomorphism between finite-type affine
groups with geometrically reduced target. No perfection assumption on the field is needed. -/
theorem faithfullyFlat_iff_dominant_of_isGeometricallyReduced (f : H ⟶ K) :
    f.hom.toAlgHom.toRingHom.FaithfullyFlat ↔
      DenseRange (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom) := by
  have : IsReduced H := Algebra.isReduced_of_isGeometricallyReduced k
  rw [faithfullyFlat_iff_injective_of_isGeometricallyReduced,
    RingHom.denseRange_comap_iff_injective]
  exact iff_of_eq (congrArg Function.Injective
    ((AlgHom.coe_toRingHom f.hom.toAlgHom).trans (BialgHom.coe_toAlgHom f.hom))).symm

end TauCeti.CommHopfAlgCat
