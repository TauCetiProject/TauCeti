/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Local
public import TauCeti.RingTheory.Henselization.IndEtale
import TauCeti.RingTheory.Etale.Weakly
import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Noetherianity of the henselization of a local ring

A local ring is Noetherian if and only if its henselization at the maximal ideal is
Noetherian. In particular, the usual Noetherian completion theorems apply to that
henselization.

For ascent, the universal local map from the henselization to the completion of the
base is faithfully flat. Indeed, the completion is flat over the base, and the
henselization is weakly étale over it, so flatness passes to the henselization.
Noetherianity then descends from the completion. Descent to the original ring uses
faithful flatness of the henselization itself.

## References

* Stacks Project, Tag 06LJ, Noetherianity of henselizations.
* `TauCeti.Henselization.indEtale` and `Algebra.WeaklyEtale.flat_iff`
  supply the flatness argument.
-/

public section

open IsLocalRing

universe u

namespace TauCeti.Henselization

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The henselization of a Noetherian local ring at its maximal ideal is Noetherian. -/
instance isNoetherianRing [IsNoetherianRing R] :
    IsNoetherianRing (algebra (maximalIdeal R)) := by
  let C := AdicCompletion (maximalIdeal R) R
  let f : algebra (maximalIdeal R) →ₐ[R] C :=
    lift (map_maximalIdeal_le (algebraMap R C))
  let : Algebra (algebra (maximalIdeal R)) C := f.toAlgebra
  have : IsScalarTower R (algebra (maximalIdeal R)) C :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have : Module.Flat (algebra (maximalIdeal R)) C :=
    (_root_.Algebra.WeaklyEtale.flat_iff (R := R)).mpr inferInstance
  have : IsLocalHom (algebraMap (algebra (maximalIdeal R)) C) :=
    ⟨(isLocalHom_lift (maximalIdeal R)
      (map_maximalIdeal_le (algebraMap R C))).map_nonunit⟩
  have : Module.FaithfullyFlat (algebra (maximalIdeal R)) C :=
    .of_flat_of_isLocalHom
  exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (A := C) <| isNoetherian_of_linearEquiv
      (Algebra.TensorProduct.rid (algebra (maximalIdeal R)) C C).toLinearEquiv.symm

/-- A local ring is Noetherian exactly when its henselization at the maximal ideal is
Noetherian. Neither implication requires the local ring to be a domain. -/
@[stacks 06LJ "ordinary henselization"]
theorem isNoetherianRing_iff :
    IsNoetherianRing (algebra (maximalIdeal R)) ↔ IsNoetherianRing R := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have : Module.FaithfullyFlat R (algebra (maximalIdeal R)) :=
    .of_flat_of_isLocalHom
  exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (A := algebra (maximalIdeal R)) <| isNoetherian_of_linearEquiv
      (Algebra.TensorProduct.rid R (algebra (maximalIdeal R))
        (algebra (maximalIdeal R))).toLinearEquiv.symm

end TauCeti.Henselization
