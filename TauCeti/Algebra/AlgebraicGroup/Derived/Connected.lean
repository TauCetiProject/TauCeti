/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Connected.Comultiplication
import TauCeti.Algebra.AlgebraicGroup.Connected.Product
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Comap
import TauCeti.AlgebraicGeometry.AugmentationPoint.ConnectedComponent

/-!
# Connectedness of the derived subgroup

The derived closed subgroup of a connected affine group of finite type over an algebraically
closed field is geometrically connected. Neither smoothness nor reducedness is needed.
This supplies the connectedness input for induction on the derived series in Lie--Kolchin.

The commutator morphism factors through the derived subgroup. Its source is connected, so its
image lies in the identity component of that subgroup. The defining universal property of the
derived subgroup then forces that identity component to be the whole subgroup.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d, for derived subgroups, and §2.a, for components.
* The identity-component construction used here is
  `TauCeti.HopfAlgebra.identityComponentHopfIdeal`.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k]
variable (H : Type v) [CommRing H] [HopfAlgebra k H]

/-- The coordinate map of the commutator morphism `G × G → D(G)`. -/
private noncomputable def commutatorToDerivedAlgHom :
    (H ⧸ (derivedDefiningIdeal (R := k) H).toIdeal) →ₐ[k] H ⊗[k] H :=
  Ideal.Quotient.liftₐ _ HopfAlgebra.commutatorAlgHom
    (fun _ hx ↦ RingHom.mem_ker.mp (derivedDefiningIdeal_toIdeal_le_ker H hx))

private theorem commutatorToDerivedAlgHom_mk (x : H) :
    commutatorToDerivedAlgHom H
      ((mkQuotient (_root_.CommHopfAlgCat.of k H) (derivedDefiningIdeal H)).hom x) =
      HopfAlgebra.commutatorAlgHom x := by
  rw [mkQuotient_apply, commutatorToDerivedAlgHom]
  exact DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp
    (derivedDefiningIdeal (R := k) H).toIdeal
    (HopfAlgebra.commutatorAlgHom (R := k) (H := H))
    (fun _ hx ↦ RingHom.mem_ker.mp (derivedDefiningIdeal_toIdeal_le_ker H hx))) x

private theorem counit_comp_commutatorToDerivedAlgHom :
    (Algebra.TensorProduct.productMap (Bialgebra.counitAlgHom k H)
      (Bialgebra.counitAlgHom k H)).comp (commutatorToDerivedAlgHom H) =
      Bialgebra.counitAlgHom k (H ⧸ (derivedDefiningIdeal (R := k) H).toIdeal) := by
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := mkQuotient_surjective
    (_root_.CommHopfAlgCat.of k H) (derivedDefiningIdeal H) x
  rw [AlgHom.comp_apply, commutatorToDerivedAlgHom_mk]
  have heval := DFunLike.congr_fun
    (HopfAlgebra.productMap_comp_commutatorAlgHom
      (1 : WithConv (H →ₐ[k] k)) 1) y
  rw [commutatorElement_self] at heval
  rw [Bialgebra.counitAlgHom_apply, CoalgHomClass.counit_comp_apply]
  simpa only [AlgHom.convOne_def, Algebra.ofId_self,
    AlgHom.id_comp, ofConv_toConv, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply] using heval

variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- If the tensor square of the ambient coordinate ring has connected spectrum, the identity
component of its derived subgroup is the whole derived subgroup. -/
private theorem identityComponentHopfIdeal_quotient_derivedDefiningIdeal_eq_bot
    [ConnectedSpace (PrimeSpectrum (H ⊗[k] H))] :
    HopfAlgebra.identityComponentHopfIdeal
      (k := k) (H := H ⧸ (derivedDefiningIdeal (R := k) H).toIdeal) = ⊥ := by
  let A := _root_.CommHopfAlgCat.of k H
  let D := quotient A (derivedDefiningIdeal H)
  let J := HopfAlgebra.identityComponentHopfIdeal (k := k) (H := D)
  let q := (mkQuotient A (derivedDefiningIdeal H)).hom
  let f := commutatorToDerivedAlgHom (k := k) H
  let ε := Algebra.TensorProduct.productMap (Bialgebra.counitAlgHom k H)
    (Bialgebra.counitAlgHom k H)
  let _ : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing k D
  let z := Bialgebra.augmentationPoint k D
  let e := PrimeSpectrum.connectedComponentIdempotent z
  have hfe : f (PrimeSpectrum.connectedComponentIdempotent z) = 1 := by
    rcases eq_zero_or_eq_one_of_isIdempotentElem
      ((PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent z).map f) with h | h
    · have hε := DFunLike.congr_fun (counit_comp_commutatorToDerivedAlgHom H) e
      have he := TauCeti.AlgHom.map_connectedComponentIdempotent_kernelPoint_eq_one
        (Bialgebra.counitAlgHom k D)
      have : ε (f e) = 1 := hε.trans he
      rw [h, map_zero] at this
      exact (zero_ne_one this).elim
    · exact h
  apply eq_bot_of_comapOfSurjective_le J
  rw [le_derivedDefiningIdeal_iff]
  intro x hx
  have hqx : q x ∈ PrimeSpectrum.connectedComponentIdeal z :=
    HopfAlgebra.mem_identityComponentHopfIdeal.mp
      (HopfIdeal.mem_comapOfSurjective.mp hx)
  obtain ⟨a, ha⟩ := PrimeSpectrum.mem_connectedComponentIdeal_iff.mp hqx
  have hfx : f (q x) = 0 := by
    rw [← ha]
    simp only [map_mul, map_sub, map_one, hfe, sub_self, mul_zero]
  exact RingHom.mem_ker.mpr ((commutatorToDerivedAlgHom_mk H x).symm.trans hfx)

/-- The derived subgroup of a connected finite-type affine group over an algebraically closed
field has connected spectrum. Smoothness and reducedness are not required. -/
theorem connectedSpace_quotient_derivedDefiningIdeal
    (H : Type u) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [ConnectedSpace (PrimeSpectrum H)] :
    ConnectedSpace (PrimeSpectrum (H ⧸ (derivedDefiningIdeal (R := k) H).toIdeal)) := by
  let A := _root_.CommHopfAlgCat.of k H
  have hA := (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k A).mpr
    inferInstance
  let _ : ConnectedSpace (PrimeSpectrum (H ⊗[k] H)) :=
    (hA.tensorProduct A A hA).connectedSpace k _
  let D := quotient A (derivedDefiningIdeal H)
  let _ : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing k D
  let z := Bialgebra.augmentationPoint k D
  have hbot : PrimeSpectrum.connectedComponentIdeal z = ⊥ := by
    rw [← HopfAlgebra.identityComponentHopfIdeal_toIdeal,
      identityComponentHopfIdeal_quotient_derivedDefiningIdeal_eq_bot, HopfIdeal.bot_toIdeal]
  let e := (Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot D)
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mp
    (PrimeSpectrum.connectedSpace_quotient_connectedComponentIdeal z)

/-- The derived subgroup of a connected finite-type affine group over an algebraically closed
field is geometrically connected. -/
theorem geometricallyConnectedCommHopfAlgProperty_quotient_derivedDefiningIdeal
    (H : Type u) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [ConnectedSpace (PrimeSpectrum H)] :
    geometricallyConnectedCommHopfAlgProperty k
      (quotient (_root_.CommHopfAlgCat.of k H) (derivedDefiningIdeal H)) :=
  (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mpr
    (connectedSpace_quotient_derivedDefiningIdeal H)

end TauCeti.CommHopfAlgCat
