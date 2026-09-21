/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Connected
import TauCeti.Algebra.AlgebraicGroup.Connected.Comultiplication
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Comap
import TauCeti.AlgebraicGeometry.AugmentationPoint.ConnectedComponent
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Connectedness of the derived subgroup

The derived closed subgroup of a connected affine group of finite type over an algebraically
closed field is geometrically connected. Neither smoothness nor reducedness is needed.
This supplies the connectedness input for induction on the derived series in Lie--Kolchin.

The commutator morphism factors through the derived subgroup. Each slice obtained by fixing
one argument is connected and contains the identity, so its image lies in the identity component
of that subgroup. The defining universal property of the derived subgroup then forces that
identity component to be the whole subgroup.

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

private theorem productMap_counit_comp_commutatorToDerivedAlgHom (g : H →ₐ[k] k) :
    (Algebra.TensorProduct.productMap g
      (Bialgebra.counitAlgHom k H)).comp (commutatorToDerivedAlgHom H) =
      Bialgebra.counitAlgHom k (H ⧸ (derivedDefiningIdeal (R := k) H).toIdeal) := by
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := mkQuotient_surjective
    (_root_.CommHopfAlgCat.of k H) (derivedDefiningIdeal H) x
  rw [AlgHom.comp_apply, commutatorToDerivedAlgHom_mk]
  have heval := DFunLike.congr_fun
    (HopfAlgebra.productMap_comp_commutatorAlgHom
      (toConv g) 1) y
  rw [commutatorElement_one_right] at heval
  rw [Bialgebra.counitAlgHom_apply, CoalgHomClass.counit_comp_apply]
  simpa only [AlgHom.convOne_def, Algebra.ofId_self,
    AlgHom.id_comp, ofConv_toConv, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply] using heval

variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- A commutator slice is connected and meets the identity, so an idempotent equal to one
at the identity pulls back to one along the commutator map. -/
private theorem commutatorToDerivedAlgHom_eq_one_of_isIdempotentElem
    [ConnectedSpace (PrimeSpectrum H)]
    (e : H ⧸ (derivedDefiningIdeal (R := k) H).toIdeal) (he : IsIdempotentElem e)
    (hεe : Bialgebra.counitAlgHom k _ e = 1) :
    commutatorToDerivedAlgHom H e = 1 := by
  let f := commutatorToDerivedAlgHom (k := k) H
  let _ : Algebra.FiniteType k (H ⊗[k] H) :=
    Algebra.FiniteType.trans (R := k) (S := H) (A := H ⊗[k] H)
      inferInstance inferInstance
  have he := he.map f
  apply eq_one_of_isIdempotentElem_of_forall_algHom_apply_eq_one (k := k) (K := k) he
  intro φ
  let g := φ.comp (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H)
  let h := φ.comp (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H)
  let F := Algebra.TensorProduct.productMap ((Algebra.ofId k H).comp g) (AlgHom.id k H)
  have hF : (Bialgebra.counitAlgHom k H).comp F =
      Algebra.TensorProduct.productMap g (Bialgebra.counitAlgHom k H) := by
    ext a <;> simp [F]
  have hφ : h.comp F = φ := by
    ext a <;> simp [F] <;> simp [g, h]
  have hFe : F (f e) = 1 := by
    rcases eq_zero_or_eq_one_of_isIdempotentElem (he.map F) with hzero | hone
    · have hε := DFunLike.congr_fun
        (productMap_counit_comp_commutatorToDerivedAlgHom H g) e
      have : Bialgebra.counitAlgHom k H (F (f e)) = 1 := by
        rw [← AlgHom.comp_apply, hF]
        exact hε.trans hεe
      rw [hzero, map_zero] at this
      exact (zero_ne_one this).elim
    · exact hone
  rw [← hφ, AlgHom.comp_apply, hFe, map_one]

/-- If the ambient coordinate ring has connected spectrum, the identity component of its
derived subgroup is the whole derived subgroup. -/
private theorem identityComponentHopfIdeal_quotient_derivedDefiningIdeal_eq_bot
    [ConnectedSpace (PrimeSpectrum H)] :
    HopfAlgebra.identityComponentHopfIdeal
      (k := k) (H := H ⧸ (derivedDefiningIdeal (R := k) H).toIdeal) = ⊥ := by
  let A := _root_.CommHopfAlgCat.of k H
  let D := quotient A (derivedDefiningIdeal H)
  -- Identify the raw quotient in the goal with the categorical quotient's carrier.
  change HopfAlgebra.identityComponentHopfIdeal (k := k) (H := D) = ⊥
  let J := HopfAlgebra.identityComponentHopfIdeal (k := k) (H := D)
  let q := (mkQuotient A (derivedDefiningIdeal H)).hom
  let f := commutatorToDerivedAlgHom (k := k) H
  let _ : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing k D
  let z := Bialgebra.augmentationPoint k D
  have hfe : f (PrimeSpectrum.connectedComponentIdempotent z) = 1 :=
    commutatorToDerivedAlgHom_eq_one_of_isIdempotentElem H _
      (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent z)
      (TauCeti.AlgHom.map_connectedComponentIdempotent_kernelPoint_eq_one
        (Bialgebra.counitAlgHom k D))
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
theorem connectedSpace_derived
    (H : Type v) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [ConnectedSpace (PrimeSpectrum H)] :
    ConnectedSpace (PrimeSpectrum (H ⧸ (derivedDefiningIdeal (R := k) H).toIdeal)) := by
  let A := _root_.CommHopfAlgCat.of k H
  let D := quotient A (derivedDefiningIdeal H)
  -- Identify the raw quotient in the goal with the categorical quotient's carrier.
  change ConnectedSpace (PrimeSpectrum D)
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
theorem geometricallyConnectedCommHopfAlgProperty_derived
    (H : Type v) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [ConnectedSpace (PrimeSpectrum H)] :
    geometricallyConnectedCommHopfAlgProperty k
      (quotient (_root_.CommHopfAlgCat.of k H) (derivedDefiningIdeal H)) :=
  (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mpr
    (connectedSpace_derived H)

/-- The structural morphism of the derived group scheme of a connected finite-type affine
group over an algebraically closed field is geometrically connected. -/
instance geometricallyConnected_derivedGroupScheme
    {H : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H]
    [ConnectedSpace (PrimeSpectrum H)] :
    AlgebraicGeometry.GeometricallyConnected (derivedGroupScheme H).X.hom :=
  (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec k
    (quotient H (derivedDefiningIdeal H))).mp
      (geometricallyConnectedCommHopfAlgProperty_derived H)

end TauCeti.CommHopfAlgCat
