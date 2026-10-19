/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Coinvariants
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Coordinate
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Quotient
import TauCeti.RingTheory.RingHom.FaithfullyFlat
import TauCeti.AlgebraicGeometry.AugmentationPoint.ConnectedComponent

/-!
# Connected extensions of affine groups

A faithfully flat homomorphism of finite-type affine groups with geometrically connected
kernel and target has geometrically connected source. Neither the groups nor the kernel
are required to be smooth or reduced.

Over an algebraically closed field, the kernel lies in the source's identity component.
Thus the coordinate map of the component group takes values in the kernel coinvariants,
which are exactly the functions pulled back from the target. The idempotent selecting the
identity component therefore comes from the connected target and must equal one.
Scalar extension gives the geometric statement over an arbitrary field.

This extension criterion is used when studying preimages of connected normal subgroups,
in particular in the reduction of a connected affine group by its solvable radical.
The proof uses the component coordinate map from `Connected.ComponentGroup.Coordinate`
and faithfully flat descent of kernel coinvariants from
`HopfIdeal.Quotient.Kernel.Coinvariants`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, extensions of algebraic groups.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §6.
-/

public section

open CategoryTheory
open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

namespace CommHopfAlgCat.Hom

open TauCeti TauCeti.CommHopfAlgCat

universe u

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {Q G : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k G]

/-- Over an algebraically closed field, a faithfully flat homomorphism of affine groups
with connected kernel and target has connected source. Only the source needs to be of
finite type. Coordinate arrows run from the target `Q` to the source `G`. -/
theorem connectedSpace_of_connected_kernel (f : Q ⟶ G)
    (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    [ConnectedSpace (PrimeSpectrum Q)]
    [ConnectedSpace (PrimeSpectrum (quotient G (kernelHopfIdeal f)))] :
    ConnectedSpace (PrimeSpectrum G) := by
  classical
  let H : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨G, (finiteTypeCommHopfAlgProperty_iff G).mpr inferInstance⟩
  let _ : IsNoetherianRing G := Algebra.FiniteType.isNoetherianRing k G
  let _ := FiniteTypeCommHopfAlgCat.instGroupConnectedComponents H
  let z : PrimeSpectrum G := Bialgebra.augmentationPoint k G
  let e : G := PrimeSpectrum.connectedComponentIdempotent z
  -- The kernel is contained in the identity component, so component functions descend.
  have hI : HopfAlgebra.identityComponentHopfIdeal (k := k) (H := G) ≤
      kernelHopfIdeal f := by
    intro x hx
    exact (mkQuotient_eq_zero_iff G (kernelHopfIdeal f) x).mp
      (identityComponentHopfIdeal_toIdeal_le_ker_of_connected
        (mkQuotient G (kernelHopfIdeal f)) hx)
  have hcoinv : ∀ x, (FiniteTypeCommHopfAlgCat.componentCoordinateHom H).hom x ∈
      (kernelHopfIdeal f).coinvariants := by
    apply (HopfIdeal.forall_hom_mem_coinvariants_iff _).mpr
    rw [FiniteTypeCommHopfAlgCat.kernelHopfIdeal_componentCoordinateHom]
    exact hI
  have hecoinv : e ∈ (kernelHopfIdeal f).coinvariants := by
    let C := ConnectedComponents (PrimeSpectrum H)
    have he := hcoinv ((ConstantGroup.functionAlgEquiv k C).symm (Pi.single 1 1))
    rw [FiniteTypeCommHopfAlgCat.componentCoordinateHom_apply,
      FiniteTypeCommHopfAlgCat.componentCoordinateMap_indicator] at he
    have heq : PrimeSpectrum.connectedComponentsIdempotent
        (1 : ConnectedComponents (PrimeSpectrum H)) = e :=
      (congrArg PrimeSpectrum.connectedComponentsIdempotent
        (FiniteTypeCommHopfAlgCat.rationalKernelPoint_one_component H).symm).trans
        (PrimeSpectrum.connectedComponentsIdempotent_mk _)
    rwa [heq] at he
  rw [coinvariants_kernelHopfIdeal_eq_range f hf] at hecoinv
  obtain ⟨a, ha⟩ := hecoinv
  have ha' : f.hom a = e := ha
  have hinj : Function.Injective f.hom := hf.injective
  have haidem : IsIdempotentElem a := by
    apply hinj
    rw [map_mul, ha']
    exact PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent z
  -- Connectedness of the target makes the descended identity-component idempotent one.
  have heone : e = 1 := by
    rcases eq_zero_or_eq_one_of_isIdempotentElem haidem with hzero | hone
    · have hε : (Bialgebra.counitAlgHom k G) e = 1 :=
        AlgHom.map_connectedComponentIdempotent_kernelPoint_eq_one
          (Bialgebra.counitAlgHom k G)
      have hezero : e = 0 := by simpa [hzero] using ha'.symm
      rw [hezero, map_zero] at hε
      exact (zero_ne_one hε).elim
    · simpa [hone] using ha'.symm
  apply (HopfAlgebra.identityComponentHopfIdeal_eq_bot_iff_connectedSpace
    (k := k) (H := G)).mp
  apply HopfIdeal.ext
  intro x
  rw [HopfAlgebra.mem_identityComponentHopfIdeal, HopfIdeal.mem_bot]
  rw [PrimeSpectrum.mem_connectedComponentIdeal_iff (x := z)]
  dsimp only [e] at heone
  simp [heone, eq_comm]

end AlgebraicallyClosed

end CommHopfAlgCat.Hom

namespace TauCeti.geometricallyConnectedCommHopfAlgProperty

universe u

variable {k : Type u} [Field k]
variable {Q G : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k G]

/-- Geometric connectedness is closed under faithfully flat extensions of affine groups.
Only the source group is required to be of finite type; smoothness, reducedness, and
perfectness of the ground field are unnecessary. -/
theorem of_kernel (hQ : geometricallyConnectedCommHopfAlgProperty k Q)
    (f : Q ⟶ G) (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hN : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient G (CommHopfAlgCat.kernelHopfIdeal f))) :
    geometricallyConnectedCommHopfAlgProperty k G := by
  let K := AlgebraicClosure k
  let fK := CommHopfAlgCat.baseChangeMap (K := K) f
  apply (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_baseChange k K G).mpr
  have hQK := (hQ.baseChange k K Q).connectedSpace K _
  let _ := hQK
  have hNK := hN.baseChange k K _
  let e := CommHopfAlgCat.quotientBaseChangeIso (K := K)
    (CommHopfAlgCat.kernelHopfIdeal f)
  rw [CommHopfAlgCat.baseChangeHopfIdeal_kernelHopfIdeal] at e
  have hNK' : geometricallyConnectedCommHopfAlgProperty K
      (CommHopfAlgCat.quotient (CommHopfAlgCat.baseChange (K := K) G)
        (CommHopfAlgCat.kernelHopfIdeal fK)) :=
    (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso e.symm hNK
  let _ := hNK'.connectedSpace K _
  apply _root_.CommHopfAlgCat.Hom.connectedSpace_of_connected_kernel fK
  dsimp only [fK]
  simpa only [CommHopfAlgCat.hom_baseChangeMap, Bialgebra.TensorProduct.map_toAlgHom,
    BialgHom.id_toAlgHom] using hf.lTensor K

end TauCeti.geometricallyConnectedCommHopfAlgProperty
