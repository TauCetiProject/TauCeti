/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Coordinate
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Coinvariants
import TauCeti.AlgebraicGeometry.AugmentationPoint.ConnectedComponent

/-!
# Component groups of quotients with connected kernel

A faithfully flat homomorphism of finite-type affine groups over an algebraically closed
field induces an isomorphism on component groups if its scheme-theoretic kernel is connected.
Neither the groups nor the kernel need be smooth or reduced. Thus quotienting by a connected
normal subgroup preserves the component group, including for infinitesimal kernels.

The component homomorphism is already surjective. For injectivity, the connected kernel
lies in the identity component, so the component coordinate functions are kernel coinvariants
and descend along the faithfully flat morphism. In particular, the idempotent selecting the
source identity component descends to an idempotent of the target. It is one at the identity,
and hence on the entire target identity component. This detects the kernel of the component
homomorphism without discarding nilpotents in either coordinate algebra.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.mapComponentGroup_injective_of_connected_kernel`:
  injectivity of the component homomorphism for a faithfully flat map with connected kernel.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupMulEquivOfConnectedKernel`:
  the induced multiplicative equivalence on component groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, identity components and quotients.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §6.7.

The descent argument follows the component-idempotent argument in
`TauCeti.Algebra.AlgebraicGroup.Connected.Extension`, using
`TauCeti.CommHopfAlgCat.coinvariants_kernelHopfIdeal_eq_range`.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The identity-component idempotent descends along a faithfully flat homomorphism with
connected kernel. -/
private theorem exists_map_eq_identityComponentIdempotent (f : Q ⟶ G)
    (hf : f.hom.hom.toAlgHom.toRingHom.FaithfullyFlat)
    [ConnectedSpace (PrimeSpectrum
      (CommHopfAlgCat.quotient G.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)))] :
    ∃ a : Q, f.hom.hom a =
      PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k G) := by
  classical
  have hI : HopfAlgebra.identityComponentHopfIdeal (k := k) (H := G) ≤
      CommHopfAlgCat.kernelHopfIdeal f.hom := by
    intro x hx
    exact (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ x).mp
      (CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected
        (CommHopfAlgCat.mkQuotient G.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)) hx)
  have hcoinv : ∀ x, (componentCoordinateHom G).hom x ∈
      (CommHopfAlgCat.kernelHopfIdeal f.hom).coinvariants := by
    apply (HopfIdeal.forall_hom_mem_coinvariants_iff _).mpr
    rw [kernelHopfIdeal_componentCoordinateHom]
    exact hI
  let C := ConnectedComponents (PrimeSpectrum G)
  have he := hcoinv ((ConstantGroup.functionAlgEquiv k C).symm (Pi.single 1 1))
  rw [componentCoordinateHom_apply, componentCoordinateMap_indicator] at he
  have heq : PrimeSpectrum.connectedComponentsIdempotent (1 : C) =
      PrimeSpectrum.connectedComponentIdempotent
        (Bialgebra.augmentationPoint k G : PrimeSpectrum G) :=
    (congrArg PrimeSpectrum.connectedComponentsIdempotent
      (rationalKernelPoint_one_component G).symm).trans
      (PrimeSpectrum.connectedComponentsIdempotent_mk _)
  rw [heq, CommHopfAlgCat.coinvariants_kernelHopfIdeal_eq_range f.hom hf] at he
  exact he

/-- A faithfully flat homomorphism with connected scheme-theoretic kernel is injective on
component groups. The source, target, and kernel may be nonreduced. -/
theorem mapComponentGroup_injective_of_connected_kernel (f : Q ⟶ G)
    (hf : f.hom.hom.toAlgHom.toRingHom.FaithfullyFlat)
    [ConnectedSpace (PrimeSpectrum
      (CommHopfAlgCat.quotient G.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)))] :
    Function.Injective (mapComponentGroup f) := by
  rw [injective_iff_map_eq_one]
  intro C hC
  obtain ⟨g, rfl⟩ := rationalComponentMap_surjective G C
  rw [mapComponentGroup_rationalComponentMap] at hC
  let h := BialgHom.mapDomain (A := k) f.hom.hom g
  let zQ : PrimeSpectrum Q := Bialgebra.augmentationPoint k Q
  let zG : PrimeSpectrum G := Bialgebra.augmentationPoint k G
  have hmem : rationalKernelPoint Q h ∈
      connectedComponent zQ := by
    apply ConnectedComponents.coe_eq_coe'.mp
    exact (rationalComponentMap_apply Q h).symm.trans
      (hC.trans (rationalKernelPoint_one_component Q).symm)
  -- Descend the source component idempotent and detect it on the target identity component.
  obtain ⟨a, ha⟩ := exists_map_eq_identityComponentIdempotent f hf
  have hidem : IsIdempotentElem a := by
    have hinj : Function.Injective f.hom.hom := hf.injective
    apply hinj
    rw [map_mul, ha]
    exact PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent _
  have hε : (Bialgebra.counitAlgHom k Q) a = 1 := by
    have he := AlgHom.congr_fun (BialgHom.counitAlgHom_comp f.hom.hom) a
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom] at he
    rw [ha, AlgHom.map_connectedComponentIdempotent_kernelPoint_eq_one] at he
    exact he.symm
  have hopen : IsClopen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Q)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨a, hidem, rfl⟩
  have hidentity : (Bialgebra.augmentationPoint k Q : PrimeSpectrum Q) ∈
      PrimeSpectrum.basicOpen a := by
    apply (PrimeSpectrum.mem_basicOpen a _).mpr
    simpa only [Bialgebra.augmentationPoint, AlgHom.kernelPoint_asIdeal, RingHom.mem_ker,
      AlgHom.coe_toRingHom] using (hε.trans_ne one_ne_zero)
  have hnonzero : h.ofConv a ≠ 0 := by
    have hm := hopen.connectedComponent_subset hidentity hmem
    have hm' := (PrimeSpectrum.mem_basicOpen a _).mp hm
    simpa only [rationalKernelPoint, AlgHom.kernelPoint_asIdeal, RingHom.mem_ker,
      AlgHom.coe_toRingHom] using hm'
  have hsource : rationalKernelPoint G g ∈
      connectedComponent zG := by
    rw [← PrimeSpectrum.basicOpen_connectedComponentIdempotent zG]
    apply (PrimeSpectrum.mem_basicOpen _ _).mpr
    have hg : g.ofConv (f.hom.hom a) ≠ 0 := by
      simpa only [h, BialgHom.mapDomain_apply, WithConv.ofConv_toConv,
        AlgHom.comp_apply, BialgHom.coe_toAlgHom] using hnonzero
    rw [ha] at hg
    simpa only [rationalKernelPoint, AlgHom.kernelPoint_asIdeal, RingHom.mem_ker,
      AlgHom.coe_toRingHom] using hg
  rw [rationalComponentMap_apply, ← rationalKernelPoint_one_component G]
  exact ConnectedComponents.coe_eq_coe'.mpr hsource

/-- A faithfully flat homomorphism of finite-type affine groups with connected kernel induces
an isomorphism of component groups. Coordinate arrows reverse the displayed equivalence. -/
noncomputable def componentGroupMulEquivOfConnectedKernel (f : Q ⟶ G)
    (hf : f.hom.hom.toAlgHom.toRingHom.FaithfullyFlat)
    [ConnectedSpace (PrimeSpectrum
      (CommHopfAlgCat.quotient G.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)))] :
    ConnectedComponents (PrimeSpectrum G) ≃* ConnectedComponents (PrimeSpectrum Q) :=
  MulEquiv.ofBijective (mapComponentGroup f)
    ⟨mapComponentGroup_injective_of_connected_kernel f hf,
      mapComponentGroup_surjective_of_injective f hf.injective⟩

/-- The equivalence for a connected kernel is the canonical component homomorphism.
Use with `rw`: keeping equivalence applications intact lets `simp` cancel inverse pairs. -/
theorem componentGroupMulEquivOfConnectedKernel_apply (f : Q ⟶ G)
    (hf : f.hom.hom.toAlgHom.toRingHom.FaithfullyFlat)
    [ConnectedSpace (PrimeSpectrum
      (CommHopfAlgCat.quotient G.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)))]
    (C : ConnectedComponents (PrimeSpectrum G)) :
    componentGroupMulEquivOfConnectedKernel f hf C = mapComponentGroup f C :=
  (rfl)

end TauCeti.FiniteTypeCommHopfAlgCat
