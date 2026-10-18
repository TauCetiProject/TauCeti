/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Coordinate
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
  obtain ⟨a, hidem, ha⟩ := f.hom.exists_map_eq_identityComponentIdempotent hf
  -- Its counit is one, so its clopen basic open contains the target identity component.
  have hε : (Bialgebra.counitAlgHom k Q) a = 1 := by
    have he := AlgHom.congr_fun (BialgHom.counitAlgHom_comp f.hom.hom) a
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom] at he
    rw [ha, AlgHom.map_connectedComponentIdempotent_kernelPoint_eq_one] at he
    exact he.symm
  have hopen : IsClopen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Q)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨a, hidem, rfl⟩
  have hidentity : (Bialgebra.augmentationPoint k Q : PrimeSpectrum Q) ∈
      PrimeSpectrum.basicOpen a :=
    (AlgHom.kernelPoint_mem_basicOpen_iff (Bialgebra.counitAlgHom k Q) a).mpr
      (hε.trans_ne one_ne_zero)
  have hnonzero : h.ofConv a ≠ 0 :=
    (AlgHom.kernelPoint_mem_basicOpen_iff h.ofConv a).mp
      (hopen.connectedComponent_subset hidentity hmem)
  -- Pull back to the source to detect the kernel of the component homomorphism.
  have hsource : rationalKernelPoint G g ∈
      connectedComponent zG := by
    rw [← PrimeSpectrum.basicOpen_connectedComponentIdempotent zG]
    apply (AlgHom.kernelPoint_mem_basicOpen_iff g.ofConv _).mpr
    have hg : g.ofConv (f.hom.hom a) ≠ 0 := by
      simpa only [h, BialgHom.mapDomain_apply, WithConv.ofConv_toConv,
        AlgHom.comp_apply, BialgHom.coe_toAlgHom] using hnonzero
    rw [ha] at hg
    exact hg
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
