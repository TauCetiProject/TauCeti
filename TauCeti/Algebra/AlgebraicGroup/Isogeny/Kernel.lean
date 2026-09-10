/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Kernel
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.CartierDuality.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange

/-!
# Kernels of isogenies

The kernel of an isogeny of affine group schemes is finite and faithfully flat over the base.
In Hopf coordinates, if `f : H ⟶ K` is finite and faithfully flat, the kernel coordinate
ring is the quotient `K ⧸ K·f(H⁺)`. The quotient--tensor comparison identifies this algebra with
`K ⊗[H] R`; finiteness and faithful flatness then follow by base change.

The same result is also recorded intrinsically for the represented affine group schemes. The
kernel square is a pullback of the isogeny along the identity section, so each of finiteness,
flatness, and surjectivity is inherited by the structural morphism of the kernel.

## Main declarations

* `TauCeti.CommHopfAlgCat.IsIsogeny.moduleFinite_quotient_kernelHopfIdeal`: the kernel
  coordinate algebra is finite over the base.
* `TauCeti.CommHopfAlgCat.IsIsogeny.faithfullyFlat_quotient_kernelHopfIdeal`: the kernel
  coordinate algebra is faithfully flat over the base.
* `TauCeti.CommHopfAlgCat.IsIsogeny.isIsogeny_kernelSpec_to_trivial`: the structural
  morphism from the represented kernel to the trivial group scheme is an isogeny.
* `TauCeti.CommHopfAlgCat.IsCentralIsogeny.kernelFiniteLocallyFree`: over a field, the
  kernel of a central isogeny as a finite locally free bicommutative Hopf algebra.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 4.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.21.

This supplies the finite-kernel consequence needed by the central-isogeny and simply-connected
cover targets in Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]
variable {H K : _root_.CommHopfAlgCat.{u} R} {f : H ⟶ K}

namespace IsIsogeny

/-- The coordinate algebra of the kernel of an isogeny is finite as a module over the base.

Under `quotientKernelHopfIdealAlgEquiv`, this is the base change of the finite `H`-module `K`
along the counit `H → R`. -/
theorem moduleFinite_quotient_kernelHopfIdeal (hf : IsIsogeny f) :
    Module.Finite R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  let : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
  let : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
  let _ : Module.Finite ↥H ↥K := hf.finite
  let _ : Module.Finite R (TensorProduct ↥H R ↥K) := inferInstance
  let _ : Module.Finite R (TensorProduct ↥H ↥K R) :=
    Module.Finite.equiv
      ((_root_.TensorProduct.comm ↥H R ↥K).restrictScalars R)
  exact Module.Finite.equiv
    ((quotientKernelHopfIdealAlgEquiv f).restrictScalars R).toLinearEquiv.symm

/-- The coordinate algebra of the kernel of an isogeny is faithfully flat over the base.

This is faithful-flat base change of `K` along the counit `H → R`, transported across the
quotient--tensor comparison. -/
theorem faithfullyFlat_quotient_kernelHopfIdeal (hf : IsIsogeny f) :
    Module.FaithfullyFlat R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  let : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
  let : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
  let _ : Module.FaithfullyFlat ↥H ↥K := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    exact hf.faithfullyFlat
  let _ : Module.FaithfullyFlat R (TensorProduct ↥H R ↥K) := inferInstance
  let _ : Module.FaithfullyFlat R (TensorProduct ↥H ↥K R) :=
    Module.FaithfullyFlat.of_linearEquiv R _
      ((_root_.TensorProduct.comm ↥H R ↥K).symm.restrictScalars R)
  exact Module.FaithfullyFlat.of_linearEquiv R _
    ((quotientKernelHopfIdealAlgEquiv f).restrictScalars R).toLinearEquiv

/-- The structural ring map of the kernel coordinate algebra of an isogeny is finite. -/
theorem finite_algebraMap_quotient_kernelHopfIdeal (hf : IsIsogeny f) :
    (algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal)).Finite := by
  rw [RingHom.finite_algebraMap]
  exact hf.moduleFinite_quotient_kernelHopfIdeal

/-- The structural ring map of the kernel coordinate algebra of an isogeny is faithfully
flat. -/
theorem faithfullyFlat_algebraMap_quotient_kernelHopfIdeal (hf : IsIsogeny f) :
    (algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal)).FaithfullyFlat := by
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact hf.faithfullyFlat_quotient_kernelHopfIdeal

/-- The structural morphism from the represented kernel of an isogeny to the trivial group
scheme is itself an isogeny. Equivalently, the kernel is a finite faithfully flat group scheme
over the base. -/
theorem isIsogeny_kernelSpec_to_trivial (hf : IsIsogeny f) :
    GroupScheme.IsIsogeny
      (0 : kernelSpec f ⟶ Grp.trivial
        (Over (AlgebraicGeometry.Spec (CommRingCat.of R)))) := by
  rw [GroupScheme.isIsogeny_iff]
  change
    AlgebraicGeometry.IsFinite
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal)))) ∧
      AlgebraicGeometry.Flat
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal)))) ∧
        AlgebraicGeometry.Surjective
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal))))
  rw [AlgebraicGeometry.IsFinite.SpecMap_iff,
    AlgebraicGeometry.flat_and_surjective_SpecMap_iff]
  exact ⟨hf.finite_algebraMap_quotient_kernelHopfIdeal,
    hf.faithfullyFlat_algebraMap_quotient_kernelHopfIdeal⟩

end IsIsogeny

namespace IsCentralIsogeny

section Field

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{u} k} {f : H ⟶ K}

/-- Over a field, the kernel coordinate algebra of a central isogeny is finite locally free and
bicommutative. This is the object property on which affine Cartier duality is defined. -/
theorem finiteLocallyFreeBicommutativeHopfAlgProperty_kernel (hf : IsCentralIsogeny f) :
    finiteLocallyFreeBicommutativeHopfAlgProperty k
      (quotient K (kernelHopfIdeal f)) := by
  rw [finiteLocallyFreeBicommutativeHopfAlgProperty_iff]
  exact ⟨hf.isIsogeny.moduleFinite_quotient_kernelHopfIdeal, inferInstance,
    hf.isCocomm_quotient_kernelHopfIdeal⟩

/-- Over a field, package the kernel of a central isogeny as a finite locally free
bicommutative Hopf algebra, ready for Cartier duality. -/
noncomputable def kernelFiniteLocallyFree (hf : IsCentralIsogeny f) :
    FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k :=
  ⟨quotient K (kernelHopfIdeal f),
    hf.finiteLocallyFreeBicommutativeHopfAlgProperty_kernel⟩

end Field

end IsCentralIsogeny

end TauCeti.CommHopfAlgCat
