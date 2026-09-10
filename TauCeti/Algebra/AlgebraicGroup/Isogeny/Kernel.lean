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
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CommHopfAlgCat

universe u v

variable {R : Type u} [CommRing R]

namespace IsIsogeny

variable {H K : _root_.CommHopfAlgCat.{v} R} {f : H ⟶ K}

/-- The coordinate algebra of the kernel is finite as a module over the base when the coordinate
map is finite. -/
theorem moduleFinite_quotient_kernelHopfIdeal (hf : f.hom.toAlgHom.Finite) :
    Module.Finite R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  let : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
  let : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
  let _ : Module.Finite ↥H ↥K := hf
  let _ : Module.Finite R (TensorProduct ↥H R ↥K) := inferInstance
  let _ : Module.Finite R (TensorProduct ↥H ↥K R) :=
    Module.Finite.equiv
      ((_root_.TensorProduct.comm ↥H R ↥K).restrictScalars R)
  exact Module.Finite.equiv
    ((quotientKernelHopfIdealAlgEquiv f).restrictScalars R).toLinearEquiv.symm

/-- The coordinate algebra of the kernel is faithfully flat over the base when the coordinate
map is faithfully flat. -/
theorem faithfullyFlat_quotient_kernelHopfIdeal
    (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    Module.FaithfullyFlat R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  let : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
  let : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
  let _ : Module.FaithfullyFlat ↥H ↥K := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    exact hf
  let _ : Module.FaithfullyFlat R (TensorProduct ↥H R ↥K) := inferInstance
  let _ : Module.FaithfullyFlat R (TensorProduct ↥H ↥K R) :=
    Module.FaithfullyFlat.of_linearEquiv R _
      ((_root_.TensorProduct.comm ↥H R ↥K).symm.restrictScalars R)
  exact Module.FaithfullyFlat.of_linearEquiv R _
    ((quotientKernelHopfIdealAlgEquiv f).restrictScalars R).toLinearEquiv

section Scheme

variable {H K : _root_.CommHopfAlgCat.{u} R} {f : H ⟶ K}

/-- The structural morphism from the represented kernel of an isogeny to the trivial group
scheme is itself an isogeny. Equivalently, the kernel is a finite faithfully flat group scheme
over the base. -/
theorem isIsogeny_kernelSpec_to_trivial (hf : IsIsogeny f) :
    GroupScheme.IsIsogeny
      (0 : kernelSpec f ⟶ Grp.trivial
        (Over (AlgebraicGeometry.Spec (CommRingCat.of R)))) := by
  rw [GroupScheme.isIsogeny_iff]
  have hfinite :
      AlgebraicGeometry.IsFinite
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal)))) :=
    (AlgebraicGeometry.IsFinite.SpecMap_iff _).2
      (RingHom.finite_algebraMap.mpr (moduleFinite_quotient_kernelHopfIdeal hf.finite))
  have hflatSurjective :
      AlgebraicGeometry.Flat
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal)))) ∧
        AlgebraicGeometry.Surjective
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal)))) :=
    (AlgebraicGeometry.flat_and_surjective_SpecMap_iff _).2
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (faithfullyFlat_quotient_kernelHopfIdeal hf.faithfullyFlat))
  simpa only [kernelSpec_to_trivial_underlying] using ⟨hfinite, hflatSurjective⟩

end Scheme

end IsIsogeny

namespace IsCentralIsogeny

section Field

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{u} k} {f : H ⟶ K}

/-- Over a field, package the kernel of a central isogeny as a finite locally free
bicommutative Hopf algebra, ready for Cartier duality. -/
noncomputable abbrev kernelFiniteLocallyFree (hf : IsCentralIsogeny f) :
    FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k :=
  ⟨quotient K (kernelHopfIdeal f),
    (finiteLocallyFreeBicommutativeHopfAlgProperty_iff k _).2
      ⟨IsIsogeny.moduleFinite_quotient_kernelHopfIdeal hf.isIsogeny.finite, inferInstance,
        hf.isCocomm_quotient_kernelHopfIdeal⟩⟩

end Field

end IsCentralIsogeny

end TauCeti.CommHopfAlgCat
