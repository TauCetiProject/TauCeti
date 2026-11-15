/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import TauCeti.CategoryTheory.Monoidal.Grp.KernelPair

/-!
# Étale homomorphisms and their kernels

A faithfully flat, quasi-compact homomorphism of group schemes is étale if and only if
its scheme-theoretic kernel is étale over the base. An étale homomorphism always has an étale
kernel, without the fpqc hypotheses. This criterion applies over arbitrary schemes and does
not require commutativity, smoothness, or finiteness of either group.

The kernel is the fibre over the identity, giving the forward implication. The identity
`G ×_H G ≅ ker(f) ×_S G`, with its second projection, gives the converse by fpqc descent
of étaleness. In particular, the criterion transfers étaleness of elliptic torsion to
multiplication on the whole elliptic curve.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
* The kernel-pair identity is `TauCeti.isPullback_mul_of_isPullback_one`; fpqc descent
  is Mathlib's `MorphismProperty.of_isPullback_of_descendsAlong`.
-/

public section

open CategoryTheory Limits CartesianMonoidalCategory AlgebraicGeometry

universe u

namespace CategoryTheory.Grp

variable {S : Scheme.{u}} {G H : Grp (Over S)}

/-- The scheme-theoretic kernel of an étale homomorphism is étale over the base. -/
theorem etale_kernel_hom (f : G ⟶ H) (hf : Etale f.hom.hom.left) :
    Etale (kernel f).X.hom := by
  simpa only [Over.forget_map, Over.toUnit_left] using
    MorphismProperty.of_isPullback (P := @Etale)
      ((TauCeti.GroupScheme.isPullback_kernel_hom f).map (Over.forget S)) hf

/-- An fpqc homomorphism of group schemes is étale exactly when its kernel is étale over
the base. The kernel is scheme-theoretic, so infinitesimal points are included. -/
theorem etale_iff_etale_kernel (f : G ⟶ H) [Surjective f.hom.hom.left]
    [Flat f.hom.hom.left] [QuasiCompact f.hom.hom.left] :
    Etale f.hom.hom.left ↔ Etale (kernel f).X.hom := by
  have hk := TauCeti.GroupScheme.isPullback_kernel_hom f
  constructor
  · exact etale_kernel_hom f
  · intro hK
    let := hK
    have h := (TauCeti.isPullback_mul_of_isPullback_one f.hom.hom
      (kernel.ι f).hom.hom hk).map (Over.forget S)
    have hs : Etale (snd (kernel f).X G.X).left := by
      rw [Over.snd_left]
      infer_instance
    have hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
        f.hom.hom.left := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    exact MorphismProperty.of_isPullback_of_descendsAlong h.flip hf hs

end CategoryTheory.Grp
