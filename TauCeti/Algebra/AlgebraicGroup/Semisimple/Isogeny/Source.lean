/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Quotient
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange

/-!
# Semisimplicity of the source of an isogeny

A smooth geometrically connected finite-type affine group admitting an isogeny to a
semisimple group is semisimple. Centrality of the isogeny is unnecessary in this direction:
the source radical maps trivially to the target, so it lies in the finite kernel. A finite
connected smooth group is trivial.

Combining this with preservation of semisimplicity under central quotients gives invariance
under central isogenies between smooth geometrically connected groups. The explicit source
hypotheses matter: adjoining a finite disconnected or infinitesimal factor to a semisimple
group gives an isogeny whose source need not be semisimple. No smoothness or reducedness of
the kernel is assumed, so inseparable isogenies are included.

The radical calculation is stated over the ground field and only requires injectivity of
the coordinate map and finiteness of the kernel. The semisimplicity theorem applies it after
extension to an algebraic closure, keeping the geometric notion of semisimplicity.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_eq_augmentation_of_finite_kernel`:
  a dominant homomorphism with finite kernel to a group with trivial radical has trivial
  source radical.
* `TauCeti.semisimpleCommHopfAlgProperty.of_isIsogeny`: the smooth geometrically connected
  source of an isogeny to a semisimple group is semisimple.
* `TauCeti.semisimpleCommHopfAlgProperty_iff_of_isCentralIsogeny`: semisimplicity is
  invariant under a central isogeny with smooth geometrically connected source.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 21, semisimple groups and isogenies.
* A. Borel, *Linear Algebraic Groups*, §11, solvable radicals.

The radical-image step uses
`TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Quotient`; the finite-kernel step uses
`TauCeti.HopfIdeal.augmentation_eq_bot_of_moduleFinite`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace semisimpleCommHopfAlgProperty

variable {k : Type u} [Field k] {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The smooth geometrically connected source of an isogeny to a semisimple affine group is
semisimple. The isogeny need not be central or separable. -/
theorem of_isIsogeny (hQ : semisimpleCommHopfAlgProperty k Q) (f : Q.obj ⟶ G.obj)
    (hf : CommHopfAlgCat.IsIsogeny f) (hsmooth : Algebra.Smooth k G)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj) :
    semisimpleCommHopfAlgProperty k G := by
  rw [semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation]
  refine ⟨hsmooth, hconnected, ?_⟩
  let K := AlgebraicClosure k
  have hfK := hf.baseChange (L := K)
  let _ := CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal hfK.finite
  exact FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_eq_augmentation_of_finite_kernel
    (CommHopfAlgCat.baseChangeMap (K := K) f) hfK.injective
    ((semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation
      k Q).mp hQ).2.2

end semisimpleCommHopfAlgProperty

/-- Semisimplicity is invariant under a central isogeny whose source is smooth and
geometrically connected. No hypothesis on the smoothness of its kernel is needed.

Use `rw [semisimpleCommHopfAlgProperty_iff_of_isCentralIsogeny f hf hsmooth hconnected]`
to transport semisimplicity along a specified central isogeny. -/
theorem semisimpleCommHopfAlgProperty_iff_of_isCentralIsogeny
    {k : Type u} [Field k] {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : Q.obj ⟶ G.obj) (hf : CommHopfAlgCat.IsCentralIsogeny f)
    (hsmooth : Algebra.Smooth k G)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj) :
    semisimpleCommHopfAlgProperty k Q ↔ semisimpleCommHopfAlgProperty k G :=
  ⟨fun hQ ↦ hQ.of_isIsogeny f hf.isIsogeny hsmooth hconnected,
    fun hG ↦ hG.of_isCentralIsogeny f hf⟩

end

end TauCeti
