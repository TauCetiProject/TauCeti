/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Image
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Image
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange

/-!
# Reductivity of isogeny covers

A smooth geometrically connected finite-type affine group admitting an isogeny to a reductive
group is reductive. This applies to inseparable isogenies as well as separable ones: after
extension to an algebraic closure, the source unipotent radical maps trivially to the target,
so it lies in the finite scheme-theoretic kernel. A finite smooth connected group is trivial.

Smoothness and geometric connectedness of the source remain explicit. They do not follow from
an arbitrary isogeny with reductive target. Centrality and reducedness of the kernel are not
needed. This result allows reductivity to be checked on an isogenous model when constructing
central-isogeny forms.

In characteristic zero the reverse implication holds as well: reductivity descends along
the injective coordinate map of an isogeny. Thus reductivity is invariant under isogenies
with geometrically connected source. Cartier's theorem makes the source automatically
smooth. Geometric connectedness of the source is still necessary: a nontrivial finite
étale group maps isogenously to the trivial group without being reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 19.
* A. Borel, *Linear Algebraic Groups*, §§11 and 14.
-/

public section

open CategoryTheory

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {G Q : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A smooth geometrically connected affine group admitting an isogeny to a reductive group
is reductive, with no separability or centrality hypothesis on the isogeny. -/
theorem of_isIsogeny_source (hQ : reductiveCommHopfAlgProperty k Q)
    (f : Q.obj ⟶ G.obj) (hf : CommHopfAlgCat.IsIsogeny f)
    (hsmooth : Algebra.Smooth k G)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj) :
    reductiveCommHopfAlgProperty k G := by
  have hQ' :=
    (reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation
      k Q).mp hQ
  rw [reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation]
  refine ⟨hsmooth, hconnected, ?_⟩
  let K := AlgebraicClosure k
  let fK := CommHopfAlgCat.baseChangeMap (K := K) f
  have hfK : CommHopfAlgCat.IsIsogeny fK := hf.baseChange
  let _ := CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal hfK.finite
  exact FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_of_finite_kernel
    (FiniteTypeCommHopfAlgCat.baseChange (K := K) G)
    (FiniteTypeCommHopfAlgCat.baseChange (K := K) Q) hQ'.2.2 fK hfK.injective

end TauCeti.reductiveCommHopfAlgProperty

namespace TauCeti

/-- In characteristic zero, reductivity is invariant under an isogeny with geometrically
connected source. Coordinate arrows reverse direction, so the source connectedness
hypothesis is on `G`. No centrality assumption or separate smoothness hypothesis is needed. -/
theorem reductiveCommHopfAlgProperty_iff_of_isIsogeny
    {k : Type u} [Field k] [CharZero k] {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : Q.obj ⟶ G.obj) (hf : CommHopfAlgCat.IsIsogeny f)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj) :
    reductiveCommHopfAlgProperty k Q ↔ reductiveCommHopfAlgProperty k G :=
  ⟨fun hQ ↦ hQ.of_isIsogeny_source f hf
      ((smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k G.obj))
      hconnected,
    fun hG ↦ hG.of_injective f hf.injective⟩

end TauCeti
