/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Composite

import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness

/-!
# Inverse images of normal subgroups under quotient homomorphisms

Let `p : G → Q` be a faithfully flat homomorphism of affine groups over a field, represented by a
coordinate morphism `Q ⟶ G`, and let `N ⊆ Q` be a normal closed subgroup cut out by a Hopf ideal
`J`. The inverse image `p⁻¹(N)` is cut out by the extended ideal `J.map p`, and it sits in an
extension of `N` by `ker p`.

This file records two consequences used to compare radicals of `G` and of its quotient `Q`.
First, any property of affine groups that is invariant under isomorphism and closed under
faithfully flat extensions holds for `p⁻¹(N)` as soon as it holds for `N` and for `ker p`.
Second, a closed subgroup of `Q` whose inverse image lies in `ker p` is trivial.

To realize `N` as a kernel, the target `Q` is assumed geometrically reduced and of finite type,
so that the projection onto the coinvariant quotient `Q ⧸ N` has kernel exactly `N`.

## Main declarations

* `TauCeti.CommHopfAlgCat.prop_quotient_map_of_kernel`: a property closed under faithfully flat
  extensions passes to inverse images of normal subgroups.
* `TauCeti.CommHopfAlgCat.eq_augmentation_of_kernelHopfIdeal_le_map`: a closed subgroup whose
  inverse image lies in the kernel of a faithfully flat homomorphism is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.c and Chapter 19.
-/

public section

open CategoryTheory
open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

namespace TauCeti.CommHopfAlgCat

universe u v

section CommRing

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- Along a faithfully flat coordinate morphism `p : H ⟶ K`, a Hopf ideal `J` of `H` whose
extension contains the kernel Hopf ideal is the augmentation ideal. Geometrically, a closed
subgroup of the quotient group `Spec H` whose inverse image in `Spec K` lies in the kernel of the
quotient homomorphism is the identity subgroup. -/
theorem eq_augmentation_of_kernelHopfIdeal_le_map (p : H ⟶ K)
    (hp : p.hom.toAlgHom.toRingHom.FaithfullyFlat) {J : HopfIdeal R H}
    (hJ : kernelHopfIdeal p ≤ J.map p.hom) :
    J = HopfIdeal.augmentation R H := by
  refine le_antisymm (HopfIdeal.le_augmentation R H J) fun x hx ↦ ?_
  rw [kernelHopfIdeal_def] at hJ
  let := p.hom.toAlgHom.toAlgebra
  let _ : Module.FaithfullyFlat H K := hp
  have hmap : p.hom x ∈ (J.map p.hom).toIdeal :=
    hJ (HopfIdeal.mem_map_of_mem p.hom hx)
  rw [HopfIdeal.map_toIdeal] at hmap
  have hx' : x ∈ (J.toIdeal.map (algebraMap H K)).comap (algebraMap H K) := by
    rwa [Ideal.mem_comap, RingHom.algebraMap_toAlgebra]
  rwa [Ideal.comap_map_eq_self_of_faithfullyFlat J.toIdeal] at hx'

end CommRing

section Field

variable {k : Type u} [Field k] {Q G : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k Q] [Algebra.FiniteType k G] [Algebra.IsGeometricallyReduced k Q]

/-- **Inverse images of normal subgroups.** Let `p : Q ⟶ G` represent a faithfully flat
homomorphism `Spec G → Spec Q` and let `J` cut out a normal closed subgroup of `Spec Q`. A
property of affine groups that is invariant under isomorphism and closed under faithfully flat
extensions holds for the inverse image, cut out by `J.map p`, whenever it holds for the subgroup
cut out by `J` and for the kernel of `p`.

The extension hypothesis `hP` is stated for an arbitrary faithfully flat coordinate morphism
`r : A ⟶ B`: the property passes from the target `Spec A` and the kernel to the source `Spec B`. -/
theorem prop_quotient_map_of_kernel (P : ObjectProperty (_root_.CommHopfAlgCat.{u} k))
    [P.IsClosedUnderIsomorphisms]
    (hP : ∀ {A B : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k B] (r : A ⟶ B),
      r.hom.toAlgHom.toRingHom.FaithfullyFlat → P A →
        P (CommHopfAlgCat.quotient B (kernelHopfIdeal r)) → P B)
    {J : HopfIdeal k Q} (hJ : J.IsNormal) (p : Q ⟶ G)
    (hp : p.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hQJ : P (CommHopfAlgCat.quotient Q J))
    (hker : P (CommHopfAlgCat.quotient G (kernelHopfIdeal p))) :
    P (CommHopfAlgCat.quotient G (J.map p.hom)) := by
  -- Realize the normal subgroup as the kernel of the coinvariant projection `f`; its inverse
  -- image is then the kernel of `f ≫ p`, an extension of `ker f` by `ker p`.
  let f := coinvariantsι hJ
  have hf : kernelHopfIdeal f = J := kernelHopfIdeal_coinvariantsι_eq hJ
  have hpre : kernelHopfIdeal (f ≫ p) = J.map p.hom := by
    rw [kernelHopfIdeal_comp, hf]
  rw [← hpre]
  refine hP (kernelCompositeMap f p) (faithfullyFlat_kernelCompositeMap f p hp) ?_
    (P.prop_of_iso (kernelCompositeKernelIso f p).symm hker)
  rwa [hf]

end Field

end TauCeti.CommHopfAlgCat
