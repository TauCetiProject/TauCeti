/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Kernels of composite affine group morphisms

For affine group morphisms `G → H → Q`, restriction gives `ker(G → Q) → ker(H → Q)`.
Its scheme-theoretic kernel is `ker(G → H)`. If `G → H` is faithfully flat and finitely
presented, so is this restriction, giving the short exact sequence of kernels in the fppf
topology. We construct the restriction in Hopf coordinates and identify its kernel ideal.

All statements hold over an arbitrary commutative base ring, including for nonreduced groups.
The coordinates of the restriction are obtained by base change along the quotient defining
`ker(H → Q)`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, exact sequences of affine groups.
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u v

variable {R : Type u} [CommRing R] {H K L : _root_.CommHopfAlgCat.{v} R}

/-- The coordinate morphism of the restriction `ker(Spec L → Spec H) → ker(Spec K → Spec H)`
of the group morphism represented by `g`. -/
noncomputable def kernelCompositeMap (f : H ⟶ K) (g : K ⟶ L) :
    quotient K (kernelHopfIdeal f) ⟶ quotient L (kernelHopfIdeal (f ≫ g)) :=
  liftQuotient (kernelHopfIdeal f) (g ≫ mkQuotient L (kernelHopfIdeal (f ≫ g))) (by
    intro x hx
    apply (mkQuotient_eq_zero_iff L (kernelHopfIdeal (f ≫ g)) (g.hom x)).mpr
    rw [kernelHopfIdeal_comp]
    exact HopfIdeal.mem_map_of_mem g.hom (HopfIdeal.mem_toIdeal.mp hx))

/-- The restriction on kernels sends a quotient representative to the class of its image. -/
@[simp]
theorem kernelCompositeMap_mk (f : H ⟶ K) (g : K ⟶ L) (x : K) :
    (kernelCompositeMap f g).hom (Ideal.Quotient.mk (kernelHopfIdeal f).toIdeal x) =
      Ideal.Quotient.mk (kernelHopfIdeal (f ≫ g)).toIdeal (g.hom x) := by
  exact (liftQuotient_mk (kernelHopfIdeal f)
    (g ≫ mkQuotient L (kernelHopfIdeal (f ≫ g))) _ x).trans
    (mkQuotient_apply L (kernelHopfIdeal (f ≫ g)) (g.hom x))

/-- Restriction to kernels commutes with their inclusions into the ambient groups. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_kernelCompositeMap (f : H ⟶ K) (g : K ⟶ L) :
    mkQuotient K (kernelHopfIdeal f) ≫ kernelCompositeMap f g =
      g ≫ mkQuotient L (kernelHopfIdeal (f ≫ g)) := by
  exact mkQuotient_comp_liftQuotient _ _ _

/-- Restriction along the identity is the identity after identifying its target quotient. -/
@[simp]
theorem kernelCompositeMap_id (f : H ⟶ K) :
    kernelCompositeMap f (𝟙 K) =
      eqToHom (congrArg (quotient K)
        (congrArg kernelHopfIdeal (Category.comp_id f)).symm) := by
  apply mkQuotient_hom_ext
  rw [mkQuotient_comp_kernelCompositeMap, Category.id_comp]
  exact (mkQuotient_comp_eqToHom (congrArg kernelHopfIdeal (Category.comp_id f))).symm

/-- Successive restrictions agree with restriction along the composite, after identifying
the target quotients by associativity. -/
@[simp]
theorem kernelCompositeMap_comp {M : _root_.CommHopfAlgCat.{v} R}
    (f : H ⟶ K) (g : K ⟶ L) (h : L ⟶ M) :
    kernelCompositeMap f g ≫ kernelCompositeMap (f ≫ g) h =
      kernelCompositeMap f (g ≫ h) ≫ eqToHom (congrArg (quotient M)
        (congrArg kernelHopfIdeal (Category.assoc f g h)).symm) := by
  apply mkQuotient_hom_ext
  simp only [← Category.assoc, mkQuotient_comp_kernelCompositeMap]
  simp only [Category.assoc, mkQuotient_comp_kernelCompositeMap, mkQuotient_comp_eqToHom]

private theorem kernelCompositeMap_eq_quotientMap (f : H ⟶ K) (g : K ⟶ L) :
    kernelCompositeMap f g =
      quotientMap (kernelHopfIdeal f) (kernelHopfIdeal (f ≫ g)) g
        (by rw [← kernelHopfIdeal_comp]) := by
  apply mkQuotient_hom_ext
  rw [mkQuotient_comp_kernelCompositeMap, mkQuotient_comp_quotientMap]

/-- The kernel of the restriction on composite kernels is the original kernel, viewed as a
closed subgroup of the composite kernel. -/
@[simp]
theorem kernelHopfIdeal_kernelCompositeMap (f : H ⟶ K) (g : K ⟶ L) :
    kernelHopfIdeal (kernelCompositeMap f g) =
      (kernelHopfIdeal g).map (mkQuotient L (kernelHopfIdeal (f ≫ g))).hom := by
  rw [kernelCompositeMap_eq_quotientMap]
  exact kernelHopfIdeal_quotientMap (kernelHopfIdeal f) (kernelHopfIdeal (f ≫ g)) g
    (by rw [← kernelHopfIdeal_comp])

/-- The scheme-theoretic kernel of the restriction on composite kernels is isomorphic to
the original kernel, including its possibly nonreduced scheme structure. -/
noncomputable def kernelCompositeKernelIso (f : H ⟶ K) (g : K ⟶ L) :
    quotient (quotient L (kernelHopfIdeal (f ≫ g)))
        (kernelHopfIdeal (kernelCompositeMap f g)) ≅ quotient L (kernelHopfIdeal g) :=
  eqToIso (congrArg (quotient _)
      (congrArg kernelHopfIdeal (kernelCompositeMap_eq_quotientMap f g))) ≪≫
    (kernelQuotientMapIsoOfLe (kernelHopfIdeal f) (kernelHopfIdeal (f ≫ g)) g
      (by rw [← kernelHopfIdeal_comp]) (kernelHopfIdeal_comp_le f g)).symm

/-- The kernel identification respects the inclusion into the composite kernel. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_kernelCompositeKernelIso_hom (f : H ⟶ K) (g : K ⟶ L) :
    mkQuotient (quotient L (kernelHopfIdeal (f ≫ g)))
        (kernelHopfIdeal (kernelCompositeMap f g)) ≫ (kernelCompositeKernelIso f g).hom =
      quotientMapOfLe L (kernelHopfIdeal_comp_le f g) := by
  rw [kernelCompositeKernelIso, Iso.trans_hom, ← Category.assoc, eqToIso.hom,
    mkQuotient_comp_eqToHom (congrArg kernelHopfIdeal (kernelCompositeMap_eq_quotientMap f g)).symm,
    Iso.symm_hom, Iso.comp_inv_eq]
  exact (quotientMapOfLe_comp_kernelQuotientMapIsoOfLe_hom
    (kernelHopfIdeal f) (kernelHopfIdeal (f ≫ g)) g (by rw [← kernelHopfIdeal_comp])
    (kernelHopfIdeal_comp_le f g)).symm

/-- A faithfully flat affine group morphism remains faithfully flat on composite kernels. -/
theorem faithfullyFlat_kernelCompositeMap (f : H ⟶ K) (g : K ⟶ L)
    (hg : g.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    (kernelCompositeMap f g).hom.toAlgHom.toRingHom.FaithfullyFlat := by
  rw [kernelCompositeMap_eq_quotientMap]
  exact quotientMap_property RingHom.FaithfullyFlat.isStableUnderBaseChange
    RingHom.FaithfullyFlat.respectsIso (kernelHopfIdeal f) (kernelHopfIdeal (f ≫ g)) g
    (kernelHopfIdeal_comp f g).symm hg

/-- A finitely presented affine group morphism remains finitely presented on composite kernels. -/
theorem finitePresentation_kernelCompositeMap (f : H ⟶ K) (g : K ⟶ L)
    (hg : g.hom.toAlgHom.toRingHom.FinitePresentation) :
    (kernelCompositeMap f g).hom.toAlgHom.toRingHom.FinitePresentation := by
  rw [kernelCompositeMap_eq_quotientMap]
  exact quotientMap_property RingHom.finitePresentation_isStableUnderBaseChange
    RingHom.finitePresentation_respectsIso (kernelHopfIdeal f) (kernelHopfIdeal (f ≫ g)) g
    (kernelHopfIdeal_comp f g).symm hg

end TauCeti.CommHopfAlgCat
