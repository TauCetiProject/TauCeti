/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation
import TauCeti.RingTheory.RingHom.Quotient

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
    rw [kernelHopfIdeal_comp, HopfIdeal.map_toIdeal]
    exact Ideal.mem_map_of_mem g.hom.toAlgHom.toRingHom hx)

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

/-- The kernel of the restriction on composite kernels is the original kernel, viewed as a
closed subgroup of the composite kernel. -/
@[simp]
theorem kernelHopfIdeal_kernelCompositeMap (f : H ⟶ K) (g : K ⟶ L) :
    kernelHopfIdeal (kernelCompositeMap f g) =
      (kernelHopfIdeal g).map (mkQuotient L (kernelHopfIdeal (f ≫ g))).hom := by
  rw [← kernelHopfIdeal_comp_of_surjective (mkQuotient K (kernelHopfIdeal f))
    (mkQuotient_surjective K (kernelHopfIdeal f)), mkQuotient_comp_kernelCompositeMap]
  exact kernelHopfIdeal_comp g _

/-- The scheme-theoretic kernel of the restriction on composite kernels is isomorphic to
the original kernel, including its possibly nonreduced scheme structure. -/
noncomputable def kernelCompositeKernelIso (f : H ⟶ K) (g : K ⟶ L) :
    quotient (quotient L (kernelHopfIdeal (f ≫ g)))
        (kernelHopfIdeal (kernelCompositeMap f g)) ≅ quotient L (kernelHopfIdeal g) := by
  let q := quotientMapOfLe L (kernelHopfIdeal_comp_le f g)
  have he : HopfIdeal.kerOfSurjective q.hom (quotientMapOfLe_surjective L
        (kernelHopfIdeal_comp_le f g)) = kernelHopfIdeal (kernelCompositeMap f g) := by
    rw [kernelHopfIdeal_kernelCompositeMap]
    exact kerOfSurjective_quotientMapOfLe L (kernelHopfIdeal_comp_le f g)
  exact eqToIso (congrArg (quotient (quotient L (kernelHopfIdeal (f ≫ g)))) he.symm) ≪≫
    quotientKerOfSurjectiveIso q (quotientMapOfLe_surjective L (kernelHopfIdeal_comp_le f g))

/-- The kernel identification respects the inclusion into the composite kernel. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_kernelCompositeKernelIso_hom (f : H ⟶ K) (g : K ⟶ L) :
    mkQuotient (quotient L (kernelHopfIdeal (f ≫ g)))
        (kernelHopfIdeal (kernelCompositeMap f g)) ≫ (kernelCompositeKernelIso f g).hom =
      quotientMapOfLe L (kernelHopfIdeal_comp_le f g) := by
  simp only [kernelCompositeKernelIso, Iso.trans_hom, eqToIso.hom, ← Category.assoc]
  refine (congrArg (fun t ↦ t ≫ _) (mkQuotient_comp_eqToHom (by
    rw [kernelHopfIdeal_kernelCompositeMap]
    exact kerOfSurjective_quotientMapOfLe L (kernelHopfIdeal_comp_le f g)))).trans ?_
  exact mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _

/-- Properties stable under base change pass to the restriction on composite kernels. -/
private theorem kernelCompositeMap_property
    {P : ∀ {A B : Type v} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hP : RingHom.IsStableUnderBaseChange P) (hiso : RingHom.RespectsIso P)
    (f : H ⟶ K) (g : K ⟶ L) (hg : P g.hom.toAlgHom.toRingHom) :
    P (kernelCompositeMap f g).hom.toAlgHom.toRingHom := by
  let I := (kernelHopfIdeal f).toIdeal
  have he : (kernelHopfIdeal (f ≫ g)).toIdeal = I.map g.hom.toAlgHom.toRingHom := by
    rw [kernelHopfIdeal_comp, HopfIdeal.map_toIdeal]
    rfl
  let e := Ideal.quotientEquivAlgOfEq L he.symm
  have hp := hiso.left (Ideal.quotientMap (I.map g.hom.toAlgHom.toRingHom)
    g.hom.toAlgHom.toRingHom Ideal.le_comap_map) e.toRingEquiv
    (hP.quotientMap hiso g.hom.toAlgHom.toRingHom I hg)
  convert hp using 1
  ext x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, e]
  exact kernelCompositeMap_mk f g x

/-- A faithfully flat affine group morphism remains faithfully flat on composite kernels. -/
theorem faithfullyFlat_kernelCompositeMap (f : H ⟶ K) (g : K ⟶ L)
    (hg : g.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    (kernelCompositeMap f g).hom.toAlgHom.toRingHom.FaithfullyFlat :=
  kernelCompositeMap_property RingHom.FaithfullyFlat.isStableUnderBaseChange
    RingHom.FaithfullyFlat.respectsIso f g hg

/-- A finitely presented affine group morphism remains finitely presented on composite kernels. -/
theorem finitePresentation_kernelCompositeMap (f : H ⟶ K) (g : K ⟶ L)
    (hg : g.hom.toAlgHom.toRingHom.FinitePresentation) :
    (kernelCompositeMap f g).hom.toAlgHom.toRingHom.FinitePresentation :=
  kernelCompositeMap_property RingHom.finitePresentation_isStableUnderBaseChange
    RingHom.finitePresentation_respectsIso f g hg

end TauCeti.CommHopfAlgCat
