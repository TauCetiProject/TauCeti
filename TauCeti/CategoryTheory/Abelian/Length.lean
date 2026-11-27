/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Data.ENat.Monoid
public import TauCeti.CategoryTheory.Subobject.Length
import Mathlib.CategoryTheory.Abelian.Exact
import TauCeti.CategoryTheory.Abelian.SubquotientPresentation
import TauCeti.CategoryTheory.Abelian.Subobject.Modular
import TauCeti.Order.ModularLattice

/-!
# Additivity of length in abelian categories

The length `CategoryTheory.length X` of an object is the Krull dimension of its lattice of
subobjects (`TauCeti.CategoryTheory.Subobject.Length`). In an abelian category the subobject
lattice of an object is modular, so an object has finite length exactly when it has a composition
series, whose length is then the length of the object (`Order.krullDim_eq_length_of_covBy`). This
file proves that in an abelian category the length is additive on short exact sequences, and
records the consequences for monomorphisms, epimorphisms and images that the Harada–Sai lemma
uses.

## Main results

* `CategoryTheory.length_eq_add_of_shortExact`: **additivity of length** on short exact sequences.
* `CategoryTheory.length_eq_add_length_cokernel` and `CategoryTheory.length_eq_length_kernel_add`:
  the length of the target of a monomorphism (the source of an epimorphism) splits along its
  cokernel (kernel).
* `CategoryTheory.length_le_of_epi`: length is antitone along epimorphisms.
* `CategoryTheory.isIso_of_mono_of_length_eq` and `CategoryTheory.isIso_of_epi_of_length_eq`: a
  monomorphism or an epimorphism between objects of the same finite length is an isomorphism.
* `CategoryTheory.length_image_le_left`: the image of `f : X ⟶ Y` is at most as long as `X`.
* `CategoryTheory.mono_of_length_image_eq` and `CategoryTheory.epi_of_length_image_eq`: a
  morphism whose image is as long as its finite-length source (target) is a monomorphism
  (epimorphism).

## Implementation notes

For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `a` the subobject of `X₂` represented by
`X₁ ⟶ X₂`, the subobjects of `X₁` are the subobjects of `X₂` below `a`
(`CategoryTheory.Subobject.subobjectOrderIso`) and, by the correspondence theorem, those of `X₃`
are the subobjects of `X₂` above `a` (`TauCeti.SubquotientPresentation.orderIso`). Additivity is
then the additivity of Krull dimension in the modular lattice `Subobject X₂`
(`Order.krullDim_eq_krullDim_Iic_add_krullDim_Ici`). Images are Mathlib's
`CategoryTheory.Limits.image`, with `Limits.factorThruImage f` an epimorphism and
`Limits.image.ι f` a monomorphism. The statements about isomorphisms assume finite length.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Chapter VI, Section 1.
-/

public section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C]

section Abelian

variable [Abelian C] {X Y : C}

/-- **Length is additive on short exact sequences**: if `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is exact, then
`length X₂ = length X₁ + length X₃`. -/
theorem length_eq_add_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    length S.X₂ = length S.X₁ + length S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have hker : kernelSubobject S.g = Subobject.mk S.f := by
    rw [← imageSubobject_mono]
    exact (S.exact_iff_image_eq_kernel.1 hS.exact).symm
  -- `X₃` is presented inside `X₂` by the subobjects `mk S.f ≤ ⊤`, with projection `S.g`.
  let P := TauCeti.SubquotientPresentation.ofEpi (le_top : Subobject.mk S.f ≤ ⊤)
    ((⊤ : Subobject S.X₂).arrow ≫ S.g)
    (by rw [← Subobject.pullback_bot, Subobject.pullback_comp, Subobject.pullback_bot, hker])
  refine WithBot.coe_injective ?_
  rw [WithBot.coe_add, coe_length, coe_length, coe_length,
    Order.krullDim_eq_krullDim_Iic_add_krullDim_Ici (Subobject.mk S.f),
    Order.krullDim_eq_of_orderIso ((Subobject.mapIsoToOrderIso
      (Subobject.underlyingIso S.f).symm).trans (Subobject.subobjectOrderIso _)),
    Order.krullDim_eq_of_orderIso (P.orderIso.trans (Set.orderIsoOfEq _ _ Set.Icc_top))]
  rfl

/-- The target of a monomorphism is as long as its source plus its cokernel. -/
theorem length_eq_add_length_cokernel (f : X ⟶ Y) [Mono f] :
    length Y = length X + length (cokernel f) :=
  length_eq_add_of_shortExact (S := ShortComplex.mk f (cokernel.π f) (by simp))
    (.mk' (ShortComplex.exact_cokernel f) inferInstance inferInstance)

/-- The source of an epimorphism is as long as its kernel plus its target. -/
theorem length_eq_length_kernel_add (f : X ⟶ Y) [Epi f] :
    length X = length (kernel f) + length Y :=
  length_eq_add_of_shortExact (S := ShortComplex.mk (kernel.ι f) f (by simp))
    (.mk' (ShortComplex.exact_kernel f) inferInstance inferInstance)

/-- **Length is antitone along epimorphisms.** -/
theorem length_le_of_epi (f : X ⟶ Y) [Epi f] : length Y ≤ length X := by
  rw [length_eq_length_kernel_add f]
  exact le_add_self

/-- **A monomorphism between objects of the same finite length is an isomorphism.** -/
theorem isIso_of_mono_of_length_eq (f : X ⟶ Y) [Mono f] (h : length X = length Y)
    (hX : length X ≠ ⊤) : IsIso f := by
  have hc : length (cokernel f) = 0 := by
    have := length_eq_add_length_cokernel f
    rw [← h] at this
    exact (add_right_inj_of_ne_top hX).mp (this.symm.trans (add_zero _).symm)
  have : Epi f := (Preadditive.epi_iff_isZero_cokernel f).mpr (length_eq_zero_iff.mp hc)
  exact isIso_of_mono_of_epi f

/-- **An epimorphism between objects of the same finite length is an isomorphism.** -/
theorem isIso_of_epi_of_length_eq (f : X ⟶ Y) [Epi f] (h : length X = length Y)
    (hY : length Y ≠ ⊤) : IsIso f := by
  have hk : length (kernel f) = 0 := by
    have := length_eq_length_kernel_add f
    rw [h] at this
    exact (add_left_inj_of_ne_top hY).mp (this.symm.trans (zero_add _).symm)
  have : Mono f := (Preadditive.mono_iff_isZero_kernel f).mpr (length_eq_zero_iff.mp hk)
  exact isIso_of_mono_of_epi f

/-- **The image of a morphism is at most as long as its source.** -/
theorem length_image_le_left (f : X ⟶ Y) : length (image f) ≤ length X :=
  length_le_of_epi (factorThruImage f)

/-- **A morphism whose image is as long as its source is a monomorphism**, when the source has
finite length. -/
theorem mono_of_length_image_eq (f : X ⟶ Y) (h : length (image f) = length X)
    (hX : length X ≠ ⊤) : Mono f := by
  have := isIso_of_epi_of_length_eq (factorThruImage f) h.symm (h ▸ hX)
  rw [← image.fac f]
  infer_instance

/-- **A morphism whose image is as long as its target is an epimorphism**, when the target has
finite length. -/
theorem epi_of_length_image_eq (f : X ⟶ Y) (h : length (image f) = length Y)
    (hY : length Y ≠ ⊤) : Epi f := by
  have := isIso_of_mono_of_length_eq (image.ι f) h (h ▸ hY)
  rw [← image.fac f]
  infer_instance

end Abelian

end CategoryTheory
