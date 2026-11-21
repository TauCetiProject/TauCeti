/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Order.KrullDimension
import Mathlib.CategoryTheory.Abelian.Exact
import TauCeti.CategoryTheory.Abelian.SubquotientPresentation
import TauCeti.CategoryTheory.Abelian.Subobject.Modular
import TauCeti.Order.ModularLattice

/-!
# The length of an object

The **length** of an object `X` of a category is the Krull dimension of its lattice of subobjects,
the supremum of the lengths `n` of strict chains `X₀ < X₁ < ⋯ < Xₙ` of subobjects, in `ℕ∞`. An
object has finite length exactly when it has a composition series, whose length is then the length
of the object (`Order.krullDim_eq_length_of_covBy`, as the subobject lattice of an object of an
abelian category is modular). This mirrors Mathlib's `Module.length`, defined through the lattice
of submodules, and agrees with it on modules (`ModuleCat.length_eq`).

In any category the length is monotone along monomorphisms, and in a category with zero morphisms
and a zero object it vanishes exactly on the zero objects. In an abelian category the length is
moreover additive on short exact sequences. This file records these facts and their consequences
for monomorphisms, epimorphisms and images that the Harada–Sai lemma uses.

## Main definitions

* `CategoryTheory.length X`: the length of an object `X`, the Krull dimension of `Subobject X`.

## Main results

* `CategoryTheory.length_eq_of_orderIso`: objects with isomorphic subobject lattices have the same
  length, and `CategoryTheory.Iso.length_eq`: length is invariant under isomorphism.
* `CategoryTheory.length_le_of_mono`: length is monotone along monomorphisms, in any category.
* `CategoryTheory.length_eq_zero_iff`: an object has length zero exactly when it is a zero object,
  in a category with zero morphisms and a zero object.
* `CategoryTheory.length_eq_add_of_shortExact`: **additivity of length** on short exact sequences.
* `CategoryTheory.length_le_of_epi`: length is antitone along epimorphisms.
* `CategoryTheory.isIso_of_mono_of_length_eq` and `CategoryTheory.isIso_of_epi_of_length_eq`: a
  monomorphism or an epimorphism between objects of the same finite length is an isomorphism.
* `CategoryTheory.length_image_le_left` and `CategoryTheory.length_image_le_right`: the image of
  `f : X ⟶ Y` is at most as long as `X` and as `Y`; the second holds whenever `f` has an image.
* `CategoryTheory.eq_zero_of_length_image_eq_zero`: a morphism whose image has length zero is
  zero.
* `CategoryTheory.length_image_eq_of_fac`: the image of a composite `e ≫ m` of an epimorphism and
  a monomorphism is as long as the object `e` and `m` pass through.
* `CategoryTheory.mono_of_length_image_eq` and `CategoryTheory.epi_of_length_image_eq`: a
  morphism whose image is as long as its finite-length source (target) is a monomorphism
  (epimorphism).

## Implementation notes

A monomorphism `f : X ⟶ Y` induces an order embedding of `Subobject X` into `Subobject Y`
(`CategoryTheory.Subobject.map`), whence monotonicity. For a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `a` the subobject of `X₂` represented by `X₁ ⟶ X₂`, the subobjects
of `X₁` are the subobjects of `X₂` below `a` (`CategoryTheory.Subobject.subobjectOrderIso`) and,
by the correspondence theorem, those of `X₃` are the subobjects of `X₂` above `a`
(`TauCeti.SubquotientPresentation.orderIso`). Additivity is then the additivity of Krull dimension
in the modular lattice `Subobject X₂` (`Order.krullDim_eq_krullDim_Iic_add_krullDim_Ici`). Images
are Mathlib's `CategoryTheory.Limits.image`, with `Limits.factorThruImage f` an epimorphism and
`Limits.image.ι f` a monomorphism. Lengths take values in `ℕ∞`, so that objects of infinite length
are allowed; the statements about isomorphisms assume finite length.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Chapter VI, Section 1.
-/

public section

namespace CategoryTheory

open Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C]

/-- The **length** of an object `X`: the Krull dimension of the lattice of subobjects of `X`, that
is the supremum of the lengths `n` of strict chains `X₀ < X₁ < ⋯ < Xₙ` of subobjects. For a module
this is `Module.length` (`ModuleCat.length_eq`). -/
noncomputable def length (X : C) : ℕ∞ :=
  (Order.krullDim (Subobject X)).unbot (by simp [Order.krullDim_eq_bot_iff])

/-- The length of `X`, as an element of `WithBot ℕ∞`, is the Krull dimension of `Subobject X`. -/
lemma coe_length (X : C) : (length X : WithBot ℕ∞) = Order.krullDim (Subobject X) :=
  WithBot.coe_unbot _ _

/-- Objects whose lattices of subobjects are isomorphic have the same length; the objects may lie
in different categories. -/
lemma length_eq_of_orderIso {D : Type u'} [Category.{v'} D] {X : C} {Y : D}
    (e : Subobject X ≃o Subobject Y) : length X = length Y :=
  WithBot.coe_injective (by rw [coe_length, coe_length, Order.krullDim_eq_of_orderIso e])

/-- **Length is invariant under isomorphism.** -/
lemma Iso.length_eq {X Y : C} (e : X ≅ Y) : length X = length Y :=
  length_eq_of_orderIso (Subobject.mapIsoToOrderIso e)

/-- **Length is monotone along monomorphisms**: the subobjects of `X` embed into those of `Y`
along a monomorphism `f : X ⟶ Y`. -/
theorem length_le_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : length X ≤ length Y :=
  WithBot.coe_le_coe.1 (by
    rw [coe_length, coe_length]
    exact Order.krullDim_le_of_strictMono _
      ((Subobject.map f).monotone.strictMono_of_injective (Subobject.map_obj_injective f)))

/-- **The image of a morphism is at most as long as its target.** -/
theorem length_image_le_right {X Y : C} (f : X ⟶ Y) [HasImage f] : length (image f) ≤ length Y :=
  length_le_of_mono (image.ι f)

section ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C] {X Y : C}

/-- **An object has length zero exactly when it is a zero object.** -/
@[simp]
lemma length_eq_zero_iff : length X = 0 ↔ IsZero X := by
  rw [← WithBot.coe_inj, coe_length, WithBot.coe_zero, Order.krullDim_eq_zero_iff_of_orderTop]
  refine ⟨fun h ↦ by_contra fun hX ↦ ?_, Subobject.subsingleton_of_isZero⟩
  exact not_nontrivial_iff_subsingleton.2 h (Subobject.nontrivial_of_not_isZero hX)

/-- **A morphism is zero when its image has length zero.** -/
theorem eq_zero_of_length_image_eq_zero (f : X ⟶ Y) [HasImage f] (h : length (image f) = 0) :
    f = 0 := by
  rw [← image.fac f, (length_eq_zero_iff.mp h).eq_of_tgt (factorThruImage f) 0, zero_comp]

end ZeroObject

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

/-- **The image of a composite of an epimorphism and a monomorphism** is as long as the object
through which they pass: if `e ≫ m = f` with `e : X ⟶ I` epi and `m : I ⟶ Y` mono, then
`length (image f) = length I`. -/
theorem length_image_eq_of_fac {I : C} (e : X ⟶ I) (m : I ⟶ Y) [Epi e] [Mono m] {f : X ⟶ Y}
    (fac : e ≫ m = f) : length (image f) = length I := by
  have : StrongEpiCategory C := strongEpiCategory_of_regularEpiCategory
  have := strongEpi_of_epi e
  exact (image.isoStrongEpiMono e m fac).length_eq.symm

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
