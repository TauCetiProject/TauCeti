/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Data.ENat.Monoid
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Length functions on abelian categories

A length function on an abelian category `C` is a function `ℓ : C → ℕ∞` that is additive on short
exact sequences and vanishes exactly on the zero objects. The motivating example is the length of
modules (`ModuleCat.isLengthFunction_length`). This file records the consequences of these two
axioms for monomorphisms, epimorphisms and images that the Harada–Sai lemma uses.

## Main definitions

* `TauCeti.IsLengthFunction ℓ`: `ℓ` is additive on short exact sequences and `ℓ X = 0` exactly when
  `X` is a zero object.

## Main results

* `TauCeti.IsLengthFunction.le_of_mono` and `TauCeti.IsLengthFunction.le_of_epi`: a length function
  is monotone along monomorphisms and antitone along epimorphisms.
* `TauCeti.IsLengthFunction.isIso_of_mono` and `TauCeti.IsLengthFunction.isIso_of_epi`: a
  monomorphism or an epimorphism between objects of the same finite length is an isomorphism.
* `TauCeti.IsLengthFunction.length_image_le_left` and
  `TauCeti.IsLengthFunction.length_image_le_right`: the image of `f : X ⟶ Y` is at most as long as
  `X` and as `Y`.
* `TauCeti.IsLengthFunction.length_image_eq_of_fac`: the image of a composite `e ≫ m` of an
  epimorphism and a monomorphism is as long as the object `e` and `m` pass through.
* `TauCeti.IsLengthFunction.mono_of_length_image_eq` and
  `TauCeti.IsLengthFunction.epi_of_length_image_eq`: a morphism whose image is as long as its
  finite-length source (target) is a monomorphism (epimorphism).

## Implementation notes

Images are Mathlib's `CategoryTheory.Limits.image`, with `Limits.factorThruImage f` an epimorphism
and `Limits.image.ι f` a monomorphism. Lengths take values in `ℕ∞`, so that the length of modules,
which may be infinite, is an example; the statements about isomorphisms assume finite length.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Chapter VI, Section 1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- `ℓ : C → ℕ∞` is a **length function** on the abelian category `C`: it is additive on short
exact sequences, `ℓ X₂ = ℓ X₁ + ℓ X₃` for `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` exact, and it vanishes exactly on
the zero objects. The length of modules is the motivating example. -/
structure IsLengthFunction (ℓ : C → ℕ∞) : Prop where
  /-- A length function is additive on short exact sequences. -/
  add : ∀ S : ShortComplex C, S.ShortExact → ℓ S.X₂ = ℓ S.X₁ + ℓ S.X₃
  /-- A length function vanishes exactly on the zero objects. -/
  eq_zero_iff : ∀ X, ℓ X = 0 ↔ IsZero X

namespace IsLengthFunction

variable {ℓ : C → ℕ∞} (hℓ : IsLengthFunction ℓ) {X Y : C}
include hℓ

/-- The target of a monomorphism is as long as its source plus its cokernel. -/
theorem eq_add_cokernel (f : X ⟶ Y) [Mono f] : ℓ Y = ℓ X + ℓ (cokernel f) :=
  hℓ.add (ShortComplex.mk f (cokernel.π f) (by simp))
    (.mk' (ShortComplex.exact_cokernel f) inferInstance inferInstance)

/-- The source of an epimorphism is as long as its kernel plus its target. -/
theorem eq_kernel_add (f : X ⟶ Y) [Epi f] : ℓ X = ℓ (kernel f) + ℓ Y :=
  hℓ.add (ShortComplex.mk (kernel.ι f) f (by simp))
    (.mk' (ShortComplex.exact_kernel f) inferInstance inferInstance)

/-- **A length function is monotone along monomorphisms.** -/
theorem le_of_mono (f : X ⟶ Y) [Mono f] : ℓ X ≤ ℓ Y := by
  rw [hℓ.eq_add_cokernel f]
  exact le_self_add

/-- **A length function is antitone along epimorphisms.** -/
theorem le_of_epi (f : X ⟶ Y) [Epi f] : ℓ Y ≤ ℓ X := by
  rw [hℓ.eq_kernel_add f]
  exact le_add_self

/-- **A length function is invariant under isomorphism.** -/
theorem eq_of_iso (e : X ≅ Y) : ℓ X = ℓ Y :=
  le_antisymm (hℓ.le_of_mono e.hom) (hℓ.le_of_epi e.hom)

/-- **A monomorphism between objects of the same finite length is an isomorphism.** -/
theorem isIso_of_mono (f : X ⟶ Y) [Mono f] (h : ℓ X = ℓ Y) (hX : ℓ X ≠ ⊤) : IsIso f := by
  have hc : ℓ (cokernel f) = 0 := by
    have := hℓ.eq_add_cokernel f
    rw [← h] at this
    exact (add_right_inj_of_ne_top hX).mp (this.symm.trans (add_zero _).symm)
  have : Epi f := (Preadditive.epi_iff_isZero_cokernel f).mpr ((hℓ.eq_zero_iff _).mp hc)
  exact isIso_of_mono_of_epi f

/-- **An epimorphism between objects of the same finite length is an isomorphism.** -/
theorem isIso_of_epi (f : X ⟶ Y) [Epi f] (h : ℓ X = ℓ Y) (hY : ℓ Y ≠ ⊤) : IsIso f := by
  have hk : ℓ (kernel f) = 0 := by
    have := hℓ.eq_kernel_add f
    rw [h] at this
    exact (add_left_inj_of_ne_top hY).mp (this.symm.trans (zero_add _).symm)
  have : Mono f := (Preadditive.mono_iff_isZero_kernel f).mpr ((hℓ.eq_zero_iff _).mp hk)
  exact isIso_of_mono_of_epi f

/-- **The image of a morphism is at most as long as its source.** -/
theorem length_image_le_left (f : X ⟶ Y) : ℓ (image f) ≤ ℓ X :=
  hℓ.le_of_epi (factorThruImage f)

/-- **The image of a morphism is at most as long as its target.** -/
theorem length_image_le_right (f : X ⟶ Y) : ℓ (image f) ≤ ℓ Y :=
  hℓ.le_of_mono (image.ι f)

/-- **The image of a composite of an epimorphism and a monomorphism** is as long as the object
through which they pass: if `e ≫ m = f` with `e : X ⟶ I` epi and `m : I ⟶ Y` mono, then
`ℓ (image f) = ℓ I`. -/
theorem length_image_eq_of_fac {I : C} (e : X ⟶ I) (m : I ⟶ Y) [Epi e] [Mono m] {f : X ⟶ Y}
    (fac : e ≫ m = f) : ℓ (image f) = ℓ I := by
  have : StrongEpiCategory C := strongEpiCategory_of_regularEpiCategory
  have := strongEpi_of_epi e
  exact (hℓ.eq_of_iso (image.isoStrongEpiMono e m fac)).symm

/-- **A morphism whose image is as long as its source is a monomorphism**, when the source has
finite length. -/
theorem mono_of_length_image_eq (f : X ⟶ Y) (h : ℓ (image f) = ℓ X) (hX : ℓ X ≠ ⊤) : Mono f := by
  have := hℓ.isIso_of_epi (factorThruImage f) h.symm (h ▸ hX)
  rw [← image.fac f]
  infer_instance

/-- **A morphism whose image is as long as its target is an epimorphism**, when the target has
finite length. -/
theorem epi_of_length_image_eq (f : X ⟶ Y) (h : ℓ (image f) = ℓ Y) (hY : ℓ Y ≠ ⊤) : Epi f := by
  have := hℓ.isIso_of_mono (image.ι f) h (h ▸ hY)
  rw [← image.fac f]
  infer_instance

/-- **A morphism is zero when its image has length zero.** -/
theorem eq_zero_of_length_image_eq_zero (f : X ⟶ Y) (h : ℓ (image f) = 0) : f = 0 := by
  rw [← image.fac f, ((hℓ.eq_zero_iff _).mp h).eq_of_tgt (factorThruImage f) 0, zero_comp]

end IsLengthFunction

end TauCeti
