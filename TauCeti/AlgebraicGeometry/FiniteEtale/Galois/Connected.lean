/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic

import TauCeti.AlgebraicGeometry.FiniteEtale.Limits

/-!
# Connected objects of the category of finite étale schemes

Let `S` be a scheme. A finite étale `S`-scheme `X` carries two notions of connectedness: the
topological one, that its underlying scheme `X.obj.left` is a `ConnectedSpace`, and the categorical
one, `CategoryTheory.PreGaloisCategory.IsConnected`, which asks that `X` is not an initial object
of `FiniteEtaleScheme S` and has no non-initial proper subobject. This file proves that they agree,
without any hypothesis on `S`.

Initial objects of `FiniteEtaleScheme S` are those with empty underlying scheme
(`TauCeti.FiniteEtaleScheme.isInitial_iff_isEmpty`), since the empty scheme is finite étale over
`S` and maps uniquely to every `S`-scheme. A monomorphism `i : Y ⟶ X` of finite étale `S`-schemes
is both an open and a closed immersion on underlying schemes, so its image is open and closed in
`X`; if `X` is connected and `Y` is nonempty, `i` is surjective, hence an epimorphism and therefore
an isomorphism because `FiniteEtaleScheme S` is balanced. Conversely, any nonempty open and closed
subset of `X` defines a non-initial subobject `clopenSubscheme` of `X`, which must be an
isomorphism when `X` is categorically connected.

## Main results

* `TauCeti.FiniteEtaleScheme.isInitial_iff_isEmpty`: a finite étale `S`-scheme is initial if and
  only if its underlying scheme is empty.
* `TauCeti.FiniteEtaleScheme.isConnected_iff_connectedSpace`: a finite étale `S`-scheme is a
  connected object of `FiniteEtaleScheme S` if and only if its underlying scheme is connected.
* `TauCeti.FiniteEtaleScheme.isConnected_spec_obj_iff`: over an affine base `Spec R`, the spectrum
  of a finite étale `R`-algebra `A` is categorically connected if and only if `PrimeSpectrum A` is
  connected.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §5.
* H. W. Lenstra, *Galois theory for schemes*, Section 5.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}}

/-- **A finite étale `S`-scheme is initial if and only if its underlying scheme is empty.** No
hypothesis on `S` is needed: the forgetful functor to schemes preserves initial objects, and a
morphism from an empty scheme to any `S`-scheme automatically commutes with the structure
morphisms. -/
@[simp]
theorem isInitial_iff_isEmpty (X : FiniteEtaleScheme S) :
    Nonempty (IsInitial X) ↔ IsEmpty X.obj.left where
  mp := fun ⟨h⟩ ↦ AlgebraicGeometry.isInitial_iff_isEmpty.mp
    ⟨h.isInitialObj ((finiteEtaleSchemeProperty S).ι ⋙ Over.forget S) X⟩
  mpr h := by
    obtain ⟨t⟩ := AlgebraicGeometry.isInitial_iff_isEmpty.mpr h
    exact ⟨IsInitial.ofUniqueHom
      (fun Y ↦ ObjectProperty.homMk (Over.homMk (t.to Y.obj.left) (t.hom_ext _ _)))
      fun Y f ↦ ObjectProperty.hom_ext _ (Over.OverMorphism.ext (t.hom_ext _ _))⟩

/-- **A finite étale `S`-scheme is categorically connected if and only if its underlying scheme is
a connected topological space.** Monomorphisms of finite étale schemes are open and closed
immersions, matching non-initial subobjects with nonempty clopen subsets. -/
@[simp]
theorem isConnected_iff_connectedSpace (X : FiniteEtaleScheme S) :
    PreGaloisCategory.IsConnected X ↔ ConnectedSpace X.obj.left where
  mp h := by
    have hne : Nonempty X.obj.left :=
      not_isEmpty_iff.mp fun he ↦ h.notInitial ((isInitial_iff_isEmpty X).mpr he).some
    have : PreconnectedSpace X.obj.left := by
      refine preconnectedSpace_iff_clopen.mpr fun U hU ↦ ?_
      rcases U.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · exact Or.inl rfl
      · let V : X.obj.left.Opens := ⟨U, hU.isOpen⟩
        let i := clopenSubschemeι V hU.isClosed
        obtain ⟨y, -⟩ : x ∈ Set.range i.hom.left := by
          rwa [range_clopenSubschemeι_hom_left]
        have hV : IsInitial (clopenSubscheme V hU.isClosed) → False :=
          fun hi ↦ ((isInitial_iff_isEmpty _).mp ⟨hi⟩).false y
        have : IsIso i := h.noTrivialComponent _ i hV
        exact Or.inr <|
          (range_clopenSubschemeι_hom_left V hU.isClosed).symm.trans i.hom.left.surjective.range_eq
    exact ⟨hne⟩
  mpr hc :=
    { notInitial hi := by
        obtain ⟨x⟩ := hc.toNonempty
        exact ((isInitial_iff_isEmpty X).mp ⟨hi⟩).false x
      noTrivialComponent Y i _ hY := by
        have hne : Nonempty Y.obj.left :=
          not_isEmpty_iff.mp fun he ↦ hY ((isInitial_iff_isEmpty Y).mpr he).some
        obtain ⟨y⟩ := hne
        have hclopen : IsClopen (Set.range i.hom.left) :=
          ⟨i.hom.left.isClosedMap.isClosed_range, i.hom.left.isOpenMap.isOpen_range⟩
        have huniv : Set.range i.hom.left = Set.univ :=
          hclopen.eq_univ ⟨i.hom.left y, y, rfl⟩
        have : Surjective i.hom.left := ⟨Set.range_eq_univ.mp huniv⟩
        have : Epi i := epi_of_surjective i
        exact isIso_of_mono_of_epi i }

/-- A finite étale `S`-scheme with connected underlying scheme is a connected object of
`FiniteEtaleScheme S`. -/
instance (X : FiniteEtaleScheme S) [ConnectedSpace X.obj.left] :
    PreGaloisCategory.IsConnected X :=
  (isConnected_iff_connectedSpace X).mpr ‹_›

/-- Over an affine base `Spec R`, the spectrum of a finite étale `R`-algebra `A` is a connected
object of `FiniteEtaleScheme (Spec R)` if and only if `PrimeSpectrum A` is connected. -/
theorem isConnected_spec_obj_iff (R : CommRingCat.{u}) (A : CommAlgCat.FiniteEtale.{u} R) :
    PreGaloisCategory.IsConnected ((spec R).obj (op A)) ↔ ConnectedSpace (PrimeSpectrum A.obj) := by
  rw [isConnected_iff_connectedSpace, spec_obj_obj]
  rfl

/-- The spectrum of a finite étale `R`-algebra with connected prime spectrum (for instance, a
domain) is a connected object of `FiniteEtaleScheme (Spec R)`. -/
instance {R : CommRingCat.{u}} (A : CommAlgCat.FiniteEtale.{u} R)
    [ConnectedSpace (PrimeSpectrum A.obj)] :
    PreGaloisCategory.IsConnected ((spec R).obj (op A)) :=
  (isConnected_spec_obj_iff R A).mpr ‹_›

end TauCeti.FiniteEtaleScheme
