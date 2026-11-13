/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import TauCeti.CategoryTheory.ObjectProperty.Homology

/-!
# Homology of short complexes modulo a Serre class

Let `P` be a Serre class in an abelian category `C`, and let `S : X₁ ⟶ X₂ ⟶ X₃` be a short
complex. The homology of `S` is a quotient of the cycles, which are a subobject of `X₂`, so it
lies in `P` whenever `X₂` does (`CategoryTheory.ObjectProperty.prop_homology_of_prop_X₂`, proved
in `TauCeti.CategoryTheory.ObjectProperty.Homology` for any class closed under subobjects and
quotients). Conversely, `X₂` is an extension of `X₂ ⧸ ker g ⊆ X₃` by the cycles, and the cycles
are an extension of the homology by a quotient of `X₁`. Hence `X₂` lies in `P` as soon as the
homology does and each of `X₁` and `X₃` either lies in `P` or is joined to `X₂` by a zero map
(`CategoryTheory.ObjectProperty.prop_X₂_of_prop_homology`).

A morphism of short complexes which is an isomorphism modulo `P` on each of the three objects
induces an isomorphism modulo `P` on homology
(`CategoryTheory.ObjectProperty.isoModSerre_homologyMap`). This is the five lemma modulo a Serre
class. It is proved through the localization of `C` with respect to `P`, which is abelian and
into which the localization functor is exact, so it preserves homology; there, isomorphisms
modulo `P` become isomorphisms.

These are the homological algebra steps of the arguments of Serre's theory of classes of abelian
groups, for instance in spectral sequences
(`TauCeti.Algebra.Homology.SpectralSequence.SerreClass`).

## Main results

* `CategoryTheory.ObjectProperty.prop_X₂_of_prop_homology`: `X₂` lies in `P` if the homology
  does and the outer objects lie in `P` or are joined to `X₂` by zero maps.
* `CategoryTheory.ObjectProperty.isoModSerre_homologyMap`: the five lemma modulo a Serre class.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C) {S : ShortComplex C}
  [P.IsSerreClass]

/-- The cycles of a short complex lie in a Serre class if its homology does and its first object
either lies in the class or is mapped to the middle object by zero. -/
lemma prop_cycles_of_prop_homology (h₁ : S.f = 0 ∨ P S.X₁) (h : P S.homology) : P S.cycles := by
  rcases h₁ with hf | h₁
  · have := S.isIso_homologyπ hf
    exact P.prop_of_iso (asIso S.homologyπ).symm h
  · exact P.prop_X₂_of_exact (S := ShortComplex.mk _ _ S.toCycles_comp_homologyπ)
      (ShortComplex.exact_of_g_is_cokernel _ S.homologyIsCokernel) h₁ h

/-- The middle object of a short complex lies in a Serre class if its cycles do and its last
object either lies in the class or receives the zero map from the middle object. -/
lemma prop_X₂_of_prop_cycles (h₃ : S.g = 0 ∨ P S.X₃) (h : P S.cycles) : P S.X₂ := by
  rcases h₃ with hg | h₃
  · have := S.isIso_iCycles hg
    exact P.prop_of_iso (asIso S.iCycles) h
  · exact P.prop_X₂_of_exact (S := ShortComplex.mk _ _ S.iCycles_g)
      (ShortComplex.exact_of_f_is_kernel _ S.cyclesIsKernel) h h₃

/-- **Objects of a short complex from its homology.** The middle object of a short complex lies
in a Serre class if its homology does, and each of the two outer objects either lies in the class
or is joined to the middle object by a zero map. -/
lemma prop_X₂_of_prop_homology (h₁ : S.f = 0 ∨ P S.X₁) (h₃ : S.g = 0 ∨ P S.X₃)
    (h : P S.homology) : P S.X₂ :=
  P.prop_X₂_of_prop_cycles h₃ (P.prop_cycles_of_prop_homology h₁ h)

/-- **The five lemma modulo a Serre class.** A morphism of short complexes which is an
isomorphism modulo a Serre class `P` on each of the three objects induces an isomorphism modulo
`P` on homology. -/
lemma isoModSerre_homologyMap {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : P.isoModSerre φ.τ₁) (h₂ : P.isoModSerre φ.τ₂) (h₃ : P.isoModSerre φ.τ₃) :
    P.isoModSerre (ShortComplex.homologyMap φ) := by
  -- In the abelian localization `L` with respect to `P`, which is exact, the three components
  -- become isomorphisms, and `L` commutes with homology.
  let L := P.isoModSerre.Q
  let := Localization.preadditive L P.isoModSerre
  have := Localization.functor_additive L P.isoModSerre
  let := SerreClassLocalization.abelian L P
  have := SerreClassLocalization.preservesFiniteLimits L P
  have := SerreClassLocalization.preservesFiniteColimits L P
  rw [← SerreClassLocalization.isIso_map_iff L P] at h₁ h₂ h₃ ⊢
  have : IsIso (L.mapShortComplex.map φ) := by
    rw [ShortComplex.isIso_iff]
    exact ⟨h₁, h₂, h₃⟩
  have h := ShortComplex.mapHomologyIso_hom_naturality φ L
  rw [← Iso.inv_comp_eq] at h
  rw [← h]
  infer_instance

end CategoryTheory.ObjectProperty
