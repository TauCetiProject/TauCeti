/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Maps from connected reduced affine schemes to finite schemes

An algebra map from a finite-dimensional algebra into a reduced algebra with connected spectrum
is constant whenever the latter algebra has a rational point. Evaluation at that point determines
the constant. Geometrically, a map from a connected reduced affine scheme to a finite scheme
factors through the image of any rational point of its source.

The image algebra is finite-dimensional, reduced, and connected, hence a field. The rational
point embeds that field in the base field, so every element of the image is a scalar. This is
the same finite-connected-ring argument used for
`TauCeti.HopfIdeal.augmentation_eq_bot_of_moduleFinite`, without any Hopf structure.

The result applies to regular maps into finite group-scheme kernels, including nonreduced ones.
-/

public section

namespace AlgHom

open TauCeti

variable {k A B : Type*} [Field k] [Semiring A] [CommRing B] [Algebra k A] [Algebra k B]
  [Module.Finite k A] [IsReduced B] [ConnectedSpace (PrimeSpectrum B)]

/-- An algebra map from a finite-dimensional algebra into a connected reduced algebra is the
constant map determined by evaluation at any rational point. The target algebra need not be
of finite type, and the source algebra need not be reduced or commutative. -/
theorem eq_algebraMap_comp_of_moduleFinite (f : A →ₐ[k] B) (e : B →ₐ[k] k) :
    f = (Algebra.ofId k B).comp (e.comp f) := by
  let _ : Nontrivial B := e.toRingHom.domain_nontrivial
  let _ : Module.Finite k f.range :=
    Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  let _ : ConnectedSpace (PrimeSpectrum f.range) :=
    connectedSpace_primeSpectrum_of_injective f.range.val.toRingHom Subtype.val_injective
  let _ : IsArtinianRing f.range := IsArtinianRing.of_finite k f.range
  let _ : IsReduced f.range := isReduced_of_injective f.range.val Subtype.val_injective
  have hfield : IsField f.range := PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp
    subsingleton_of_preconnected_totallyDisconnected
  have hinj : Function.Injective (e.comp f.range.val) :=
    let _ := hfield.toField
    (e.comp f.range.val).toRingHom.injective
  ext x
  have hx : f.rangeRestrict x = algebraMap k f.range (e (f x)) := hinj (by simp)
  exact congrArg Subtype.val hx

end AlgHom
