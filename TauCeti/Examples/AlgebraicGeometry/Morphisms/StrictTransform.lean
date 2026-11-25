/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.AlgebraicGeometry.Blowup.Restriction
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.StrictTransform.Basic

/-!
# Strict transforms of the origin of `𝔸¹` and along blowups away from `X`

The strict transform `strictTransform f φ U` depends on the open `U`, not only on `φ`. For the
identity of `𝔸¹ = Spec R[t]` and `X` the origin, `f : Spec R ⟶ Spec R[t]` given by `t ↦ 0`:

* with `U = 𝔸¹` the strict transform is the zero ideal sheaf, so it is all of `X ×_{𝔸¹} 𝔸¹ ≅ X`;
* with `U = 𝔾_m = D(t)` the strict transform is the unit ideal sheaf, the empty subscheme, since
  `f⁻¹(𝔾_m)` is empty.

Both opens are modification witnesses of the identity over a field; the strict transforms differ
because `f⁻¹(𝔾_m) = ∅` is not dense in `f⁻¹(𝔸¹) = X`.

For the blowup `Bl_I S ⟶ S` along a centre `V(I)` disjoint from the image of `f : X ⟶ S`, the
strict transform of `X` with respect to `U = S ∖ V(I)` is the zero ideal sheaf on
`X ×_S Bl_I S`, and the projection `X ×_S Bl_I S ⟶ X` is an isomorphism: the strict transform
is `X` itself.
-/

public section

noncomputable section

open CategoryTheory Limits Polynomial AlgebraicGeometry

namespace TauCeti.StrictTransformExamples

universe u

variable (R : Type u) [CommRing R]

/-- The origin `Spec R ⟶ 𝔸¹_R = Spec R[t]`, given by `t ↦ 0`. -/
def origin : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R[X]) :=
  Spec.map (CommRingCat.ofHom (evalRingHom 0))

/-- The preimage of `𝔾_m = D(t)` under the origin is empty. -/
theorem origin_preimage_basicOpen_X :
    origin R ⁻¹ᵁ (PrimeSpectrum.basicOpen (X : R[X])) = ⊥ := by
  rw [origin, SpecMap_preimage_basicOpen]
  exact (PrimeSpectrum.basicOpen_eq_bot_iff _).2 (by simp)

/-- With the witness `U = 𝔸¹`, the strict transform of the origin along the identity is the zero
ideal sheaf. -/
example : (origin R).strictTransform (𝟙 _) ⊤ = ⊥ :=
  Scheme.Hom.strictTransform_top _ _

/-- With the witness `U = 𝔾_m`, the strict transform of the origin along the identity is the unit
ideal sheaf, the empty subscheme. -/
theorem strictTransform_origin_basicOpen_X :
    (origin R).strictTransform (𝟙 _) (PrimeSpectrum.basicOpen (X : R[X])) = ⊤ :=
  Scheme.Hom.strictTransform_eq_top_of_preimage_eq_bot _ _ _ (origin_preimage_basicOpen_X R)

/-- **Blowing up away from `X`.** If the centre `V(I)` of the blowup `Bl_I S ⟶ S` does not meet
the image of `f : X ⟶ S`, the strict transform of `X` is the zero ideal sheaf on `X ×_S Bl_I S`,
and the projection `X ×_S Bl_I S ⟶ X` is an isomorphism. -/
theorem strictTransform_blowupToBase_of_preimage_eq_top {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (h : f ⁻¹ᵁ I.support.compl = ⊤) :
    f.strictTransform I.blowupToBase I.support.compl = ⊥ ∧
      IsIso (pullback.fst f I.blowupToBase) :=
  ⟨Scheme.Hom.strictTransform_eq_bot_of_preimage_eq_top _ _ _ h,
    f.isIso_pullbackFst_of_preimage_eq_top _ h inferInstance⟩

end TauCeti.StrictTransformExamples
