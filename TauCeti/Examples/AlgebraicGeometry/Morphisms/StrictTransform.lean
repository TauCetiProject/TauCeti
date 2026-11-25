/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.AlgebraicGeometry.Blowup.Restriction
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.StrictTransform.Properties
public import Mathlib.Algebra.DualNumber
import TauCeti.Algebra.DualNumber.Basic
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Strict transforms of the origin of `𝔸¹`, along blowups away from `X`, and of the dual numbers

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

For `X = Spec k[ε] ⟶ Spec k`, `φ = 𝟙` and `U = Spec k`, the strict transform is `X`. Its
reduction `X_red` has the same support as `X` and is also flat over `Spec k`, as is every scheme
over a field, but `X_red` does not agree with `X` over `U` as a closed subscheme: the nilradical
of `X ×_k k ≅ X` is not zero, so by the uniqueness of flat closed subschemes agreeing with `X`
over `U` (`AlgebraicGeometry.Scheme.Hom.strictTransform_unique_of_flat_of_dense`) it does not
vanish over `U`. Agreement of supports over `U` alone does not characterize the strict transform.
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

section DualNumber

variable (k : Type u) [Field k]

/-- The structure morphism `Spec k[ε] ⟶ Spec k` of the dual numbers. -/
def dualNumberToBase : Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))

/-- With `φ = 𝟙` and `U = Spec k`, the strict transform of `Spec k[ε]` is all of
`Spec k[ε] ×_k k`. -/
example : (dualNumberToBase k).strictTransform (𝟙 _) ⊤ = ⊥ :=
  Scheme.Hom.strictTransform_top _ _

/-- **Uniqueness for `Spec k[ε]`.** A closed subscheme of `Spec k[ε] ×_k k` agreeing with it over
`U = Spec k` as closed subschemes is the strict transform `Spec k[ε] ×_k k` itself; flatness over
`Spec k` is automatic. -/
theorem eq_bot_of_comap_strictTransformOpen_eq_bot_dualNumberToBase
    (I : (pullback (dualNumberToBase k) (𝟙 _)).IdealSheafData)
    (hI : I.comap (Scheme.Hom.strictTransformOpen (dualNumberToBase k) (𝟙 _) ⊤).ι = ⊥) :
    I = ⊥ := by
  rw [← Scheme.Hom.strictTransform_top (dualNumberToBase k) (𝟙 _)]
  exact Scheme.Hom.strictTransform_unique_of_flat_of_dense _ _ _ (by simp) I hI

/-- `Spec k[ε] ×_k k ≅ Spec k[ε]` is not reduced: `ε ≠ 0` and `ε² = 0`. -/
theorem not_isReduced_pullback_dualNumberToBase :
    ¬ IsReduced (pullback (dualNumberToBase k) (𝟙 _)) := by
  intro h
  have : IsReduced (Spec (CommRingCat.of (DualNumber k))) :=
    isReduced_of_isOpenImmersion (inv (pullback.fst (dualNumberToBase k) (𝟙 _)))
  have hred : _root_.IsReduced (DualNumber k) :=
    (affine_isReduced_iff (CommRingCat.of (DualNumber k))).mp this
  exact DualNumber.not_isReduced (R := k) hred

/-- **The reduction of `Spec k[ε]` is not the strict transform.** The nilradical of
`Spec k[ε] ×_k k` is not the strict transform `⊥`, since `Spec k[ε] ×_k k` is not reduced, although
the closed subscheme it cuts out is flat over `Spec k`, like the strict transform. -/
theorem nilradical_ne_strictTransform_dualNumberToBase :
    (pullback (dualNumberToBase k) (𝟙 _)).nilradical ≠
      (dualNumberToBase k).strictTransform (𝟙 _) ⊤ := by
  rw [Scheme.Hom.strictTransform_top, Ne, Scheme.nilradical_eq_bot_iff]
  exact not_isReduced_pullback_dualNumberToBase k

/-- The reduction of `Spec k[ε] ×_k k` is flat over `Spec k`, as is every scheme over a field. -/
example : Flat ((pullback (dualNumberToBase k) (𝟙 _)).nilradical.subschemeι ≫
    pullback.snd (dualNumberToBase k) (𝟙 _)) :=
  inferInstance

/-- **Supports do not detect agreement over `U`.** The reduction of `Spec k[ε] ×_k k` has the
full support, but does not agree with `Spec k[ε] ×_k k` over `U = Spec k` as a closed subscheme. -/
theorem support_nilradical_eq_top_and_comap_ne_bot_dualNumberToBase :
    (pullback (dualNumberToBase k) (𝟙 _)).nilradical.support = ⊤ ∧
      (pullback (dualNumberToBase k) (𝟙 _)).nilradical.comap
        (Scheme.Hom.strictTransformOpen (dualNumberToBase k) (𝟙 _) ⊤).ι ≠ ⊥ :=
  ⟨Scheme.support_nilradical _, fun h ↦ nilradical_ne_strictTransform_dualNumberToBase k
    ((eq_bot_of_comap_strictTransformOpen_eq_bot_dualNumberToBase k _ h).trans
      (Scheme.Hom.strictTransform_top _ _).symm)⟩

end DualNumber

end TauCeti.StrictTransformExamples
