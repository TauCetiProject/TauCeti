/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.IdealSheaf.Power
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
public import TauCeti.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic

/-!
# Thickenings of schemes

A *thickening* of schemes is a closed immersion `i : Z ⟶ X` that is surjective on underlying
points, so that `Z` and `X` have the same underlying space and differ only in their structure
sheaves; equivalently, the ideal sheaf of `i` consists of locally nilpotent sections. A thickening
is *first order* if the square of its ideal sheaf vanishes (Stacks, Definition 37.2.1 (04EX)).
The basic example is `Spec k ⟶ Spec k[ε]`, for the dual numbers `k[ε] = k[x] ⧸ (x²)`.

First-order thickenings are the test objects of infinitesimal deformation theory: formally smooth,
formally unramified and formally étale morphisms are defined by lifting along them, and when a
lift along a first-order thickening with ideal `I` exists, the set of such lifts is a torsor under a
module of homomorphisms into `I`.

## Main definitions

* `TauCeti.AlgebraicGeometry.IsThickening i`: `i` is a closed immersion surjective on points.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening i`: `i` is a closed immersion whose ideal
  sheaf has square zero.

## Main results

* `TauCeti.AlgebraicGeometry.isThickening_iff_ker_le_nilradical`: a closed immersion is a
  thickening if and only if its ideal sheaf is contained in the nilradical of the target.
* `TauCeti.AlgebraicGeometry.IsThickening.SpecMap_iff`: for a surjective ring map `φ : R ⟶ S`,
  `Spec S ⟶ Spec R` is a thickening if and only if the kernel of `φ` is a nil ideal.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.SpecMap_iff`: for a surjective ring map
  `φ : R ⟶ S`, `Spec S ⟶ Spec R` is a first-order thickening if and only if the kernel of `φ` has
  square zero.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.SpecMap_quotient_mk` and
  `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.exists_iso_quotient`: `Spec (B ⧸ I) ⟶ Spec B`
  is a first-order thickening when `I ^ 2 = ⊥`, and every first-order thickening of an affine
  scheme is of this form up to isomorphism.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.SpecMap_fstHom`: the closed immersion
  `Spec R ⟶ Spec (TrivSqZeroExt R M)` given by the projection to `R` is a first-order thickening.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.SpecMap_quotient_factor_iff` and
  `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.SpecMap_quotient_factor_pow_succ`: for ideals
  `J ≤ I`, `Spec (R ⧸ I) ⟶ Spec (R ⧸ J)` is a first-order thickening if and only if `I ^ 2 ≤ J`,
  which holds in particular for successive positive powers `I ^ (n + 2) ≤ I ^ (n + 1)`.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.inclusion_iff` and
  `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.inclusion_pow_succ`: for ideal sheaves
  `I ≤ J`, the inclusion `V(J) ⟶ V(I)` is a first-order thickening if and only if `J ^ 2 ≤ I`,
  which holds in particular for successive positive powers `I ^ (n + 2) ≤ I ^ (n + 1)`.
* `TauCeti.AlgebraicGeometry.IsThickening.factor_firstOrder`: a closed immersion whose ideal sheaf
  `I` satisfies `I ^ (n + 2) = 0` factors, by Mathlib's `IsClosedImmersion.lift`, through
  `V(I ^ (n + 1))` as a thickening with ideal of vanishing `(n + 1)`-st power followed by a
  first-order thickening.
* `TauCeti.AlgebraicGeometry.isThickening_of_isNilpotent_ker`: a closed immersion with nilpotent
  ideal sheaf is a thickening.
* `TauCeti.AlgebraicGeometry.IsThickening.ker_le_ker`: a morphism from a reduced scheme kills the
  ideal sheaf of a thickening of its target, so it lifts along the thickening; the reduction
  `X.nilradical.subscheme ⟶ X` is a thickening.
* Thickenings contain the isomorphisms and are stable under composition and base change;
  first-order thickenings contain the isomorphisms, respect isomorphisms and are stable under base
  change.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.isThickening`: a first-order thickening is a
  thickening, and `TauCeti.AlgebraicGeometry.IsThickening.isUniversalHomeomorphism`: a thickening
  is a universal homeomorphism.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.isNilpotent_ker`: the ideal sheaf of a
  first-order thickening is nilpotent.

## References

* [Stacks Project, Definition 37.2.1](https://stacks.math.columbia.edu/tag/04EX).
* [Stacks Project, Lemma 37.2.3](https://stacks.math.columbia.edu/tag/04EZ), base change of
  thickenings.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ Y` is a *thickening* if it is a closed immersion that is
surjective on underlying points. Then `X` and `Y` have the same underlying space, and the ideal
sheaf of `f` consists of locally nilpotent sections (`isThickening_iff_ker_le_nilradical`).
Stacks, Definition 37.2.1 (04EX). -/
@[stacks 04EX, mk_iff]
class IsThickening (f : X ⟶ Y) : Prop extends IsClosedImmersion f, Surjective f

/-- Thickenings are the closed immersions that are surjective. -/
theorem isThickening_eq :
    @IsThickening.{u} = (@IsClosedImmersion ⊓ @Surjective : MorphismProperty Scheme.{u}) := by
  ext X Y f
  exact isThickening_iff f

/-- A closed immersion is a thickening if and only if its ideal sheaf is contained in the
nilradical of the target, that is, consists of locally nilpotent sections. -/
theorem isThickening_iff_ker_le_nilradical (i : Z ⟶ X) [IsClosedImmersion i] :
    IsThickening i ↔ i.ker ≤ X.nilradical := by
  -- The image of a closed immersion is closed, and it is the support of the ideal sheaf.
  have hrange : (i.ker.support : Set X) = Set.range i := by
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
  -- An ideal sheaf lies in the nilradical exactly when its support is everything.
  have hnil : i.ker ≤ X.nilradical ↔ i.ker.support = ⊤ := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_top,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, top_le_iff]
  simp [isThickening_iff, surjective_iff, hnil, ← Set.range_eq_univ, ← hrange,
    ‹IsClosedImmersion i›]

/-- A closed immersion whose ideal sheaf is nilpotent is a thickening. -/
theorem isThickening_of_isNilpotent_ker (i : Z ⟶ X) [IsClosedImmersion i]
    (h : IsNilpotent i.ker) : IsThickening i := by
  obtain ⟨m, hm⟩ := h
  exact (isThickening_iff_ker_le_nilradical i).2 <|
    calc i.ker ≤ i.ker.radical := Scheme.IdealSheafData.le_radical _
      _ = (i.ker ^ (m + 1)).radical := (Scheme.IdealSheafData.radical_pow _ m.succ_ne_zero).symm
      _ = X.nilradical := by
        rw [pow_eq_zero_of_le m.le_succ hm, Scheme.IdealSheafData.zero_eq_bot,
          Scheme.IdealSheafData.radical_bot]

namespace IsThickening

-- The instances for `⊓` are not found by instance search through `isThickening_eq`, so they are
-- named explicitly.
instance isMultiplicative : IsMultiplicative @IsThickening.{u} :=
  isThickening_eq ▸ IsMultiplicative.inf

instance isStableUnderComposition : IsStableUnderComposition @IsThickening.{u} :=
  isMultiplicative.toIsStableUnderComposition

instance isStableUnderBaseChange : IsStableUnderBaseChange @IsThickening.{u} :=
  isThickening_eq ▸ IsStableUnderBaseChange.inf

instance respectsIso : RespectsIso @IsThickening.{u} :=
  isThickening_eq ▸ RespectsIso.inf _ _

/-- An isomorphism is a thickening. -/
instance (priority := 100) of_isIso (i : Z ⟶ X) [IsIso i] : IsThickening i where

/-- A composite of thickenings is a thickening. -/
instance comp (i : Z ⟶ Y) (j : Y ⟶ X) [IsThickening i] [IsThickening j] :
    IsThickening (i ≫ j) where

/-- The base change of a thickening is a thickening. -/
instance pullback_fst (f : Y ⟶ X) (i : Z ⟶ X) [IsThickening i] :
    IsThickening (pullback.fst f i) where

/-- The base change of a thickening is a thickening. -/
instance pullback_snd (i : Z ⟶ X) (f : Y ⟶ X) [IsThickening i] :
    IsThickening (pullback.snd i f) where

/-- A thickening is a universal homeomorphism: it is integral and universally injective, as is
every closed immersion, and it is surjective. -/
instance (priority := 100) isUniversalHomeomorphism (i : Z ⟶ X) [IsThickening i] :
    IsUniversalHomeomorphism i :=
  (isUniversalHomeomorphism_iff_isIntegralHom_universallyInjective_surjective i).2
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- The reduction `X.nilradical.subscheme ⟶ X` is a thickening. -/
instance subschemeι_nilradical (X : Scheme.{u}) : IsThickening X.nilradical.subschemeι :=
  (isThickening_iff_ker_le_nilradical _).2 (Scheme.IdealSheafData.ker_subschemeι _).le

/-- A morphism from a reduced scheme kills the ideal sheaf of every thickening of its target, so it
lifts along the thickening (`IsClosedImmersion.lift`). -/
theorem ker_le_ker (i : Z ⟶ X) [IsThickening i] (f : Y ⟶ X) [IsReduced Y] : i.ker ≤ f.ker :=
  ((isThickening_iff_ker_le_nilradical i).1 ‹_›).trans f.nilradical_le_ker

/-- For a surjective ring map `φ : R ⟶ S`, the closed immersion `Spec S ⟶ Spec R` is a thickening
if and only if the kernel of `φ` is a nil ideal. -/
theorem SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : Function.Surjective φ) :
    IsThickening (Spec.map φ) ↔ RingHom.ker φ.hom ≤ nilradical R := by
  have := IsClosedImmersion.spec_of_surjective φ hφ
  -- On points, `Spec.map φ` is the comap map of prime spectra.
  have hsurj : Surjective (Spec.map φ) ↔ Function.Surjective (PrimeSpectrum.comap φ.hom) := by
    rw [surjective_iff, funext (Spec.map_apply φ)]
    exact Iff.rfl
  rw [isThickening_iff, hsurj, ← Set.range_eq_univ, range_comap_of_surjective _ _ hφ,
    PrimeSpectrum.zeroLocus_eq_univ_iff]
  exact and_iff_right ‹_›

end IsThickening

/-- A morphism of schemes `f : X ⟶ Y` is a *first-order thickening* if it is a closed immersion
whose ideal sheaf `𝓘` satisfies `𝓘 * 𝓘 = 0`. Stacks, Definition 37.2.1 (04EX). -/
@[stacks 04EX, mk_iff]
class IsFirstOrderThickening (f : X ⟶ Y) : Prop extends IsClosedImmersion f where
  /-- The ideal sheaf of a first-order thickening has square zero. -/
  ker_mul_self : f.ker * f.ker = ⊥

namespace IsFirstOrderThickening

/-- The ideal sheaf of a first-order thickening is nilpotent. -/
theorem isNilpotent_ker (i : Z ⟶ X) [IsFirstOrderThickening i] : IsNilpotent i.ker :=
  ⟨2, by simp [pow_two, ker_mul_self]⟩

/-- A first-order thickening is a thickening: its ideal sheaf has square zero, so it lies in the
nilradical. -/
instance (priority := 100) isThickening (i : Z ⟶ X) [IsFirstOrderThickening i] :
    IsThickening i :=
  isThickening_of_isNilpotent_ker i (isNilpotent_ker i)

/-- An isomorphism is a first-order thickening. -/
instance (priority := 100) of_isIso (i : Z ⟶ X) [IsIso i] : IsFirstOrderThickening i where
  ker_mul_self := by rw [Scheme.Hom.ker_eq_bot_of_isIso, Scheme.IdealSheafData.bot_mul]

/-- Precomposing a first-order thickening with an isomorphism gives a first-order thickening. -/
instance comp_of_isIso (e : Y ⟶ Z) (i : Z ⟶ X) [IsIso e] [IsFirstOrderThickening i] :
    IsFirstOrderThickening (e ≫ i) where
  ker_mul_self := by rw [Scheme.Hom.ker_comp_of_isIso, ker_mul_self]

/-- The base change of a first-order thickening is a first-order thickening: its ideal sheaf is
the inverse image of the original one, and inverse images of ideal sheaves preserve products. -/
instance pullback_fst (f : Y ⟶ X) (i : Z ⟶ X) [IsFirstOrderThickening i] :
    IsFirstOrderThickening (pullback.fst f i) where
  ker_mul_self := by
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← Scheme.IdealSheafData.comap_mul, ker_mul_self, Scheme.IdealSheafData.comap_bot]

/-- The base change of a first-order thickening is a first-order thickening. -/
instance pullback_snd (i : Z ⟶ X) (f : Y ⟶ X) [IsFirstOrderThickening i] :
    IsFirstOrderThickening (pullback.snd i f) := by
  rw [← pullbackSymmetry_hom_comp_fst]
  infer_instance

/-- Postcomposing a first-order thickening with an isomorphism gives a first-order thickening. -/
instance comp_of_isIso_right (i : Z ⟶ Y) (e : Y ⟶ X) [IsFirstOrderThickening i] [IsIso e] :
    IsFirstOrderThickening (i ≫ e) := by
  -- Up to an isomorphism of sources, `i ≫ e` is the base change of `i` along `inv e`.
  rw [← IsIso.inv_hom_id_assoc (pullback.snd (inv e) i) (i ≫ e), ← pullback.condition_assoc,
    IsIso.inv_hom_id, Category.comp_id]
  infer_instance

/-- First-order thickenings are stable under composition with isomorphisms on either side. -/
instance respectsIso : RespectsIso @IsFirstOrderThickening.{u} :=
  RespectsIso.mk _ (fun e i _ ↦ comp_of_isIso e.hom i) (fun e i _ ↦ comp_of_isIso_right i e.hom)

/-- First-order thickenings are stable under base change along arbitrary pullback squares. -/
instance isStableUnderBaseChange : IsStableUnderBaseChange @IsFirstOrderThickening.{u} :=
  IsStableUnderBaseChange.mk' fun _ _ _ f i _ _ ↦ pullback_fst f i

/-- The restriction of a first-order thickening over an open subset is a first-order thickening. -/
instance morphismRestrict (i : Z ⟶ X) [IsFirstOrderThickening i] (U : X.Opens) :
    IsFirstOrderThickening (i ∣_ U) :=
  of_isPullback (P := @IsFirstOrderThickening) (isPullback_morphismRestrict i U).flip ‹_›

/-- For a surjective ring map `φ : R ⟶ S`, the closed immersion `Spec S ⟶ Spec R` is a first-order
thickening if and only if the kernel of `φ` has square zero. -/
theorem SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : Function.Surjective φ) :
    IsFirstOrderThickening (Spec.map φ) ↔ RingHom.ker φ.hom * RingHom.ker φ.hom = ⊥ := by
  have := IsClosedImmersion.spec_of_surjective φ hφ
  -- The ideal sheaf of `Spec.map φ` is generated by the kernel of `φ`, read in `Γ(Spec R, ⊤)`.
  have hker : (Spec.map φ).ker * (Spec.map φ).ker = ⊥ ↔
      RingHom.ker φ.hom * RingHom.ker φ.hom = ⊥ := by
    rw [Scheme.Hom.ker_Spec_map, ← Scheme.IdealSheafData.ofIdealTop_mul, ← Ideal.map_mul,
      Scheme.IdealSheafData.ofIdealTop_eq_bot_iff, Ideal.map_eq_bot_iff_of_injective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).1]
  exact ⟨fun h ↦ hker.1 h.ker_mul_self, fun h ↦ ⟨hker.2 h⟩⟩

/-- The closed immersion `Spec (B ⧸ I) ⟶ Spec B` of a square-zero ideal `I` is a first-order
thickening. -/
theorem SpecMap_quotient_mk {B : CommRingCat.{u}} {I : Ideal B}
    (hI : I ^ 2 = ⊥) :
    IsFirstOrderThickening (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  (SpecMap_iff _ Ideal.Quotient.mk_surjective).2 <| by
    rwa [CommRingCat.hom_ofHom, Ideal.mk_ker, ← pow_two]

/-- The closed immersion `Spec R ⟶ Spec (TrivSqZeroExt R M)` given by the projection to `R` is a
first-order thickening, since its kernel `M` squares to zero. For `M = R` this is the inclusion
`Spec R ⟶ Spec R[ε]` over `ε ↦ 0`. -/
instance SpecMap_fstHom {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsFirstOrderThickening
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M : TrivSqZeroExt R M →+* R))) :=
  (SpecMap_iff _ TrivSqZeroExt.fst_surjective).2 <|
    (pow_two _).symm.trans (TrivSqZeroExt.kerIdeal_sq R M)

/-- A first-order thickening `i : T ⟶ T'` with `T'` affine is, up to isomorphisms of source and
target, the closed immersion `Spec (B ⧸ I) ⟶ Spec B` for `B = Γ(T', ⊤)` and an ideal `I` of `B`
with `I ^ 2 = ⊥`. -/
theorem exists_iso_quotient {T T' : Scheme.{u}} [IsAffine T']
    (i : T ⟶ T') [IsFirstOrderThickening i] :
    ∃ (I : Ideal Γ(T', ⊤)) (e : T ≅ Spec (.of (Γ(T', ⊤) ⧸ I))), I ^ 2 = ⊥ ∧
      i ≫ T'.isoSpec.hom = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := i ≫ T'.isoSpec.hom)).1 inferInstance
  refine ⟨I, e, ?_, he⟩
  have : IsFirstOrderThickening (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
    rw [← (Iso.inv_comp_eq _).2 he]
    infer_instance
  have := (SpecMap_iff _ Ideal.Quotient.mk_surjective).1 this
  rwa [CommRingCat.hom_ofHom, Ideal.mk_ker, ← pow_two] at this

/-- For ideals `J ≤ I` of a commutative ring `R`, the closed immersion
`Spec (R ⧸ I) ⟶ Spec (R ⧸ J)` induced by `Ideal.Quotient.factor h` is a first-order thickening if
and only if `I ^ 2 ≤ J`. -/
theorem SpecMap_quotient_factor_iff {R : Type u} [CommRing R] {I J : Ideal R} (h : J ≤ I) :
    IsFirstOrderThickening (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ↔
      I ^ 2 ≤ J := by
  rw [SpecMap_iff _ (Ideal.Quotient.factor_surjective h), CommRingCat.hom_ofHom,
    Ideal.Quotient.factor_ker, ← Ideal.map_mul, ← pow_two, Ideal.map_eq_bot_iff_le_ker,
    Ideal.mk_ker]

/-- For any ideal `I` of a commutative ring `R` and any `n : ℕ`, the closed immersion
`Spec (R ⧸ I ^ (n + 1)) ⟶ Spec (R ⧸ I ^ (n + 2))` between successive positive ideal-power
quotients is a first-order thickening. -/
theorem SpecMap_quotient_factor_pow_succ {R : Type u} [CommRing R] {I : Ideal R} {n : ℕ}
    (h : I ^ (n + 2) ≤ I ^ (n + 1)) :
    IsFirstOrderThickening (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) :=
  (SpecMap_quotient_factor_iff h).mpr <| by
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by omega)

/-- For ideal sheaves `I ≤ J` on a scheme, the inclusion `V(J) ⟶ V(I)` of closed subschemes is a
first-order thickening if and only if `J ^ 2 ≤ I`. -/
theorem inclusion_iff {I J : X.IdealSheafData} (h : I ≤ J) :
    IsFirstOrderThickening (Scheme.IdealSheafData.inclusion h) ↔ J ^ 2 ≤ I := by
  -- The ideal sheaf of the inclusion is `J.comap I.subschemeι`, whose square is the inverse image
  -- of `J ^ 2`; this vanishes exactly when `J ^ 2` lies in `I`, the ideal sheaf of `V(I) ⟶ X`.
  have hker : (Scheme.IdealSheafData.inclusion h).ker * (Scheme.IdealSheafData.inclusion h).ker =
      (J ^ 2).comap I.subschemeι := by
    rw [Scheme.IdealSheafData.ker_inclusion, ← Scheme.IdealSheafData.comap_mul, pow_two]
  refine ⟨fun hJ ↦ ?_, fun hJ ↦ ⟨?_⟩⟩
  · have := congrArg (·.map I.subschemeι) (hker.symm.trans hJ.ker_mul_self)
    simp only [Scheme.IdealSheafData.map_comap_of_isClosedImmersion,
      Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι] at this
    exact sup_eq_right.mp this
  · rw [hker]
    refine le_bot_iff.mp ((Scheme.IdealSheafData.comap_mono _ hJ).trans_eq ?_)
    simpa using I.subschemeι.comap_ker_self

/-- For any ideal sheaf `I` and any `n : ℕ`, the inclusion `V(I ^ (n + 1)) ⟶ V(I ^ (n + 2))`
between successive positive infinitesimal neighbourhoods of `V(I)` is a first-order thickening. -/
theorem inclusion_pow_succ {I : X.IdealSheafData} {n : ℕ} (h : I ^ (n + 2) ≤ I ^ (n + 1)) :
    IsFirstOrderThickening (Scheme.IdealSheafData.inclusion h) :=
  (inclusion_iff h).mpr <| by
    rw [← pow_mul]
    exact I.pow_le_pow_right (by omega)

/-- The product of two sections of the ideal sheaf of a first-order thickening vanishes, over any
open subset. -/
theorem mul_eq_zero_of_app_eq_zero (i : Z ⟶ X) [IsFirstOrderThickening i] {U : X.Opens}
    {s t : Γ(X, U)} (hs : i.app U s = 0) (ht : i.app U t = 0) : s * t = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf U _ _ fun x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  have hres : ∀ s : Γ(X, U), i.app U s = 0 →
      X.presheaf.map (homOfLE hVU).op s ∈ i.ker.ideal ⟨V, hV⟩ := by
    intro s hs
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker, ← CommRingCat.comp_apply, i.naturality,
      CommRingCat.comp_apply, hs, map_zero]
  have h0 : X.presheaf.map (homOfLE hVU).op (s * t) = 0 := by
    have : _ ∈ (i.ker * i.ker).ideal ⟨V, hV⟩ := Ideal.mul_mem_mul (hres s hs) (hres t ht)
    rw [ker_mul_self, ← map_mul] at this
    simpa using this
  -- `section_ext` states its goal for the presheaf of `X.sheaf`, which is `X.presheaf`.
  change X.presheaf.germ U x hx (s * t) = X.presheaf.germ U x hx 0
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) x hxV, h0, map_zero, map_zero]

end IsFirstOrderThickening

namespace IsThickening

/-- A closed immersion `i : Z ⟶ X` whose ideal sheaf `I` satisfies `I ^ (n + 2) = 0` factors as
`Z ⟶ X' ⟶ X` through the closed subscheme `X' = V(I ^ (n + 1))`, where `X' ⟶ X` is a first-order
thickening (as `(I ^ (n + 1)) ^ 2 ≤ I ^ (n + 2) = 0`) and `Z ⟶ X'` is a thickening whose ideal
sheaf `I / I ^ (n + 1)` has vanishing `(n + 1)`-st power. Inductively, a thickening with nilpotent
ideal sheaf is a composite of first-order thickenings. -/
theorem factor_firstOrder (i : Z ⟶ X) [IsClosedImmersion i] {n : ℕ} (h : i.ker ^ (n + 2) = ⊥) :
    IsFirstOrderThickening (i.ker ^ (n + 1)).subschemeι ∧
      IsThickening (IsClosedImmersion.lift (i.ker ^ (n + 1)).subschemeι i
        (i.ker.ker_subschemeι_pow_le n.succ_ne_zero)) ∧
      (IsClosedImmersion.lift (i.ker ^ (n + 1)).subschemeι i
        (i.ker.ker_subschemeι_pow_le n.succ_ne_zero)).ker ^ (n + 1) = ⊥ := by
  -- The `(n + 1)`-st power of the ideal sheaf of `Z ⟶ X'` is the inverse image of `I ^ (n + 1)`,
  -- which vanishes on `X'`.
  have hker : (IsClosedImmersion.lift (i.ker ^ (n + 1)).subschemeι i
      (i.ker.ker_subschemeι_pow_le n.succ_ne_zero)).ker ^ (n + 1) = ⊥ :=
    Scheme.Hom.ker_pow_eq_bot_of_ker_comp_pow_le _ (i.ker ^ (n + 1)).subschemeι
      (by rw [IsClosedImmersion.lift_fac, Scheme.IdealSheafData.ker_subschemeι])
  refine ⟨⟨?_⟩, isThickening_of_isNilpotent_ker _ ⟨n + 1, hker⟩, hker⟩
  rw [Scheme.IdealSheafData.ker_subschemeι, ← pow_add, ← le_bot_iff, ← h]
  exact i.ker.pow_le_pow_right (by omega)

end IsThickening

end TauCeti.AlgebraicGeometry
