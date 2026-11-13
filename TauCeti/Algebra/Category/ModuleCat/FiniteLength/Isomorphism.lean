/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.KrullSchmidt
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Isomorphism

/-!
# Functors detecting isomorphisms of finite-length modules

Let `F` be an additive functor out of `ModuleCat A`, such as the quotient functor to the projective
or the injective stable category. Suppose that for finite-length modules `M` and `N`, `F` reflects
zero retracts: every retract of `M` or of `N` that `F` sends to zero is zero. If `F` is surjective
on maps `N ⟶ M`, it detects invertibility of maps `M ⟶ N`; if it is also surjective on maps
`M ⟶ N`, then `M ≅ N` as soon as `F M ≅ F N`.

These are the statements of `TauCeti/CategoryTheory/Preadditive/KrullSchmidt/Isomorphism.lean`
for the restriction of `F` to the modules of finite length, which form a Krull-Schmidt category
(`TauCeti.isKrullSchmidt_isFiniteLength`).

## Main results

* `CategoryTheory.Functor.isIso_map_iff_of_isFiniteLength_of_reflects_isZero_retract`: `F` detects
  invertibility.
* `CategoryTheory.Functor.nonempty_iso_obj_iff_of_isFiniteLength_of_reflects_isZero_retract`: `F`
  detects isomorphism classes.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace CategoryTheory.Functor

open CategoryTheory.Limits ModuleCat

universe u v

variable {A : Type u} [Ring A] {D : Type*} [Category* D] [Preadditive D]
  (F : ModuleCat.{v} A ⥤ D) [F.Additive]

omit [Preadditive D] [F.Additive] in
/-- A retract of `M` that `F` kills is zero, read in the category of finite-length modules. -/
private theorem isZero_of_retract_of_isZero_map {M : ModuleCat.{v} A}
    (hZ : ∀ {K : ModuleCat.{v} A}, Retract K M → IsZero (F.obj K) → IsZero K)
    (hM : isFiniteLength.{v} A M) {K : (isFiniteLength.{v} A).FullSubcategory}
    (r : Retract K ⟨M, hM⟩) (hK : IsZero (((isFiniteLength.{v} A).ι ⋙ F).obj K)) : IsZero K :=
  IsZero.of_full_of_faithful_of_isZero (isFiniteLength.{v} A).ι K
    (hZ (r.map (isFiniteLength.{v} A).ι) hK)

/-- **Detecting invertibility between finite-length modules**: if an additive functor `F` sends
no nonzero retract of `M` or of `N` to zero and is surjective on maps `N ⟶ M`, a map `M ⟶ N` is
invertible exactly when its image under `F` is. -/
theorem isIso_map_iff_of_isFiniteLength_of_reflects_isZero_retract {M N : ModuleCat.{v} A}
    (f : M ⟶ N)
    (hF : Function.Surjective (F.map : (N ⟶ M) → (F.obj N ⟶ F.obj M)))
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hZM : ∀ {K : ModuleCat.{v} A}, Retract K M → IsZero (F.obj K) → IsZero K)
    (hZN : ∀ {K : ModuleCat.{v} A}, Retract K N → IsZero (F.obj K) → IsZero K) :
    IsIso (F.map f) ↔ IsIso f := by
  let P := isFiniteLength.{v} A
  have hM' : P M := (isFiniteLength_iff M).mpr hM
  have hN' : P N := (isFiniteLength_iff N).mpr hN
  let f' : (⟨M, hM'⟩ : P.FullSubcategory) ⟶ ⟨N, hN'⟩ := ObjectProperty.homMk f
  have h := (P.ι ⋙ F).isIso_map_iff_of_reflects_isZero_retract f'
    (fun g ↦ by obtain ⟨g', hg'⟩ := hF g; exact ⟨ObjectProperty.homMk g', hg'⟩)
    (isZero_of_retract_of_isZero_map F hZM hM') (isZero_of_retract_of_isZero_map F hZN hN')
  exact h.trans (isIso_iff_of_reflects_iso f' P.ι).symm

/-- **Detecting isomorphism classes of finite-length modules**: if an additive functor `F` sends
no nonzero retract of `M` or of `N` to zero and is surjective on maps `M ⟶ N` and `N ⟶ M`, then
`F M ≅ F N` exactly when `M ≅ N`. -/
theorem nonempty_iso_obj_iff_of_isFiniteLength_of_reflects_isZero_retract (M N : ModuleCat.{v} A)
    (hF : Function.Surjective (F.map : (M ⟶ N) → (F.obj M ⟶ F.obj N)))
    (hF' : Function.Surjective (F.map : (N ⟶ M) → (F.obj N ⟶ F.obj M)))
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hZM : ∀ {K : ModuleCat.{v} A}, Retract K M → IsZero (F.obj K) → IsZero K)
    (hZN : ∀ {K : ModuleCat.{v} A}, Retract K N → IsZero (F.obj K) → IsZero K) :
    Nonempty (F.obj M ≅ F.obj N) ↔ Nonempty (M ≅ N) := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨e⟩ ↦ ⟨F.mapIso e⟩⟩
  obtain ⟨f, hf⟩ := hF e.hom
  have : IsIso (F.map f) := hf.symm ▸ e.isIso_hom
  have := (F.isIso_map_iff_of_isFiniteLength_of_reflects_isZero_retract f hF' hM hN hZM hZN).1 this
  exact ⟨asIso f⟩

end CategoryTheory.Functor
