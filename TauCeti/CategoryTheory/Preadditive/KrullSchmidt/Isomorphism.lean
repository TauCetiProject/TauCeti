/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Retract
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic

/-!
# Functors detecting isomorphisms in a Krull-Schmidt category

Let `C` be a Krull-Schmidt category and `F` a functor out of `C`, such as the quotient functor to a
stable category. Suppose that `F` reflects zero retracts of an object `X`: every retract of `X`
that `F` sends to zero is zero. Then every endomorphism of `X` that `F` sends to zero is radical.
Decompose `X` into objects with local endomorphism rings: a nonradical endomorphism has a
component `Pᵢ ⟶ Pⱼ` that is an isomorphism (`TauCeti.mem_jacobsonRadical_iff_forall_not_isIso`),
which makes `Pᵢ` a retract of `X` whose identity factors through the endomorphism, so that `F`
kills the nonzero object `Pᵢ`.

For additive `F` it follows that an endomorphism sent to the identity is invertible. If moreover
`F` reflects zero retracts of `X` and of `Y` and is surjective on maps `Y ⟶ X`, it detects
invertibility of maps `X ⟶ Y`; if it is also surjective on maps `X ⟶ Y`, then `X ≅ Y` as soon as
`F X ≅ F Y`. Indecomposability is not required.

## Main results

* `CategoryTheory.Functor.mem_jacobsonRadical_of_map_eq_zero`: an endomorphism killed by `F` is
  radical.
* `CategoryTheory.Functor.isIso_of_map_eq_id`: an endomorphism sent to the identity is invertible.
* `CategoryTheory.Functor.isIso_map_iff_of_reflects_isZero_retract`: `F` detects invertibility.
* `CategoryTheory.Functor.nonempty_iso_obj_iff_of_reflects_isZero_retract`: `F` detects
  isomorphism classes.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace CategoryTheory.Functor

open CategoryTheory.Limits TauCeti

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C] [IsKrullSchmidt C]
  {D : Type*} [Category* D]

section ZeroMorphisms

variable [HasZeroMorphisms D] (F : C ⥤ D)

/-- **An endomorphism killed by a functor reflecting zero retracts is radical.** In a Krull-Schmidt
category, if `F` sends no nonzero retract of `X` to zero, every endomorphism `e` of `X` with
`F e = 0` lies in the radical of `End X`. -/
theorem mem_jacobsonRadical_of_map_eq_zero {X : C}
    (hZ : ∀ {K : C}, Retract K X → IsZero (F.obj K) → IsZero K) {e : X ⟶ X}
    (he : F.map e = 0) : e ∈ jacobsonRadical X X := by
  obtain ⟨n, P, hP, ⟨φ⟩⟩ := IsKrullSchmidt.exists_iso_biproduct X
  rw [mem_jacobsonRadical_iff_forall_not_isIso P P hP hP φ φ]
  intro i j hij
  -- The component `Pᵢ ⟶ Pⱼ` is invertible, so `Pᵢ` is a retract of `X` through `e`.
  let r : Retract (P i) X :=
    { i := biproduct.ι P i ≫ φ.inv
      r := e ≫ φ.hom ≫ biproduct.π P j ≫
        CategoryTheory.inv (biproduct.ι P i ≫ φ.inv ≫ e ≫ φ.hom ≫ biproduct.π P j)
      retract := by
        rw [← IsIso.hom_inv_id (biproduct.ι P i ≫ φ.inv ≫ e ≫ φ.hom ≫ biproduct.π P j)]
        simp only [Category.assoc] }
  have hz : IsZero (F.obj (P i)) := by
    rw [IsZero.iff_id_eq_zero, ← F.map_id, ← r.retract, F.map_comp]
    simp [r, he]
  have := hP i
  exact one_ne_zero (α := End (P i)) (End.ext ((hZ r hz).eq_of_src _ _))

end ZeroMorphisms

variable [Preadditive D] (F : C ⥤ D) [F.Additive]

/-- **An endomorphism sent to the identity is invertible**, for an additive functor out of a
Krull-Schmidt category that reflects zero retracts of `X`: `𝟙 X - u` is killed by `F`, hence
radical. -/
theorem isIso_of_map_eq_id {X : C} (hZ : ∀ {K : C}, Retract K X → IsZero (F.obj K) → IsZero K)
    {u : X ⟶ X} (hu : F.map u = 𝟙 (F.obj X)) : IsIso u := by
  have h := F.mem_jacobsonRadical_of_map_eq_zero hZ (e := 𝟙 X - u)
    (by rw [F.map_sub, F.map_id, hu, sub_self])
  simpa using mem_jacobsonRadical_iff_isIso_id_sub_comp_right.mp h (𝟙 X)

/-- **Detecting invertibility in a Krull-Schmidt category**: if an additive functor `F` sends no
nonzero retract of `X` or of `Y` to zero and is surjective on maps `Y ⟶ X`, a map `X ⟶ Y` is
invertible exactly when its image under `F` is. -/
theorem isIso_map_iff_of_reflects_isZero_retract {X Y : C} (f : X ⟶ Y)
    (hF : Function.Surjective (F.map : (Y ⟶ X) → (F.obj Y ⟶ F.obj X)))
    (hZX : ∀ {K : C}, Retract K X → IsZero (F.obj K) → IsZero K)
    (hZY : ∀ {K : C}, Retract K Y → IsZero (F.obj K) → IsZero K) :
    IsIso (F.map f) ↔ IsIso f := by
  refine ⟨fun hf ↦ ?_, fun _ ↦ inferInstance⟩
  obtain ⟨g, hg⟩ := hF (CategoryTheory.inv (F.map f))
  have := F.isIso_of_map_eq_id hZX (u := f ≫ g) (by simp [hg])
  have := F.isIso_of_map_eq_id hZY (u := g ≫ f) (by simp [hg])
  have : IsSplitMono f :=
    .mk' ⟨g ≫ CategoryTheory.inv (f ≫ g), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
  have : IsSplitEpi f :=
    .mk' ⟨CategoryTheory.inv (g ≫ f) ≫ g, by rw [Category.assoc, IsIso.inv_hom_id]⟩
  exact isIso_of_mono_of_isSplitEpi f

/-- **Detecting isomorphism classes in a Krull-Schmidt category**: if an additive functor `F`
sends no nonzero retract of `X` or of `Y` to zero and is surjective on maps `X ⟶ Y` and
`Y ⟶ X`, then `F X ≅ F Y` exactly when `X ≅ Y`. -/
theorem nonempty_iso_obj_iff_of_reflects_isZero_retract (X Y : C)
    (hF : Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)))
    (hF' : Function.Surjective (F.map : (Y ⟶ X) → (F.obj Y ⟶ F.obj X)))
    (hZX : ∀ {K : C}, Retract K X → IsZero (F.obj K) → IsZero K)
    (hZY : ∀ {K : C}, Retract K Y → IsZero (F.obj K) → IsZero K) :
    Nonempty (F.obj X ≅ F.obj Y) ↔ Nonempty (X ≅ Y) := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨e⟩ ↦ ⟨F.mapIso e⟩⟩
  obtain ⟨f, hf⟩ := hF e.hom
  have : IsIso (F.map f) := hf.symm ▸ e.isIso_hom
  have := (F.isIso_map_iff_of_reflects_isZero_retract f hF' hZX hZY).1 this
  exact ⟨asIso f⟩

end CategoryTheory.Functor
