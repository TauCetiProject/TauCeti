/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Schur
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate
public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive
public import TauCeti.CategoryTheory.Semisimple.Basic

/-!
# Duals of simple objects

In a rigid monoidal abelian category whose tensor product is additive, the right dual of a simple
object is simple. Taking right adjoint mates is a bijection `(A ⟶ B) ≃ (Bᘁ ⟶ Aᘁ)` reversing
composition, with inverse the left adjoint mate, and every object `Y` is the right dual `(ᘁY)ᘁ` of
its left dual. So a monomorphism `f : Y ⟶ Xᘁ` is the mate of the epimorphism `ᘁf : X ⟶ ᘁY`, which
out of the simple object `X` is an isomorphism or zero.

This is what makes duality act on the simple isomorphism classes of a fusion category.

If the tensor unit is simple, the tensor product of two nonzero objects is nonzero
(`TauCeti.not_isZero_tensorObj`). The coevaluation `𝟙_ C ⟶ Y ⊗ Yᘁ` of a nonzero object is nonzero,
hence a monomorphism out of the simple unit, and whiskering by `X` keeps it a monomorphism because
`X ⊗ -` is right adjoint to `Xᘁ ⊗ -`. So `X ≅ X ⊗ 𝟙_ C` embeds into `(X ⊗ Y) ⊗ Yᘁ`. Without a
simple unit this fails: in a multifusion category two distinct simple summands of the unit have
zero tensor product.

If a member of an exact pairing has scalar endomorphisms over a commutative semiring `R`
(the structure map `algebraMap R (End _)` is surjective, as for a simple object with
finite-dimensional endomorphisms over an algebraically closed field), Frobenius reciprocity shows
that every morphism from the paired tensor product to the unit is a scalar multiple of the
evaluation. Both choices of the member are available; they control the two categorical trace
pairings. In a finite semisimple category, a nonzero morphism `η : 𝟙_ C ⟶ Y ⊗ X` is split on some
simple summand of the unit, and the evaluation is a multiple of the retraction there, so
composing `η` with the evaluation gives a nonzero endomorphism of the unit. The unit need not be
simple; when it is, this endomorphism is invertible by Schur's lemma.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.8
-/

public section

open CategoryTheory Limits MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Abelian

variable [Abelian C] [MonoidalPreadditive C] [RigidCategory C]

/-- In a rigid monoidal abelian category, the right dual of a simple object is simple. -/
instance simple_rightDual (X : C) [Simple X] : Simple Xᘁ where
  mono_isIso_iff_nonzero {Y} f _ := by
    -- `f` is the right mate of its left mate `g : X ⟶ ᘁY`.
    let g : X ⟶ ᘁY := ᘁf
    have hg : gᘁ = f := rightAdjointMate_leftAdjointMate f
    have hg0 : g = 0 ↔ f = 0 := by
      rw [← hg, ← rightAdjointMate_injective.eq_iff, rightAdjointMate_zero]
    -- Since `f` is a monomorphism, `g` is an epimorphism.
    have : Epi g := ⟨fun {Z} a b hab ↦ by
      have h := congrArg rightAdjointMate hab
      rw [comp_rightAdjointMate, comp_rightAdjointMate, hg, cancel_mono] at h
      exact rightAdjointMate_injective h⟩
    refine ⟨fun _ h0 ↦ ?_, fun h0 ↦ ?_⟩
    · -- If `f` were a zero isomorphism, then `Xᘁ` and hence `X` would be zero.
      have h : (𝟙 X)ᘁ = (0 : X ⟶ X)ᘁ := by
        rw [rightAdjointMate_id, rightAdjointMate_zero, ← IsIso.inv_hom_id f]
        simp only [h0, comp_zero]
      exact CategoryTheory.id_ne_zero X (rightAdjointMate_injective h)
    · have : IsIso g := CategoryTheory.isIso_of_epi_of_ne_zero (mt hg0.1 h0)
      -- The mate of `inv g` inverts `gᘁ = f`; the identity of `(ᘁY)ᘁ` is that of `Y`, since
      -- `(ᘁY)ᘁ = Y` holds by definition (`CategoryTheory.rightDual_leftDual`).
      rw [← hg]
      exact ⟨⟨(inv g)ᘁ,
        by rw [← comp_rightAdjointMate, IsIso.inv_hom_id, rightAdjointMate_id]; rfl,
        by rw [← comp_rightAdjointMate, IsIso.hom_inv_id, rightAdjointMate_id]⟩⟩

end Abelian

/-- In a right rigid monoidal preadditive category with kernels and simple tensor unit, the tensor
product of two nonzero objects is nonzero. -/
theorem not_isZero_tensorObj [Preadditive C] [HasKernels C] [MonoidalPreadditive C]
    [RightRigidCategory C] [Simple (𝟙_ C)] {X Y : C} (hX : ¬IsZero X) (hY : ¬IsZero Y) :
    ¬IsZero (X ⊗ Y) := by
  intro h
  have : Mono (η_ Y Yᘁ) := CategoryTheory.mono_of_ne_zero_from_simple (coevaluation_ne_zero hY)
  have : Mono (X ◁ η_ Y Yᘁ) :=
    (CategoryTheory.Functor.preservesMonomorphisms_of_adjunction
      (tensorLeftAdjunction X Xᘁ)).preserves (η_ Y Yᘁ)
  have h' : IsZero (X ⊗ Y ⊗ Yᘁ) := ((tensorRight Yᘁ).map_isZero h).of_iso (α_ X Y Yᘁ).symm
  refine hX (IsZero.of_iso ?_ (ρ_ X).symm)
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (X ◁ η_ Y Yᘁ)]
  exact h'.eq_of_tgt _ _

/-- If the right member `Y` of an exact pairing has scalar endomorphisms over `R`, every morphism
from the paired tensor product to the unit is a scalar multiple of the evaluation. -/
theorem hom_tensorUnit_eq_smul_evaluation_of_surjective_right {R : Type*} [CommSemiring R]
    [Preadditive C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
    {X Y : C} [ExactPairing X Y] (hY : Function.Surjective (algebraMap R (End Y)))
    (f : Y ⊗ X ⟶ 𝟙_ C) : ∃ c : R, f = c • ε_ X Y := by
  let e := (tensorRightHomLinearEquiv R Y X Y (𝟙_ C)).trans
    (Linear.homCongr R (Iso.refl Y) (λ_ Y))
  obtain ⟨c, hc⟩ := End.exists_smul_id_eq_of_surjective hY (e f)
  refine ⟨c, e.injective ?_⟩
  rw [map_smul, ← hc]
  congr 1
  -- Frobenius reciprocity carries evaluation to the identity, with the unitors removed.
  simp only [e, LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.refl_inv,
    Category.id_comp, tensorRightHomLinearEquiv_apply]
  simp [tensorRightHomEquiv, ExactPairing.coevaluation_evaluation]

/-- If the left member `X` of an exact pairing has scalar endomorphisms over `R`, every morphism
from the paired tensor product to the unit is a scalar multiple of the evaluation. -/
theorem hom_tensorUnit_eq_smul_evaluation_of_surjective_left {R : Type*} [CommSemiring R]
    [Preadditive C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
    {X Y : C} [ExactPairing X Y] (hX : Function.Surjective (algebraMap R (End X)))
    (f : Y ⊗ X ⟶ 𝟙_ C) : ∃ c : R, f = c • ε_ X Y := by
  let e := (tensorLeftHomLinearEquiv R X X Y (𝟙_ C)).trans
    (Linear.homCongr R (Iso.refl X) (ρ_ X))
  obtain ⟨c, hc⟩ := End.exists_smul_id_eq_of_surjective hX (e f)
  refine ⟨c, e.injective ?_⟩
  rw [map_smul, ← hc]
  congr 1
  -- The other Frobenius reciprocity bijection carries evaluation to the identity of `X`.
  simp only [e, LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.refl_inv,
    Category.id_comp, tensorLeftHomLinearEquiv_apply]
  simp [tensorLeftHomEquiv, ExactPairing.evaluation_coevaluation]

section FiniteSemisimple

variable {R : Type*} [CommSemiring R] [Abelian C] [MonoidalPreadditive C] [Linear R C]
  [MonoidalLinear R C] [IsFiniteSemisimpleCategory C]

omit [MonoidalPreadditive C] [MonoidalLinear R C] in
/-- In a finite semisimple category, if every morphism `Z ⟶ 𝟙_ C` is a scalar multiple of `g`,
then `g` closes up every nonzero `η : 𝟙_ C ⟶ Z` to a nonzero endomorphism of the unit. -/
private theorem comp_ne_zero_of_forall_eq_smul {Z : C} {g : Z ⟶ 𝟙_ C}
    (hg : ∀ f : Z ⟶ 𝟙_ C, ∃ c : R, f = c • g) {η : 𝟙_ C ⟶ Z} (hη : η ≠ 0) : η ≫ g ≠ 0 := by
  -- Some nonzero `a : S ⟶ 𝟙_ C` out of a simple object makes `a ≫ η` split.
  obtain ⟨S, _, a, ha, _⟩ := exists_simple_isSplitMono_comp_of_ne_zero hη
  -- Its retraction, followed by `a`, is a multiple of `g`; so `η ≫ g = 0` would kill `a`.
  obtain ⟨c, hc⟩ := hg (retraction (a ≫ η) ≫ a)
  intro h
  refine ha ?_
  rw [← IsSplitMono.id_assoc (a ≫ η) a, hc, Category.assoc, Linear.comp_smul, h, smul_zero,
    comp_zero]

/-- **Schur's lemma for an exact pairing with right member having scalar endomorphisms**: in a
finite semisimple category, if `Y` has scalar endomorphisms over `R`, every nonzero
`η : 𝟙_ C ⟶ Y ⊗ X` closes up with the evaluation of an exact pairing of `X` and `Y` to a nonzero
endomorphism of the unit. The unit need not be simple. -/
theorem comp_evaluation_ne_zero_of_surjective_right {X Y : C} [ExactPairing X Y]
    (hY : Function.Surjective (algebraMap R (End Y))) {η : 𝟙_ C ⟶ Y ⊗ X} (hη : η ≠ 0) :
    η ≫ ε_ X Y ≠ 0 :=
  comp_ne_zero_of_forall_eq_smul (hom_tensorUnit_eq_smul_evaluation_of_surjective_right hY) hη

/-- **Schur's lemma for an exact pairing with left member having scalar endomorphisms**: in a
finite semisimple category, if `X` has scalar endomorphisms over `R`, every nonzero
`η : 𝟙_ C ⟶ Y ⊗ X` closes up with the evaluation of an exact pairing of `X` and `Y` to a nonzero
endomorphism of the unit. The unit need not be simple. -/
theorem comp_evaluation_ne_zero_of_surjective_left {X Y : C} [ExactPairing X Y]
    (hX : Function.Surjective (algebraMap R (End X))) {η : 𝟙_ C ⟶ Y ⊗ X} (hη : η ≠ 0) :
    η ≫ ε_ X Y ≠ 0 :=
  comp_ne_zero_of_forall_eq_smul (hom_tensorUnit_eq_smul_evaluation_of_surjective_left hX) hη

end FiniteSemisimple

end TauCeti
