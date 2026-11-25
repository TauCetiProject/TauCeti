/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory
public import TauCeti.Algebra.Homology.HomotopyCategory.HomComplex.Tensor
public import TauCeti.Algebra.Homology.InternalHomComplex.Basic

/-!
# Homotopy invariance of the internal Hom complex

Let `C` be a closed monoidal preadditive category with countable products. Pre- and
postcomposition by homotopic maps of cochain complexes induce homotopic maps of internal Hom
complexes `CochainComplex.internalHomComplex K L`. Under the identification of morphisms
`T ⟶ 𝓗om^n(K, L)` with degree `n` cochains `K ⊗ T ⟶ L`, a homotopy `h` from `g` to `g'` in the
target acts by `z ↦ z ∘ h`, and a homotopy `h` from `f` to `f'` in the source acts by
`z ↦ (-1)ⁿ (h ⊗ T) ∘ z`, exactly as for Hom complexes of abelian groups.

Hence the internal Hom complex descends to a bifunctor
`TauCeti.internalHomComplexHomotopyFunctor C : K(C)ᵒᵖ ⥤ K(C) ⥤ K(C)` on homotopy categories,
contravariant in the source and covariant in the target. Composed with K-injective replacements,
this bifunctor defines the derived internal Hom.

## Main definitions

* `TauCeti.internalHomComplexPrecompHomotopy` and `TauCeti.internalHomComplexPostcompHomotopy`:
  the homotopies induced by a homotopy in the source or in the target.
* `TauCeti.internalHomComplexHomotopyFunctor`: the internal Hom complex on homotopy categories.

## References

* [Stacks Project, Section 20.41 (0A8K)](https://stacks.math.columbia.edu/tag/0A8K): the Hom
  complex of complexes of `𝒪_X`-modules.
* The construction of the homotopies and of the bifunctor on homotopy categories follows
  `TauCeti.linearHomComplexPrecompHomotopy`, `TauCeti.linearHomComplexPostcompHomotopy` and
  `TauCeti.linearHomComplexHomotopyFunctor` for the `R`-linear Hom complex.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed CochainComplex CochainComplex.HomComplex

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [HasCountableProducts C]

variable {K₁ K₂ L₁ L₂ : CochainComplex C ℤ}

/-- The degree `0` component of the differential of a degree `-1` cochain `H` between internal
Hom complexes, transported to cochains: on `φ : T ⟶ 𝓗om^p(K₁, L₁)` it is the differential of
`φ ≫ H` plus `H` applied to the differential of `φ`. -/
private lemma internalHomComplexHomEquiv_comp_δ_v
    (H : Cochain (internalHomComplex K₁ L₁) (internalHomComplex K₂ L₂) (-1)) {T : C} (p : ℤ)
    (φ : T ⟶ (internalHomComplex K₁ L₁).X p) :
    internalHomComplexHomEquiv K₂ L₂ T p (φ ≫ (δ (-1) 0 H).v p p (add_zero p)) =
      δ (p - 1) p (internalHomComplexHomEquiv K₂ L₂ T (p - 1) (φ ≫ H.v p (p - 1) (by omega))) +
        internalHomComplexHomEquiv K₂ L₂ T p
          ((φ ≫ (internalHomComplex K₁ L₁).d p (p + 1)) ≫ H.v (p + 1) p (by omega)) := by
  rw [δ_v (-1) 0 (by omega) _ p p (add_zero p) (p - 1) (p + 1) (by omega) rfl,
    Int.negOnePow_zero, one_smul, Preadditive.comp_add, map_add, ← Category.assoc,
    internalHomComplexHomEquiv_comp_d, Category.assoc]

section Postcomp

/-- The components `z ↦ z ∘ h` of the homotopy induced by a degree `-1` cochain `h` in the
target. -/
private def postcompHomotopyHom (K : CochainComplex C ℤ) (h : Cochain L₁ L₂ (-1)) (p q : ℤ)
    (hpq : p + -1 = q) :
    (internalHomComplex K L₁).X p ⟶ (internalHomComplex K L₂).X q :=
  (internalHomComplexHomEquiv K L₂ _ q).symm
    ((internalHomComplexHomEquiv K L₁ _ p (𝟙 _)).comp h hpq)

private lemma internalHomComplexHomEquiv_comp_postcompHomotopyHom (K : CochainComplex C ℤ)
    (h : Cochain L₁ L₂ (-1)) {T : C} {p q : ℤ} (hpq : p + -1 = q)
    (φ : T ⟶ (internalHomComplex K L₁).X p) :
    internalHomComplexHomEquiv K L₂ T q (φ ≫ postcompHomotopyHom K h p q hpq) =
      (internalHomComplexHomEquiv K L₁ T p φ).comp h hpq := by
  rw [internalHomComplexHomEquiv_comp, postcompHomotopyHom, AddEquiv.apply_symm_apply,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← internalHomComplexHomEquiv_comp,
    Category.comp_id]

/-- A homotopy between `g` and `g'` induces a homotopy between postcomposition by `g` and
postcomposition by `g'` on internal Hom complexes. -/
def internalHomComplexPostcompHomotopy (K : CochainComplex C ℤ) {g g' : L₁ ⟶ L₂}
    (h : Homotopy g g') :
    Homotopy (internalHomComplexPostcomp K g) (internalHomComplexPostcomp K g') :=
  (Cochain.equivHomotopy _ _).symm
    ⟨Cochain.mk (postcompHomotopyHom K (Cochain.ofHomotopy h)), by
      refine Cochain.ext _ _ fun p q hpq ↦ ?_
      obtain rfl : p = q := by omega
      refine internalHomComplex_hom_ext' ?_
      simp only [Cochain.add_v, Cochain.ofHom_v, Preadditive.comp_add, map_add,
        internalHomComplexHomEquiv_comp_δ_v, Cochain.mk_v,
        internalHomComplexHomEquiv_comp_postcompHomotopyHom, internalHomComplexHomEquiv_comp_d,
        internalHomComplexHomEquiv_comp_postcomp_f]
      -- The cochain identity `δ (z ∘ h) + (δ z) ∘ h + z ∘ g = z ∘ g'`, from `δ h = g' - g`.
      rw [δ_comp _ _ _ (p + 1) 0 p (by omega) rfl (by omega), δ_ofHomotopy, Cochain.comp_sub]
      simp only [Int.reduceNeg, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
      abel⟩

end Postcomp

section Precomp

/-- The components `z ↦ (-1)ᵖ (h ⊗ T) ∘ z` of the homotopy induced by a homotopy `h` in the
source, on the degree `p` term. -/
private def precompHomotopyHom {f f' : K₁ ⟶ K₂} (h : Homotopy f f') (L : CochainComplex C ℤ)
    (p q : ℤ) (hpq : p + -1 = q) :
    (internalHomComplex K₂ L).X p ⟶ (internalHomComplex K₁ L).X q :=
  (internalHomComplexHomEquiv K₁ L _ q).symm
    (p.negOnePow • (Cochain.ofHomotopy ((tensorRight _).mapHomotopy h)).comp
      (internalHomComplexHomEquiv K₂ L _ p (𝟙 _)) (by omega))

private lemma internalHomComplexHomEquiv_comp_precompHomotopyHom {f f' : K₁ ⟶ K₂}
    (h : Homotopy f f') (L : CochainComplex C ℤ) {T : C} {p q : ℤ} (hpq : p + -1 = q)
    (φ : T ⟶ (internalHomComplex K₂ L).X p) :
    internalHomComplexHomEquiv K₁ L T q (φ ≫ precompHomotopyHom h L p q hpq) =
      p.negOnePow • (Cochain.ofHomotopy ((tensorRight T).mapHomotopy h)).comp
        (internalHomComplexHomEquiv K₂ L T p φ) (by omega) := by
  rw [internalHomComplexHomEquiv_comp, precompHomotopyHom, AddEquiv.apply_symm_apply,
    Cochain.comp_units_smul, ← Cochain.comp_assoc _ _ _ (zero_add (-1)) (by omega) (by omega),
    Homotopy.ofHom_whiskerLeft_comp_ofHomotopy,
    Cochain.comp_assoc _ _ _ (add_zero (-1)) (zero_add p) (by omega),
    ← internalHomComplexHomEquiv_comp, Category.comp_id]

/-- A homotopy between `f` and `f'` induces a homotopy between precomposition by `f` and
precomposition by `f'` on internal Hom complexes. -/
def internalHomComplexPrecompHomotopy {f f' : K₁ ⟶ K₂} (h : Homotopy f f')
    (L : CochainComplex C ℤ) :
    Homotopy (internalHomComplexPrecomp f L) (internalHomComplexPrecomp f' L) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨Cochain.mk (precompHomotopyHom h L), by
      refine Cochain.ext _ _ fun p q hpq ↦ ?_
      obtain rfl : p = q := by omega
      refine internalHomComplex_hom_ext' ?_
      simp only [Cochain.add_v, Cochain.ofHom_v, Preadditive.comp_add, map_add,
        internalHomComplexHomEquiv_comp_δ_v, Cochain.mk_v,
        internalHomComplexHomEquiv_comp_precompHomotopyHom, internalHomComplexHomEquiv_comp_d,
        internalHomComplexHomEquiv_comp_precomp_f]
      -- The cochain identity `δ (±(h ⊗ T) ∘ z) ± (h ⊗ T) ∘ δ z + (f ⊗ T) ∘ z = (f' ⊗ T) ∘ z`,
      -- from `δ (h ⊗ T) = f' ⊗ T - f ⊗ T`.
      rw [δ_units_smul, δ_comp _ _ _ 0 (p + 1) p (by omega) (by omega) rfl, δ_ofHomotopy,
        Cochain.sub_comp, Int.negOnePow_succ, smul_add, smul_smul, Int.units_mul_self]
      simp only [one_smul, Units.neg_smul]
      abel⟩

end Precomp

variable (C) in
/-- The internal Hom complex as a bifunctor on homotopy categories, contravariant in the source
and covariant in the target. On the images of complexes `K` and `L` it is the image of
`CochainComplex.internalHomComplex K L`. -/
-- Expose the object assignment so that the values on images of complexes have computed types.
@[expose]
def internalHomComplexHomotopyFunctor :
    (HomotopyCategory C (.up ℤ))ᵒᵖ ⥤ HomotopyCategory C (.up ℤ) ⥤
      HomotopyCategory C (.up ℤ) :=
  Functor.leftOp <| CategoryTheory.Quotient.lift _
    { obj K := .op <| CategoryTheory.Quotient.lift _
        ((internalHomComplexFunctor C).obj (.op K) ⋙ HomotopyCategory.quotient _ _)
        (fun _ _ _ _ ⟨h⟩ ↦ HomotopyCategory.eq_of_homotopy _ _
          (internalHomComplexPostcompHomotopy K h))
      map f := .op <| CategoryTheory.Quotient.natTransLift _
        (Functor.whiskerRight ((internalHomComplexFunctor C).map f.op)
          (HomotopyCategory.quotient _ _))
      map_id K := by
        -- After `simp`, both sides agree up to `Quotient.lift_obj_functor_obj`, which is `rfl`.
        apply Quiver.Hom.unop_inj
        apply CategoryTheory.Quotient.natTrans_ext
        ext L
        simp
        rfl
      map_comp f f' := by
        apply Quiver.Hom.unop_inj
        refine Eq.trans ?_ (CategoryTheory.Quotient.comp_natTransLift _ _ _).symm
        rw [op_comp, Functor.map_comp, Functor.whiskerRight_comp]
        rfl }
    (fun _ _ _ _ ⟨h⟩ ↦ by
      apply Quiver.Hom.unop_inj
      apply CategoryTheory.Quotient.natTrans_ext
      ext L
      exact HomotopyCategory.eq_of_homotopy _ _ (internalHomComplexPrecompHomotopy h L))

@[simp]
lemma internalHomComplexHomotopyFunctor_obj_obj (K L : CochainComplex C ℤ) :
    ((internalHomComplexHomotopyFunctor C).obj
        (.op ((HomotopyCategory.quotient C _).obj K))).obj
          ((HomotopyCategory.quotient C _).obj L) =
      (HomotopyCategory.quotient _ _).obj (internalHomComplex K L) :=
  (rfl)

@[simp]
lemma internalHomComplexHomotopyFunctor_obj_map (K : CochainComplex C ℤ) (g : L₁ ⟶ L₂) :
    ((internalHomComplexHomotopyFunctor C).obj
        (.op ((HomotopyCategory.quotient C _).obj K))).map
          ((HomotopyCategory.quotient C _).map g) =
      (HomotopyCategory.quotient _ _).map (internalHomComplexPostcomp K g) :=
  (rfl)

@[simp]
lemma internalHomComplexHomotopyFunctor_map_app (f : K₁ ⟶ K₂) (L : CochainComplex C ℤ) :
    ((internalHomComplexHomotopyFunctor C).map ((HomotopyCategory.quotient C _).map f).op).app
        ((HomotopyCategory.quotient C _).obj L) =
      (HomotopyCategory.quotient _ _).map (internalHomComplexPrecomp f L) :=
  (rfl)

end TauCeti
