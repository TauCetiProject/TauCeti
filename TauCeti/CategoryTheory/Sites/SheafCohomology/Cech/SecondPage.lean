/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.FirstDifferential

/-!
# The second page of the Čech-to-cohomology spectral sequence

Let `U` be a family of objects of a site and `F` an abelian sheaf with an injective resolution
`R`. The first page (numbered `2`) of the Čech-to-cohomology spectral sequence has the Čech
cochains `Čᵖ(U, Hᵏ(F))` of the cohomology presheaf `V ↦ Hᵏ(V, F)` as objects, and its
differential is, up to the sign `(-1)^k`, the Čech differential
(`TauCeti.CategoryTheory.cechToCohomologySpectralSequence_page_two_d`). This file identifies the
objects of the next page (numbered `3`) with the Čech cohomology groups `Hᵖ(Č(U, Hᵏ(F)))`, the
cohomology in degree `p` of the Čech complex `Č(U, Hᵏ(F))`
(`TauCeti.CategoryTheory.cechToCohomologySecondPageXIso`, Stacks, Lemma 21.10.6 (03AZ)).

As for the first differential, this is first done for any cochain complex `I` of presheaves with
values in an abelian category with exact products, and a presheaf `P` isomorphic to the cohomology
presheaf `Hᵏ(I)` (`TauCeti.CategoryTheory.presheafCechDoubleComplexSpectralSequenceSecondPageXIso`):
the object of the second page is the homology of the first page at the same place, which is
computed from the first differentials into and out of it. Since the spectral sequence lives in the
opposite category `Aᵒᵖ`, the differential into the object at Čech degree `p` comes from Čech degree
`p + 1`, and the one out of it goes to Čech degree `p - 1`; in Čech degree `0` the latter has a
zero target, the first page vanishing in negative Čech degrees.

## Main declarations

* `TauCeti.CategoryTheory.presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso`: the first
  page as Čech cochains of a presheaf isomorphic to the cohomology presheaf.
* `TauCeti.CategoryTheory.presheafCechDoubleComplexSpectralSequenceSecondPageXIso`,
  `TauCeti.CategoryTheory.cechToCohomologySecondPageXIso`: the second page is Čech cohomology.

## References

* [Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV), Section 21.10 on Čech
  cohomology and cohomology, Lemma 21.10.6 (tag 03AZ) for the spectral sequence.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe w v u

namespace TauCeti.CategoryTheory

section Sign

variable {A : Type*} [Category* A] [Preadditive A]

/-- A sign `(-1)^k` times an isomorphism is an isomorphism. -/
lemma isIso_neg_one_pow_zsmul (k : ℕ) {X Y : A} (f : X ⟶ Y) [IsIso f] :
    IsIso (((-1 : ℤ) ^ k) • f) :=
  ⟨((-1 : ℤ) ^ k) • inv f, by
    simp [smul_smul, ← mul_pow], by simp [smul_smul, ← mul_pow]⟩

end Sign

section General

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type*} [Category* A]
  [Abelian A] [HasProducts.{w} A] {ι : Type w} (U : ι → C)
  [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin n → ι)) A]
  (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (k : ℕ) {P : Cᵒᵖ ⥤ A} (e : I.homology k ≅ P)

/-- The object at `(-k - 2p, p)` on the first page (numbered `2`) of the spectral sequence of the
Čech double complex is the opposite of the Čech cochains `Čᵖ(U, P)` of a presheaf `P` isomorphic
to the cohomology presheaf `Hᵏ(I)`. -/
def presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso (p : ℕ) :
    ((presheafCechDoubleComplexSpectralSequence U I).page 2).X (-(k : ℤ) - 2 * p, p) ≅
      op (((cechComplexFunctor U).obj P).X p) :=
  presheafCechDoubleComplexSpectralSequenceFirstPageXIso U I p k ≪≫
    (presheafCechColumnHomologyIso U I p k ≪≫
      (cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) p).mapIso e).symm.op

/-- The identification `presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso` is that of
the first page with the column homology, followed by `presheafCechColumnHomologyIso` and `e`. -/
lemma presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso_hom (p : ℕ) :
    (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I k e p).hom =
      (presheafCechDoubleComplexSpectralSequenceFirstPageXIso U I p k).hom ≫
        ((cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) p).map e.inv ≫
          (presheafCechColumnHomologyIso U I p k).inv).op :=
  (rfl)

/-- The first differential, from `(-k - 2(p + 1), p + 1)` to `(-k - 2p, p)`, is `(-1)^k` times
the opposite of the Čech differential of `P` under
`presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso`. -/
lemma presheafCechDoubleComplexSpectralSequence_page_two_d_firstPageXIsoOfIso (p : ℕ) :
    ((presheafCechDoubleComplexSpectralSequence U I).page 2).d
        (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p) ≫
      (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I k e p).hom =
    (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I k e (p + 1)).hom ≫
      (((-1 : ℤ) ^ k) • (((cechComplexFunctor U).obj P).d p (p + 1)).op) := by
  rw [presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso_hom,
    presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso_hom]
  exact presheafCechDoubleComplexSpectralSequence_page_two_d_comp_iso U I p k e

/-- The morphism from the short complex of the first page at `(-k - 2p, p)` to the opposite of
the short complex of the Čech complex of `P` at degree `p`, given the component `τ₃` on the target
of the outgoing differential, for `q` the Čech degree before `p`. Its first component is an
isomorphism, its second is `(-1)^k` times one. -/
def presheafCechDoubleComplexSpectralSequenceFirstPageShortComplexHom (p q : ℕ) (j : ℤ × ℤ)
    (τ₃ : ((presheafCechDoubleComplexSpectralSequence U I).page 2).X j ⟶
      op (((cechComplexFunctor U).obj P).X q))
    (hg : ((presheafCechDoubleComplexSpectralSequence U I).page 2).d (-(k : ℤ) - 2 * p, p) j ≫
        τ₃ = ((-1 : ℤ) ^ k) • ((presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso
          U I k e p).hom ≫ (((cechComplexFunctor U).obj P).d q p).op)) :
    ((presheafCechDoubleComplexSpectralSequence U I).page 2).sc'
        (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p) j ⟶
      (((cechComplexFunctor U).obj P).sc' q p (p + 1)).op where
  τ₁ := (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I k e (p + 1)).hom
  τ₂ := ((-1 : ℤ) ^ k) •
    (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I k e p).hom
  τ₃ := τ₃
  comm₁₂ := by
    change _ ≫ (((cechComplexFunctor U).obj P).d p (p + 1)).op =
      ((presheafCechDoubleComplexSpectralSequence U I).page 2).d _ _ ≫ (((-1 : ℤ) ^ k) • _)
    rw [Preadditive.comp_zsmul,
      presheafCechDoubleComplexSpectralSequence_page_two_d_firstPageXIsoOfIso U I k e p,
      Preadditive.comp_zsmul, smul_smul, ← mul_pow]
    simp
  comm₂₃ := by
    change (((-1 : ℤ) ^ k) • _) ≫ (((cechComplexFunctor U).obj P).d q p).op =
      ((presheafCechDoubleComplexSpectralSequence U I).page 2).d _ _ ≫ τ₃
    rw [hg, Preadditive.zsmul_comp]

/-- The object of the second page at `(-k - 2p, p)` is the opposite of the Čech cohomology, given
the target `j` of the outgoing first differential and a monomorphism `τ₃` from it compatible with
the Čech differential into degree `p`, from the degree `q` before `p`. -/
def presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom (p q : ℕ) (j : ℤ × ℤ)
    (hq : (ComplexShape.up ℕ).prev p = q)
    (hj : (ComplexShape.up' ((2 : ℤ), 1 - 2)).next (-(k : ℤ) - 2 * p, (p : ℤ)) = j)
    (τ₃ : ((presheafCechDoubleComplexSpectralSequence U I).page 2).X j ⟶
      op (((cechComplexFunctor U).obj P).X q)) [Mono τ₃]
    (hg : ((presheafCechDoubleComplexSpectralSequence U I).page 2).d (-(k : ℤ) - 2 * p, p) j ≫
        τ₃ = ((-1 : ℤ) ^ k) • ((presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso
          U I k e p).hom ≫ (((cechComplexFunctor U).obj P).d q p).op)) :
    ((presheafCechDoubleComplexSpectralSequence U I).page 3).X (-(k : ℤ) - 2 * p, p) ≅
      op (((cechComplexFunctor U).obj P).homology p) :=
  have := isIso_neg_one_pow_zsmul k
    (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I k e p).hom
  have : IsIso (ShortComplex.homologyMap
      (presheafCechDoubleComplexSpectralSequenceFirstPageShortComplexHom U I k e p q j τ₃ hg)) :=
    ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _
      (inferInstanceAs
        (Epi (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I k e (p + 1)).hom))
      (inferInstanceAs (IsIso (((-1 : ℤ) ^ k) •
        (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I k e p).hom)))
      (inferInstanceAs (Mono τ₃))
  ((presheafCechDoubleComplexSpectralSequence U I).iso 2 3 _ (by norm_num) (by norm_num)).symm ≪≫
    HomologicalComplex.homologyIsoSc' _ _ _ _
      (ComplexShape.prev_eq' _ (by ext <;> simp; lia)) hj ≪≫
    asIso (ShortComplex.homologyMap
      (presheafCechDoubleComplexSpectralSequenceFirstPageShortComplexHom U I k e p q j τ₃ hg)) ≪≫
    (((cechComplexFunctor U).obj P).sc' q p (p + 1)).homologyOpIso ≪≫
    (((cechComplexFunctor U).obj P).homologyIsoSc' q p (p + 1) hq (by simp)).op

/-- **The second page of the spectral sequence of the Čech double complex.** With exact products,
its object at `(-k - 2p, p)` (the first page being numbered `2`) is the opposite of the Čech
cohomology `Hᵖ(Č(U, P))` of a presheaf `P` isomorphic to the cohomology presheaf `Hᵏ(I)`: the
cohomology in degree `p` of the Čech complex `Č(U, P)`. -/
def presheafCechDoubleComplexSpectralSequenceSecondPageXIso : (p : ℕ) →
    ((presheafCechDoubleComplexSpectralSequence U I).page 3).X (-(k : ℤ) - 2 * p, p) ≅
      op (((cechComplexFunctor U).obj P).homology p)
  | 0 =>
    have hZ : IsZero (((presheafCechDoubleComplexSpectralSequence U I).page 2).X
        (-(k : ℤ) + 2, -1)) :=
      (presheafCechDoubleComplex U I).flip.isZero_rowFiltrationSpectralSequence_page_X 2 le_rfl
        _ _ (Or.inl (by norm_num))
    have : Mono (0 : ((presheafCechDoubleComplexSpectralSequence U I).page 2).X
        (-(k : ℤ) + 2, -1) ⟶ op (((cechComplexFunctor U).obj P).X 0)) :=
      ⟨fun _ _ _ ↦ hZ.eq_of_tgt _ _⟩
    presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom U I k e 0 0 (-(k : ℤ) + 2, -1)
      CochainComplex.prev_nat_zero (ComplexShape.next_eq' _ (by ext <;> simp)) 0
      (by rw [((cechComplexFunctor U).obj P).shape 0 0 (by simp)]; simp only [Limits.comp_zero,
        op_zero]; exact (zsmul_zero _).symm)
  | p + 1 =>
    have : Mono (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I k e p).hom :=
      inferInstance
    presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom U I k e (p + 1) p
      (-(k : ℤ) - 2 * p, p) (CochainComplex.prev_nat_succ p)
      (ComplexShape.next_eq' _ (by ext <;> simp; lia))
      (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I k e p).hom
      (by rw [presheafCechDoubleComplexSpectralSequence_page_two_d_firstPageXIsoOfIso,
        Preadditive.comp_zsmul])

end General

section Sheaf

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] {ι : Type v} (U : ι → C)
  {F : Sheaf J AddCommGrpCat.{v}} (R : InjectiveResolution F)
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- **The second page of the Čech-to-cohomology spectral sequence.** Its object at `(-k - 2p, p)`
(the first page being numbered `2`) is the opposite of the Čech cohomology group `Hᵖ(Č(U, Hᵏ(F)))`,
the cohomology in degree `p` of the Čech complex of the cohomology presheaf `V ↦ Hᵏ(V, F)`. -/
def cechToCohomologySecondPageXIso (p k : ℕ) :
    ((cechToCohomologySpectralSequence U R).page 3).X (-(k : ℤ) - 2 * p, p) ≅
      op (((cechComplexFunctor U).obj (F.cohomologyPresheaf k)).homology p) :=
  presheafCechDoubleComplexSpectralSequenceSecondPageXIso U R.presheafComplex k
    (_root_.CategoryTheory.Sheaf.H'.homologyIsoCohomologyPresheaf (R.ι.f 0)
      R.ι_f_zero_comp_complex_d R.exact₀ R.cocomplex_exactAt_succ
      (fun _ j k ↦ Abelian.Ext.subsingleton_of_injective _ (R.cocomplex.X j) k) k) p

end Sheaf

end TauCeti.CategoryTheory
