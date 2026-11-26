/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.Opposite
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

* `TauCeti.CategoryTheory.presheafCechDoubleComplexSpectralSequenceSecondPageXIso`,
  `TauCeti.CategoryTheory.cechToCohomologySecondPageXIso`: the second page is Čech cohomology.
* `TauCeti.CategoryTheory.homologyπ_cechToCohomologySecondPageXIso_hom_homologyπ_op`: on the class
  of a cycle of the first page, this identification is the class of the corresponding Čech
  cocycle, under the identification `TauCeti.CategoryTheory.cechToCohomologyFirstPageXIso` of the
  first page with Čech cochains.

## References

* [Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV), Section 21.10 on Čech
  cohomology and cohomology, Lemma 21.10.6 (tag 03AZ) for the spectral sequence.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe w v u

namespace TauCeti.CategoryTheory

section General

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type*} [Category* A]
  [Abelian A] [HasProducts.{w} A] {ι : Type w} (U : ι → C)
  (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (k : ℕ) {P : Cᵒᵖ ⥤ A} (e : I.homology k ≅ P)

/-- The morphism from the short complex of the first page at `(-k - 2p, p)` to the opposite of
the short complex of the Čech complex of `P` at degree `p`, given the component `τ₃` on the target
of the outgoing differential, for `q` the Čech degree before `p`. Its first component is `(-1)^k`
times an isomorphism, its second is an isomorphism. -/
@[simps]
private def presheafCechDoubleComplexSpectralSequenceFirstPageShortComplexHom (p q : ℕ)
    [HasExactLimitsOfShape (Discrete (Fin (p + 1) → ι)) A]
    [HasExactLimitsOfShape (Discrete (Fin (p + 1 + 1) → ι)) A] (j : ℤ × ℤ)
    (τ₃ : ((presheafCechDoubleComplexSpectralSequence U I).page 2).X j ⟶
      op (((cechComplexFunctor U).obj P).X q))
    (hg : ((presheafCechDoubleComplexSpectralSequence U I).page 2).d (-(k : ℤ) - 2 * p, p) j ≫
        τ₃ = (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I p k e).hom ≫
          (((cechComplexFunctor U).obj P).d q p).op) :
    ((presheafCechDoubleComplexSpectralSequence U I).page 2).sc'
        (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p) j ⟶
      (((cechComplexFunctor U).obj P).sc' q p (p + 1)).op where
  τ₁ := (((-1 : ℤˣ) ^ k) •
    presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I (p + 1) k e).hom
  τ₂ := (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I p k e).hom
  τ₃ := τ₃
  comm₁₂ := by
    dsimp only [shortComplexFunctor'_obj_f, ShortComplex.op_f, shortComplexFunctor'_obj_g]
    rw [presheafCechDoubleComplexSpectralSequence_page_two_d_comp_iso]
    simp [Units.smul_def]
  comm₂₃ := by
    dsimp only [shortComplexFunctor'_obj_g, ShortComplex.op_g, shortComplexFunctor'_obj_f]
    exact hg.symm

/-- The object of the second page at `(-k - 2p, p)` is the opposite of the Čech cohomology, given
the target `j` of the outgoing first differential and a monomorphism `τ₃` from it compatible with
the Čech differential into degree `p`, from the degree `q` before `p`. -/
private def presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom (p q : ℕ)
    [HasExactLimitsOfShape (Discrete (Fin (p + 1) → ι)) A]
    [HasExactLimitsOfShape (Discrete (Fin (p + 1 + 1) → ι)) A] (j : ℤ × ℤ)
    (hq : (ComplexShape.up ℕ).prev p = q)
    (hj : (ComplexShape.up' ((2 : ℤ), 1 - 2)).next (-(k : ℤ) - 2 * p, (p : ℤ)) = j)
    (τ₃ : ((presheafCechDoubleComplexSpectralSequence U I).page 2).X j ⟶
      op (((cechComplexFunctor U).obj P).X q)) [Mono τ₃]
    (hg : ((presheafCechDoubleComplexSpectralSequence U I).page 2).d (-(k : ℤ) - 2 * p, p) j ≫
        τ₃ = (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I p k e).hom ≫
          (((cechComplexFunctor U).obj P).d q p).op) :
    ((presheafCechDoubleComplexSpectralSequence U I).page 3).X (-(k : ℤ) - 2 * p, p) ≅
      op (((cechComplexFunctor U).obj P).homology p) :=
  have : IsIso (ShortComplex.homologyMap
      (presheafCechDoubleComplexSpectralSequenceFirstPageShortComplexHom U I k e p q j τ₃ hg)) :=
    ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _
      (inferInstanceAs (Epi (((-1 : ℤˣ) ^ k) •
        presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I (p + 1) k e).hom))
      (inferInstanceAs
        (IsIso (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I p k e).hom))
      (inferInstanceAs (Mono τ₃))
  ((presheafCechDoubleComplexSpectralSequence U I).iso 2 3 (-(k : ℤ) - 2 * p, p)).symm ≪≫
    HomologicalComplex.homologyIsoSc' _ _ _ _
      (ComplexShape.prev_eq' _ (by ext <;> simp; lia)) hj ≪≫
    asIso (ShortComplex.homologyMap
      (presheafCechDoubleComplexSpectralSequenceFirstPageShortComplexHom U I k e p q j τ₃ hg)) ≪≫
    (((cechComplexFunctor U).obj P).sc' q p (p + 1)).homologyOpIso ≪≫
    (((cechComplexFunctor U).obj P).homologyIsoSc' q p (p + 1) hq (by simp)).op

/-- `presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom` is characterized on cycles: a
cycle of the first page at `(-k - 2p, p)`, sent to the second page and then to the opposite of
the Čech cohomology `Hᵖ(Č(U, P))`, is the Čech cochain it corresponds to under
`presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso`, as a Čech cocycle. -/
private lemma
    homologyπ_presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom_hom_homologyπ_op
    (p q : ℕ) [HasExactLimitsOfShape (Discrete (Fin (p + 1) → ι)) A]
    [HasExactLimitsOfShape (Discrete (Fin (p + 1 + 1) → ι)) A] (j : ℤ × ℤ)
    (hq : (ComplexShape.up ℕ).prev p = q)
    (hj : (ComplexShape.up' ((2 : ℤ), 1 - 2)).next (-(k : ℤ) - 2 * p, (p : ℤ)) = j)
    -- The page bound is given as `le_rfl`: its default `lia` proof fails to elaborate in the
    -- statement of this private lemma.
    (τ₃ : ((presheafCechDoubleComplexSpectralSequence U I).page 2 le_rfl).X j ⟶
      op (((cechComplexFunctor U).obj P).X q)) [Mono τ₃]
    (hg : ((presheafCechDoubleComplexSpectralSequence U I).page 2).d (-(k : ℤ) - 2 * p, p) j ≫
        τ₃ = (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I p k e).hom ≫
          (((cechComplexFunctor U).obj P).d q p).op) :
    ((presheafCechDoubleComplexSpectralSequence U I).page 2).homologyπ (-(k : ℤ) - 2 * p, p) ≫
        ((presheafCechDoubleComplexSpectralSequence U I).iso 2 3 (-(k : ℤ) - 2 * p, p)).hom ≫
        (presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom U I k e p q j hq hj τ₃
          hg).hom ≫ (((cechComplexFunctor U).obj P).homologyπ p).op =
      ((presheafCechDoubleComplexSpectralSequence U I).page 2).iCycles (-(k : ℤ) - 2 * p, p) ≫
        (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I p k e).hom ≫
          (((cechComplexFunctor U).obj P).iCycles p).op := by
  -- The first call merges the opposite maps into the Čech side into `(iCycles ≫ pOpcycles).op`;
  -- the second splits it again so that `cyclesOpIso_hom_pOpcycles_op` applies.
  simp [presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom, ← op_comp]
  simp

/-- The zero morphism to the Čech cochains of degree `0` from the object at `(-k + 2, -1)` of the
first page is a monomorphism: that object is zero, the first page vanishing in negative Čech
degrees. -/
private lemma presheafCechDoubleComplexSpectralSequence_mono_zero :
    Mono (0 : ((presheafCechDoubleComplexSpectralSequence U I).page 2).X (-(k : ℤ) + 2, -1) ⟶
      op (((cechComplexFunctor U).obj P).X 0)) :=
  ⟨fun _ _ _ ↦ ((presheafCechDoubleComplex U I).flip.isZero_rowFiltrationSpectralSequence_page_X
    2 le_rfl _ _ (Or.inl (by norm_num))).eq_of_tgt _ _⟩

/-- **The second page of the spectral sequence of the Čech double complex.** With exact products,
its object at `(-k - 2p, p)` (the first page being numbered `2`) is the opposite of the Čech
cohomology `Hᵖ(Č(U, P))` of a presheaf `P` isomorphic to the cohomology presheaf `Hᵏ(I)`: the
cohomology in degree `p` of the Čech complex `Č(U, P)`. -/
def presheafCechDoubleComplexSpectralSequenceSecondPageXIso
    [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A] : (p : ℕ) →
    ((presheafCechDoubleComplexSpectralSequence U I).page 3).X (-(k : ℤ) - 2 * p, p) ≅
      op (((cechComplexFunctor U).obj P).homology p)
  | 0 =>
    have := presheafCechDoubleComplexSpectralSequence_mono_zero U I k (P := P)
    presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom U I k e 0 0 (-(k : ℤ) + 2, -1)
      CochainComplex.prev_nat_zero (ComplexShape.next_eq' _ (by ext <;> simp)) 0
      (by rw [((cechComplexFunctor U).obj P).shape 0 0 (by simp)]; simp)
  | p + 1 =>
    presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom U I k e (p + 1) p
      (-(k : ℤ) - 2 * p, p) (CochainComplex.prev_nat_succ p)
      (ComplexShape.next_eq' _ (by ext <;> simp; lia))
      (((-1 : ℤˣ) ^ k) • presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I p k e).hom
      (by
        simp only [Preadditive.smul_iso_hom, Units.smul_def, Preadditive.comp_zsmul]
        rw [presheafCechDoubleComplexSpectralSequence_page_two_d_comp_iso]
        simp [smul_smul, ← mul_pow])

/-- `presheafCechDoubleComplexSpectralSequenceSecondPageXIso` is characterized on cycles: a cycle of
the first page at `(-k - 2p, p)`, sent to the second page and then to the opposite of the Čech
cohomology `Hᵖ(Č(U, P))`, is the Čech cochain it corresponds to under
`presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso`, as a Čech cocycle. -/
lemma homologyπ_presheafCechDoubleComplexSpectralSequenceSecondPageXIso_hom_homologyπ_op
    [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A] (p : ℕ) :
    ((presheafCechDoubleComplexSpectralSequence U I).page 2).homologyπ (-(k : ℤ) - 2 * p, p) ≫
        ((presheafCechDoubleComplexSpectralSequence U I).iso 2 3 (-(k : ℤ) - 2 * p, p)).hom ≫
        (presheafCechDoubleComplexSpectralSequenceSecondPageXIso U I k e p).hom ≫
          (((cechComplexFunctor U).obj P).homologyπ p).op =
      ((presheafCechDoubleComplexSpectralSequence U I).page 2).iCycles (-(k : ℤ) - 2 * p, p) ≫
        (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I p k e).hom ≫
          (((cechComplexFunctor U).obj P).iCycles p).op := by
  cases p with
  | zero =>
    have := presheafCechDoubleComplexSpectralSequence_mono_zero U I k (P := P)
    exact homologyπ_presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom_hom_homologyπ_op
      U I k e ..
  | succ p =>
    exact homologyπ_presheafCechDoubleComplexSpectralSequenceSecondPageXIsoOfHom_hom_homologyπ_op
      U I k e ..

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

/-- `cechToCohomologySecondPageXIso` is characterized on cycles: a cycle of the first page at
`(-k - 2p, p)`, sent to the second page and then to the opposite of the Čech cohomology group
`Hᵖ(Č(U, Hᵏ(F)))`, is the Čech cochain it corresponds to under `cechToCohomologyFirstPageXIso`, as
a Čech cocycle. -/
lemma homologyπ_cechToCohomologySecondPageXIso_hom_homologyπ_op (p k : ℕ) :
    ((cechToCohomologySpectralSequence U R).page 2).homologyπ (-(k : ℤ) - 2 * p, p) ≫
        ((cechToCohomologySpectralSequence U R).iso 2 3 (-(k : ℤ) - 2 * p, p)).hom ≫
        (cechToCohomologySecondPageXIso U R p k).hom ≫
          (((cechComplexFunctor U).obj (F.cohomologyPresheaf k)).homologyπ p).op =
      ((cechToCohomologySpectralSequence U R).page 2).iCycles (-(k : ℤ) - 2 * p, p) ≫
        (cechToCohomologyFirstPageXIso U R p k).hom ≫
          (((cechComplexFunctor U).obj (F.cohomologyPresheaf k)).iCycles p).op := by
  rw [cechToCohomologyFirstPageXIso_hom]
  exact homologyπ_presheafCechDoubleComplexSpectralSequenceSecondPageXIso_hom_homologyπ_op U
    R.presheafComplex k _ p

end Sheaf

end TauCeti.CategoryTheory
