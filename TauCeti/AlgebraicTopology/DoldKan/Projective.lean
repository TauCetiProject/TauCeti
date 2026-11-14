/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import TauCeti.AlgebraicTopology.DoldKan.SimplicialHomotopy

/-!
# Non-additive functors on projective simplicial objects and the Dold–Puppe construction

In their 1961 memoir *Homologie nicht-additiver Funktoren*, Albrecht Dold and Dieter Puppe showed
how to derive arbitrary (not necessarily additive) functors `F : C ⥤ D` from an abelian category `C`
into a preadditive category `D` with homology by passing through simplicial objects via the Dold–Kan
correspondence:

1. A simplicial object `X : SimplicialObject C` has projective components if and only if its
   normalized chain complex `N.obj X` has projective components (`projective_iff_N_projective`), and
   the inverse Dold–Kan functor `Γ` sends degreewise projective chain complexes to degreewise
   projective simplicial objects (`Γ₀.projective_obj`, `Γ.projective_obj`).
2. When `X` and `Y` are degreewise projective simplicial objects in an abelian category `C`, a
   morphism `f : X ⟶ Y` induces a quasi-isomorphism on alternating face map complexes if and only
   if `f` is a simplicial homotopy equivalence
   (`quasiIso_alternatingFaceMapComplex_map_iff_of_projective`, `homotopyEquivOfQuasiIso`).
3. Because levelwise postcomposition `(SimplicialObject.whiskering C D).obj F` by *any* functor
   `F : C ⥤ D` preserves simplicial homotopies—even when `F` is non-additive—it sends weak
   equivalences between degreewise projective simplicial objects to chain homotopy equivalences and
   hence to quasi-isomorphisms (`quasiIso_whiskering_of_projective`), including when `F` is defined
   only on a full subcategory `C₀` such as `(isProjective C).FullSubcategory` or finitely generated
   projectives (`quasiIso_whiskering_of_fullyFaithful_projective`,
   `quasiIso_whiskering_isProjective`).
4. Evaluating `Idempotents.DoldKan.Γ ⋙ (whiskering C D).obj F ⋙ alternatingFaceMapComplex D`
   (`CategoryTheory.Functor.doldPuppeFunctor`) therefore carries chain homotopies to chain
   homotopies, preserves quasi-isomorphisms between degreewise projective chain complexes, agrees up
   to chain homotopy equivalence with `F.mapHomologicalComplex (.down ℕ)` when `F` is additive,
   sends `(ChainComplex.single₀ C).obj X` to `(ChainComplex.single₀ D).obj (F.obj X)` up to chain
   homotopy equivalence, and evaluates the non-additive constant functor `(Functor.const C).obj B`
   to `(ChainComplex.single₀ D).obj B` on every chain complex `K` (including `K = 0`).

## Main definitions and results

* `CategoryTheory.SimplicialObject.projective_iff_N_projective`: `X` is degreewise projective if and
  only if `Idempotents.DoldKan.N.obj X` is degreewise projective.
* `CategoryTheory.Idempotents.DoldKan.N.constIso`,
  `CategoryTheory.Idempotents.DoldKan.Γ.single₀Iso`: `N` carries `(SimplicialObject.const C).obj X`
  isomorphically to `(ChainComplex.single₀ C).obj X`, and `Γ` carries
  `(ChainComplex.single₀ C).obj X` isomorphically to `(SimplicialObject.const C).obj X`.
* `CategoryTheory.SimplicialObject.quasiIso_alternatingFaceMapComplex_map_iff_of_projective`,
  `CategoryTheory.SimplicialObject.homotopyEquivOfQuasiIso`: weak equivalences between degreewise
  projective simplicial objects coincide with simplicial homotopy equivalences.
* `CategoryTheory.SimplicialObject.quasiIso_whiskering_of_projective`,
  `CategoryTheory.SimplicialObject.quasiIso_whiskering_of_fullyFaithful_projective`,
  `CategoryTheory.SimplicialObject.quasiIso_whiskering_isProjective`: arbitrary (possibly
  non-additive) functors preserve weak equivalences between degreewise projective simplicial
  objects.
* `CategoryTheory.Functor.doldPuppeFunctor`: the Dold–Puppe chain-complex functor
  `Γ ⋙ (whiskering C D).obj F ⋙ alternatingFaceMapComplex D`, together with its homotopy,
  quasi-isomorphism, additivity, degree-zero, and constant-functor laws.

## References

* A. Dold and D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312, §§3–4 (especially 3.31 and 4.4–4.7).
* D. Quillen, *Homotopical Algebra*, Lecture Notes in Mathematics 43, Springer-Verlag (1967),
  Chapter II, §4.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press (1994),
  Chapter 8, §8.4.
-/

public noncomputable section

universe v u v' u'

open CategoryTheory Limits Opposite SimplexCategory AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial DoldKan

namespace CategoryTheory.SimplicialObject

/-- Because `SimplexCategory` is skeletal with objects `⦋n⦌`, degreewise projectivity on `⦋n⦌`
gives projectivity at every `Δ : SimplexCategoryᵒᵖ`. -/
theorem projective_obj_of_projective {C : Type u} [Category.{v} C] (X : SimplicialObject C)
    [hX : ∀ n : ℕ, Projective (X _⦋n⦌)] (Δ : SimplexCategoryᵒᵖ) :
    Projective (X.obj Δ) :=
  hX Δ.unop.len

end CategoryTheory.SimplicialObject

namespace AlgebraicTopology.DoldKan

instance Γ₀.projective_obj {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
    (K : ChainComplex C ℕ) [∀ n, Projective (K.X n)] (Δ : SimplexCategoryᵒᵖ) :
    Projective ((Γ₀.obj K).obj Δ) := by
  have : ∀ A : SimplicialObject.Splitting.IndexSet Δ, Projective (Γ₀.Obj.summand K Δ A) :=
    fun A ↦ inferInstanceAs (Projective (K.X A.1.unop.len))
  let p : Projective (∐ fun A : SimplicialObject.Splitting.IndexSet Δ ↦ Γ₀.Obj.summand K Δ A) :=
    { factors f e _ :=
        ⟨Sigma.desc fun A ↦ Projective.factorThru (Sigma.ι _ A ≫ f) e,
          Sigma.hom_ext _ _ fun A ↦ by simp⟩ }
  exact p

end AlgebraicTopology.DoldKan

namespace CategoryTheory.Idempotents.DoldKan

section Projective

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]

instance Γ.projective_obj (K : ChainComplex C ℕ) [∀ n, Projective (K.X n)]
    (Δ : SimplexCategoryᵒᵖ) :
    Projective ((Γ.obj K).obj Δ) :=
  inferInstanceAs (Projective ((Γ₀.obj K).obj Δ))

instance N.projective_X (X : SimplicialObject C) [∀ n, Projective (X _⦋n⦌)] (n : ℕ) :
    Projective ((N.obj X).X n) := by
  let r : Retract ((N.obj X).X n) (X _⦋n⦌) :=
    { i := (inclusionN.app X).f n
      r := (PInftyToN.app X).f n
      retract := by
        rw [← HomologicalComplex.comp_f, inclusionN_app_comp_PInftyToN_app,
          HomologicalComplex.id_f] }
  exact r.projective

end Projective

section ConstSingle₀

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]

omit [HasZeroObject C] in
/-- In positive degree `m + 1`, the normalized chain complex of a constant simplicial object is
zero, because every simplex is in the image of `σ 0 = 𝟙 X`. -/
lemma isZero_N_const_obj_X_succ (X : C) (m : ℕ) :
    IsZero ((N.obj ((SimplicialObject.const C).obj X)).X (m + 1)) := by
  have hP : (PInfty (X := (SimplicialObject.const C).obj X)).f (m + 1) = 0 := by
    have hσ := σ_comp_PInfty ((SimplicialObject.const C).obj X) (0 : Fin (m + 1))
    dsimp [SimplicialObject.σ] at hσ
    rwa [Category.id_comp] at hσ
  rw [IsZero.iff_id_eq_zero]
  calc
    𝟙 ((N.obj ((SimplicialObject.const C).obj X)).X (m + 1))
      = ((inclusionN.app ((SimplicialObject.const C).obj X)).f (m + 1)) ≫
          ((PInftyToN.app ((SimplicialObject.const C).obj X)).f (m + 1)) := by
        rw [← HomologicalComplex.comp_f, inclusionN_app_comp_PInftyToN_app,
          HomologicalComplex.id_f]
    _ = ((inclusionN.app ((SimplicialObject.const C).obj X)) ≫ PInfty).f (m + 1) ≫
          ((PInftyToN.app ((SimplicialObject.const C).obj X)).f (m + 1)) := by
        rw [inclusionN_app_comp_PInfty]
    _ = 0 := by
        rw [HomologicalComplex.comp_f, hP, comp_zero, zero_comp]

/-- The normalized chain complex `N.obj ((SimplicialObject.const C).obj X)` of a constant simplicial
object is canonically isomorphic to `(ChainComplex.single₀ C).obj X`. -/
def N.constIso (X : C) :
    N.obj ((SimplicialObject.const C).obj X) ≅ (ChainComplex.single₀ C).obj X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun
      | 0 =>
        { hom := (inclusionN.app ((SimplicialObject.const C).obj X)).f 0
          inv := (PInftyToN.app ((SimplicialObject.const C).obj X)).f 0
          hom_inv_id := by
            rw [← HomologicalComplex.comp_f, inclusionN_app_comp_PInftyToN_app,
              HomologicalComplex.id_f]
          inv_hom_id := by
            rw [← HomologicalComplex.comp_f, PInftyToN_app_comp_inclusionN_app, PInfty_f_0]
            rfl } ≪≫ (HomologicalComplex.singleObjXSelf (.down ℕ) 0 X).symm
      | m + 1 =>
        (isZero_N_const_obj_X_succ X m).iso
          (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 X (m + 1) (by omega)))
    (fun i j hij ↦ by
      dsimp [ComplexShape.down] at hij
      obtain rfl := hij.symm
      exact (isZero_N_const_obj_X_succ X j).eq_of_src _ _)

@[simp]
lemma N.constIso_hom_f_zero (X : C) :
    (N.constIso X).hom.f 0 = (inclusionN.app ((SimplicialObject.const C).obj X)).f 0 := by
  simp [N.constIso]

@[simp]
lemma N.constIso_inv_f_zero (X : C) :
    (N.constIso X).inv.f 0 = (PInftyToN.app ((SimplicialObject.const C).obj X)).f 0 := by
  simp [N.constIso]

/-- Under the inverse Dold–Kan functor `Γ`, the chain complex `(ChainComplex.single₀ C).obj X`
concentrated in degree `0` corresponds to the constant simplicial object
`(SimplicialObject.const C).obj X`. -/
def Γ.single₀Iso (X : C) :
    Γ.obj ((ChainComplex.single₀ C).obj X) ≅ (SimplicialObject.const C).obj X :=
  Γ.mapIso (N.constIso X).symm ≪≫ (ε (C := C)).symm.app ((SimplicialObject.const C).obj X)

end ConstSingle₀

end CategoryTheory.Idempotents.DoldKan

namespace CategoryTheory.Abelian.DoldKan

instance Γ.projective_obj {A : Type u} [Category.{v} A] [Abelian A]
    (K : ChainComplex A ℕ) [∀ n, Projective (K.X n)] (Δ : SimplexCategoryᵒᵖ) :
    Projective ((Γ.obj K).obj Δ) :=
  inferInstanceAs (Projective ((Idempotents.DoldKan.Γ.obj K).obj Δ))

end CategoryTheory.Abelian.DoldKan

namespace AlgebraicTopology

instance normalizedMooreComplex.projective_X {A : Type u} [Category.{v} A] [Abelian A]
    (X : SimplicialObject A) [∀ n, Projective (X _⦋n⦌)] (n : ℕ) :
    Projective (((normalizedMooreComplex A).obj X).X n) :=
  Projective.of_iso
    (HomologicalComplex.Hom.isoApp ((Abelian.DoldKan.comparisonN (A := A)).symm.app X) n)
    inferInstance

end AlgebraicTopology

namespace CategoryTheory.SimplicialObject

/-- In an idempotent-complete preadditive category with finite coproducts, a simplicial object `X`
is degreewise projective if and only if its normalized chain complex `Idempotents.DoldKan.N.obj X`
is degreewise projective. -/
theorem projective_iff_N_projective {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteCoproducts C] [IsIdempotentComplete C] (X : SimplicialObject C) :
    (∀ n : ℕ, Projective (X _⦋n⦌)) ↔ ∀ n : ℕ, Projective ((Idempotents.DoldKan.N.obj X).X n) := by
  constructor
  · intro _ n
    infer_instance
  · intro _ n
    have hΓ : Projective
        ((Idempotents.DoldKan.Γ.obj (Idempotents.DoldKan.N.obj X)).obj (op ⦋n⦌)) :=
      inferInstance
    exact Projective.of_iso
      (((Idempotents.DoldKan.ε (C := C)).symm.app X).app (op ⦋n⦌)) hΓ

/-- In an abelian category, a simplicial object `X` is degreewise projective if and only if its
normalized Moore complex `(normalizedMooreComplex A).obj X` is degreewise projective. -/
theorem projective_iff_normalizedMooreComplex_projective {A : Type u} [Category.{v} A] [Abelian A]
    (X : SimplicialObject A) :
    (∀ n : ℕ, Projective (X _⦋n⦌)) ↔
      ∀ n : ℕ, Projective (((normalizedMooreComplex A).obj X).X n) := by
  rw [projective_iff_N_projective]
  refine ⟨fun h n ↦ ?_, fun h n ↦ ?_⟩
  · exact Projective.of_iso
      (HomologicalComplex.Hom.isoApp ((Abelian.DoldKan.comparisonN (A := A)).symm.app X) n) (h n)
  · exact Projective.of_iso
      (HomologicalComplex.Hom.isoApp ((Abelian.DoldKan.comparisonN (A := A)).app X) n) (h n)

section WhiskeringProjective

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- For degreewise projective simplicial objects `X` and `Y` in an abelian category, a morphism
`f : X ⟶ Y` induces a quasi-isomorphism on alternating face map complexes if and only if `f` is a
simplicial homotopy equivalence. -/
theorem quasiIso_alternatingFaceMapComplex_map_iff_of_projective
    {X Y : SimplicialObject C} [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)]
    (f : X ⟶ Y) :
    QuasiIso ((alternatingFaceMapComplex C).map f) ↔ ∃ e : HomotopyEquiv X Y, e.hom = f := by
  have : ∀ n, Projective (((alternatingFaceMapComplex C).obj X).X n) := fun n ↦
    inferInstanceAs (Projective (X _⦋n⦌))
  have : ∀ n, Projective (((alternatingFaceMapComplex C).obj Y).X n) := fun n ↦
    inferInstanceAs (Projective (Y _⦋n⦌))
  rw [ChainComplex.quasiIso_iff_of_projective,
    homotopyEquivalences_alternatingFaceMapComplex_map_iff]

/-- Upgrade a morphism `f : X ⟶ Y` between degreewise projective simplicial objects in an abelian
category whose alternating face map complex morphism is a quasi-isomorphism to a simplicial homotopy
equivalence `HomotopyEquiv X Y` with forward morphism `f`. -/
def homotopyEquivOfQuasiIso {X Y : SimplicialObject C}
    [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)] (f : X ⟶ Y)
    [hf : QuasiIso ((alternatingFaceMapComplex C).map f)] :
    HomotopyEquiv X Y :=
  ((quasiIso_alternatingFaceMapComplex_map_iff_of_projective f).mp hf).choose

@[simp]
lemma homotopyEquivOfQuasiIso_hom {X Y : SimplicialObject C}
    [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)] (f : X ⟶ Y)
    [hf : QuasiIso ((alternatingFaceMapComplex C).map f)] :
    (homotopyEquivOfQuasiIso f).hom = f :=
  ((quasiIso_alternatingFaceMapComplex_map_iff_of_projective f).mp hf).choose_spec

/-- Any functor `F : C ⥤ D` (not necessarily additive) sends a weak equivalence `f : X ⟶ Y` between
degreewise projective simplicial objects in `C` to a simplicial homotopy equivalence in
`SimplicialObject D`. -/
theorem exists_homotopyEquiv_whiskering_map_of_projective
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {X Y : SimplicialObject C} [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)]
    (f : X ⟶ Y) [QuasiIso ((alternatingFaceMapComplex C).map f)] :
    ∃ e : HomotopyEquiv (((whiskering C D).obj F).obj X) (((whiskering C D).obj F).obj Y),
      e.hom = ((whiskering C D).obj F).map f :=
  ⟨(homotopyEquivOfQuasiIso f).whiskerRight F, by simp⟩

/-- Any functor `F : C ⥤ D` into a preadditive category `D` (not necessarily additive) sends a weak
equivalence `f : X ⟶ Y` between degreewise projective simplicial objects in `C` to a chain homotopy
equivalence on alternating face map complexes. -/
theorem homotopyEquivalences_alternatingFaceMapComplex_whiskering_map_of_projective
    {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D)
    {X Y : SimplicialObject C} [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)]
    (f : X ⟶ Y) [QuasiIso ((alternatingFaceMapComplex C).map f)] :
    HomologicalComplex.homotopyEquivalences D (.down ℕ)
      ((alternatingFaceMapComplex D).map (((whiskering C D).obj F).map f)) := by
  obtain ⟨e, he⟩ := exists_homotopyEquiv_whiskering_map_of_projective F f
  rw [← he]
  exact e.homotopyEquivalences_alternatingFaceMapComplex_map

/-- **Non-additive functors preserve weak equivalences of projective simplicial objects**
(Dold–Puppe, §§4.4–4.7): for *any* functor `F : C ⥤ D` (without any additivity assumption on `F`)
from an abelian category `C` to a preadditive category `D` with homology, if `X` and `Y` are
degreewise projective simplicial objects in `C` and `f : X ⟶ Y` induces a quasi-isomorphism on
alternating face map complexes, then `((whiskering C D).obj F).map f` also induces a
quasi-isomorphism on alternating face map complexes. -/
theorem quasiIso_whiskering_of_projective
    {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryWithHomology D] (F : C ⥤ D)
    {X Y : SimplicialObject C} [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)]
    (f : X ⟶ Y) [QuasiIso ((alternatingFaceMapComplex C).map f)] :
    QuasiIso ((alternatingFaceMapComplex D).map (((whiskering C D).obj F).map f)) :=
  homotopyEquivalences_le_quasiIso D (.down ℕ) _
    (homotopyEquivalences_alternatingFaceMapComplex_whiskering_map_of_projective F f)

/-- Normalized-chains variant of `quasiIso_whiskering_of_projective`: when `D` is also idempotent
complete with finite coproducts, `Idempotents.DoldKan.N.map (((whiskering C D).obj F).map f)` is a
quasi-isomorphism. -/
theorem quasiIso_N_whiskering_of_projective
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteCoproducts D]
    [IsIdempotentComplete D] [CategoryWithHomology D] (F : C ⥤ D)
    {X Y : SimplicialObject C} [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)]
    (f : X ⟶ Y) [QuasiIso ((alternatingFaceMapComplex C).map f)] :
    QuasiIso (Idempotents.DoldKan.N.map (((whiskering C D).obj F).map f)) := by
  obtain ⟨e, he⟩ := exists_homotopyEquiv_whiskering_map_of_projective F f
  let hEquiv : _root_.HomotopyEquiv
      (Idempotents.DoldKan.N.obj (((whiskering C D).obj F).obj X))
      (Idempotents.DoldKan.N.obj (((whiskering C D).obj F).obj Y)) :=
    { hom := Idempotents.DoldKan.N.map e.hom
      inv := Idempotents.DoldKan.N.map e.inv
      homotopyHomInvId :=
        (_root_.Homotopy.ofEq (Idempotents.DoldKan.N.map_comp e.hom e.inv).symm).trans
          (e.homotopyHomInvId.toNHomotopy.trans
            (_root_.Homotopy.ofEq (Idempotents.DoldKan.N.map_id _)))
      homotopyInvHomId :=
        (_root_.Homotopy.ofEq (Idempotents.DoldKan.N.map_comp e.inv e.hom).symm).trans
          (e.homotopyInvHomId.toNHomotopy.trans
            (_root_.Homotopy.ofEq (Idempotents.DoldKan.N.map_id _))) }
  rw [← he]
  exact homotopyEquivalences_le_quasiIso D (.down ℕ) _ hEquiv.homotopyEquivalences_hom

/-- **Full-subcategory version of `quasiIso_whiskering_of_projective`**: if `ι : C₀ ⥤ C` is a fully
faithful functor into an abelian category `C` (for example `P.ι : P.FullSubcategory ⥤ C` for
`isProjective C` or finitely generated projective modules), `F : C₀ ⥤ D` is *any* functor defined
only on `C₀`, `X` and `Y` are simplicial objects in `C₀` whose images under `ι` are degreewise
projective in `C`, and `f : X ⟶ Y` becomes a weak equivalence after whiskering by `ι`, then
`((whiskering C₀ D).obj F).map f` induces a quasi-isomorphism on alternating face map complexes. -/
theorem quasiIso_whiskering_of_fullyFaithful_projective
    {C₀ : Type*} [Category* C₀] (ι : C₀ ⥤ C) [ι.Full] [ι.Faithful]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryWithHomology D]
    (F : C₀ ⥤ D) {X Y : SimplicialObject C₀}
    [hX : ∀ n, Projective (ι.obj (X _⦋n⦌))] [hY : ∀ n, Projective (ι.obj (Y _⦋n⦌))]
    (f : X ⟶ Y) [QuasiIso ((alternatingFaceMapComplex C).map (((whiskering C₀ C).obj ι).map f))] :
    QuasiIso ((alternatingFaceMapComplex D).map (((whiskering C₀ D).obj F).map f)) := by
  have : ∀ n, Projective ((((whiskering C₀ C).obj ι).obj X) _⦋n⦌) := hX
  have : ∀ n, Projective ((((whiskering C₀ C).obj ι).obj Y) _⦋n⦌) := hY
  let e : HomotopyEquiv X Y :=
    (homotopyEquivOfQuasiIso (((whiskering C₀ C).obj ι).map f)).ofFullyFaithful ι
  have he : e.hom = f := by
    apply ((whiskering C₀ C).obj ι).map_injective
    dsimp only [e]
    rw [HomotopyEquiv.map_ofFullyFaithful_hom, homotopyEquivOfQuasiIso_hom]
  rw [← he, ← e.whiskerRight_hom F]
  exact (e.whiskerRight F).quasiIso_alternatingFaceMapComplex_map

/-- Specialization of `quasiIso_whiskering_of_fullyFaithful_projective` to functors
`F : (isProjective C).FullSubcategory ⥤ D` defined only on the full subcategory of projective
objects of `C`. -/
theorem quasiIso_whiskering_isProjective
    {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryWithHomology D]
    (F : (isProjective C).FullSubcategory ⥤ D)
    {X Y : SimplicialObject (isProjective C).FullSubcategory} (f : X ⟶ Y)
    [QuasiIso ((alternatingFaceMapComplex C).map
      (((whiskering (isProjective C).FullSubcategory C).obj (isProjective C).ι).map f))] :
    QuasiIso ((alternatingFaceMapComplex D).map
      (((whiskering (isProjective C).FullSubcategory D).obj F).map f)) := by
  have : ∀ n, Projective ((isProjective C).ι.obj (X _⦋n⦌)) := fun n ↦ (X _⦋n⦌).property
  have : ∀ n, Projective ((isProjective C).ι.obj (Y _⦋n⦌)) := fun n ↦ (Y _⦋n⦌).property
  exact quasiIso_whiskering_of_fullyFaithful_projective (isProjective C).ι F f

end WhiskeringProjective

end CategoryTheory.SimplicialObject

namespace CategoryTheory

section DoldPuppe

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- **The Dold–Puppe chain-complex functor** associated to an arbitrary (not necessarily additive)
functor `F : C ⥤ D`: sends `K : ChainComplex C ℕ` to the alternating face map complex of `F` applied
levelwise to `Idempotents.DoldKan.Γ.obj K`. Evaluating `F.doldPuppeFunctor` on a projective
resolution computes the left derived functor of `F` in the sense of Dold and Puppe. -/
abbrev Functor.doldPuppeFunctor (F : C ⥤ D) : ChainComplex C ℕ ⥤ ChainComplex D ℕ :=
  Idempotents.DoldKan.Γ ⋙ (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D

lemma Functor.doldPuppeFunctor_obj (F : C ⥤ D) (K : ChainComplex C ℕ) :
    F.doldPuppeFunctor.obj K =
      (alternatingFaceMapComplex D).obj
        (((SimplicialObject.whiskering C D).obj F).obj (Idempotents.DoldKan.Γ.obj K)) :=
  (rfl)

lemma Functor.doldPuppeFunctor_map (F : C ⥤ D) {K L : ChainComplex C ℕ} (f : K ⟶ L) :
    F.doldPuppeFunctor.map f =
      (alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).obj F).map (Idempotents.DoldKan.Γ.map f)) :=
  (rfl)

/-- Naturality of `Functor.doldPuppeFunctor` with respect to a natural transformation
`α : F ⟶ G`. -/
def NatTrans.doldPuppeFunctor {F G : C ⥤ D} (α : F ⟶ G) :
    F.doldPuppeFunctor ⟶ G.doldPuppeFunctor :=
  Functor.whiskerLeft Idempotents.DoldKan.Γ
    (Functor.whiskerRight ((SimplicialObject.whiskering C D).map α) (alternatingFaceMapComplex D))

@[simp]
lemma NatTrans.doldPuppeFunctor_app_f {F G : C ⥤ D} (α : F ⟶ G) (K : ChainComplex C ℕ) (n : ℕ) :
    ((NatTrans.doldPuppeFunctor α).app K).f n = α.app ((Idempotents.DoldKan.Γ.obj K) _⦋n⦌) :=
  (rfl)

@[simp]
lemma NatTrans.doldPuppeFunctor_id (F : C ⥤ D) :
    NatTrans.doldPuppeFunctor (𝟙 F) = 𝟙 F.doldPuppeFunctor := by
  ext K n
  simp

@[simp]
lemma NatTrans.doldPuppeFunctor_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.doldPuppeFunctor (α ≫ β) =
      NatTrans.doldPuppeFunctor α ≫ NatTrans.doldPuppeFunctor β := by
  ext K n
  simp

/-- For *any* functor `F : C ⥤ D` (not necessarily additive), `F.doldPuppeFunctor` preserves chain
homotopies. -/
def Functor.doldPuppeMapHomotopy (F : C ⥤ D) {K L : ChainComplex C ℕ} {φ ψ : K ⟶ L}
    (H : Homotopy φ ψ) :
    Homotopy (F.doldPuppeFunctor.map φ) (F.doldPuppeFunctor.map ψ) :=
  ((Idempotents.DoldKan.Γ.mapHomotopy H).whiskerRight F).toChainHomotopy

/-- For *any* functor `F : C ⥤ D` (not necessarily additive), `F.doldPuppeFunctor` preserves chain
homotopy equivalences. -/
def Functor.doldPuppeMapHomotopyEquiv (F : C ⥤ D) {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) :
    HomotopyEquiv (F.doldPuppeFunctor.obj K) (F.doldPuppeFunctor.obj L) :=
  ((Idempotents.DoldKan.Γ.mapHomotopyEquiv e).whiskerRight F).toChainHomotopyEquiv

@[simp]
lemma Functor.doldPuppeMapHomotopyEquiv_hom (F : C ⥤ D) {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) :
    (F.doldPuppeMapHomotopyEquiv e).hom = F.doldPuppeFunctor.map e.hom := by
  dsimp [Functor.doldPuppeMapHomotopyEquiv, Functor.doldPuppeFunctor]
  simp

@[simp]
lemma Functor.doldPuppeMapHomotopyEquiv_inv (F : C ⥤ D) {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) :
    (F.doldPuppeMapHomotopyEquiv e).inv = F.doldPuppeFunctor.map e.inv := by
  dsimp [Functor.doldPuppeMapHomotopyEquiv, Functor.doldPuppeFunctor]
  simp

/-- **Agreement with the classical additive derived functor** (Dold–Puppe, Satz 4.7): when
`F : C ⥤ D` is additive, `F.doldPuppeFunctor.obj K` is canonically chain homotopy equivalent to
`(F.mapHomologicalComplex (.down ℕ)).obj K` for every chain complex `K`. -/
def Functor.doldPuppeFunctorAdditiveHomotopyEquiv (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) :
    HomotopyEquiv (F.doldPuppeFunctor.obj K) ((F.mapHomologicalComplex (.down ℕ)).obj K) :=
  (HomotopyEquiv.ofIso
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.app
        (Idempotents.DoldKan.Γ.obj K))).trans
    ((F.mapHomotopyEquiv
        (Idempotents.DoldKan.homotopyEquivNAlternatingFaceMapComplex
          (Idempotents.DoldKan.Γ.obj K)).symm).trans
      (HomotopyEquiv.ofIso
        ((F.mapHomologicalComplex (.down ℕ)).mapIso ((Idempotents.DoldKan.η (C := C)).app K))))

/-- When `F : C ⥤ D` is additive and `D` has homology, the comparison chain map from
`F.doldPuppeFunctor.obj K` to `(F.mapHomologicalComplex (.down ℕ)).obj K` is a
quasi-isomorphism. -/
instance Functor.quasiIso_doldPuppeFunctorAdditiveHomotopyEquiv_hom [CategoryWithHomology D]
    (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    QuasiIso (F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom :=
  homotopyEquivalences_le_quasiIso D (.down ℕ) _
    (F.doldPuppeFunctorAdditiveHomotopyEquiv K).homotopyEquivalences_hom

/-- **Degree-zero law**: for any object `X : C` and any functor `F : C ⥤ D` into a preadditive
category with a zero object, `F.doldPuppeFunctor.obj ((ChainComplex.single₀ C).obj X)` is
canonically chain homotopy equivalent to `(ChainComplex.single₀ D).obj (F.obj X)`. In particular,
when `X` is projective, `(ChainComplex.single₀ C).obj X` is a projective resolution of `X`, so the
derived functor of `F` recovers `F.obj X` concentrated in degree `0`. -/
def Functor.doldPuppeFunctorSingle₀HomotopyEquiv [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) (X : C) :
    HomotopyEquiv (F.doldPuppeFunctor.obj ((ChainComplex.single₀ C).obj X))
      ((ChainComplex.single₀ D).obj (F.obj X)) := by
  let isoSimp : ((SimplicialObject.whiskering C D).obj F).obj
        (Idempotents.DoldKan.Γ.obj ((ChainComplex.single₀ C).obj X)) ≅
      (SimplicialObject.const D).obj (F.obj X) :=
    ((SimplicialObject.whiskering C D).obj F).mapIso (Idempotents.DoldKan.Γ.single₀Iso X) ≪≫
      NatIso.ofComponents (fun _ ↦ Iso.refl (F.obj X)) (fun _ ↦ by dsimp; simp)
  exact (HomotopyEquiv.ofIso ((alternatingFaceMapComplex D).mapIso isoSimp)).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj X)).homotopyEquiv

instance Functor.quasiIso_doldPuppeFunctorSingle₀HomotopyEquiv_hom
    [HasZeroObject C] [HasZeroObject D] [CategoryWithHomology D]
    (F : C ⥤ D) (X : C) :
    QuasiIso (F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom :=
  homotopyEquivalences_le_quasiIso D (.down ℕ) _
    (F.doldPuppeFunctorSingle₀HomotopyEquiv X).homotopyEquivalences_hom

/-- **Constant non-additive functor law**: for any object `B : D` and any chain complex
`K : ChainComplex C ℕ` (including `K = 0`), `((Functor.const C).obj B).doldPuppeFunctor.obj K` is
canonically chain homotopy equivalent to `(ChainComplex.single₀ D).obj B`. -/
def Functor.doldPuppeFunctorConstHomotopyEquiv [HasZeroObject D] (B : D) (K : ChainComplex C ℕ) :
    HomotopyEquiv (((Functor.const C).obj B).doldPuppeFunctor.obj K)
      ((ChainComplex.single₀ D).obj B) := by
  let isoSimp : ((SimplicialObject.whiskering C D).obj ((Functor.const C).obj B)).obj
        (Idempotents.DoldKan.Γ.obj K) ≅
      (SimplicialObject.const D).obj B :=
    NatIso.ofComponents (fun _ ↦ Iso.refl B) (fun _ ↦ by dsimp)
  exact (HomotopyEquiv.ofIso ((alternatingFaceMapComplex D).mapIso isoSimp)).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv

instance Functor.quasiIso_doldPuppeFunctorConstHomotopyEquiv_hom
    [HasZeroObject D] [CategoryWithHomology D] (B : D) (K : ChainComplex C ℕ) :
    QuasiIso (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom :=
  homotopyEquivalences_le_quasiIso D (.down ℕ) _
    (Functor.doldPuppeFunctorConstHomotopyEquiv B K).homotopyEquivalences_hom

end DoldPuppe

section AbelianDoldPuppe

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryWithHomology D]

/-- **Resolution independence of the Dold–Puppe construction**: in an abelian category `C`, if
`P` and `Q` are degreewise projective chain complexes and `f : P ⟶ Q` is a quasi-isomorphism, then
for *any* functor `F : C ⥤ D` (not necessarily additive), `F.doldPuppeFunctor.map f` is a
quasi-isomorphism. -/
theorem Functor.quasiIso_doldPuppeFunctor_map_of_projective (F : C ⥤ D)
    {P Q : ChainComplex C ℕ} [∀ n, Projective (P.X n)] [∀ n, Projective (Q.X n)]
    (f : P ⟶ Q) [hf : QuasiIso f] :
    QuasiIso (F.doldPuppeFunctor.map f) := by
  rw [ChainComplex.quasiIso_iff_of_projective] at hf
  obtain ⟨e, rfl⟩ := hf
  rw [← F.doldPuppeMapHomotopyEquiv_hom e]
  exact homotopyEquivalences_le_quasiIso D (.down ℕ) _
    (F.doldPuppeMapHomotopyEquiv e).homotopyEquivalences_hom

end AbelianDoldPuppe

end CategoryTheory
