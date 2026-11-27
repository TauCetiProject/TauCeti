/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.FiniteFree
public import TauCeti.CategoryTheory.Preadditive.ModCat.Flat.Basic

/-!
# Finite-free factorization for flat modules

A morphism from a finite sum of representable modules into a flat module factors
through another finite sum of representables while killing any specified finite
system of relations. Passing to cokernels gives the finite-free factorization
criterion for maps from finitely presented modules, in the form of Lazard's
*Autour de la platitude*, Chapter I, Lemma 1.1 and Theorem 1.2 (i)–(ii).
-/

public section

universe v u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {F : ModCat.{v} C} {l m n : ℕ} {X : Fin l → C} {Y : Fin m → C} {Z : Fin n → C}

local instance : (yoneda C).Additive where
  map_add {_ _ f g} := ObjectProperty.hom_ext _ (preadditiveYoneda.map_add (f := f) (g := g))

private noncomputable def yonedaMatrix (β : ∀ i j, X i ⟶ Y j) :
    (⨁ (yoneda C).obj ∘ X) ⟶ (⨁ (yoneda C).obj ∘ Y) :=
  biproduct.matrix fun i j ↦ (yoneda C).map (β i j)

private theorem yonedaMatrix_comp_eq_zero (β : ∀ i j, X i ⟶ Y j) (α : ∀ j k, Y j ⟶ Z k)
    (h : ∀ i k, ∑ j, β i j ≫ α j k = 0) : yonedaMatrix β ≫ yonedaMatrix α = 0 := by
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro k
  simp only [yonedaMatrix, Category.assoc, biproduct.matrix_π, biproduct.ι_matrix_assoc,
    biproduct.lift_desc, zero_comp, comp_zero, ← Functor.map_comp]
  rw [← (yoneda C).map_sum, h, Functor.map_zero]

private theorem exists_yonedaMatrix
    (d : (⨁ (yoneda C).obj ∘ X) ⟶ (⨁ (yoneda C).obj ∘ Y)) :
    ∃ β : ∀ i j, X i ⟶ Y j, yonedaMatrix β = d := by
  refine ⟨fun i j ↦ (yoneda C).preimage (biproduct.components d i j), ?_⟩
  simpa only [yonedaMatrix, Functor.map_preimage] using biproduct.components_matrix d

private theorem exists_biproduct_desc_app_id (y : ∀ j, F.obj.obj (op (Y j))) :
    ∃ p : (⨁ (yoneda C).obj ∘ Y) ⟶ F, ∀ j,
      (biproduct.ι ((yoneda C).obj ∘ Y) j ≫ p).hom.app (op (Y j)) (𝟙 (Y j)) = y j := by
  have := (additiveFunctor_iff F.obj).1 F.property
  let a (j : Fin m) : (yoneda C).obj (Y j) ⟶ F :=
    ObjectProperty.homMk
      { app T := AddCommGrpCat.ofHom
          ((AddMonoidHom.eval (y j)).comp (AddCommGrpCat.homAddEquiv.toAddMonoidHom.comp
            (F.obj.mapAddHom.comp (opHom T.unop (Y j)))))
        naturality T U g := by
          ext (f : T.unop ⟶ Y j)
          exact ConcreteCategory.congr_hom (F.obj.map_comp f.op g) (y j) }
  refine ⟨biproduct.desc a, fun j ↦ ?_⟩
  rw [biproduct.ι_desc]
  -- Evaluation at the identity reduces to the functor's identity law on the given element.
  change F.obj.map (𝟙 (Y j)).op (y j) = y j
  simp

private theorem biproduct_lift_comp_app_id {A : C} (β : ∀ j, A ⟶ Y j)
    (p : (⨁ (yoneda C).obj ∘ Y) ⟶ F) :
    (biproduct.lift (f := (yoneda C).obj ∘ Y) (fun j ↦ (yoneda C).map (β j)) ≫ p).hom.app
        (op A) (𝟙 A) =
      ∑ j, F.obj.map (β j).op
        ((biproduct.ι ((yoneda C).obj ∘ Y) j ≫ p).hom.app (op (Y j)) (𝟙 (Y j))) := by
  let ev : (((yoneda C).obj A) ⟶ F) →+ F.obj.obj (op A) :=
    AddMonoidHom.mk' (fun f ↦ f.hom.app (op A) (𝟙 A)) (fun _ _ ↦ rfl)
  -- Bundle evaluation so it can be applied to the finite sum of morphisms.
  change ev (biproduct.lift (f := (yoneda C).obj ∘ Y)
    (fun j ↦ (yoneda C).map (β j)) ≫ p) = _
  rw [biproduct.lift_eq, Preadditive.sum_comp, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  let g := (biproduct.ι ((yoneda C).obj ∘ Y) j ≫ p).hom
  have hj : g.app (op A) (β j ≫ 𝟙 (Y j)) =
      F.obj.map (β j).op (g.app (op (Y j)) (𝟙 (Y j))) :=
    ConcreteCategory.congr_hom (g.naturality (β j).op) (𝟙 (Y j))
  rw [Category.assoc]
  -- The representable map applied to the identity at A is composition with β j.
  change g.app (op A) (𝟙 A ≫ β j) = _
  simpa only [Category.id_comp, Category.comp_id] using hj

private theorem yonedaMatrix_comp_app_id (β : ∀ i j, X i ⟶ Y j)
    (p : (⨁ (yoneda C).obj ∘ Y) ⟶ F) (i : Fin l) :
    (biproduct.ι ((yoneda C).obj ∘ X) i ≫ yonedaMatrix β ≫ p).hom.app (op (X i)) (𝟙 (X i)) =
      ∑ j, F.obj.map (β i j).op
        ((biproduct.ι ((yoneda C).obj ∘ Y) j ≫ p).hom.app (op (Y j)) (𝟙 (Y j))) := by
  rw [yonedaMatrix, biproduct.ι_matrix_assoc, biproduct_lift_comp_app_id]

/-- For flat `F`, a morphism `p : V ⟶ F` killing a morphism `d : U ⟶ V` between finite
sums of representables factors through a finite free module by a map that still kills `d`. -/
theorem Flat.exists_factorization_of_comp_eq_zero [F.Flat] {U V : ModCat.{v} C}
    (hU : isFiniteFree C U) (hV : isFiniteFree C V) (d : U ⟶ V) (p : V ⟶ F) (h : d ≫ p = 0) :
    ∃ (W : ModCat.{v} C) (_ : isFiniteFree C W) (a : V ⟶ W) (b : W ⟶ F), a ≫ b = p ∧ d ≫ a = 0 := by
  obtain ⟨l, X, ⟨eU⟩⟩ := isFiniteFree_iff_exists_iso_biproduct.mp hU
  obtain ⟨m, Y, ⟨eV⟩⟩ := isFiniteFree_iff_exists_iso_biproduct.mp hV
  obtain ⟨β, hβ⟩ := exists_yonedaMatrix (eU.inv ≫ d ≫ eV.hom)
  let q := eV.inv ≫ p
  have hq : yonedaMatrix β ≫ q = 0 := by simp [hβ, q, h]
  let y (j : Fin m) :=
    (biproduct.ι ((yoneda C).obj ∘ Y) j ≫ q).hom.app (op (Y j)) (𝟙 (Y j))
  have hy (i : Fin l) : ∑ j, F.obj.map (β i j).op (y j) = 0 := by
    rw [← yonedaMatrix_comp_app_id β q i, hq, comp_zero]
    rfl
  obtain ⟨n, Z, z, α, hy', hα⟩ := Flat.exists_factorization_of_sum_eq_zero β y hy
  let a := yonedaMatrix (fun j i ↦ α i j)
  obtain ⟨b, hb⟩ := exists_biproduct_desc_app_id z
  have hab : a ≫ b = q := by
    apply biproduct.hom_ext'
    intro j
    apply ObjectProperty.hom_ext
    apply preadditiveYoneda_obj_hom_ext
    rw [yonedaMatrix_comp_app_id]
    simpa only [hb] using (hy' j).symm
  have hda : yonedaMatrix β ≫ a = 0 := yonedaMatrix_comp_eq_zero β _ hα
  refine ⟨_, isFiniteFree_biproduct_yoneda Z,
    eV.hom ≫ a, b, by simp [hab, q], ?_⟩
  simpa [hβ] using congrArg (fun f ↦ eU.hom ≫ f) hda

/-- Every morphism from a finitely presented module to a flat module factors through a finite
free module. -/
theorem Flat.exists_factorization_of_isFinitelyPresentedFunctor [F.Flat] {P : ModCat.{v} C}
    (hP : IsFinitelyPresentedFunctor P.obj) (f : P ⟶ F) :
    ∃ (Q : ModCat.{v} C) (_ : isFiniteFree C Q) (a : P ⟶ Q) (b : Q ⟶ F), a ≫ b = f := by
  obtain ⟨U, V, hU, hV, d, p, hp, ⟨hc⟩⟩ :=
    isFinitelyPresentedFunctor_iff_exists_finiteFree_presentation.mp hP
  have h : d ≫ (p ≫ f) = 0 := by simp [← Category.assoc, hp]
  obtain ⟨Q, hQ, a, b, hab, ha⟩ := Flat.exists_factorization_of_comp_eq_zero hU hV d (p ≫ f) h
  obtain ⟨a', ha'⟩ := CokernelCofork.IsColimit.desc' hc a ha
  have ha'' : p ≫ a' = a := ha'
  refine ⟨Q, hQ, a', b, Cofork.IsColimit.hom_ext hc ?_⟩
  simpa only [CokernelCofork.π_ofπ, reassoc_of% ha''] using hab

/-- A module is flat if and only if every morphism into it from a finitely presented module
factors through a finite free module. -/
theorem flat_iff_forall_exists_factorization :
    F.Flat ↔ ∀ ⦃P : ModCat.{v} C⦄, IsFinitelyPresentedFunctor P.obj → ∀ f : P ⟶ F,
      ∃ (Q : ModCat.{v} C) (_ : isFiniteFree C Q) (a : P ⟶ Q) (b : Q ⟶ F), a ≫ b = f := by
  refine ⟨fun hF _ hP f ↦ Flat.exists_factorization_of_isFinitelyPresentedFunctor hP f, ?_⟩
  intro hF
  constructor
  intro A m Y β y h
  let d : (yoneda C).obj A ⟶ (⨁ (yoneda C).obj ∘ Y) :=
    biproduct.lift fun j ↦ (yoneda C).map (β j)
  obtain ⟨p, hpy⟩ := exists_biproduct_desc_app_id y
  have hp : d ≫ p = 0 := by
    apply ObjectProperty.hom_ext
    apply preadditiveYoneda_obj_hom_ext
    refine (biproduct_lift_comp_app_id β p).trans (Eq.trans ?_ (Eq.refl 0))
    simpa only [hpy] using h
  have hU := isFiniteFree_yoneda_obj A
  have hV := isFiniteFree_biproduct_yoneda Y
  have hP := isFinitelyPresentedFunctor_iff_exists_finiteFree_presentation.mpr
    ⟨_, _, hU, hV, d, cokernel.π d, cokernel.condition d, ⟨cokernelIsCokernel d⟩⟩
  obtain ⟨Q, hQ, a, b, hab⟩ := hF hP (cokernel.desc d p hp)
  obtain ⟨n, Z, ⟨e⟩⟩ := isFiniteFree_iff_exists_iso_biproduct.mp hQ
  obtain ⟨α, hα⟩ := exists_yonedaMatrix (cokernel.π d ≫ a ≫ e.hom)
  let q := e.inv ≫ b
  have hq : yonedaMatrix α ≫ q = p := by
    simp [hα, q, hab]
  refine isTrivialRelation_def.mpr
    ⟨n, Z, fun i ↦ (biproduct.ι ((yoneda C).obj ∘ Z) i ≫ q).hom.app (op (Z i)) (𝟙 (Z i)),
      fun i j ↦ α j i, ?_, ?_⟩
  · intro j
    rw [← yonedaMatrix_comp_app_id α q j, hq, hpy]
  · intro i
    have hz : d ≫ yonedaMatrix α ≫ biproduct.π ((yoneda C).obj ∘ Z) i = 0 := by
      simp [hα, cokernel.condition_assoc]
    apply (yoneda C).map_injective
    rw [Functor.map_zero, Functor.map_sum]
    simpa only [d, yonedaMatrix, biproduct.matrix_π, biproduct.lift_desc, ← Functor.map_comp]
      using hz

/-- A finitely presented flat module is projective. -/
theorem Flat.projective_of_isFinitelyPresentedFunctor [F.Flat]
    (hF : IsFinitelyPresentedFunctor F.obj) : Projective F := by
  obtain ⟨P, hP, a, b, hab⟩ := Flat.exists_factorization_of_isFinitelyPresentedFunctor hF (𝟙 F)
  have := projective_of_isFiniteFree hP
  exact (Retract.mk a b hab).projective

end TauCeti.ModCat
