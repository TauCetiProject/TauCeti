/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.Refinements
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
public import TauCeti.CategoryTheory.Shift.CommShift

/-!
# Projections of the mapping cocone and short exact sequences

The mapping cocone `mappingCocone φ` of a morphism `φ : K ⟶ L` of cochain complexes is
`(mappingCone φ)⟦-1⟧`, and its projections `mappingCocone.fst φ : mappingCocone φ ⟶ K` and
`mappingCocone.snd φ` are built from those of the mapping cone. This file records the components
of these projections, the differential of the second projection, and their naturality
with respect to the shifted mapping cone map induced by a commutative square.

For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of cochain complexes in an abelian category,
the first map lifts to the mapping cocone of the second, and this lift `X₁ ⟶ mappingCocone S.g`
is a quasi-isomorphism. This is dual to Mathlib's `mappingCone.quasiIso_descShortComplex`, which
compares the mapping cone of the first map with the third term.

## Main results

* `CochainComplex.mappingCocone.fst_f`, `CochainComplex.mappingCocone.snd_v`: the components of
  the projections of the mapping cocone are those of the mapping cone.
* `CochainComplex.mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst` and
  `CochainComplex.mappingCocone.shiftFunctor_map_mappingCone_map_f_snd_v`: the projections of
  the mapping cocone are natural in commutative squares.
* `CochainComplex.mappingCocone.quasiIso_lift_of_shortExact`: for a short exact sequence `S` of
  cochain complexes, the lift `S.X₁ ⟶ mappingCocone S.g` of `S.f` is a quasi-isomorphism.

## Mapping cocones of natural transformations and shifts

For a natural transformation `τ : F ⟶ G` of functors `D ⥤ CochainComplex C ℤ`, the mapping
cocones `X ↦ mappingCocone (τ.app X)` form the functor `NatTrans.mappingCoconeFunctor τ`, the
composite of `NatTrans.mappingConeFunctor τ` with `⟦-1⟧`. When `F`, `G` and `τ` commute with the
shifts, so does this functor: the shift of mapping cones is composed with the commutation of
`⟦-1⟧` with the shifts twisted by the sign `(-1)^a` (`TauCeti.shiftFunctorCommShift`). The two
signs cancel on the first component, so that the first projections
`mappingCocone (τ.app X) ⟶ F.obj X` form a natural transformation compatible with the shifts
(`NatTrans.mappingCoconeFunctorFst`).

When `τ` is induced by a natural transformation `α : F ⟶ G` of additive functors, the mapping
cocone functor sends the mapping cone triangle of a morphism `φ` to the mapping cone triangle of its
image (`NatTrans.mappingCoconeFunctorMapTriangleIso`). This combines the corresponding statement
for the mapping cone functor with the comparison `TauCeti.shiftFunctorMapTriangleIso` for `⟦-1⟧`
and Mathlib's `mappingCone.shiftTriangleIso`.
-/

public section

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex.mappingCocone

open HomComplex

section

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- The components of the first projection of the mapping cocone are those of the first
projection of the mapping cone. -/
lemma fst_f {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p : ℤ) :
    (fst φ).f p = (mappingCone.fst φ).1.v (p + -1) p (by lia) := by
  simp [fst, Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]
  rfl

/-- The first projection of the mapping cocone is natural in commutative squares. -/
@[reassoc]
lemma shiftFunctor_map_mappingCone_map_comp_fst {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) :
    (mappingCone.map φ₁ φ₂ a b comm)⟦(-1 : ℤ)⟧' ≫ fst φ₂ = fst φ₁ ≫ a := by
  -- `mappingCocone φ` is `(mappingCone φ)⟦-1⟧` only up to unfolding, so the components are
  -- restated in matching types before rewriting.
  ext n : 1
  change ((mappingCone.map φ₁ φ₂ a b comm)⟦(-1 : ℤ)⟧').f n ≫ (fst φ₂).f n =
    (fst φ₁).f n ≫ a.f n
  rw [fst_f, fst_f, shiftFunctor_map_f']
  change (mappingCone.map φ₁ φ₂ a b comm).f (n + -1) ≫
      (mappingCone.fst φ₂).1.v (n + -1) n (by lia) =
    (mappingCone.fst φ₁).1.v (n + -1) n (by lia) ≫ a.f n
  apply mappingCone.ext_from φ₁ n (n + -1) (by lia) <;> simp [mappingCone.map]

/-- The components of the second projection of the mapping cocone are those of the second
projection of the mapping cone. -/
lemma snd_v {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p q : ℤ) (hpq : p + -1 = q) :
    (snd φ).v p q hpq = (mappingCone.snd φ).v (p + -1) q (by omega) := by
  subst hpq
  -- `snd φ` is a left shift of `mappingCone.snd φ`, but its source `mappingCocone φ` is
  -- `(mappingCone φ)⟦-1⟧` only up to unfolding, so it is restated before `leftShift_v` applies.
  change ((mappingCone.snd φ).leftShift (-1) (-1) (zero_add _)).v p (p + -1) rfl = _
  rw [Cochain.leftShift_v _ (-1) (-1) _ p (p + -1) rfl (p + -1) (add_zero _)]
  simp [Int.negOnePow_even 2 ⟨1, rfl⟩]

/-- The second projection of the native shifted cone has differential `-f a - d b`. -/
lemma d_snd_v {K L : CochainComplex C ℤ} (f : K ⟶ L) (p : ℤ) :
    (mappingCocone f).d p (p + 1) ≫ (snd f).v (p + 1) p (by omega) =
      -(fst f).f p ≫ f.f p -
        (snd f).v p (p + -1) rfl ≫ L.d (p + -1) p := by
  rw [snd_v, snd_v, fst_f]
  -- Restate the native cocone as the shifted cone so its differential formula applies.
  change ((mappingCone f)⟦(-1 : ℤ)⟧).d p (p + 1) ≫ _ = _
  simp only [shiftFunctor_obj_d', Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul, Preadditive.neg_comp]
  have hcomp (i : ℤ) (hi : i = p) :
      (mappingCone f).d (p + -1) i ≫ (mappingCone.snd f).v i p (by omega) =
        (mappingCone f).d (p + -1) p ≫ (mappingCone.snd f).v p p (add_zero p) := by
    subst hi
    rfl
  rw [hcomp _ (by omega), mappingCone.d_snd_v f (p + -1) p (by omega)]
  simp only [neg_add, sub_eq_add_neg]
  rfl

/-- The second projection of the mapping cocone is natural in commutative squares. -/
@[reassoc]
lemma shiftFunctor_map_mappingCone_map_f_snd_v {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)
    (p : ℤ) :
    ((mappingCone.map φ₁ φ₂ a b comm)⟦(-1 : ℤ)⟧').f p ≫ (snd φ₂).v p (p + -1) rfl =
      (snd φ₁).v p (p + -1) rfl ≫ b.f (p + -1) := by
  rw [snd_v, snd_v, shiftFunctor_map_f']
  -- As in `shiftFunctor_map_mappingCone_map_comp_fst`, the components are restated in matching
  -- types before applying the extensionality lemma for maps out of the mapping cone.
  change (mappingCone.map φ₁ φ₂ a b comm).f (p + -1) ≫
      (mappingCone.snd φ₂).v (p + -1) (p + -1) (add_zero _) =
    (mappingCone.snd φ₁).v (p + -1) (p + -1) (add_zero _) ≫ b.f (p + -1)
  apply mappingCone.ext_from φ₁ p (p + -1) (by lia) <;> simp [mappingCone.map]

/-- Two morphisms to a term of the mapping cocone are equal if their compositions with both
projections are. -/
lemma ext_to {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p q : ℤ) (hpq : p + -1 = q) {A : C}
    {f g : A ⟶ (mappingCocone φ).X p}
    (h₁ : f ≫ (fst φ).f p = g ≫ (fst φ).f p)
    (h₂ : f ≫ (snd φ).v p q hpq = g ≫ (snd φ).v p q hpq) : f = g := by
  rw [← Category.comp_id f, ← Category.comp_id g, ← id_X φ p q hpq, Preadditive.comp_add,
    Preadditive.comp_add, reassoc_of% h₁, reassoc_of% h₂]

end

section Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- The mapping cocone of an identity morphism is acyclic, since it is contractible. -/
lemma acyclic_mappingCocone_id (L : CochainComplex C ℤ) : (mappingCocone (𝟙 L)).Acyclic :=
  fun i ↦ by
    rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
    have := ((mappingCone.homotopyToZeroOfId L).shift (-1)).homologyMap_eq i
    simp only [CategoryTheory.Functor.map_id, Functor.map_zero, homologyMap_id,
      homologyMap_zero] at this
    exact this

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The map `mappingCocone φ ⟶ mappingCocone (𝟙 L)` induced by the square from `φ` to `𝟙 L`;
it is `φ` on the first component and the identity on the second. -/
private noncomputable def toId : mappingCocone φ ⟶ mappingCocone (𝟙 L) :=
  (mappingCone.map φ (𝟙 L) φ (𝟙 L) (by simp))⟦(-1 : ℤ)⟧'

@[reassoc]
private lemma toId_comp_fst : toId φ ≫ fst (𝟙 L) = fst φ ≫ φ :=
  shiftFunctor_map_mappingCone_map_comp_fst _ _ _ _ _

@[reassoc]
private lemma toId_f_fst_f (p : ℤ) : (toId φ).f p ≫ (fst (𝟙 L)).f p = (fst φ).f p ≫ φ.f p :=
  HomologicalComplex.congr_hom (toId_comp_fst φ) p

@[reassoc]
private lemma toId_f_snd_v (p : ℤ) :
    (toId φ).f p ≫ (snd (𝟙 L)).v p (p + -1) rfl = (snd φ).v p (p + -1) rfl :=
  (shiftFunctor_map_mappingCone_map_f_snd_v _ _ _ _ _ p).trans (Category.comp_id _)

/-- The map to the mapping cocone of `𝟙 L` is a degreewise epimorphism when `φ` is. -/
private lemma epi_toId_f (p : ℤ) [Epi (φ.f p)] : Epi ((toId φ).f p) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A y
  obtain ⟨A', π, hπ, x, hx⟩ :=
    surjective_up_to_refinements_of_epi (φ.f p) (y ≫ (fst (𝟙 L)).f p)
  refine ⟨A', π, hπ, x ≫ (inl φ).v p p (add_zero p) +
    π ≫ y ≫ (snd (𝟙 L)).v p (p + -1) rfl ≫ (inr φ).1.v (p + -1) p (by lia), ?_⟩
  apply ext_to (𝟙 L) p (p + -1) rfl
  · simp [toId_f_fst_f, hx]
  · simp [toId_f_snd_v]

variable {S : ShortComplex (CochainComplex C ℤ)}

@[reassoc (attr := simp)]
private lemma lift_comp_toId : lift S.g S.f 0 (by simp) ≫ toId S.g = 0 := by
  ext p
  apply ext_to _ p (p + -1) rfl
  · rw [← HomologicalComplex.comp_f, Category.assoc, toId_comp_fst, lift_fst_assoc, S.zero]
    simp
  · simp [toId_f_snd_v]

/-- The lift of `S.f` to the mapping cocone of `S.g` is the kernel of the map to the mapping
cocone of `𝟙 S.X₃`, degreewise. -/
private lemma shortExact_lift_toId (hS : S.ShortExact) :
    (ShortComplex.mk _ _ (lift_comp_toId (S := S))).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦ ?_
  have hSp := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS p
  have : Mono (S.f.f p) := hSp.mono_f
  have : Epi (S.g.f p) := hSp.epi_g
  refine .mk' ?_ (mono_of_mono_fac (lift_f_fst_f S.g S.f 0 (by simp) p)) (epi_toId_f S.g p)
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x (hx : x ≫ (toId S.g).f p = 0)
  have h₁ : (x ≫ (fst S.g).f p) ≫ S.g.f p = 0 := by
    simpa [toId_f_fst_f] using hx =≫ (fst (𝟙 S.X₃)).f p
  have h₂ : x ≫ (snd S.g).v p (p + -1) rfl = 0 := by
    simpa [toId_f_snd_v] using hx =≫ (snd (𝟙 S.X₃)).v p (p + -1) rfl
  obtain ⟨A', π, hπ, z, hz⟩ :=
    (ShortComplex.exact_iff_exact_up_to_refinements _).1 hSp.exact _ h₁
  refine ⟨A', π, hπ, z, (?_ : π ≫ x = z ≫ (lift S.g S.f 0 (by simp)).f p)⟩
  apply ext_to S.g p (p + -1) rfl
  · simpa using hz
  · simp [h₂]

/-- For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of cochain complexes, the lift
`X₁ ⟶ mappingCocone S.g` of `S.f` is a quasi-isomorphism. -/
theorem quasiIso_lift_of_shortExact (hS : S.ShortExact) :
    QuasiIso (lift S.g S.f 0 (by simp)) := by
  -- The proof does not compare connecting maps: the lift is the kernel of a degreewise
  -- epimorphism onto the mapping cocone of `𝟙 X₃`, which is contractible. We use the long exact
  -- homology sequence of the short exact sequence
  -- `X₁ ⟶ mappingCocone S.g ⟶ mappingCocone (𝟙 X₃)`, whose third term is acyclic.
  have hT := shortExact_lift_toId hS
  have hC := acyclic_mappingCocone_id S.X₃
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (homologyMap (lift S.g S.f 0 (by simp)) n) :=
    (hT.homology_exact₁ (n - 1) n (by simp)).mono_g
      (((hC (n - 1)).isZero_homology).eq_of_src _ _)
  have : Epi (homologyMap (lift S.g S.f 0 (by simp)) n) :=
    (hT.homology_exact₂ n).epi_f (((hC n).isZero_homology).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Abelian

end CochainComplex.mappingCocone

namespace CochainComplex.mappingCocone

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {K L : CochainComplex C ℤ}

/-- Under the shift of mapping cones `CochainComplex.mappingCone.shiftIso`, followed by the
commutation `X⟦-1⟧⟦a⟧ ≅ X⟦a⟧⟦-1⟧` twisted by the sign `(-1)^a`, the shifted first projection of the
mapping cocone of `φ` is the first projection of the mapping cocone of `φ⟦a⟧'`. -/
lemma shiftFunctor_map_shiftIso_inv_comp_fst (φ : K ⟶ L) (a : ℤ) :
    (mappingCone.shiftIso φ a).inv⟦(-1 : ℤ)⟧' ≫
      ((a * -1).negOnePow • (shiftFunctorComm _ a (-1)).hom.app (mappingCone φ)) ≫
        (fst φ)⟦a⟧' = fst (φ⟦a⟧') := by
  ext p
  have h₁ := fst_f φ (p + a)
  have h₂ := fst_f (φ⟦a⟧') p
  simp only [HomologicalComplex.comp_f, shiftFunctor_map_f']
  -- The mapping cocone is `(mappingCone φ)⟦-1⟧` only up to unfolding, so the components of the
  -- first projections are rewritten up to that unfolding.
  erw [h₁, h₂]
  simp [shiftFunctorComm_hom_app_f, HomComplex.Cochain.XIsoOfEq_hom_comp_v, smul_smul,
    Linear.units_smul_comp, Linear.comp_units_smul]

end CochainComplex.mappingCocone

namespace CategoryTheory.NatTrans

open CochainComplex TauCeti

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {D : Type*} [Category* D] {F G : D ⥤ CochainComplex C ℤ} (τ : F ⟶ G)

/-- The mapping cocone of a natural transformation `τ : F ⟶ G` of functors with values in cochain
complexes, as the functor `X ↦ mappingCocone (τ.app X) = (mappingCone (τ.app X))⟦-1⟧`. -/
@[expose]
noncomputable def mappingCoconeFunctor : D ⥤ CochainComplex C ℤ :=
  mappingConeFunctor τ ⋙ CategoryTheory.shiftFunctor _ (-1)

@[simp]
theorem mappingCoconeFunctor_obj (X : D) :
    (mappingCoconeFunctor τ).obj X = mappingCocone (τ.app X) :=
  (rfl)

@[simp]
theorem mappingCoconeFunctor_map {X Y : D} (f : X ⟶ Y) :
    (mappingCoconeFunctor τ).map f = (mappingCone.map _ _ (F.map f) (G.map f)
      (τ.naturality f).symm)⟦(-1 : ℤ)⟧' :=
  (rfl)

/-- The first projections `mappingCocone (τ.app X) ⟶ F.obj X`, as a natural transformation. -/
@[expose]
noncomputable def mappingCoconeFunctorFst : mappingCoconeFunctor τ ⟶ F where
  app X := mappingCocone.fst (τ.app X)
  naturality _ _ f :=
    mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst _ _ _ _ (τ.naturality f).symm

@[simp]
theorem mappingCoconeFunctorFst_app (X : D) :
    (mappingCoconeFunctorFst τ).app X = mappingCocone.fst (τ.app X) :=
  (rfl)

variable [HasShift D ℤ] [F.CommShift ℤ] [G.CommShift ℤ] [NatTrans.CommShift τ ℤ]

/-- The mapping cocone of a natural transformation compatible with the shifts commutes with the
shifts: the mapping cone functor commutes with them, and `⟦-1⟧` commutes with the shift by `a`
through `shiftFunctorComm` twisted by the sign `(-1)^a`. -/
noncomputable instance : (mappingCoconeFunctor τ).CommShift ℤ :=
  letI := shiftFunctorCommShift (CochainComplex C ℤ) (-1)
  inferInstanceAs ((mappingConeFunctor τ ⋙ CategoryTheory.shiftFunctor _ (-1)).CommShift ℤ)

theorem mappingCoconeFunctor_commShiftIso_hom_app (a : ℤ) (X : D) :
    ((mappingCoconeFunctor τ).commShiftIso a).hom.app X =
      (mappingConeFunctorShiftIso τ a X).hom⟦(-1 : ℤ)⟧' ≫
        ((a * -1).negOnePow •
          (shiftFunctorComm _ a (-1)).hom.app (mappingCone (τ.app X))) := by
  let := shiftFunctorCommShift (CochainComplex C ℤ) (-1)
  refine (Functor.commShiftIso_comp_hom_app (mappingConeFunctor τ)
    (CategoryTheory.shiftFunctor _ (-1)) a X).trans ?_
  rw [shiftFunctorCommShift_commShiftIso_hom_app, mappingConeFunctor_commShiftIso_hom_app]
  -- The two sides differ only by `(mappingConeFunctor τ).obj X = mappingCone (τ.app X)`, which
  -- holds by definition (`mappingConeFunctor_obj`) but cannot be rewritten inside the dependent
  -- types of the morphisms.
  rfl

/-- The first projections of the mapping cocones commute with the shifts. -/
instance : NatTrans.CommShift (mappingCoconeFunctorFst τ) ℤ := ⟨fun a ↦ by
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    mappingCoconeFunctor_commShiftIso_hom_app, mappingCoconeFunctorFst_app,
    mappingConeFunctorShiftIso_hom, Functor.map_comp, Category.assoc]
  -- The outer composition passes through `mappingCocone (τ.app X)⟦a⟧`, which is
  -- `(mappingCone (τ.app X))⟦-1⟧⟦a⟧` only up to unfolding, so it is reassociated by hand.
  exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (mappingCocone.shiftFunctor_map_shiftIso_inv_comp_fst _ _))).trans
      (mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst _ _ _ _ _)⟩

end CategoryTheory.NatTrans

namespace CategoryTheory.NatTrans

open CochainComplex TauCeti

variable {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
  {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C] {F G : A ⥤ C}
  [F.Additive] [G.Additive] (α : F ⟶ G) {K L : CochainComplex A ℤ} (φ : K ⟶ L)

/-- For a natural transformation `α : F ⟶ G` of additive functors, the mapping cocone functor
`K ↦ mappingCocone (α.app K)` of the induced natural transformation of functors on cochain
complexes sends the mapping cone triangle of `φ` to the mapping cone triangle of its image,
compatibly with its commutation with the shifts. -/
noncomputable def mappingCoconeFunctorMapTriangleIso :
    (mappingCoconeFunctor (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))).mapTriangle.obj
        (mappingCone.triangle φ) ≅
      mappingCone.triangle
        ((mappingCoconeFunctor (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))).map φ) :=
  letI := shiftFunctorCommShift (CochainComplex C ℤ) (-1)
  (Functor.mapTriangleCompIso _ (CategoryTheory.shiftFunctor _ (-1))).app _ ≪≫
    (CategoryTheory.shiftFunctor _ (-1)).mapTriangle.mapIso
      (mappingConeFunctorMapTriangleIso α φ) ≪≫
    shiftFunctorMapTriangleIso _ (-1) _ ≪≫ mappingCone.shiftTriangleIso _ (-1)

/-! The components of `mappingCoconeFunctorMapTriangleIso` are composites of the components of
its four factors, whose objects agree only after unfolding `mappingCoconeFunctor`. The proofs
below therefore split the composite with `change`, rewrite the factors by their component lemmas,
and identify the remaining identities and signs. -/

@[simp]
lemma mappingCoconeFunctorMapTriangleIso_hom_hom₁ :
    (mappingCoconeFunctorMapTriangleIso α φ).hom.hom₁ = 𝟙 _ := by
  change _ ≫ _ ≫ _ ≫ (𝟙 _ : (_ : CochainComplex C ℤ) ⟶ _) = _
  simp only [Iso.app_hom, Functor.mapTriangleCompIso_hom_app_hom₁, Functor.mapIso_hom,
    Functor.mapTriangle_map_hom₁, mappingConeFunctorMapTriangleIso_hom_hom₁, Functor.map_id,
    shiftFunctorMapTriangleIso_hom_hom₁]
  exact (Category.id_comp _).trans ((Category.id_comp _).trans (Category.id_comp _))

@[simp]
lemma mappingCoconeFunctorMapTriangleIso_hom_hom₂ :
    (mappingCoconeFunctorMapTriangleIso α φ).hom.hom₂ = 𝟙 _ := by
  change _ ≫ _ ≫ _ ≫
    ((-1 : ℤ).negOnePow • 𝟙 (mappingCocone ((NatTrans.mapHomologicalComplex α _).app L))) = _
  simp only [Iso.app_hom, Functor.mapTriangleCompIso_hom_app_hom₂, Functor.mapIso_hom,
    Functor.mapTriangle_map_hom₂, mappingConeFunctorMapTriangleIso_hom_hom₂, Functor.map_id,
    shiftFunctorMapTriangleIso_hom_hom₂]
  change 𝟙 (mappingCocone ((NatTrans.mapHomologicalComplex α _).app L)) ≫ 𝟙 _ ≫
    ((-1 : ℤ).negOnePow • 𝟙 (mappingCocone ((NatTrans.mapHomologicalComplex α _).app L))) ≫
      ((-1 : ℤ).negOnePow • 𝟙 _) = 𝟙 _
  simp

@[simp]
lemma mappingCoconeFunctorMapTriangleIso_hom_hom₃ :
    (mappingCoconeFunctorMapTriangleIso α φ).hom.hom₃ =
      (mappingConeFunctorMapTriangleIso α φ).hom.hom₃⟦(-1 : ℤ)⟧' ≫
        (mappingCone.shiftIso _ (-1)).hom := by
  change _ ≫ _ ≫ _ ≫ (mappingCone.shiftIso _ (-1)).hom = _
  simp only [Iso.app_hom, Functor.mapTriangleCompIso_hom_app_hom₃, Functor.mapIso_hom,
    Functor.mapTriangle_map_hom₃, shiftFunctorMapTriangleIso_hom_hom₃]
  exact (Category.id_comp _).trans (whisker_eq _ (Category.id_comp _))

@[simp]
lemma mappingCoconeFunctorMapTriangleIso_inv_hom₁ :
    (mappingCoconeFunctorMapTriangleIso α φ).inv.hom₁ = 𝟙 _ := by
  change (((𝟙 _ : (_ : CochainComplex C ℤ) ⟶ _) ≫ _) ≫ _) ≫ _ = _
  simp only [Iso.app_inv, Functor.mapTriangleCompIso_inv_app_hom₁, Functor.mapIso_inv,
    Functor.mapTriangle_map_hom₁, mappingConeFunctorMapTriangleIso_inv_hom₁, Functor.map_id,
    shiftFunctorMapTriangleIso_inv_hom₁]
  exact (Category.comp_id _).trans ((Category.comp_id _).trans (Category.comp_id _))

@[simp]
lemma mappingCoconeFunctorMapTriangleIso_inv_hom₂ :
    (mappingCoconeFunctorMapTriangleIso α φ).inv.hom₂ = 𝟙 _ := by
  change ((((-1 : ℤ).negOnePow⁻¹ •
    𝟙 (mappingCocone ((NatTrans.mapHomologicalComplex α _).app L))) ≫ _) ≫ _) ≫ _ = _
  simp only [Iso.app_inv, Functor.mapTriangleCompIso_inv_app_hom₂, Functor.mapIso_inv,
    Functor.mapTriangle_map_hom₂, mappingConeFunctorMapTriangleIso_inv_hom₂, Functor.map_id,
    shiftFunctorMapTriangleIso_inv_hom₂]
  change ((((-1 : ℤ).negOnePow⁻¹ • 𝟙 (mappingCocone ((NatTrans.mapHomologicalComplex α _).app L))) ≫
    ((-1 : ℤ).negOnePow • 𝟙 (mappingCocone ((NatTrans.mapHomologicalComplex α _).app L)))) ≫ 𝟙 _) ≫
      𝟙 _ = 𝟙 _
  simp

@[simp]
lemma mappingCoconeFunctorMapTriangleIso_inv_hom₃ :
    (mappingCoconeFunctorMapTriangleIso α φ).inv.hom₃ =
      (mappingCone.shiftIso _ (-1)).inv ≫
        (mappingConeFunctorMapTriangleIso α φ).inv.hom₃⟦(-1 : ℤ)⟧' := by
  change (((mappingCone.shiftIso _ (-1)).inv ≫ _) ≫ _) ≫ _ = _
  simp only [Iso.app_inv, Functor.mapTriangleCompIso_inv_app_hom₃, Functor.mapIso_inv,
    Functor.mapTriangle_map_hom₃, shiftFunctorMapTriangleIso_inv_hom₃]
  exact (Category.comp_id _).trans (eq_whisker (Category.comp_id _) _)

end CategoryTheory.NatTrans
