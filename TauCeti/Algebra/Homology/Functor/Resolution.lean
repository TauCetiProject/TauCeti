/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Cycles and augmented resolutions of diagrams of complexes

For a diagram `K : D ⥤ HomologicalComplex A c`, the cycles in degree `i` form a diagram in `A`.
Their inclusions and the differentials corestricted to cycles are natural transformations,
forming the short complex `Zⁱ(K) ⟶ Kⁱ ⟶ Zʲ(K)`. At any object where `K` is exact in degree `j`,
this sequence is short exact if `c.Rel i j`.

An augmentation `ε : P ⋙ CochainComplex.single₀ A ⟶ K` gives the short complex
`P ⟶ K⁰ ⟶ Z¹(K)`. It is short exact at any object where `ε` is a quasi-isomorphism in degrees
zero and one. These sequences split an augmented resolution into short exact sequences, allowing
objectwise dimension shifting without imposing exactness at every object of the diagram.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Functor

section Cycles

variable {D A : Type*} [Category* D] [Category* A] [HasZeroMorphisms A]
  [CategoryWithHomology A] {ι : Type*} {c : ComplexShape ι}
  (K : D ⥤ HomologicalComplex A c)

/-- The natural inclusion of the diagram of degree-`i` cycles into the degree-`i` terms. -/
def iCycles (i : ι) : K ⋙ HomologicalComplex.cyclesFunctor A c i ⟶
    K ⋙ HomologicalComplex.eval A c i where
  app Y := (K.obj Y).iCycles i
  naturality _ _ f := HomologicalComplex.cyclesMap_i (K.map f) i

@[simp]
lemma iCycles_app (i : ι) (Y : D) : (K.iCycles i).app Y = (K.obj Y).iCycles i := (rfl)

/-- The differential from degree `i` corestricted to the diagram of degree-`j` cycles. -/
def toCycles (i j : ι) : K ⋙ HomologicalComplex.eval A c i ⟶
    K ⋙ HomologicalComplex.cyclesFunctor A c j where
  app Y := (K.obj Y).toCycles i j
  naturality _ _ f := ((K.obj _).toCycles_cyclesMap (K.map f) i j).symm

@[simp]
lemma toCycles_app (i j : ι) (Y : D) :
    (K.toCycles i j).app Y = (K.obj Y).toCycles i j := (rfl)

/-- The short complex `Zⁱ(K) ⟶ Kⁱ ⟶ Zʲ(K)` of diagrams of cycles and terms. -/
def cyclesShortComplex (i j : ι) : ShortComplex (D ⥤ A) :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) <|
    NatTrans.ext <| funext fun Y ↦ (K.obj Y).iCycles_toCycles i j

@[simp]
lemma cyclesShortComplex_X₁ (i j : ι) :
    (K.cyclesShortComplex i j).X₁ = K ⋙ HomologicalComplex.cyclesFunctor A c i := (rfl)

@[simp]
lemma cyclesShortComplex_X₂ (i j : ι) :
    (K.cyclesShortComplex i j).X₂ = K ⋙ HomologicalComplex.eval A c i := (rfl)

@[simp]
lemma cyclesShortComplex_X₃ (i j : ι) :
    (K.cyclesShortComplex i j).X₃ = K ⋙ HomologicalComplex.cyclesFunctor A c j := (rfl)

@[simp]
lemma cyclesShortComplex_f (i j : ι) :
    (K.cyclesShortComplex i j).f = eqToHom (K.cyclesShortComplex_X₁ i j) ≫
      K.iCycles i ≫ eqToHom (K.cyclesShortComplex_X₂ i j).symm := by
  unfold cyclesShortComplex
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp]
lemma cyclesShortComplex_g (i j : ι) :
    (K.cyclesShortComplex i j).g = eqToHom (K.cyclesShortComplex_X₂ i j) ≫
      K.toCycles i j ≫ eqToHom (K.cyclesShortComplex_X₃ i j).symm := by
  unfold cyclesShortComplex
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp]
lemma map_cyclesShortComplex (i j : ι) (Y : D) :
    (K.cyclesShortComplex i j).map ((evaluation D A).obj Y) =
      ShortComplex.mk ((K.obj Y).iCycles i) ((K.obj Y).toCycles i j)
        ((K.obj Y).iCycles_toCycles i j) := (rfl)

end Cycles

variable {D A : Type*} [Category* D] [Category* A] [Preadditive A]
  [CategoryWithHomology A] {ι : Type*} {c : ComplexShape ι}
  (K : D ⥤ HomologicalComplex A c)

/-- The cycle sequence is short exact at an object where the complex is exact in the next degree.
No exactness is required at the other objects of the diagram. -/
lemma shortExact_map_cyclesShortComplex (i j : ι) (hij : c.Rel i j) {Y : D}
    (hY : (K.obj Y).ExactAt j) :
    ((K.cyclesShortComplex i j).map ((evaluation D A).obj Y)).ShortExact := by
  rw [K.map_cyclesShortComplex]
  have : Epi ((K.obj Y).toCycles i j) :=
    HomologicalComplex.epi_toCycles_of_exactAt hY (c.prev_eq' hij)
  exact
    { exact := by
        simpa only [HomologicalComplex.cyclesShortComplex_def] using
          (K.obj Y).cyclesShortComplex_exact i j (c.next_eq' hij)
      mono_f := inferInstanceAs (Mono ((K.obj Y).iCycles i))
      epi_g := inferInstanceAs (Epi ((K.obj Y).toCycles i j)) }

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

section Augmentation

variable {D A : Type*} [Category* D] [Category* A] [HasZeroMorphisms A]
  [HasZeroObject A] {P : D ⥤ A} {K : D ⥤ CochainComplex A ℕ}
  (ε : P ⋙ CochainComplex.single₀ A ⟶ K)

/-- The degree-zero component of an augmentation, as a morphism of diagrams in `A`. -/
def augmentationι : P ⟶ K ⋙ HomologicalComplex.eval A _ 0 :=
  (Functor.rightUnitor P).inv ≫
    Functor.whiskerLeft P (HomologicalComplex.singleCompEvalIsoSelf A (ComplexShape.up ℕ) 0).inv ≫
      (Functor.associator P (CochainComplex.single₀ A) _).inv ≫
        Functor.whiskerRight ε (HomologicalComplex.eval A _ 0)

@[simp]
lemma augmentationι_app (Y : D) :
    ε.augmentationι.app Y =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj Y)).inv ≫ (ε.app Y).f 0 := by
  simp [augmentationι]

variable [CategoryWithHomology A]

/-- The short complex `P ⟶ K⁰ ⟶ Z¹(K)` cut out by an augmented diagram of cochain complexes. -/
def augmentationShortComplex : ShortComplex (D ⥤ A) :=
  ShortComplex.mk ε.augmentationι (K.toCycles 0 1) <|
    NatTrans.ext <| funext fun Y ↦ by
      rw [NatTrans.comp_app, zero_app, augmentationι_app, Functor.toCycles_app]
      exact (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (HomologicalComplex.single_f_toCycles (ε.app Y) 1)).trans comp_zero

@[simp]
lemma augmentationShortComplex_X₁ : ε.augmentationShortComplex.X₁ = P := (rfl)

@[simp]
lemma augmentationShortComplex_X₂ :
    ε.augmentationShortComplex.X₂ = K ⋙ HomologicalComplex.eval A _ 0 := (rfl)

@[simp]
lemma augmentationShortComplex_X₃ :
    ε.augmentationShortComplex.X₃ = K ⋙ HomologicalComplex.cyclesFunctor A _ 1 := (rfl)

@[simp]
lemma augmentationShortComplex_f :
    ε.augmentationShortComplex.f = eqToHom ε.augmentationShortComplex_X₁ ≫
      ε.augmentationι ≫ eqToHom ε.augmentationShortComplex_X₂.symm := by
  unfold augmentationShortComplex
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp]
lemma augmentationShortComplex_g :
    ε.augmentationShortComplex.g = eqToHom ε.augmentationShortComplex_X₂ ≫
      K.toCycles 0 1 ≫ eqToHom ε.augmentationShortComplex_X₃.symm := by
  unfold augmentationShortComplex
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp]
lemma map_augmentationShortComplex (Y : D) :
    ε.augmentationShortComplex.map ((evaluation D A).obj Y) =
      ShortComplex.mk
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj Y)).inv ≫ (ε.app Y).f 0)
        ((K.obj Y).toCycles 0 1)
        ((Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (HomologicalComplex.single_f_toCycles (ε.app Y) 1)).trans
            comp_zero) := by
  dsimp only [augmentationShortComplex, ShortComplex.map]
  simp only [evaluation_obj_map, augmentationι_app, Functor.toCycles_app]
  rfl

end Augmentation

variable {D A : Type*} [Category* D] [Category* A] [Preadditive A]
  [HasZeroObject A] [CategoryWithHomology A] {P : D ⥤ A} {K : D ⥤ CochainComplex A ℕ}
  (ε : P ⋙ CochainComplex.single₀ A ⟶ K)

/-- The augmented sequence is short exact at any object where the augmentation is a
quasi-isomorphism in degrees zero and one. No condition on its higher cohomology is needed. -/
lemma shortExact_map_augmentationShortComplex {Y : D}
    (h₀ : QuasiIsoAt (ε.app Y) 0) (h₁ : QuasiIsoAt (ε.app Y) 1) :
    (ε.augmentationShortComplex.map ((evaluation D A).obj Y)).ShortExact := by
  rw [ε.map_augmentationShortComplex]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj Y)
  let ψ := (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℕ) 0 0 1).map
    (ε.app Y)
  -- In degree zero, the augmentation identifies its source with the kernel of the differential.
  have hψ := (ShortComplex.quasiIso_iff_isIso_liftCycles ψ
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) _ _ _ _)
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) _ _ _ _)
    ((K.obj Y).shape 0 0 (by simp))).1
      ((CochainComplex.quasiIsoAt₀_iff (ε.app Y)).1 h₀)
  let S := (K.obj Y).sc' 0 0 1
  let l := S.liftCycles ((ε.app Y).f 0) (HomologicalComplex.single_f_d (ε.app Y) 1)
  have : IsIso (S.liftCycles ((ε.app Y).f 0)
      (HomologicalComplex.single_f_d (ε.app Y) 1)) := hψ
  have hk : IsLimit (KernelFork.ofι ((ε.app Y).f 0)
      (HomologicalComplex.single_f_d (ε.app Y) 1)) :=
    IsLimit.ofIsoLimit S.cyclesIsKernel
      (Fork.ext (asIso l).symm (by
        apply (cancel_epi l).1
        simp only [Iso.symm_hom, ← Category.assoc, asIso_inv, IsIso.hom_inv_id,
          Category.id_comp]
        erw [KernelFork.ι_ofι, KernelFork.ι_ofι]
        exact (S.liftCycles_i _ _).symm))
  have hmono : Mono ((ε.app Y).f 0) := mono_of_isLimit_fork hk
  have hexact : (ShortComplex.mk ((ε.app Y).f 0) ((K.obj Y).d 0 1)
      (HomologicalComplex.single_f_d (ε.app Y) 1)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ hk
  -- Exactness in degree one makes the differential onto the next cycles an epimorphism.
  have h₁' : (K.obj Y).ExactAt 1 := (quasiIsoAt_iff_exactAt (ε.app Y) 1
    (CochainComplex.exactAt_succ_single_obj _ 0)).1 h₁
  have : Epi ((K.obj Y).toCycles 0 1) :=
    HomologicalComplex.epi_toCycles_of_exactAt h₁' (by simp)
  let φ : ShortComplex.mk
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj Y)).inv ≫ (ε.app Y).f 0)
      ((K.obj Y).toCycles 0 1) ((Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (HomologicalComplex.single_f_toCycles (ε.app Y) 1)).trans comp_zero) ⟶
      ShortComplex.mk ((ε.app Y).f 0) ((K.obj Y).d 0 1)
        (HomologicalComplex.single_f_d (ε.app Y) 1) :=
    { τ₁ := e.inv
      τ₂ := 𝟙 _
      τ₃ := (K.obj Y).iCycles 1
      comm₁₂ := (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (HomologicalComplex.toCycles_i _ _ _).symm }
  -- The degree-zero term of a single complex is identified with `P(Y)` by `e`.
  exact
    { exact := (@ShortComplex.exact_iff_of_epi_of_isIso_of_mono _ _ _ _ _ φ
        (inferInstanceAs (Epi e.inv)) (inferInstanceAs (IsIso (𝟙 _)))
        (inferInstanceAs (Mono ((K.obj Y).iCycles 1)))).2 hexact
      mono_f := @mono_comp _ _ _ _ _ e.inv inferInstance ((ε.app Y).f 0) hmono
      epi_g := inferInstanceAs (Epi ((K.obj Y).toCycles 0 1)) }

end CategoryTheory.NatTrans
