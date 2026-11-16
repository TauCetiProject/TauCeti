/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Subobject.Limits
public import TauCeti.CategoryTheory.Subobject.Image

/-!
# Subquotient presentations in an abelian category

A subquotient presentation `p : TauCeti.SubquotientPresentation A X` records a pair of subobjects
`p.bottom ≤ p.top` of an ambient object `A` together with an isomorphism
`p.iso : cokernel (Subobject.ofLE p.bottom p.top p.le) ≅ X`. It determines a canonical epimorphism
`p.proj : (p.top : C) ⟶ X` with kernel `p.bottom`.

## Main declarations

* `CategoryTheory.Subobject.exists_pullback_eq_of_epi` and
  `CategoryTheory.Subobject.pullback_exists_eq_of_kernelSubobject_le`: the Galois correspondence
  between subobjects of the target of an epimorphism and subobjects of its source containing the
  kernel.
* `TauCeti.SubquotientPresentation`: a presentation of an object `X` as a subquotient of `A`.
* `TauCeti.SubquotientPresentation.subobjectOrderIso`: the order isomorphism between `Subobject X`
  and the interval `Set.Icc p.bottom p.top` in `Subobject A`, given by `p.lift` and `p.desc`,
  together with preservation of greatest lower bounds and least upper bounds of nonempty families.
* `TauCeti.SubquotientPresentation.subquotient` and `TauCeti.SubquotientPresentation.comp`:
  given `I ≤ K` in `Subobject X`, the induced presentation of `cokernel (Subobject.ofLE I K hIK)`
  inside `A` by `(p.lift I, p.lift K)`, composition of nested presentations (`comp`, `comp_assoc`,
  `comp_refl`, `lift_comp`), two-step naturality (`subquotient_subquotient`), and functoriality
  under morphisms of ambient objects (`map`, `map_subquotient`, `comp_map`).
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C] {X Y : C}

lemma le_pullback_iff [HasPullbacks C] (f : X ⟶ Y) (X' : Subobject X) (Y' : Subobject Y) :
    X' ≤ (pullback f).obj Y' ↔ Y'.Factors (X'.arrow ≫ f) := by
  refine ⟨fun h ↦ (pullback_factors_iff f Y' X'.arrow).mp
    (factors_of_le X'.arrow h (factors_self X')), fun h ↦ ?_⟩
  exact le_pullback_of_comm f (Y'.factorThru (X'.arrow ≫ f) h) (Y'.factorThru_arrow _ h)

lemma exists_le_iff [HasPullbacks C] [HasImages C] (f : X ⟶ Y) (X' : Subobject X)
    (Y' : Subobject Y) :
    («exists» f).obj X' ≤ Y' ↔ Y'.Factors (X'.arrow ≫ f) :=
  ((existsPullbackAdj f).gc X' Y').trans (le_pullback_iff f X' Y')

@[simp]
lemma pullback_bot [HasZeroMorphisms C] [HasZeroObject C] [HasPullbacks C]
    (f : X ⟶ Y) [HasKernel f] :
    (pullback f).obj ⊥ = kernelSubobject f := by
  refine le_antisymm ?_ ?_
  · refine le_kernelSubobject _ _ ?_
    rw [← (isPullback f ⊥).w, bot_arrow, comp_zero]
  · rw [le_pullback_iff, kernelSubobject_arrow_comp]
    exact factors_zero

lemma kernelSubobject_cokernel_π [Abelian C] (f : X ⟶ Y) [Mono f] :
    kernelSubobject (cokernel.π f) = mk f := by
  refine le_antisymm ?_ ?_
  · exact le_mk_of_comm (Abelian.monoLift f _ (kernelSubobject_arrow_comp _))
      (Abelian.monoLift_comp _ _ _)
  · exact mk_le_mk_of_comm (kernel.lift (cokernel.π f) f (cokernel.condition f)) (by simp)

/-- For an epimorphism `f : X ⟶ Y` in an abelian category, taking the direct image of the pullback
of a subobject `S` of `Y` recovers `S`. -/
@[simp]
theorem exists_pullback_eq_of_epi [Abelian C] (f : X ⟶ Y) [Epi f] (S : Subobject Y) :
    («exists» f).obj ((pullback f).obj S) = S := by
  simp only [exists_eq_imageSubobject, ← (isPullback f S).w, imageSubobject_comp_eq_of_epi,
    imageSubobject_mono, mk_arrow]

/-- For an epimorphism `f : X ⟶ Y` in an abelian category, taking the pullback of the direct image
of a subobject `S` of `X` containing `kernelSubobject f` recovers `S`. -/
theorem pullback_exists_eq_of_kernelSubobject_le [Abelian C] (f : X ⟶ Y) [Epi f]
    {S : Subobject X} (hS : kernelSubobject f ≤ S) :
    (pullback f).obj ((«exists» f).obj S) = S := by
  refine le_antisymm ?_ (le_pullback_exists f S)
  -- Since `kernelSubobject f ≤ S`, `cokernel.π S.arrow` annihilates `kernel.ι f` and therefore
  -- factors through the epimorphism `f`.
  have hker : kernel.ι f ≫ cokernel.π S.arrow = 0 := by
    rw [← kernelSubobject_arrow' f, Category.assoc, ← ofLE_arrow hS, Category.assoc,
      cokernel.condition, comp_zero, comp_zero]
  let g : Y ⟶ cokernel S.arrow := Abelian.epiDesc f (cokernel.π S.arrow) hker
  have hfg : f ≫ g = cokernel.π S.arrow := Abelian.comp_epiDesc f (cokernel.π S.arrow) hker
  have him : ((«exists» f).obj S).arrow ≫ g = 0 := by
    have hcomp : (S.arrow ≫ f) ≫ g = 0 := by rw [Category.assoc, hfg, cokernel.condition]
    have him0 : (imageSubobject (S.arrow ≫ f)).arrow ≫ g = 0 :=
      imageSubobject_arrow_comp_eq_zero hcomp
    rw [← ofLE_arrow (exists_eq_imageSubobject f S).le, Category.assoc, him0, comp_zero]
  have hzero : ((pullback f).obj ((«exists» f).obj S)).arrow ≫ cokernel.π S.arrow = 0 := by
    rw [← hfg, ← Category.assoc, ← (isPullback f ((«exists» f).obj S)).w, Category.assoc,
      him, comp_zero]
  exact le_of_comm (Abelian.monoLift S.arrow _ hzero) (Abelian.monoLift_comp _ _ _)

/-- In an abelian category, the cokernel of an inclusion `B ≤ Z` of subobjects is zero if and only
if `B = Z`. -/
theorem isZero_cokernel_ofLE_iff [Abelian C] {A : C} {B Z : Subobject A} (h : B ≤ Z) :
    IsZero (cokernel (ofLE B Z h)) ↔ B = Z := by
  rw [← Preadditive.epi_iff_isZero_cokernel]
  refine ⟨fun _ ↦ ?_, fun hEq ↦ ?_⟩
  · have : IsIso (ofLE B Z h) := isIso_of_mono_of_epi (ofLE B Z h)
    exact le_antisymm h (le_of_comm (inv (ofLE B Z h)) (by simp))
  · subst hEq
    rw [ofLE_refl]
    infer_instance

end CategoryTheory.Subobject

namespace TauCeti

/-- A presentation of an object `X` as a subquotient `top / bottom` of an ambient object `A`,
consisting of subobjects `bottom ≤ top` of `A` and an isomorphism from
`cokernel (Subobject.ofLE bottom top le)` to `X`. -/
structure SubquotientPresentation {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasCokernels C] (A X : C) where
  /-- The denominator subobject of `A`. -/
  bottom : Subobject A
  /-- The numerator subobject of `A`. -/
  top : Subobject A
  /-- The inclusion of `bottom` into `top`. -/
  le : bottom ≤ top
  /-- The identification of the quotient `top / bottom` with `X`. -/
  iso : cokernel (Subobject.ofLE bottom top le) ≅ X

namespace SubquotientPresentation

section Basic

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]
  {A A' A'' X X' X'' Y : C}

/-- The canonical epimorphism `(p.top : C) ⟶ X` associated to a subquotient presentation `p`. -/
noncomputable def proj (p : SubquotientPresentation A X) : (p.top : C) ⟶ X :=
  cokernel.π (Subobject.ofLE p.bottom p.top p.le) ≫ p.iso.hom

lemma proj_eq (p : SubquotientPresentation A X) :
    p.proj = cokernel.π (Subobject.ofLE p.bottom p.top p.le) ≫ p.iso.hom := by
  rfl

instance (p : SubquotientPresentation A X) : Epi p.proj := by
  dsimp [proj]
  infer_instance

@[reassoc (attr := simp)]
lemma ofLE_comp_proj (p : SubquotientPresentation A X) :
    Subobject.ofLE p.bottom p.top p.le ≫ p.proj = 0 := by
  simp [proj]

/-- `p.proj` exhibits `X` as the cokernel of `Subobject.ofLE p.bottom p.top p.le`. -/
noncomputable def isColimitCokernelCofork (p : SubquotientPresentation A X) :
    IsColimit (CokernelCofork.ofπ p.proj p.ofLE_comp_proj) :=
  IsColimit.ofIsoColimit (cokernelIsCokernel (Subobject.ofLE p.bottom p.top p.le))
    (Cofork.ext p.iso rfl)

@[ext (iff := false)]
lemma ext {p q : SubquotientPresentation A X}
    (hB : p.bottom = q.bottom) (hZ : p.top = q.top)
    (hproj : p.proj = (Subobject.isoOfEq _ _ hZ).hom ≫ q.proj) : p = q := by
  cases p
  cases q
  dsimp at hB hZ hproj
  subst hB
  subst hZ
  congr 1
  ext
  simpa [proj] using hproj

/-- The tautological presentation of `cokernel (Subobject.ofLE B Z h)` inside `A`. -/
noncomputable abbrev ofLE (B Z : Subobject A) (h : B ≤ Z) :
    SubquotientPresentation A (cokernel (Subobject.ofLE B Z h)) where
  bottom := B
  top := Z
  le := h
  iso := Iso.refl _

@[simp]
lemma ofLE_proj (B Z : Subobject A) (h : B ≤ Z) :
    (ofLE B Z h).proj = cokernel.π (Subobject.ofLE B Z h) := by
  simp [proj, ofLE]

/-- Transport a subquotient presentation along an isomorphism of the presented object. -/
noncomputable abbrev transIso (p : SubquotientPresentation A X) (e : X ≅ Y) :
    SubquotientPresentation A Y where
  bottom := p.bottom
  top := p.top
  le := p.le
  iso := p.iso ≪≫ e

@[reassoc, simp]
lemma transIso_proj (p : SubquotientPresentation A X) (e : X ≅ Y) :
    (p.transIso e).proj = p.proj ≫ e.hom := by
  simp [proj, transIso]

@[simp]
lemma transIso_refl (p : SubquotientPresentation A X) :
    p.transIso (Iso.refl X) = p :=
  ext rfl rfl (by simp)

lemma transIso_trans (p : SubquotientPresentation A X) (e : X ≅ X') (e' : X' ≅ X'') :
    (p.transIso e).transIso e' = p.transIso (e ≪≫ e') :=
  ext rfl rfl (by simp)

/-- A morphism `f : A ⟶ A'` carrying `p.bottom` into `q.bottom` and `p.top` into `q.top` induces
a canonical morphism `X ⟶ X'` between the presented subquotients. -/
noncomputable def map (p : SubquotientPresentation A X) (q : SubquotientPresentation A' X')
    (f : A ⟶ A') (hB : q.bottom.Factors (p.bottom.arrow ≫ f))
    (hZ : q.top.Factors (p.top.arrow ≫ f)) : X ⟶ X' :=
  p.iso.inv ≫ cokernel.desc (Subobject.ofLE p.bottom p.top p.le)
    (q.top.factorThru (p.top.arrow ≫ f) hZ ≫ q.proj) (by
      have hsq : Subobject.ofLE p.bottom p.top p.le ≫ q.top.factorThru (p.top.arrow ≫ f) hZ =
          q.bottom.factorThru (p.bottom.arrow ≫ f) hB ≫ Subobject.ofLE q.bottom q.top q.le := by
        rw [← cancel_mono q.top.arrow]
        simp
      rw [reassoc_of% hsq, ofLE_comp_proj, comp_zero])

@[reassoc (attr := simp)]
lemma proj_comp_map (p : SubquotientPresentation A X) (q : SubquotientPresentation A' X')
    (f : A ⟶ A') (hB : q.bottom.Factors (p.bottom.arrow ≫ f))
    (hZ : q.top.Factors (p.top.arrow ≫ f)) :
    p.proj ≫ p.map q f hB hZ = q.top.factorThru (p.top.arrow ≫ f) hZ ≫ q.proj := by
  simp [proj, map]

lemma map_eq_of_proj_comp (p : SubquotientPresentation A X) (q : SubquotientPresentation A' X')
    (f : A ⟶ A') (hB : q.bottom.Factors (p.bottom.arrow ≫ f))
    (hZ : q.top.Factors (p.top.arrow ≫ f)) {g : X ⟶ X'}
    (hg : p.proj ≫ g = q.top.factorThru (p.top.arrow ≫ f) hZ ≫ q.proj) :
    p.map q f hB hZ = g := by
  rw [← cancel_epi p.proj, proj_comp_map, hg]

@[simp]
lemma map_id (p : SubquotientPresentation A X)
    (hB : p.bottom.Factors (p.bottom.arrow ≫ 𝟙 A))
    (hZ : p.top.Factors (p.top.arrow ≫ 𝟙 A)) :
    p.map p (𝟙 A) hB hZ = 𝟙 X := by
  apply map_eq_of_proj_comp
  have h1 : p.top.factorThru (p.top.arrow ≫ 𝟙 A) hZ = 𝟙 (p.top : C) := by
    rw [← cancel_mono p.top.arrow]
    simp
  rw [h1, Category.comp_id, Category.id_comp]

lemma map_comp (p : SubquotientPresentation A X) (q : SubquotientPresentation A' X')
    (r : SubquotientPresentation A'' X'') (f : A ⟶ A') (g : A' ⟶ A'')
    (hB : q.bottom.Factors (p.bottom.arrow ≫ f)) (hZ : q.top.Factors (p.top.arrow ≫ f))
    (hB' : r.bottom.Factors (q.bottom.arrow ≫ g)) (hZ' : r.top.Factors (q.top.arrow ≫ g))
    (hB'' : r.bottom.Factors (p.bottom.arrow ≫ (f ≫ g)))
    (hZ'' : r.top.Factors (p.top.arrow ≫ (f ≫ g))) :
    p.map q f hB hZ ≫ q.map r g hB' hZ' = p.map r (f ≫ g) hB'' hZ'' := by
  symm
  apply map_eq_of_proj_comp
  rw [proj_comp_map_assoc, proj_comp_map, ← Category.assoc]
  congr 1
  rw [← cancel_mono r.top.arrow]
  simp

@[simp]
lemma map_transIso_left (p : SubquotientPresentation A X) (q : SubquotientPresentation A' X')
    (e : X ≅ Y) (f : A ⟶ A')
    (hB : q.bottom.Factors (p.bottom.arrow ≫ f)) (hZ : q.top.Factors (p.top.arrow ≫ f)) :
    (p.transIso e).map q f hB hZ = e.inv ≫ p.map q f hB hZ := by
  apply map_eq_of_proj_comp
  simp

@[simp]
lemma map_transIso_right (p : SubquotientPresentation A X) (q : SubquotientPresentation A' X')
    (e : X' ≅ Y) (f : A ⟶ A')
    (hB : q.bottom.Factors (p.bottom.arrow ≫ f)) (hZ : q.top.Factors (p.top.arrow ≫ f)) :
    p.map (q.transIso e) f hB hZ = p.map q f hB hZ ≫ e.hom := by
  apply map_eq_of_proj_comp
  simp

/-- Two presentations of `X` and `X'` inside the same object `A` with equal `bottom` and `top`
subobjects are canonically isomorphic. -/
noncomputable def isoOfEq {p : SubquotientPresentation A X} {q : SubquotientPresentation A X'}
    (hB : p.bottom = q.bottom) (hZ : p.top = q.top) : X ≅ X' where
  hom := p.map q (𝟙 A)
    (by rw [Category.comp_id, hB]; exact Subobject.factors_self q.bottom)
    (by rw [Category.comp_id, hZ]; exact Subobject.factors_self q.top)
  inv := q.map p (𝟙 A)
    (by rw [Category.comp_id, ← hB]; exact Subobject.factors_self p.bottom)
    (by rw [Category.comp_id, ← hZ]; exact Subobject.factors_self p.top)
  hom_inv_id := by
    rw [map_comp]
    · simp
    · rw [Category.comp_id, Category.comp_id]
      exact Subobject.factors_self p.bottom
    · rw [Category.comp_id, Category.comp_id]
      exact Subobject.factors_self p.top
  inv_hom_id := by
    rw [map_comp]
    · simp
    · rw [Category.comp_id, Category.comp_id]
      exact Subobject.factors_self q.bottom
    · rw [Category.comp_id, Category.comp_id]
      exact Subobject.factors_self q.top

@[reassoc (attr := simp)]
lemma proj_comp_isoOfEq_hom {p : SubquotientPresentation A X} {q : SubquotientPresentation A X'}
    (hB : p.bottom = q.bottom) (hZ : p.top = q.top) :
    p.proj ≫ (isoOfEq hB hZ).hom = (Subobject.isoOfEq _ _ hZ).hom ≫ q.proj := by
  dsimp [isoOfEq]
  rw [proj_comp_map]
  congr 1
  rw [← cancel_mono q.top.arrow]
  simp

end Basic

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {A A' X X' Y : C}

/-- The canonical isomorphism `cokernel (Subobject.ofLE ⊥ ⊤ bot_le) ≅ A`. -/
noncomputable def reflIso (A : C) :
    cokernel (Subobject.ofLE (⊥ : Subobject A) ⊤ bot_le) ≅ A :=
  cokernelIsoOfEq (by rw [← cancel_mono (⊤ : Subobject A).arrow]; simp) ≪≫
    cokernelZeroIsoTarget ≪≫ asIso (⊤ : Subobject A).arrow

/-- The identity presentation of `A` inside itself by `(⊥, ⊤)`, with projection
`(⊤ : Subobject A).arrow`. -/
noncomputable abbrev refl (A : C) : SubquotientPresentation A A where
  bottom := ⊥
  top := ⊤
  le := bot_le
  iso := reflIso A

@[simp]
lemma refl_proj (A : C) : (refl A).proj = (⊤ : Subobject A).arrow := by
  simp [proj, refl, reflIso]

@[simp]
lemma kernelSubobject_proj (p : SubquotientPresentation A X) :
    kernelSubobject p.proj = Subobject.mk (Subobject.ofLE p.bottom p.top p.le) := by
  rw [proj, kernelSubobject_comp_mono, Subobject.kernelSubobject_cokernel_π]

/-- The preimage of a subobject `Y` of `X` in the ambient object `A` along `p.proj`, lying in the
interval `[p.bottom, p.top]`. -/
noncomputable def lift (p : SubquotientPresentation A X) (Y : Subobject X) : Subobject A :=
  (Subobject.map p.top.arrow).obj ((Subobject.pullback p.proj).obj Y)

/-- The image in `X` of a subobject `W` of `A` intersected with `p.top` along `p.proj`. -/
noncomputable def desc (p : SubquotientPresentation A X) (W : Subobject A) : Subobject X :=
  (Subobject.exists p.proj).obj ((Subobject.pullback p.top.arrow).obj W)

lemma lift_mono (p : SubquotientPresentation A X) {Y₁ Y₂ : Subobject X} (h : Y₁ ≤ Y₂) :
    p.lift Y₁ ≤ p.lift Y₂ :=
  (Subobject.map p.top.arrow).monotone ((Subobject.pullback p.proj).monotone h)

lemma lift_monotone (p : SubquotientPresentation A X) : Monotone p.lift :=
  fun _ _ h ↦ p.lift_mono h

lemma desc_mono (p : SubquotientPresentation A X) {W₁ W₂ : Subobject A} (h : W₁ ≤ W₂) :
    p.desc W₁ ≤ p.desc W₂ :=
  (Subobject.exists p.proj).monotone ((Subobject.pullback p.top.arrow).monotone h)

lemma desc_monotone (p : SubquotientPresentation A X) : Monotone p.desc :=
  fun _ _ h ↦ p.desc_mono h

@[simp]
lemma lift_bot (p : SubquotientPresentation A X) : p.lift ⊥ = p.bottom := by
  simp only [lift, Subobject.pullback_bot, kernelSubobject_proj, Subobject.map_mk,
    Subobject.ofLE_arrow, Subobject.mk_arrow]

@[simp]
lemma lift_top (p : SubquotientPresentation A X) : p.lift ⊤ = p.top := by
  rw [lift, Subobject.pullback_top, Subobject.map_top, Subobject.mk_arrow]

lemma bottom_le_lift (p : SubquotientPresentation A X) (Y : Subobject X) :
    p.bottom ≤ p.lift Y :=
  p.lift_bot ▸ p.lift_monotone bot_le

lemma lift_le_top (p : SubquotientPresentation A X) (Y : Subobject X) :
    p.lift Y ≤ p.top :=
  p.lift_top ▸ p.lift_monotone le_top

@[simp]
lemma desc_lift (p : SubquotientPresentation A X) (Y : Subobject X) :
    p.desc (p.lift Y) = Y := by
  rw [desc, lift, Subobject.pullback_map_self, Subobject.exists_pullback_eq_of_epi]

lemma lift_desc (p : SubquotientPresentation A X) {W : Subobject A}
    (hB : p.bottom ≤ W) (hZ : W ≤ p.top) :
    p.lift (p.desc W) = W := by
  have hinf : (Subobject.map p.top.arrow).obj ((Subobject.pullback p.top.arrow).obj W) = W := by
    rw [← Subobject.inf_eq_map_pullback, inf_eq_right.mpr hZ]
  have hker : kernelSubobject p.proj ≤ (Subobject.pullback p.top.arrow).obj W := by
    have hle : (Subobject.map p.top.arrow).obj (kernelSubobject p.proj) ≤
        (Subobject.map p.top.arrow).obj ((Subobject.pullback p.top.arrow).obj W) := by
      simp only [kernelSubobject_proj, Subobject.map_mk, Subobject.ofLE_arrow, Subobject.mk_arrow,
        hinf]
      exact hB
    simpa [Subobject.pullback_map_self] using (Subobject.pullback p.top.arrow).monotone hle
  rw [lift, desc, Subobject.pullback_exists_eq_of_kernelSubobject_le p.proj hker, hinf]

/-- Preimage along `p.proj` is an order isomorphism from `Subobject X` onto the interval
`Set.Icc p.bottom p.top` in `Subobject A`, with inverse `p.desc`. -/
noncomputable def subobjectOrderIso (p : SubquotientPresentation A X) :
    Subobject X ≃o Set.Icc p.bottom p.top where
  toFun Y := ⟨p.lift Y, p.bottom_le_lift Y, p.lift_le_top Y⟩
  invFun W := p.desc W.1
  left_inv := p.desc_lift
  right_inv W := Subtype.ext (p.lift_desc W.2.1 W.2.2)
  map_rel_iff' {Y₁ Y₂} :=
    ⟨fun h ↦ by simpa [p.desc_lift] using p.desc_monotone h, fun h ↦ p.lift_monotone h⟩

@[simp]
lemma subobjectOrderIso_apply_val (p : SubquotientPresentation A X) (Y : Subobject X) :
    (p.subobjectOrderIso Y : Subobject A) = p.lift Y := by rfl

@[simp]
lemma subobjectOrderIso_symm_apply (p : SubquotientPresentation A X)
    (W : Set.Icc p.bottom p.top) :
    p.subobjectOrderIso.symm W = p.desc W.1 := by rfl

@[simp]
lemma lift_le_lift_iff (p : SubquotientPresentation A X) {Y₁ Y₂ : Subobject X} :
    p.lift Y₁ ≤ p.lift Y₂ ↔ Y₁ ≤ Y₂ :=
  p.subobjectOrderIso.le_iff_le

lemma lift_injective (p : SubquotientPresentation A X) : Function.Injective p.lift :=
  fun _ _ h ↦ p.subobjectOrderIso.injective (Subtype.ext h)

@[simp]
lemma lift_eq_lift_iff (p : SubquotientPresentation A X) {Y₁ Y₂ : Subobject X} :
    p.lift Y₁ = p.lift Y₂ ↔ Y₁ = Y₂ :=
  p.lift_injective.eq_iff

private lemma lift_eq_of_eq (p : SubquotientPresentation A X) (Z : Subobject A) (hZ : p.top = Z)
    (π : (Z : C) ⟶ X) (hπ : p.proj = (Subobject.isoOfEq _ _ hZ).hom ≫ π) (S : Subobject X) :
    p.lift S = (Subobject.map Z.arrow).obj ((Subobject.pullback π).obj S) := by
  subst hZ
  simp [lift, hπ]

@[simp]
lemma refl_lift (A : C) (S : Subobject A) : (refl A).lift S = S := by
  rw [lift_eq_of_eq (refl A) ⊤ rfl (⊤ : Subobject A).arrow (by simp),
    ← Subobject.inf_eq_map_pullback, top_inf_eq]

@[simp]
lemma refl_desc (A : C) (S : Subobject A) : (refl A).desc S = S := by
  simpa [refl_lift] using (refl A).desc_lift S

@[simp]
lemma lift_transIso (p : SubquotientPresentation A X) (e : X ≅ Y) (S : Subobject Y) :
    (p.transIso e).lift S = p.lift ((Subobject.pullback e.hom).obj S) := by
  rw [lift_eq_of_eq (p.transIso e) p.top rfl (p.proj ≫ e.hom) (by simp),
    Subobject.pullback_comp, lift]

/-- For a nonempty set `s` of subobjects of `X`, `p.lift Y` is the greatest lower bound of
`p.lift '' s` in `Subobject A` if and only if `Y` is the greatest lower bound of `s`. -/
theorem isGLB_lift_image_iff (p : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {Y : Subobject X} :
    IsGLB (p.lift '' s) (p.lift Y) ↔ IsGLB s Y := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ⟨?_, ?_⟩⟩
  · intro Z hZ
    exact (p.lift_le_lift_iff).mp (h.1 ⟨Z, hZ, rfl⟩)
  · intro W hW
    refine (p.lift_le_lift_iff).mp (h.2 ?_)
    rintro _ ⟨Z, hZ, rfl⟩
    exact p.lift_mono (hW hZ)
  · rintro _ ⟨Z, hZ, rfl⟩
    exact p.lift_mono (h.1 hZ)
  · intro W hW
    obtain ⟨Z₀, hZ₀⟩ := hs
    have hW_top : W ≤ p.top := (hW ⟨Z₀, hZ₀, rfl⟩).trans (p.lift_le_top Z₀)
    have hW'_top : W ⊔ p.bottom ≤ p.top := sup_le hW_top p.le
    have hdesc : p.desc (W ⊔ p.bottom) ≤ Y := h.2 fun Z hZ ↦ by
      have hle : W ⊔ p.bottom ≤ p.lift Z := sup_le (hW ⟨Z, hZ, rfl⟩) (p.bottom_le_lift Z)
      simpa [p.desc_lift] using p.desc_mono hle
    exact le_sup_left.trans <| (p.lift_desc le_sup_right hW'_top).symm.le.trans
      (p.lift_mono hdesc)

/-- For a nonempty set `s` of subobjects of `X`, any greatest lower bound of `p.lift '' s` in
`Subobject A` lies in `[p.bottom, p.top]` and descends to a greatest lower bound of `s`. -/
theorem isGLB_desc_of_isGLB_lift_image (p : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {W : Subobject A} (hW : IsGLB (p.lift '' s) W) :
    IsGLB s (p.desc W) ∧ p.lift (p.desc W) = W := by
  obtain ⟨Z₀, hZ₀⟩ := hs
  have hB : p.bottom ≤ W := hW.2 (by rintro _ ⟨Z, _, rfl⟩; exact p.bottom_le_lift Z)
  have hZ : W ≤ p.top := (hW.1 ⟨Z₀, hZ₀, rfl⟩).trans (p.lift_le_top Z₀)
  have hEq : p.lift (p.desc W) = W := p.lift_desc hB hZ
  exact ⟨(p.isGLB_lift_image_iff ⟨Z₀, hZ₀⟩).mp (hEq.symm ▸ hW), hEq⟩

/-- For a nonempty set `s` of subobjects of `X`, `p.lift Y` is the least upper bound of
`p.lift '' s` in `Subobject A` if and only if `Y` is the least upper bound of `s`. -/
theorem isLUB_lift_image_iff (p : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {Y : Subobject X} :
    IsLUB (p.lift '' s) (p.lift Y) ↔ IsLUB s Y := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ⟨?_, ?_⟩⟩
  · intro Z hZ
    exact (p.lift_le_lift_iff).mp (h.1 ⟨Z, hZ, rfl⟩)
  · intro W hW
    refine (p.lift_le_lift_iff).mp (h.2 ?_)
    rintro _ ⟨Z, hZ, rfl⟩
    exact p.lift_mono (hW hZ)
  · rintro _ ⟨Z, hZ, rfl⟩
    exact p.lift_mono (h.1 hZ)
  · intro W hW
    obtain ⟨Z₀, hZ₀⟩ := hs
    have hB_W : p.bottom ≤ W := (p.bottom_le_lift Z₀).trans (hW ⟨Z₀, hZ₀, rfl⟩)
    have hB_W' : p.bottom ≤ W ⊓ p.top := le_inf hB_W p.le
    have hdesc : Y ≤ p.desc (W ⊓ p.top) := h.2 fun Z hZ ↦ by
      have hle : p.lift Z ≤ W ⊓ p.top := le_inf (hW ⟨Z, hZ, rfl⟩) (p.lift_le_top Z)
      simpa [p.desc_lift] using p.desc_mono hle
    exact (p.lift_mono hdesc).trans <|
      (p.lift_desc hB_W' inf_le_right).le.trans inf_le_left

/-- For a nonempty set `s` of subobjects of `X`, any least upper bound of `p.lift '' s` in
`Subobject A` lies in `[p.bottom, p.top]` and descends to a least upper bound of `s`. -/
theorem isLUB_desc_of_isLUB_lift_image (p : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {W : Subobject A} (hW : IsLUB (p.lift '' s) W) :
    IsLUB s (p.desc W) ∧ p.lift (p.desc W) = W := by
  obtain ⟨Z₀, hZ₀⟩ := hs
  have hB : p.bottom ≤ W := (p.bottom_le_lift Z₀).trans (hW.1 ⟨Z₀, hZ₀, rfl⟩)
  have hZ : W ≤ p.top := hW.2 (by rintro _ ⟨Z, _, rfl⟩; exact p.lift_le_top Z)
  have hEq : p.lift (p.desc W) = W := p.lift_desc hB hZ
  exact ⟨(p.isLUB_lift_image_iff ⟨Z₀, hZ₀⟩).mp (hEq.symm ▸ hW), hEq⟩

/-- The presented object `X` is zero if and only if `p.bottom = p.top`. -/
theorem isZero_iff_bottom_eq_top (p : SubquotientPresentation A X) :
    IsZero X ↔ p.bottom = p.top :=
  ⟨fun h ↦ (Subobject.isZero_cokernel_ofLE_iff p.le).mp (h.of_iso p.iso),
    fun h ↦ ((Subobject.isZero_cokernel_ofLE_iff p.le).mpr h).of_iso p.iso.symm⟩

private lemma lift_eq_mk (p : SubquotientPresentation A X) (K : Subobject X) :
    p.lift K = Subobject.mk (((Subobject.pullback p.proj).obj K).arrow ≫ p.top.arrow) := by
  rw [lift]
  nth_rw 1 [← Subobject.mk_arrow ((Subobject.pullback p.proj).obj K)]
  rw [Subobject.map_mk]

private noncomputable def liftIsoPullback (p : SubquotientPresentation A X) (K : Subobject X) :
    (p.lift K : C) ≅ ((Subobject.pullback p.proj).obj K : C) :=
  Subobject.isoOfEq _ _ (p.lift_eq_mk K) ≪≫
    Subobject.underlyingIso (((Subobject.pullback p.proj).obj K).arrow ≫ p.top.arrow)

private lemma liftIsoPullback_hom_comp_arrow (p : SubquotientPresentation A X) (K : Subobject X) :
    (p.liftIsoPullback K).hom ≫ ((Subobject.pullback p.proj).obj K).arrow =
      Subobject.ofLE (p.lift K) p.top (p.lift_le_top K) := by
  rw [← cancel_mono p.top.arrow, Category.assoc]
  simp [liftIsoPullback]

/-- The canonical epimorphism `(p.lift K : C) ⟶ (K : C)` restricting `p.proj` to the preimage of
a subobject `K` of `X`. -/
noncomputable def liftProj (p : SubquotientPresentation A X) (K : Subobject X) :
    (p.lift K : C) ⟶ (K : C) :=
  (p.liftIsoPullback K).hom ≫ Subobject.pullbackπ p.proj K

instance (p : SubquotientPresentation A X) (K : Subobject X) : Epi (p.liftProj K) := by
  dsimp [liftProj]
  infer_instance

@[reassoc (attr := simp)]
lemma liftProj_comp_arrow (p : SubquotientPresentation A X) (K : Subobject X) :
    p.liftProj K ≫ K.arrow = Subobject.ofLE (p.lift K) p.top (p.lift_le_top K) ≫ p.proj := by
  dsimp [liftProj]
  rw [Category.assoc, (Subobject.isPullback p.proj K).w,
    reassoc_of% (p.liftIsoPullback_hom_comp_arrow K)]

lemma isPullback_liftProj (p : SubquotientPresentation A X) (K : Subobject X) :
    IsPullback (p.liftProj K) (Subobject.ofLE (p.lift K) p.top (p.lift_le_top K))
      K.arrow p.proj :=
  (Subobject.isPullback p.proj K).of_iso (p.liftIsoPullback K).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp [liftProj])
    (by rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.eq_inv_comp,
      liftIsoPullback_hom_comp_arrow])
    (by simp) (by simp)

@[reassoc (attr := simp)]
lemma ofLE_comp_liftProj (p : SubquotientPresentation A X) {I K : Subobject X} (hIK : I ≤ K) :
    Subobject.ofLE (p.lift I) (p.lift K) (p.lift_mono hIK) ≫ p.liftProj K =
      p.liftProj I ≫ Subobject.ofLE I K hIK := by
  rw [← cancel_mono K.arrow]
  simp

/-- The canonical isomorphism identifying `p.lift K / p.lift I` with `K / I`. -/
noncomputable def subquotientIso (p : SubquotientPresentation A X) {I K : Subobject X}
    (hIK : I ≤ K) :
    cokernel (Subobject.ofLE (p.lift I) (p.lift K) (p.lift_mono hIK)) ≅
      cokernel (Subobject.ofLE I K hIK) := by
  have hcomp : Subobject.ofLE (p.lift I) (p.lift K) (p.lift_mono hIK) ≫
      (p.liftProj K ≫ cokernel.π (Subobject.ofLE I K hIK)) = 0 := by
    rw [ofLE_comp_liftProj_assoc p hIK, cokernel.condition, comp_zero]
  have hker : IsLimit (KernelFork.ofι
      (Subobject.ofLE (p.lift I) (p.lift K) (p.lift_mono hIK)) hcomp) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W} g hg ↦ ?_) (fun {W} g hg ↦ ?_)
      (fun {W} g hg m hm ↦ ?_)
    · have hg0 : (g ≫ p.liftProj K) ≫ cokernel.π (Subobject.ofLE I K hIK) = 0 := by
        simpa [Category.assoc] using hg
      let u : W ⟶ (I : C) := Abelian.monoLift (Subobject.ofLE I K hIK) (g ≫ p.liftProj K) hg0
      have hu : u ≫ I.arrow =
          (g ≫ Subobject.ofLE (p.lift K) p.top (p.lift_le_top K)) ≫ p.proj := by
        calc
          u ≫ I.arrow = (u ≫ Subobject.ofLE I K hIK) ≫ K.arrow := by simp
          _ = g ≫ p.liftProj K ≫ K.arrow := by
                rw [Abelian.monoLift_comp, Category.assoc]
          _ = (g ≫ Subobject.ofLE (p.lift K) p.top (p.lift_le_top K)) ≫ p.proj := by
                rw [liftProj_comp_arrow, Category.assoc]
      have hfacPull : ((Subobject.pullback p.proj).obj I).Factors
          (g ≫ Subobject.ofLE (p.lift K) p.top (p.lift_le_top K)) :=
        (pullback_factors_iff p.proj I _).mpr (hu ▸ Subobject.factors_comp_arrow u)
      have hinv : (p.liftIsoPullback I).inv ≫ (p.lift I).arrow =
          ((Subobject.pullback p.proj).obj I).arrow ≫ p.top.arrow := by
        rw [Iso.inv_comp_eq, ← Subobject.ofLE_arrow (p.lift_le_top I),
          ← p.liftIsoPullback_hom_comp_arrow I, Category.assoc]
      have hEq : (((Subobject.pullback p.proj).obj I).factorThru _ hfacPull ≫
          (p.liftIsoPullback I).inv) ≫ (p.lift I).arrow = g ≫ (p.lift K).arrow := by
        rw [Category.assoc, hinv, Subobject.factorThru_arrow_assoc, Category.assoc,
          Subobject.ofLE_arrow]
      exact (p.lift I).factorThru (g ≫ (p.lift K).arrow) (hEq ▸ Subobject.factors_comp_arrow _)
    · rw [← cancel_mono (p.lift K).arrow]
      simp
    · rw [← cancel_mono (Subobject.ofLE (p.lift I) (p.lift K) (p.lift_mono hIK)),
        ← cancel_mono (p.lift K).arrow]
      simpa [Category.assoc] using congrArg (· ≫ (p.lift K).arrow) hm
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (Subobject.ofLE (p.lift I) (p.lift K) (p.lift_mono hIK)))
    (Abelian.epiIsCokernelOfKernel _ hker)

/-- Given subobjects `I ≤ K` of `X`, the presentation of `cokernel (Subobject.ofLE I K hIK)` inside
the ambient object `A` by `(p.lift I, p.lift K)`. -/
noncomputable abbrev subquotient (p : SubquotientPresentation A X) {I K : Subobject X}
    (hIK : I ≤ K) :
    SubquotientPresentation A (cokernel (Subobject.ofLE I K hIK)) where
  bottom := p.lift I
  top := p.lift K
  le := p.lift_mono hIK
  iso := p.subquotientIso hIK

@[reassoc, simp]
lemma subquotient_proj (p : SubquotientPresentation A X) {I K : Subobject X} (hIK : I ≤ K) :
    (p.subquotient hIK).proj = p.liftProj K ≫ cokernel.π (Subobject.ofLE I K hIK) := by
  dsimp [proj, subquotient, subquotientIso]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (Subobject.ofLE (p.lift I) (p.lift K) (p.lift_mono hIK))) _
    WalkingParallelPair.one

/-- Lifting a subobject along `p.subquotient hIK` agrees with lifting first along `ofLE I K hIK`
and then along `p`. -/
theorem lift_subquotient (p : SubquotientPresentation A X) {I K : Subobject X} (hIK : I ≤ K)
    (S : Subobject (cokernel (Subobject.ofLE I K hIK))) :
    (p.subquotient hIK).lift S = p.lift ((ofLE I K hIK).lift S) := by
  have hpb := p.isPullback_liftProj K
  have hmp : (Subobject.map (Subobject.ofLE (p.lift K) p.top (p.lift_le_top K))).obj
      ((Subobject.pullback (p.liftProj K)).obj
        ((Subobject.pullback (cokernel.π (Subobject.ofLE I K hIK))).obj S)) =
      (Subobject.pullback p.proj).obj
        ((Subobject.map K.arrow).obj
          ((Subobject.pullback (cokernel.π (Subobject.ofLE I K hIK))).obj S)) :=
    Subobject.map_pullback hpb.w hpb.isLimit _
  rw [lift_eq_of_eq (p.subquotient hIK) (p.lift K) rfl
      (p.liftProj K ≫ cokernel.π (Subobject.ofLE I K hIK)) (by simp),
    Subobject.pullback_comp]
  have hmap : ∀ T : Subobject (p.lift K : C),
      (Subobject.map (p.lift K).arrow).obj T =
        (Subobject.map p.top.arrow).obj
          ((Subobject.map (Subobject.ofLE (p.lift K) p.top (p.lift_le_top K))).obj T) := fun T ↦ by
    rw [← Subobject.map_comp]
    simp only [Subobject.ofLE_arrow]
  rw [hmap, hmp, lift_eq_of_eq (ofLE I K hIK) K rfl (cokernel.π (Subobject.ofLE I K hIK)) (by simp),
    lift]

/-- Two-step naturality of subquotient presentations: forming the subquotient of `p.subquotient hIK`
for `I'' ≤ K''` produces the same presentation as forming the single subquotient of `p` for
`I' = (ofLE I K hIK).lift I'' ≤ K' = (ofLE I K hIK).lift K''` and transporting along the
canonical isomorphism of the two quotients. -/
theorem subquotient_subquotient (p : SubquotientPresentation A X) {I K : Subobject X}
    (hIK : I ≤ K) {I'' K'' : Subobject (cokernel (Subobject.ofLE I K hIK))} (h'' : I'' ≤ K'') :
    (p.subquotient hIK).subquotient h'' =
      (p.subquotient ((ofLE I K hIK).lift_mono h'')).transIso
        ((ofLE I K hIK).subquotient h'').iso := by
  set q := ofLE I K hIK
  have hB : ((p.subquotient hIK).subquotient h'').bottom =
      (p.subquotient (q.lift_mono h'')).bottom := p.lift_subquotient hIK I''
  have hZ : ((p.subquotient hIK).subquotient h'').top =
      (p.subquotient (q.lift_mono h'')).top := p.lift_subquotient hIK K''
  refine ext hB hZ ?_
  have hproj_q : cokernel.π (Subobject.ofLE (q.lift I'') (q.lift K'') (q.lift_mono h'')) ≫
      (q.subquotient h'').iso.hom =
      q.liftProj K'' ≫ cokernel.π (Subobject.ofLE I'' K'' h'') := by
    simpa [proj] using q.subquotient_proj h''
  rw [subquotient_proj, transIso_proj, subquotient_proj_assoc, hproj_q, ← Category.assoc,
    ← Category.assoc]
  congr 1
  rw [← cancel_mono K''.arrow]
  simp only [Category.assoc, liftProj_comp_arrow, subquotient_proj]
  rw [← ofLE_comp_liftProj_assoc p (q.lift_le_top K''), ← Category.assoc]
  simp [q]

/-- Two-step naturality starting directly from a chain `I ≤ I' ≤ K' ≤ K` in `Subobject X`: the
subquotient presentation of `p` at `(I', K')` agrees with the two-step presentation through
`ofLE I K` up to the canonical isomorphism of quotients. -/
theorem subquotient_eq_subquotient_subquotient (p : SubquotientPresentation A X)
    {I I' K' K : Subobject X} (hII' : I ≤ I') (hI'K' : I' ≤ K') (hK'K : K' ≤ K) :
    ((p.subquotient (hII'.trans (hI'K'.trans hK'K))).subquotient
      ((ofLE I K (hII'.trans (hI'K'.trans hK'K))).desc_mono hI'K')).transIso
      (isoOfEq
        (p := (ofLE I K (hII'.trans (hI'K'.trans hK'K))).subquotient
          ((ofLE I K (hII'.trans (hI'K'.trans hK'K))).desc_mono hI'K'))
        (q := ofLE I' K' hI'K')
        ((ofLE I K (hII'.trans (hI'K'.trans hK'K))).lift_desc hII' (hI'K'.trans hK'K))
        ((ofLE I K (hII'.trans (hI'K'.trans hK'K))).lift_desc (hII'.trans hI'K') hK'K)) =
      p.subquotient hI'K' := by
  set hIK := hII'.trans (hI'K'.trans hK'K)
  set q := ofLE I K hIK
  have hdesc : q.desc I' ≤ q.desc K' := q.desc_mono hI'K'
  have hI' : q.lift (q.desc I') = I' := q.lift_desc hII' (hI'K'.trans hK'K)
  have hK' : q.lift (q.desc K') = K' := q.lift_desc (hII'.trans hI'K') hK'K
  rw [subquotient_subquotient, transIso_trans]
  have hB : p.lift (q.lift (q.desc I')) = p.lift I' := congrArg p.lift hI'
  have hZ : p.lift (q.lift (q.desc K')) = p.lift K' := congrArg p.lift hK'
  refine ext hB hZ ?_
  have hq : cokernel.π (Subobject.ofLE (q.lift (q.desc I')) (q.lift (q.desc K'))
      (q.lift_mono hdesc)) ≫
      (q.subquotient hdesc).iso.hom ≫
      (isoOfEq (p := q.subquotient hdesc) (q := ofLE I' K' hI'K') hI' hK').hom =
      (Subobject.isoOfEq _ _ hK').hom ≫ cokernel.π (Subobject.ofLE I' K' hI'K') := by
    have := proj_comp_isoOfEq_hom (p := q.subquotient hdesc) (q := ofLE I' K' hI'K') hI' hK'
    simpa [proj] using this
  rw [transIso_proj, subquotient_proj_assoc, Iso.trans_hom, hq, subquotient_proj,
    ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono K'.arrow]
  simp [q]

/-- If `f : A ⟶ A'` induces `p.map q f hB hZ : X ⟶ X'`, and `p.map q f hB hZ` maps `S` into `S'`,
then `f` maps `p.lift S` into `q.lift S'`. -/
lemma factors_lift_of_factors_map (p : SubquotientPresentation A X)
    (q : SubquotientPresentation A' X') (f : A ⟶ A')
    (hB : q.bottom.Factors (p.bottom.arrow ≫ f)) (hZ : q.top.Factors (p.top.arrow ≫ f))
    {S : Subobject X} {S' : Subobject X'}
    (hS : S'.Factors (S.arrow ≫ p.map q f hB hZ)) :
    (q.lift S').Factors ((p.lift S).arrow ≫ f) := by
  let u : (p.lift S : C) ⟶ (q.top : C) :=
    Subobject.ofLE (p.lift S) p.top (p.lift_le_top S) ≫ q.top.factorThru (p.top.arrow ≫ f) hZ
  have hu_arrow : u ≫ q.top.arrow = (p.lift S).arrow ≫ f := by
    simp [u]
  have hu_proj : u ≫ q.proj = p.liftProj S ≫ (S.arrow ≫ p.map q f hB hZ) := by
    dsimp [u]
    rw [Category.assoc, ← proj_comp_map, ← Category.assoc, ← liftProj_comp_arrow, Category.assoc]
  have hpull : ((Subobject.pullback q.proj).obj S').Factors u :=
    (pullback_factors_iff q.proj S' u).mpr
      (hu_proj ▸ Subobject.factors_of_factors_right (p.liftProj S) hS)
  have hinv : (q.liftIsoPullback S').inv ≫ (q.lift S').arrow =
      ((Subobject.pullback q.proj).obj S').arrow ≫ q.top.arrow := by
    rw [Iso.inv_comp_eq, ← Subobject.ofLE_arrow (q.lift_le_top S'),
      ← q.liftIsoPullback_hom_comp_arrow S', Category.assoc]
  have hEq : (((Subobject.pullback q.proj).obj S').factorThru u hpull ≫
      (q.liftIsoPullback S').inv) ≫ (q.lift S').arrow = (p.lift S).arrow ≫ f := by
    rw [Category.assoc, hinv, Subobject.factorThru_arrow_assoc, hu_arrow]
  exact hEq ▸ Subobject.factors_comp_arrow _

/-- Compatibility of `map` with `subquotient`: the morphism induced by `f : A ⟶ A'` between
`p.subquotient hIK` and `q.subquotient hI'K'` equals the morphism induced by `p.map q f hB hZ`
between `ofLE I K hIK` and `ofLE I' K' hI'K'`. -/
theorem map_subquotient (p : SubquotientPresentation A X)
    (q : SubquotientPresentation A' X') (f : A ⟶ A')
    (hB : q.bottom.Factors (p.bottom.arrow ≫ f)) (hZ : q.top.Factors (p.top.arrow ≫ f))
    {I K : Subobject X} (hIK : I ≤ K) {I' K' : Subobject X'} (hI'K' : I' ≤ K')
    (hI : I'.Factors (I.arrow ≫ p.map q f hB hZ))
    (hK : K'.Factors (K.arrow ≫ p.map q f hB hZ)) :
    (p.subquotient hIK).map (q.subquotient hI'K') f
        (p.factors_lift_of_factors_map q f hB hZ hI)
        (p.factors_lift_of_factors_map q f hB hZ hK) =
      (ofLE I K hIK).map (ofLE I' K' hI'K') (p.map q f hB hZ) hI hK := by
  apply map_eq_of_proj_comp
  have hpi : cokernel.π (Subobject.ofLE I K hIK) ≫
      (ofLE I K hIK).map (ofLE I' K' hI'K') (p.map q f hB hZ) hI hK =
      K'.factorThru (K.arrow ≫ p.map q f hB hZ) hK ≫ cokernel.π (Subobject.ofLE I' K' hI'K') := by
    simpa [ofLE_proj] using
      proj_comp_map (ofLE I K hIK) (ofLE I' K' hI'K') (p.map q f hB hZ) hI hK
  rw [subquotient_proj_assoc, hpi, subquotient_proj, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono K'.arrow]
  simp only [Category.assoc, Subobject.factorThru_arrow, liftProj_comp_arrow]
  have hfac : (q.lift K').factorThru ((p.lift K).arrow ≫ f)
        (p.factors_lift_of_factors_map q f hB hZ hK) ≫
      Subobject.ofLE (q.lift K') q.top (q.lift_le_top K') =
      Subobject.ofLE (p.lift K) p.top (p.lift_le_top K) ≫
        q.top.factorThru (p.top.arrow ≫ f) hZ := by
    rw [← cancel_mono q.top.arrow]
    simp
  rw [reassoc_of% hfac, ← proj_comp_map p q f hB hZ]
  simp

/-- The morphism induced by `f : A ⟶ A'` between identity presentations `refl A` and `refl A'`
is `f` itself. -/
lemma map_refl (f : A ⟶ A')
    (hB : (refl A').bottom.Factors ((refl A).bottom.arrow ≫ f))
    (hZ : (refl A').top.Factors ((refl A).top.arrow ≫ f)) :
    (refl A).map (refl A') f hB hZ = f := by
  apply map_eq_of_proj_comp
  simp [refl_proj]

/-- Any presentation `p` equals `(ofLE p.bottom p.top p.le).transIso p.iso`. -/
lemma ofLE_transIso_eq_self (p : SubquotientPresentation A X) :
    (ofLE p.bottom p.top p.le).transIso p.iso = p := by
  refine ext rfl rfl ?_
  simp [proj]

/-- Compose a subquotient presentation `p` of `X` inside `A` with a subquotient presentation `q`
of `Y` inside `X`, obtaining a subquotient presentation of `Y` inside `A` with bottom
`p.lift q.bottom` and top `p.lift q.top`. -/
noncomputable abbrev comp {Y : C} (p : SubquotientPresentation A X)
    (q : SubquotientPresentation X Y) : SubquotientPresentation A Y :=
  (p.subquotient q.le).transIso q.iso

lemma comp_proj {Y : C} (p : SubquotientPresentation A X) (q : SubquotientPresentation X Y) :
    (p.comp q).proj = p.liftProj q.top ≫ q.proj := by
  rw [transIso_proj, subquotient_proj_assoc, proj]

/-- Lifting a subobject along a composite presentation `p.comp q` lifts first along `q` and then
along `p`. -/
lemma lift_comp {Y : C} (p : SubquotientPresentation A X) (q : SubquotientPresentation X Y)
    (S : Subobject Y) :
    (p.comp q).lift S = p.lift (q.lift S) := by
  rw [lift_transIso, lift_subquotient]
  congr 1
  rw [← lift_transIso, ofLE_transIso_eq_self]

/-- Composing a presentation with the identity presentation `refl X` returns the original
presentation. -/
lemma comp_refl (p : SubquotientPresentation A X) :
    p.comp (refl X) = p := by
  refine ext p.lift_bot p.lift_top ?_
  rw [comp_proj, refl_proj, liftProj_comp_arrow]
  rfl

/-- Transporting a composite presentation along an isomorphism `e` on the target is the same as
transporting the second factor along `e`. -/
lemma comp_transIso {Y Z : C} (p : SubquotientPresentation A X)
    (q : SubquotientPresentation X Y) (e : Y ≅ Z) :
    (p.comp q).transIso e = p.comp (q.transIso e) :=
  transIso_trans (p.subquotient q.le) q.iso e

/-- Taking a subquotient of a composite presentation `p.comp q` is the same as composing `p` with
the subquotient of `q`. -/
lemma comp_subquotient {Y : C} (p : SubquotientPresentation A X)
    (q : SubquotientPresentation X Y) {I K : Subobject Y} (hIK : I ≤ K) :
    (p.comp q).subquotient hIK = p.comp (q.subquotient hIK) := by
  refine ext (p.lift_comp q I) (p.lift_comp q K) ?_
  have hlhs : ((p.comp q).subquotient hIK).proj =
      (p.comp q).liftProj K ≫ cokernel.π (Subobject.ofLE I K hIK) :=
    (p.comp q).subquotient_proj hIK
  have hrhs : (p.comp (q.subquotient hIK)).proj =
      (p.liftProj (q.lift K) ≫ q.liftProj K) ≫ cokernel.π (Subobject.ofLE I K hIK) := by
    rw [comp_proj, q.subquotient_proj hIK, Category.assoc]
  rw [hlhs, hrhs, ← Category.assoc]
  congr 1
  rw [← cancel_mono K.arrow]
  have h1 : (p.comp q).liftProj K ≫ K.arrow =
      (Subobject.ofLE ((p.comp q).lift K) (p.lift q.top) ((p.comp q).lift_le_top K) ≫
        p.liftProj q.top) ≫ q.proj := by
    rw [liftProj_comp_arrow, comp_proj, Category.assoc]
  have h2 : ((Subobject.isoOfEq ((p.comp q).lift K) (p.lift (q.lift K)) (p.lift_comp q K)).hom ≫
        p.liftProj (q.lift K) ≫ q.liftProj K) ≫ K.arrow =
      ((Subobject.isoOfEq ((p.comp q).lift K) (p.lift (q.lift K)) (p.lift_comp q K)).hom ≫
        Subobject.ofLE (p.lift (q.lift K)) (p.lift q.top) (p.lift_mono (q.lift_le_top K))) ≫
        p.liftProj q.top ≫ q.proj := by
    simp only [Category.assoc, liftProj_comp_arrow, ← ofLE_comp_liftProj_assoc]
  rw [h1, h2, Category.assoc]
  congr 1
  rw [← cancel_mono (p.lift q.top).arrow]
  simp

/-- Composition of subquotient presentations is associative. -/
lemma comp_assoc {Y Z : C} (p : SubquotientPresentation A X)
    (q : SubquotientPresentation X Y) (r : SubquotientPresentation Y Z) :
    (p.comp q).comp r = p.comp (q.comp r) :=
  (congrArg (·.transIso r.iso) (p.comp_subquotient q r.le)).trans
    (p.comp_transIso (q.subquotient r.le) r.iso)

/-- Functoriality of composition of subquotient presentations: the morphism induced by `f : A ⟶ A'`
between `p.comp q` and `p'.comp q'` equals the morphism induced by `p.map p' f hB hZ` between `q`
and `q'`. -/
theorem comp_map {Y Y' : C} (p : SubquotientPresentation A X)
    (p' : SubquotientPresentation A' X') (q : SubquotientPresentation X Y)
    (q' : SubquotientPresentation X' Y') (f : A ⟶ A')
    (hB : p'.bottom.Factors (p.bottom.arrow ≫ f)) (hZ : p'.top.Factors (p.top.arrow ≫ f))
    (hBq : q'.bottom.Factors (q.bottom.arrow ≫ p.map p' f hB hZ))
    (hZq : q'.top.Factors (q.top.arrow ≫ p.map p' f hB hZ)) :
    (p.comp q).map (p'.comp q') f
        (p.factors_lift_of_factors_map p' f hB hZ hBq)
        (p.factors_lift_of_factors_map p' f hB hZ hZq) =
      q.map q' (p.map p' f hB hZ) hBq hZq := by
  have h1 := map_transIso_left (p.subquotient q.le) (p'.comp q') q.iso f
    (p.factors_lift_of_factors_map p' f hB hZ hBq)
    (p.factors_lift_of_factors_map p' f hB hZ hZq)
  have h2 := map_transIso_right (p.subquotient q.le) (p'.subquotient q'.le) q'.iso f
    (p.factors_lift_of_factors_map p' f hB hZ hBq)
    (p.factors_lift_of_factors_map p' f hB hZ hZq)
  have h3 := map_subquotient p p' f hB hZ q.le q'.le hBq hZq
  rw [h1, h2, h3]
  symm
  apply map_eq_of_proj_comp
  rw [proj, Category.assoc, Iso.hom_inv_id_assoc]
  have hpi := proj_comp_map (ofLE q.bottom q.top q.le) (ofLE q'.bottom q'.top q'.le)
    (p.map p' f hB hZ) hBq hZq
  simp only [ofLE_proj] at hpi
  rw [reassoc_of% hpi, proj]

end Abelian

end SubquotientPresentation

end TauCeti
