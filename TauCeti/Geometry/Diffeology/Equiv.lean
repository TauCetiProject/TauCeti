/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeology.Induced
public import TauCeti.Geometry.Diffeology.Prod

/-!
# Diffeomorphisms of diffeological spaces

This file defines `TauCeti.Diffeology.DSmoothEquiv X Y`, the type of bundled diffeomorphisms
between diffeological spaces `X` and `Y`: bijections that are smooth in both directions.

Every diffeological diffeomorphism is both an induction and a subduction, preserves plots and
smoothness under composition on either side, and induces a homeomorphism when both spaces carry
topologies compatible with their D-topologies (`TauCeti.Diffeology.DSmoothEquiv.toHomeomorph`).
Conversely, an induction defines a diffeomorphism onto its range with the subspace diffeology
(`TauCeti.Diffeology.IsInduction.toDSmoothEquivRange`).

## Main declarations

* `TauCeti.Diffeology.DSmoothEquiv`: bundled diffeomorphisms of diffeological spaces.
* `TauCeti.Diffeology.DSmoothEquiv.refl`, `TauCeti.Diffeology.DSmoothEquiv.symm`,
  `TauCeti.Diffeology.DSmoothEquiv.trans`: identity, inverse, and composition.
* `TauCeti.Diffeology.DSmoothEquiv.prodCongr`, `TauCeti.Diffeology.DSmoothEquiv.prodComm`,
  `TauCeti.Diffeology.DSmoothEquiv.prodAssoc`, `TauCeti.Diffeology.DSmoothEquiv.prodUnique`,
  `TauCeti.Diffeology.DSmoothEquiv.uniqueProd`: product congruences, associator/commutator, and
  unit laws for `[Unique _]` factors.
* `TauCeti.Diffeology.DSmoothEquiv.instHomeomorphClass`,
  `TauCeti.Diffeology.DSmoothEquiv.toHomeomorph`: `HomeomorphClass` instance and underlying
  homeomorphism for spaces with compatible D-topologies.
* `TauCeti.Diffeology.IsInduction.toDSmoothEquivRange`: diffeomorphism from the source of an
  induction onto its range.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Chapter 1, Articles 1.15–1.17 and 1.29.
-/

public noncomputable section

open Function Set _root_.Diffeology
open scoped Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

/-- A diffeomorphism between diffeological spaces: an equivalence whose forward and inverse maps
are both diffeologically smooth. -/
structure DSmoothEquiv (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y]
    extends X ≃ Y where
  /-- The forward map is smooth. -/
  dSmooth_toFun : DSmooth toFun
  /-- The inverse map is smooth. -/
  dSmooth_invFun : DSmooth invFun

namespace DSmoothEquiv

variable {X Y Z Q R : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]
  [DiffeologicalSpace Q] [DiffeologicalSpace R]

instance instEquivLike : EquivLike (DSmoothEquiv X Y) X Y where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e₁ e₂ h _ := by
    cases e₁ with | mk f₁ _ _ => cases e₂ with | mk f₂ _ _ =>
    congr; exact Equiv.coe_fn_injective h

/-- The coercion of `toEquiv` agrees with the `EquivLike` coercion. -/
@[simp, grind =] theorem coe_toEquiv (e : DSmoothEquiv X Y) : ⇑e.toEquiv = ⇑e := (rfl)

/-- `toEquiv` is injective. -/
theorem toEquiv_injective : Injective (toEquiv : DSmoothEquiv X Y → (X ≃ Y)) :=
  fun _ _ h ↦ DFunLike.ext _ _ (Equiv.ext_iff.mp h)

@[ext] theorem ext {e₁ e₂ : DSmoothEquiv X Y} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
  DFunLike.ext e₁ e₂ h

@[simp, grind =] theorem coe_mk (e : X ≃ Y) (hf : DSmooth e) (hi : DSmooth e.symm) :
    ⇑(mk e hf hi) = ⇑e := (rfl)
@[simp, grind =] theorem mk_apply (e : X ≃ Y) (hf : DSmooth e) (hi : DSmooth e.symm) (x : X) :
    mk e hf hi x = e x := (rfl)

/-- A diffeological diffeomorphism is smooth. -/
@[fun_prop] protected theorem dSmooth (e : DSmoothEquiv X Y) : DSmooth e := e.dSmooth_toFun

/-- The identity diffeomorphism of a diffeological space. -/
protected def refl (X : Type*) [DiffeologicalSpace X] : DSmoothEquiv X X :=
  ⟨Equiv.refl X, dSmooth_id, dSmooth_id⟩

@[simp, grind =] theorem coe_refl : ⇑(DSmoothEquiv.refl X) = id := (rfl)
@[simp, grind =] theorem refl_apply (x : X) : DSmoothEquiv.refl X x = x := (rfl)
@[simp] theorem toEquiv_refl : (DSmoothEquiv.refl X).toEquiv = Equiv.refl X := (rfl)

instance : Inhabited (DSmoothEquiv X X) := ⟨DSmoothEquiv.refl X⟩

/-- The inverse of a diffeological diffeomorphism. -/
@[symm] protected def symm (e : DSmoothEquiv X Y) : DSmoothEquiv Y X :=
  ⟨e.toEquiv.symm, e.dSmooth_invFun, e.dSmooth_toFun⟩

@[simp] theorem symm_symm (e : DSmoothEquiv X Y) : e.symm.symm = e := (rfl)
@[simp, grind =] theorem toEquiv_symm (e : DSmoothEquiv X Y) : e.symm.toEquiv = e.toEquiv.symm :=
  (rfl)
@[simp, grind =] theorem coe_symm_toEquiv (e : DSmoothEquiv X Y) : ⇑e.toEquiv.symm = ⇑e.symm :=
  (rfl)
@[simp] theorem symm_refl : (DSmoothEquiv.refl X).symm = DSmoothEquiv.refl X := (rfl)
@[simp, grind =] theorem symm_mk (e : X ≃ Y) (hf : DSmooth e) (hi : DSmooth e.symm) :
    (mk e hf hi).symm = mk e.symm hi hf := (rfl)
@[simp, grind =] theorem apply_symm_apply (e : DSmoothEquiv X Y) (y : Y) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y
@[simp, grind =] theorem symm_apply_apply (e : DSmoothEquiv X Y) (x : X) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x
@[simp] theorem symm_comp_self (e : DSmoothEquiv X Y) : ⇑e.symm ∘ ⇑e = id :=
  funext e.symm_apply_apply
@[simp] theorem self_comp_symm (e : DSmoothEquiv X Y) : ⇑e ∘ ⇑e.symm = id :=
  funext e.apply_symm_apply

theorem symm_apply_eq (e : DSmoothEquiv X Y) {y : Y} {x : X} : e.symm y = x ↔ y = e x :=
  e.toEquiv.symm_apply_eq

theorem eq_symm_apply (e : DSmoothEquiv X Y) {y : Y} {x : X} : x = e.symm y ↔ e x = y :=
  e.toEquiv.eq_symm_apply

/-- The inverse of a diffeological diffeomorphism is smooth. -/
@[fun_prop] theorem dSmooth_symm (e : DSmoothEquiv X Y) : DSmooth e.symm := e.dSmooth_invFun

/-- Composition of diffeological diffeomorphisms. -/
@[trans] protected def trans (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) : DSmoothEquiv X Z :=
  ⟨e₁.toEquiv.trans e₂.toEquiv, e₂.dSmooth.comp e₁.dSmooth, e₁.symm.dSmooth.comp e₂.symm.dSmooth⟩

@[simp, grind =] theorem coe_trans (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) :
    ⇑(e₁.trans e₂) = ⇑e₂ ∘ ⇑e₁ := (rfl)
@[simp, grind =] theorem trans_apply (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) (x : X) :
    e₁.trans e₂ x = e₂ (e₁ x) := (rfl)
@[simp] theorem toEquiv_trans (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) :
    (e₁.trans e₂).toEquiv = e₁.toEquiv.trans e₂.toEquiv := (rfl)
@[simp] theorem symm_trans (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm := (rfl)
@[simp] theorem refl_trans (e : DSmoothEquiv X Y) : (DSmoothEquiv.refl X).trans e = e :=
  ext fun _ ↦ rfl
@[simp] theorem trans_refl (e : DSmoothEquiv X Y) : e.trans (DSmoothEquiv.refl Y) = e :=
  ext fun _ ↦ rfl

theorem trans_assoc (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) (e₃ : DSmoothEquiv Z Q) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  ext fun _ ↦ rfl

@[simp] theorem self_trans_symm (e : DSmoothEquiv X Y) : e.trans e.symm = DSmoothEquiv.refl X :=
  ext e.symm_apply_apply
@[simp] theorem symm_trans_self (e : DSmoothEquiv X Y) : e.symm.trans e = DSmoothEquiv.refl Y :=
  ext e.apply_symm_apply

/-- Postcomposing a map from a Cartesian space with a diffeomorphism preserves plots. -/
@[simp] theorem comp_isPlot_iff (e : DSmoothEquiv X Y) {n : ℕ} {p : 𝔼ⁿ → X} :
    IsPlot (e ∘ p) ↔ IsPlot p :=
  ⟨fun hp ↦ by simpa only [← comp_assoc, symm_comp_self, id_comp] using e.symm.dSmooth n _ hp,
    fun hp ↦ e.dSmooth n p hp⟩

/-- Postcomposing with a diffeomorphism preserves diffeological smoothness. -/
@[simp] theorem comp_dSmooth_iff (e : DSmoothEquiv Y Z) {f : X → Y} :
    DSmooth (e ∘ f) ↔ DSmooth f :=
  ⟨fun hf ↦ by simpa only [← comp_assoc, symm_comp_self, id_comp] using e.symm.dSmooth.comp hf,
    fun hf ↦ e.dSmooth.comp hf⟩

/-- Precomposing with a diffeomorphism preserves diffeological smoothness. -/
@[simp] theorem dSmooth_comp_iff (e : DSmoothEquiv X Y) {f : Y → Z} :
    DSmooth (f ∘ e) ↔ DSmooth f :=
  ⟨fun hf ↦ by simpa only [comp_assoc, self_comp_symm, comp_id] using hf.comp e.symm.dSmooth,
    fun hf ↦ hf.comp e.dSmooth⟩

/-- Every diffeological diffeomorphism is an induction. -/
theorem isInduction (e : DSmoothEquiv X Y) : IsInduction e where
  injective := e.injective
  isPlot_iff := e.comp_isPlot_iff.symm

/-- Every diffeological diffeomorphism is a subduction. -/
theorem isSubduction (e : DSmoothEquiv X Y) : IsSubduction e where
  surjective := e.surjective
  dSmooth := e.dSmooth
  locallyLifts {_ p} hp := locallyLifts_iff.mpr fun z _ ↦
    ⟨univ, isOpen_univ, mem_univ z, subset_univ univ, e.symm ∘ p,
      isPlotOn_of_isPlot (e.symm.dSmooth _ p hp) univ, fun y _ ↦ e.apply_symm_apply (p y)⟩

/-- Product of two diffeological diffeomorphisms. -/
def prodCongr (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Q R) : DSmoothEquiv (X × Q) (Y × R) :=
  ⟨e₁.toEquiv.prodCongr e₂.toEquiv, e₁.dSmooth.prodMap e₂.dSmooth,
    e₁.symm.dSmooth.prodMap e₂.symm.dSmooth⟩

@[simp, grind =] theorem prodCongr_apply (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Q R)
    (p : X × Q) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) := (rfl)
@[simp] theorem prodCongr_symm (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Q R) :
    (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm := (rfl)

/-- Commutativity of the product diffeology. -/
def prodComm (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y] :
    DSmoothEquiv (X × Y) (Y × X) :=
  ⟨Equiv.prodComm X Y, dSmooth_swap, dSmooth_swap⟩

@[simp, grind =] theorem prodComm_apply (p : X × Y) : prodComm X Y p = p.swap := (rfl)
@[simp] theorem prodComm_symm : (prodComm X Y).symm = prodComm Y X := (rfl)

/-- Associativity of the product diffeology. -/
def prodAssoc (X Y Z : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y]
    [DiffeologicalSpace Z] : DSmoothEquiv ((X × Y) × Z) (X × (Y × Z)) where
  toEquiv := Equiv.prodAssoc X Y Z
  dSmooth_toFun := (dSmooth_fst.comp dSmooth_fst).prodMk
    ((dSmooth_snd.comp dSmooth_fst).prodMk dSmooth_snd)
  dSmooth_invFun := ((dSmooth_fst.prodMk (dSmooth_fst.comp dSmooth_snd)).prodMk
    (dSmooth_snd.comp dSmooth_snd))

@[simp, grind =] theorem prodAssoc_apply (p : (X × Y) × Z) :
    prodAssoc X Y Z p = (p.1.1, (p.1.2, p.2)) := (rfl)
@[simp, grind =] theorem prodAssoc_symm_apply (p : X × (Y × Z)) :
    (prodAssoc X Y Z).symm p = ((p.1, p.2.1), p.2.2) := (rfl)

section Homeomorph

variable [TopologicalSpace X] [IsDTopologyCompatible X]
  [TopologicalSpace Y] [IsDTopologyCompatible Y]

instance instHomeomorphClass : HomeomorphClass (DSmoothEquiv X Y) X Y where
  map_continuous e := e.dSmooth_toFun.continuous'
  inv_continuous e := e.dSmooth_invFun.continuous'

/-- A diffeological diffeomorphism between spaces carrying topologies equal to their D-topologies
is a homeomorphism. -/
def toHomeomorph (e : DSmoothEquiv X Y) : X ≃ₜ Y :=
  ⟨e.toEquiv, e.dSmooth.continuous', e.symm.dSmooth.continuous'⟩

@[simp, grind =] theorem coe_toHomeomorph (e : DSmoothEquiv X Y) : ⇑e.toHomeomorph = ⇑e := (rfl)

theorem toHomeomorph_injective : Injective (toHomeomorph : DSmoothEquiv X Y → (X ≃ₜ Y)) :=
  fun _ _ h ↦ ext fun x ↦ congr($(h) x)

@[simp] theorem toHomeomorph_refl : (DSmoothEquiv.refl X).toHomeomorph = Homeomorph.refl X :=
  Homeomorph.ext fun _ ↦ rfl

@[simp, grind =] theorem toHomeomorph_symm (e : DSmoothEquiv X Y) :
    e.symm.toHomeomorph = e.toHomeomorph.symm := (rfl)

@[simp] theorem toHomeomorph_trans [TopologicalSpace Z] [IsDTopologyCompatible Z]
    (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) :
    (e₁.trans e₂).toHomeomorph = e₁.toHomeomorph.trans e₂.toHomeomorph :=
  Homeomorph.ext fun _ ↦ rfl

end Homeomorph

end DSmoothEquiv

section IsInduction

variable {X Y : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] {f : Y → X}
  (hf : IsInduction f)

/-- An induction defines a diffeomorphism onto its range equipped with the subspace diffeology. -/
def IsInduction.toDSmoothEquivRange : DSmoothEquiv Y (range f) :=
  ⟨Equiv.ofInjective f hf.injective, hf.dSmooth_ofInjective, hf.dSmooth_ofInjective_symm⟩

@[simp] theorem IsInduction.toEquiv_toDSmoothEquivRange :
    hf.toDSmoothEquivRange.toEquiv = Equiv.ofInjective f hf.injective := (rfl)
@[simp, grind =] theorem IsInduction.coe_toDSmoothEquivRange_apply (y : Y) :
    (hf.toDSmoothEquivRange y : X) = f y := (rfl)
@[simp] theorem IsInduction.toDSmoothEquivRange_symm_apply (y : Y) :
    hf.toDSmoothEquivRange.symm ⟨f y, mem_range_self y⟩ = y :=
  hf.toDSmoothEquivRange.symm_apply_eq.mpr (Subtype.ext rfl)

theorem IsInduction.apply_toDSmoothEquivRange_symm (z : range f) :
    f (hf.toDSmoothEquivRange.symm z) = z :=
  Equiv.apply_ofInjective_symm hf.injective z

@[simp] theorem IsInduction.self_comp_toDSmoothEquivRange_symm :
    f ∘ ⇑hf.toDSmoothEquivRange.symm = Subtype.val :=
  funext hf.apply_toDSmoothEquivRange_symm

end IsInduction

/-! ### Product unit laws -/

namespace DSmoothEquiv

variable (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y]

/-- Right unit law `X × Y ≃ X` for the product diffeology when `Y` has a unique element. -/
def prodUnique [Unique Y] : DSmoothEquiv (X × Y) X :=
  ⟨Equiv.prodUnique X Y, dSmooth_fst, dSmooth_id.prodMk (dSmooth_of_subsingleton _)⟩

@[simp] theorem coe_prodUnique [Unique Y] : ⇑(prodUnique X Y) = Prod.fst := (rfl)
@[grind =] theorem prodUnique_apply [Unique Y] (p : X × Y) : prodUnique X Y p = p.1 := (rfl)
@[simp, grind =] theorem prodUnique_symm_apply [Unique Y] (x : X) :
    (prodUnique X Y).symm x = (x, default) := (rfl)
@[simp] theorem toEquiv_prodUnique [Unique Y] :
    (prodUnique X Y).toEquiv = Equiv.prodUnique X Y := (rfl)

/-- Left unit law `X × Y ≃ Y` for the product diffeology when `X` has a unique element. -/
def uniqueProd [Unique X] : DSmoothEquiv (X × Y) Y :=
  (prodComm X Y).trans (prodUnique Y X)

@[simp] theorem coe_uniqueProd [Unique X] : ⇑(uniqueProd X Y) = Prod.snd := (rfl)
@[grind =] theorem uniqueProd_apply [Unique X] (p : X × Y) : uniqueProd X Y p = p.2 := (rfl)
@[simp, grind =] theorem uniqueProd_symm_apply [Unique X] (y : Y) :
    (uniqueProd X Y).symm y = (default, y) := (rfl)
@[simp] theorem toEquiv_uniqueProd [Unique X] :
    (uniqueProd X Y).toEquiv = Equiv.uniqueProd Y X := (rfl)

end DSmoothEquiv

end TauCeti.Diffeology
