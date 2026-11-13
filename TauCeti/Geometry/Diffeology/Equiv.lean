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
  `TauCeti.Diffeology.DSmoothEquiv.prodAssoc`: product diffeomorphisms.
* `TauCeti.Diffeology.DSmoothEquiv.toHomeomorph`: underlying homeomorphism for spaces with
  compatible D-topologies.
* `TauCeti.Diffeology.IsInduction.toDSmoothEquivRange`: diffeomorphism from the source of an
  induction onto its range.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Chapter 1, Articles 1.15–1.17 and 1.29.
-/

public noncomputable section

open Function Set
open scoped Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

/-- A diffeomorphism between diffeological spaces: an equivalence whose forward and inverse maps
are both diffeologically smooth. -/
structure DSmoothEquiv (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y]
    extends X ≃ Y where
  /-- The forward map is smooth. -/
  dSmooth_toFun : _root_.Diffeology.DSmooth toFun
  /-- The inverse map is smooth. -/
  dSmooth_invFun : _root_.Diffeology.DSmooth invFun

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
    congr
    exact Equiv.coe_fn_injective h

/-- The coercion of `toEquiv` agrees with the `EquivLike` coercion. -/
@[simp, grind =]
theorem coe_toEquiv (e : DSmoothEquiv X Y) : ⇑e.toEquiv = ⇑e :=
  (rfl)

/-- `toEquiv` is injective. -/
theorem toEquiv_injective : Injective (toEquiv : DSmoothEquiv X Y → (X ≃ Y)) :=
  fun _ _ h ↦ DFunLike.ext _ _ (Equiv.ext_iff.mp h)

@[ext]
theorem ext {e₁ e₂ : DSmoothEquiv X Y} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
  DFunLike.ext e₁ e₂ h

@[simp, grind =]
theorem coe_mk (e : X ≃ Y) (hf : _root_.Diffeology.DSmooth e)
    (hi : _root_.Diffeology.DSmooth e.symm) : ⇑(mk e hf hi) = ⇑e :=
  (rfl)

@[simp, grind =]
theorem mk_apply (e : X ≃ Y) (hf : _root_.Diffeology.DSmooth e)
    (hi : _root_.Diffeology.DSmooth e.symm) (x : X) : mk e hf hi x = e x :=
  (rfl)

/-- A diffeological diffeomorphism is smooth. -/
@[fun_prop]
protected theorem dSmooth (e : DSmoothEquiv X Y) : _root_.Diffeology.DSmooth e :=
  e.dSmooth_toFun

/-- The identity diffeomorphism of a diffeological space. -/
protected def refl (X : Type*) [DiffeologicalSpace X] : DSmoothEquiv X X where
  toEquiv := Equiv.refl X
  dSmooth_toFun := _root_.Diffeology.dSmooth_id
  dSmooth_invFun := _root_.Diffeology.dSmooth_id

@[simp, grind =]
theorem coe_refl : ⇑(DSmoothEquiv.refl X) = id :=
  (rfl)

@[simp, grind =]
theorem refl_apply (x : X) : DSmoothEquiv.refl X x = x :=
  (rfl)

@[simp]
theorem toEquiv_refl : (DSmoothEquiv.refl X).toEquiv = Equiv.refl X :=
  (rfl)

instance : Inhabited (DSmoothEquiv X X) := ⟨DSmoothEquiv.refl X⟩

/-- The inverse of a diffeological diffeomorphism. -/
@[symm]
protected def symm (e : DSmoothEquiv X Y) : DSmoothEquiv Y X where
  toEquiv := e.toEquiv.symm
  dSmooth_toFun := e.dSmooth_invFun
  dSmooth_invFun := e.dSmooth_toFun

@[simp]
theorem symm_symm (e : DSmoothEquiv X Y) : e.symm.symm = e :=
  (rfl)

@[simp, grind =]
theorem toEquiv_symm (e : DSmoothEquiv X Y) : e.symm.toEquiv = e.toEquiv.symm :=
  (rfl)

@[simp, grind =]
theorem coe_symm_toEquiv (e : DSmoothEquiv X Y) : ⇑e.toEquiv.symm = ⇑e.symm :=
  (rfl)

@[simp]
theorem symm_refl : (DSmoothEquiv.refl X).symm = DSmoothEquiv.refl X :=
  (rfl)

@[simp, grind =]
theorem symm_mk (e : X ≃ Y) (hf : _root_.Diffeology.DSmooth e)
    (hi : _root_.Diffeology.DSmooth e.symm) :
    (mk e hf hi).symm = mk e.symm hi hf :=
  (rfl)

@[simp, grind =]
theorem apply_symm_apply (e : DSmoothEquiv X Y) (y : Y) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

@[simp, grind =]
theorem symm_apply_apply (e : DSmoothEquiv X Y) (x : X) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[simp]
theorem symm_comp_self (e : DSmoothEquiv X Y) : ⇑e.symm ∘ ⇑e = id :=
  funext e.symm_apply_apply

@[simp]
theorem self_comp_symm (e : DSmoothEquiv X Y) : ⇑e ∘ ⇑e.symm = id :=
  funext e.apply_symm_apply

theorem symm_apply_eq (e : DSmoothEquiv X Y) {y : Y} {x : X} : e.symm y = x ↔ y = e x :=
  e.toEquiv.symm_apply_eq

theorem eq_symm_apply (e : DSmoothEquiv X Y) {y : Y} {x : X} : x = e.symm y ↔ e x = y :=
  e.toEquiv.eq_symm_apply

/-- The inverse of a diffeological diffeomorphism is smooth. -/
@[fun_prop]
theorem dSmooth_symm (e : DSmoothEquiv X Y) : _root_.Diffeology.DSmooth e.symm :=
  e.dSmooth_invFun

/-- Composition of diffeological diffeomorphisms. -/
@[trans]
protected def trans (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) : DSmoothEquiv X Z where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  dSmooth_toFun := e₂.dSmooth.comp e₁.dSmooth
  dSmooth_invFun := e₁.symm.dSmooth.comp e₂.symm.dSmooth

@[simp, grind =]
theorem coe_trans (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) :
    ⇑(e₁.trans e₂) = ⇑e₂ ∘ ⇑e₁ :=
  (rfl)

@[simp, grind =]
theorem trans_apply (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) (x : X) :
    e₁.trans e₂ x = e₂ (e₁ x) :=
  (rfl)

@[simp]
theorem toEquiv_trans (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) :
    (e₁.trans e₂).toEquiv = e₁.toEquiv.trans e₂.toEquiv :=
  (rfl)

@[simp]
theorem symm_trans (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  (rfl)

@[simp]
theorem refl_trans (e : DSmoothEquiv X Y) : (DSmoothEquiv.refl X).trans e = e :=
  ext fun _ ↦ rfl

@[simp]
theorem trans_refl (e : DSmoothEquiv X Y) : e.trans (DSmoothEquiv.refl Y) = e :=
  ext fun _ ↦ rfl

theorem trans_assoc (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) (e₃ : DSmoothEquiv Z Q) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  ext fun _ ↦ rfl

@[simp]
theorem self_trans_symm (e : DSmoothEquiv X Y) : e.trans e.symm = DSmoothEquiv.refl X :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self (e : DSmoothEquiv X Y) : e.symm.trans e = DSmoothEquiv.refl Y :=
  ext e.apply_symm_apply

/-- Postcomposing a map from a Cartesian space with a diffeomorphism preserves plots. -/
@[simp]
theorem isPlot_comp_iff (e : DSmoothEquiv X Y) {n : ℕ} {p : 𝔼ⁿ → X} :
    _root_.Diffeology.IsPlot (e ∘ p) ↔ _root_.Diffeology.IsPlot p :=
  ⟨fun hp ↦ by simpa only [← comp_assoc, symm_comp_self, id_comp] using e.symm.dSmooth n _ hp,
    fun hp ↦ e.dSmooth n p hp⟩

/-- Postcomposing with a diffeomorphism preserves diffeological smoothness. -/
@[simp]
theorem dSmooth_comp_iff (e : DSmoothEquiv Y Z) {f : X → Y} :
    _root_.Diffeology.DSmooth (e ∘ f) ↔ _root_.Diffeology.DSmooth f :=
  ⟨fun hf ↦ by simpa only [← comp_assoc, symm_comp_self, id_comp] using e.symm.dSmooth.comp hf,
    fun hf ↦ e.dSmooth.comp hf⟩

/-- Precomposing with a diffeomorphism preserves diffeological smoothness. -/
@[simp]
theorem comp_dSmooth_iff (e : DSmoothEquiv X Y) {f : Y → Z} :
    _root_.Diffeology.DSmooth (f ∘ e) ↔ _root_.Diffeology.DSmooth f :=
  ⟨fun hf ↦ by simpa only [comp_assoc, self_comp_symm, comp_id] using hf.comp e.symm.dSmooth,
    fun hf ↦ hf.comp e.dSmooth⟩

/-- Every diffeological diffeomorphism is an induction. -/
theorem isInduction (e : DSmoothEquiv X Y) : IsInduction e where
  injective := e.injective
  isPlot_iff := e.isPlot_comp_iff.symm

/-- Every diffeological diffeomorphism is a subduction. -/
theorem isSubduction (e : DSmoothEquiv X Y) : IsSubduction e where
  surjective := e.surjective
  dSmooth := e.dSmooth
  locallyLifts {_ p} hp := locallyLifts_iff.mpr fun z _ ↦
    ⟨univ, isOpen_univ, mem_univ z, subset_univ univ, e.symm ∘ p,
      isPlotOn_of_isPlot (e.symm.dSmooth _ p hp) univ, fun y _ ↦ e.apply_symm_apply (p y)⟩

/-- Product of two diffeological diffeomorphisms. -/
def prodCongr (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Q R) :
    DSmoothEquiv (X × Q) (Y × R) where
  toEquiv := e₁.toEquiv.prodCongr e₂.toEquiv
  dSmooth_toFun := e₁.dSmooth.prodMap e₂.dSmooth
  dSmooth_invFun := e₁.symm.dSmooth.prodMap e₂.symm.dSmooth

@[simp, grind =]
theorem prodCongr_apply (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Q R) (p : X × Q) :
    e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) :=
  (rfl)

@[simp]
theorem prodCongr_symm (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Q R) :
    (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm :=
  (rfl)

/-- Commutativity of the product diffeology. -/
def prodComm (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y] :
    DSmoothEquiv (X × Y) (Y × X) where
  toEquiv := Equiv.prodComm X Y
  dSmooth_toFun := dSmooth_swap
  dSmooth_invFun := dSmooth_swap

@[simp, grind =]
theorem prodComm_apply (p : X × Y) : prodComm X Y p = p.swap :=
  (rfl)

@[simp]
theorem prodComm_symm : (prodComm X Y).symm = prodComm Y X :=
  (rfl)

/-- Associativity of the product diffeology. -/
def prodAssoc (X Y Z : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y]
    [DiffeologicalSpace Z] : DSmoothEquiv ((X × Y) × Z) (X × (Y × Z)) where
  toEquiv := Equiv.prodAssoc X Y Z
  dSmooth_toFun := (dSmooth_fst.comp dSmooth_fst).prodMk
    ((dSmooth_snd.comp dSmooth_fst).prodMk dSmooth_snd)
  dSmooth_invFun := ((dSmooth_fst.prodMk (dSmooth_fst.comp dSmooth_snd)).prodMk
    (dSmooth_snd.comp dSmooth_snd))

@[simp, grind =]
theorem prodAssoc_apply (p : (X × Y) × Z) :
    prodAssoc X Y Z p = (p.1.1, (p.1.2, p.2)) :=
  (rfl)

@[simp, grind =]
theorem prodAssoc_symm_apply (p : X × (Y × Z)) :
    (prodAssoc X Y Z).symm p = ((p.1, p.2.1), p.2.2) :=
  (rfl)

/-- A diffeological diffeomorphism between spaces carrying topologies equal to their D-topologies
is a homeomorphism. -/
def toHomeomorph [TopologicalSpace X] [_root_.Diffeology.IsDTopologyCompatible X]
    [TopologicalSpace Y] [_root_.Diffeology.IsDTopologyCompatible Y] (e : DSmoothEquiv X Y) :
    X ≃ₜ Y where
  toEquiv := e.toEquiv
  continuous_toFun := e.dSmooth.continuous'
  continuous_invFun := e.symm.dSmooth.continuous'

@[simp, grind =]
theorem coe_toHomeomorph [TopologicalSpace X] [_root_.Diffeology.IsDTopologyCompatible X]
    [TopologicalSpace Y] [_root_.Diffeology.IsDTopologyCompatible Y] (e : DSmoothEquiv X Y) :
    ⇑e.toHomeomorph = ⇑e :=
  (rfl)

@[simp]
theorem toHomeomorph_symm [TopologicalSpace X] [_root_.Diffeology.IsDTopologyCompatible X]
    [TopologicalSpace Y] [_root_.Diffeology.IsDTopologyCompatible Y] (e : DSmoothEquiv X Y) :
    e.toHomeomorph.symm = e.symm.toHomeomorph :=
  (rfl)

end DSmoothEquiv

/-- An induction defines a diffeomorphism onto its range equipped with the subspace diffeology. -/
def IsInduction.toDSmoothEquivRange {X Y : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y]
    {f : Y → X} (hf : IsInduction f) : DSmoothEquiv Y (range f) where
  toEquiv := Equiv.ofInjective f hf.injective
  dSmooth_toFun := hf.dSmooth_ofInjective
  dSmooth_invFun := hf.dSmooth_ofInjective_symm

@[simp, grind =]
theorem IsInduction.coe_toDSmoothEquivRange_apply {X Y : Type*} [DiffeologicalSpace X]
    [DiffeologicalSpace Y] {f : Y → X} (hf : IsInduction f) (y : Y) :
    (hf.toDSmoothEquivRange y : X) = f y :=
  (rfl)

/-! ### Subsingletons and `PUnit` -/

/-- Every map from a Cartesian space into a subsingleton diffeological space is a plot, since it
is constant. -/
theorem isPlot_of_subsingleton {X : Type*} [DiffeologicalSpace X] [Subsingleton X] {n : ℕ}
    (p : 𝔼ⁿ → X) : _root_.Diffeology.IsPlot p := by
  convert _root_.Diffeology.isPlot_const (x := p 0)

/-- Every map into a subsingleton diffeological space is smooth. -/
theorem dSmooth_of_subsingleton {X Y : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y]
    [Subsingleton Y] (f : X → Y) : _root_.Diffeology.DSmooth f :=
  fun _ p _ ↦ isPlot_of_subsingleton (f ∘ p)

/-- The unique diffeology on `PUnit`, whose D-topology is the standard topology. -/
instance instDiffeologicalSpacePUnit : DiffeologicalSpace PUnit where
  plots _ := univ
  constant_plots _ := mem_univ _
  plot_reparam _ _ := mem_univ _
  locality _ := mem_univ _
  dTopology := inferInstance
  isOpen_iff_preimages_plots {u} :=
    ⟨fun _ _ p _ ↦ by
      rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · exact isOpen_empty
      · convert isOpen_univ
        exact eq_univ_of_forall fun z ↦ mem_preimage.mpr (Subsingleton.elim x (p z) ▸ hx),
      fun _ ↦ trivial⟩

instance instIsDTopologyCompatiblePUnit : _root_.Diffeology.IsDTopologyCompatible PUnit := ⟨rfl⟩

namespace DSmoothEquiv

variable (X : Type*) [DiffeologicalSpace X]

/-- Left unit law `PUnit × X ≃ X` for the product diffeology. -/
def punitProd : DSmoothEquiv (PUnit × X) X where
  toEquiv := Equiv.punitProd X
  dSmooth_toFun := dSmooth_snd
  dSmooth_invFun := (dSmooth_of_subsingleton _).prodMk _root_.Diffeology.dSmooth_id

@[simp, grind =]
theorem punitProd_apply (p : PUnit × X) : punitProd X p = p.2 :=
  (rfl)

@[simp, grind =]
theorem punitProd_symm_apply (x : X) : (punitProd X).symm x = (PUnit.unit, x) :=
  (rfl)

/-- Right unit law `X × PUnit ≃ X` for the product diffeology. -/
def prodPUnit : DSmoothEquiv (X × PUnit) X where
  toEquiv := Equiv.prodPUnit X
  dSmooth_toFun := dSmooth_fst
  dSmooth_invFun := _root_.Diffeology.dSmooth_id.prodMk (dSmooth_of_subsingleton _)

@[simp, grind =]
theorem prodPUnit_apply (p : X × PUnit) : prodPUnit X p = p.1 :=
  (rfl)

@[simp, grind =]
theorem prodPUnit_symm_apply (x : X) : (prodPUnit X).symm x = (x, PUnit.unit) :=
  (rfl)

end DSmoothEquiv

end TauCeti.Diffeology
