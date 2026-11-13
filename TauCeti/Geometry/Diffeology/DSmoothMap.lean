/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeology.Equiv

/-!
# Bundled smooth maps and the functional diffeology

This file defines `TauCeti.Diffeology.DSmoothMap X Y`, the type of bundled diffeologically smooth
maps between diffeological spaces `X` and `Y`, and equips it with the functional diffeology
(`TauCeti.Diffeology.instDiffeologicalSpaceDSmoothMap`): a parametrized family
`p : 𝔼ⁿ → DSmoothMap X Y` is a plot precisely when `(u, x) ↦ p u x` is smooth on `𝔼ⁿ × X`.

This makes the category of diffeological spaces Cartesian closed without any vector-space or
manifold assumptions on the mapping space:

* **Universal property** (`TauCeti.Diffeology.DSmoothMap.dSmooth_iff_uncurry`): for any
  diffeological space `Z`, a map `g : Z → DSmoothMap X Y` is smooth if and only if
  `(z, x) ↦ g z x` is smooth on `Z × X`. Likewise, on any subset `u` of `𝔼ⁿ`, `p` is a local plot
  on `u` if and only if `(q, x) ↦ p q.1 x` is smooth on `u × X`
  (`TauCeti.Diffeology.DSmoothMap.isPlotOn_iff_dSmooth_uncurry`).
* **Evaluation and composition**: evaluation `DSmoothMap X Y × X → Y`
  (`TauCeti.Diffeology.DSmoothMap.dSmooth_eval`) and composition
  `DSmoothMap Y Z × DSmoothMap X Y → DSmoothMap X Z`
  (`TauCeti.Diffeology.DSmoothMap.dSmooth_comp`) are smooth.
* **Exponential law** (`TauCeti.Diffeology.DSmoothMap.curryEquiv`): currying and uncurrying give a
  diffeological diffeomorphism `DSmoothMap (Z × X) Y ≃ DSmoothMap Z (DSmoothMap X Y)`.
* **Constant and point-domain maps**: sending `y` to the constant map at `y` is an induction when
  `X` is nonempty (`TauCeti.Diffeology.DSmoothMap.isInduction_const`), and evaluation at `default`
  identifies `DSmoothMap X Y` with `Y` as a diffeological space when `X` has a unique element
  (`TauCeti.Diffeology.DSmoothMap.evalUniqueEquiv`).
* **Smooth translation families**: on a type with smooth multiplication, left and right
  multiplication define smooth maps `G → DSmoothMap G G`
  (`TauCeti.Diffeology.DSmoothMap.dSmooth_mulLeft`,
  `TauCeti.Diffeology.DSmoothMap.dSmooth_mulRight`, and their additive counterparts).
* **D-topology of evaluation**: when `X` is locally compact, `DSmoothMap X Y × X` inherits
  D-topology compatibility from
  `TauCeti.Diffeology.instIsDTopologyCompatibleProdOfLocallyCompactSpaceRight`, so evaluation is
  continuous for the product topology (`TauCeti.Diffeology.DSmoothMap.continuous_eval`).

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Articles 1.57–1.60, for the functional diffeology, evaluation,
  composition, and currying.
* J. D. Christensen, G. Sinnamon and E. Wu, *The D-topology for diffeological spaces*, Pacific J.
  Math. **272** (2014), 87–110, Section 4, for D-topologies of products and mapping spaces.
* B. Eltschig, `lean-catdg` (`CatDG.Diffeology.DSmoothMap`), for a prior Lean 4 formalization of
  bundled smooth maps and functional diffeologies alongside which `Mathlib.Geometry.Diffeology`
  was developed.
-/

public noncomputable section

open Function Set
open scoped ContDiff Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

/-- Bundled diffeologically smooth maps from `X` to `Y`. -/
structure DSmoothMap (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y] where
  /-- The underlying function of a smooth map. -/
  toFun : X → Y
  /-- The underlying function is diffeologically smooth. -/
  dSmooth_toFun : _root_.Diffeology.DSmooth toFun

namespace DSmoothMap

section Basic

variable {X Y Z Q R : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]
  [DiffeologicalSpace Q] [DiffeologicalSpace R]

instance instFunLike : FunLike (DSmoothMap X Y) X Y where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

instance instContinuousMapClass [TopologicalSpace X] [_root_.Diffeology.IsDTopologyCompatible X]
    [TopologicalSpace Y] [_root_.Diffeology.IsDTopologyCompatible Y] :
    ContinuousMapClass (DSmoothMap X Y) X Y where
  map_continuous f := f.dSmooth_toFun.continuous'

@[simp, grind =]
theorem toFun_eq_coe (f : DSmoothMap X Y) : f.toFun = ⇑f :=
  (rfl)

theorem coe_injective : Injective ((⇑) : DSmoothMap X Y → (X → Y)) :=
  DFunLike.coe_injective

@[ext]
theorem ext {f g : DSmoothMap X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp, grind =]
theorem coe_mk (f : X → Y) (hf : _root_.Diffeology.DSmooth f) : ⇑(mk f hf) = f :=
  (rfl)

@[simp, grind =]
theorem mk_apply (f : X → Y) (hf : _root_.Diffeology.DSmooth f) (x : X) : mk f hf x = f x :=
  (rfl)

@[simp]
theorem eta (f : DSmoothMap X Y) : mk f f.dSmooth_toFun = f :=
  (rfl)

/-- A bundled smooth map is smooth. -/
@[fun_prop]
protected theorem dSmooth (f : DSmoothMap X Y) : _root_.Diffeology.DSmooth f :=
  f.dSmooth_toFun

/-- Composing a plot with a bundled smooth map gives a plot. -/
protected theorem isPlot_comp (f : DSmoothMap X Y) {n : ℕ} {p : 𝔼ⁿ → X}
    (hp : _root_.Diffeology.IsPlot p) : _root_.Diffeology.IsPlot (f ∘ p) :=
  f.dSmooth n p hp

/-- Copy of a `DSmoothMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : DSmoothMap X Y) (f' : X → Y) (h : f' = f) : DSmoothMap X Y where
  toFun := f'
  dSmooth_toFun := h.symm ▸ f.dSmooth

@[simp]
theorem coe_copy (f : DSmoothMap X Y) (f' : X → Y) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  (rfl)

theorem copy_eq (f : DSmoothMap X Y) (f' : X → Y) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

/-- The identity map as a bundled smooth map. -/
protected def id (X : Type*) [DiffeologicalSpace X] : DSmoothMap X X :=
  ⟨_root_.id, _root_.Diffeology.dSmooth_id⟩

@[simp, grind =]
theorem coe_id : ⇑(DSmoothMap.id X) = _root_.id :=
  (rfl)

@[simp, grind =]
theorem id_apply (x : X) : DSmoothMap.id X x = x :=
  (rfl)

/-- Composition of bundled smooth maps. -/
def comp (g : DSmoothMap Y Z) (f : DSmoothMap X Y) : DSmoothMap X Z :=
  ⟨g ∘ f, g.dSmooth.comp f.dSmooth⟩

@[simp, grind =]
theorem coe_comp (g : DSmoothMap Y Z) (f : DSmoothMap X Y) : ⇑(g.comp f) = ⇑g ∘ ⇑f :=
  (rfl)

@[simp, grind =]
theorem comp_apply (g : DSmoothMap Y Z) (f : DSmoothMap X Y) (x : X) : g.comp f x = g (f x) :=
  (rfl)

@[simp]
theorem comp_id (f : DSmoothMap X Y) : f.comp (DSmoothMap.id X) = f :=
  ext fun _ ↦ rfl

@[simp]
theorem id_comp (f : DSmoothMap X Y) : (DSmoothMap.id Y).comp f = f :=
  ext fun _ ↦ rfl

theorem comp_assoc (h : DSmoothMap Z Q) (g : DSmoothMap Y Z) (f : DSmoothMap X Y) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  (rfl)

/-- Constant map as a bundled smooth map. -/
def const (X : Type*) [DiffeologicalSpace X] (y : Y) : DSmoothMap X Y :=
  ⟨Function.const X y, _root_.Diffeology.dSmooth_const⟩

@[simp, grind =]
theorem coe_const (y : Y) : ⇑(const X y) = Function.const X y :=
  (rfl)

@[simp, grind =]
theorem const_apply (y : Y) (x : X) : const X y x = y :=
  (rfl)

@[simp]
theorem comp_const (g : DSmoothMap Y Z) (y : Y) : g.comp (const X y) = const X (g y) :=
  ext fun _ ↦ rfl

@[simp]
theorem const_comp (f : DSmoothMap X Y) (z : Z) : (const Y z).comp f = const X z :=
  ext fun _ ↦ rfl

instance [Inhabited Y] : Inhabited (DSmoothMap X Y) := ⟨const X default⟩

/-- First projection of a product as a bundled smooth map. -/
def fst : DSmoothMap (X × Y) X :=
  ⟨Prod.fst, dSmooth_fst⟩

@[simp, grind =]
theorem coe_fst : ⇑(fst : DSmoothMap (X × Y) X) = Prod.fst :=
  (rfl)

@[simp, grind =]
theorem fst_apply (p : X × Y) : fst p = p.1 :=
  (rfl)

/-- Second projection of a product as a bundled smooth map. -/
def snd : DSmoothMap (X × Y) Y :=
  ⟨Prod.snd, dSmooth_snd⟩

@[simp, grind =]
theorem coe_snd : ⇑(snd : DSmoothMap (X × Y) Y) = Prod.snd :=
  (rfl)

@[simp, grind =]
theorem snd_apply (p : X × Y) : snd p = p.2 :=
  (rfl)

/-- Product of two smooth maps with a common domain. -/
def prodMk (f : DSmoothMap Z X) (g : DSmoothMap Z Y) : DSmoothMap Z (X × Y) :=
  ⟨fun z ↦ (f z, g z), f.dSmooth.prodMk g.dSmooth⟩

@[simp, grind =]
theorem prodMk_apply (f : DSmoothMap Z X) (g : DSmoothMap Z Y) (z : Z) :
    f.prodMk g z = (f z, g z) :=
  (rfl)

@[simp]
theorem fst_comp_prodMk (f : DSmoothMap Z X) (g : DSmoothMap Z Y) :
    fst.comp (f.prodMk g) = f :=
  ext fun _ ↦ rfl

@[simp]
theorem snd_comp_prodMk (f : DSmoothMap Z X) (g : DSmoothMap Z Y) :
    snd.comp (f.prodMk g) = g :=
  ext fun _ ↦ rfl

@[simp]
theorem prod_eta (f : DSmoothMap Z (X × Y)) : (fst.comp f).prodMk (snd.comp f) = f :=
  ext fun _ ↦ rfl

/-- Cartesian product of two bundled smooth maps. -/
def prodMap (f : DSmoothMap X Q) (g : DSmoothMap Y R) : DSmoothMap (X × Y) (Q × R) :=
  ⟨Prod.map f g, f.dSmooth.prodMap g.dSmooth⟩

@[simp, grind =]
theorem coe_prodMap (f : DSmoothMap X Q) (g : DSmoothMap Y R) :
    ⇑(f.prodMap g) = Prod.map f g :=
  (rfl)

@[simp, grind =]
theorem prodMap_apply (f : DSmoothMap X Q) (g : DSmoothMap Y R) (p : X × Y) :
    f.prodMap g p = (f p.1, g p.2) :=
  (rfl)

/-- Inclusion of a subtype equipped with the subspace diffeology. -/
def subtypeVal {P : X → Prop} : DSmoothMap (Subtype P) X :=
  ⟨Subtype.val, dSmooth_subtype_val⟩

@[simp, grind =]
theorem coe_subtypeVal {P : X → Prop} : ⇑(subtypeVal : DSmoothMap (Subtype P) X) = Subtype.val :=
  (rfl)

@[simp, grind =]
theorem subtypeVal_apply {P : X → Prop} (x : Subtype P) : subtypeVal x = (x : X) :=
  (rfl)

/-- Restrict the codomain of a smooth map to a subset carrying the subspace diffeology. -/
def codRestrict (f : DSmoothMap X Y) (s : Set Y) (hs : ∀ x, f x ∈ s) : DSmoothMap X s :=
  ⟨s.codRestrict f hs, f.dSmooth.subtype_mk hs⟩

@[simp, grind =]
theorem coe_codRestrict_apply (f : DSmoothMap X Y) (s : Set Y) (hs : ∀ x, f x ∈ s) (x : X) :
    (f.codRestrict s hs x : Y) = f x :=
  (rfl)

@[simp]
theorem subtypeVal_comp_codRestrict (f : DSmoothMap X Y) (s : Set Y) (hs : ∀ x, f x ∈ s) :
    subtypeVal.comp (f.codRestrict s hs) = f :=
  ext fun _ ↦ rfl

end Basic

end DSmoothMap

namespace DSmoothEquiv

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

/-- View a diffeological diffeomorphism as a bundled smooth map. -/
def toDSmoothMap (e : DSmoothEquiv X Y) : DSmoothMap X Y :=
  ⟨e, e.dSmooth⟩

@[simp, grind =]
theorem coe_toDSmoothMap (e : DSmoothEquiv X Y) : ⇑e.toDSmoothMap = ⇑e :=
  (rfl)

@[simp, grind =]
theorem toDSmoothMap_apply (e : DSmoothEquiv X Y) (x : X) : e.toDSmoothMap x = e x :=
  (rfl)

@[simp]
theorem toDSmoothMap_refl : (DSmoothEquiv.refl X).toDSmoothMap = DSmoothMap.id X :=
  DSmoothMap.ext fun _ ↦ by simp

@[simp]
theorem toDSmoothMap_trans (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) :
    (e₁.trans e₂).toDSmoothMap = e₂.toDSmoothMap.comp e₁.toDSmoothMap :=
  DSmoothMap.ext fun _ ↦ by simp

@[simp]
theorem symm_toDSmoothMap_comp (e : DSmoothEquiv X Y) :
    e.symm.toDSmoothMap.comp e.toDSmoothMap = DSmoothMap.id X :=
  DSmoothMap.ext e.symm_apply_apply

@[simp]
theorem toDSmoothMap_comp_symm (e : DSmoothEquiv X Y) :
    e.toDSmoothMap.comp e.symm.toDSmoothMap = DSmoothMap.id Y :=
  DSmoothMap.ext e.apply_symm_apply

/-- Construct a diffeological diffeomorphism from mutually inverse bundled smooth maps. -/
def ofDSmoothMap (f : DSmoothMap X Y) (g : DSmoothMap Y X)
    (h₁ : g.comp f = DSmoothMap.id X) (h₂ : f.comp g = DSmoothMap.id Y) : DSmoothEquiv X Y :=
  mk ⟨f, g, fun x ↦ congr($(h₁) x), fun y ↦ congr($(h₂) y)⟩ f.dSmooth g.dSmooth

@[simp, grind =]
theorem coe_ofDSmoothMap (f : DSmoothMap X Y) (g : DSmoothMap Y X)
    (h₁ : g.comp f = DSmoothMap.id X) (h₂ : f.comp g = DSmoothMap.id Y) :
    ⇑(ofDSmoothMap f g h₁ h₂) = ⇑f :=
  (rfl)

@[simp, grind =]
theorem ofDSmoothMap_apply (f : DSmoothMap X Y) (g : DSmoothMap Y X)
    (h₁ : g.comp f = DSmoothMap.id X) (h₂ : f.comp g = DSmoothMap.id Y) (x : X) :
    ofDSmoothMap f g h₁ h₂ x = f x :=
  (rfl)

@[simp]
theorem ofDSmoothMap_symm (f : DSmoothMap X Y) (g : DSmoothMap Y X)
    (h₁ : g.comp f = DSmoothMap.id X) (h₂ : f.comp g = DSmoothMap.id Y) :
    (ofDSmoothMap f g h₁ h₂).symm = ofDSmoothMap g f h₂ h₁ :=
  ext fun _ ↦ by simp [ofDSmoothMap]

end DSmoothEquiv

/-! ### The functional diffeology -/

section FunctionalDiffeology

variable {X Y Z Q : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]
  [DiffeologicalSpace Q]

/-- The functional diffeology on `DSmoothMap X Y`: a parametrized family `p : 𝔼ⁿ → DSmoothMap X Y`
is a plot precisely when `(u, x) ↦ p u x` is smooth on `𝔼ⁿ × X`. -/
instance instDiffeologicalSpaceDSmoothMap : DiffeologicalSpace (DSmoothMap X Y) where
  plots _ := {p | _root_.Diffeology.DSmooth fun q : _ × X ↦ p q.1 q.2}
  constant_plots f := f.dSmooth.comp dSmooth_snd
  plot_reparam hp hf := hp.comp (hf.dSmooth.prodMap _root_.Diffeology.dSmooth_id)
  locality {n p} hp := by
    intro k r hr
    obtain ⟨hr₁, hr₂⟩ := isPlot_prod_iff.mp hr
    refine DiffeologicalSpace.locality fun w ↦ ?_
    obtain ⟨v, hv, hrv, hpv⟩ := hp (r w).1
    have hr₁_diff : ContDiff ℝ ∞ (Prod.fst ∘ r) := hr₁.contDiff
    refine ⟨(Prod.fst ∘ r) ⁻¹' v, hv.preimage hr₁_diff.continuous, hrv, fun {j} h hhv hh ↦ ?_⟩
    have hpf : _root_.Diffeology.DSmooth (fun q : 𝔼ʲ × X ↦ p (r (h q.1)).1 q.2) :=
      hpv hhv (hr₁_diff.comp hh)
    exact hpf j (fun z ↦ (z, (r (h z)).2))
      (isPlot_prod_iff.mpr ⟨_root_.Diffeology.isPlot_id,
        _root_.Diffeology.isPlot_reparam hr₂ hh⟩)

namespace DSmoothMap

/-- A map from a Cartesian space into `DSmoothMap X Y` is a plot if and only if its uncurried
form on `𝔼ⁿ × X` is smooth. -/
@[simp]
theorem isPlot_iff_dSmooth_uncurry {n : ℕ} {p : 𝔼ⁿ → DSmoothMap X Y} :
    _root_.Diffeology.IsPlot p ↔ _root_.Diffeology.DSmooth (fun q : 𝔼ⁿ × X ↦ p q.1 q.2) :=
  (Iff.rfl)

/-- A map from a Cartesian space into `DSmoothMap X Y` is a local plot on a subset `u` if and only
if `(q, x) ↦ p q.1 x` is smooth on `u × X` with `u` carrying its subspace diffeology. -/
@[simp]
theorem isPlotOn_iff_dSmooth_uncurry {n : ℕ} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → DSmoothMap X Y} :
    IsPlotOn u p ↔ _root_.Diffeology.DSmooth (fun q : u × X ↦ p q.1.1 q.2) := by
  refine ⟨fun hp m r hr ↦ ?_, fun h ↦ isPlotOn_iff.mpr fun f hfu hf ↦ ?_⟩
  · obtain ⟨hr₁, hr₂⟩ := isPlot_prod_iff.mp hr
    have hr₁_diff : ContDiff ℝ ∞ (Subtype.val ∘ Prod.fst ∘ r) :=
      (isPlot_subtype_iff.mp hr₁).contDiff
    have hpf : _root_.Diffeology.DSmooth (fun q : 𝔼ᵐ × X ↦ p ((r q.1).1 : 𝔼ⁿ) q.2) :=
      hp.isPlot_comp (fun z _ ↦ (r z).1.2) hr₁_diff
    exact hpf m (fun z ↦ (z, (r z).2))
      (isPlot_prod_iff.mpr ⟨_root_.Diffeology.isPlot_id, hr₂⟩)
  · have hF : _root_.Diffeology.DSmooth
        (fun q : _ × X ↦ ((⟨f q.1, hfu (mem_univ q.1)⟩ : u), q.2)) :=
      ((hf.dSmooth.comp dSmooth_fst).subtype_mk fun q ↦ hfu (mem_univ q.1)).prodMk dSmooth_snd
    exact h.comp hF

/-- **Universal property of the functional diffeology.** A map `g : Z → DSmoothMap X Y` is smooth
if and only if `(z, x) ↦ g z x` is smooth on `Z × X`. -/
@[simp]
theorem dSmooth_iff_uncurry {g : Z → DSmoothMap X Y} :
    _root_.Diffeology.DSmooth g ↔ _root_.Diffeology.DSmooth (fun q : Z × X ↦ g q.1 q.2) := by
  refine ⟨fun hg n r hr ↦ ?_, fun hg n p hp ↦ ?_⟩
  · obtain ⟨hr₁, hr₂⟩ := isPlot_prod_iff.mp hr
    exact (hg n (Prod.fst ∘ r) hr₁) n (fun w ↦ (w, (r w).2))
      (isPlot_prod_iff.mpr ⟨_root_.Diffeology.isPlot_id, hr₂⟩)
  · exact hg.comp (hp.dSmooth.prodMap _root_.Diffeology.dSmooth_id)

/-- Evaluation `DSmoothMap X Y × X → Y` is smooth. -/
@[fun_prop]
theorem dSmooth_eval : _root_.Diffeology.DSmooth (fun q : DSmoothMap X Y × X ↦ q.1 q.2) :=
  dSmooth_iff_uncurry.mp _root_.Diffeology.dSmooth_id

/-- Evaluation as a bundled smooth map `DSmoothMap X Y × X → Y`. -/
def eval : DSmoothMap (DSmoothMap X Y × X) Y :=
  ⟨fun q ↦ q.1 q.2, dSmooth_eval⟩

@[simp, grind =]
theorem eval_apply (q : DSmoothMap X Y × X) : eval q = q.1 q.2 :=
  (rfl)

/-- Evaluation at a fixed point `x : X` as a bundled smooth map `DSmoothMap X Y → Y`. -/
def evalAt (x : X) : DSmoothMap (DSmoothMap X Y) Y :=
  ⟨fun f ↦ f x,
    dSmooth_eval.comp (_root_.Diffeology.dSmooth_id.prodMk _root_.Diffeology.dSmooth_const)⟩

@[simp, grind =]
theorem evalAt_apply (x : X) (f : DSmoothMap X Y) : evalAt x f = f x :=
  (rfl)

/-- Evaluating a smooth map at a fixed point `x : X` is smooth on `DSmoothMap X Y`. -/
@[fun_prop]
theorem dSmooth_evalAt (x : X) : _root_.Diffeology.DSmooth (fun f : DSmoothMap X Y ↦ f x) :=
  (evalAt x).dSmooth

/-- Composition `DSmoothMap Y Z × DSmoothMap X Y → DSmoothMap X Z` is smooth. -/
@[fun_prop]
theorem dSmooth_comp :
    _root_.Diffeology.DSmooth (fun q : DSmoothMap Y Z × DSmoothMap X Y ↦ q.1.comp q.2) :=
  dSmooth_iff_uncurry.mpr <|
    dSmooth_eval.comp <|
      (dSmooth_fst.comp dSmooth_fst).prodMk
        (dSmooth_eval.comp ((dSmooth_snd.comp dSmooth_fst).prodMk dSmooth_snd))

/-- Composition as a bundled smooth map. -/
def compMap : DSmoothMap (DSmoothMap Y Z × DSmoothMap X Y) (DSmoothMap X Z) :=
  ⟨fun q ↦ q.1.comp q.2, dSmooth_comp⟩

@[simp, grind =]
theorem compMap_apply (q : DSmoothMap Y Z × DSmoothMap X Y) : compMap q = q.1.comp q.2 :=
  (rfl)

/-- Postcomposition with a bundled smooth map `g : DSmoothMap Y Z` as a bundled smooth map
`DSmoothMap X Y → DSmoothMap X Z`. -/
def postcomp (X : Type*) [DiffeologicalSpace X] (g : DSmoothMap Y Z) :
    DSmoothMap (DSmoothMap X Y) (DSmoothMap X Z) :=
  ⟨g.comp, dSmooth_comp.comp (_root_.Diffeology.dSmooth_const.prodMk _root_.Diffeology.dSmooth_id)⟩

@[simp, grind =]
theorem postcomp_apply (g : DSmoothMap Y Z) (f : DSmoothMap X Y) :
    postcomp X g f = g.comp f :=
  (rfl)

@[simp]
theorem postcomp_id : postcomp X (DSmoothMap.id Y) = DSmoothMap.id (DSmoothMap X Y) :=
  ext fun _ ↦ id_comp _

@[simp]
theorem postcomp_comp (h : DSmoothMap Z Q) (g : DSmoothMap Y Z) :
    (postcomp X h).comp (postcomp X g) = postcomp X (h.comp g) :=
  ext fun _ ↦ rfl

/-- Precomposition with a bundled smooth map `f : DSmoothMap X Y` as a bundled smooth map
`DSmoothMap Y Z → DSmoothMap X Z`. -/
def precomp (Z : Type*) [DiffeologicalSpace Z] (f : DSmoothMap X Y) :
    DSmoothMap (DSmoothMap Y Z) (DSmoothMap X Z) :=
  ⟨fun g ↦ g.comp f,
    dSmooth_comp.comp (_root_.Diffeology.dSmooth_id.prodMk _root_.Diffeology.dSmooth_const)⟩

@[simp, grind =]
theorem precomp_apply (f : DSmoothMap X Y) (g : DSmoothMap Y Z) :
    precomp Z f g = g.comp f :=
  (rfl)

@[simp]
theorem precomp_id : precomp Z (DSmoothMap.id X) = DSmoothMap.id (DSmoothMap X Z) :=
  ext fun _ ↦ comp_id _

@[simp]
theorem precomp_comp (g : DSmoothMap Y Q) (f : DSmoothMap X Y) :
    (precomp Z f).comp (precomp Z g) = precomp Z (g.comp f) :=
  ext fun _ ↦ rfl

/-- Curry a smooth map `Z × X → Y` to a smooth map `Z → DSmoothMap X Y`. -/
def curry (f : DSmoothMap (Z × X) Y) : DSmoothMap Z (DSmoothMap X Y) where
  toFun z := ⟨fun x ↦ f (z, x),
    f.dSmooth.comp (_root_.Diffeology.dSmooth_const.prodMk _root_.Diffeology.dSmooth_id)⟩
  dSmooth_toFun := dSmooth_iff_uncurry.mpr f.dSmooth

@[simp, grind =]
theorem curry_apply (f : DSmoothMap (Z × X) Y) (z : Z) (x : X) :
    curry f z x = f (z, x) :=
  (rfl)

/-- Uncurry a smooth map `Z → DSmoothMap X Y` to a smooth map `Z × X → Y`. -/
def uncurry (g : DSmoothMap Z (DSmoothMap X Y)) : DSmoothMap (Z × X) Y :=
  ⟨fun q ↦ g q.1 q.2, dSmooth_iff_uncurry.mp g.dSmooth⟩

@[simp, grind =]
theorem uncurry_apply (g : DSmoothMap Z (DSmoothMap X Y)) (q : Z × X) :
    uncurry g q = g q.1 q.2 :=
  (rfl)

@[simp]
theorem uncurry_curry (f : DSmoothMap (Z × X) Y) : uncurry (curry f) = f :=
  ext fun _ ↦ rfl

@[simp]
theorem curry_uncurry (g : DSmoothMap Z (DSmoothMap X Y)) : curry (uncurry g) = g :=
  ext fun _ ↦ ext fun _ ↦ rfl

/-- Currying is smooth for the functional diffeologies. -/
@[fun_prop]
theorem dSmooth_curry :
    _root_.Diffeology.DSmooth (curry : DSmoothMap (Z × X) Y → DSmoothMap Z (DSmoothMap X Y)) :=
  dSmooth_iff_uncurry.mpr <| dSmooth_iff_uncurry.mpr <|
    dSmooth_eval.comp ((dSmooth_fst.comp dSmooth_fst).prodMk
      ((dSmooth_snd.comp dSmooth_fst).prodMk dSmooth_snd))

/-- Uncurrying is smooth for the functional diffeologies. -/
@[fun_prop]
theorem dSmooth_uncurry :
    _root_.Diffeology.DSmooth (uncurry : DSmoothMap Z (DSmoothMap X Y) → DSmoothMap (Z × X) Y) :=
  dSmooth_iff_uncurry.mpr <|
    dSmooth_eval.comp
      ((dSmooth_eval.comp (dSmooth_fst.prodMk (dSmooth_fst.comp dSmooth_snd))).prodMk
        (dSmooth_snd.comp dSmooth_snd))

/-- **Exponential law for diffeological spaces.** Currying and uncurrying form a diffeological
diffeomorphism `DSmoothMap (Z × X) Y ≃ DSmoothMap Z (DSmoothMap X Y)`. -/
def curryEquiv : DSmoothEquiv (DSmoothMap (Z × X) Y) (DSmoothMap Z (DSmoothMap X Y)) :=
  DSmoothEquiv.ofDSmoothMap ⟨curry, dSmooth_curry⟩ ⟨uncurry, dSmooth_uncurry⟩
    (ext uncurry_curry) (ext curry_uncurry)

@[simp, grind =]
theorem curryEquiv_apply (f : DSmoothMap (Z × X) Y) : curryEquiv f = curry f :=
  (rfl)

@[simp, grind =]
theorem curryEquiv_symm_apply (g : DSmoothMap Z (DSmoothMap X Y)) :
    curryEquiv.symm g = uncurry g := by
  simp [curryEquiv]

/-- Sending `y : Y` to the constant smooth map `X → Y` at `y` is smooth. -/
@[fun_prop]
theorem dSmooth_const : _root_.Diffeology.DSmooth (const X : Y → DSmoothMap X Y) :=
  dSmooth_iff_uncurry.mpr dSmooth_fst

/-- Sending `y : Y` to the constant smooth map `X → Y` as a bundled smooth map. -/
def constMap (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y] :
    DSmoothMap Y (DSmoothMap X Y) :=
  ⟨const X, dSmooth_const⟩

@[simp, grind =]
theorem constMap_apply (y : Y) (x : X) : constMap X Y y x = y :=
  (rfl)

/-- When `X` is nonempty, the inclusion of constant maps `Y → DSmoothMap X Y` is an induction. -/
theorem isInduction_const [Nonempty X] : IsInduction (const X : Y → DSmoothMap X Y) where
  injective y₁ y₂ h := by
    obtain ⟨x₀⟩ := ‹Nonempty X›
    exact congr($(h) x₀)
  isPlot_iff {n p} := by
    refine ⟨fun hp ↦ dSmooth_const n p hp, fun hp ↦ ?_⟩
    obtain ⟨x₀⟩ := ‹Nonempty X›
    exact (dSmooth_evalAt x₀) n (const X ∘ p) hp

/-- When `X` has a unique element, evaluation at `default` identifies `DSmoothMap X Y` with `Y`
as a diffeological space, with inverse `DSmoothMap.constMap`. -/
def evalUniqueEquiv (X Y : Type*) [DiffeologicalSpace X] [Unique X] [DiffeologicalSpace Y] :
    DSmoothEquiv (DSmoothMap X Y) Y :=
  DSmoothEquiv.ofDSmoothMap (evalAt default) (constMap X Y)
    (ext fun f ↦ ext fun x ↦ congrArg f (Subsingleton.elim default x))
    (ext fun _ ↦ rfl)

@[simp, grind =]
theorem evalUniqueEquiv_apply [Unique X] (f : DSmoothMap X Y) :
    evalUniqueEquiv X Y f = f default :=
  (rfl)

@[simp, grind =]
theorem evalUniqueEquiv_symm_apply [Unique X] (y : Y) :
    (evalUniqueEquiv X Y).symm y = const X y := by
  ext
  simp [evalUniqueEquiv]

/-! ### Smooth multiplication and translation families -/

section Mul

variable {G : Type*} [Mul G] [DiffeologicalSpace G]

/-- Left multiplication by `g` as a bundled smooth map when multiplication on `G` is smooth. -/
@[to_additive
/-- Left addition by `g` as a bundled smooth map when addition on `G` is smooth. -/]
def mulLeft (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2)) (g : G) :
    DSmoothMap G G :=
  ⟨(g * ·), hmul.comp (_root_.Diffeology.dSmooth_const.prodMk _root_.Diffeology.dSmooth_id)⟩

@[to_additive (attr := simp, grind =)]
theorem mulLeft_apply (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2))
    (g x : G) : mulLeft hmul g x = g * x :=
  (rfl)

/-- Right multiplication by `g` as a bundled smooth map when multiplication on `G` is smooth. -/
@[to_additive
/-- Right addition by `g` as a bundled smooth map when addition on `G` is smooth. -/]
def mulRight (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2)) (g : G) :
    DSmoothMap G G :=
  ⟨(· * g), hmul.comp (_root_.Diffeology.dSmooth_id.prodMk _root_.Diffeology.dSmooth_const)⟩

@[to_additive (attr := simp, grind =)]
theorem mulRight_apply (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2))
    (g x : G) : mulRight hmul g x = x * g :=
  (rfl)

/-- The left-translation family `g ↦ (x ↦ g * x)` is smooth into `DSmoothMap G G`. -/
@[to_additive
/-- The left-translation family `g ↦ (x ↦ g + x)` is smooth into `DSmoothMap G G`. -/]
theorem dSmooth_mulLeft (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2)) :
    _root_.Diffeology.DSmooth (mulLeft hmul) :=
  dSmooth_iff_uncurry.mpr hmul

/-- The right-translation family `g ↦ (x ↦ x * g)` is smooth into `DSmoothMap G G`. -/
@[to_additive
/-- The right-translation family `g ↦ (x ↦ x + g)` is smooth into `DSmoothMap G G`. -/]
theorem dSmooth_mulRight (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2)) :
    _root_.Diffeology.DSmooth (mulRight hmul) :=
  dSmooth_iff_uncurry.mpr (hmul.comp dSmooth_swap)

end Mul

/-! ### Continuity of evaluation -/

/-- When `X` is locally compact and `DSmoothMap X Y`, `X`, and `Y` carry topologies compatible
with their D-topologies, evaluation `DSmoothMap X Y × X → Y` is continuous for the product
topology. -/
@[fun_prop]
theorem continuous_eval
    [TopologicalSpace (DSmoothMap X Y)] [_root_.Diffeology.IsDTopologyCompatible (DSmoothMap X Y)]
    [TopologicalSpace X] [_root_.Diffeology.IsDTopologyCompatible X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [_root_.Diffeology.IsDTopologyCompatible Y] :
    Continuous (fun q : DSmoothMap X Y × X ↦ q.1 q.2) :=
  dSmooth_eval.continuous'

end DSmoothMap

namespace DSmoothEquiv

variable {X₁ X₂ Y₁ Y₂ : Type*} [DiffeologicalSpace X₁] [DiffeologicalSpace X₂]
  [DiffeologicalSpace Y₁] [DiffeologicalSpace Y₂]

/-- Diffeomorphic domains and codomains induce diffeomorphic mapping spaces. -/
def arrowCongr (e₁ : DSmoothEquiv X₁ X₂) (e₂ : DSmoothEquiv Y₁ Y₂) :
    DSmoothEquiv (DSmoothMap X₁ Y₁) (DSmoothMap X₂ Y₂) :=
  ofDSmoothMap
    ((DSmoothMap.postcomp X₂ e₂.toDSmoothMap).comp (DSmoothMap.precomp Y₁ e₁.symm.toDSmoothMap))
    ((DSmoothMap.postcomp X₁ e₂.symm.toDSmoothMap).comp (DSmoothMap.precomp Y₂ e₁.toDSmoothMap))
    (DSmoothMap.ext fun f ↦ DSmoothMap.ext fun x ↦ by simp)
    (DSmoothMap.ext fun g ↦ DSmoothMap.ext fun x ↦ by simp)

@[simp, grind =]
theorem arrowCongr_apply (e₁ : DSmoothEquiv X₁ X₂) (e₂ : DSmoothEquiv Y₁ Y₂)
    (f : DSmoothMap X₁ Y₁) (x : X₂) :
    e₁.arrowCongr e₂ f x = e₂ (f (e₁.symm x)) :=
  (rfl)

@[simp]
theorem arrowCongr_symm (e₁ : DSmoothEquiv X₁ X₂) (e₂ : DSmoothEquiv Y₁ Y₂) :
    (e₁.arrowCongr e₂).symm = e₁.symm.arrowCongr e₂.symm := by
  ext g x
  simp [arrowCongr]

end DSmoothEquiv

end FunctionalDiffeology

end TauCeti.Diffeology
