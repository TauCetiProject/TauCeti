/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen
public import TauCeti.Geometry.Diffeology.Equiv
public import TauCeti.Geometry.Diffeology.Induced
public import TauCeti.Geometry.Diffeology.Prod

/-!
# Functional diffeologies and Cartesian closedness

For diffeological spaces `X` and `Y`, the bundled smooth maps `TauCeti.Diffeology.DSmoothMap X Y`
carry a canonical *functional diffeology*: a parametrization `p : 𝔼ⁿ → DSmoothMap X Y` is a plot
if and only if its uncurried evaluation `(u, x) ↦ p u x` is smooth on `𝔼ⁿ × X`. With this
diffeology, evaluation `DSmoothMap X Y × X → Y` is smooth, currying identifies smooth maps
`Z × X → Y` with smooth maps `Z → DSmoothMap X Y` (`DSmoothMap.dSmooth_iff`), currying is a
diffeological diffeomorphism `DSmoothMap (Z × X) Y ≃ DSmoothMap Z (DSmoothMap X Y)`
(`DSmoothMap.curryEquiv`), and composition `DSmoothMap Y Z × DSmoothMap X Y → DSmoothMap X Z` is
smooth (`DSmoothMap.dSmooth_comp`). Diffeological spaces therefore form a Cartesian closed category.
Diffeomorphic domains and codomains give diffeomorphic mapping spaces
(`DSmoothEquiv.arrowCongr`), and on a type with smooth multiplication the left and right
translation families `G → DSmoothMap G G` are smooth (`DSmoothMap.dSmooth_mulLeft`,
`DSmoothMap.dSmooth_mulRight`).

On the topological side:

* When `X` and `Y` carry topologies compatible with their D-topologies, forgetting smoothness
  `DSmoothMap X Y → C(X, Y)` is continuous from the functional D-topology to the compact-open
  topology (`DSmoothMap.continuous_toContinuousMap`), without any local compactness assumption.
* When in addition `X` is locally compact, the D-topology of `DSmoothMap X Y × X` equals the
  product of the functional D-topology with the topology of `X`
  (`dTopology_prod_eq_of_isDTopologyCompatible_right`), so evaluation is jointly continuous
  (`DSmoothMap.continuous_eval`).
* For a one-point domain `[Unique X]` (such as `PUnit`), evaluation at the unique point is a
  diffeological isomorphism `DSmoothMap X Y ≃ Y` (`DSmoothMap.uniqueEquiv`).
* Evaluation at a point is continuous whenever `DSmoothMap X Y` and `Y` carry D-topology-compatible
  topologies (`DSmoothMap.instContinuousEvalConst`), and joint evaluation is continuous whenever
  `DSmoothMap X Y × X` and `Y` do (`DSmoothMap.instContinuousEval`).

## Main declarations

* `TauCeti.Diffeology.DSmoothMap`: bundled diffeologically smooth maps `X → Y`.
* `TauCeti.Diffeology.DSmoothMap.instDiffeologicalSpace`: the functional diffeology on
  `DSmoothMap X Y`.
* `TauCeti.Diffeology.DSmoothMap.dSmooth_eval`, `Diffeology.DSmooth.eval`, and
  `TauCeti.Diffeology.DSmoothMap.eval`: smoothness of the evaluation map `DSmoothMap X Y × X → Y`.
* `TauCeti.Diffeology.DSmoothMap.dSmooth_iff`, `TauCeti.Diffeology.DSmoothMap.curry`,
  `TauCeti.Diffeology.DSmoothMap.uncurry`, `TauCeti.Diffeology.DSmoothMap.curryEquiv`: the
  exponential law for diffeological spaces.
* `TauCeti.Diffeology.DSmoothMap.dSmooth_comp`, `TauCeti.Diffeology.DSmoothMap.compMap`: smoothness
  of composition.
* `TauCeti.Diffeology.DSmoothEquiv.toDSmoothMap`, `TauCeti.Diffeology.DSmoothEquiv.ofDSmoothMap`,
  `TauCeti.Diffeology.DSmoothEquiv.arrowCongr`: diffeomorphisms as bundled smooth maps and the
  induced diffeomorphisms of mapping spaces.
* `TauCeti.Diffeology.DSmoothMap.mulLeft`, `TauCeti.Diffeology.DSmoothMap.mulRight`,
  `TauCeti.Diffeology.DSmoothMap.dSmooth_mulLeft`, `TauCeti.Diffeology.DSmoothMap.dSmooth_mulRight`:
  smooth translation families.
* `TauCeti.Diffeology.DSmoothMap.uniqueEquiv`: diffeological identification `DSmoothMap X Y ≃ Y`
  for `[Unique X]`.
* `TauCeti.Diffeology.DSmoothMap.continuous_toContinuousMap` and
  `TauCeti.Diffeology.DSmoothMap.continuous_eval`: comparison of the functional D-topology with
  the compact-open topology and joint continuity of evaluation on locally compact domains.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), §1.57–1.60 for functional diffeologies, smooth evaluation, and
  currying.
* J. D. Christensen, G. Sinnamon, and E. Wu, *The D-topology for diffeological spaces*, Pacific J.
  Math. **272** (2014), 87–110, §4 for the D-topology of functional diffeologies and continuity of
  evaluation.
-/

public noncomputable section

open Function Set
open scoped ContDiff Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

/-! ### Bundled diffeologically smooth maps -/

/-- Bundled diffeologically smooth maps from `X` to `Y`. -/
structure DSmoothMap (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y] where
  /-- The underlying function of a bundled smooth map. -/
  protected toFun : X → Y
  /-- Smoothness of the underlying function. -/
  protected dSmooth_toFun : _root_.Diffeology.DSmooth toFun

namespace DSmoothMap

variable {X Y Z W : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y]
  [DiffeologicalSpace Z] [DiffeologicalSpace W]

/-- Coercion from bundled smooth maps to functions. -/
instance instFunLike : FunLike (DSmoothMap X Y) X Y where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

/-- Coercion to a function agrees with `DSmoothMap.toFun`. -/
@[simp]
theorem toFun_eq_coe (f : DSmoothMap X Y) : f.toFun = f :=
  (rfl)

/-- Evaluating a bundled smooth map constructed by `DSmoothMap.mk` applies the underlying map. -/
@[simp]
theorem coe_mk (f : X → Y) (hf : _root_.Diffeology.DSmooth f) :
    ⇑(⟨f, hf⟩ : DSmoothMap X Y) = f :=
  (rfl)

/-- Rebuilding a bundled smooth map from its coercion recovers the original map. -/
@[simp]
theorem mk_coe (f : DSmoothMap X Y) (hf : _root_.Diffeology.DSmooth f) :
    (⟨f, hf⟩ : DSmoothMap X Y) = f :=
  (rfl)

/-- Two bundled smooth maps are equal if and only if they agree at every point. -/
@[ext]
theorem ext {f g : DSmoothMap X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Replace the underlying function of a `DSmoothMap` by a definitionally convenient equal map. -/
protected def copy (f : DSmoothMap X Y) (f' : X → Y) (h : f' = f) : DSmoothMap X Y :=
  ⟨f', h.symm ▸ f.dSmooth_toFun⟩

/-- Coercing `DSmoothMap.copy` returns the replacement function. -/
@[simp]
theorem coe_copy (f : DSmoothMap X Y) (f' : X → Y) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  (rfl)

/-- `DSmoothMap.copy` is equal to the original bundled smooth map. -/
theorem copy_eq (f : DSmoothMap X Y) (f' : X → Y) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

/-- Every bundled smooth map is diffeologically smooth. -/
@[fun_prop]
protected theorem dSmooth (f : DSmoothMap X Y) : _root_.Diffeology.DSmooth f :=
  f.dSmooth_toFun

/-- Every bundled smooth map is continuous for the D-topologies of its domain and codomain. -/
protected theorem continuous_dTopology (f : DSmoothMap X Y) :
    @Continuous X Y _root_.Diffeology.dTopology _root_.Diffeology.dTopology f :=
  f.dSmooth.continuous

/-- Between spaces whose topologies agree with their D-topologies, every bundled smooth map is
continuous. -/
@[fun_prop]
protected theorem continuous [TopologicalSpace X] [_root_.Diffeology.IsDTopologyCompatible X]
    [TopologicalSpace Y] [_root_.Diffeology.IsDTopologyCompatible Y] (f : DSmoothMap X Y) :
    Continuous f :=
  f.dSmooth.continuous'

/-- The identity map as a bundled smooth map. -/
protected def id : DSmoothMap X X :=
  ⟨_root_.id, _root_.Diffeology.dSmooth_id⟩

/-- Coercing `DSmoothMap.id` gives the identity function. -/
@[simp]
theorem coe_id : ⇑(DSmoothMap.id : DSmoothMap X X) = _root_.id :=
  (rfl)

/-- Evaluating `DSmoothMap.id` at `x` returns `x`. -/
@[simp]
theorem id_apply (x : X) : (DSmoothMap.id : DSmoothMap X X) x = x :=
  (rfl)

/-- Default bundled smooth map into an inhabited diffeological space. -/
instance [Inhabited Y] : Inhabited (DSmoothMap X Y) :=
  ⟨⟨fun _ ↦ default, _root_.Diffeology.dSmooth_const⟩⟩

/-- The constant map at `y` as a bundled smooth map. -/
def const (y : Y) : DSmoothMap X Y :=
  ⟨Function.const X y, _root_.Diffeology.dSmooth_const⟩

/-- Coercing `DSmoothMap.const y` gives `Function.const X y`. -/
@[simp]
theorem coe_const (y : Y) : ⇑(const y : DSmoothMap X Y) = Function.const X y :=
  (rfl)

/-- Evaluating `DSmoothMap.const y` at any point returns `y`. -/
@[simp]
theorem const_apply (y : Y) (x : X) : (const y : DSmoothMap X Y) x = y :=
  (rfl)

/-- Composition of bundled smooth maps. -/
def comp (g : DSmoothMap Y Z) (f : DSmoothMap X Y) : DSmoothMap X Z :=
  ⟨g ∘ f, g.dSmooth.comp f.dSmooth⟩

/-- Coercing `g.comp f` gives function composition `g ∘ f`. -/
@[simp]
theorem coe_comp (g : DSmoothMap Y Z) (f : DSmoothMap X Y) : ⇑(g.comp f) = g ∘ f :=
  (rfl)

/-- Evaluating `g.comp f` at `x` returns `g (f x)`. -/
@[simp]
theorem comp_apply (g : DSmoothMap Y Z) (f : DSmoothMap X Y) (x : X) : (g.comp f) x = g (f x) :=
  (rfl)

/-- Right identity law for `DSmoothMap.comp`. -/
@[simp]
theorem comp_id (f : DSmoothMap X Y) : f.comp DSmoothMap.id = f :=
  (rfl)

/-- Left identity law for `DSmoothMap.comp`. -/
@[simp]
theorem id_comp (f : DSmoothMap X Y) : DSmoothMap.id.comp f = f :=
  (rfl)

/-- Associativity of `DSmoothMap.comp`. -/
@[simp]
theorem comp_assoc (h : DSmoothMap Z W) (g : DSmoothMap Y Z) (f : DSmoothMap X Y) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  (rfl)

/-- Composing a constant map on the left yields the same constant map. -/
@[simp]
theorem const_comp (z : Z) (f : DSmoothMap X Y) : (const z).comp f = const z :=
  (rfl)

/-- Composing a bundled smooth map with a constant map yields a constant map. -/
@[simp]
theorem comp_const (g : DSmoothMap Y Z) (y : Y) : g.comp (const y : DSmoothMap X Y) = const (g y) :=
  (rfl)

/-- The first projection of a product as a bundled smooth map. -/
def fst : DSmoothMap (X × Y) X :=
  ⟨Prod.fst, dSmooth_fst⟩

/-- Coercing `DSmoothMap.fst` gives `Prod.fst`. -/
@[simp]
theorem coe_fst : ⇑(fst : DSmoothMap (X × Y) X) = Prod.fst :=
  (rfl)

/-- Evaluating `DSmoothMap.fst` at `p` returns `p.1`. -/
@[simp]
theorem fst_apply (p : X × Y) : (fst : DSmoothMap (X × Y) X) p = p.1 :=
  (rfl)

/-- The second projection of a product as a bundled smooth map. -/
def snd : DSmoothMap (X × Y) Y :=
  ⟨Prod.snd, dSmooth_snd⟩

/-- Coercing `DSmoothMap.snd` gives `Prod.snd`. -/
@[simp]
theorem coe_snd : ⇑(snd : DSmoothMap (X × Y) Y) = Prod.snd :=
  (rfl)

/-- Evaluating `DSmoothMap.snd` at `p` returns `p.2`. -/
@[simp]
theorem snd_apply (p : X × Y) : (snd : DSmoothMap (X × Y) Y) p = p.2 :=
  (rfl)

/-- Pairing two bundled smooth maps with common domain into a product space. -/
def prodMk (f : DSmoothMap Z X) (g : DSmoothMap Z Y) : DSmoothMap Z (X × Y) :=
  ⟨fun z ↦ (f z, g z), f.dSmooth.prodMk g.dSmooth⟩

/-- Coercing `f.prodMk g` gives `fun z ↦ (f z, g z)`. -/
@[simp]
theorem coe_prodMk (f : DSmoothMap Z X) (g : DSmoothMap Z Y) :
    ⇑(f.prodMk g) = fun z ↦ (f z, g z) :=
  (rfl)

/-- Evaluating `f.prodMk g` at `z` returns `(f z, g z)`. -/
@[simp]
theorem prodMk_apply (f : DSmoothMap Z X) (g : DSmoothMap Z Y) (z : Z) :
    (f.prodMk g) z = (f z, g z) :=
  (rfl)

/-- Composing `DSmoothMap.fst` with `f.prodMk g` recovers `f`. -/
@[simp]
theorem fst_comp_prodMk (f : DSmoothMap Z X) (g : DSmoothMap Z Y) : fst.comp (f.prodMk g) = f :=
  (rfl)

/-- Composing `DSmoothMap.snd` with `f.prodMk g` recovers `g`. -/
@[simp]
theorem snd_comp_prodMk (f : DSmoothMap Z X) (g : DSmoothMap Z Y) : snd.comp (f.prodMk g) = g :=
  (rfl)

/-- Product of two bundled smooth maps on product spaces. -/
def prodMap (f : DSmoothMap X Z) (g : DSmoothMap Y W) : DSmoothMap (X × Y) (Z × W) :=
  ⟨Prod.map f g, f.dSmooth.prodMap g.dSmooth⟩

/-- Coercing `f.prodMap g` gives `Prod.map f g`. -/
@[simp]
theorem coe_prodMap (f : DSmoothMap X Z) (g : DSmoothMap Y W) :
    ⇑(f.prodMap g) = Prod.map f g :=
  (rfl)

/-- Evaluating `f.prodMap g` at `p` returns `(f p.1, g p.2)`. -/
@[simp]
theorem prodMap_apply (f : DSmoothMap X Z) (g : DSmoothMap Y W) (p : X × Y) :
    (f.prodMap g) p = (f p.1, g p.2) :=
  (rfl)

/-- Inclusion of a subtype carrying the subspace diffeology as a bundled smooth map. -/
def subtypeVal (s : Set X) : DSmoothMap s X :=
  ⟨Subtype.val, dSmooth_subtype_val⟩

/-- Coercing `DSmoothMap.subtypeVal s` gives `Subtype.val`. -/
@[simp]
theorem coe_subtypeVal (s : Set X) : ⇑(subtypeVal s) = Subtype.val :=
  (rfl)

/-- Evaluating `DSmoothMap.subtypeVal s` at `x` returns `x.1`. -/
@[simp]
theorem subtypeVal_apply (s : Set X) (x : s) : subtypeVal s x = x.val :=
  (rfl)

/-- The coercion from bundled smooth maps to functions is injective. -/
theorem coe_injective : Injective ((⇑) : DSmoothMap X Y → X → Y) :=
  DFunLike.coe_injective

/-- Composing a plot with a bundled smooth map gives a plot. -/
protected theorem isPlot_comp (f : DSmoothMap X Y) {n : ℕ} {p : 𝔼ⁿ → X}
    (hp : _root_.Diffeology.IsPlot p) : _root_.Diffeology.IsPlot (f ∘ p) :=
  f.dSmooth n p hp

/-- A bundled smooth map into a product is the pairing of its two components. -/
@[simp]
theorem prod_eta (f : DSmoothMap Z (X × Y)) : (fst.comp f).prodMk (snd.comp f) = f :=
  ext fun _ ↦ rfl

/-- Restrict the codomain of a bundled smooth map to a subset carrying the subspace diffeology. -/
def codRestrict (f : DSmoothMap X Y) (s : Set Y) (hs : ∀ x, f x ∈ s) : DSmoothMap X s :=
  ⟨s.codRestrict f hs, f.dSmooth.subtype_mk hs⟩

/-- The value of `f.codRestrict s hs` at `x` is `f x`. -/
@[simp]
theorem coe_codRestrict_apply (f : DSmoothMap X Y) (s : Set Y) (hs : ∀ x, f x ∈ s) (x : X) :
    (f.codRestrict s hs x : Y) = f x :=
  (rfl)

/-- Composing `f.codRestrict s hs` with the subtype inclusion recovers `f`. -/
@[simp]
theorem subtypeVal_comp_codRestrict (f : DSmoothMap X Y) (s : Set Y) (hs : ∀ x, f x ∈ s) :
    (subtypeVal s).comp (f.codRestrict s hs) = f :=
  ext fun _ ↦ rfl

/-! ### The functional diffeology -/

/-- The functional diffeology on `DSmoothMap X Y`: a parametrization `p : 𝔼ⁿ → DSmoothMap X Y` is a
plot if and only if its uncurried evaluation `(u, x) ↦ p u x` is smooth on `𝔼ⁿ × X`. See
Iglesias-Zemmour, *Diffeology*, §1.57. -/
instance instDiffeologicalSpace : DiffeologicalSpace (DSmoothMap X Y) where
  plots n := {p | _root_.Diffeology.DSmooth fun ux : 𝔼ⁿ × X ↦ p ux.1 ux.2}
  constant_plots f := f.dSmooth.comp dSmooth_snd
  plot_reparam hp hf := hp.comp (hf.dSmooth.prodMap _root_.Diffeology.dSmooth_id)
  locality {n p} hp := fun k q hq ↦ by
    apply DiffeologicalSpace.locality
    intro z
    have hq1 : ContDiff ℝ ∞ (Prod.fst ∘ q) :=
      _root_.Diffeology.isPlot_iff_contDiff.mp (isPlot_prod_iff.mp hq).1
    obtain ⟨u, hu, hzu, hpu⟩ := hp (q z).1
    refine ⟨(Prod.fst ∘ q) ⁻¹' u, hu.preimage hq1.continuous, hzu, fun {l r} hru hr ↦ ?_⟩
    have hpu' := hpu (f := (Prod.fst ∘ q) ∘ r) hru (hq1.comp hr)
    have harg : _root_.Diffeology.IsPlot (fun w : 𝔼ˡ ↦ (w, (q (r w)).2)) :=
      isPlot_prod_iff.mpr ⟨_root_.Diffeology.isPlot_id,
        (_root_.Diffeology.isPlot_reparam hq hr).dSmooth_comp dSmooth_snd⟩
    exact hpu' l _ harg

/-- A parametrization into `DSmoothMap X Y` is a plot of the functional diffeology if and only if
its uncurried evaluation `(u, x) ↦ p u x` is smooth on `𝔼ⁿ × X`. -/
theorem isPlot_iff {n : ℕ} {p : 𝔼ⁿ → DSmoothMap X Y} :
    _root_.Diffeology.IsPlot p ↔ _root_.Diffeology.DSmooth (fun ux : 𝔼ⁿ × X ↦ p ux.1 ux.2) :=
  (Iff.rfl)

/-- A map into `DSmoothMap X Y` is a local plot on a subset `u ⊆ 𝔼ⁿ` if and only if its uncurried
evaluation is smooth on `u × X` (where `u` carries the subspace diffeology). -/
theorem isPlotOn_iff {n : ℕ} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → DSmoothMap X Y} :
    TauCeti.Diffeology.IsPlotOn u p ↔
      _root_.Diffeology.DSmooth (fun ux : u × X ↦ p ux.1.val ux.2) := by
  constructor
  · intro hp m q hq
    have hq1 : ContDiff ℝ ∞ (fun v ↦ (q v).1.val) :=
      _root_.Diffeology.isPlot_iff_contDiff.mp (isPlot_subtype_iff.mp (isPlot_prod_iff.mp hq).1)
    have hpq : _root_.Diffeology.IsPlot (p ∘ fun v ↦ (q v).1.val) :=
      hp.isPlot_comp (fun v _ ↦ (q v).1.property) hq1
    have harg : _root_.Diffeology.IsPlot (fun v : 𝔼ᵐ ↦ (v, (q v).2)) :=
      isPlot_prod_iff.mpr ⟨_root_.Diffeology.isPlot_id, (isPlot_prod_iff.mp hq).2⟩
    exact isPlot_iff.mp hpq m _ harg
  · refine fun h ↦ TauCeti.Diffeology.isPlotOn_iff.mpr fun {m} f hfu hf ↦ isPlot_iff.mpr ?_
    have hfsub : _root_.Diffeology.DSmooth (fun v : 𝔼ᵐ ↦ (⟨f v, hfu (mem_univ v)⟩ : u)) :=
      hf.dSmooth.subtype_mk fun v ↦ hfu (mem_univ v)
    exact h.comp (hfsub.prodMap _root_.Diffeology.dSmooth_id)

end DSmoothMap

/-! ### Diffeomorphisms as bundled smooth maps -/

namespace DSmoothEquiv

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

/-- View a diffeological diffeomorphism as a bundled smooth map. -/
def toDSmoothMap (e : DSmoothEquiv X Y) : DSmoothMap X Y :=
  ⟨e, e.dSmooth⟩

/-- Coercing `e.toDSmoothMap` gives `e`. -/
@[simp]
theorem coe_toDSmoothMap (e : DSmoothEquiv X Y) : ⇑e.toDSmoothMap = ⇑e :=
  (rfl)

/-- Evaluating `e.toDSmoothMap` at `x` returns `e x`. -/
@[simp]
theorem toDSmoothMap_apply (e : DSmoothEquiv X Y) (x : X) : e.toDSmoothMap x = e x :=
  (rfl)

/-- `DSmoothEquiv.toDSmoothMap` is injective. -/
theorem toDSmoothMap_injective :
    Injective (toDSmoothMap : DSmoothEquiv X Y → DSmoothMap X Y) :=
  fun _ _ h ↦ ext fun x ↦ congr($(h) x)

/-- The identity diffeomorphism is the identity bundled smooth map. -/
@[simp]
theorem toDSmoothMap_refl : (DSmoothEquiv.refl X).toDSmoothMap = DSmoothMap.id :=
  DSmoothMap.ext fun _ ↦ by simp

/-- `DSmoothEquiv.toDSmoothMap` turns composition of diffeomorphisms into composition of maps. -/
@[simp]
theorem toDSmoothMap_trans (e₁ : DSmoothEquiv X Y) (e₂ : DSmoothEquiv Y Z) :
    (e₁.trans e₂).toDSmoothMap = e₂.toDSmoothMap.comp e₁.toDSmoothMap :=
  DSmoothMap.ext fun _ ↦ by simp

/-- A diffeomorphism followed by its inverse is the identity bundled smooth map. -/
@[simp]
theorem symm_comp_toDSmoothMap (e : DSmoothEquiv X Y) :
    e.symm.toDSmoothMap.comp e.toDSmoothMap = DSmoothMap.id :=
  DSmoothMap.ext e.symm_apply_apply

/-- The inverse of a diffeomorphism followed by the diffeomorphism is the identity bundled smooth
map. -/
@[simp]
theorem toDSmoothMap_comp_symm (e : DSmoothEquiv X Y) :
    e.toDSmoothMap.comp e.symm.toDSmoothMap = DSmoothMap.id :=
  DSmoothMap.ext e.apply_symm_apply

/-- Construct a diffeological diffeomorphism from mutually inverse bundled smooth maps. -/
def ofDSmoothMap (f : DSmoothMap X Y) (g : DSmoothMap Y X)
    (h₁ : g.comp f = DSmoothMap.id) (h₂ : f.comp g = DSmoothMap.id) : DSmoothEquiv X Y :=
  mk ⟨f, g, fun x ↦ congr($(h₁) x), fun y ↦ congr($(h₂) y)⟩ f.dSmooth g.dSmooth

/-- Coercing `ofDSmoothMap f g h₁ h₂` gives `f`. -/
@[simp]
theorem coe_ofDSmoothMap (f : DSmoothMap X Y) (g : DSmoothMap Y X)
    (h₁ : g.comp f = DSmoothMap.id) (h₂ : f.comp g = DSmoothMap.id) :
    ⇑(ofDSmoothMap f g h₁ h₂) = ⇑f :=
  (rfl)

/-- Viewing `ofDSmoothMap f g h₁ h₂` as a bundled smooth map gives `f`. -/
@[simp]
theorem toDSmoothMap_ofDSmoothMap (f : DSmoothMap X Y) (g : DSmoothMap Y X)
    (h₁ : g.comp f = DSmoothMap.id) (h₂ : f.comp g = DSmoothMap.id) :
    (ofDSmoothMap f g h₁ h₂).toDSmoothMap = f :=
  (rfl)

/-- The inverse of `ofDSmoothMap f g h₁ h₂` is `ofDSmoothMap g f h₂ h₁`. -/
@[simp]
theorem ofDSmoothMap_symm (f : DSmoothMap X Y) (g : DSmoothMap Y X)
    (h₁ : g.comp f = DSmoothMap.id) (h₂ : f.comp g = DSmoothMap.id) :
    (ofDSmoothMap f g h₁ h₂).symm = ofDSmoothMap g f h₂ h₁ :=
  ext fun _ ↦ by simp [ofDSmoothMap]

end DSmoothEquiv

/-! ### Smooth evaluation, currying, and composition -/

section ExponentialLaw

variable {X Y Z W : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y]
  [DiffeologicalSpace Z] [DiffeologicalSpace W]

namespace DSmoothMap

/-- Evaluation `DSmoothMap X Y × X → Y` is diffeologically smooth. See Iglesias-Zemmour,
*Diffeology*, §1.57. -/
@[fun_prop]
theorem dSmooth_eval : _root_.Diffeology.DSmooth (fun fx : DSmoothMap X Y × X ↦ fx.1 fx.2) := by
  intro n q hq
  obtain ⟨hq1, hq2⟩ := isPlot_prod_iff.mp hq
  exact isPlot_iff.mp hq1 n (fun u ↦ (u, (q u).2))
    (isPlot_prod_iff.mpr ⟨_root_.Diffeology.isPlot_id, hq2⟩)

/-- Pointwise evaluation of a smooth family of bundled smooth maps along a smooth argument is
smooth. -/
@[fun_prop]
protected theorem _root_.Diffeology.DSmooth.eval {f : Z → DSmoothMap X Y} {g : Z → X}
    (hf : _root_.Diffeology.DSmooth f) (hg : _root_.Diffeology.DSmooth g) :
    _root_.Diffeology.DSmooth (fun z ↦ f z (g z)) :=
  dSmooth_eval.comp (hf.prodMk hg)

/-- **Exponential law for diffeological spaces.** A map `Z → DSmoothMap X Y` is smooth for the
functional diffeology if and only if its uncurried map `Z × X → Y` is smooth. See Iglesias-Zemmour,
*Diffeology*, §1.59. -/
theorem dSmooth_iff {f : Z → DSmoothMap X Y} :
    _root_.Diffeology.DSmooth f ↔ _root_.Diffeology.DSmooth (fun zx : Z × X ↦ f zx.1 zx.2) :=
  ⟨fun hf ↦ (hf.comp dSmooth_fst).eval dSmooth_snd,
    fun hf _ _ hp ↦ isPlot_iff.mpr (hf.comp (hp.dSmooth.prodMap
      _root_.Diffeology.dSmooth_id))⟩

/-- Composition `DSmoothMap Y Z × DSmoothMap X Y → DSmoothMap X Z` is diffeologically smooth. See
Iglesias-Zemmour, *Diffeology*, §1.58. -/
@[fun_prop]
theorem dSmooth_comp :
    _root_.Diffeology.DSmooth (fun gf : DSmoothMap Y Z × DSmoothMap X Y ↦ gf.1.comp gf.2) :=
  dSmooth_iff.mpr
    ((dSmooth_fst.comp dSmooth_fst).eval ((dSmooth_snd.comp dSmooth_fst).eval dSmooth_snd))

/-- Pointwise composition of two smooth families of bundled smooth maps is smooth. -/
@[fun_prop]
protected theorem _root_.Diffeology.DSmooth.comp_dSmoothMap {g : W → DSmoothMap Y Z}
    {f : W → DSmoothMap X Y} (hg : _root_.Diffeology.DSmooth g)
    (hf : _root_.Diffeology.DSmooth f) :
    _root_.Diffeology.DSmooth (fun w ↦ (g w).comp (f w)) :=
  dSmooth_comp.comp (hg.prodMk hf)

/-- Evaluation as a bundled smooth map `DSmoothMap X Y × X → Y`. -/
def eval : DSmoothMap (DSmoothMap X Y × X) Y :=
  ⟨fun fx ↦ fx.1 fx.2, dSmooth_eval⟩

/-- Coercing `DSmoothMap.eval` gives `fun fx ↦ fx.1 fx.2`. -/
@[simp]
theorem coe_eval : ⇑(eval : DSmoothMap (DSmoothMap X Y × X) Y) = fun fx ↦ fx.1 fx.2 :=
  (rfl)

/-- Evaluating `DSmoothMap.eval` at `(f, x)` returns `f x`. -/
@[simp]
theorem eval_apply (f : DSmoothMap X Y) (x : X) : eval (f, x) = f x :=
  (rfl)

/-- Evaluation at a fixed point `x : X` as a bundled smooth map `DSmoothMap X Y → Y`. -/
def evalAt (x : X) : DSmoothMap (DSmoothMap X Y) Y :=
  ⟨fun f ↦ f x, _root_.Diffeology.dSmooth_id.eval _root_.Diffeology.dSmooth_const⟩

/-- Coercing `DSmoothMap.evalAt x` gives `fun f ↦ f x`. -/
@[simp]
theorem coe_evalAt (x : X) : ⇑(evalAt x : DSmoothMap (DSmoothMap X Y) Y) = fun f ↦ f x :=
  (rfl)

/-- Evaluating `DSmoothMap.evalAt x` at `f` returns `f x`. -/
@[simp]
theorem evalAt_apply (x : X) (f : DSmoothMap X Y) : evalAt x f = f x :=
  (rfl)

/-- Evaluation at a fixed point `x : X` is diffeologically smooth on `DSmoothMap X Y`. -/
@[fun_prop]
theorem dSmooth_evalAt (x : X) :
    _root_.Diffeology.DSmooth (fun f : DSmoothMap X Y ↦ f x) :=
  (evalAt x).dSmooth

/-- Evaluating a smooth family `f : Z → DSmoothMap X Y` at a fixed point `x : X` is smooth. -/
@[fun_prop]
protected theorem _root_.Diffeology.DSmooth.eval_const {f : Z → DSmoothMap X Y}
    (hf : _root_.Diffeology.DSmooth f) (x : X) : _root_.Diffeology.DSmooth (f · x) :=
  (dSmooth_evalAt x).comp hf

/-- Curry a bundled smooth map `Z × X → Y` into a bundled smooth map `Z → DSmoothMap X Y`. -/
def curry (f : DSmoothMap (Z × X) Y) : DSmoothMap Z (DSmoothMap X Y) :=
  ⟨fun z ↦ ⟨fun x ↦ f (z, x),
      f.dSmooth.comp ((_root_.Diffeology.dSmooth_const (y := z)).prodMk
        _root_.Diffeology.dSmooth_id)⟩,
    DSmoothMap.dSmooth_iff.mpr f.dSmooth⟩

/-- Evaluating `f.curry` at `z` and `x` returns `f (z, x)`. -/
@[simp]
theorem curry_apply (f : DSmoothMap (Z × X) Y) (z : Z) (x : X) : f.curry z x = f (z, x) :=
  (rfl)

/-- Uncurry a bundled smooth map `Z → DSmoothMap X Y` into a bundled smooth map `Z × X → Y`. -/
def uncurry (g : DSmoothMap Z (DSmoothMap X Y)) : DSmoothMap (Z × X) Y :=
  ⟨fun zx ↦ g zx.1 zx.2, DSmoothMap.dSmooth_iff.mp g.dSmooth⟩

/-- Coercing `g.uncurry` gives `fun zx ↦ g zx.1 zx.2`. -/
@[simp]
theorem coe_uncurry (g : DSmoothMap Z (DSmoothMap X Y)) :
    ⇑g.uncurry = fun zx ↦ g zx.1 zx.2 :=
  (rfl)

/-- Evaluating `g.uncurry` at `zx` returns `g zx.1 zx.2`. -/
@[simp]
theorem uncurry_apply (g : DSmoothMap Z (DSmoothMap X Y)) (zx : Z × X) :
    g.uncurry zx = g zx.1 zx.2 :=
  (rfl)

/-- Uncurrying `f.curry` recovers `f`. -/
@[simp]
theorem uncurry_curry (f : DSmoothMap (Z × X) Y) : f.curry.uncurry = f := by
  ext ⟨z, x⟩
  rfl

/-- Currying `g.uncurry` recovers `g`. -/
@[simp]
theorem curry_uncurry (g : DSmoothMap Z (DSmoothMap X Y)) : g.uncurry.curry = g := by
  ext z x
  rfl

/-- Currying is diffeologically smooth between the functional diffeologies. -/
@[fun_prop]
theorem dSmooth_curry :
    _root_.Diffeology.DSmooth (curry : DSmoothMap (Z × X) Y → DSmoothMap Z (DSmoothMap X Y)) :=
  DSmoothMap.dSmooth_iff.mpr <| DSmoothMap.dSmooth_iff.mpr <|
    (dSmooth_fst.comp dSmooth_fst).eval ((dSmooth_snd.comp dSmooth_fst).prodMk dSmooth_snd)

/-- Uncurrying is diffeologically smooth between the functional diffeologies. -/
@[fun_prop]
theorem dSmooth_uncurry :
    _root_.Diffeology.DSmooth (uncurry : DSmoothMap Z (DSmoothMap X Y) → DSmoothMap (Z × X) Y) :=
  DSmoothMap.dSmooth_iff.mpr <|
    (dSmooth_fst.eval (dSmooth_fst.comp dSmooth_snd)).eval (dSmooth_snd.comp dSmooth_snd)

/-- Currying is an induction (hence a diffeological isomorphism) between `DSmoothMap (Z × X) Y`
and `DSmoothMap Z (DSmoothMap X Y)`. -/
theorem isInduction_curry :
    IsInduction (curry : DSmoothMap (Z × X) Y → DSmoothMap Z (DSmoothMap X Y)) :=
  (LeftInverse.isInduction uncurry_curry) dSmooth_curry dSmooth_uncurry

/-- Uncurrying is an induction (hence a diffeological isomorphism) between
`DSmoothMap Z (DSmoothMap X Y)` and `DSmoothMap (Z × X) Y`. -/
theorem isInduction_uncurry :
    IsInduction (uncurry : DSmoothMap Z (DSmoothMap X Y) → DSmoothMap (Z × X) Y) :=
  (LeftInverse.isInduction curry_uncurry) dSmooth_uncurry dSmooth_curry

/-- **Exponential law for diffeological spaces.** Currying and uncurrying form a diffeological
diffeomorphism `DSmoothMap (Z × X) Y ≃ DSmoothMap Z (DSmoothMap X Y)`. -/
def curryEquiv : DSmoothEquiv (DSmoothMap (Z × X) Y) (DSmoothMap Z (DSmoothMap X Y)) :=
  DSmoothEquiv.ofDSmoothMap ⟨curry, dSmooth_curry⟩ ⟨uncurry, dSmooth_uncurry⟩
    (ext uncurry_curry) (ext curry_uncurry)

/-- Applying `DSmoothMap.curryEquiv` applies `DSmoothMap.curry`. -/
@[simp]
theorem curryEquiv_apply (f : DSmoothMap (Z × X) Y) : curryEquiv f = f.curry :=
  (rfl)

/-- Applying `DSmoothMap.curryEquiv.symm` applies `DSmoothMap.uncurry`. -/
@[simp]
theorem curryEquiv_symm_apply (g : DSmoothMap Z (DSmoothMap X Y)) :
    curryEquiv.symm g = g.uncurry := by
  simp [curryEquiv]

/-- Composition as a bundled smooth map `DSmoothMap Y Z × DSmoothMap X Y → DSmoothMap X Z`. -/
def compMap : DSmoothMap (DSmoothMap Y Z × DSmoothMap X Y) (DSmoothMap X Z) :=
  ⟨fun gf ↦ gf.1.comp gf.2, dSmooth_comp⟩

/-- Coercing `DSmoothMap.compMap` gives `fun gf ↦ gf.1.comp gf.2`. -/
@[simp]
theorem coe_compMap :
    ⇑(compMap : DSmoothMap (DSmoothMap Y Z × DSmoothMap X Y) (DSmoothMap X Z)) =
      fun gf ↦ gf.1.comp gf.2 :=
  (rfl)

/-- Evaluating `DSmoothMap.compMap` at `(g, f)` returns `g.comp f`. -/
@[simp]
theorem compMap_apply (g : DSmoothMap Y Z) (f : DSmoothMap X Y) : compMap (g, f) = g.comp f :=
  (rfl)

/-- Postcomposition with `g : DSmoothMap Y Z` as a bundled smooth map
`DSmoothMap X Y → DSmoothMap X Z`. -/
def postcomp (g : DSmoothMap Y Z) : DSmoothMap (DSmoothMap X Y) (DSmoothMap X Z) :=
  ⟨g.comp, dSmooth_comp.comp ((_root_.Diffeology.dSmooth_const (y := g)).prodMk
    _root_.Diffeology.dSmooth_id)⟩

/-- Coercing `DSmoothMap.postcomp g` gives `g.comp`. -/
@[simp]
theorem coe_postcomp (g : DSmoothMap Y Z) :
    ⇑(postcomp g : DSmoothMap (DSmoothMap X Y) (DSmoothMap X Z)) = g.comp :=
  (rfl)

/-- Evaluating `DSmoothMap.postcomp g` at `f` returns `g.comp f`. -/
@[simp]
theorem postcomp_apply (g : DSmoothMap Y Z) (f : DSmoothMap X Y) : postcomp g f = g.comp f :=
  (rfl)

/-- Precomposition with `f : DSmoothMap X Y` as a bundled smooth map
`DSmoothMap Y Z → DSmoothMap X Z`. -/
def precomp (f : DSmoothMap X Y) : DSmoothMap (DSmoothMap Y Z) (DSmoothMap X Z) :=
  ⟨fun g ↦ g.comp f, dSmooth_comp.comp (_root_.Diffeology.dSmooth_id.prodMk
    (_root_.Diffeology.dSmooth_const (y := f)))⟩

/-- Coercing `DSmoothMap.precomp f` gives `fun g ↦ g.comp f`. -/
@[simp]
theorem coe_precomp (f : DSmoothMap X Y) :
    ⇑(precomp f : DSmoothMap (DSmoothMap Y Z) (DSmoothMap X Z)) = fun g ↦ g.comp f :=
  (rfl)

/-- Evaluating `DSmoothMap.precomp f` at `g` returns `g.comp f`. -/
@[simp]
theorem precomp_apply (f : DSmoothMap X Y) (g : DSmoothMap Y Z) : precomp f g = g.comp f :=
  (rfl)

/-- Postcomposition with the identity is the identity. -/
@[simp]
theorem postcomp_id :
    (postcomp DSmoothMap.id : DSmoothMap (DSmoothMap X Y) (DSmoothMap X Y)) = DSmoothMap.id :=
  ext id_comp

/-- Postcomposition is functorial. -/
@[simp]
theorem postcomp_comp (h : DSmoothMap Z W) (g : DSmoothMap Y Z) :
    (postcomp h).comp (postcomp g : DSmoothMap (DSmoothMap X Y) (DSmoothMap X Z)) =
      postcomp (h.comp g) :=
  (rfl)

/-- Precomposition with the identity is the identity. -/
@[simp]
theorem precomp_id :
    (precomp DSmoothMap.id : DSmoothMap (DSmoothMap X Y) (DSmoothMap X Y)) = DSmoothMap.id :=
  ext comp_id

/-- Precomposition is contravariantly functorial. -/
@[simp]
theorem precomp_comp (g : DSmoothMap Y W) (f : DSmoothMap X Y) :
    (precomp f).comp (precomp g : DSmoothMap (DSmoothMap W Z) (DSmoothMap Y Z)) =
      precomp (g.comp f) :=
  (rfl)

/-- Sending `y : Y` to the constant map `const y : DSmoothMap X Y` is smooth. -/
@[fun_prop]
protected theorem dSmooth_const : _root_.Diffeology.DSmooth (const : Y → DSmoothMap X Y) :=
  DSmoothMap.dSmooth_iff.mpr dSmooth_fst

/-- Inclusion of constant maps `Y → DSmoothMap X Y` as a bundled smooth map. -/
def constMap : DSmoothMap Y (DSmoothMap X Y) :=
  ⟨const, DSmoothMap.dSmooth_const⟩

/-- Coercing `DSmoothMap.constMap` gives `DSmoothMap.const`. -/
@[simp]
theorem coe_constMap : ⇑(constMap : DSmoothMap Y (DSmoothMap X Y)) = const :=
  (rfl)

/-- Evaluating `DSmoothMap.constMap` at `y` returns `DSmoothMap.const y`. -/
@[simp]
theorem constMap_apply (y : Y) : (constMap : DSmoothMap Y (DSmoothMap X Y)) y = const y :=
  (rfl)

/-- When `X` is nonempty, the inclusion of constant maps `Y → DSmoothMap X Y` is an induction. -/
theorem isInduction_const [Nonempty X] : IsInduction (const : Y → DSmoothMap X Y) :=
  let ⟨x⟩ := ‹Nonempty X›
  (LeftInverse.isInduction fun _ ↦ rfl) DSmoothMap.dSmooth_const (dSmooth_evalAt x)

/-! ### Smooth multiplication and translation families -/

section Mul

variable {G : Type*} [Mul G] [DiffeologicalSpace G]

/-- Left multiplication by `g` as a bundled smooth map when multiplication on `G` is smooth. -/
@[to_additive
/-- Left addition by `g` as a bundled smooth map when addition on `G` is smooth. -/]
def mulLeft (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2)) (g : G) :
    DSmoothMap G G :=
  ⟨(g * ·), hmul.comp (_root_.Diffeology.dSmooth_const.prodMk _root_.Diffeology.dSmooth_id)⟩

/-- Evaluating `DSmoothMap.mulLeft hmul g` at `x` returns `g * x`. -/
@[to_additive (attr := simp)
/-- Evaluating `DSmoothMap.addLeft hadd g` at `x` returns `g + x`. -/]
theorem mulLeft_apply (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2)) (g x : G) :
    mulLeft hmul g x = g * x :=
  (rfl)

/-- Right multiplication by `g` as a bundled smooth map when multiplication on `G` is smooth. -/
@[to_additive
/-- Right addition by `g` as a bundled smooth map when addition on `G` is smooth. -/]
def mulRight (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2)) (g : G) :
    DSmoothMap G G :=
  ⟨(· * g), hmul.comp (_root_.Diffeology.dSmooth_id.prodMk _root_.Diffeology.dSmooth_const)⟩

/-- Evaluating `DSmoothMap.mulRight hmul g` at `x` returns `x * g`. -/
@[to_additive (attr := simp)
/-- Evaluating `DSmoothMap.addRight hadd g` at `x` returns `x + g`. -/]
theorem mulRight_apply (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2)) (g x : G) :
    mulRight hmul g x = x * g :=
  (rfl)

/-- The left-translation family `g ↦ (x ↦ g * x)` is smooth into `DSmoothMap G G`. -/
@[to_additive (attr := fun_prop)
/-- The left-translation family `g ↦ (x ↦ g + x)` is smooth into `DSmoothMap G G`. -/]
theorem dSmooth_mulLeft (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2)) :
    _root_.Diffeology.DSmooth (mulLeft hmul) :=
  dSmooth_iff.mpr hmul

/-- The right-translation family `g ↦ (x ↦ x * g)` is smooth into `DSmoothMap G G`. -/
@[to_additive (attr := fun_prop)
/-- The right-translation family `g ↦ (x ↦ x + g)` is smooth into `DSmoothMap G G`. -/]
theorem dSmooth_mulRight (hmul : _root_.Diffeology.DSmooth (fun p : G × G ↦ p.1 * p.2)) :
    _root_.Diffeology.DSmooth (mulRight hmul) :=
  dSmooth_iff.mpr (hmul.comp dSmooth_swap)

end Mul

/-! ### Point-domain identification -/

section Unique

variable [Unique X]

/-- When `X` has a unique point, evaluation at `default` identifies `DSmoothMap X Y` with `Y` as a
diffeological space, with inverse `DSmoothMap.constMap`. -/
def uniqueEquiv : DSmoothEquiv (DSmoothMap X Y) Y :=
  DSmoothEquiv.ofDSmoothMap (evalAt default) constMap
    (ext fun f ↦ ext fun x ↦ congrArg f (Subsingleton.elim default x)) (ext fun _ ↦ rfl)

/-- Evaluating `DSmoothMap.uniqueEquiv` at `f` returns `f default`. -/
@[simp]
theorem uniqueEquiv_apply (f : DSmoothMap X Y) : uniqueEquiv f = f default :=
  (rfl)

/-- Evaluating `DSmoothMap.uniqueEquiv.symm` at `y` returns `DSmoothMap.const y`. -/
@[simp]
theorem uniqueEquiv_symm_apply (y : Y) : (uniqueEquiv (X := X)).symm y = const y := by
  simp [uniqueEquiv]

end Unique

/-! ### D-topology, compact-open topology, and locally compact evaluation -/

section Topology

variable [TopologicalSpace X] [_root_.Diffeology.IsDTopologyCompatible X]
  [TopologicalSpace Y] [_root_.Diffeology.IsDTopologyCompatible Y]

/-- Bundled smooth maps between D-topology-compatible spaces form a `ContinuousMapClass`. -/
instance instContinuousMapClass : ContinuousMapClass (DSmoothMap X Y) X Y where
  map_continuous f := f.continuous

/-- Coercing `DSmoothMap.id` to `C(X, X)` yields `ContinuousMap.id X`. -/
@[simp]
theorem toContinuousMap_id :
    ((DSmoothMap.id : DSmoothMap X X) : C(X, X)) = ContinuousMap.id X :=
  (rfl)

/-- Coercing `DSmoothMap.const y` to `C(X, Y)` yields `ContinuousMap.const X y`. -/
@[simp]
theorem toContinuousMap_const (y : Y) :
    ((const y : DSmoothMap X Y) : C(X, Y)) = ContinuousMap.const X y :=
  (rfl)

/-- Coercing `g.comp f` to `C(X, Z)` commutes with composition. -/
@[simp]
theorem toContinuousMap_comp [TopologicalSpace Z] [_root_.Diffeology.IsDTopologyCompatible Z]
    (g : DSmoothMap Y Z) (f : DSmoothMap X Y) :
    ((g.comp f : DSmoothMap X Z) : C(X, Z)) = (g : C(Y, Z)).comp (f : C(X, Y)) :=
  (rfl)

/-- Forgetting smoothness `DSmoothMap X Y → C(X, Y)` is continuous from the functional D-topology
to the compact-open topology, without any local compactness assumption on `X`. -/
theorem continuous_toContinuousMap :
    @Continuous (DSmoothMap X Y) C(X, Y) _root_.Diffeology.dTopology inferInstance
      (fun f : DSmoothMap X Y ↦ (f : C(X, Y))) := by
  refine continuous_dTopology_dom_iff.mpr fun n p hp ↦ ?_
  refine ContinuousMap.continuous_of_continuous_uncurry (fun u ↦ (p u : C(X, Y))) ?_
  exact (isPlot_iff.mp hp).continuous'

/-- When `X` is locally compact and `X`, `Y` carry topologies compatible with their D-topologies,
evaluation `(DSmoothMap X Y, dTopology) × X → Y` is jointly continuous. -/
theorem continuous_eval [LocallyCompactSpace X] :
    @Continuous (DSmoothMap X Y × X) Y
      (@instTopologicalSpaceProd (DSmoothMap X Y) X _root_.Diffeology.dTopology
        ‹TopologicalSpace X›)
      ‹TopologicalSpace Y› (fun fx ↦ fx.1 fx.2) := by
  have hc := (dSmooth_eval (X := X) (Y := Y)).continuous
  rwa [dTopology_prod_eq_of_isDTopologyCompatible_right,
    _root_.Diffeology.IsDTopologyCompatible.dTop_eq Y] at hc

end Topology

/-- When `DSmoothMap X Y` and `Y` carry topologies compatible with their D-topologies, evaluation
at any fixed point `x : X` is continuous. -/
instance instContinuousEvalConst
    [TopologicalSpace (DSmoothMap X Y)] [_root_.Diffeology.IsDTopologyCompatible (DSmoothMap X Y)]
    [TopologicalSpace Y] [_root_.Diffeology.IsDTopologyCompatible Y] :
    ContinuousEvalConst (DSmoothMap X Y) X Y where
  continuous_eval_const x := (dSmooth_evalAt x).continuous'

/-- When `DSmoothMap X Y × X` and `Y` carry topologies compatible with their D-topologies (for
instance when `DSmoothMap X Y` and `X` are D-topology-compatible and `X` is locally compact), joint
evaluation `DSmoothMap X Y × X → Y` is continuous for the product topology. -/
instance instContinuousEval
    [TopologicalSpace (DSmoothMap X Y)] [TopologicalSpace X]
    [_root_.Diffeology.IsDTopologyCompatible (DSmoothMap X Y × X)]
    [TopologicalSpace Y] [_root_.Diffeology.IsDTopologyCompatible Y] :
    ContinuousEval (DSmoothMap X Y) X Y where
  continuous_eval := dSmooth_eval.continuous'

end DSmoothMap

namespace DSmoothEquiv

variable {X₁ X₂ Y₁ Y₂ : Type*} [DiffeologicalSpace X₁] [DiffeologicalSpace X₂]
  [DiffeologicalSpace Y₁] [DiffeologicalSpace Y₂]

/-- Diffeomorphic domains and codomains induce diffeomorphic mapping spaces. -/
def arrowCongr (e₁ : DSmoothEquiv X₁ X₂) (e₂ : DSmoothEquiv Y₁ Y₂) :
    DSmoothEquiv (DSmoothMap X₁ Y₁) (DSmoothMap X₂ Y₂) :=
  ofDSmoothMap
    ((DSmoothMap.postcomp e₂.toDSmoothMap).comp (DSmoothMap.precomp e₁.symm.toDSmoothMap))
    ((DSmoothMap.postcomp e₂.symm.toDSmoothMap).comp (DSmoothMap.precomp e₁.toDSmoothMap))
    (DSmoothMap.ext fun _ ↦ DSmoothMap.ext fun _ ↦ by simp)
    (DSmoothMap.ext fun _ ↦ DSmoothMap.ext fun _ ↦ by simp)

/-- Evaluating `e₁.arrowCongr e₂ f` at `x` returns `e₂ (f (e₁.symm x))`. -/
@[simp]
theorem arrowCongr_apply (e₁ : DSmoothEquiv X₁ X₂) (e₂ : DSmoothEquiv Y₁ Y₂)
    (f : DSmoothMap X₁ Y₁) (x : X₂) : e₁.arrowCongr e₂ f x = e₂ (f (e₁.symm x)) :=
  (rfl)

/-- The inverse of `e₁.arrowCongr e₂` is `e₁.symm.arrowCongr e₂.symm`. -/
@[simp]
theorem arrowCongr_symm (e₁ : DSmoothEquiv X₁ X₂) (e₂ : DSmoothEquiv Y₁ Y₂) :
    (e₁.arrowCongr e₂).symm = e₁.symm.arrowCongr e₂.symm := by
  ext
  simp [arrowCongr]

end DSmoothEquiv

end ExponentialLaw

end TauCeti.Diffeology
