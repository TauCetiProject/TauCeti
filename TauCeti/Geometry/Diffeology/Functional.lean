/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen
public import TauCeti.Geometry.Diffeology.Induced
public import TauCeti.Geometry.Diffeology.Prod

/-!
# Functional diffeologies and Cartesian closedness

For diffeological spaces `X` and `Y`, the bundled smooth maps `TauCeti.Diffeology.DSmoothMap X Y`
carry a canonical *functional diffeology*: a parametrization `p : 𝔼ⁿ → DSmoothMap X Y` is a plot
if and only if its uncurried evaluation `(u, x) ↦ p u x` is smooth on `𝔼ⁿ × X`. With this
diffeology, evaluation `DSmoothMap X Y × X → Y` is smooth, currying identifies smooth maps
`Z × X → Y` with smooth maps `Z → DSmoothMap X Y` (`dSmooth_curry_iff`, `DSmoothMap.curryEquiv`),
and composition `DSmoothMap Y Z × DSmoothMap X Y → DSmoothMap X Z` is smooth (`dSmooth_comp`).
Diffeological spaces therefore form a Cartesian closed category.

On the topological side:

* When `X` and `Y` carry topologies compatible with their D-topologies, forgetting smoothness
  `DSmoothMap X Y → C(X, Y)` is continuous from the functional D-topology to the compact-open
  topology (`DSmoothMap.continuous_toContinuousMap`), without any local compactness assumption.
* When in addition `X` is locally compact, the D-topology of `DSmoothMap X Y × X` equals the
  product of the functional D-topology with the topology of `X` (`DSmoothMap.dTopology_prod_eq`),
  so evaluation is jointly continuous (`DSmoothMap.continuous_eval`).
* For a one-point domain `[Unique X]` (such as `PUnit`), evaluation at the unique point is a
  diffeological isomorphism `DSmoothMap X Y ≃ Y` (`DSmoothMap.uniqueEquiv`).

## Main declarations

* `TauCeti.Diffeology.instDiffeologicalSpacePUnit`: the canonical diffeology on `PUnit`.
* `TauCeti.Diffeology.DSmoothMap`: bundled diffeologically smooth maps `X → Y`.
* `TauCeti.Diffeology.DSmoothMap.instDiffeologicalSpace`: the functional diffeology on
  `DSmoothMap X Y`.
* `TauCeti.Diffeology.dSmooth_eval`, `Diffeology.DSmooth.eval`, and
  `TauCeti.Diffeology.DSmoothMap.eval`: smoothness of the evaluation map `DSmoothMap X Y × X → Y`.
* `TauCeti.Diffeology.dSmooth_curry_iff`, `TauCeti.Diffeology.DSmoothMap.curry`,
  `TauCeti.Diffeology.DSmoothMap.uncurry`, `TauCeti.Diffeology.DSmoothMap.curryEquiv`: the
  exponential law for diffeological spaces.
* `TauCeti.Diffeology.dSmooth_comp`, `TauCeti.Diffeology.DSmoothMap.compMap`: smoothness of
  composition.
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

/-! ### The point diffeology on `PUnit` -/

/-- The canonical diffeology on `PUnit`, in which every parametrization is a plot and the
D-topology is definitionally the standard topology. -/
instance instDiffeologicalSpacePUnit : DiffeologicalSpace PUnit where
  plots _ := univ
  constant_plots _ := trivial
  plot_reparam _ _ := trivial
  locality _ := trivial
  dTopology := inferInstance
  isOpen_iff_preimages_plots {u} := by
    rcases u.eq_empty_or_nonempty with rfl | ⟨⟨⟩, hu⟩
    · exact ⟨fun _ _ _ _ ↦ isOpen_empty, fun _ ↦ isOpen_empty⟩
    · obtain rfl : u = univ := eq_univ_of_forall fun ⟨⟩ ↦ hu
      exact ⟨fun _ _ _ _ ↦ isOpen_univ, fun _ ↦ isOpen_univ⟩

/-- The D-topology of `PUnit` agrees with its standard topology. -/
instance instIsDTopologyCompatiblePUnit : _root_.Diffeology.IsDTopologyCompatible PUnit :=
  ⟨rfl⟩

/-- Every parametrization of `PUnit` is a plot. -/
theorem isPlot_punit {n : ℕ} (p : 𝔼ⁿ → PUnit) : _root_.Diffeology.IsPlot p :=
  trivial

/-- Every map from a diffeological space to `PUnit` is smooth. -/
@[fun_prop]
theorem dSmooth_punit {X : Type*} [DiffeologicalSpace X] (f : X → PUnit) :
    _root_.Diffeology.DSmooth f :=
  fun _ _ _ ↦ trivial

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
    Continuous f := by
  rw [← _root_.Diffeology.IsDTopologyCompatible.dTop_eq X,
    ← _root_.Diffeology.IsDTopologyCompatible.dTop_eq Y]
  exact f.continuous_dTopology

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
theorem subtypeVal_apply (s : Set X) (x : s) : subtypeVal s x = x.1 :=
  (rfl)

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
      _root_.Diffeology.DSmooth (fun ux : u × X ↦ p ux.1.1 ux.2) := by
  constructor
  · intro hp m q hq
    have hq1 : ContDiff ℝ ∞ (fun v ↦ (q v).1.1) :=
      _root_.Diffeology.isPlot_iff_contDiff.mp (isPlot_subtype_iff.mp (isPlot_prod_iff.mp hq).1)
    have hpq : _root_.Diffeology.IsPlot (p ∘ fun v ↦ (q v).1.1) :=
      hp.isPlot_comp (fun v _ ↦ (q v).1.2) hq1
    have harg : _root_.Diffeology.IsPlot (fun v : 𝔼ᵐ ↦ (v, (q v).2)) :=
      isPlot_prod_iff.mpr ⟨_root_.Diffeology.isPlot_id, (isPlot_prod_iff.mp hq).2⟩
    exact isPlot_iff.mp hpq m _ harg
  · refine fun h ↦ TauCeti.Diffeology.isPlotOn_iff.mpr fun {m} f hfu hf ↦ isPlot_iff.mpr ?_
    have hfsub : _root_.Diffeology.DSmooth (fun v : 𝔼ᵐ ↦ (⟨f v, hfu (mem_univ v)⟩ : u)) :=
      hf.dSmooth.subtype_mk fun v ↦ hfu (mem_univ v)
    exact h.comp (hfsub.prodMap _root_.Diffeology.dSmooth_id)

end DSmoothMap

/-! ### Smooth evaluation, currying, and composition -/

section ExponentialLaw

variable {X Y Z W : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y]
  [DiffeologicalSpace Z] [DiffeologicalSpace W]

/-- Evaluation `DSmoothMap X Y × X → Y` is diffeologically smooth. See Iglesias-Zemmour,
*Diffeology*, §1.57. -/
@[fun_prop]
theorem dSmooth_eval : _root_.Diffeology.DSmooth (fun fx : DSmoothMap X Y × X ↦ fx.1 fx.2) := by
  intro n q hq
  obtain ⟨hq1, hq2⟩ := isPlot_prod_iff.mp hq
  exact DSmoothMap.isPlot_iff.mp hq1 n (fun u ↦ (u, (q u).2))
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
theorem dSmooth_curry_iff {f : Z → DSmoothMap X Y} :
    _root_.Diffeology.DSmooth f ↔ _root_.Diffeology.DSmooth (fun zx : Z × X ↦ f zx.1 zx.2) :=
  ⟨fun hf ↦ (hf.comp dSmooth_fst).eval dSmooth_snd,
    fun hf _ _ hp ↦ DSmoothMap.isPlot_iff.mpr (hf.comp (hp.dSmooth.prodMap
      _root_.Diffeology.dSmooth_id))⟩

/-- Composition `DSmoothMap Y Z × DSmoothMap X Y → DSmoothMap X Z` is diffeologically smooth. See
Iglesias-Zemmour, *Diffeology*, §1.58. -/
@[fun_prop]
theorem dSmooth_comp :
    _root_.Diffeology.DSmooth (fun gf : DSmoothMap Y Z × DSmoothMap X Y ↦ gf.1.comp gf.2) :=
  dSmooth_curry_iff.mpr
    ((dSmooth_fst.comp dSmooth_fst).eval ((dSmooth_snd.comp dSmooth_fst).eval dSmooth_snd))

namespace DSmoothMap

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

/-- Curry a bundled smooth map `Z × X → Y` into a bundled smooth map `Z → DSmoothMap X Y`. -/
def curry (f : DSmoothMap (Z × X) Y) : DSmoothMap Z (DSmoothMap X Y) :=
  ⟨fun z ↦ ⟨fun x ↦ f (z, x),
      f.dSmooth.comp ((_root_.Diffeology.dSmooth_const (y := z)).prodMk
        _root_.Diffeology.dSmooth_id)⟩,
    dSmooth_curry_iff.mpr f.dSmooth⟩

/-- Evaluating `f.curry` at `z` and `x` returns `f (z, x)`. -/
@[simp]
theorem curry_apply (f : DSmoothMap (Z × X) Y) (z : Z) (x : X) : f.curry z x = f (z, x) :=
  (rfl)

/-- Uncurry a bundled smooth map `Z → DSmoothMap X Y` into a bundled smooth map `Z × X → Y`. -/
def uncurry (g : DSmoothMap Z (DSmoothMap X Y)) : DSmoothMap (Z × X) Y :=
  ⟨fun zx ↦ g zx.1 zx.2, dSmooth_curry_iff.mp g.dSmooth⟩

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

/-- Currying as an equivalence `DSmoothMap (Z × X) Y ≃ DSmoothMap Z (DSmoothMap X Y)`. -/
def curryEquiv : DSmoothMap (Z × X) Y ≃ DSmoothMap Z (DSmoothMap X Y) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

/-- Applying `DSmoothMap.curryEquiv` applies `DSmoothMap.curry`. -/
@[simp]
theorem curryEquiv_apply (f : DSmoothMap (Z × X) Y) : curryEquiv f = f.curry :=
  (rfl)

/-- Applying `DSmoothMap.curryEquiv.symm` applies `DSmoothMap.uncurry`. -/
@[simp]
theorem curryEquiv_symm_apply (g : DSmoothMap Z (DSmoothMap X Y)) :
    curryEquiv.symm g = g.uncurry :=
  (rfl)

/-- Currying is diffeologically smooth between the functional diffeologies. -/
@[fun_prop]
theorem dSmooth_curry :
    _root_.Diffeology.DSmooth (curry : DSmoothMap (Z × X) Y → DSmoothMap Z (DSmoothMap X Y)) :=
  dSmooth_curry_iff.mpr <| dSmooth_curry_iff.mpr <|
    (dSmooth_fst.comp dSmooth_fst).eval ((dSmooth_snd.comp dSmooth_fst).prodMk dSmooth_snd)

/-- Uncurrying is diffeologically smooth between the functional diffeologies. -/
@[fun_prop]
theorem dSmooth_uncurry :
    _root_.Diffeology.DSmooth (uncurry : DSmoothMap Z (DSmoothMap X Y) → DSmoothMap (Z × X) Y) :=
  dSmooth_curry_iff.mpr <|
    (dSmooth_fst.eval (dSmooth_fst.comp dSmooth_snd)).eval (dSmooth_snd.comp dSmooth_snd)

/-- Currying is an induction (hence a diffeological isomorphism) between `DSmoothMap (Z × X) Y`
and `DSmoothMap Z (DSmoothMap X Y)`. -/
theorem isInduction_curry :
    IsInduction (curry : DSmoothMap (Z × X) Y → DSmoothMap Z (DSmoothMap X Y)) :=
  curryEquiv.left_inv.isInduction dSmooth_curry dSmooth_uncurry

/-- Uncurrying is an induction (hence a diffeological isomorphism) between
`DSmoothMap Z (DSmoothMap X Y)` and `DSmoothMap (Z × X) Y`. -/
theorem isInduction_uncurry :
    IsInduction (uncurry : DSmoothMap Z (DSmoothMap X Y) → DSmoothMap (Z × X) Y) :=
  curryEquiv.right_inv.isInduction dSmooth_uncurry dSmooth_curry

/-- Composition as a bundled smooth map `DSmoothMap Y Z × DSmoothMap X Y → DSmoothMap X Z`. -/
def compMap : DSmoothMap (DSmoothMap Y Z × DSmoothMap X Y) (DSmoothMap X Z) :=
  ⟨fun gf ↦ gf.1.comp gf.2, dSmooth_comp⟩

/-- Evaluating `DSmoothMap.compMap` at `(g, f)` returns `g.comp f`. -/
@[simp]
theorem compMap_apply (g : DSmoothMap Y Z) (f : DSmoothMap X Y) : compMap (g, f) = g.comp f :=
  (rfl)

/-- Postcomposition with `g : DSmoothMap Y Z` as a bundled smooth map
`DSmoothMap X Y → DSmoothMap X Z`. -/
def postcomp (g : DSmoothMap Y Z) : DSmoothMap (DSmoothMap X Y) (DSmoothMap X Z) :=
  ⟨g.comp, dSmooth_comp.comp ((_root_.Diffeology.dSmooth_const (y := g)).prodMk
    _root_.Diffeology.dSmooth_id)⟩

/-- Evaluating `DSmoothMap.postcomp g` at `f` returns `g.comp f`. -/
@[simp]
theorem postcomp_apply (g : DSmoothMap Y Z) (f : DSmoothMap X Y) : postcomp g f = g.comp f :=
  (rfl)

/-- Precomposition with `f : DSmoothMap X Y` as a bundled smooth map
`DSmoothMap Y Z → DSmoothMap X Z`. -/
def precomp (f : DSmoothMap X Y) : DSmoothMap (DSmoothMap Y Z) (DSmoothMap X Z) :=
  ⟨fun g ↦ g.comp f, dSmooth_comp.comp (_root_.Diffeology.dSmooth_id.prodMk
    (_root_.Diffeology.dSmooth_const (y := f)))⟩

/-- Evaluating `DSmoothMap.precomp f` at `g` returns `g.comp f`. -/
@[simp]
theorem precomp_apply (f : DSmoothMap X Y) (g : DSmoothMap Y Z) : precomp f g = g.comp f :=
  (rfl)

/-- Sending `y : Y` to the constant map `const y : DSmoothMap X Y` is smooth. -/
@[fun_prop]
theorem dSmooth_constMap : _root_.Diffeology.DSmooth (const : Y → DSmoothMap X Y) :=
  dSmooth_curry_iff.mpr dSmooth_fst

/-- Inclusion of constant maps `Y → DSmoothMap X Y` as a bundled smooth map. -/
def constMap : DSmoothMap Y (DSmoothMap X Y) :=
  ⟨const, dSmooth_constMap⟩

/-- Evaluating `DSmoothMap.constMap` at `y` returns `DSmoothMap.const y`. -/
@[simp]
theorem constMap_apply (y : Y) : (constMap : DSmoothMap Y (DSmoothMap X Y)) y = const y :=
  (rfl)

/-- When `X` is nonempty, the inclusion of constant maps `Y → DSmoothMap X Y` is an induction. -/
theorem isInduction_const [Nonempty X] : IsInduction (const : Y → DSmoothMap X Y) :=
  let ⟨x⟩ := ‹Nonempty X›
  (LeftInverse.isInduction fun _ ↦ rfl) dSmooth_constMap (dSmooth_evalAt x)

/-! ### Point-domain identification -/

section Unique

variable [Unique X]

/-- When `X` has a unique point, evaluation at `default` identifies `DSmoothMap X Y` with `Y`. -/
def uniqueEquiv : DSmoothMap X Y ≃ Y where
  toFun := evalAt default
  invFun := const
  left_inv f := by
    ext x
    rw [evalAt_apply, const_apply, Unique.eq_default x]
  right_inv _ := rfl

/-- Evaluating `DSmoothMap.uniqueEquiv` at `f` returns `f default`. -/
@[simp]
theorem uniqueEquiv_apply (f : DSmoothMap X Y) : uniqueEquiv f = f default :=
  (rfl)

/-- Evaluating `DSmoothMap.uniqueEquiv.symm` at `y` returns `DSmoothMap.const y`. -/
@[simp]
theorem uniqueEquiv_symm_apply (y : Y) : (uniqueEquiv (X := X)).symm y = const y :=
  (rfl)

/-- For `[Unique X]`, `uniqueEquiv : DSmoothMap X Y ≃ Y` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_uniqueEquiv : _root_.Diffeology.DSmooth (uniqueEquiv : DSmoothMap X Y → Y) :=
  dSmooth_evalAt default

/-- For `[Unique X]`, `uniqueEquiv.symm : Y ≃ DSmoothMap X Y` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_uniqueEquiv_symm :
    _root_.Diffeology.DSmooth ((uniqueEquiv (X := X) (Y := Y)).symm) :=
  dSmooth_constMap

/-- For `[Unique X]`, evaluation `uniqueEquiv : DSmoothMap X Y ≃ Y` is an induction (hence a
diffeological isomorphism). -/
theorem isInduction_uniqueEquiv : IsInduction (uniqueEquiv : DSmoothMap X Y → Y) :=
  uniqueEquiv.left_inv.isInduction dSmooth_uniqueEquiv dSmooth_uniqueEquiv_symm

/-- For `[Unique X]`, constant inclusion `uniqueEquiv.symm : Y ≃ DSmoothMap X Y` is an
induction. -/
theorem isInduction_uniqueEquiv_symm :
    IsInduction ((uniqueEquiv (X := X) (Y := Y)).symm) :=
  uniqueEquiv.right_inv.isInduction dSmooth_uniqueEquiv_symm dSmooth_uniqueEquiv

end Unique

/-! ### D-topology, compact-open topology, and locally compact evaluation -/

section Topology

variable [TopologicalSpace X] [_root_.Diffeology.IsDTopologyCompatible X]

/-- When `X` is locally compact and its topology agrees with its D-topology, the D-topology of
`DSmoothMap X Y × X` equals the product of the functional D-topology with the topology of `X`,
without requiring any topological structure on `Y`. -/
theorem dTopology_prod_eq [LocallyCompactSpace X] :
    (_root_.Diffeology.dTopology : TopologicalSpace (DSmoothMap X Y × X)) =
      @instTopologicalSpaceProd (DSmoothMap X Y) X _root_.Diffeology.dTopology
        ‹TopologicalSpace X› :=
  dTopology_prod_eq_of_isDTopologyCompatible_right

variable [TopologicalSpace Y] [_root_.Diffeology.IsDTopologyCompatible Y]

/-- Bundled smooth maps between D-topology-compatible spaces form a `ContinuousMapClass`. -/
instance instContinuousMapClass : ContinuousMapClass (DSmoothMap X Y) X Y where
  map_continuous f := f.continuous

/-- Forget smoothness to obtain a bundled continuous map `C(X, Y)`. -/
def toContinuousMap (f : DSmoothMap X Y) : C(X, Y) :=
  ⟨f, f.continuous⟩

/-- Coercing `f.toContinuousMap` recovers `f`. -/
@[simp]
theorem coe_toContinuousMap (f : DSmoothMap X Y) : ⇑f.toContinuousMap = f :=
  (rfl)

/-- Evaluating `f.toContinuousMap` at `x` returns `f x`. -/
@[simp]
theorem toContinuousMap_apply (f : DSmoothMap X Y) (x : X) : f.toContinuousMap x = f x :=
  (rfl)

/-- Forgetting smoothness `DSmoothMap X Y → C(X, Y)` is injective. -/
theorem toContinuousMap_injective : Injective (toContinuousMap : DSmoothMap X Y → C(X, Y)) :=
  fun _ _ h ↦ ext fun x ↦ congrArg (fun g : C(X, Y) ↦ g x) h

/-- Forgetting smoothness `DSmoothMap X Y → C(X, Y)` is continuous from the functional D-topology
to the compact-open topology, without any local compactness assumption on `X`. -/
theorem continuous_toContinuousMap :
    @Continuous (DSmoothMap X Y) C(X, Y) _root_.Diffeology.dTopology inferInstance
      toContinuousMap := by
  refine continuous_dTopology_dom_iff.mpr fun n p hp ↦ ?_
  refine ContinuousMap.continuous_of_continuous_uncurry (fun u ↦ (p u).toContinuousMap) ?_
  have hc := (isPlot_iff.mp hp).continuous
  rwa [dTopology_euclideanSpace_prod, _root_.Diffeology.IsDTopologyCompatible.dTop_eq X,
    _root_.Diffeology.IsDTopologyCompatible.dTop_eq Y] at hc

/-- When `X` is locally compact and `X`, `Y` carry topologies compatible with their D-topologies,
evaluation `(DSmoothMap X Y, dTopology) × X → Y` is jointly continuous. -/
theorem continuous_eval [LocallyCompactSpace X] :
    @Continuous (DSmoothMap X Y × X) Y
      (@instTopologicalSpaceProd (DSmoothMap X Y) X _root_.Diffeology.dTopology
        ‹TopologicalSpace X›)
      ‹TopologicalSpace Y› (fun fx ↦ fx.1 fx.2) := by
  have hc := (dSmooth_eval (X := X) (Y := Y)).continuous
  rwa [dTopology_prod_eq, _root_.Diffeology.IsDTopologyCompatible.dTop_eq Y] at hc

end Topology

end DSmoothMap

end ExponentialLaw

end TauCeti.Diffeology
