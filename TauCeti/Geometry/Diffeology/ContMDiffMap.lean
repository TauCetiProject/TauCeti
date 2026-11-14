/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import TauCeti.Geometry.Diffeology.Functional
public import TauCeti.Geometry.Diffeology.Manifold
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.ManifoldFamily

/-!
# Functional diffeologies on bundled smooth manifold maps

For finite-dimensional boundaryless smooth manifolds `M` and `N` carrying compatible diffeologies,
diffeologically smooth maps `M → N` coincide with ordinary smooth manifold maps
(`TauCeti.dSmooth_iff_contMDiff`). This file lifts that comparison to the mapping spaces
`C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` and `TauCeti.Diffeology.DSmoothMap M N`:

* `ContMDiffMap.toDSmoothMap` embeds `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` into `DSmoothMap M N` for any
  compatible charted spaces, and `TauCeti.Diffeology.DSmoothMap.equivContMDiffMap` upgrades this to
  a diffeological isomorphism when `M` is a finite-dimensional smooth manifold.
* `TauCeti.Diffeology.instDiffeologicalSpaceContMDiffMap` equips `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` with
  the functional diffeology induced along `ContMDiffMap.toDSmoothMap`. Smooth maps from any
  diffeological space `Z` into `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` correspond to smooth uncurried maps
  `Z × M → N` (`TauCeti.Diffeology.dSmooth_contMDiffMap_iff`). When `M` is a finite-dimensional
  smooth manifold, plots `p : 𝔼ⁿ → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` are precisely the parametrizations
  whose uncurried evaluation `𝔼ⁿ × M → N` is `C^∞` (`TauCeti.Diffeology.isPlot_contMDiffMap_iff`),
  and `TauCeti.Diffeology.contMDiffMapFunctionalDiffeology` constructs the same diffeology directly
  on manifolds without pre-installed diffeology instances.
* For any finite-dimensional smooth manifold `M` with a compatible diffeology, the product
  D-topology identity holds on `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ × M` without any Hausdorff assumption on
  `M`, making evaluation jointly continuous for the functional D-topology
  (`TauCeti.Diffeology.continuous_eval_contMDiffMap`).
* Moreover, every weak-Whitney open set of `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` is open in the functional
  D-topology (`TauCeti.Diffeology.dTopology_le_manifoldWeakWhitneyTopology`), via
  `ContMDiff.continuous_manifoldWeakWhitney`.
* Left and right translations (`smoothLeftMul`, `smoothRightMul`) on any manifold with smooth
  multiplication (`ContMDiffMul`) vary diffeologically smoothly in `C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯`.

## Main declarations

* `ContMDiffMap.toDSmoothMap`, `TauCeti.Diffeology.DSmoothMap.toContMDiffMap`, and
  `TauCeti.Diffeology.DSmoothMap.equivContMDiffMap`: mapping-space bridge between `ContMDiffMap`
  and `DSmoothMap`.
* `TauCeti.Diffeology.instDiffeologicalSpaceContMDiffMap` and
  `TauCeti.Diffeology.contMDiffMapFunctionalDiffeology`: functional diffeology on
  `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯`.
* `TauCeti.Diffeology.dSmooth_contMDiffMap_iff`, `ContMDiff.dSmooth_contMDiffMap`,
  `TauCeti.Diffeology.isPlot_contMDiffMap_iff`, and
  `TauCeti.Diffeology.dSmooth_contMDiffMap_iff_contMDiff`: exponential law and characterization of
  plots and smooth families via uncurried regularity.
* `TauCeti.Diffeology.continuous_eval_contMDiffMap` and
  `TauCeti.Diffeology.dTopology_le_manifoldWeakWhitneyTopology`: joint continuity of evaluation and
  comparison with the weak Whitney `C^∞` topology.
* `TauCeti.Diffeology.dSmooth_smoothLeftMul` and `TauCeti.Diffeology.dSmooth_smoothRightMul`:
  diffeological smoothness of left and right translation families.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), §1.15, §1.57–1.60, and §4.3.
* J. D. Christensen, G. Sinnamon, and E. Wu, *The D-topology for diffeological spaces*, Pacific J.
  Math. **272** (2014), 87–110, §4.
-/

public noncomputable section

open Function Set TauCeti TauCeti.Diffeology
open scoped ContDiff Manifold Topology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

/-! ### Dot-notation coercion from `ContMDiffMap` to `DSmoothMap` -/

namespace ContMDiffMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [DiffeologicalSpace M] [IsContMDiffCompatible E M]
  [TopologicalSpace N] [ChartedSpace F N] [DiffeologicalSpace N] [IsContMDiffCompatible F N]
  [TopologicalSpace P] [ChartedSpace G P] [DiffeologicalSpace P] [IsContMDiffCompatible G P]

/-- Every bundled `C^∞` manifold map between compatible charted spaces is diffeologically smooth. -/
@[fun_prop]
protected theorem dSmooth (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) : _root_.Diffeology.DSmooth f :=
  f.contMDiff.dSmooth

/-- Turn a bundled `C^∞` manifold map between compatible charted spaces into a bundled
diffeologically smooth map. Neither finite-dimensionality nor atlas smoothness is required. -/
def toDSmoothMap (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) : DSmoothMap M N :=
  ⟨f, f.dSmooth⟩

/-- Coercing `f.toDSmoothMap` recovers `f`. -/
@[simp]
theorem coe_toDSmoothMap (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) : ⇑f.toDSmoothMap = f :=
  (rfl)

/-- Evaluating `f.toDSmoothMap` at `x` returns `f x`. -/
@[simp]
theorem toDSmoothMap_apply (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) (x : M) :
    f.toDSmoothMap x = f x :=
  (rfl)

/-- `ContMDiffMap.toDSmoothMap` commutes with composition. -/
@[simp]
theorem toDSmoothMap_comp (g : C^∞⟮𝓘(ℝ, F), N; 𝓘(ℝ, G), P⟯)
    (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) :
    (g.comp f).toDSmoothMap = g.toDSmoothMap.comp f.toDSmoothMap := by
  ext x
  simp

end ContMDiffMap

/-! ### Functional diffeology and mapping-space bridge on `ContMDiffMap` -/

namespace TauCeti.Diffeology

section Compatible

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [DiffeologicalSpace M] [IsContMDiffCompatible E M]
  [TopologicalSpace N] [ChartedSpace F N] [DiffeologicalSpace N] [IsContMDiffCompatible F N]
  [TopologicalSpace P] [ChartedSpace G P] [DiffeologicalSpace P] [IsContMDiffCompatible G P]

/-- Embedding `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` into `DSmoothMap M N` is injective. -/
theorem toDSmoothMap_injective :
    Injective (ContMDiffMap.toDSmoothMap : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ → DSmoothMap M N) :=
  fun _ _ h ↦ ContMDiffMap.ext fun x ↦ congrArg (fun g : DSmoothMap M N ↦ g x) h

/-- `ContMDiffMap.toDSmoothMap` sends `ContMDiffMap.id` to `DSmoothMap.id`. -/
@[simp]
theorem toDSmoothMap_id :
    (ContMDiffMap.id : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, E), M⟯).toDSmoothMap = DSmoothMap.id := by
  ext x
  simp
  rfl

/-- `ContMDiffMap.toDSmoothMap` sends `ContMDiffMap.const y` to `DSmoothMap.const y`. -/
@[simp]
theorem toDSmoothMap_const (y : N) :
    (ContMDiffMap.const y : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯).toDSmoothMap = DSmoothMap.const y := by
  ext x
  simp

/-- The functional diffeology on `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯`, induced from `DSmoothMap M N` along
`ContMDiffMap.toDSmoothMap`. -/
instance instDiffeologicalSpaceContMDiffMap :
    DiffeologicalSpace C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ :=
  inducedDiffeology ContMDiffMap.toDSmoothMap

/-- `ContMDiffMap.toDSmoothMap` is an induction for the functional diffeologies. -/
theorem isInduction_toDSmoothMap :
    IsInduction (ContMDiffMap.toDSmoothMap : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ → DSmoothMap M N) :=
  ⟨toDSmoothMap_injective, isPlot_inducedDiffeology_iff ContMDiffMap.toDSmoothMap⟩

/-- `ContMDiffMap.toDSmoothMap` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_toDSmoothMap :
    _root_.Diffeology.DSmooth
      (ContMDiffMap.toDSmoothMap : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ → DSmoothMap M N) :=
  isInduction_toDSmoothMap.dSmooth

/-- Evaluation `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ × M → N` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_eval_contMDiffMap :
    _root_.Diffeology.DSmooth (fun fx : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ × M ↦ fx.1 fx.2) :=
  (dSmooth_toDSmoothMap.comp dSmooth_fst).eval dSmooth_snd

/-- Pointwise evaluation of a smooth family in `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` along a smooth
argument is diffeologically smooth. -/
@[fun_prop]
protected theorem _root_.Diffeology.DSmooth.eval_contMDiffMap {Z : Type*} [DiffeologicalSpace Z]
    {f : Z → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯} {g : Z → M}
    (hf : _root_.Diffeology.DSmooth f) (hg : _root_.Diffeology.DSmooth g) :
    _root_.Diffeology.DSmooth (fun z ↦ f z (g z)) :=
  dSmooth_eval_contMDiffMap.comp (hf.prodMk hg)

/-- Evaluation at a fixed point `x : M` is diffeologically smooth on
`C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯`. -/
@[fun_prop]
theorem dSmooth_evalAt_contMDiffMap (x : M) :
    _root_.Diffeology.DSmooth (fun f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ ↦ f x) :=
  _root_.Diffeology.dSmooth_id.eval_contMDiffMap _root_.Diffeology.dSmooth_const

/-- Composition `C^∞⟮𝓘(ℝ, F), N; 𝓘(ℝ, G), P⟯ × C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ →
C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, G), P⟯` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_comp_contMDiffMap :
    _root_.Diffeology.DSmooth
      (fun gf : C^∞⟮𝓘(ℝ, F), N; 𝓘(ℝ, G), P⟯ × C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ ↦ gf.1.comp gf.2) := by
  refine isInduction_toDSmoothMap.dSmooth_iff.mpr ?_
  have h := dSmooth_comp.comp
    ((dSmooth_toDSmoothMap (M := N) (N := P)).prodMap (dSmooth_toDSmoothMap (M := M) (N := N)))
  simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, ContMDiffMap.toDSmoothMap_comp] using h

/-- Pointwise composition of two smooth families of bundled `C^∞` manifold maps is
diffeologically smooth. -/
@[fun_prop]
protected theorem _root_.Diffeology.DSmooth.comp_contMDiffMap {Z : Type*} [DiffeologicalSpace Z]
    {g : Z → C^∞⟮𝓘(ℝ, F), N; 𝓘(ℝ, G), P⟯} {f : Z → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯}
    (hg : _root_.Diffeology.DSmooth g) (hf : _root_.Diffeology.DSmooth f) :
    _root_.Diffeology.DSmooth (fun z ↦ (g z).comp (f z)) :=
  dSmooth_comp_contMDiffMap.comp (hg.prodMk hf)

/-- Sending `y : N` to the constant map `ContMDiffMap.const y` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_const_contMDiffMap :
    _root_.Diffeology.DSmooth (ContMDiffMap.const : N → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) := by
  refine isInduction_toDSmoothMap.dSmooth_iff.mpr ?_
  simpa only [Function.comp_def, toDSmoothMap_const] using
    (DSmoothMap.dSmooth_const (X := M) (Y := N))

/-- **Exponential law on `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯`.** A map from any diffeological space `Z`
into `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` is diffeologically smooth if and only if its uncurried
evaluation `Z × M → N` is diffeologically smooth. -/
theorem dSmooth_contMDiffMap_iff {Z : Type*} [DiffeologicalSpace Z]
    {f : Z → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯} :
    _root_.Diffeology.DSmooth f ↔
      _root_.Diffeology.DSmooth (fun zm : Z × M ↦ f zm.1 zm.2) := by
  rw [isInduction_toDSmoothMap.dSmooth_iff, DSmoothMap.dSmooth_iff]
  simp only [Function.comp_apply, ContMDiffMap.toDSmoothMap_apply]

/-- A parametrization `p : 𝔼ⁿ → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` is a plot of the functional
diffeology if and only if its uncurried evaluation `𝔼ⁿ × M → N` is diffeologically smooth. -/
theorem isPlot_contMDiffMap_iff_dSmooth {n : ℕ} {p : 𝔼ⁿ → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯} :
    _root_.Diffeology.IsPlot p ↔
      _root_.Diffeology.DSmooth (fun ux : 𝔼ⁿ × M ↦ p ux.1 ux.2) := by
  rw [isPlot_inducedDiffeology_iff, DSmoothMap.isPlot_iff]
  simp only [Function.comp_apply, ContMDiffMap.toDSmoothMap_apply]

/-- Any family `f : P → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` whose uncurried evaluation `P × M → N` is
`C^∞` is diffeologically smooth, without requiring finite-dimensionality or atlas smoothness on
`P`, `M`, or `N`. -/
protected theorem _root_.ContMDiff.dSmooth_contMDiffMap
    {f : P → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯}
    (hf : ContMDiff (𝓘(ℝ, G).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (fun pm : P × M ↦ f pm.1 pm.2)) :
    _root_.Diffeology.DSmooth f :=
  dSmooth_contMDiffMap_iff.mpr hf.dSmooth_prod

end Compatible

namespace DSmoothMap

section ManifoldDomain

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [DiffeologicalSpace M] [IsContMDiffCompatible E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [DiffeologicalSpace N] [IsContMDiffCompatible F N]

/-- Turn a bundled diffeologically smooth map from a finite-dimensional smooth manifold `M` to a
compatible charted space `N` into a bundled `C^∞` manifold map. -/
def toContMDiffMap (f : DSmoothMap M N) : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ :=
  ⟨f, f.dSmooth.contMDiff⟩

/-- Coercing `f.toContMDiffMap` recovers `f`. -/
@[simp]
theorem coe_toContMDiffMap (f : DSmoothMap M N) : ⇑f.toContMDiffMap = f :=
  (rfl)

/-- Evaluating `f.toContMDiffMap` at `x` returns `f x`. -/
@[simp]
theorem toContMDiffMap_apply (f : DSmoothMap M N) (x : M) : f.toContMDiffMap x = f x :=
  (rfl)

/-- Converting `f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` to `DSmoothMap M N` and back recovers `f`. -/
@[simp]
theorem toContMDiffMap_toDSmoothMap (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) :
    f.toDSmoothMap.toContMDiffMap = f := by
  ext x
  rfl

/-- Converting `f : DSmoothMap M N` to `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` and back recovers `f`. -/
@[simp]
theorem toDSmoothMap_toContMDiffMap (f : DSmoothMap M N) :
    f.toContMDiffMap.toDSmoothMap = f := by
  ext x
  rfl

/-- Equivalence between `DSmoothMap M N` and `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` when `M` is a
finite-dimensional boundaryless smooth manifold. -/
def equivContMDiffMap : DSmoothMap M N ≃ C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ where
  toFun := toContMDiffMap
  invFun := ContMDiffMap.toDSmoothMap
  left_inv := toDSmoothMap_toContMDiffMap
  right_inv := toContMDiffMap_toDSmoothMap

/-- Applying `DSmoothMap.equivContMDiffMap` applies `DSmoothMap.toContMDiffMap`. -/
@[simp]
theorem equivContMDiffMap_apply (f : DSmoothMap M N) :
    equivContMDiffMap f = f.toContMDiffMap :=
  (rfl)

/-- Applying `DSmoothMap.equivContMDiffMap.symm` applies `ContMDiffMap.toDSmoothMap`. -/
@[simp]
theorem equivContMDiffMap_symm_apply (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) :
    equivContMDiffMap.symm f = f.toDSmoothMap :=
  (rfl)

/-- Converting `DSmoothMap M N` into `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` is injective. -/
theorem toContMDiffMap_injective :
    Injective (toContMDiffMap : DSmoothMap M N → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) :=
  equivContMDiffMap.injective

/-- `DSmoothMap.toContMDiffMap` sends `DSmoothMap.id` to `ContMDiffMap.id`. -/
@[simp]
theorem toContMDiffMap_id :
    (DSmoothMap.id : DSmoothMap M M).toContMDiffMap = ContMDiffMap.id := by
  ext x
  simp
  rfl

/-- `DSmoothMap.toContMDiffMap` sends `DSmoothMap.const y` to `ContMDiffMap.const y`. -/
@[simp]
theorem toContMDiffMap_const (y : N) :
    (DSmoothMap.const y : DSmoothMap M N).toContMDiffMap = ContMDiffMap.const y := by
  ext x
  simp

/-- `DSmoothMap.toContMDiffMap` commutes with composition when the intermediate space is also a
finite-dimensional smooth manifold. -/
@[simp]
theorem toContMDiffMap_comp {G P : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace P] [ChartedSpace G P] [DiffeologicalSpace P] [IsContMDiffCompatible G P]
    [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ, F) ∞ N]
    (g : DSmoothMap N P) (f : DSmoothMap M N) :
    (g.comp f).toContMDiffMap = g.toContMDiffMap.comp f.toContMDiffMap := by
  ext x
  simp

/-- `DSmoothMap.toContMDiffMap` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_toContMDiffMap :
    _root_.Diffeology.DSmooth (toContMDiffMap : DSmoothMap M N → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) := by
  refine isInduction_toDSmoothMap.dSmooth_iff.mpr ?_
  simpa only [Function.comp_def, toDSmoothMap_toContMDiffMap] using
    (_root_.Diffeology.dSmooth_id' (X := DSmoothMap M N))

/-- `DSmoothMap.toContMDiffMap` is an induction, hence a diffeological isomorphism between
`DSmoothMap M N` and `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯`. -/
theorem isInduction_toContMDiffMap :
    IsInduction (toContMDiffMap : DSmoothMap M N → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) :=
  equivContMDiffMap.left_inv.isInduction dSmooth_toContMDiffMap dSmooth_toDSmoothMap

end ManifoldDomain

end DSmoothMap

/-! ### Plot characterization and topology comparisons -/

section PlotsAndTopology

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]

/-- Direct construction of the functional diffeology on `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` for
manifolds `M` and `N` without requiring pre-installed `DiffeologicalSpace` instances on `M` or
`N`. Its plots are the parametrizations whose uncurried map `𝔼ⁿ × M → N` is `C^∞`. -/
@[instance_reducible]
def contMDiffMapFunctionalDiffeology (E M F N : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] :
    DiffeologicalSpace C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ :=
  let : DiffeologicalSpace M := manifoldDiffeology E M
  let : DiffeologicalSpace N := manifoldDiffeology F N
  instDiffeologicalSpaceContMDiffMap

variable [DiffeologicalSpace M] [IsContMDiffCompatible E M]
  [DiffeologicalSpace N] [IsContMDiffCompatible F N]

/-- A parametrization `p : 𝔼ⁿ → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` is a plot of the functional
diffeology if and only if its uncurried evaluation `(u, x) ↦ p u x` is `C^∞` on `𝔼ⁿ × M`. -/
theorem isPlot_contMDiffMap_iff {n : ℕ} {p : 𝔼ⁿ → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯} :
    _root_.Diffeology.IsPlot p ↔
      ContMDiff (𝓘(ℝ, 𝔼ⁿ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (fun ux : 𝔼ⁿ × M ↦ p ux.1 ux.2) :=
  isPlot_contMDiffMap_iff_dSmooth.trans dSmooth_prod_iff_contMDiff

/-- When `M` and `N` carry compatible diffeologies, `contMDiffMapFunctionalDiffeology E M F N`
equals the canonical instance `instDiffeologicalSpaceContMDiffMap`. -/
@[simp]
theorem contMDiffMapFunctionalDiffeology_eq [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ, F) ∞ N] :
    contMDiffMapFunctionalDiffeology E M F N = instDiffeologicalSpaceContMDiffMap := by
  obtain rfl : ‹DiffeologicalSpace M› = manifoldDiffeology E M :=
    isContMDiffCompatible_iff_eq_manifoldDiffeology.mp inferInstance
  obtain rfl : ‹DiffeologicalSpace N› = manifoldDiffeology F N :=
    isContMDiffCompatible_iff_eq_manifoldDiffeology.mp inferInstance
  rfl

/-- A map `f : P → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` from a finite-dimensional smooth manifold `P` is
diffeologically smooth if and only if its uncurried evaluation `P × M → N` is `C^∞`. -/
theorem dSmooth_contMDiffMap_iff_contMDiff [DiffeologicalSpace P] [IsContMDiffCompatible G P]
    {f : P → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯} :
    _root_.Diffeology.DSmooth f ↔
      ContMDiff (𝓘(ℝ, G).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (fun pm : P × M ↦ f pm.1 pm.2) :=
  dSmooth_contMDiffMap_iff.trans dSmooth_prod_iff_contMDiff

/-- For a finite-dimensional smooth manifold `M` with a compatible diffeology (without requiring
`M` to be Hausdorff), the D-topology of `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ × M` equals the product of the
functional D-topology with the manifold topology of `M`. -/
theorem dTopology_contMDiffMap_prod_eq :
    (_root_.Diffeology.dTopology :
        TopologicalSpace (C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ × M)) =
      @instTopologicalSpaceProd C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ M
        _root_.Diffeology.dTopology ‹TopologicalSpace M› := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  exact dTopology_prod_eq_of_isDTopologyCompatible_right

/-- Evaluation `(C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯, dTopology) × M → N` is jointly continuous whenever
`N` carries a topology compatible with its D-topology (for instance any compatible manifold `N`),
without requiring `M` or `N` to be Hausdorff. -/
theorem continuous_eval_contMDiffMap [_root_.Diffeology.IsDTopologyCompatible N] :
    @Continuous (C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ × M) N
      (@instTopologicalSpaceProd C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ M
        _root_.Diffeology.dTopology ‹TopologicalSpace M›)
      ‹TopologicalSpace N› (fun fx ↦ fx.1 fx.2) := by
  have hc := (dSmooth_eval_contMDiffMap (E := E) (F := F) (M := M) (N := N)).continuous
  rwa [dTopology_contMDiffMap_prod_eq, _root_.Diffeology.IsDTopologyCompatible.dTop_eq N] at hc

section WeakWhitney

open scoped TauCeti.ManifoldWeakWhitney

/-- The identity map on `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` is continuous from the functional
D-topology to the weak Whitney `C^∞` topology. -/
theorem continuous_dTopology_manifoldWeakWhitney [IsManifold 𝓘(ℝ, F) ∞ N] :
    @Continuous C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯
      _root_.Diffeology.dTopology ContMDiffMap.manifoldWeakWhitneyTopology id :=
  continuous_dTopology_dom_iff.mpr fun n p hp ↦ by
    have h : ContMDiff (𝓘(ℝ, 𝔼ⁿ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (fun ux : 𝔼ⁿ × M ↦ p ux.1 ux.2) :=
      isPlot_contMDiffMap_iff.mp hp
    exact h.continuous_manifoldWeakWhitney

/-- The functional D-topology on `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` is finer than (or equal to) the
weak Whitney `C^∞` topology: every weak-Whitney open set is open in the functional D-topology. -/
theorem dTopology_le_manifoldWeakWhitneyTopology [IsManifold 𝓘(ℝ, F) ∞ N] :
    (_root_.Diffeology.dTopology : TopologicalSpace C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) ≤
      ContMDiffMap.manifoldWeakWhitneyTopology :=
  @continuous_id_iff_le _ _root_.Diffeology.dTopology ContMDiffMap.manifoldWeakWhitneyTopology |>.mp
    continuous_dTopology_manifoldWeakWhitney

end WeakWhitney

end PlotsAndTopology

/-! ### Smoothness of translation families on Lie groups and smooth monoids -/

section ContMDiffMul

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Mul G] [TopologicalSpace G] [ChartedSpace E G] [ContMDiffMul 𝓘(ℝ, E) ∞ G]
  [DiffeologicalSpace G] [IsContMDiffCompatible E G]

/-- Left multiplication `g ↦ smoothLeftMul 𝓘(ℝ, E) g` into `C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯` on a
manifold with smooth multiplication is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_smoothLeftMul :
    _root_.Diffeology.DSmooth (fun g : G ↦ smoothLeftMul 𝓘(ℝ, E) g) := by
  refine ContMDiff.dSmooth_contMDiffMap ?_
  simpa only [L_apply] using (contMDiff_mul (I := 𝓘(ℝ, E)) (n := ∞) (G := G))

/-- Right multiplication `g ↦ smoothRightMul 𝓘(ℝ, E) g` into `C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯` on a
manifold with smooth multiplication is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_smoothRightMul :
    _root_.Diffeology.DSmooth (fun g : G ↦ smoothRightMul 𝓘(ℝ, E) g) := by
  refine ContMDiff.dSmooth_contMDiffMap ?_
  simpa only [R_apply, Function.comp_def] using
    ((contMDiff_mul (I := 𝓘(ℝ, E)) (n := ∞) (G := G)).comp
      (contMDiff_snd.prodMk contMDiff_fst))

end ContMDiffMul

end TauCeti.Diffeology
