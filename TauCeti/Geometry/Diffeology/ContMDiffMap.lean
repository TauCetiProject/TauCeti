/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Diffeology.Functional
public import TauCeti.Geometry.Diffeology.Manifold
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.ManifoldFamily

import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pow

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
  the functional diffeology induced along `ContMDiffMap.toDSmoothMap`. When `M` is a
  finite-dimensional smooth manifold, its plots `p : 𝔼ⁿ → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` are
  precisely the parametrizations whose uncurried evaluation `𝔼ⁿ × M → N` is `C^∞`
  (`TauCeti.Diffeology.isPlot_contMDiffMap_iff`), and
  `TauCeti.Diffeology.contMDiffMapFunctionalDiffeology` constructs the same diffeology directly on
  manifolds without pre-installed diffeology instances.
* Because every finite-dimensional charted space is locally compact
  (`ChartedSpace.locallyCompactSpace`), the product D-topology identity holds on
  `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ × M` without any Hausdorff assumption on `M`, making evaluation
  jointly continuous for the functional D-topology
  (`TauCeti.Diffeology.continuous_eval_contMDiffMap`).
* Moreover, every weak-Whitney open set of `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` is open in the functional
  D-topology (`TauCeti.Diffeology.dTopology_le_manifoldWeakWhitneyTopology`), via
  `ContMDiff.continuous_manifoldWeakWhitney`.
* Left and right translations on any manifold with smooth multiplication (`ContMDiffMul`) vary
  diffeologically smoothly in `C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯`, specializing to the rotation family on
  `Circle`. Concrete counterexamples on `ℝ` (`abs` and `x ↦ x ^ 3`) record that non-smooth maps are
  not plots and that a smooth bijection with non-smooth inverse is neither an induction nor a
  subduction.

## Main declarations

* `ContMDiffMap.toDSmoothMap`, `TauCeti.Diffeology.DSmoothMap.toContMDiffMap`, and
  `TauCeti.Diffeology.DSmoothMap.equivContMDiffMap`: mapping-space bridge between `ContMDiffMap`
  and `DSmoothMap`.
* `TauCeti.Diffeology.instDiffeologicalSpaceContMDiffMap` and
  `TauCeti.Diffeology.contMDiffMapFunctionalDiffeology`: functional diffeology on
  `C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯`.
* `TauCeti.Diffeology.isPlot_contMDiffMap_iff` and
  `TauCeti.Diffeology.dSmooth_contMDiffMap_iff_contMDiff`: characterization of plots and smooth
  families via uncurried `ContMDiff` regularity.
* `TauCeti.Diffeology.continuous_eval_contMDiffMap` and
  `TauCeti.Diffeology.dTopology_le_manifoldWeakWhitneyTopology`: joint continuity of evaluation and
  comparison with the weak Whitney `C^∞` topology.
* `TauCeti.Diffeology.dSmooth_mulLeftContMDiffMap`,
  `TauCeti.Diffeology.dSmooth_mulRightContMDiffMap`, and `TauCeti.Diffeology.isPlot_circleRotation`:
  smooth translation families and circle rotation plot.
* `TauCeti.Diffeology.not_isPlot_abs`, `TauCeti.Diffeology.not_isInduction_cubeEquiv`, and
  `TauCeti.Diffeology.not_isSubduction_cubeEquiv`: non-plot and non-diffeomorphism witnesses on `ℝ`.

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

/-- Turn a bundled `C^∞` manifold map between compatible charted spaces into a bundled
diffeologically smooth map. Neither finite-dimensionality nor atlas smoothness is required. -/
def toDSmoothMap (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) : DSmoothMap M N :=
  ⟨f, f.contMDiff.dSmooth⟩

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

/-- Sending `y : N` to the constant map `ContMDiffMap.const y` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_const_contMDiffMap :
    _root_.Diffeology.DSmooth (ContMDiffMap.const : N → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) := by
  refine isInduction_toDSmoothMap.dSmooth_iff.mpr ?_
  simpa only [Function.comp_def, toDSmoothMap_const] using
    (DSmoothMap.dSmooth_constMap (X := M) (Y := N))

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

/-- `DSmoothMap.toContMDiffMap` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_toContMDiffMap :
    _root_.Diffeology.DSmooth (toContMDiffMap : DSmoothMap M N → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) :=
  isInduction_toDSmoothMap.dSmooth_iff.mpr _root_.Diffeology.dSmooth_id

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
      ContMDiff (𝓘(ℝ, 𝔼ⁿ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (fun ux : 𝔼ⁿ × M ↦ p ux.1 ux.2) := by
  rw [isPlot_inducedDiffeology_iff, DSmoothMap.isPlot_iff, dSmooth_prod_iff_contMDiff]
  rfl

/-- When `M` and `N` carry compatible diffeologies, `contMDiffMapFunctionalDiffeology E M F N`
equals the canonical instance `instDiffeologicalSpaceContMDiffMap`. -/
@[simp]
theorem contMDiffMapFunctionalDiffeology_eq [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ, F) ∞ N] :
    contMDiffMapFunctionalDiffeology E M F N = instDiffeologicalSpaceContMDiffMap := by
  ext n p
  exact (@isPlot_contMDiffMap_iff E F _ _ _ _ _ M N _ _ _ _ _
    (manifoldDiffeology E M) inferInstance (manifoldDiffeology F N) inferInstance n p).trans
    isPlot_contMDiffMap_iff.symm

/-- A map `f : P → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯` from a finite-dimensional smooth manifold `P` is
diffeologically smooth if and only if its uncurried evaluation `P × M → N` is `C^∞`. -/
theorem dSmooth_contMDiffMap_iff_contMDiff [DiffeologicalSpace P] [IsContMDiffCompatible G P]
    {f : P → C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯} :
    _root_.Diffeology.DSmooth f ↔
      ContMDiff (𝓘(ℝ, G).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (fun pm : P × M ↦ f pm.1 pm.2) := by
  rw [isInduction_toDSmoothMap.dSmooth_iff, dSmooth_curry_iff, dSmooth_prod_iff_contMDiff]
  rfl

/-- Every finite-dimensional charted space `M` is locally compact, so the D-topology of
`C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯ × M` equals the product of the functional D-topology with the
manifold topology of `M` (without requiring `M` to be Hausdorff). -/
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

/-- Left multiplication `x ↦ g * x` as a bundled `C^∞` map `G → G`. -/
@[to_additive /-- Left addition `x ↦ g + x` as a bundled `C^∞` map `G → G`. -/]
def mulLeftContMDiffMap (g : G) : C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯ :=
  ⟨(g * ·), contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)⟩

/-- Evaluating `mulLeftContMDiffMap g` at `x` returns `g * x`. -/
@[to_additive (attr := simp) /-- Evaluating `addLeftContMDiffMap g` at `x` returns `g + x`. -/]
theorem mulLeftContMDiffMap_apply (g x : G) : mulLeftContMDiffMap (E := E) g x = g * x :=
  (rfl)

/-- Right multiplication `x ↦ x * g` as a bundled `C^∞` map `G → G`. -/
@[to_additive /-- Right addition `x ↦ x + g` as a bundled `C^∞` map `G → G`. -/]
def mulRightContMDiffMap (g : G) : C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯ :=
  ⟨(· * g), contMDiff_mul_right (I := 𝓘(ℝ, E)) (n := ∞)⟩

/-- Evaluating `mulRightContMDiffMap g` at `x` returns `x * g`. -/
@[to_additive (attr := simp) /-- Evaluating `addRightContMDiffMap g` at `x` returns `x + g`. -/]
theorem mulRightContMDiffMap_apply (g x : G) : mulRightContMDiffMap (E := E) g x = x * g :=
  (rfl)

variable [DiffeologicalSpace G] [IsContMDiffCompatible E G]

/-- Left multiplication `G → C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯` is diffeologically smooth. -/
@[to_additive (attr := fun_prop)
  /-- Left addition `G → C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯` is diffeologically smooth. -/]
theorem dSmooth_mulLeftContMDiffMap :
    _root_.Diffeology.DSmooth (mulLeftContMDiffMap : G → C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯) :=
  isInduction_toDSmoothMap.dSmooth_iff.mpr <|
    dSmooth_curry_iff.mpr (contMDiff_mul (I := 𝓘(ℝ, E)) (n := ∞)).dSmooth_prod

/-- Right multiplication `G → C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯` is diffeologically smooth. -/
@[to_additive (attr := fun_prop)
  /-- Right addition `G → C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯` is diffeologically smooth. -/]
theorem dSmooth_mulRightContMDiffMap :
    _root_.Diffeology.DSmooth (mulRightContMDiffMap : G → C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, E), G⟯) :=
  isInduction_toDSmoothMap.dSmooth_iff.mpr <|
    dSmooth_curry_iff.mpr
      ((contMDiff_mul (I := 𝓘(ℝ, E)) (n := ∞)).comp
        (contMDiff_snd.prodMk contMDiff_fst)).dSmooth_prod

end ContMDiffMul

/-! ### Circle rotation plots and non-smooth / non-diffeomorphism witnesses -/

/-- The standard manifold diffeology on the unit circle `Circle` in `ℂ`. -/
instance instDiffeologicalSpaceCircle : DiffeologicalSpace Circle :=
  manifoldDiffeology (𝔼¹) Circle

/-- `Circle` with `instDiffeologicalSpaceCircle` is compatible with its standard manifold
structure modelled on `𝔼¹`. -/
instance instIsContMDiffCompatibleCircle : IsContMDiffCompatible (𝔼¹) Circle :=
  inferInstanceAs (@IsContMDiffCompatible (𝔼¹) _ _ Circle _ _ (manifoldDiffeology (𝔼¹) Circle))

/-- The exponential map `Circle.exp : ℝ → Circle` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_circleExp : _root_.Diffeology.DSmooth Circle.exp :=
  contMDiff_circleExp.dSmooth

/-- Rotation of `Circle` by angle `t : ℝ`, bundled in `C^∞⟮𝓡 1, Circle; 𝓡 1, Circle⟯`. -/
def circleRotation (t : ℝ) : C^∞⟮𝓡 1, Circle; 𝓡 1, Circle⟯ :=
  mulRightContMDiffMap (Circle.exp t)

/-- Evaluating `circleRotation t` at `z` returns `z * Circle.exp t`. -/
@[simp]
theorem circleRotation_apply (t : ℝ) (z : Circle) : circleRotation t z = z * Circle.exp t :=
  (rfl)

/-- The circle rotation family `ℝ → C^∞⟮𝓡 1, Circle; 𝓡 1, Circle⟯` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_circleRotation : _root_.Diffeology.DSmooth circleRotation :=
  dSmooth_mulRightContMDiffMap.comp dSmooth_circleExp

/-- Reparametrizing `circleRotation` by `𝔼¹` via `u ↦ u 0` yields a plot of the functional
diffeology on `C^∞⟮𝓡 1, Circle; 𝓡 1, Circle⟯`. -/
theorem isPlot_circleRotation :
    _root_.Diffeology.IsPlot (fun u : 𝔼¹ ↦ circleRotation (u 0)) := by
  have hcoord : ContDiff ℝ ∞ (fun u : 𝔼¹ ↦ u 0) :=
    (contDiff_apply ℝ (fun _ : Fin 1 ↦ ℝ) 0).comp (EuclideanSpace.equiv (Fin 1) ℝ).contDiff
  exact (dSmooth_circleRotation.comp hcoord.dSmooth).isPlot

/-- The absolute value `abs : ℝ → ℝ` is continuous (`C⁰`) on `ℝ` without being diffeologically
smooth. -/
theorem not_dSmooth_abs : ¬ _root_.Diffeology.DSmooth (abs : ℝ → ℝ) := fun h ↦
  not_differentiableAt_abs_zero ((_root_.Diffeology.dSmooth_iff_contDiff.mp h).differentiable
    (by simp) 0)

/-- The `C⁰` curve `u ↦ |u 0|` from `𝔼¹` to `ℝ` is not a plot of `ℝ`. -/
theorem not_isPlot_abs : ¬ _root_.Diffeology.IsPlot (fun u : 𝔼¹ ↦ |u 0|) := by
  intro hp
  have h1 : ContDiff ℝ ∞ (fun t : ℝ ↦ (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t)) :=
    (EuclideanSpace.equiv (Fin 1) ℝ).symm.contDiff.comp (contDiff_pi.mpr fun _ ↦ contDiff_id)
  have habs : ContDiff ℝ ∞ (abs : ℝ → ℝ) :=
    (_root_.Diffeology.isPlot_iff_contDiff.mp hp).comp h1
  exact not_differentiableAt_abs_zero (habs.differentiable (by simp) 0)

/-- The cubing bijection `x ↦ x ^ 3` on `ℝ`, bundled as an equivalence `ℝ ≃ ℝ`. -/
def cubeEquiv : ℝ ≃ ℝ :=
  Equiv.ofBijective (fun x : ℝ ↦ x ^ 3) <| by
    refine ⟨(Nat.odd_iff.mpr rfl : Odd 3).strictMono_pow.injective, fun y ↦ ?_⟩
    let a : ℝ := min (-1) y
    let b : ℝ := max 1 y
    have ha : a ≤ -1 := min_le_left (-1) y
    have hay : a ≤ y := min_le_right (-1) y
    have hb : 1 ≤ b := le_max_left 1 y
    have hby : y ≤ b := le_max_right 1 y
    have hab : a ≤ b := by linarith
    have ha2 : 1 ≤ a ^ 2 := by nlinarith
    have hb2 : 1 ≤ b ^ 2 := by nlinarith
    have ha3 : a ^ 3 ≤ y := by
      have hmul : a * a ^ 2 ≤ a * 1 := mul_le_mul_of_nonpos_left ha2 (by linarith)
      nlinarith
    have hb3 : y ≤ b ^ 3 := by
      have hmul : b * 1 ≤ b * b ^ 2 := mul_le_mul_of_nonneg_left hb2 (by linarith)
      nlinarith
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc hab (continuous_pow 3).continuousOn ⟨ha3, hb3⟩
    exact ⟨x, hx⟩

/-- Evaluating `cubeEquiv` at `x` returns `x ^ 3`. -/
@[simp]
theorem cubeEquiv_apply (x : ℝ) : cubeEquiv x = x ^ 3 :=
  (rfl)

/-- `cubeEquiv` maps `0` to `0`. -/
theorem cubeEquiv_zero : cubeEquiv 0 = 0 := by
  simp

/-- `cubeEquiv.symm` maps `0` to `0`. -/
@[simp]
theorem cubeEquiv_symm_zero : cubeEquiv.symm 0 = 0 :=
  cubeEquiv.symm_apply_eq.mpr cubeEquiv_zero.symm

/-- `cubeEquiv : ℝ ≃ ℝ` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_cubeEquiv : _root_.Diffeology.DSmooth cubeEquiv :=
  _root_.Diffeology.dSmooth_iff_contDiff.mpr (contDiff_id.pow 3)

/-- The inverse of `cubeEquiv` (`y ↦ y ^ (1 / 3)`) is not diffeologically smooth, even though
`cubeEquiv` is a smooth bijection. -/
theorem not_dSmooth_cubeEquiv_symm : ¬ _root_.Diffeology.DSmooth cubeEquiv.symm := by
  intro h
  have hg : DifferentiableAt ℝ cubeEquiv.symm 0 :=
    (_root_.Diffeology.dSmooth_iff_contDiff.mp h).differentiable (by simp) 0
  have hf : HasDerivAt cubeEquiv (3 * (0 : ℝ) ^ (3 - 1)) 0 := hasDerivAt_pow 3 (0 : ℝ)
  have hcomp : HasDerivAt (cubeEquiv.symm ∘ cubeEquiv)
      (deriv cubeEquiv.symm 0 * (3 * (0 : ℝ) ^ (3 - 1))) 0 := by
    have hg0 : HasDerivAt cubeEquiv.symm (deriv cubeEquiv.symm 0) (cubeEquiv 0) := by
      simpa only [cubeEquiv_zero] using hg.hasDerivAt
    exact hg0.comp 0 hf
  have hid : HasDerivAt (cubeEquiv.symm ∘ cubeEquiv) 1 0 := by
    have heq : cubeEquiv.symm ∘ cubeEquiv = id := funext cubeEquiv.left_inv
    simpa only [heq] using hasDerivAt_id (0 : ℝ)
  have h10 : (1 : ℝ) = deriv cubeEquiv.symm 0 * (3 * (0 : ℝ) ^ (3 - 1)) := hid.unique hcomp
  norm_num at h10

/-- `cubeEquiv : ℝ → ℝ` is a smooth bijection that is not an induction. -/
theorem not_isInduction_cubeEquiv : ¬ IsInduction (cubeEquiv : ℝ → ℝ) := fun h ↦
  not_dSmooth_cubeEquiv_symm <| h.dSmooth_iff.mpr <| by
    have heq : (cubeEquiv : ℝ → ℝ) ∘ cubeEquiv.symm = id := funext cubeEquiv.right_inv
    simpa only [heq] using _root_.Diffeology.dSmooth_id

/-- `cubeEquiv : ℝ → ℝ` is a smooth bijection that is not a subduction. -/
theorem not_isSubduction_cubeEquiv : ¬ IsSubduction (cubeEquiv : ℝ → ℝ) := fun h ↦
  not_dSmooth_cubeEquiv_symm <| (h.dSmooth_iff cubeEquiv.symm).mpr <| by
    have heq : cubeEquiv.symm ∘ (cubeEquiv : ℝ → ℝ) = id := funext cubeEquiv.left_inv
    simpa only [heq] using _root_.Diffeology.dSmooth_id

end TauCeti.Diffeology
