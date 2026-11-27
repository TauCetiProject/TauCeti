/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Functions with Hölder derivatives on a compact set

`TauCeti.HasHolderFDerivOn α s K f` says that `f` is differentiable at the points of `s` with a
derivative `f'`, and that both `f` and `f'` are `α`-Hölder on `K`. For a compact `K` this is
stable under bilinear products (`TauCeti.HasHolderFDerivOn.comp₂`), sums and finite sums,
continuous linear maps applied after the function, and precomposition with a map which is `C¹`
with `C¹` derivative on a compact convex `K` (`TauCeti.hasHolderFDerivOn_comp`):
`D(g ∘ Φ) = Dg(Φ ·) DΦ`. This is how the entries of a coefficient pulled back along a change of
variables, which are sums of products of such compositions, are shown to have Hölder derivatives.

The composition step uses that a Hölder function after a Lipschitz map is Hölder with the same
exponent (`HolderOnWith.comp_lipschitzOnWith`).

## Main declarations

* `HolderOnWith.comp_lipschitzOnWith`: an `r`-Hölder function after a `K`-Lipschitz map is
  `r`-Hölder.
* `TauCeti.HasHolderFDerivOn`: differentiable with a derivative, both `α`-Hölder on a set.
* `TauCeti.HasHolderFDerivOn.comp₂`, `TauCeti.HasHolderFDerivOn.add`,
  `TauCeti.HasHolderFDerivOn.sum`, `TauCeti.HasHolderFDerivOn.clm_comp`: bilinear products, sums
  and continuous linear maps.
* `TauCeti.HasHolderFDerivOn.exists_holderOnWith_fderiv`: `fderiv` is Hölder.
* `TauCeti.hasHolderFDerivOn_comp`: composition with a `C¹` map whose derivative is `C¹`.
-/

public section

noncomputable section

open Set
open scoped NNReal

/-- An `r`-Hölder function on `t` after a map that is `K`-Lipschitz on `s` and maps `s` into `t`
is `r`-Hölder on `s`, with constant `C K ^ r`. -/
theorem HolderOnWith.comp_lipschitzOnWith {X Y Z : Type*} [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] [PseudoEMetricSpace Z] {C r K : ℝ≥0} {g : Y → Z} {t : Set Y}
    (hg : HolderOnWith C r g t) {f : X → Y} {s : Set X} (hf : LipschitzOnWith K f s)
    (hst : MapsTo f s t) : HolderOnWith (C * K ^ (r : ℝ)) r (g ∘ f) s := by
  simpa only [mul_one] using hg.comp hf.holderOnWith hst

namespace TauCeti

variable {E E' F A B G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {α : ℝ≥0}

/-- `f` is differentiable at the points of `s` with a derivative `f'`, and both `f` and `f'` are
`α`-Hölder on `K`. -/
def HasHolderFDerivOn (α : ℝ≥0) (s K : Set E) (f : E → F) : Prop :=
  ∃ f' : E → E →L[ℝ] F, (∀ y ∈ s, HasFDerivAt f (f' y) y) ∧ (∃ C, HolderOnWith C α f K) ∧
    ∃ C, HolderOnWith C α f' K

/-- Bilinear products preserve `HasHolderFDerivOn` on a compact set, for a positive exponent. -/
theorem HasHolderFDerivOn.comp₂ (L : A →L[ℝ] B →L[ℝ] G) (hα : 0 < α) {s K : Set E}
    (hK : IsCompact K) {f : E → A} {g : E → B} (hf : HasHolderFDerivOn α s K f)
    (hg : HasHolderFDerivOn α s K g) :
    HasHolderFDerivOn α s K fun z => L (f z) (g z) := by
  obtain ⟨f', hf', ⟨Cf, hfC⟩, ⟨Cf', hf'C⟩⟩ := hf
  obtain ⟨g', hg', ⟨Cg, hgC⟩, ⟨Cg', hg'C⟩⟩ := hg
  obtain ⟨C₁, h₁⟩ := (L.precompR E).exists_holderOnWith_comp₂_of_isCompact hK hα hfC hg'C
  obtain ⟨C₂, h₂⟩ := (L.precompL E).exists_holderOnWith_comp₂_of_isCompact hK hα hf'C hgC
  exact ⟨fun y => L.precompR E (f y) (g' y) + L.precompL E (f' y) (g y),
    fun y hy => L.hasFDerivAt_of_bilinear (hf' y hy) (hg' y hy),
    L.exists_holderOnWith_comp₂_of_isCompact hK hα hfC hgC, _, h₁.add h₂⟩

/-- Sums preserve `HasHolderFDerivOn`. -/
theorem HasHolderFDerivOn.add {s K : Set E} {f g : E → F}
    (hf : HasHolderFDerivOn α s K f) (hg : HasHolderFDerivOn α s K g) :
    HasHolderFDerivOn α s K (f + g) := by
  obtain ⟨f', hf', ⟨Cf, hfC⟩, ⟨Cf', hf'C⟩⟩ := hf
  obtain ⟨g', hg', ⟨Cg, hgC⟩, ⟨Cg', hg'C⟩⟩ := hg
  exact ⟨f' + g', fun y hy => (hf' y hy).add (hg' y hy), ⟨_, hfC.add hgC⟩, ⟨_, hf'C.add hg'C⟩⟩

/-- Finite sums preserve `HasHolderFDerivOn`. -/
theorem HasHolderFDerivOn.sum {ι : Type*} (t : Finset ι) {s K : Set E} {f : ι → E → F}
    (hf : ∀ i ∈ t, HasHolderFDerivOn α s K (f i)) :
    HasHolderFDerivOn α s K fun z => ∑ i ∈ t, f i z := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨0, fun y _ => by simpa using hasFDerivAt_const (0 : F) y,
      ⟨0, fun x _ y _ => by simp⟩, ⟨0, fun x _ y _ => by simp⟩⟩
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i t)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A continuous linear map applied after a function preserves `HasHolderFDerivOn`. -/
theorem HasHolderFDerivOn.clm_comp (T : F →L[ℝ] G) {s K : Set E} {f : E → F}
    (hf : HasHolderFDerivOn α s K f) : HasHolderFDerivOn α s K fun z => T (f z) := by
  obtain ⟨f', hf', ⟨Cf, hfC⟩, ⟨Cf', hf'C⟩⟩ := hf
  exact ⟨fun y => T.comp (f' y), fun y hy => T.hasFDerivAt.comp y (hf' y hy),
    ⟨_, T.lipschitzWith.comp_holderOnWith hfC⟩,
    ⟨_, (ContinuousLinearMap.compL ℝ E F G T).lipschitzWith.comp_holderOnWith hf'C⟩⟩

/-- On a set `s` contained in `K`, the derivative of a function with `HasHolderFDerivOn` is
`α`-Hölder on `s`. -/
theorem HasHolderFDerivOn.exists_holderOnWith_fderiv {s K : Set E} (hsK : s ⊆ K)
    {f : E → F} (hf : HasHolderFDerivOn α s K f) :
    ∃ C, HolderOnWith C α (fderiv ℝ f) s := by
  obtain ⟨f', hf', -, ⟨C, hC⟩⟩ := hf
  exact ⟨C, (hC.mono hsK).congr fun y hy => (hf' y hy).fderiv.symm⟩

/-- A `C¹` function `g` whose derivative is `α`-Hölder on a set `t`, composed with a map `Φ` that
is `C¹` with `C¹` derivative on a compact convex set `K` and maps `K` into `t`, has
`HasHolderFDerivOn` on every open `s ⊆ K`: `D(g ∘ Φ) = Dg(Φ ·) DΦ`. -/
theorem hasHolderFDerivOn_comp (hα : 0 < α) (hα1 : α ≤ 1) {s K : Set E} (hs : IsOpen s)
    (hsK : s ⊆ K) (hK : IsCompact K) (hKc : Convex ℝ K) {Φ : E → E'} (hΦ : ContDiffOn ℝ 1 Φ K)
    (hDΦ : ContDiffOn ℝ 1 (fderiv ℝ Φ) K) {g : E' → F} {O t : Set E'} (hO : IsOpen O)
    (hg : ContDiffOn ℝ 1 g O) (hKO : MapsTo Φ K O) (hKt : MapsTo Φ K t) {C : ℝ≥0}
    (hgH : HolderOnWith C α (fderiv ℝ g) t) : HasHolderFDerivOn α s K fun y => g (Φ y) := by
  obtain ⟨LΦ, hLΦ⟩ := hΦ.exists_lipschitzOnWith one_ne_zero hKc hK
  obtain ⟨CΦ, hCΦ⟩ := hDΦ.exists_holderOnWith hKc hK hα1
  refine ⟨fun y => (fderiv ℝ g (Φ y)).comp (fderiv ℝ Φ y), fun y hy => ?_,
    (hg.comp hΦ hKO).exists_holderOnWith hKc hK hα1,
    (ContinuousLinearMap.compL ℝ E E' F).exists_holderOnWith_comp₂_of_isCompact hK hα
      (hgH.comp_lipschitzOnWith hLΦ hKt) hCΦ⟩
  have hΦd := (hΦ.differentiableOn one_ne_zero y (hsK hy)).differentiableAt
    (Filter.mem_of_superset (hs.mem_nhds hy) hsK)
  have hd := (hg.differentiableOn one_ne_zero (Φ y) (hKO (hsK hy))).differentiableAt
    (hO.mem_nhds (hKO (hsK hy)))
  exact hd.hasFDerivAt.comp y hΦd.hasFDerivAt

end TauCeti
