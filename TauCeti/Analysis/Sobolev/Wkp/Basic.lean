/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient
public import TauCeti.Analysis.Sobolev.GraphStep
public import TauCeti.Analysis.Sobolev.W1p.Basic

/-!
# Arbitrary-order weak Sobolev spaces

This file constructs the real-valued Sobolev space `W^{k,p}(Ω)` for every natural number
`k`, on an open subset of a finite-dimensional real inner product space.  The first-order stage
is `TauCeti.W1p`.  Every successor stage applies `TauCeti.WeakDerivStep` to the highest weak
derivative of the preceding stage.  Thus an element of `W^{k+1,p}(Ω)` records an element of
`W^{k,p}(Ω)` and an `Lᵖ` weak derivative of its order-`k` derivative.

The iterated derivative fields are basis-free.  `TauCeti.IteratedGradient E 0` is `E`, the weak
gradient identified with a linear functional by the real inner product, and
`TauCeti.IteratedGradient E (j+1)` adds one continuous-linear derivative direction on the left.
Consequently the highest field of `W^{k+1,p}` has type
`Lᵖ(Ω; TauCeti.IteratedGradient E k)`.

Every stage is a closed weak-derivative graph, hence complete.  No boundedness or boundary
regularity of `Ω` is used.  The norm of `W^{1,p}(Ω)` is that of `TauCeti.W1p`: the `Lᵖ` norm of
the pointwise Euclidean norm of the value and the gradient.  Each later stage takes the Euclidean
product norm of its two components, so at every order `k + 2` and for every `p` the squared norm is
the sum of the squared norm of the one-order-lower component and the squared norm of the highest
weak derivative.  At order one this identity holds for `p = 2` but not in general; it fails, for
instance, for `sin` in `W^{1,∞}(ℝ)`.  The derivative fields above first order carry operator norms,
so the norm of `W^{k,2}(Ω)` with `k ≥ 2` need not be induced by an inner product: on
`Ω = (0,1)² ⊆ ℝ²`, for instance, `x²/2` and `y²/2` violate the parallelogram law.  It is a
Banach-space norm, not in general the Hilbert-space norm of `H^k(Ω)`.

## Implementation notes

The bundled stage machinery `TauCeti.SobolevStage`, `TauCeti.firstSobolevStage`,
`TauCeti.SobolevStage.next`, and `TauCeti.sobolevStage` is public on purpose: it is what indexes
the type `TauCeti.Wkp`, so its normed, complete structure and the order `0` and `1` boundary cases
are recovered by unfolding it rather than by transport.  `TauCeti.firstSobolevStage`,
`TauCeti.SobolevStage.next`, and `TauCeti.Wkp` are reducible.  The recursion
`TauCeti.sobolevStage` is exposed but semireducible, so that at a concrete order instance search
stops at `(sobolevStage j).Space` and finds the
`TauCeti.SobolevStage` shortcut instances keyed there.  The shortcut instances are provided at both
the bundled-stage and `Wkp` indexings so instance search need not rederive these structures
through the recursion.  The identifications of `Wkp … 1` with `TauCeti.W1p` and of
`Wkp … (k + 2)` with a `TauCeti.WeakDerivStep` are therefore definitional but not reducible, and
`rw` and `simp` do not unfold `TauCeti.sobolevStage` to match across them in either direction: a
lemma stated for `TauCeti.W1p` or `TauCeti.WeakDerivStep` applied to a `Wkp … 1` or
`Wkp … (k + 2)` term, and a `Wkp`-indexed lemma applied to a term typed as `TauCeti.W1p` or
`TauCeti.WeakDerivStep`, must both be given their argument explicitly.
The projections below are sealed instead, and are used through their characteristic equations
`TauCeti.Wkp.lowerOrder_zero`, `TauCeti.Wkp.lowerOrder_succ`, `TauCeti.Wkp.iteratedGradient_zero`,
`TauCeti.Wkp.iteratedGradient_succ`, `TauCeti.Wkp.value_zero`, and `TauCeti.Wkp.value_succ`, and
through `TauCeti.Wkp.lowerOrder_succ_coe` and `TauCeti.Wkp.iteratedGradient_succ_coe`, which give
the two projections above first order as the components of the underlying graph element.

## Main declarations

* `TauCeti.Wkp`: `W^{k,p}(Ω)`, with `Wkp 0 = Lᵖ(Ω)` and `Wkp 1 = W1p`.
* `TauCeti.Wkp.lowerOrder`: the continuous projection `W^{k+1,p} → W^{k,p}`.
* `TauCeti.Wkp.iteratedGradient`: the highest weak derivative of a positive-order Sobolev function.
* `TauCeti.Wkp.hasWeakFDerivOn_iteratedGradient`: adjacent recorded derivatives satisfy the weak
  derivative identity.

## References

The iterated weak-derivative definition and closed-graph completeness argument follow
L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace

universe u

variable {E : Type u} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 <= p)]

/-- The bundled data used to iterate weak-derivative graph spaces.  Its `j`th stage carries the
space of order `j + 1` and its highest derivative projection. -/
structure SobolevStage (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ENNReal) [Fact (1 <= p)] (j : ℕ) where
  /-- The Sobolev space of order `j + 1`. -/
  Space : Type u
  /-- The normed additive commutative group structure on the order-`j + 1` Sobolev space. -/
  [normedAddCommGroup : NormedAddCommGroup Space]
  /-- The normed `ℝ`-space structure on the order-`j + 1` Sobolev space. -/
  [normedSpace : NormedSpace ℝ Space]
  /-- The completeness instance for the order-`j + 1` Sobolev space. -/
  [completeSpace : CompleteSpace Space]
  /-- The continuous projection to the highest weak derivative field. -/
  iteratedGradientL : Space →L[ℝ] Lp (IteratedGradient E j) p (mu.restrict Omega)

/-- The first stage of the arbitrary-order construction is `W1p`, whose highest-derivative
projection is the weak gradient. -/
@[reducible, expose] noncomputable def firstSobolevStage : SobolevStage mu Omega p 0 where
  Space := W1p mu Omega p
  iteratedGradientL := W1p.gradientL

/-- Adjoin the weak derivative of a stage's highest derivative field. -/
@[reducible, expose] noncomputable def SobolevStage.next (S : SobolevStage mu Omega p j) :
    SobolevStage mu Omega p (j + 1) := by
  letI : NormedAddCommGroup S.Space := S.normedAddCommGroup
  letI : NormedSpace ℝ S.Space := S.normedSpace
  letI : CompleteSpace S.Space := S.completeSpace
  exact
    { Space := WeakDerivStep mu Omega p S.iteratedGradientL
      iteratedGradientL := WeakDerivStep.weakFDerivL S.iteratedGradientL }

/-- The `j`th iterated weak-derivative stage, representing Sobolev order `j + 1`. -/
@[expose] noncomputable def sobolevStage : (j : ℕ) → SobolevStage mu Omega p j
  | 0 => firstSobolevStage
  | j + 1 => (sobolevStage j).next

@[instance_reducible, expose] noncomputable def SobolevStage.instNormedAddCommGroup
    (j : ℕ) : NormedAddCommGroup
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).Space :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).normedAddCommGroup

attribute [instance] SobolevStage.instNormedAddCommGroup

@[instance_reducible, expose] noncomputable def SobolevStage.instNormedSpace
    (j : ℕ) : NormedSpace ℝ
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).Space :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).normedSpace

attribute [instance] SobolevStage.instNormedSpace

theorem SobolevStage.instCompleteSpace (j : ℕ) :
    CompleteSpace (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).Space :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).completeSpace

attribute [instance] SobolevStage.instCompleteSpace

/-- The arbitrary-order, real-valued weak Sobolev space `W^{k,p}(Ω)`.  At order zero this is
`Lᵖ(Ω)`; order one is `W1p`; every further order adjoins the weak derivative of the highest
derivative field from the preceding order. -/
@[reducible, expose] noncomputable def Wkp (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ENNReal) [Fact (1 <= p)] : ℕ → Type u
  | 0 => Lp ℝ p (mu.restrict Omega)
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).Space

@[instance_reducible, expose] noncomputable def Wkp.instNormedAddCommGroup :
    (k : ℕ) → NormedAddCommGroup (Wkp mu Omega p k)
  | 0 => inferInstance
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).normedAddCommGroup

attribute [instance] Wkp.instNormedAddCommGroup

@[instance_reducible, expose] noncomputable def Wkp.instNormedSpace :
    (k : ℕ) → NormedSpace ℝ (Wkp mu Omega p k)
  | 0 => inferInstance
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).normedSpace

attribute [instance] Wkp.instNormedSpace

/-- Every weak Sobolev space `W^{k,p}(Ω)` is complete in its iterated graph norm. -/
theorem Wkp.instCompleteSpace :
    (k : ℕ) → CompleteSpace (Wkp mu Omega p k)
  | 0 => inferInstance
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).completeSpace

attribute [instance] Wkp.instCompleteSpace

namespace Wkp

/-- The continuous projection that forgets the highest weak derivative. -/
def lowerOrderL : (k : ℕ) → Wkp mu Omega p (k + 1) →L[ℝ] Wkp mu Omega p k
  | 0 => W1p.valueL
  | k + 1 => WeakDerivStep.prevL
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL

/-- A positive-order Sobolev function regarded as a Sobolev function of one lower order. -/
def lowerOrder (k : ℕ) (u : Wkp mu Omega p (k + 1)) : Wkp mu Omega p k :=
  lowerOrderL k u

/-- Evaluating the continuous lower-order projection equals `lowerOrder`. -/
theorem lowerOrderL_apply (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    lowerOrderL k u = lowerOrder k u :=
  (rfl)

/-- The continuous projection to the first-order part of a positive-order Sobolev function. -/
def firstOrderL : (k : ℕ) → Wkp mu Omega p (k + 1) →L[ℝ] W1p mu Omega p
  | 0 => ContinuousLinearMap.id ℝ _
  | k + 1 => (firstOrderL k).comp (lowerOrderL (k + 1))

/-- Forget the derivatives above first order in a higher-order Sobolev function. -/
def firstOrder (k : ℕ) (u : Wkp mu Omega p (k + 1)) : W1p mu Omega p :=
  firstOrderL k u

/-- Evaluating the continuous first-order projection equals `firstOrder`. -/
theorem firstOrderL_apply (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    firstOrderL k u = firstOrder k u :=
  (rfl)

/-- The first-order part of a first-order Sobolev function is itself. -/
@[simp] theorem firstOrder_zero (u : Wkp mu Omega p 1) : firstOrder 0 u = u :=
  -- `firstOrderL 0` is the identity, and `Wkp … 1` unfolds to `W1p` because `sobolevStage 0`
  -- is `firstSobolevStage`.
  (rfl)

/-- Forgetting one derivative before taking the first-order part has no effect. -/
theorem firstOrder_succ (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    firstOrder (k + 1) u = firstOrder k (lowerOrder (k + 1) u) := by
  simp only [firstOrder, firstOrderL, lowerOrder, ContinuousLinearMap.comp_apply]

/-- The continuous projection to the highest weak derivative of a positive-order Sobolev
function.  For `W^{k+1,p}` its target is `Lᵖ(Ω; IteratedGradient E k)`. -/
def iteratedGradientL (k : ℕ) : Wkp mu Omega p (k + 1) →L[ℝ]
    Lp (IteratedGradient E k) p (mu.restrict Omega) :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL

/-- The highest weak derivative recorded by a positive-order Sobolev function. -/
def iteratedGradient (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    Lp (IteratedGradient E k) p (mu.restrict Omega) :=
  iteratedGradientL k u

/-- Evaluating the continuous highest-derivative projection equals `iteratedGradient`. -/
theorem iteratedGradientL_apply (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    iteratedGradientL k u = iteratedGradient k u :=
  (rfl)

/-- The continuous projection of a Sobolev function to its `Lᵖ` value component. -/
def valueL : (k : ℕ) → Wkp mu Omega p k →L[ℝ] Lp ℝ p (mu.restrict Omega)
  | 0 => ContinuousLinearMap.id ℝ _
  | k + 1 => (valueL k).comp (lowerOrderL k)

/-- The `Lᵖ` value component of an arbitrary-order Sobolev function. -/
def value (k : ℕ) (u : Wkp mu Omega p k) : Lp ℝ p (mu.restrict Omega) :=
  valueL k u

/-- Evaluating the continuous value projection equals `value`. -/
@[simp]
theorem valueL_apply (k : ℕ) (u : Wkp mu Omega p k) : valueL k u = value k u :=
  (rfl)

/-- The value component preserves addition. -/
@[simp]
theorem value_add (k : ℕ) (u v : Wkp mu Omega p k) :
    value k (u + v) = value k u + value k v := by
  simpa only [← valueL_apply] using (valueL k).map_add u v

/-- The value component preserves scalar multiplication. -/
@[simp]
theorem value_smul (k : ℕ) (c : ℝ) (u : Wkp mu Omega p k) :
    value k (c • u) = c • value k u := by
  simpa only [← valueL_apply] using (valueL k).map_smul c u

/-- At order zero, the value component of a Sobolev function is the function itself. -/
@[simp]
theorem value_zero (u : Wkp mu Omega p 0) : value 0 u = u :=
  by simp only [value, valueL, ContinuousLinearMap.id_apply]

/-- Taking the value component commutes with forgetting the highest derivative. -/
theorem value_succ (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    value (k + 1) u = value k (lowerOrder k u) :=
  by simp only [value, valueL, lowerOrder, ContinuousLinearMap.comp_apply]

/-- At first order, the generic lower-order projection is the `W1p` value projection. -/
@[simp]
theorem lowerOrder_zero (u : Wkp mu Omega p 1) : lowerOrder 0 u = W1p.value u :=
  by
    -- `lowerOrderL 0` is `W1p.valueL`, and `exact` unfolds `Wkp … 1` to `W1p` (`sobolevStage 0`
    -- is `firstSobolevStage`).  `W1p.value` is sealed, so the identification goes through its
    -- application theorem.
    exact W1p.valueL_apply u

/-- At first order, the generic value projection is the `W1p` value projection. -/
@[simp]
theorem value_one (u : Wkp mu Omega p 1) : value 1 u = W1p.value u := by
  simp only [value_succ, value_zero, lowerOrder_zero]

/-- At first order, the generic highest derivative is the `W1p` weak gradient. -/
@[simp]
theorem iteratedGradient_zero (u : Wkp mu Omega p 1) :
    iteratedGradient 0 u = W1p.gradient u :=
  by
    -- `iteratedGradientL 0` is `W1p.gradientL`, and `exact` unfolds `Wkp … 1` to `W1p`
    -- (`sobolevStage 0` is `firstSobolevStage`).  `W1p.gradient` is sealed, so the
    -- identification goes through its application theorem.
    exact W1p.gradientL_apply u

/-- Forgetting higher derivatives preserves the `Lᵖ` value. -/
@[simp] theorem value_firstOrder (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    W1p.value (firstOrder k u) = value (k + 1) u := by
  induction k with
  | zero => exact (value_one u).symm
  | succ k ih =>
      calc
        W1p.value (firstOrder (k + 1) u) =
            value (k + 1) (lowerOrder (k + 1) u) := by
              rw [firstOrder_succ, ih]
        _ = value (k + 1 + 1) u := (value_succ (k + 1) u).symm

/-- The highest derivative projection is the one stored in the corresponding recursive stage. -/
theorem iteratedGradient_eq_sobolevStage_iteratedGradientL
    (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    iteratedGradient k u =
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u :=
  (rfl)

/-- Above first order, the lower-order projection is the preceding-component projection of the
generic weak-derivative graph step. -/
theorem lowerOrder_succ (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    lowerOrder (k + 1) u = WeakDerivStep.prev
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u := by
  exact WeakDerivStep.prevL_apply
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

/-- Above first order, the highest derivative is the derivative component of the generic
weak-derivative graph step. -/
theorem iteratedGradient_succ (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    iteratedGradient (k + 1) u = WeakDerivStep.weakFDeriv
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u := by
  exact WeakDerivStep.weakFDerivL_apply
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

/-- Above first order, the lower-order projection is the first component of the underlying
weak-derivative graph element. -/
theorem lowerOrder_succ_coe (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    lowerOrder (k + 1) u = WithLp.fst u.1 :=
  (lowerOrder_succ k u).trans (WeakDerivStep.prev_coe _ u)

/-- Above first order, the highest derivative is the second component of the underlying
weak-derivative graph element. -/
theorem iteratedGradient_succ_coe (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    iteratedGradient (k + 1) u = WithLp.snd u.1 :=
  (iteratedGradient_succ k u).trans (WeakDerivStep.weakFDeriv_coe _ u)

/-- The first weak derivative identity, with the gradient identified with a linear functional
through the real inner product. -/
theorem hasWeakFDerivOn_value (u : Wkp mu Omega p 1) :
    HasWeakFDerivOn mu Omega (value 1 u)
      (fun x => innerSL ℝ (iteratedGradient 0 u x)) := by
  simpa only [value_one, iteratedGradient_zero] using
    W1p.hasWeakFDerivOn u

/-- Construct an order-`k+2` Sobolev function from an order-`k+1` function and a weak
derivative of its highest derivative. -/
def mk (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) : Wkp mu Omega p (k + 2) := by
  exact WeakDerivStep.mk
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u D h

/-- Forgetting the adjoined derivative of `mk k u D h` recovers `u`. -/
@[simp]
theorem lowerOrder_mk (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    lowerOrder (k + 1) (mk k u D h) = u := by
  rw [lowerOrder_succ]
  exact WeakDerivStep.prev_mk
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u D h

/-- The value component of `mk k u D h` is the value component of `u`. -/
@[simp]
theorem value_mk (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    value (k + 2) (mk k u D h) = value (k + 1) u := by
  rw [value_succ, lowerOrder_mk]

/-- The highest weak derivative of `mk k u D h` is the adjoined derivative `D`. -/
@[simp]
theorem iteratedGradient_mk (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    iteratedGradient (k + 1) (mk k u D h) = D := by
  rw [iteratedGradient_succ]
  exact WeakDerivStep.weakFDeriv_mk
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u D h

/-- The highest derivative of an order-`k+2` Sobolev function is the weak Fréchet derivative
of the highest derivative of its order-`k+1` projection. -/
theorem hasWeakFDerivOn_iteratedGradient (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    HasWeakFDerivOn mu Omega (iteratedGradient k (lowerOrder (k + 1) u))
      (iteratedGradient (k + 1) u) := by
  rw [iteratedGradient_eq_sobolevStage_iteratedGradientL, lowerOrder_succ,
    iteratedGradient_succ]
  exact WeakDerivStep.hasWeakFDerivOn_base_prev
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

/-- Two positive-order Sobolev functions are equal when their lower-order components are equal;
uniqueness of weak derivatives determines the highest components. -/
theorem ext_lowerOrder (k : ℕ) {u v : Wkp mu Omega p (k + 1)}
    (h : lowerOrder k u = lowerOrder k v) : u = v := by
  cases k with
  | zero => exact W1p.ext_value (by simpa only [lowerOrder_zero] using h)
  | succ k =>
      rw [lowerOrder_succ, lowerOrder_succ] at h
      exact WeakDerivStep.ext h

/-- Two arbitrary-order Sobolev functions are equal when their `Lᵖ` value components are equal.
Successive uniqueness of weak derivatives determines every higher component. -/
@[ext]
theorem ext : ∀ (k : ℕ) {u v : Wkp mu Omega p k}, value k u = value k v → u = v
  | 0, _, _, h => by simpa only [value_zero] using h
  | 1, _, _, h => W1p.ext_value (by simpa only [value_one] using h)
  | k + 2, _, _, h => ext_lowerOrder (k + 1) (ext (k + 1) (by
      simpa only [value_succ] using h))

/-- The graph norm controls the one-order-lower Sobolev component. -/
theorem norm_lowerOrder_le (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    ‖lowerOrder k u‖ ≤ ‖u‖ := by
  cases k with
  | zero =>
      rw [lowerOrder_zero]
      exact W1p.norm_value_le u
  | succ k =>
      rw [lowerOrder_succ]
      exact WeakDerivStep.norm_prev_le
        (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

/-- The iterated graph norm controls the `Lᵖ` value component at every order. -/
theorem norm_value_le : ∀ (k : ℕ) (u : Wkp mu Omega p k), ‖value k u‖ ≤ ‖u‖
  | 0, u => by simpa only [value_zero] using le_rfl
  | k + 1, u =>
      (norm_value_le k (lowerOrder k u)).trans (norm_lowerOrder_le k u)

/-- The graph norm controls the highest weak derivative. -/
theorem norm_iteratedGradient_le (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    ‖iteratedGradient k u‖ ≤ ‖u‖ := by
  cases k with
  | zero =>
      rw [iteratedGradient_zero]
      exact W1p.norm_gradient_le u
  | succ k =>
      rw [iteratedGradient_succ]
      exact WeakDerivStep.norm_weakFDeriv_le
        (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

/-- At order at least two, and for every exponent `p`, the squared graph norm is the sum of the
squared norms of the lower-order component and the highest weak derivative. -/
theorem norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) :
    ‖u‖ ^ 2 = ‖lowerOrder (k + 1) u‖ ^ 2 + ‖iteratedGradient (k + 1) u‖ ^ 2 := by
  rw [lowerOrder_succ, iteratedGradient_succ]
  exact WeakDerivStep.norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

/-- At exponent two, the squared graph norm at every positive order is the sum of the squared
norm of the lower-order component and the squared norm of the highest weak derivative.  The
exponent matters only at order one, where the norm is that of `TauCeti.W1p`; from order two on the
identity holds for every `p`
(`TauCeti.Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ`). -/
theorem norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq (k : ℕ)
    (u : Wkp mu Omega 2 (k + 1)) :
    ‖u‖ ^ 2 = ‖lowerOrder k u‖ ^ 2 + ‖iteratedGradient k u‖ ^ 2 := by
  cases k with
  | zero =>
      rw [lowerOrder_zero, iteratedGradient_zero]
      exact W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u
  | succ k =>
      exact norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u

/-- Convergence in a positive-order Sobolev norm is equivalent to convergence of the
preceding Sobolev component and the highest weak derivative. -/
theorem tendsto_iff_lowerOrder_iteratedGradient (k : ℕ) {I : Type*} {l : Filter I}
    {v : I → Wkp mu Omega p (k + 1)} {u : Wkp mu Omega p (k + 1)} :
    Filter.Tendsto v l (nhds u) ↔
      Filter.Tendsto (fun i => lowerOrder k (v i)) l (nhds (lowerOrder k u)) ∧
      Filter.Tendsto (fun i => iteratedGradient k (v i)) l
        (nhds (iteratedGradient k u)) := by
  cases k with
  | zero =>
      simp only [lowerOrder_zero, iteratedGradient_zero]
      exact W1p.tendsto_iff_value_gradient
  | succ k =>
      -- Each later stage is a subtype of a `WithLp` product; its product equivalence recovers
      -- exactly the two characteristic projections, without a norm estimate.
      simp only [lowerOrder_succ_coe, iteratedGradient_succ_coe]
      refine (tendsto_subtype_rng (f := v) (x := u)).trans ?_
      rw [(WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toHomeomorph.isEmbedding.tendsto_nhds_iff]
      simp only [Function.comp_def, ContinuousLinearEquiv.coe_toHomeomorph,
        WithLp.prodContinuousLinearEquiv_apply]
      exact Prod.tendsto_iff _ _

end Wkp

end TauCeti
