/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.UnitInterval

/-!
# Graphons

A **graphon** on a probability space `(Ω, μ)` is a `[0, 1]`-valued symmetric kernel: an
everywhere-defined `W : Ω → Ω → ℝ` that is symmetric, jointly measurable, and takes values in
`[0, 1]`. It is the limit object of the dense graph limit theory.

**A graphon is a kernel with a range constraint, not a new carrier.** `Graphon` extends
`SymmKernel`, so symmetry and measurability are inherited rather than restated, and every
kernel-level construction applies to a graphon through `Graphon.toSymmKernel`. That projection is
what lets the cut norm — defined on kernels, so that a *difference* `U - W` of graphons is in its
domain — be applied to graphons without a second definition.

**Graphons carry no algebra.** They are deliberately not an `AddCommGroup` or a `Module`: the
`[0, 1]` constraint is not preserved by addition, negation, or scaling, so `U - W` is a kernel and
not a graphon. This is exactly why the roadmap puts the cut norm on `SymmKernel` and the range
constraint here.

**The measure is a genuine parameter here.** Unlike `SymmKernel`, whose measure is a phantom
argument, `Graphon` requires `[IsProbabilityMeasure μ]`: the analytic theory built on graphons —
homomorphism densities, the cut metric, sampling — integrates against `μ` and needs total mass one.

## Main definitions

* `TauCeti.DenseGraphLimits.Graphon` — the `[0, 1]`-valued symmetric kernel, with a `FunLike`
  coercion, extensionality by the underlying function, and the `toSymmKernel` projection.
* `TauCeti.DenseGraphLimits.Graphon.const` — the constant graphon with value `p : I`.
* `TauCeti.DenseGraphLimits.Graphon.clampSymm` — turn a measurable real-valued kernel into a
  graphon by averaging with its transpose and clamping to `[0, 1]`.

## Main results

* `Graphon.symm`, `Graphon.measurable` — symmetry and joint measurability, inherited from the
  kernel;
* `Graphon.nonneg`, `Graphon.le_one` — the pointwise range constraint, in eliminator form;
* `Graphon.const_apply` — the constant graphon evaluates to its parameter.
* `Graphon.clampSymm_apply_of_mem` — symmetrizing and clamping leaves a symmetric value already in
  `[0, 1]` unchanged.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — the graphon carrier and the
  constant graphon. The signature follows `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`.
  Homomorphism densities, the cut norm and cut distance, the `GraphonSpace` quotient and its
  a.e.-identification, and the step graphon of a finite graph are separate targets and are not built
  here.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013).
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §7.
-/

public section

open MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A **graphon**: a `[0, 1]`-valued symmetric kernel on a probability space.

Extends `SymmKernel`, so symmetry, measurability and boundedness come from there; the only new
field is the pointwise range constraint. -/
structure Graphon (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    extends SymmKernel Ω μ where
  /-- A graphon takes values in `[0, 1]`. Stated via `Graphon.nonneg` and `Graphon.le_one`. -/
  mem01' : ∀ x y, toFun x y ∈ Set.Icc (0 : ℝ) 1

namespace Graphon

/-- A graphon acts as its underlying function `Ω → Ω → ℝ`. -/
instance instFunLike : FunLike (Graphon Ω μ) Ω (Ω → ℝ) where
  coe W := W.toSymmKernel
  coe_injective W W' h := by
    cases W
    cases W'
    congr 1
    exact DFunLike.coe_injective h

/-- Constructing a graphon does not change the underlying function of its symmetric kernel. -/
@[simp]
theorem coe_mk (K : SymmKernel Ω μ) (hmem) : ⇑(Graphon.mk K hmem) = ⇑K := rfl

/-- Projecting a graphon to its kernel does not change the underlying function. -/
@[simp]
theorem coe_toSymmKernel (W : Graphon Ω μ) : ⇑W.toSymmKernel = ⇑W := rfl

/-- Two graphons agreeing pointwise are equal: the range constraint is a proposition, so the
underlying function determines the graphon. -/
@[ext]
theorem ext {W W' : Graphon Ω μ} (h : ∀ x y, W x y = W' x y) : W = W' :=
  DFunLike.ext _ _ fun x => funext fun y => h x y

/-- A graphon is symmetric, inherited from the underlying kernel. -/
theorem symm (W : Graphon Ω μ) (x y : Ω) : W x y = W y x := W.symm' x y

/-- A graphon is jointly measurable, inherited from the underlying kernel. -/
theorem measurable (W : Graphon Ω μ) : Measurable (Function.uncurry (W : Ω → Ω → ℝ)) := W.meas'

/-- A graphon takes values in `[0, 1]`. -/
theorem mem_Icc (W : Graphon Ω μ) (x y : Ω) : W x y ∈ Set.Icc (0 : ℝ) 1 := W.mem01' x y

/-- A graphon is nonnegative. -/
theorem nonneg (W : Graphon Ω μ) (x y : Ω) : 0 ≤ W x y := (W.mem_Icc x y).1

/-- A graphon is bounded above by `1`. -/
theorem le_one (W : Graphon Ω μ) (x y : Ω) : W x y ≤ 1 := (W.mem_Icc x y).2

/-- Average a measurable real-valued kernel with its transpose and clamp the result to `[0, 1]`.

This is the common strict-representative construction: averaging enforces pointwise symmetry, and
clamping enforces the graphon range without changing values that were already symmetric and in
`[0, 1]`. -/
@[expose]
noncomputable def clampSymm (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → Ω → ℝ)
    (hf : Measurable (Function.uncurry f)) : Graphon Ω μ where
  toSymmKernel :=
    { toFun := fun x y => max 0 (min 1 ((f x y + f y x) / 2))
      symm' := fun x y => by simp only [add_comm]
      meas' := measurable_const.max (measurable_const.min
        ((hf.add (hf.comp (measurable_snd.prodMk measurable_fst))).div_const 2))
      bdd' := ⟨1, fun x y => abs_le.2
        ⟨by linarith [le_max_left (0 : ℝ) (min 1 ((f x y + f y x) / 2))],
          max_le zero_le_one (min_le_left _ _)⟩⟩ }
  mem01' := fun x y => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- Evaluating `clampSymm` gives the averaged and clamped kernel. -/
@[simp]
theorem clampSymm_apply (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → Ω → ℝ)
    (hf : Measurable (Function.uncurry f)) (x y : Ω) :
    clampSymm μ f hf x y = max 0 (min 1 ((f x y + f y x) / 2)) := rfl

/-- Symmetrizing and clamping does not change a value that is symmetric and already in `[0, 1]`. -/
theorem clampSymm_apply_of_mem (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → Ω → ℝ)
    (hf : Measurable (Function.uncurry f)) {x y : Ω} (hsymm : f x y = f y x)
    (hmem : f x y ∈ Set.Icc (0 : ℝ) 1) : clampSymm μ f hf x y = f x y := by
  rw [clampSymm_apply, ← hsymm, add_self_div_two, min_eq_right hmem.2,
    max_eq_right hmem.1]

/-- The **constant graphon** with value `p`.

The parameter is taken in `unitInterval`, the same convention Mathlib's
`SimpleGraph.binomialRandom` uses for `G(V, p)`, so that the later sampling compatibility statement
needs no translation. -/
def const (μ : Measure Ω) [IsProbabilityMeasure μ] (p : I) : Graphon Ω μ where
  toFun _ _ := (p : ℝ)
  symm' _ _ := rfl
  meas' := measurable_const
  bdd' := ⟨1, fun _ _ => by
    rw [abs_of_nonneg p.2.1]
    exact p.2.2⟩
  mem01' _ _ := p.2

/-- The constant graphon evaluates to its parameter at every pair of points. -/
@[simp]
theorem const_apply (μ : Measure Ω) [IsProbabilityMeasure μ] (p : I) (x y : Ω) :
    const μ p x y = (p : ℝ) := (rfl)

end Graphon

end DenseGraphLimits

end TauCeti
