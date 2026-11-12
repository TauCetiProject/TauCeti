/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Approximating a lower semicontinuous function from below

On a pseudometric space, an `ℝ≥0∞`-valued lower semicontinuous function is the pointwise supremum
of an increasing sequence of bounded Lipschitz functions. This file builds that sequence
explicitly, as the truncated inf-convolution

`lscApproxAux f n x = ⨅ y, ((f y ⊓ n).toReal + n * dist x y)`,

and packages it as a sequence in `Ω →ᵇ ℝ≥0`.

Monotone approximation from below by *bounded continuous* functions is what turns the monotone
convergence theorem into a lower semicontinuity statement for integrals against a varying measure,
which is why the target of the approximation is `Ω →ᵇ ℝ≥0` rather than merely a continuous
function: the weak topology on measures is defined by pairing with exactly these test functions.

## Main declarations

* `TauCeti.lscApproxAux`: the truncated inf-convolution, a real-valued function bounded by `n` and
  Lipschitz with constant `n`.
* `TauCeti.iSup_ofReal_lscApproxAux`: at a point where `f` is lower semicontinuous, the
  approximations increase to the value of `f`.
* `TauCeti.lscApprox`: the same sequence bundled as bounded continuous `ℝ≥0`-valued functions.
* `LowerSemicontinuous.exists_boundedContinuous_monotone_iSup_eq`: the resulting interface,
  stating only that some monotone sequence of bounded continuous functions has pointwise
  supremum `f`.

## Implementation notes

The inf-convolution is taken of the truncation `f ⊓ n` rather than of `f` itself, so that the
`n`-th approximation is bounded by `n`; truncating is what allows infinite values of `f` to be
reached in the limit. The infimum is formed in `ℝ` (rather than in `ℝ≥0∞`) because the Lipschitz
estimate is then Mathlib's `LipschitzWith.of_le_add_mul`, and because bounded continuous functions
are the intended target. The construction is the one used for `LipschitzOnWith.extend_real`.
-/

public section

open Metric Set
open scoped BoundedContinuousFunction ENNReal NNReal

namespace TauCeti

variable {Ω : Type*} [PseudoMetricSpace Ω] {f : Ω → ℝ≥0∞} {n : ℕ} {x : Ω}

/-- The `n`-th truncated inf-convolution of `f : Ω → ℝ≥0∞` on a pseudometric space: the infimum
over `y` of `(f y ⊓ n).toReal + n * dist x y`. It is nonnegative, bounded by `n`, Lipschitz with
constant `n`, increasing in `n`, and, when `f` is lower semicontinuous, increases pointwise to
`f`. -/
noncomputable def lscApproxAux (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) : ℝ :=
  ⨅ y : Ω, ((f y ⊓ (n : ℝ≥0∞)).toReal + n * dist x y)

/-- The family whose infimum defines `TauCeti.lscApproxAux` is bounded below by `0`. This is an
internal step towards `TauCeti.lscApproxAux_le_add`, which is the bound consumers use. -/
private theorem bddBelow_range_lscApproxAux (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) :
    BddBelow (range fun y : Ω ↦ (f y ⊓ (n : ℝ≥0∞)).toReal + n * dist x y) :=
  ⟨0, forall_mem_range.2 fun _ ↦ by positivity⟩

/-- The defining upper bound for `TauCeti.lscApproxAux`, one for each competitor `y`. -/
theorem lscApproxAux_le_add (f : Ω → ℝ≥0∞) (n : ℕ) (x y : Ω) :
    lscApproxAux f n x ≤ (f y ⊓ (n : ℝ≥0∞)).toReal + n * dist x y :=
  ciInf_le (bddBelow_range_lscApproxAux f n x) y

/-- A lower bound valid for every competitor `y` is a lower bound for
`TauCeti.lscApproxAux`. -/
theorem le_lscApproxAux {a : ℝ} (h : ∀ y, a ≤ (f y ⊓ (n : ℝ≥0∞)).toReal + n * dist x y) :
    a ≤ lscApproxAux f n x :=
  have : Nonempty Ω := ⟨x⟩
  le_ciInf h

/-- The approximations are nonnegative. -/
theorem lscApproxAux_nonneg (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) : 0 ≤ lscApproxAux f n x :=
  le_lscApproxAux fun _ ↦ by positivity

/-- Taking `y = x` in the defining infimum bounds the approximation by the truncation of `f`
at `x`. -/
theorem lscApproxAux_le_toReal_inf (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) :
    lscApproxAux f n x ≤ (f x ⊓ (n : ℝ≥0∞)).toReal := by
  simpa using lscApproxAux_le_add f n x x

/-- The `n`-th approximation is bounded by `n`. -/
theorem lscApproxAux_le_natCast (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) : lscApproxAux f n x ≤ n :=
  (lscApproxAux_le_toReal_inf f n x).trans <|
    ENNReal.toReal_le_of_le_ofReal n.cast_nonneg (by simp)

/-- Every approximation lies below `f`. -/
theorem ofReal_lscApproxAux_le (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) :
    ENNReal.ofReal (lscApproxAux f n x) ≤ f x :=
  (ENNReal.ofReal_le_of_le_toReal (lscApproxAux_le_toReal_inf f n x)).trans inf_le_left

/-- The `n`-th approximation is Lipschitz with constant `n`. -/
theorem lipschitzWith_lscApproxAux (f : Ω → ℝ≥0∞) (n : ℕ) :
    LipschitzWith (n : ℝ≥0) (lscApproxAux f n) := by
  refine LipschitzWith.of_le_add_mul _ fun x y ↦ sub_le_iff_le_add.1 <| le_lscApproxAux fun z ↦ ?_
  rw [sub_le_iff_le_add]
  calc lscApproxAux f n x ≤ (f z ⊓ (n : ℝ≥0∞)).toReal + n * dist x z := lscApproxAux_le_add f n x z
    _ ≤ (f z ⊓ (n : ℝ≥0∞)).toReal + n * (dist x y + dist y z) := by
        gcongr; exact dist_triangle ..
    _ = (f z ⊓ (n : ℝ≥0∞)).toReal + n * dist y z + (n : ℝ≥0) * dist x y := by push_cast; ring

/-- The approximations are continuous. -/
theorem continuous_lscApproxAux (f : Ω → ℝ≥0∞) (n : ℕ) : Continuous (lscApproxAux f n) :=
  (lipschitzWith_lscApproxAux f n).continuous

/-- The approximations increase with `n`, both the truncation level and the Lipschitz constant
growing. -/
theorem monotone_lscApproxAux (f : Ω → ℝ≥0∞) (x : Ω) : Monotone fun n : ℕ ↦ lscApproxAux f n x :=
  fun m n hmn ↦ le_lscApproxAux fun y ↦ (lscApproxAux_le_add f m x y).trans <| by
    gcongr
    exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) inf_le_right

/-- At a point where `f : Ω → ℝ≥0∞` is lower semicontinuous, its truncated inf-convolutions
increase to the value of `f`. -/
theorem iSup_ofReal_lscApproxAux (hf : LowerSemicontinuousAt f x) :
    ⨆ n : ℕ, ENNReal.ofReal (lscApproxAux f n x) = f x := by
  refine le_antisymm (iSup_le fun n ↦ ofReal_lscApproxAux_le f n x)
    (le_of_forall_lt_imp_le_of_dense fun b hbf ↦ ?_)
  -- `b` is a strict lower bound for `f` on a ball `ball x ε`, and `b ≠ ∞`; once
  -- `n ≥ max b (b / ε)`, every competitor in the infimum defining the `n`-th approximation
  -- is at least `b`.
  have hb : b ≠ ∞ := (hbf.trans_le le_top).ne
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hf b hbf)
  obtain ⟨n, hn⟩ := exists_nat_ge (max b.toReal (b.toReal / ε))
  have hnb : b.toReal ≤ n := (le_max_left _ _).trans hn
  have hne : b.toReal ≤ n * ε := (div_le_iff₀ hε).1 ((le_max_right _ _).trans hn)
  refine le_iSup_of_le n <| (ENNReal.le_ofReal_iff_toReal_le hb (lscApproxAux_nonneg f n x)).2 <|
    le_lscApproxAux fun y ↦ ?_
  rcases lt_or_ge (dist x y) ε with hy | hy
  · have hbn : b ≤ (n : ℝ≥0∞) := by
      simpa using (ENNReal.le_ofReal_iff_toReal_le hb n.cast_nonneg).2 hnb
    have : b.toReal ≤ (f y ⊓ (n : ℝ≥0∞)).toReal :=
      ENNReal.toReal_mono (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) inf_le_right)
        (le_inf (hball (by rwa [dist_comm])).le hbn)
    linarith [show (0 : ℝ) ≤ n * dist x y by positivity]
  · have : (n : ℝ) * ε ≤ n * dist x y := by gcongr
    linarith [ENNReal.toReal_nonneg (a := f y ⊓ (n : ℝ≥0∞))]

/-- The truncated inf-convolution of `f : Ω → ℝ≥0∞`, bundled as a bounded continuous
`ℝ≥0`-valued function: the nonnegative part of `TauCeti.lscApproxAux f n`, which is bounded
by `n`. -/
noncomputable def lscApprox (f : Ω → ℝ≥0∞) (n : ℕ) : Ω →ᵇ ℝ≥0 :=
  (BoundedContinuousFunction.ofNormedAddCommGroup (lscApproxAux f n) (continuous_lscApproxAux f n)
    n fun x ↦ by
      rw [Real.norm_of_nonneg (lscApproxAux_nonneg f n x)]
      exact lscApproxAux_le_natCast f n x).nnrealPart

/-- The value of the bundled approximation, as a nonnegative real. This is deliberately not
`@[simp]`: the `ℝ≥0∞` coercion `TauCeti.coe_lscApprox_apply` is the simp-normal form, and marking
this lemma as well would pre-simplify that lemma's left-hand side (the `simpNF` linter rejects
the pair). -/
theorem lscApprox_apply (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) :
    lscApprox f n x = (lscApproxAux f n x).toNNReal :=
  (rfl)

/-- The value of the bundled approximation, as an element of `ℝ≥0∞`. -/
@[simp]
theorem coe_lscApprox_apply (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) :
    (lscApprox f n x : ℝ≥0∞) = ENNReal.ofReal (lscApproxAux f n x) :=
  (rfl)

/-- The bundled approximations increase pointwise with `n`. -/
theorem monotone_coe_lscApprox (f : Ω → ℝ≥0∞) :
    Monotone fun n : ℕ ↦ fun x ↦ ((lscApprox f n x : ℝ≥0) : ℝ≥0∞) := fun _ _ hmn x ↦ by
  simpa only [coe_lscApprox_apply] using
    ENNReal.ofReal_le_ofReal (monotone_lscApproxAux f x hmn)

/-- At a point where `f` is lower semicontinuous, the bundled approximations increase to the
value of `f`. -/
theorem iSup_coe_lscApprox (hf : LowerSemicontinuousAt f x) :
    ⨆ n : ℕ, ((lscApprox f n x : ℝ≥0) : ℝ≥0∞) = f x := by
  simpa only [coe_lscApprox_apply] using iSup_ofReal_lscApproxAux hf

/-- On a pseudometric space, a lower semicontinuous `f : Ω → ℝ≥0∞` is the pointwise supremum of
an increasing sequence of bounded continuous `ℝ≥0`-valued functions. -/
theorem _root_.LowerSemicontinuous.exists_boundedContinuous_monotone_iSup_eq
    (hf : LowerSemicontinuous f) :
    ∃ g : ℕ → (Ω →ᵇ ℝ≥0), (Monotone fun n ↦ fun x ↦ ((g n x : ℝ≥0) : ℝ≥0∞)) ∧
      ∀ x, ⨆ n, ((g n x : ℝ≥0) : ℝ≥0∞) = f x :=
  ⟨lscApprox f, monotone_coe_lscApprox f, fun x ↦ iSup_coe_lscApprox (hf x)⟩

end TauCeti
