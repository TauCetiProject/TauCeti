/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.FiniteDimensional
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Coprod

/-!
# Incidence equations and parametric transversality to a map

Let `F : E × P → V` be a family of maps parametrized by `p : P` and `j : W → V` a target map. The
slice `x ↦ F (x, p)` is transverse to `j` when, at every incidence pair `(x, y)` with
`F (x, p) = j y`, the images of `fderiv ℝ (fun x' ↦ F (x', p)) x` and `fderiv ℝ j y` together span
`V`, equivalently when `(u, v) ↦ d_x F(x, p) u - dj(y) v` is surjective. Writing the incidence
equation as `TauCeti.incidenceEquation F j ((x, y), p) = F (x, p) - j y` puts the spatial pair
`(x, y) : E × W` in the first factor and the parameter `p : P` in the second, matching
`TauCeti.IsRegularParameter` and `TauCeti.IsRegularParameterOn`.

This file builds the derivative, invariance, dimension-counting, and measure-theoretic generic
parameter API for `TauCeti.incidenceEquation`:

* `TauCeti.incidenceEquation`: the map `((x, y), p) ↦ F (x, p) - j y` on `(E × W) × P`.
* `TauCeti.IsRegularIncidenceParameter` and `TauCeti.IsRegularIncidenceParameterOn`: regularity of
  a parameter `p` for `incidenceEquation F j` at level `0`, globally or on a subset
  `U ⊆ (E × W) × P`.
* `TauCeti.isRegularIncidenceParameterOn_iff_coprod` and
  `TauCeti.isRegularIncidenceParameterOn_iff_range_sup_eq_top`: slice-transversality criteria in
  terms of `(fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)` and the span of the two
  derivative ranges, assuming differentiability only along the incidence locus in `U`.
* `TauCeti.surjective_fderiv_incidenceEquation_iff`: universal transversality at `((x, y), p)` is
  surjectivity of `(fderiv ℝ F (x, p)).coprod (-fderiv ℝ j y)`.
* `TauCeti.IsRegularIncidenceParameterOn.of_maps`: functoriality under maps on `E`, `W`, and `V`
  whose derivatives at incidence points are surjective on the sources and surjective/injective on
  the target, giving invariance under continuous linear equivalences
  (`TauCeti.isRegularIncidenceParameter_comp_equiv_iff`).
* `TauCeti.disjoint_range_of_isRegularIncidenceParameter`: when
  `finrank ℝ E + finrank ℝ W < finrank ℝ V`, a regular incidence parameter avoids `range j`
  entirely (requiring neither differentiability of `F`, `j` nor finite-dimensionality of `V`).
* `TauCeti.addHaar_setOf_not_isRegularIncidenceParameterOn_eq_zero` and
  `TauCeti.addHaar_setOf_not_isRegularIncidenceParameter`: in finite dimensions, under universal
  transversality and `C^n` smoothness above the Morse--Sard threshold
  `finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 ≤ n`, almost every parameter for additive Haar
  measure has a transverse slice, with countable-family corollaries
  `TauCeti.ae_forall_isRegularIncidenceParameterOn` and
  `TauCeti.ae_forall_disjoint_range_of_finrank_lt`.
* Concrete witnesses for the quadratic family `(x, p) ↦ x ^ 2 + p` on `ℝ`, characterizing regular
  parameters against the origin (`p ≠ 0`) and against the identity (`∀ p, True`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2012, Chapter 6, Theorem 6.35 (Parametric Transversality Theorem).
* V. Guillemin, A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1 §5 and
  Chapter 2 §3.
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 3, Theorem 2.7.
-/

public section

open Filter Function MeasureTheory MeasureTheory.Measure Module Set
open scoped ContDiff Topology

namespace TauCeti

section Algebraic

/-- The incidence equation `((x, y), p) ↦ F (x, p) - j y` associated with a parametrized family
`F : E × P → V` and a map `j : W → V`. Grouping `(x, y)` in the first factor places the parameter
`p` in the second factor expected by `TauCeti.IsRegularParameter`. -/
def incidenceEquation {E W P V : Type*} [Sub V] (F : E × P → V) (j : W → V) :
    (E × W) × P → V :=
  fun z ↦ F (z.1.1, z.2) - j z.1.2

/-- Characteristic unfolding of `TauCeti.incidenceEquation` at an arbitrary triple `z`. -/
theorem incidenceEquation_def {E W P V : Type*} [Sub V] (F : E × P → V) (j : W → V)
    (z : (E × W) × P) :
    incidenceEquation F j z = F (z.1.1, z.2) - j z.1.2 :=
  (rfl)

/-- Evaluation of `TauCeti.incidenceEquation` at `(xy, p)`. -/
@[simp]
theorem incidenceEquation_pair {E W P V : Type*} [Sub V] (F : E × P → V) (j : W → V)
    (xy : E × W) (p : P) :
    incidenceEquation F j (xy, p) = F (xy.1, p) - j xy.2 :=
  (rfl)

/-- Evaluation of `TauCeti.incidenceEquation` at `((x, y), p)`. -/
theorem incidenceEquation_mk {E W P V : Type*} [Sub V] (F : E × P → V) (j : W → V)
    (x : E) (y : W) (p : P) :
    incidenceEquation F j ((x, y), p) = F (x, p) - j y :=
  (rfl)

/-- The incidence equation vanishes at `((x, y), p)` precisely at an incidence `F (x, p) = j y`. -/
theorem incidenceEquation_eq_zero_iff {E W P V : Type*} [AddGroup V] {F : E × P → V} {j : W → V}
    {x : E} {y : W} {p : P} :
    incidenceEquation F j ((x, y), p) = 0 ↔ F (x, p) = j y :=
  sub_eq_zero

end Algebraic

section Normed

variable {E W P V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A parameter `p : P` is a **regular incidence parameter** for `F : E × P → V` against
`j : W → V` when `p` is regular at level `0` for `TauCeti.incidenceEquation F j`: at every pair
`(x, y)` with `F (x, p) = j y`, the partial linearization of `incidenceEquation F j` along `E × W`
is surjective. -/
def IsRegularIncidenceParameter (F : E × P → V) (j : W → V) (p : P) : Prop :=
  IsRegularParameter (incidenceEquation F j) 0 p

/-- Unfolding `TauCeti.IsRegularIncidenceParameter` to `TauCeti.IsRegularParameter`. -/
theorem isRegularIncidenceParameter_iff {F : E × P → V} {j : W → V} {p : P} :
    IsRegularIncidenceParameter F j p ↔
      ∀ xy : E × W, F (xy.1, p) = j xy.2 →
        Surjective
          ((fderiv ℝ (incidenceEquation F j) (xy, p)).comp
            (ContinuousLinearMap.inl ℝ (E × W) P)) := by
  simp only [IsRegularIncidenceParameter, isRegularParameter_iff, incidenceEquation_pair,
    sub_eq_zero]

/-- Subset-localized variant of `TauCeti.IsRegularIncidenceParameter`: regularity of `p` is
required only at incidence points `((x, y), p) ∈ U`. -/
def IsRegularIncidenceParameterOn (F : E × P → V) (j : W → V)
    (U : Set ((E × W) × P)) (p : P) : Prop :=
  IsRegularParameterOn (incidenceEquation F j) U 0 p

/-- Unfolding `TauCeti.IsRegularIncidenceParameterOn` to `TauCeti.IsRegularParameterOn`. -/
theorem isRegularIncidenceParameterOn_iff {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p : P} :
    IsRegularIncidenceParameterOn F j U p ↔
      ∀ xy : E × W, (xy, p) ∈ U → F (xy.1, p) = j xy.2 →
        Surjective
          ((fderiv ℝ (incidenceEquation F j) (xy, p)).comp
            (ContinuousLinearMap.inl ℝ (E × W) P)) := by
  simp only [IsRegularIncidenceParameterOn, isRegularParameterOn_iff, incidenceEquation_pair,
    sub_eq_zero]

/-- Incidence regularity on `univ` coincides with global incidence regularity. -/
@[simp]
theorem isRegularIncidenceParameterOn_univ {F : E × P → V} {j : W → V} {p : P} :
    IsRegularIncidenceParameterOn F j univ p ↔ IsRegularIncidenceParameter F j p :=
  isRegularParameterOn_univ

/-- Every parameter is vacuously regular on the empty set. -/
@[simp]
theorem isRegularIncidenceParameterOn_empty (F : E × P → V) (j : W → V) (p : P) :
    IsRegularIncidenceParameterOn F j ∅ p :=
  isRegularParameterOn_iff.2 fun _ h ↦ False.elim h

/-- Incidence regularity on a set is inherited by subsets. -/
theorem IsRegularIncidenceParameterOn.mono {F : E × P → V} {j : W → V}
    {U U' : Set ((E × W) × P)} {p : P} (hUU' : U ⊆ U')
    (h : IsRegularIncidenceParameterOn F j U' p) :
    IsRegularIncidenceParameterOn F j U p :=
  IsRegularParameterOn.mono hUU' h

/-- A globally regular incidence parameter is regular on every subset. -/
theorem IsRegularIncidenceParameter.isRegularIncidenceParameterOn {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p : P} (h : IsRegularIncidenceParameter F j p) :
    IsRegularIncidenceParameterOn F j U p :=
  IsRegularParameter.isRegularParameterOn h

/-- Any parameter whose slice misses `range j` inside `U` is vacuously regular on `U`. -/
theorem isRegularIncidenceParameterOn_of_forall_ne {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p : P}
    (hne : ∀ x y, ((x, y), p) ∈ U → F (x, p) ≠ j y) :
    IsRegularIncidenceParameterOn F j U p :=
  isRegularIncidenceParameterOn_iff.2 fun ⟨x, y⟩ hU hEq ↦ False.elim (hne x y hU hEq)

/-- Any parameter whose slice misses `range j` is vacuously a regular incidence parameter. -/
theorem isRegularIncidenceParameter_of_forall_ne {F : E × P → V} {j : W → V} {p : P}
    (hne : ∀ x y, F (x, p) ≠ j y) :
    IsRegularIncidenceParameter F j p :=
  isRegularIncidenceParameterOn_univ.1 <|
    isRegularIncidenceParameterOn_of_forall_ne fun x y _ ↦ hne x y

/-- On an open subset `U ⊆ (E × W) × P`, `TauCeti.IsRegularIncidenceParameterOn` depends only on
the values of `incidenceEquation F j` on `U`. -/
theorem _root_.IsOpen.isRegularIncidenceParameterOn_congr {F F' : E × P → V} {j j' : W → V}
    {U : Set ((E × W) × P)} (hU : IsOpen U) {p : P}
    (hEq : EqOn (incidenceEquation F j) (incidenceEquation F' j') U) :
    IsRegularIncidenceParameterOn F j U p ↔ IsRegularIncidenceParameterOn F' j' U p := by
  rw [IsRegularIncidenceParameterOn, IsRegularIncidenceParameterOn,
    isRegularParameterOn_iff, isRegularParameterOn_iff]
  refine forall_congr' fun xy ↦ imp_congr_right fun hxyU ↦ ?_
  have hev : incidenceEquation F j =ᶠ[𝓝 (xy, p)] incidenceEquation F' j' :=
    hEq.eventuallyEq_of_mem (hU.mem_nhds hxyU)
  rw [hEq hxyU, hev.fderiv_eq]

/-- Total Fréchet derivative of `TauCeti.incidenceEquation` at `((x, y), p)`. -/
theorem hasFDerivAt_incidenceEquation {F : E × P → V} {j : W → V}
    {DF : E × P →L[ℝ] V} {Dj : W →L[ℝ] V} {x : E} {y : W} {p : P}
    (hF : HasFDerivAt F DF (x, p)) (hj : HasFDerivAt j Dj y) :
    HasFDerivAt (incidenceEquation F j)
      (DF.comp (((ContinuousLinearMap.fst ℝ E W).comp
          (ContinuousLinearMap.fst ℝ (E × W) P)).prod
          (ContinuousLinearMap.snd ℝ (E × W) P)) -
        Dj.comp ((ContinuousLinearMap.snd ℝ E W).comp
          (ContinuousLinearMap.fst ℝ (E × W) P)))
      ((x, y), p) := by
  have h1 : HasFDerivAt (fun z : (E × W) × P ↦ (z.1.1, z.2))
      (((ContinuousLinearMap.fst ℝ E W).comp (ContinuousLinearMap.fst ℝ (E × W) P)).prod
        (ContinuousLinearMap.snd ℝ (E × W) P)) ((x, y), p) :=
    (hasFDerivAt_fst.comp ((x, y), p) hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have h2 : HasFDerivAt (fun z : (E × W) × P ↦ z.1.2)
      ((ContinuousLinearMap.snd ℝ E W).comp (ContinuousLinearMap.fst ℝ (E × W) P)) ((x, y), p) :=
    hasFDerivAt_snd.comp ((x, y), p) hasFDerivAt_fst
  exact (hF.comp ((x, y), p) h1).sub (hj.comp ((x, y), p) h2)

/-- Formula for `fderiv ℝ (incidenceEquation F j) ((x, y), p)` applied to `((u, v), q)`. -/
theorem fderiv_incidenceEquation_apply {F : E × P → V} {j : W → V} {x : E} {y : W} {p : P}
    (hF : DifferentiableAt ℝ F (x, p)) (hj : DifferentiableAt ℝ j y)
    (u : E) (v : W) (q : P) :
    fderiv ℝ (incidenceEquation F j) ((x, y), p) ((u, v), q) =
      fderiv ℝ F (x, p) (u, q) - fderiv ℝ j y v := by
  rw [(hasFDerivAt_incidenceEquation hF.hasFDerivAt hj.hasFDerivAt).fderiv]
  rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Fréchet derivative of the fixed-parameter map `xy ↦ incidenceEquation F j (xy, p)` at `(x, y)`:
given derivatives `DFx` of the slice `x' ↦ F (x', p)` at `x` and `Dj` of `j` at `y`, it equals
`DFx.coprod (-Dj)`. Neither a norm on `P` nor joint differentiability of `F` is needed. -/
theorem hasFDerivAt_incidenceEquation_slice {F : E × P → V} {j : W → V}
    {DFx : E →L[ℝ] V} {Dj : W →L[ℝ] V} {x : E} {y : W} {p : P}
    (hFx : HasFDerivAt (fun x' ↦ F (x', p)) DFx x) (hj : HasFDerivAt j Dj y) :
    HasFDerivAt (fun xy : E × W ↦ incidenceEquation F j (xy, p))
      (DFx.coprod (-Dj)) (x, y) := by
  have h1 : HasFDerivAt ((fun x' ↦ F (x', p)) ∘ Prod.fst)
      (DFx.comp (ContinuousLinearMap.fst ℝ E W)) (x, y) :=
    HasFDerivAt.comp (x, y) hFx hasFDerivAt_fst
  have h2 : HasFDerivAt (j ∘ Prod.snd)
      (Dj.comp (ContinuousLinearMap.snd ℝ E W)) (x, y) :=
    HasFDerivAt.comp (x, y) hj hasFDerivAt_snd
  refine (h1.sub h2).congr_fderiv (ContinuousLinearMap.ext fun ⟨u, v⟩ ↦ ?_)
  simp [sub_eq_add_neg]

/-- When `F` is jointly differentiable at `(x, p)` and `j` is differentiable at `y`, restricting
the total derivative `fderiv ℝ (incidenceEquation F j) ((x, y), p)` to `E × W` along
`ContinuousLinearMap.inl ℝ (E × W) P` equals the coproduct
`(fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)`. -/
theorem fderiv_incidenceEquation_comp_inl {F : E × P → V} {j : W → V} {x : E} {y : W} {p : P}
    (hF : DifferentiableAt ℝ F (x, p)) (hj : DifferentiableAt ℝ j y) :
    (fderiv ℝ (incidenceEquation F j) ((x, y), p)).comp
        (ContinuousLinearMap.inl ℝ (E × W) P) =
      (fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y) := by
  have hFx : HasFDerivAt (fun x' ↦ F (x', p))
      ((fderiv ℝ F (x, p)).comp (ContinuousLinearMap.inl ℝ E P)) x :=
    hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x p)
  refine ContinuousLinearMap.ext fun ⟨u, v⟩ ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    fderiv_incidenceEquation_apply hF hj, hFx.fderiv, ContinuousLinearMap.coprod_apply,
    _root_.neg_apply, sub_eq_add_neg]

/-- Smoothness of `TauCeti.incidenceEquation` at a point `z = ((x, y), p)` from smoothness of `F`
at `(x, p)` and `j` at `y`. -/
theorem contDiffAt_incidenceEquation {F : E × P → V} {j : W → V} {n : ℕ∞ω} {z : (E × W) × P}
    (hF : ContDiffAt ℝ n F (z.1.1, z.2)) (hj : ContDiffAt ℝ n j z.1.2) :
    ContDiffAt ℝ n (incidenceEquation F j) z := by
  have h1 : ContDiffAt ℝ n (fun w : (E × W) × P ↦ (w.1.1, w.2)) z :=
    (contDiffAt_fst.comp z contDiffAt_fst).prodMk contDiffAt_snd
  have h2 : ContDiffAt ℝ n (fun w : (E × W) × P ↦ w.1.2) z :=
    contDiffAt_snd.comp z contDiffAt_fst
  exact (hF.comp z h1).sub (hj.comp z h2)

/-- Global `C^n` smoothness of `TauCeti.incidenceEquation`. -/
theorem contDiff_incidenceEquation {F : E × P → V} {j : W → V} {n : ℕ∞ω}
    (hF : ContDiff ℝ n F) (hj : ContDiff ℝ n j) :
    ContDiff ℝ n (incidenceEquation F j) :=
  contDiff_iff_contDiffAt.2 fun z ↦
    contDiffAt_incidenceEquation (hF.contDiffAt (x := (z.1.1, z.2))) (hj.contDiffAt (x := z.1.2))

/-- **Universal transversality criterion.** When `F` is differentiable at `(x, p)` and `j` is
differentiable at `y`, the total derivative of `TauCeti.incidenceEquation F j` at `((x, y), p)` is
surjective if and only if `(fderiv ℝ F (x, p)).coprod (-fderiv ℝ j y)` is surjective (i.e., the
family `F` as a map on `E × P` is transverse to `j` at `((x, p), y)`). -/
theorem surjective_fderiv_incidenceEquation_iff {F : E × P → V} {j : W → V}
    {x : E} {y : W} {p : P}
    (hF : DifferentiableAt ℝ F (x, p)) (hj : DifferentiableAt ℝ j y) :
    Surjective (fderiv ℝ (incidenceEquation F j) ((x, y), p)) ↔
      Surjective ((fderiv ℝ F (x, p)).coprod (-fderiv ℝ j y)) := by
  constructor
  · intro hsurj w
    obtain ⟨⟨⟨u, v⟩, q⟩, hw⟩ := hsurj w
    refine ⟨((u, q), v), ?_⟩
    simpa [fderiv_incidenceEquation_apply hF hj, sub_eq_add_neg] using hw
  · intro hsurj w
    obtain ⟨⟨⟨u, q⟩, v⟩, hw⟩ := hsurj w
    refine ⟨((u, v), q), ?_⟩
    simpa [fderiv_incidenceEquation_apply hF hj, sub_eq_add_neg] using hw

/-- Universal transversality at `((x, y), p)` holds automatically whenever the parameter derivative
`q ↦ fderiv ℝ F (x, p) (0, q)` is already surjective. -/
theorem surjective_fderiv_incidenceEquation_of_surjective_inr {F : E × P → V} {j : W → V}
    {x : E} {y : W} {p : P}
    (hF : DifferentiableAt ℝ F (x, p)) (hj : DifferentiableAt ℝ j y)
    (hP : Surjective ((fderiv ℝ F (x, p)).comp (ContinuousLinearMap.inr ℝ E P))) :
    Surjective (fderiv ℝ (incidenceEquation F j) ((x, y), p)) := by
  intro w
  obtain ⟨q, hq⟩ := hP w
  refine ⟨((0, 0), q), ?_⟩
  simpa [fderiv_incidenceEquation_apply hF hj] using hq

/-- **Slice-transversality criterion on `U` (coproduct form).** Assuming differentiability of `F`
and `j` only at incidence points in `U`, `p` is regular on `U` if and only if
`(fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)` is surjective at every incidence point
`((x, y), p) ∈ U`. -/
theorem isRegularIncidenceParameterOn_iff_coprod {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p : P}
    (hF : ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y → DifferentiableAt ℝ j y) :
    IsRegularIncidenceParameterOn F j U p ↔
      ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y →
        Surjective ((fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)) := by
  rw [isRegularIncidenceParameterOn_iff]
  refine ⟨fun h x y hU hEq ↦ ?_, fun h ⟨x, y⟩ hU hEq ↦ ?_⟩
  · rw [← fderiv_incidenceEquation_comp_inl (hF x y hU hEq) (hj x y hU hEq)]
    exact h (x, y) hU hEq
  · rw [fderiv_incidenceEquation_comp_inl (hF x y hU hEq) (hj x y hU hEq)]
    exact h x y hU hEq

/-- **Slice-transversality criterion on `U` (subspace-sum form).** Assuming differentiability of
`F` and `j` only at incidence points in `U`, `p` is regular on `U` if and only if the ranges of
`fderiv ℝ (fun x' ↦ F (x', p)) x` and `fderiv ℝ j y` together span `V` at every incidence point
`((x, y), p) ∈ U`. -/
theorem isRegularIncidenceParameterOn_iff_range_sup_eq_top {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p : P}
    (hF : ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y → DifferentiableAt ℝ j y) :
    IsRegularIncidenceParameterOn F j U p ↔
      ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y →
        (fderiv ℝ (fun x' ↦ F (x', p)) x).range ⊔ (fderiv ℝ j y).range = ⊤ := by
  rw [isRegularIncidenceParameterOn_iff_coprod hF hj]
  refine forall₂_congr fun x y ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ ?_
  exact ContinuousLinearMap.surjective_coprod_neg_iff _ _

/-- **Global slice-transversality criterion (coproduct form).** -/
theorem isRegularIncidenceParameter_iff_coprod {F : E × P → V} {j : W → V} {p : P}
    (hF : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ j y) :
    IsRegularIncidenceParameter F j p ↔
      ∀ x y, F (x, p) = j y →
        Surjective ((fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)) := by
  rw [← isRegularIncidenceParameterOn_univ,
    isRegularIncidenceParameterOn_iff_coprod (fun x y _ ↦ hF x y) (fun x y _ ↦ hj x y)]
  simp

/-- **Global slice-transversality criterion (subspace-sum form).** -/
theorem isRegularIncidenceParameter_iff_range_sup_eq_top {F : E × P → V} {j : W → V} {p : P}
    (hF : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ j y) :
    IsRegularIncidenceParameter F j p ↔
      ∀ x y, F (x, p) = j y →
        (fderiv ℝ (fun x' ↦ F (x', p)) x).range ⊔ (fderiv ℝ j y).range = ⊤ := by
  rw [← isRegularIncidenceParameterOn_univ,
    isRegularIncidenceParameterOn_iff_range_sup_eq_top (fun x y _ ↦ hF x y) (fun x y _ ↦ hj x y)]
  simp

end Normed

section Invariance

variable {E E' W W' P P' V V' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W']
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup P'] [NormedSpace ℝ P']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']

/-- **Nonlinear coordinate-change transfer for `IsRegularIncidenceParameterOn`.** Suppose
`φ : E' → E`, `ψ : W' → W`, `τ : P' → P`, and `χ : V → V'` satisfy:
* `χ` reflects incidence equalities (`χ (F (φ x', τ p')) = χ (j (ψ y')) → F (...) = j (...)`),
* at each incidence point `((x', y'), p') ∈ U'`, `φ`, `ψ`, and `χ` have surjective derivatives,
  and `((φ x', ψ y'), τ p') ∈ U`.

Then regularity of `τ p'` on `U` transfers to regularity of `p'` on `U'` for the composed system
`z ↦ χ (F (φ z.1, τ z.2))` against `χ ∘ j ∘ ψ`. This is the local chart-transfer step for
manifold incidence transversality. -/
theorem IsRegularIncidenceParameterOn.of_maps {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {U' : Set ((E' × W') × P')}
    {φ : E' → E} {ψ : W' → W} {τ : P' → P} {χ : V → V'} {p' : P'}
    (h : IsRegularIncidenceParameterOn F j U (τ p'))
    (hmaps : ∀ x' y', ((x', y'), p') ∈ U' → χ (F (φ x', τ p')) = χ (j (ψ y')) →
      ((φ x', ψ y'), τ p') ∈ U ∧ F (φ x', τ p') = j (ψ y'))
    (hF : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      DifferentiableAt ℝ F (φ x', τ p'))
    (hj : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      DifferentiableAt ℝ j (ψ y'))
    (hφ : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      DifferentiableAt ℝ φ x' ∧ Surjective (fderiv ℝ φ x'))
    (hψ : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      DifferentiableAt ℝ ψ y' ∧ Surjective (fderiv ℝ ψ y'))
    (hτ : DifferentiableAt ℝ τ p')
    (hχ : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      DifferentiableAt ℝ χ (j (ψ y')) ∧ Surjective (fderiv ℝ χ (j (ψ y')))) :
    IsRegularIncidenceParameterOn
      (fun z : E' × P' ↦ χ (F (φ z.1, τ z.2))) (fun y' ↦ χ (j (ψ y'))) U' p' := by
  have hF' : ∀ x' y', ((x', y'), p') ∈ U' → χ (F (φ x', τ p')) = χ (j (ψ y')) →
      DifferentiableAt ℝ (fun z : E' × P' ↦ χ (F (φ z.1, τ z.2))) (x', p') := by
    intro x' y' hU' hEq'
    obtain ⟨_, hEq⟩ := hmaps x' y' hU' hEq'
    have hχd : DifferentiableAt ℝ χ (F (φ x', τ p')) := hEq.symm ▸ (hχ x' y' hU' hEq).1
    have hpair : DifferentiableAt ℝ (fun z : E' × P' ↦ (φ z.1, τ z.2)) (x', p') :=
      ((hφ x' y' hU' hEq).1.comp (x', p') differentiableAt_fst).prodMk
        (hτ.comp (x', p') differentiableAt_snd)
    exact hχd.comp (x', p') ((hF x' y' hU' hEq).comp (x', p') hpair)
  have hj' : ∀ x' y', ((x', y'), p') ∈ U' → χ (F (φ x', τ p')) = χ (j (ψ y')) →
      DifferentiableAt ℝ (fun w ↦ χ (j (ψ w))) y' := by
    intro x' y' hU' hEq'
    obtain ⟨_, hEq⟩ := hmaps x' y' hU' hEq'
    exact (hχ x' y' hU' hEq).1.comp y'
      ((hj x' y' hU' hEq).comp y' (hψ x' y' hU' hEq).1)
  rw [isRegularIncidenceParameterOn_iff_coprod hF' hj']
  intro x' y' hU' hEq'
  obtain ⟨hU, hEq⟩ := hmaps x' y' hU' hEq'
  have hFxy := hF x' y' hU' hEq
  have hjxy := hj x' y' hU' hEq
  obtain ⟨hφd, hφs⟩ := hφ x' y' hU' hEq
  obtain ⟨hψd, hψs⟩ := hψ x' y' hU' hEq
  obtain ⟨hχd, hχs⟩ := hχ x' y' hU' hEq
  have hsurj0 : Surjective
      ((fderiv ℝ (fun x ↦ F (x, τ p')) (φ x')).coprod (-fderiv ℝ j (ψ y'))) := by
    have hcomp := isRegularIncidenceParameterOn_iff.1 h (φ x', ψ y') hU hEq
    rwa [fderiv_incidenceEquation_comp_inl hFxy hjxy] at hcomp
  have hFx : HasFDerivAt (fun x'' ↦ χ (F (φ x'', τ p')))
      ((fderiv ℝ χ (j (ψ y'))).comp
        ((fderiv ℝ (fun x ↦ F (x, τ p')) (φ x')).comp (fderiv ℝ φ x'))) x' := by
    have hslice : DifferentiableAt ℝ (fun x ↦ F (x, τ p')) (φ x') :=
      hFxy.comp (φ x') (differentiableAt_id.prodMk (differentiableAt_const (τ p')))
    have hχF : HasFDerivAt χ (fderiv ℝ χ (j (ψ y'))) (F (φ x', τ p')) :=
      hEq.symm ▸ hχd.hasFDerivAt
    exact hχF.comp x' (hslice.hasFDerivAt.comp x' hφd.hasFDerivAt)
  have hjy : HasFDerivAt (fun w ↦ χ (j (ψ w)))
      ((fderiv ℝ χ (j (ψ y'))).comp ((fderiv ℝ j (ψ y')).comp (fderiv ℝ ψ y'))) y' :=
    hχd.hasFDerivAt.comp y' (hjxy.hasFDerivAt.comp y' hψd.hasFDerivAt)
  rw [hFx.fderiv, hjy.fderiv]
  intro w'
  obtain ⟨w, rfl⟩ := hχs w'
  obtain ⟨⟨u, v⟩, huv⟩ := hsurj0 w
  obtain ⟨u', rfl⟩ := hφs u
  obtain ⟨v', rfl⟩ := hψs v
  refine ⟨(u', v'), ?_⟩
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply,
    _root_.neg_apply, ← map_neg, ← map_add] at huv ⊢
  exact congrArg (fderiv ℝ χ (j (ψ y'))) huv

/-- One-way transfer of `IsRegularIncidenceParameter` along continuous linear equivalences. -/
private theorem isRegularIncidenceParameter_comp_equiv (eE : E' ≃L[ℝ] E) (eW : W' ≃L[ℝ] W)
    (eP : P' ≃L[ℝ] P) (eV : V ≃L[ℝ] V') {F : E × P → V} {j : W → V} {p' : P'}
    (h : IsRegularIncidenceParameter F j (eP p')) :
    IsRegularIncidenceParameter
      (fun z : E' × P' ↦ eV (F (eE z.1, eP z.2))) (fun y' ↦ eV (j (eW y'))) p' := by
  let eEW : (E' × W') ≃L[ℝ] (E × W) := eE.prodCongr eW
  let eTot : ((E' × W') × P') ≃L[ℝ] ((E × W) × P) := eEW.prodCongr eP
  have heq : incidenceEquation (fun z : E' × P' ↦ eV (F (eE z.1, eP z.2)))
      (fun y' ↦ eV (j (eW y'))) =
        (eV : V → V') ∘ incidenceEquation F j ∘ (eTot : (E' × W') × P' → (E × W) × P) := by
    ext ⟨⟨x', y'⟩, q'⟩
    simp [incidenceEquation, eTot, eEW]
  rw [isRegularIncidenceParameter_iff] at h ⊢
  rw [heq]
  intro ⟨x', y'⟩ hEq'
  have hsurj := h (eE x', eW y') (eV.injective hEq')
  have hpt : eTot ((x', y'), p') = ((eE x', eW y'), eP p') := by
    simp [eTot, eEW]
  rw [eV.comp_fderiv, eTot.comp_right_fderiv, hpt]
  intro w'
  obtain ⟨⟨u, v⟩, huv⟩ := hsurj (eV.symm w')
  refine ⟨(eE.symm u, eW.symm v), ?_⟩
  have : eV ((fderiv ℝ (incidenceEquation F j) ((eE x', eW y'), eP p')) ((u, v), 0)) = w' := by
    simpa using congrArg eV huv
  simpa [eTot, eEW] using this

/-- **Invariance under continuous linear equivalences** on `E`, `W`, `P`, and `V` (requiring no
differentiability hypotheses on `F` or `j`). -/
theorem isRegularIncidenceParameter_comp_equiv_iff (eE : E' ≃L[ℝ] E) (eW : W' ≃L[ℝ] W)
    (eP : P' ≃L[ℝ] P) (eV : V ≃L[ℝ] V') {F : E × P → V} {j : W → V} {p' : P'} :
    IsRegularIncidenceParameter
        (fun z : E' × P' ↦ eV (F (eE z.1, eP z.2))) (fun y' ↦ eV (j (eW y'))) p' ↔
      IsRegularIncidenceParameter F j (eP p') := by
  refine ⟨fun h ↦ ?_, isRegularIncidenceParameter_comp_equiv eE eW eP eV⟩
  have hsymm := isRegularIncidenceParameter_comp_equiv eE.symm eW.symm eP.symm eV.symm
    (p' := eP p') (by simpa using h)
  simpa using hsymm

end Invariance

section Avoidance

variable {E W P V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Dimension-counting avoidance on a set `U`.** When `E` and `W` are finite-dimensional and
`finrank ℝ E + finrank ℝ W < finrank ℝ V`, no continuous linear map `E × W →L[ℝ] V` can be
surjective, so a parameter `p` that is regular on `U` admits no incidence points in `U` at all.
Neither differentiability of `F`, `j` nor `[FiniteDimensional ℝ V]` is required. -/
theorem ne_of_isRegularIncidenceParameterOn_of_finrank_lt
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
    {F : E × P → V} {j : W → V} {U : Set ((E × W) × P)} {p : P}
    (hdim : finrank ℝ E + finrank ℝ W < finrank ℝ V)
    (hp : IsRegularIncidenceParameterOn F j U p)
    {x : E} {y : W} (hU : ((x, y), p) ∈ U) :
    F (x, p) ≠ j y := by
  intro hEq
  have hsurj := isRegularIncidenceParameterOn_iff.1 hp (x, y) hU hEq
  have hle : finrank ℝ V ≤ finrank ℝ (E × W) :=
    LinearMap.finrank_le_finrank_of_surjective hsurj
  rw [Module.finrank_prod] at hle
  omega

/-- **Dimension-counting avoidance.** When `finrank ℝ E + finrank ℝ W < finrank ℝ V` for
finite-dimensional `E` and `W`, the slice at any regular incidence parameter `p` has range disjoint
from `range j`. -/
theorem disjoint_range_of_isRegularIncidenceParameter
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
    {F : E × P → V} {j : W → V} {p : P}
    (hdim : finrank ℝ E + finrank ℝ W < finrank ℝ V)
    (hp : IsRegularIncidenceParameter F j p) :
    Disjoint (range fun x ↦ F (x, p)) (range j) := by
  refine disjoint_iff_forall_ne.2 ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact ne_of_isRegularIncidenceParameterOn_of_finrank_lt hdim
    hp.isRegularIncidenceParameterOn (mem_univ _)

/-- When `E` and `W` are finite-dimensional and `V` is infinite-dimensional, the slice at any
regular incidence parameter `p` likewise misses `range j`. -/
theorem disjoint_range_of_isRegularIncidenceParameter_of_not_finiteDimensional
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
    (hV : ¬ FiniteDimensional ℝ V) {F : E × P → V} {j : W → V} {p : P}
    (hp : IsRegularIncidenceParameter F j p) :
    Disjoint (range fun x ↦ F (x, p)) (range j) := by
  refine disjoint_iff_forall_ne.2 ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hEq
  have hsurj := isRegularIncidenceParameter_iff.1 hp (x, y) hEq
  exact hV (Module.Finite.of_surjective _ hsurj)

end Avoidance

section FiniteDimensionalGeneric

variable {E W P V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Generic incidence parameters on a subset `U` (measure form).** Let `F : E × P → V` and
`j : W → V` be maps between finite-dimensional real normed spaces, and `U ⊆ (E × W) × P` any set.
If at every incidence point `z = ((x, y), p) ∈ U` with `F (x, p) = j y`, `F` is `C^n` at `(x, p)`,
`j` is `C^n` at `y`, and the total derivative of `incidenceEquation F j` at `z` is surjective, with
`finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 ≤ n`, then the parameters not regular on `U` have
additive Haar measure zero. -/
theorem addHaar_setOf_not_isRegularIncidenceParameterOn_eq_zero
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [IsAddHaarMeasure μ]
    {F : E × P → V} {j : W → V} {U : Set ((E × W) × P)} {n : ℕ∞ω}
    (hF : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n F (z.1.1, z.2))
    (hj : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n j z.1.2)
    (htotal : ∀ z ∈ U, incidenceEquation F j z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F j) z))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    μ {p | ¬ IsRegularIncidenceParameterOn F j U p} = 0 := by
  have hn' : ((finrank ℝ (E × W) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n := by
    rwa [Module.finrank_prod]
  exact addHaar_setOf_not_isRegularParameterOn_eq_zero μ
    (fun z hzU hz0 ↦ contDiffAt_incidenceEquation (hF z hzU hz0) (hj z hzU hz0))
    htotal hn'

/-- Almost every parameter for additive Haar measure is a regular incidence parameter on `U`. -/
theorem ae_isRegularIncidenceParameterOn
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [IsAddHaarMeasure μ]
    {F : E × P → V} {j : W → V} {U : Set ((E × W) × P)} {n : ℕ∞ω}
    (hF : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n F (z.1.1, z.2))
    (hj : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n j z.1.2)
    (htotal : ∀ z ∈ U, incidenceEquation F j z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F j) z))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∀ᵐ p ∂μ, IsRegularIncidenceParameterOn F j U p :=
  ae_iff.2 (addHaar_setOf_not_isRegularIncidenceParameterOn_eq_zero μ hF hj htotal hn)

/-- The parameters that are regular on `U` are dense in `P` (needing no measurable space on `P`). -/
theorem dense_setOf_isRegularIncidenceParameterOn
    {F : E × P → V} {j : W → V} {U : Set ((E × W) × P)} {n : ℕ∞ω}
    (hF : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n F (z.1.1, z.2))
    (hj : ∀ z ∈ U, incidenceEquation F j z = 0 → ContDiffAt ℝ n j z.1.2)
    (htotal : ∀ z ∈ U, incidenceEquation F j z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F j) z))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {p | IsRegularIncidenceParameterOn F j U p} := by
  have hn' : ((finrank ℝ (E × W) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n := by
    rwa [Module.finrank_prod]
  exact dense_setOf_isRegularParameterOn
    (fun z hzU hz0 ↦ contDiffAt_incidenceEquation (hF z hzU hz0) (hj z hzU hz0))
    htotal hn'

/-- **Generic incidence parameters for smooth maps.** Under universal transversality for smooth maps
between finite-dimensional real normed spaces, the parameters whose slice is not transverse to `j`
have additive Haar measure zero. -/
theorem addHaar_setOf_not_isRegularIncidenceParameter
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [μ.IsAddHaarMeasure]
    {F : E × P → V} {j : W → V}
    (hF : ContDiff ℝ ∞ F) (hj : ContDiff ℝ ∞ j)
    (htotal : ∀ z, incidenceEquation F j z = 0 →
      Function.Surjective (fderiv ℝ (incidenceEquation F j) z)) :
    μ {p | ¬ IsRegularIncidenceParameter F j p} = 0 := by
  simpa only [isRegularIncidenceParameterOn_univ] using
    addHaar_setOf_not_isRegularIncidenceParameterOn_eq_zero (U := univ) (n := ∞) μ
      (fun z _ _ ↦ hF.contDiffAt) (fun z _ _ ↦ hj.contDiffAt)
      (fun z _ ↦ htotal z) (by simp)

/-- Almost every parameter for additive Haar measure has a slice transverse to `j`. -/
theorem ae_isRegularIncidenceParameter
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [μ.IsAddHaarMeasure]
    {F : E × P → V} {j : W → V}
    (hF : ContDiff ℝ ∞ F) (hj : ContDiff ℝ ∞ j)
    (htotal : ∀ z, incidenceEquation F j z = 0 →
      Function.Surjective (fderiv ℝ (incidenceEquation F j) z)) :
    ∀ᵐ p ∂μ, IsRegularIncidenceParameter F j p :=
  ae_iff.2 (addHaar_setOf_not_isRegularIncidenceParameter μ hF hj htotal)

/-- The regular incidence parameters of a universally transverse smooth family are dense in `P`. -/
theorem dense_setOf_isRegularIncidenceParameter
    {F : E × P → V} {j : W → V}
    (hF : ContDiff ℝ ∞ F) (hj : ContDiff ℝ ∞ j)
    (htotal : ∀ z, incidenceEquation F j z = 0 →
      Function.Surjective (fderiv ℝ (incidenceEquation F j) z)) :
    Dense {p | IsRegularIncidenceParameter F j p} := by
  simpa only [isRegularIncidenceParameterOn_univ] using
    dense_setOf_isRegularIncidenceParameterOn (U := univ) (n := ∞)
      (fun z _ _ ↦ hF.contDiffAt) (fun z _ _ ↦ hj.contDiffAt)
      (fun z _ ↦ htotal z) (by simp)

end FiniteDimensionalGeneric

section CountableFamily

variable {ι E P V : Type*} [Countable ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, FiniteDimensional ℝ (W i)]

/-- **Simultaneous generic transversality to a countable family of maps.** Almost every parameter
`p` is simultaneously regular on `U i` against `j i : W i → V` for all `i : ι`. -/
theorem ae_forall_isRegularIncidenceParameterOn
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [IsAddHaarMeasure μ]
    {F : E × P → V} {j : ∀ i, W i → V} {U : ∀ i, Set ((E × W i) × P)} {n : ι → ℕ∞ω}
    (hF : ∀ i, ∀ z ∈ U i, incidenceEquation F (j i) z = 0 → ContDiffAt ℝ (n i) F (z.1.1, z.2))
    (hj : ∀ i, ∀ z ∈ U i, incidenceEquation F (j i) z = 0 → ContDiffAt ℝ (n i) (j i) z.1.2)
    (htotal : ∀ i, ∀ z ∈ U i, incidenceEquation F (j i) z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F (j i)) z))
    (hn : ∀ i, ((finrank ℝ E + finrank ℝ (W i) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n i) :
    ∀ᵐ p ∂μ, ∀ i, IsRegularIncidenceParameterOn F (j i) (U i) p :=
  ae_all_iff.2 fun i ↦
    ae_isRegularIncidenceParameterOn μ (hF i) (hj i) (htotal i) (hn i)

/-- Parameters simultaneously regular on `U i` against a countable family `j i : W i → V` are
dense in `P`. -/
theorem dense_setOf_forall_isRegularIncidenceParameterOn
    {F : E × P → V} {j : ∀ i, W i → V} {U : ∀ i, Set ((E × W i) × P)} {n : ι → ℕ∞ω}
    (hF : ∀ i, ∀ z ∈ U i, incidenceEquation F (j i) z = 0 → ContDiffAt ℝ (n i) F (z.1.1, z.2))
    (hj : ∀ i, ∀ z ∈ U i, incidenceEquation F (j i) z = 0 → ContDiffAt ℝ (n i) (j i) z.1.2)
    (htotal : ∀ i, ∀ z ∈ U i, incidenceEquation F (j i) z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F (j i)) z))
    (hn : ∀ i, ((finrank ℝ E + finrank ℝ (W i) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n i) :
    Dense {p | ∀ i, IsRegularIncidenceParameterOn F (j i) (U i) p} := by
  borelize P
  exact Measure.dense_of_ae (μ := (addHaar : Measure P))
    (ae_forall_isRegularIncidenceParameterOn addHaar hF hj htotal hn)

/-- **Simultaneous generic avoidance of a countable family of low-dimensional targets.** When
`finrank ℝ E + finrank ℝ (W i) < finrank ℝ V` for every `i`, almost every parameter gives a slice
whose image misses `range (j i)` for all `i`. Notice that `n = 1` already meets the Morse--Sard
threshold `finrank ℝ E + finrank ℝ (W i) - finrank ℝ V + 1 = 1`. -/
theorem ae_forall_disjoint_range_of_finrank_lt
    [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [IsAddHaarMeasure μ]
    {F : E × P → V} {j : ∀ i, W i → V} {n : ℕ∞ω} (hn : 1 ≤ n)
    (hF : ∀ i z, incidenceEquation F (j i) z = 0 → ContDiffAt ℝ n F (z.1.1, z.2))
    (hj : ∀ i z, incidenceEquation F (j i) z = 0 → ContDiffAt ℝ n (j i) z.1.2)
    (htotal : ∀ i z, incidenceEquation F (j i) z = 0 →
      Surjective (fderiv ℝ (incidenceEquation F (j i)) z))
    (hdim : ∀ i, finrank ℝ E + finrank ℝ (W i) < finrank ℝ V) :
    ∀ᵐ p ∂μ, ∀ i, Disjoint (range fun x ↦ F (x, p)) (range (j i)) := by
  have hae := ae_forall_isRegularIncidenceParameterOn (U := fun _ ↦ univ) (n := fun _ ↦ n) μ
    (fun i z _ ↦ hF i z) (fun i z _ ↦ hj i z) (fun i z _ ↦ htotal i z) fun i ↦ by
      have hsub : finrank ℝ E + finrank ℝ (W i) - finrank ℝ V = 0 :=
        Nat.sub_eq_zero_of_le (hdim i).le
      simpa [hsub] using hn
  filter_upwards [hae] with p hp i
  exact disjoint_range_of_isRegularIncidenceParameter (hdim i)
    (isRegularIncidenceParameterOn_univ.1 (hp i))

end CountableFamily

section Examples

/-- For the quadratic family `F(x, p) = x ^ 2 + p` on `ℝ` against the point `0 : Unit → ℝ`, a
parameter `p : ℝ` is regular if and only if `p ≠ 0`: at `p = 0` the unique solution `x = 0` is
degenerate, for `p < 0` the two roots `±√(-p)` have nonzero derivative `2 x`, and for `p > 0` the
fibre is empty. -/
theorem isRegularIncidenceParameter_sq_add_zero_iff (p : ℝ) :
    IsRegularIncidenceParameter (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2) (fun _ : Unit ↦ (0 : ℝ)) p ↔
      p ≠ 0 := by
  have hF : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2) :=
    (contDiff_fst.pow 2).add contDiff_snd
  have hj : ContDiff ℝ ∞ (fun _ : Unit ↦ (0 : ℝ)) := contDiff_const
  rw [isRegularIncidenceParameter_iff_coprod
    (fun _ _ _ ↦ hF.contDiffAt.differentiableAt (by simp))
    (fun _ _ _ ↦ hj.contDiffAt.differentiableAt (by simp))]
  have hslice (x u : ℝ) :
      fderiv ℝ (fun x' : ℝ ↦ (x', p).1 ^ 2 + (x', p).2) x u = 2 * x * u := by
    have hd : HasDerivAt (fun x' : ℝ ↦ x' ^ 2 + p) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const p
    have hfd := hd.hasFDerivAt.fderiv
    have hfun : (fun x' : ℝ ↦ (x', p).1 ^ 2 + (x', p).2) = fun x' : ℝ ↦ x' ^ 2 + p := rfl
    rw [hfun, hfd]
    simp [mul_comm]
  have hj0 (y : Unit) : fderiv ℝ (fun _ : Unit ↦ (0 : ℝ)) y = 0 := by
    simp
  constructor
  · intro h hp0
    subst hp0
    obtain ⟨⟨u, _⟩, huv⟩ := h 0 () (by norm_num) 1
    simp only [ContinuousLinearMap.coprod_apply, hslice 0 u, hj0, neg_zero, zero_apply] at huv
    norm_num at huv
  · intro hp x y hxy w
    have hx0 : x ≠ 0 := by
      intro rfl
      apply hp
      linarith
    refine ⟨(w / (2 * x), ()), ?_⟩
    have h2x : 2 * x ≠ 0 := mul_ne_zero two_ne_zero hx0
    simp only [ContinuousLinearMap.coprod_apply, hslice x (w / (2 * x)), hj0, neg_zero,
      zero_apply, add_zero]
    exact mul_div_cancel₀ w h2x

/-- At `p = 0`, the quadratic family `(x, p) ↦ x ^ 2 + p` fails incidence regularity against `0`. -/
theorem not_isRegularIncidenceParameter_sq_add_zero_zero :
    ¬ IsRegularIncidenceParameter (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2) (fun _ : Unit ↦ (0 : ℝ)) 0 := by
  simp [isRegularIncidenceParameter_sq_add_zero_iff]

/-- At `p = -1`, the quadratic family `(x, p) ↦ x ^ 2 + p` has a nonempty regular fibre `{ -1, 1 }`
against `0`. -/
theorem isRegularIncidenceParameter_sq_add_zero_neg_one :
    IsRegularIncidenceParameter (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2)
      (fun _ : Unit ↦ (0 : ℝ)) (-1) := by
  simp [isRegularIncidenceParameter_sq_add_zero_iff]

/-- At `p = 1`, the quadratic family `(x, p) ↦ x ^ 2 + p` is regular against `0` (with empty
fibre). -/
theorem isRegularIncidenceParameter_sq_add_zero_one :
    IsRegularIncidenceParameter (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2)
      (fun _ : Unit ↦ (0 : ℝ)) 1 := by
  simp [isRegularIncidenceParameter_sq_add_zero_iff]

/-- Against `id : ℝ → ℝ`, every parameter `p : ℝ` of the quadratic family `(x, p) ↦ x ^ 2 + p` is
regular because `fderiv ℝ id y = id` already spans `ℝ`. -/
theorem isRegularIncidenceParameter_sq_add_id (p : ℝ) :
    IsRegularIncidenceParameter (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2) (id : ℝ → ℝ) p := by
  have hF : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2) :=
    (contDiff_fst.pow 2).add contDiff_snd
  rw [isRegularIncidenceParameter_iff_coprod
    (fun _ _ _ ↦ hF.contDiffAt.differentiableAt (by simp))
    (fun _ _ _ ↦ differentiableAt_id)]
  intro x y _ w
  refine ⟨(0, -w), ?_⟩
  simp

end Examples

end TauCeti
