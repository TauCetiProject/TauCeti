/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.GlobalParametric
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Coprod

/-!
# Incidence equations and transverse parameters

For a family `F : E × P → V` and a map `j : W → V`, the incidence equation is
`TauCeti.incidenceEquation F j ((x, y), p) = F (x, p) - j y = 0`. Regularity
(`TauCeti.IsRegularIncidenceParameter` globally, `TauCeti.IsRegularIncidenceParameterOn` on a
subset `U ⊆ (E × W) × P`) restricts the joint Fréchet derivative of the incidence equation at
`((x, y), p)` to the source directions `E × W`, requiring surjectivity at every incidence point.
Because surjectivity of a restricted Fréchet derivative implies differentiability, regularity at an
incidence point automatically implies differentiability of `F` and `j` there and agrees with slice
transversality: the source linearization is `(u, v) ↦ d_x F(x, p) u - dj(y) v`, equivalently the
ranges of `fderiv ℝ (fun x' ↦ F (x', p)) x` and `fderiv ℝ j y` together span `V`.

These equations express transversality to a map, without requiring its image to be closed or
embedded. If the sources `E` and `W` are finite-dimensional and either
`Module.finrank ℝ E + Module.finrank ℝ W < Module.finrank ℝ V` or `V` is infinite-dimensional,
regularity implies disjointness of the two images without any differentiability hypotheses.

## Main declarations

* `TauCeti.incidenceEquation`: `((x, y), p) ↦ F (x, p) - j y`, with continuity, smoothness, and
  derivative rules over arbitrary nontrivially normed fields, plus universal transversality criteria
  `TauCeti.surjective_fderiv_incidenceEquation_iff` and
  `TauCeti.surjective_fderiv_incidenceEquation_iff_range_sup_eq_top`.
* `TauCeti.IsRegularIncidenceParameter` and `TauCeti.IsRegularIncidenceParameterOn`: global and
  subset-localized incidence regularity, with union/monotonicity/open-congruence lemmas and
  slice-transversality criteria in both coproduct and subspace-sum forms.
* `TauCeti.IsRegularIncidenceParameterOn.comp`,
  `TauCeti.isRegularIncidenceParameterOn_comp_equiv_iff`, and
  `TauCeti.isRegularIncidenceParameter_comp_equiv_iff`: nonlinear chart transfer and unconditional
  continuous linear equivalence invariance.
* `TauCeti.IsRegularIncidenceParameter.disjoint_range`,
  `TauCeti.IsRegularIncidenceParameterOn.ne_of_finrank_lt`, and
  `TauCeti.IsRegularIncidenceParameter.disjoint_range_of_not_finiteDimensional`: dimension-counting
  avoidance.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2012, Chapter 6.
-/

public section

open Function Set
open scoped ContDiff

namespace TauCeti

variable {E W V P : Type*}

section Equation

variable [AddGroup V]

/-- The equation whose zeros are the incidences of a parametrized map with `j`.
The source variables precede the parameter. -/
def incidenceEquation (F : E × P → V) (j : W → V) : (E × W) × P → V :=
  fun z ↦ F (z.1.1, z.2) - j z.1.2

/-- The incidence equation as a function of source and parameter coordinates. -/
theorem incidenceEquation_def (F : E × P → V) (j : W → V) :
    incidenceEquation F j = fun z ↦ F (z.1.1, z.2) - j z.1.2 :=
  (rfl)

/-- Evaluate the incidence equation at an arbitrary source and parameter point. -/
@[simp, grind =]
theorem incidenceEquation_apply (F : E × P → V) (j : W → V) (z : (E × W) × P) :
    incidenceEquation F j z = F (z.1.1, z.2) - j z.1.2 :=
  (rfl)

/-- A zero of the incidence equation is an equality of the two maps. -/
@[grind =]
theorem incidenceEquation_eq_zero {F : E × P → V} {j : W → V} {z : (E × W) × P} :
    incidenceEquation F j z = 0 ↔ F (z.1.1, z.2) = j z.1.2 := by
  simp only [incidenceEquation_apply, sub_eq_zero]

end Equation

section Continuity

variable [TopologicalSpace E] [TopologicalSpace W] [TopologicalSpace P]
  [AddGroup V] [TopologicalSpace V] [ContinuousSub V]

/-- The incidence equation is continuous wherever its two maps are continuous. -/
@[fun_prop]
theorem _root_.ContinuousAt.incidenceEquation {F : E × P → V} {j : W → V}
    {x : E} {y : W} {p : P} (hF : ContinuousAt F (x, p)) (hj : ContinuousAt j y) :
    ContinuousAt (incidenceEquation F j) ((x, y), p) := by
  exact (hF.comp (f := fun z : (E × W) × P ↦ (z.1.1, z.2))
    (x := ((x, y), p)) (continuousAt_fst.fst.prodMk continuousAt_snd)).sub
    (hj.comp (f := fun z : (E × W) × P ↦ z.1.2)
      (x := ((x, y), p)) continuousAt_fst.snd)

/-- The incidence equation is continuous when its two maps are continuous. -/
@[fun_prop]
theorem _root_.Continuous.incidenceEquation {F : E × P → V} {j : W → V}
    (hF : Continuous F) (hj : Continuous j) : Continuous (incidenceEquation F j) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨⟨x, y⟩, p⟩
  exact (hF.continuousAt (x := (x, p))).incidenceEquation hj.continuousAt

variable [IsTopologicalAddGroup V]

omit [ContinuousSub V] in
/-- The incidence equation is continuous at a point exactly when the family and the map
are continuous at the corresponding points. -/
@[simp]
theorem continuousAt_incidenceEquation_iff {F : E × P → V} {j : W → V}
    {z : (E × W) × P} :
    ContinuousAt (incidenceEquation F j) z ↔
      ContinuousAt F (z.1.1, z.2) ∧ ContinuousAt j z.1.2 := by
  obtain ⟨⟨x, y⟩, p⟩ := z
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.incidenceEquation h.2⟩
  · have hF : F = fun q ↦ incidenceEquation F j ((q.1, y), q.2) + j y := by
      funext q
      simp
    rw [hF]
    exact (h.comp (f := fun q : E × P ↦ ((q.1, y), q.2)) (x := (x, p)) (by fun_prop)).add_const _
  · have hj : j = fun w ↦ -incidenceEquation F j ((x, w), p) + F (x, p) := by
      funext w
      simp
    rw [hj]
    exact (h.comp (f := fun w : W ↦ ((x, w), p)) (x := y) (by fun_prop)).neg.add_const _

omit [ContinuousSub V] in
/-- On nonempty source and parameter spaces, the incidence equation is continuous exactly
when its two maps are continuous. -/
@[simp]
theorem continuous_incidenceEquation_iff [Nonempty E] [Nonempty W] [Nonempty P]
    {F : E × P → V} {j : W → V} :
    Continuous (incidenceEquation F j) ↔ Continuous F ∧ Continuous j := by
  inhabit E
  inhabit W
  inhabit P
  simp only [continuous_iff_continuousAt]
  exact ⟨fun h ↦ ⟨fun z ↦ (continuousAt_incidenceEquation_iff.1
    (h ((z.1, default), z.2))).1,
    fun y ↦ (continuousAt_incidenceEquation_iff.1 (h ((default, y), default))).2⟩,
    fun h z ↦ (h.1 _).incidenceEquation (h.2 _)⟩

end Continuity

section Derivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]

/-- The incidence equation has the pointwise differentiability order of its two maps. -/
@[fun_prop]
theorem _root_.ContDiffAt.incidenceEquation {n : ℕ∞ω} {F : E × P → V} {j : W → V}
    {x : E} {y : W} {p : P}
    (hF : ContDiffAt 𝕜 n F (x, p)) (hj : ContDiffAt 𝕜 n j y) :
    ContDiffAt 𝕜 n (incidenceEquation F j) ((x, y), p) := by
  exact (hF.comp ((x, y), p) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub
    (hj.comp ((x, y), p) contDiffAt_fst.snd)

/-- The incidence equation has the differentiability order of the family and the map. -/
@[fun_prop]
theorem _root_.ContDiff.incidenceEquation {n : ℕ∞ω} {F : E × P → V} {j : W → V}
    (hF : ContDiff 𝕜 n F) (hj : ContDiff 𝕜 n j) :
    ContDiff 𝕜 n (incidenceEquation F j) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨⟨x, y⟩, p⟩
  exact (hF.contDiffAt (x := (x, p))).incidenceEquation hj.contDiffAt

/-- Derivatives of the two maps give the full derivative of the incidence equation. -/
@[fun_prop]
theorem _root_.HasFDerivAt.incidenceEquation
    {F : E × P → V} {j : W → V} {F' : E × P →L[𝕜] V} {j' : W →L[𝕜] V}
    {x : E} {y : W} {p : P} (hF : HasFDerivAt F F' (x, p)) (hj : HasFDerivAt j j' y) :
    HasFDerivAt (incidenceEquation F j)
      (((F'.comp (.inl 𝕜 E P)).coprod (-j')).coprod (F'.comp (.inr 𝕜 E P)))
      ((x, y), p) := by
  rw [incidenceEquation_def]
  have hfst : HasFDerivAt (Prod.fst : (E × W) × P → E × W)
      (ContinuousLinearMap.fst 𝕜 (E × W) P) ((x, y), p) := hasFDerivAt_fst
  refine ((hF.comp ((x, y), p) (hfst.fst.prodMk hasFDerivAt_snd)).sub
    (hj.comp ((x, y), p) hfst.snd)).congr_fderiv ?_
  ext <;> simp [← Prod.zero_eq_mk]

/-- Strict derivatives of the maps give the strict derivative of the incidence equation. -/
@[fun_prop]
theorem _root_.HasStrictFDerivAt.incidenceEquation
    {F : E × P → V} {j : W → V} {F' : E × P →L[𝕜] V} {j' : W →L[𝕜] V}
    {x : E} {y : W} {p : P}
    (hF : HasStrictFDerivAt F F' (x, p)) (hj : HasStrictFDerivAt j j' y) :
    HasStrictFDerivAt (incidenceEquation F j)
      (((F'.comp (.inl 𝕜 E P)).coprod (-j')).coprod (F'.comp (.inr 𝕜 E P)))
      ((x, y), p) := by
  rw [incidenceEquation_def]
  have hfst : HasStrictFDerivAt (Prod.fst : (E × W) × P → E × W)
      (ContinuousLinearMap.fst 𝕜 (E × W) P) ((x, y), p) := hasStrictFDerivAt_fst
  refine ((hF.comp ((x, y), p) (hfst.fst.prodMk hasStrictFDerivAt_snd)).sub
    (hj.comp ((x, y), p) hfst.snd)).congr_fderiv ?_
  ext <;> simp [← Prod.zero_eq_mk]

/-- The incidence equation is differentiable wherever its two maps are differentiable. -/
@[fun_prop]
theorem _root_.DifferentiableAt.incidenceEquation
    {F : E × P → V} {j : W → V} {x : E} {y : W} {p : P}
    (hF : DifferentiableAt 𝕜 F (x, p)) (hj : DifferentiableAt 𝕜 j y) :
    DifferentiableAt 𝕜 (incidenceEquation F j) ((x, y), p) :=
  (hF.hasFDerivAt.incidenceEquation hj.hasFDerivAt).differentiableAt

/-- The incidence equation is differentiable when its two maps are differentiable. -/
@[fun_prop]
theorem _root_.Differentiable.incidenceEquation {F : E × P → V} {j : W → V}
    (hF : Differentiable 𝕜 F) (hj : Differentiable 𝕜 j) :
    Differentiable 𝕜 (incidenceEquation F j) :=
  fun _ ↦ (hF _).incidenceEquation (hj _)

/-- The incidence equation is differentiable at a point exactly when the family and the map
are differentiable at the corresponding points. -/
@[simp]
theorem differentiableAt_incidenceEquation_iff {F : E × P → V} {j : W → V}
    {z : (E × W) × P} :
    DifferentiableAt 𝕜 (incidenceEquation F j) z ↔
      DifferentiableAt 𝕜 F (z.1.1, z.2) ∧ DifferentiableAt 𝕜 j z.1.2 := by
  obtain ⟨⟨x, y⟩, p⟩ := z
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.incidenceEquation h.2⟩
  · have hF : F = fun q ↦ incidenceEquation F j ((q.1, y), q.2) + j y := by
      funext q
      simp
    rw [hF]
    exact (h.comp (f := fun q : E × P ↦ ((q.1, y), q.2)) (x, p) (by fun_prop)).add_const _
  · have hj : j = fun w ↦ F (x, p) - incidenceEquation F j ((x, w), p) := by
      funext w
      simp
    rw [hj]
    exact (h.comp (f := fun w : W ↦ ((x, w), p)) y (by fun_prop)).const_sub _

/-- The incidence equation is differentiable exactly when its two maps are differentiable. -/
@[simp]
theorem differentiable_incidenceEquation_iff {F : E × P → V} {j : W → V} :
    Differentiable 𝕜 (incidenceEquation F j) ↔ Differentiable 𝕜 F ∧ Differentiable 𝕜 j :=
  ⟨fun h ↦ ⟨fun z ↦ (differentiableAt_incidenceEquation_iff.1 (h ((z.1, 0), z.2))).1,
    fun y ↦ (differentiableAt_incidenceEquation_iff.1 (h ((0, y), 0))).2⟩,
    fun h ↦ h.1.incidenceEquation h.2⟩

/-- The incidence equation has differentiability order `n` at a point exactly when the family
and the map have that order at the corresponding points. -/
@[simp]
theorem contDiffAt_incidenceEquation_iff {n : ℕ∞ω} {F : E × P → V} {j : W → V}
    {z : (E × W) × P} :
    ContDiffAt 𝕜 n (incidenceEquation F j) z ↔
      ContDiffAt 𝕜 n F (z.1.1, z.2) ∧ ContDiffAt 𝕜 n j z.1.2 := by
  obtain ⟨⟨x, y⟩, p⟩ := z
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.incidenceEquation h.2⟩
  · have hF : F = fun q ↦ incidenceEquation F j ((q.1, y), q.2) + j y := by
      funext q
      simp
    rw [hF]
    exact (h.comp (f := fun q : E × P ↦ ((q.1, y), q.2)) (x, p) (by fun_prop)).add
      contDiffAt_const
  · have hj : j = fun w ↦ F (x, p) - incidenceEquation F j ((x, w), p) := by
      funext w
      simp
    rw [hj]
    exact contDiffAt_const.sub (h.comp (f := fun w : W ↦ ((x, w), p)) y (by fun_prop))

/-- The incidence equation has differentiability order `n` exactly when its two maps do. -/
@[simp]
theorem contDiff_incidenceEquation_iff {n : ℕ∞ω} {F : E × P → V} {j : W → V} :
    ContDiff 𝕜 n (incidenceEquation F j) ↔ ContDiff 𝕜 n F ∧ ContDiff 𝕜 n j := by
  simp only [contDiff_iff_contDiffAt]
  exact ⟨fun h ↦ ⟨fun z ↦ (contDiffAt_incidenceEquation_iff.1 (h ((z.1, 0), z.2))).1,
    fun y ↦ (contDiffAt_incidenceEquation_iff.1 (h ((0, y), 0))).2⟩,
    fun h ↦ fun z ↦ (h.1 _).incidenceEquation (h.2 _)⟩

/-- The full derivative of the incidence equation, including the parameter direction. -/
theorem fderiv_incidenceEquation_apply
    {F : E × P → V} {j : W → V} {x : E} {y : W} {p : P}
    (hF : DifferentiableAt 𝕜 F (x, p)) (hj : DifferentiableAt 𝕜 j y)
    (u : E) (v : W) (q : P) :
    fderiv 𝕜 (incidenceEquation F j) ((x, y), p) ((u, v), q) =
      fderiv 𝕜 F (x, p) (u, q) - fderiv 𝕜 j y v := by
  rw [(hF.hasFDerivAt.incidenceEquation hj.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, neg_apply, ContinuousLinearMap.inr_apply, sub_eq_add_neg]
  rw [add_right_comm, ← map_add]
  simp

/-- The source derivative is `(u, v) ↦ D_x F (x, p) u - D j y v`. -/
theorem fderiv_incidenceEquation_comp_inl
    {F : E × P → V} {j : W → V} {x : E} {y : W} {p : P}
    (hF : DifferentiableAt 𝕜 F (x, p)) (hj : DifferentiableAt 𝕜 j y) :
    (fderiv 𝕜 (incidenceEquation F j) ((x, y), p)).comp
        (ContinuousLinearMap.inl 𝕜 (E × W) P) =
      ((fderiv 𝕜 F (x, p)).comp (ContinuousLinearMap.inl 𝕜 E P)).coprod
        (-fderiv 𝕜 j y) := by
  apply ContinuousLinearMap.ext
  rintro ⟨u, v⟩
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    fderiv_incidenceEquation_apply hF hj, ContinuousLinearMap.coprod_apply,
    neg_apply, sub_eq_add_neg]

/-- The parameter derivative of the incidence equation is that of the family. -/
theorem fderiv_incidenceEquation_comp_inr
    {F : E × P → V} {j : W → V} {x : E} {y : W} {p : P}
    (hj : DifferentiableAt 𝕜 j y) :
    (fderiv 𝕜 (incidenceEquation F j) ((x, y), p)).comp
        (ContinuousLinearMap.inr 𝕜 (E × W) P) =
      (fderiv 𝕜 F (x, p)).comp (ContinuousLinearMap.inr 𝕜 E P) := by
  by_cases hF : DifferentiableAt 𝕜 F (x, p)
  · ext q
    simp [fderiv_incidenceEquation_apply hF hj]
  · have h : ¬ DifferentiableAt 𝕜 (incidenceEquation F j) ((x, y), p) :=
      fun h ↦ hF (differentiableAt_incidenceEquation_iff.1 h).1
    simp [fderiv_zero_of_not_differentiableAt hF, fderiv_zero_of_not_differentiableAt h]

omit [NormedAddCommGroup P] [NormedSpace 𝕜 P] in
/-- Fréchet derivative of the fixed-parameter map `xy ↦ incidenceEquation F j (xy, p)` at `(x, y)`:
given derivatives `DFx` of the slice `x' ↦ F (x', p)` at `x` and `Dj` of `j` at `y`, it equals
`DFx.coprod (-Dj)`. Neither a norm on `P` nor joint differentiability of `F` is needed. -/
theorem hasFDerivAt_incidenceEquation_slice {F : E × P → V} {j : W → V}
    {DFx : E →L[𝕜] V} {Dj : W →L[𝕜] V} {x : E} {y : W} {p : P}
    (hFx : HasFDerivAt (fun x' ↦ F (x', p)) DFx x) (hj : HasFDerivAt j Dj y) :
    HasFDerivAt (fun xy : E × W ↦ incidenceEquation F j (xy, p))
      (DFx.coprod (-Dj)) (x, y) := by
  have h1 : HasFDerivAt ((fun x' ↦ F (x', p)) ∘ Prod.fst)
      (DFx.comp (ContinuousLinearMap.fst 𝕜 E W)) (x, y) :=
    HasFDerivAt.comp (x, y) hFx hasFDerivAt_fst
  have h2 : HasFDerivAt (j ∘ Prod.snd)
      (Dj.comp (ContinuousLinearMap.snd 𝕜 E W)) (x, y) :=
    HasFDerivAt.comp (x, y) hj hasFDerivAt_snd
  refine (h1.sub h2).congr_fderiv (ContinuousLinearMap.ext fun ⟨u, v⟩ ↦ ?_)
  simp [sub_eq_add_neg]

omit [NormedAddCommGroup P] [NormedSpace 𝕜 P] in
/-- Fréchet derivative of the fixed-parameter map `xy ↦ incidenceEquation F j (xy, p)` at `(x, y)`
when the slice `x' ↦ F (x', p)` is differentiable at `x` and `j` is differentiable at `y`. -/
theorem fderiv_incidenceEquation_slice {F : E × P → V} {j : W → V}
    {x : E} {y : W} {p : P}
    (hFx : DifferentiableAt 𝕜 (fun x' ↦ F (x', p)) x) (hj : DifferentiableAt 𝕜 j y) :
    fderiv 𝕜 (fun xy : E × W ↦ incidenceEquation F j (xy, p)) (x, y) =
      (fderiv 𝕜 (fun x' ↦ F (x', p)) x).coprod (-fderiv 𝕜 j y) :=
  (hasFDerivAt_incidenceEquation_slice hFx.hasFDerivAt hj.hasFDerivAt).fderiv

/-- **Universal transversality criterion (coproduct form).** When `F` is differentiable at `(x, p)`
and `j` is differentiable at `y`, the total derivative of `TauCeti.incidenceEquation F j` at
`((x, y), p)` is surjective if and only if `(fderiv 𝕜 F (x, p)).coprod (-fderiv 𝕜 j y)` is
surjective. -/
theorem surjective_fderiv_incidenceEquation_iff {F : E × P → V} {j : W → V}
    {x : E} {y : W} {p : P}
    (hF : DifferentiableAt 𝕜 F (x, p)) (hj : DifferentiableAt 𝕜 j y) :
    Surjective (fderiv 𝕜 (incidenceEquation F j) ((x, y), p)) ↔
      Surjective ((fderiv 𝕜 F (x, p)).coprod (-fderiv 𝕜 j y)) := by
  constructor
  · intro hsurj w
    obtain ⟨⟨⟨u, v⟩, q⟩, hw⟩ := hsurj w
    refine ⟨((u, q), v), ?_⟩
    simpa [fderiv_incidenceEquation_apply hF hj, sub_eq_add_neg] using hw
  · intro hsurj w
    obtain ⟨⟨⟨u, q⟩, v⟩, hw⟩ := hsurj w
    refine ⟨((u, v), q), ?_⟩
    simpa [fderiv_incidenceEquation_apply hF hj, sub_eq_add_neg] using hw

/-- **Universal transversality criterion (subspace-sum form).** When `F` is differentiable at
`(x, p)` and `j` is differentiable at `y`, the total derivative of `TauCeti.incidenceEquation F j`
at `((x, y), p)` is surjective if and only if the ranges of `fderiv 𝕜 F (x, p)` and `fderiv 𝕜 j y`
together span `V`. -/
theorem surjective_fderiv_incidenceEquation_iff_range_sup_eq_top {F : E × P → V} {j : W → V}
    {x : E} {y : W} {p : P}
    (hF : DifferentiableAt 𝕜 F (x, p)) (hj : DifferentiableAt 𝕜 j y) :
    Surjective (fderiv 𝕜 (incidenceEquation F j) ((x, y), p)) ↔
      (fderiv 𝕜 F (x, p)).range ⊔ (fderiv 𝕜 j y).range = ⊤ :=
  (surjective_fderiv_incidenceEquation_iff hF hj).trans
    (ContinuousLinearMap.surjective_coprod_neg_iff _ _)

/-- Universal transversality at `((x, y), p)` holds automatically whenever `j` is differentiable at
`y` and the parameter derivative `q ↦ fderiv 𝕜 F (x, p) (0, q)` is surjective. -/
theorem surjective_fderiv_incidenceEquation_of_surjective_comp_inr {F : E × P → V}
    {j : W → V} {x : E} {y : W} {p : P}
    (hj : DifferentiableAt 𝕜 j y)
    (hP : Surjective ((fderiv 𝕜 F (x, p)).comp (ContinuousLinearMap.inr 𝕜 E P))) :
    Surjective (fderiv 𝕜 (incidenceEquation F j) ((x, y), p)) := by
  rw [← fderiv_incidenceEquation_comp_inr hj, ContinuousLinearMap.coe_comp] at hP
  exact hP.of_comp

end Derivative

section Regular

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Incidence regularity requires the joint Fréchet derivative of the incidence equation,
restricted to the source directions `E × W`, to be surjective at every incidence point.
It agrees with slice transversality when `F` and `j` are differentiable there. -/
def IsRegularIncidenceParameter (F : E × P → V) (j : W → V) (p : P) : Prop :=
  IsRegularParameter (incidenceEquation F j) 0 p

/-- Regular incidence parameters are precisely the regular parameters of the zero equation. -/
theorem isRegularIncidenceParameter_iff {F : E × P → V} {j : W → V} {p : P} :
    IsRegularIncidenceParameter F j p ↔ IsRegularParameter (incidenceEquation F j) 0 p :=
  (Iff.rfl)

/-- Subset-localized variant of `TauCeti.IsRegularIncidenceParameter`: regularity of `p` is
required only at incidence points `((x, y), p) ∈ U`. -/
def IsRegularIncidenceParameterOn (F : E × P → V) (j : W → V)
    (U : Set ((E × W) × P)) (p : P) : Prop :=
  IsRegularParameterOn (incidenceEquation F j) U 0 p

/-- Regular incidence parameters on `U` are precisely the regular parameters on `U` of the zero
equation. -/
theorem isRegularIncidenceParameterOn_iff {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p : P} :
    IsRegularIncidenceParameterOn F j U p ↔ IsRegularParameterOn (incidenceEquation F j) U 0 p :=
  (Iff.rfl)

/-- Incidence regularity on `univ` coincides with global incidence regularity. -/
@[simp]
theorem isRegularIncidenceParameterOn_univ {F : E × P → V} {j : W → V} {p : P} :
    IsRegularIncidenceParameterOn F j univ p ↔ IsRegularIncidenceParameter F j p :=
  isRegularParameterOn_univ

/-- Every parameter is vacuously regular on the empty set. -/
@[simp]
theorem isRegularIncidenceParameterOn_empty (F : E × P → V) (j : W → V) (p : P) :
    IsRegularIncidenceParameterOn F j ∅ p :=
  isRegularParameterOn_empty (incidenceEquation F j) 0 p

/-- Incidence regularity on a binary union holds if and only if it holds on each piece. -/
@[simp]
theorem isRegularIncidenceParameterOn_union {F : E × P → V} {j : W → V}
    {U U' : Set ((E × W) × P)} {p : P} :
    IsRegularIncidenceParameterOn F j (U ∪ U') p ↔
      IsRegularIncidenceParameterOn F j U p ∧ IsRegularIncidenceParameterOn F j U' p :=
  isRegularParameterOn_union

/-- Incidence regularity on an indexed union holds if and only if it holds on each member. -/
@[simp]
theorem isRegularIncidenceParameterOn_iUnion {ι : Sort*} {F : E × P → V} {j : W → V}
    {U : ι → Set ((E × W) × P)} {p : P} :
    IsRegularIncidenceParameterOn F j (⋃ i, U i) p ↔
      ∀ i, IsRegularIncidenceParameterOn F j (U i) p :=
  isRegularParameterOn_iUnion

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

/-- On an open subset `U ⊆ (E × W) × P`, `TauCeti.IsRegularIncidenceParameterOn` depends only on
the values of `incidenceEquation F j` on `U`. -/
theorem _root_.IsOpen.isRegularIncidenceParameterOn_congr {F F' : E × P → V} {j j' : W → V}
    {U : Set ((E × W) × P)} (hU : IsOpen U) {p : P}
    (hEq : EqOn (incidenceEquation F j) (incidenceEquation F' j') U) :
    IsRegularIncidenceParameterOn F j U p ↔ IsRegularIncidenceParameterOn F' j' U p :=
  hU.isRegularParameterOn_congr hEq

/-- At an incidence point in `U` of a slice regular on `U`, the family and the map are
differentiable. -/
theorem IsRegularIncidenceParameterOn.differentiableAt
    {F : E × P → V} {j : W → V} {U : Set ((E × W) × P)} {p : P} {x : E} {y : W}
    (h : IsRegularIncidenceParameterOn F j U p) (hU : ((x, y), p) ∈ U) (hxy : F (x, p) = j y) :
    DifferentiableAt ℝ F (x, p) ∧ DifferentiableAt ℝ j y :=
  differentiableAt_incidenceEquation_iff.1
    ((isRegularIncidenceParameterOn_iff.1 h).differentiableAt
      (x := (x, y)) hU (incidenceEquation_eq_zero.2 hxy))

/-- At an incidence point of a regular slice, the family and the map are differentiable. -/
theorem IsRegularIncidenceParameter.differentiableAt
    {F : E × P → V} {j : W → V} {p : P} {x : E} {y : W}
    (h : IsRegularIncidenceParameter F j p) (hxy : F (x, p) = j y) :
    DifferentiableAt ℝ F (x, p) ∧ DifferentiableAt ℝ j y :=
  h.isRegularIncidenceParameterOn.differentiableAt (mem_univ _) hxy

/-- At an incidence point in `U`, regularity on `U` gives surjectivity of the source
linearization. -/
theorem IsRegularIncidenceParameterOn.surjective
    {F : E × P → V} {j : W → V} {U : Set ((E × W) × P)} {p : P} {x : E} {y : W}
    (h : IsRegularIncidenceParameterOn F j U p) (hU : ((x, y), p) ∈ U) (hxy : F (x, p) = j y) :
    Surjective (((fderiv ℝ F (x, p)).comp (.inl ℝ E P)).coprod (-fderiv ℝ j y)) := by
  obtain ⟨hF, hj⟩ := h.differentiableAt hU hxy
  rw [← fderiv_incidenceEquation_comp_inl hF hj]
  exact (isRegularParameterOn_iff.1 (isRegularIncidenceParameterOn_iff.1 h)) (x, y) hU
    (incidenceEquation_eq_zero.2 hxy)

/-- At an incidence point, regularity gives surjectivity of the source linearization. -/
theorem IsRegularIncidenceParameter.surjective
    {F : E × P → V} {j : W → V} {p : P} {x : E} {y : W}
    (h : IsRegularIncidenceParameter F j p) (hxy : F (x, p) = j y) :
    Surjective (((fderiv ℝ F (x, p)).comp (.inl ℝ E P)).coprod (-fderiv ℝ j y)) :=
  h.isRegularIncidenceParameterOn.surjective (mem_univ _) hxy

/-- For maps differentiable at incidence points in `U`, regular incidence on `U` is surjectivity of
the difference of their source derivatives there. -/
theorem isRegularIncidenceParameterOn_iff_surjective
    {F : E × P → V} {j : W → V} {U : Set ((E × W) × P)} {p : P}
    (hF : ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y → DifferentiableAt ℝ j y) :
    IsRegularIncidenceParameterOn F j U p ↔ ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y →
      Surjective (((fderiv ℝ F (x, p)).comp (ContinuousLinearMap.inl ℝ E P)).coprod
        (-fderiv ℝ j y)) := by
  rw [isRegularIncidenceParameterOn_iff, isRegularParameterOn_iff]
  simp only [Prod.forall, incidenceEquation_eq_zero]
  congr! 4 with x y hU hxy
  rw [fderiv_incidenceEquation_comp_inl (hF x y hU hxy) (hj x y hU hxy)]

/-- For differentiable maps, regular incidence is the usual surjectivity criterion
for the difference of their source derivatives. Differentiability is needed only at
incidence points. -/
theorem isRegularIncidenceParameter_iff_surjective
    {F : E × P → V} {j : W → V} {p : P}
    (hF : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ j y) :
    IsRegularIncidenceParameter F j p ↔ ∀ x y, F (x, p) = j y →
      Surjective (((fderiv ℝ F (x, p)).comp (ContinuousLinearMap.inl ℝ E P)).coprod
        (-fderiv ℝ j y)) := by
  rw [← isRegularIncidenceParameterOn_univ,
    isRegularIncidenceParameterOn_iff_surjective (fun x y _ ↦ hF x y) (fun x y _ ↦ hj x y)]
  simp

/-- At an incidence point `((x, y), p) ∈ U` of a slice regular on `U`, the slice-derivative
coproduct `(fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)` is surjective (requiring no
differentiability hypotheses on `F` or `j`). -/
theorem IsRegularIncidenceParameterOn.surjective_coprod {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p : P} (hp : IsRegularIncidenceParameterOn F j U p)
    {x : E} {y : W} (hU : ((x, y), p) ∈ U) (hEq : F (x, p) = j y) :
    Surjective ((fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)) := by
  obtain ⟨hF, _⟩ := hp.differentiableAt hU hEq
  have hFx : HasFDerivAt (fun x' ↦ F (x', p))
      ((fderiv ℝ F (x, p)).comp (ContinuousLinearMap.inl ℝ E P)) x :=
    hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x p)
  rw [hFx.fderiv]
  exact hp.surjective hU hEq

/-- At an incidence point `((x, y), p) ∈ U` of a slice regular on `U`, the ranges of the slice
derivative `fderiv ℝ (fun x' ↦ F (x', p)) x` and `fderiv ℝ j y` together span `V`. -/
theorem IsRegularIncidenceParameterOn.range_sup_eq_top {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p : P} (hp : IsRegularIncidenceParameterOn F j U p)
    {x : E} {y : W} (hU : ((x, y), p) ∈ U) (hEq : F (x, p) = j y) :
    (fderiv ℝ (fun x' ↦ F (x', p)) x).range ⊔ (fderiv ℝ j y).range = ⊤ :=
  (ContinuousLinearMap.surjective_coprod_neg_iff _ _).1 (hp.surjective_coprod hU hEq)

/-- At an incidence pair `(x, y)` of a regular slice, the slice-derivative coproduct
`(fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)` is surjective. -/
theorem IsRegularIncidenceParameter.surjective_coprod {F : E × P → V} {j : W → V}
    {p : P} (hp : IsRegularIncidenceParameter F j p)
    {x : E} {y : W} (hEq : F (x, p) = j y) :
    Surjective ((fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)) :=
  hp.isRegularIncidenceParameterOn.surjective_coprod (mem_univ _) hEq

/-- At an incidence pair `(x, y)` of a regular slice, the ranges of
`fderiv ℝ (fun x' ↦ F (x', p)) x` and `fderiv ℝ j y` together span `V`. -/
theorem IsRegularIncidenceParameter.range_sup_eq_top {F : E × P → V} {j : W → V}
    {p : P} (hp : IsRegularIncidenceParameter F j p)
    {x : E} {y : W} (hEq : F (x, p) = j y) :
    (fderiv ℝ (fun x' ↦ F (x', p)) x).range ⊔ (fderiv ℝ j y).range = ⊤ :=
  hp.isRegularIncidenceParameterOn.range_sup_eq_top (mem_univ _) hEq

/-- **Slice-transversality criterion on `U` (coproduct form).** Assuming differentiability of `F`
and `j` only at incidence points in `U`, `p` is regular on `U` if and only if
`(fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)` is surjective at every incidence point
`((x, y), p) ∈ U`. -/
theorem isRegularIncidenceParameterOn_iff_surjective_coprod {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p : P}
    (hF : ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y → DifferentiableAt ℝ j y) :
    IsRegularIncidenceParameterOn F j U p ↔
      ∀ x y, ((x, y), p) ∈ U → F (x, p) = j y →
        Surjective ((fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)) := by
  rw [isRegularIncidenceParameterOn_iff_surjective hF hj]
  congr! 4 with x y hU hEq
  have hFx : HasFDerivAt (fun x' ↦ F (x', p))
      ((fderiv ℝ F (x, p)).comp (ContinuousLinearMap.inl ℝ E P)) x :=
    (hF x y hU hEq).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x p)
  rw [hFx.fderiv]

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
  rw [isRegularIncidenceParameterOn_iff_surjective_coprod hF hj]
  congr! 4 with x y _ _
  exact ContinuousLinearMap.surjective_coprod_neg_iff _ _

/-- **Global slice-transversality criterion (coproduct form).** Assuming differentiability of `F`
and `j` at incidence points, `p` is a regular incidence parameter if and only if
`(fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)` is surjective whenever
`F (x, p) = j y`. -/
theorem isRegularIncidenceParameter_iff_surjective_coprod {F : E × P → V} {j : W → V} {p : P}
    (hF : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ j y) :
    IsRegularIncidenceParameter F j p ↔
      ∀ x y, F (x, p) = j y →
        Surjective ((fderiv ℝ (fun x' ↦ F (x', p)) x).coprod (-fderiv ℝ j y)) := by
  rw [← isRegularIncidenceParameterOn_univ,
    isRegularIncidenceParameterOn_iff_surjective_coprod (fun x y _ ↦ hF x y) (fun x y _ ↦ hj x y)]
  simp

/-- **Global slice-transversality criterion (subspace-sum form).** Assuming differentiability of
`F` and `j` at incidence points, `p` is a regular incidence parameter if and only if the ranges of
`fderiv ℝ (fun x' ↦ F (x', p)) x` and `fderiv ℝ j y` together span `V` whenever
`F (x, p) = j y`. -/
theorem isRegularIncidenceParameter_iff_range_sup_eq_top {F : E × P → V} {j : W → V} {p : P}
    (hF : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ j y) :
    IsRegularIncidenceParameter F j p ↔
      ∀ x y, F (x, p) = j y →
        (fderiv ℝ (fun x' ↦ F (x', p)) x).range ⊔ (fderiv ℝ j y).range = ⊤ := by
  rw [← isRegularIncidenceParameterOn_univ,
    isRegularIncidenceParameterOn_iff_range_sup_eq_top (fun x y _ ↦ hF x y) (fun x y _ ↦ hj x y)]
  simp

/-- Any parameter whose slice misses `range j` inside `U` is vacuously regular on `U`. -/
theorem isRegularIncidenceParameterOn_of_forall_ne {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p : P}
    (hne : ∀ x y, ((x, y), p) ∈ U → F (x, p) ≠ j y) :
    IsRegularIncidenceParameterOn F j U p := by
  rw [isRegularIncidenceParameterOn_iff, isRegularParameterOn_iff]
  rintro ⟨x, y⟩ hU hEq
  exact (hne x y hU (incidenceEquation_eq_zero.1 hEq)).elim

/-- A slice which misses the image of `j` is a regular incidence slice. -/
theorem isRegularIncidenceParameter_of_disjoint_range
    {F : E × P → V} {j : W → V} {p : P}
    (h : Disjoint (range fun x ↦ F (x, p)) (range j)) :
    IsRegularIncidenceParameter F j p :=
  isRegularIncidenceParameterOn_univ.1 <|
    isRegularIncidenceParameterOn_of_forall_ne fun x y _ hxy ↦
      Set.disjoint_left.1 h ⟨x, rfl⟩ ⟨y, hxy.symm⟩

/-- **Dimension-counting avoidance on a set `U`.** When `E` and `W` are finite-dimensional and
`Module.finrank ℝ E + Module.finrank ℝ W < Module.finrank ℝ V`, a parameter `p` that is regular on
`U` admits no incidence points in `U`. No differentiability of `F` or `j` is required. -/
theorem IsRegularIncidenceParameterOn.ne_of_finrank_lt [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ W] {F : E × P → V} {j : W → V} {U : Set ((E × W) × P)} {p : P}
    (h : IsRegularIncidenceParameterOn F j U p)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ W < Module.finrank ℝ V)
    {x : E} {y : W} (hU : ((x, y), p) ∈ U) :
    F (x, p) ≠ j y := by
  intro hxy
  have hs := (isRegularParameterOn_iff.1 (isRegularIncidenceParameterOn_iff.1 h)) (x, y) hU
    (incidenceEquation_eq_zero.2 hxy)
  have hd := LinearMap.finrank_le_finrank_of_surjective hs
  rw [Module.finrank_prod] at hd
  exact (not_le_of_gt hdim) hd

/-- When the sources `E` and `W` are finite-dimensional and the sum of their
`Module.finrank`s is below the target `Module.finrank`, a regular slice has no incidence
points. This inequality applies only to finite-dimensional targets. No differentiability
hypotheses are needed for this implication. -/
theorem IsRegularIncidenceParameter.disjoint_range [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ W] {F : E × P → V} {j : W → V} {p : P}
    (h : IsRegularIncidenceParameter F j p)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ W < Module.finrank ℝ V) :
    Disjoint (range fun x ↦ F (x, p)) (range j) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  exact h.isRegularIncidenceParameterOn.ne_of_finrank_lt hdim (mem_univ _) hy.symm

/-- When the sources `E` and `W` are finite-dimensional and the sum of their
`Module.finrank`s is below the target `Module.finrank`, regular incidence is equivalent to
avoidance. The inequality requires a finite-dimensional target. -/
theorem isRegularIncidenceParameter_iff_disjoint_range [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ W] {F : E × P → V} {j : W → V} {p : P}
    (hdim : Module.finrank ℝ E + Module.finrank ℝ W < Module.finrank ℝ V) :
    IsRegularIncidenceParameter F j p ↔ Disjoint (range fun x ↦ F (x, p)) (range j) :=
  ⟨fun h ↦ h.disjoint_range hdim, isRegularIncidenceParameter_of_disjoint_range⟩

/-- When `E` and `W` are finite-dimensional and `V` is infinite-dimensional, a regular slice
likewise misses `range j`, with no differentiability hypotheses on `F` or `j`. -/
theorem IsRegularIncidenceParameter.disjoint_range_of_not_finiteDimensional
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
    {F : E × P → V} {j : W → V} {p : P}
    (h : IsRegularIncidenceParameter F j p) (hV : ¬ FiniteDimensional ℝ V) :
    Disjoint (range fun x ↦ F (x, p)) (range j) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have hs := (isRegularParameter_iff.1 (isRegularIncidenceParameter_iff.1 h)) (x, y)
    (incidenceEquation_eq_zero.2 hy.symm)
  exact hV (Module.Finite.of_surjective _ hs)

/-- When `F` is differentiable at every incidence point, surjectivity of the derivative of `j`
there suffices for transverse incidence, without any rank condition on the source derivative
of `F`. This includes the identity map, even for a singular source slice. -/
theorem isRegularIncidenceParameter_of_surjective_fderiv
    {F : E × P → V} {j : W → V} {p : P}
    (hF : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hs : ∀ x y, F (x, p) = j y → Surjective (fderiv ℝ j y)) :
    IsRegularIncidenceParameter F j p := by
  rw [isRegularIncidenceParameter_iff_surjective hF
    fun _ y hxy ↦ differentiableAt_of_fderiv_surjective (hs _ y hxy)]
  intro x y hxy v
  obtain ⟨w, hw⟩ := hs x y hxy (-v)
  exact ⟨(0, w), by simp [hw, ← Prod.zero_eq_mk]⟩

/-- Incidence with the identity is regular exactly when the family is differentiable
at every source point of the parameter slice. -/
@[simp]
theorem isRegularIncidenceParameter_id {F : E × P → V} {p : P} :
    IsRegularIncidenceParameter F (id : V → V) p ↔ ∀ x, DifferentiableAt ℝ F (x, p) := by
  refine ⟨fun h x ↦ (h.differentiableAt (y := F (x, p)) rfl).1, fun hF ↦ ?_⟩
  apply isRegularIncidenceParameter_of_surjective_fderiv
    (fun x _ _ ↦ hF x)
  intro _ y _
  simpa using (Function.surjective_id : Surjective (id : V → V))

/-- Incidence with a constant map is the level equation at that constant. -/
@[simp]
theorem isRegularIncidenceParameter_const {F : E × P → V} {c : V} {p : P} :
    IsRegularIncidenceParameter F (fun _ : W ↦ c) p ↔ IsRegularParameter F c p := by
  refine ⟨fun h ↦ isRegularParameter_iff.2 fun x hx v ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨⟨u, _⟩, hu⟩ := h.surjective (y := 0) hx v
    exact ⟨u, by simpa using hu⟩
  · refine (isRegularIncidenceParameter_iff_surjective (fun _ _ hx ↦ h.differentiableAt hx)
      fun _ _ _ ↦ differentiableAt_const c).2 fun x _ hx v ↦ ?_
    obtain ⟨u, hu⟩ := isRegularParameter_iff.1 h x hx v
    exact ⟨(u, 0), by simpa using hu⟩

/-- Incidence with the zero map is the zero level equation. -/
@[simp]
theorem isRegularIncidenceParameter_zero {F : E × P → V} {p : P} :
    IsRegularIncidenceParameter F (0 : W → V) p ↔ IsRegularParameter F 0 p :=
  isRegularIncidenceParameter_const

end Regular

section Invariance

variable {E' W' V' P' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup P'] [NormedSpace ℝ P']

/-- **Nonlinear coordinate-change transfer for `IsRegularIncidenceParameterOn`.** Suppose
`φ : E' → E`, `ψ : W' → W`, `τ : P' → P`, and `χ : V → V'` satisfy, at each incidence point
`((x', y'), p') ∈ U'` with `χ (F (φ x', τ p')) = χ (j (ψ y'))`:
* `((φ x', ψ y'), τ p') ∈ U` and `F (φ x', τ p') = j (ψ y')` (`χ` reflects incidence equalities),
* `φ`, `ψ`, and `χ` have surjective derivatives at `x'`, `y'`, and `j (ψ y')` (which automatically
  makes them differentiable there), and `τ` is differentiable at `p'`.

Then regularity of `τ p'` on `U` transfers to regularity of `p'` on `U'` for the composed system
`z ↦ χ (F (φ z.1, τ z.2))` against `χ ∘ j ∘ ψ`, with no extra differentiability hypotheses on `F`
or `j`. This is the local chart-transfer step for manifold incidence transversality. -/
theorem IsRegularIncidenceParameterOn.comp {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {U' : Set ((E' × W') × P')}
    {φ : E' → E} {ψ : W' → W} {τ : P' → P} {χ : V → V'} {p' : P'}
    (h : IsRegularIncidenceParameterOn F j U (τ p'))
    (hmaps : ∀ x' y', ((x', y'), p') ∈ U' → χ (F (φ x', τ p')) = χ (j (ψ y')) →
      ((φ x', ψ y'), τ p') ∈ U ∧ F (φ x', τ p') = j (ψ y'))
    (hφ : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      Surjective (fderiv ℝ φ x'))
    (hψ : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      Surjective (fderiv ℝ ψ y'))
    (hτ : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      DifferentiableAt ℝ τ p')
    (hχ : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      Surjective (fderiv ℝ χ (j (ψ y')))) :
    IsRegularIncidenceParameterOn
      (fun z : E' × P' ↦ χ (F (φ z.1, τ z.2))) (fun y' ↦ χ (j (ψ y'))) U' p' := by
  have hF' : ∀ x' y', ((x', y'), p') ∈ U' → χ (F (φ x', τ p')) = χ (j (ψ y')) →
      DifferentiableAt ℝ (fun z : E' × P' ↦ χ (F (φ z.1, τ z.2))) (x', p') := by
    intro x' y' hU' hEq'
    obtain ⟨hU, hEq⟩ := hmaps x' y' hU' hEq'
    obtain ⟨hFxy, _⟩ := h.differentiableAt hU hEq
    have hχd : DifferentiableAt ℝ χ (F (φ x', τ p')) :=
      hEq.symm ▸ differentiableAt_of_fderiv_surjective (hχ x' y' hU' hEq)
    have hφd := differentiableAt_of_fderiv_surjective (hφ x' y' hU' hEq)
    have hpair : DifferentiableAt ℝ (fun z : E' × P' ↦ (φ z.1, τ z.2)) (x', p') :=
      (hφd.comp (x', p') differentiableAt_fst).prodMk
        ((hτ x' y' hU' hEq).comp (x', p') differentiableAt_snd)
    exact hχd.comp (x', p') (hFxy.comp (x', p') hpair)
  have hj' : ∀ x' y', ((x', y'), p') ∈ U' → χ (F (φ x', τ p')) = χ (j (ψ y')) →
      DifferentiableAt ℝ (fun w ↦ χ (j (ψ w))) y' := by
    intro x' y' hU' hEq'
    obtain ⟨hU, hEq⟩ := hmaps x' y' hU' hEq'
    obtain ⟨_, hjxy⟩ := h.differentiableAt hU hEq
    exact (differentiableAt_of_fderiv_surjective (hχ x' y' hU' hEq)).comp y'
      (hjxy.comp y' (differentiableAt_of_fderiv_surjective (hψ x' y' hU' hEq)))
  rw [isRegularIncidenceParameterOn_iff_surjective_coprod hF' hj']
  intro x' y' hU' hEq'
  obtain ⟨hU, hEq⟩ := hmaps x' y' hU' hEq'
  obtain ⟨hFxy, hjxy⟩ := h.differentiableAt hU hEq
  have hφs := hφ x' y' hU' hEq
  have hψs := hψ x' y' hU' hEq
  have hχs := hχ x' y' hU' hEq
  have hφd := differentiableAt_of_fderiv_surjective hφs
  have hψd := differentiableAt_of_fderiv_surjective hψs
  have hχd := differentiableAt_of_fderiv_surjective hχs
  have hsurj0 := h.surjective_coprod hU hEq
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
    neg_apply, ← map_neg, ← map_add] at huv ⊢
  exact congrArg (fderiv ℝ χ (j (ψ y'))) huv

/-- **Subset-localized invariance under continuous linear equivalences** on `E`, `W`, `P`, and `V`
(requiring no differentiability hypotheses on `F` or `j`). -/
theorem isRegularIncidenceParameterOn_comp_equiv_iff (eE : E' ≃L[ℝ] E) (eW : W' ≃L[ℝ] W)
    (eP : P' ≃L[ℝ] P) (eV : V ≃L[ℝ] V') {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p' : P'} :
    IsRegularIncidenceParameterOn
        (fun z : E' × P' ↦ eV (F (eE z.1, eP z.2))) (fun y' ↦ eV (j (eW y')))
        (((eE.prodCongr eW).prodCongr eP) ⁻¹' U) p' ↔
      IsRegularIncidenceParameterOn F j U (eP p') := by
  constructor
  · intro h
    have h₀ : IsRegularIncidenceParameterOn
        (fun z : E' × P' ↦ eV (F (eE z.1, eP z.2))) (fun y' ↦ eV (j (eW y')))
        (((eE.prodCongr eW).prodCongr eP) ⁻¹' U) (eP.symm (eP p')) := by
      simpa using h
    simpa using IsRegularIncidenceParameterOn.comp h₀ (U' := U)
      (φ := eE.symm) (ψ := eW.symm) (τ := eP.symm) (χ := eV.symm)
      (fun _ _ hU hEq ↦ ⟨by simpa using hU, eV.symm.injective hEq⟩)
      (fun _ _ _ _ ↦ by rw [eE.symm.fderiv]; exact eE.symm.surjective)
      (fun _ _ _ _ ↦ by rw [eW.symm.fderiv]; exact eW.symm.surjective)
      (fun _ _ _ _ ↦ eP.symm.differentiableAt)
      (fun _ _ _ _ ↦ by rw [eV.symm.fderiv]; exact eV.symm.surjective)
  · intro h
    exact IsRegularIncidenceParameterOn.comp h
      (φ := eE) (ψ := eW) (τ := eP) (χ := eV)
      (fun _ _ hU hEq ↦ ⟨by simpa using hU, eV.injective hEq⟩)
      (fun _ _ _ _ ↦ by rw [eE.fderiv]; exact eE.surjective)
      (fun _ _ _ _ ↦ by rw [eW.fderiv]; exact eW.surjective)
      (fun _ _ _ _ ↦ eP.differentiableAt)
      (fun _ _ _ _ ↦ by rw [eV.fderiv]; exact eV.surjective)

/-- **Invariance under continuous linear equivalences** on `E`, `W`, `P`, and `V` (requiring no
differentiability hypotheses on `F` or `j`). -/
theorem isRegularIncidenceParameter_comp_equiv_iff (eE : E' ≃L[ℝ] E) (eW : W' ≃L[ℝ] W)
    (eP : P' ≃L[ℝ] P) (eV : V ≃L[ℝ] V') {F : E × P → V} {j : W → V} {p' : P'} :
    IsRegularIncidenceParameter
        (fun z : E' × P' ↦ eV (F (eE z.1, eP z.2))) (fun y' ↦ eV (j (eW y'))) p' ↔
      IsRegularIncidenceParameter F j (eP p') := by
  simpa only [preimage_univ, isRegularIncidenceParameterOn_univ] using
    isRegularIncidenceParameterOn_comp_equiv_iff (F := F) (j := j) (U := univ) (p' := p')
      eE eW eP eV

end Invariance

end TauCeti
