/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Analysis.Matrix.Normed
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.RegularValue.Level
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.Det
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Analysis.Calculus.ContDiff.Matrix

/-!
# The analytic special linear group

The special linear group over `ℝ` or `ℂ` is an analytic Lie group with its existing subspace
topology. Its matrix inclusion is an analytic embedding, and the tangent image at the identity
is exactly the trace-zero matrices. The model has dimension `card n * card n - 1`, including
the trivial group with empty matrix index.

The public atlas is chosen nonconstructively and characterized by its analytic manifold and
matrix-embedding properties. For a nonempty index, `det = 1` is a regular level; the empty-index
group admits the discrete singleton atlas. Use `instIsManifold` and `isSmoothEmbedding_subtypeVal`
instead of unfolding individual charts.

Matrix-valued maps use the `L∞` operator norm. Enable `open scoped Matrix.Norms.Operator` and
`attribute [local instance] Matrix.linftyOpTopologicalSpace` when using these results.

## Main declarations

* `Matrix.SpecialLinearGroup.Model`: the model vector space.
* `Matrix.SpecialLinearGroup.instChartedSpace`, `Matrix.SpecialLinearGroup.instIsManifold`,
  `Matrix.SpecialLinearGroup.instLieGroup`: the native analytic structures.
* `Matrix.SpecialLinearGroup.isSmoothEmbedding_subtypeVal`: the analytic matrix embedding.
* `Matrix.SpecialLinearGroup.contMDiff_subtypeVal`, `Matrix.SpecialLinearGroup.contMDiff_toGL`:
  analytic inclusions into matrices and the general linear group.
* `Matrix.SpecialLinearGroup.range_mvfderiv_subtypeVal_one`: the trace-zero tangent image.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Chapter 5, Corollary 5.14 (Regular Level Set Theorem), and Chapter 7, Example 7.18(c),(e).
-/

public noncomputable section

open Matrix Manifold Function
open scoped ContDiff Manifold Matrix.Norms.Operator
attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace Matrix.SpecialLinearGroup

/-- The model of dimension `card n * card n - 1` for the special linear group. -/
abbrev Model (n : Type*) [Fintype n] (𝕜 : Type*) :=
  Fin (Fintype.card n * Fintype.card n - 1) → 𝕜

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

private theorem existsSLCharts :
    ∃ c : ChartedSpace (Model n 𝕜) (SpecialLinearGroup n 𝕜),
      let := c
      IsManifold 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) ∧
        Manifold.IsSmoothEmbedding 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) ω
          (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have : IsEmpty (Fin (Fintype.card n * Fintype.card n - 1)) := by
      simp only [Fintype.card_of_isEmpty, zero_mul, Nat.zero_sub]
      infer_instance
    let : ChartedSpace (Model n 𝕜) (SpecialLinearGroup n 𝕜) :=
      ChartedSpace.ofDiscreteTopology
    let : IsManifold 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) :=
      IsManifold.of_discreteTopology ω
    exact ⟨inferInstance, inferInstance,
      contMDiff_of_subsingleton.isImmersion_of_injective_mfderiv (by simp)
        (fun x u v _ ↦
          (tangentSpaceCastModel 𝓘(𝕜, Model n 𝕜) x).injective (Subsingleton.elim _ _)), .subtypeVal⟩
  | inr hn =>
    have hf : ContDiff 𝕜 ω (det : Matrix n n 𝕜 → 𝕜) :=
      ContDiff.matrix_det fun i j ↦ (Matrix.entryLinearMap 𝕜 𝕜 i j).toContinuousLinearMap.contDiff
    have hfm (x : Matrix n n 𝕜) (_ : x.det = 1) :
        ContMDiffAt 𝓘(𝕜, Matrix n n 𝕜) 𝓘(𝕜, 𝕜) ω det x := hf.contMDiff.contMDiffAt
    have hf1 (x : Matrix n n 𝕜) (hx : x.det = 1) :
        ContMDiffAt 𝓘(𝕜, Matrix n n 𝕜) 𝓘(𝕜, 𝕜) 1 det x := (hfm x hx).of_le le_top
    have hreg := Matrix.isRegularValue_det (n := n) (𝕜 := 𝕜) one_ne_zero
    have hdim : Module.finrank 𝕜 (Matrix n n 𝕜) - Module.finrank 𝕜 𝕜 =
        Fintype.card n * Fintype.card n - 1 := by simp [Module.finrank_matrix]
    let c : ChartedSpace (Model n 𝕜) (SpecialLinearGroup n 𝕜) :=
      TauCeti.regularLevelChartedSpace (I := 𝓘(𝕜, Matrix n n 𝕜)) (M := Matrix n n 𝕜)
        (f := det) (c := 1) hf1 hreg hdim
    let := c
    have hm : IsManifold 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) :=
      TauCeti.isManifold_regularLevel (by simp) hfm hreg hdim
    have he : Manifold.IsSmoothEmbedding 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) ω
        (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) :=
      TauCeti.isSmoothEmbedding_coe_regularLevel
        (I := 𝓘(𝕜, Matrix n n 𝕜)) (M := Matrix n n 𝕜) (f := det) (c := 1)
        (by simp) hfm hreg hdim
    exact ⟨c, hm, he⟩

/-- A nonconstructively chosen analytic atlas on the native special linear group.
Its public properties are `instIsManifold` and `isSmoothEmbedding_subtypeVal`; individual charts
are not specified. -/
@[instance_reducible]
instance instChartedSpace : ChartedSpace (Model n 𝕜) (SpecialLinearGroup n 𝕜) :=
  -- Private witness lookup is unavailable in exported data, and an untyped proof leaves
  -- choose's predicate unresolved. Proof irrelevance identifies this witness with the
  -- one used by choose_spec below.
  Classical.choose (show ∃ c : ChartedSpace (Model n 𝕜) (SpecialLinearGroup n 𝕜),
    let := c
    IsManifold 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) ∧
      Manifold.IsSmoothEmbedding 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) ω
        (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) from by exact existsSLCharts)

/-- The special linear group is an analytic manifold over its scalar field. -/
instance instIsManifold : IsManifold 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) :=
  (Classical.choose_spec existsSLCharts).1

/-- The matrix inclusion of the special linear group is an analytic embedding. -/
theorem isSmoothEmbedding_subtypeVal :
    Manifold.IsSmoothEmbedding 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) ω
      (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) :=
  (Classical.choose_spec existsSLCharts).2

/-- The matrix inclusion of the special linear group has every differentiability order. -/
theorem contMDiff_subtypeVal {k : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) k
      (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) :=
  isSmoothEmbedding_subtypeVal.contMDiff.of_le le_top

/-- The inclusion of the special linear group into the general linear group is analytic. -/
theorem contMDiff_toGL {k : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) k
      (SpecialLinearGroup.toGL : SpecialLinearGroup n 𝕜 → GL n 𝕜) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  simpa only [Function.comp_def, SpecialLinearGroup.coe_GL_coe_matrix] using
    (isSmoothEmbedding_subtypeVal (n := n) (𝕜 := 𝕜)).contMDiff.of_le (show k ≤ ω from le_top)

/-- The special linear group is an analytic Lie group over its scalar field. -/
instance instLieGroup : LieGroup 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) := by
  have hi := (isSmoothEmbedding_subtypeVal (n := n) (𝕜 := 𝕜)).1
  exact
    { contMDiff_mul := (ContMDiff.iff_comp_isImmersion hi).2 ⟨continuous_mul, by
        refine (Units.contMDiff_val.comp
          (((contMDiff_toGL (n := n) (𝕜 := 𝕜)).comp contMDiff_fst).mul
            ((contMDiff_toGL (n := n) (𝕜 := 𝕜)).comp contMDiff_snd))).congr ?_
        intro p
        exact (SpecialLinearGroup.coe_mul p.1 p.2).trans
          (Units.val_mul (SpecialLinearGroup.toGL p.1) (SpecialLinearGroup.toGL p.2)).symm⟩
      contMDiff_inv := (ContMDiff.iff_comp_isImmersion hi).2 ⟨continuous_inv, by
        simpa only [Function.comp_def, ← map_inv, SpecialLinearGroup.coe_GL_coe_matrix] using
          Units.contMDiff_val.comp (contMDiff_toGL (n := n) (𝕜 := 𝕜)).inv⟩ }

/-- The tangent image at the identity consists exactly of the trace-zero matrices. -/
theorem range_mvfderiv_subtypeVal_one :
    (mvfderiv 𝓘(𝕜, Model n 𝕜)
      (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) 1).range =
      (Matrix.traceLinearMap n 𝕜 𝕜).ker := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn => exact Subsingleton.elim _ _
  | inr hn =>
    have hr := (Matrix.isRegularValue_det (n := n) (𝕜 := 𝕜) one_ne_zero).isRegularPoint
      (x := (1 : Matrix n n 𝕜)) (by simp)
    have heq :
        (mfderiv 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜)
          (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) 1).range =
          (mfderiv 𝓘(𝕜, Matrix n n 𝕜) 𝓘(𝕜, 𝕜) det 1).ker :=
      hr.range_mfderiv_eq_ker_mfderiv
      (g := fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) (p := 1)
      (.of_forall fun A ↦ A.2)
      ((isSmoothEmbedding_subtypeVal (n := n) (𝕜 := 𝕜)).1.mfderiv_injective (by simp) 1)
      (by
        simp only [Module.finrank_matrix, Module.finrank_self, Module.finrank_fin_fun, Model]
        have hdim := hr.finrank_ker_mfderiv_add_finrank
        simp only [Module.finrank_matrix, Module.finrank_self] at hdim
        omega)
    let e := NormedSpace.fromTangentSpace (𝕜 := 𝕜) (1 : Matrix n n 𝕜)
    let tr : Matrix n n 𝕜 →L[𝕜] 𝕜 := (traceLinearMap n 𝕜 𝕜).toContinuousLinearMap
    have hd : mvfderiv 𝓘(𝕜, Matrix n n 𝕜) det 1 = tr.comp e.toContinuousLinearMap := by
      ext v
      calc
        mvfderiv 𝓘(𝕜, Matrix n n 𝕜) det 1 v = trace (e v) := Matrix.mvfderiv_det_one v
        _ = (tr.comp e.toContinuousLinearMap) v := by
          simp [tr]
    rw [← TauCeti.ker_mvfderiv, hd] at heq
    have hmap := congrArg (Submodule.map e.toLinearMap) heq
    have hcancel := Submodule.map_comap_eq_of_surjective (f := e.toLinearMap)
      e.surjective tr.toLinearMap.ker
    rw [TauCeti.range_mvfderiv]
    exact hmap.trans hcancel


end Matrix.SpecialLinearGroup
