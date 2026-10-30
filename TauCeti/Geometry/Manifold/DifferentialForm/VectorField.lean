/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity
public import Mathlib.Analysis.Calculus.DifferentialForm.VectorField
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

/-!
# Exterior differentiation evaluated on vector fields

The invariant formula for the exterior derivative expresses its evaluation on differentiable
vector fields as an alternating sum of directional derivatives and a sum of Lie-bracket terms.
It is useful when the fields are adapted to a distribution rather than to a coordinate chart.
The within-set statements also apply at boundary and corner points.

For vector fields `V` and `W` tangent to the kernel of a real one-form `α` near `x`, the formula
reduces to `α_x ([V, W]_x) = -dα_x (V_x, W_x)`
(`TauCeti.RoughForm.apply_mlieBracket_eq_neg_mextDeriv`), so the bracket stays in the kernel
exactly when `dα` vanishes on the fields (`TauCeti.RoughForm.mlieBracket_mem_ker_iff`).

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 14.29 and
  Proposition 14.32.
* Mathlib's `extDerivWithin_apply_vectorField`, the flat invariant formula transported here
  through the preferred extended chart.
-/

public section

noncomputable section

open Set Filter Bundle VectorField
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [IsManifold I 1 M]
  {k : ℕ} {s : Set M} {x : M}

private theorem inChartAt_apply_mpullbackWithin_eventuallyEq
    (φ : RoughForm I M F k) (V : Fin k → (y : M) → TangentSpace I y) :
    (fun z ↦ φ.inChartAt x z
      (fun i ↦ VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm (V i) (range I) z))
      =ᶠ[𝓝[range I] (extChartAt I x x)]
        (fun y ↦ φ y (V · y)) ∘ (extChartAt I x).symm := by
  filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
  have heval := RoughForm.inChartAt_apply φ x z
    (fun i ↦ VectorField.mpullbackWithin 𝓘(ℝ, E) I
      (extChartAt I x).symm (V i) (range I) z)
  refine heval.trans ?_
  congr 1
  funext i
  exact (isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse _

/-- In the preferred chart at `x`, differentiating the evaluation of a form's coordinate
expression on the coordinate expressions of vector fields gives the manifold derivative of the
evaluation of the form on the fields. -/
theorem fderivWithin_inChartAt_apply_mpullbackWithin
    (φ : RoughForm I M F k) (V : Fin k → (y : M) → TangentSpace I y)
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt x)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x))
    (hV : ∀ i, DifferentiableWithinAt ℝ
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm (V i) (range I))
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x)) :
    fderivWithin ℝ (fun z ↦ φ.inChartAt x z
      (fun i ↦ VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm (V i) (range I) z))
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) =
        mvfderivWithin I (fun y ↦ φ y (V · y)) s x := by
  have heq := inChartAt_apply_mpullbackWithin_eventuallyEq (x := x) φ V
  have hpoint := heq.self_of_nhdsWithin (mem_range_self (chartAt H x x))
  have heqs := heq.filter_mono (nhdsWithin_mono _
    (inter_subset_right (s := (extChartAt I x).symm ⁻¹' s)))
  have hpflat := (hφ.continuousAlternatingMap_apply hV).congr_of_eventuallyEq heqs.symm hpoint.symm
  have hp := hpflat.mdifferentiableWithinAt_of_comp_extChartAt_symm
  rw [hp.mvfderivWithin]
  simpa only [writtenInExtChartAt, extChartAt_self_eq, PartialEquiv.refl_coe,
    modelWithCornersSelf_coe, Function.id_comp] using heqs.fderivWithin_eq hpoint

/-- The invariant exterior-derivative formula within a subset, in positive degree.
The bracket sum uses pairs `(i.castSucc, j.succ)` with `i ≤ j`, so its sign is the negative
of the usual sum indexed by strictly increasing pairs. -/
theorem mextDerivWithin_apply_vectorField {n : ℕ}
    {φ : RoughForm I M F (n + 1)}
    {V : Fin (n + 2) → (y : M) → TangentSpace I y}
    (hφ : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin (n + 1)]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (n + 1)]→L[ℝ] F) y (φ y)) s x)
    (hV : ∀ i, MDifferentiableWithinAt I I.tangent
      (fun y ↦ (V i y : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mextDerivWithin φ s x (V · x) =
      (∑ i, (-1) ^ i.val •
        mvfderivWithin I (fun y ↦ φ y (i.removeNth (V · y))) s x (V i x)) -
      ∑ i : Fin (n + 1), ∑ j ≥ i, (-1) ^ (i + j : ℕ) •
        φ x (Matrix.vecCons (mlieBracketWithin I (V i.castSucc) (V j.succ) s x)
          (j.removeNth <| i.castSucc.removeNth (V · x))) := by
  -- Read both the form and the fields in the preferred chart, without requiring completeness.
  let V' : Fin (n + 2) → E → E := fun i ↦
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm (V i) (range I)
  let s' : Set E := (extChartAt I x).symm ⁻¹' s ∩ range I
  have hφ' : DifferentiableWithinAt ℝ (φ.inChartAt x) s' (extChartAt I x x) :=
    φ.differentiableWithinAt_inChartAt hφ
  have hV' : ∀ i, DifferentiableWithinAt ℝ (V' i) s' (extChartAt I x x) := by
    exact fun i ↦ (hV i).differentiableWithinAt_mpullbackWithin_extChartAt_symm
  -- At the chart centre, the tangent coordinates and the transported bracket are unchanged.
  have hvalue (i : Fin (n + 2)) : V' i (extChartAt I x x) = V i x :=
    VectorField.mpullbackWithin_extChartAt_symm_self (V i) x
  have hbracket (i j : Fin (n + 2)) :
      lieBracketWithin ℝ (V' i) (V' j) s' (extChartAt I x x) =
        mlieBracketWithin I (V i) (V j) s x :=
    VectorField.lieBracketWithin_mpullbackWithin_extChartAt_symm (V i) (V j) s x
  -- Apply the flat invariant formula, then transport its directional terms by germ equality.
  rw [mextDerivWithin_def]
  have hflat := extDerivWithin_apply_vectorField hφ' hV' hs
  have hvalues : (V' · (extChartAt I x x)) = (V · x) := funext hvalue
  rw [hvalues] at hflat
  refine hflat.trans ?_
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have hd := fderivWithin_inChartAt_apply_mpullbackWithin (s := s) φ
      (fun j ↦ V (i.succAbove j)) hφ' (fun j ↦ hV' (i.succAbove j))
    simp only [hvalue]
    simp +unfoldPartialApp only [Fin.removeNth, V', s']
    convert! congrArg (fun f : TangentSpace I x →L[ℝ] F ↦ f (V i x)) hd using 1
  · simp only [hbracket, RoughForm.inChartAt_extChartAt_self]
    rfl

/-- The invariant exterior-derivative formula on positive-degree forms. Each directional
term differentiates the scalar or vector-valued evaluation of the form on the other fields. -/
theorem mextDeriv_apply_vectorField {n : ℕ} {φ : RoughForm I M F (n + 1)}
    {V : Fin (n + 2) → (y : M) → TangentSpace I y}
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin (n + 1)]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (n + 1)]→L[ℝ] F) y (φ y)) x)
    (hV : ∀ i, MDifferentiableAt I I.tangent
      (fun y ↦ (V i y : TangentBundle I M)) x) :
    mextDeriv φ x (V · x) =
      (∑ i, (-1) ^ i.val •
        mvfderiv I (fun y ↦ φ y (i.removeNth (V · y))) x (V i x)) -
      ∑ i : Fin (n + 1), ∑ j ≥ i, (-1) ^ (i + j : ℕ) •
        φ x (Matrix.vecCons (mlieBracket I (V i.castSucc) (V j.succ) x)
          (j.removeNth <| i.castSucc.removeNth (V · x))) := by
  simpa only [mextDerivWithin_univ, mvfderivWithin_univ, mlieBracketWithin_univ] using
    mextDerivWithin_apply_vectorField hφ.mdifferentiableWithinAt
      (fun i ↦ (hV i).mdifferentiableWithinAt) (uniqueMDiffWithinAt_univ I)

/-- The exterior derivative of a one-form on two differentiable vector fields, within a subset:
`dφ(V, W) = V(φ(W)) - W(φ(V)) - φ([V, W])`. -/
theorem mextDerivWithin_apply_one {φ : RoughForm I M F 1}
    {V W : (y : M) → TangentSpace I y}
    (hφ : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] F) y (φ y)) s x)
    (hV : MDifferentiableWithinAt I I.tangent
      (fun y ↦ (V y : TangentBundle I M)) s x)
    (hW : MDifferentiableWithinAt I I.tangent
      (fun y ↦ (W y : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mextDerivWithin φ s x ![V x, W x] =
      mvfderivWithin I (fun y ↦ φ y ![W y]) s x (V x) -
        mvfderivWithin I (fun y ↦ φ y ![V y]) s x (W x) -
        φ x ![mlieBracketWithin I V W s x] := by
  have h := mextDerivWithin_apply_vectorField (V := ![V, W]) hφ
    (fun i ↦ by fin_cases i <;> assumption) hs
  simp +unfoldPartialApp [Fin.sum_univ_two, Fin.removeNth,
    sub_eq_add_neg] at h
  -- Evaluation commutes with these finite tuples; normalize them before comparing the formula.
  have htuple (y : M) : (fun i ↦ ![V, W] i y) = ![V y, W y] := by
    funext i
    fin_cases i <;> rfl
  have hWtuple (y : M) : (fun _ : Fin 1 ↦ W y) = ![W y] := by
    funext i
    fin_cases i
    rfl
  have hVtuple (y : M) : (fun i : Fin 1 ↦ ![V, W] (Fin.succAbove 1 i) y) = ![V y] := by
    funext i
    fin_cases i
    rfl
  have hempty : (fun _ : Fin 0 ↦ W x) = ![] := Subsingleton.elim _ _
  simpa only [htuple, hWtuple, hVtuple, hempty, sub_eq_add_neg] using h

/-- For a one-form and vector fields differentiable at a point, the exterior derivative is
the commutator of directional evaluations, corrected by evaluating the form on the Lie bracket. -/
theorem mextDeriv_apply_one {φ : RoughForm I M F 1}
    {V W : (y : M) → TangentSpace I y}
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] F) y (φ y)) x)
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x)
    (hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x) :
    mextDeriv φ x ![V x, W x] =
      mvfderiv I (fun y ↦ φ y ![W y]) x (V x) -
        mvfderiv I (fun y ↦ φ y ![V y]) x (W x) - φ x ![mlieBracket I V W x] := by
  simpa only [mextDerivWithin_univ, mvfderivWithin_univ, mlieBracketWithin_univ] using
    mextDerivWithin_apply_one hφ.mdifferentiableWithinAt hV.mdifferentiableWithinAt
      hW.mdifferentiableWithinAt (uniqueMDiffWithinAt_univ I)

section Kernel

variable {α : RoughForm I M ℝ 1} {V W : (y : M) → TangentSpace I y}

namespace RoughForm

/-- **Cartan's formula for the Levi form.** For vector fields `V` and `W` tangent to the kernel of
a one-form `α` near `x`, `α_x ([V, W]_x) = -dα_x (V_x, W_x)`. -/
theorem apply_mlieBracket_eq_neg_mextDeriv
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x)
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x)
    (hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x)
    (hVα : ∀ᶠ y in 𝓝 x, V y ∈ α.ker y) (hWα : ∀ᶠ y in 𝓝 x, W y ∈ α.ker y) :
    α x ![mlieBracket I V W x] = -mextDeriv α x ![V x, W x] := by
  have hzero {U : (y : M) → TangentSpace I y} (hU : ∀ᶠ y in 𝓝 x, U y ∈ α.ker y) :
      mvfderiv I (fun y ↦ α y ![U y]) x = 0 := by
    have hU' : (fun y ↦ α y ![U y]) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hU] with y hy using mem_ker.mp hy
    ext v
    simp [mvfderiv, hU'.mfderiv_eq]
  rw [mextDeriv_apply_one hα hV hW, hzero hVα, hzero hWα]
  simp

/-- For vector fields `V` and `W` tangent to the kernel of a one-form `α` near `x`, the bracket
`[V, W]_x` lies in `ker α_x` exactly when `dα_x (V_x, W_x) = 0`. -/
theorem mlieBracket_mem_ker_iff
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x)
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x)
    (hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x)
    (hVα : ∀ᶠ y in 𝓝 x, V y ∈ α.ker y) (hWα : ∀ᶠ y in 𝓝 x, W y ∈ α.ker y) :
    mlieBracket I V W x ∈ α.ker x ↔ mextDeriv α x ![V x, W x] = 0 := by
  rw [mem_ker, apply_mlieBracket_eq_neg_mextDeriv hα hV hW hVα hWα, neg_eq_zero]

end RoughForm

end Kernel

namespace SmoothForm

/-- The invariant exterior-derivative formula for a bundled smooth form. -/
theorem mextDeriv_apply_vectorField {n : ℕ} {φ : SmoothForm I M F (n + 1)}
    {V : Fin (n + 2) → (y : M) → TangentSpace I y}
    (hV : ∀ i, MDifferentiableAt I I.tangent
      (fun y ↦ (V i y : TangentBundle I M)) x) :
    mextDeriv φ.1 x (V · x) =
      (∑ i, (-1) ^ i.val •
        mvfderiv I (fun y ↦ φ.1 y (i.removeNth (V · y))) x (V i x)) -
      ∑ i : Fin (n + 1), ∑ j ≥ i, (-1) ^ (i + j : ℕ) •
        φ.1 x (Matrix.vecCons (mlieBracket I (V i.castSucc) (V j.succ) x)
          (j.removeNth <| i.castSucc.removeNth (V · x))) := by
  exact TauCeti.mextDeriv_apply_vectorField (φ.mdifferentiableAt x) hV

/-- The invariant formula for the exterior derivative of a bundled smooth one-form. -/
theorem mextDeriv_apply_one {φ : SmoothForm I M F 1}
    {V W : (y : M) → TangentSpace I y}
    (hV : MDifferentiableAt I I.tangent
      (fun y ↦ (V y : TangentBundle I M)) x)
    (hW : MDifferentiableAt I I.tangent
      (fun y ↦ (W y : TangentBundle I M)) x) :
    mextDeriv φ.1 x ![V x, W x] =
      mvfderiv I (fun y ↦ φ.1 y ![W y]) x (V x) -
        mvfderiv I (fun y ↦ φ.1 y ![V y]) x (W x) -
        φ.1 x ![mlieBracket I V W x] := by
  exact TauCeti.mextDeriv_apply_one (φ.mdifferentiableAt x) hV hW

end SmoothForm

end TauCeti
