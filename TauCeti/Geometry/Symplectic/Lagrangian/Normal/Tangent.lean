/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.Normal.Basic

/-!
# Normal covectors of Lagrangian immersions

At a point of a Lagrangian immersion `f : N → M`, the quotient of the ambient
tangent space by `range (df)` is canonically the continuous dual of the source
tangent space. The identification is `[n] ↦ (v ↦ σ(df v, n))`; in particular it
uses the sign appropriate to the canonical form `ω = -dλ` on a cotangent bundle.
For a map with Lagrangian tangent images, the differential need only be injective
at the point in question. Thus it also applies to embeddings and does not impose
compactness, closedness of the two-form, or a choice of transverse complement.

This is a fibrewise statement. No smooth structure on the family of normal
quotients is asserted here.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Section 8.1.
-/

public noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M}

/-- The normal quotient at a Lagrangian tangent image with injective differential
is canonically the cotangent space of the source, by `[n](v) = σ(df v, n)`. -/
def IsLagrangianMap.normalCotangentEquiv (h : hσ.IsLagrangianMap J f) (x : N)
    (hinj : Function.Injective (mfderiv J I f x)) :
    (TangentSpace I (f x) ⧸ LinearMap.range (mfderiv J I f x).toLinearMap) ≃L[ℝ]
      (TangentSpace J x →L[ℝ] ℝ) :=
  letI : FiniteDimensional ℝ (TangentSpace J x) :=
    FiniteDimensional.of_injective (mfderiv J I f x).toLinearMap hinj
  letI : IsClosed (LinearMap.range (mfderiv J I f x).toLinearMap :
      Set (TangentSpace I (f x))) := Submodule.closed_of_finiteDimensional _
  (((isLagrangianMap_iff_forall.mp h x).normalEquivDual.trans
    (LinearEquiv.ofInjective (mfderiv J I f x).toLinearMap hinj).dualMap).trans
      LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

/-- Evaluation of the cotangent identification on a representative of a normal class. -/
@[simp]
theorem IsLagrangianMap.normalCotangentEquiv_mk_apply (h : hσ.IsLagrangianMap J f)
    (x : N) (hinj : Function.Injective (mfderiv J I f x))
    (n : TangentSpace I (f x)) (v : TangentSpace J x) :
    h.normalCotangentEquiv x hinj (Submodule.Quotient.mk n) v =
      SmoothBundleForm.eval₂ σ (f x) (mfderiv J I f x v) n := by
  simp [normalCotangentEquiv]

/-- A normal class is the one corresponding to a prescribed covector exactly when
all its symplectic pairings with tangent vectors have the prescribed values. -/
theorem IsLagrangianMap.normalCotangentEquiv_symm_apply_eq_mk_iff
    (h : hσ.IsLagrangianMap J f) (x : N) (hinj : Function.Injective (mfderiv J I f x))
    (α : TangentSpace J x →L[ℝ] ℝ) (n : TangentSpace I (f x)) :
    (h.normalCotangentEquiv x hinj).symm α = Submodule.Quotient.mk n ↔
      ∀ v : TangentSpace J x, SmoothBundleForm.eval₂ σ (f x) (mfderiv J I f x v) n = α v := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  exact ContinuousLinearMap.ext_iff.trans
    (forall_congr' fun v ↦ by rw [normalCotangentEquiv_mk_apply, eq_comm])

end TauCeti.SmoothTwoForm.IsNondegenerate
