/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import TauCeti.Geometry.Manifold.VectorBundle.DoubleDual.Line
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Differential forms as density-valued double duals

The coefficient bundle for distributional `k`-currents is the density-valued dual of
the bundle of real `k`-forms. Its test fibres are the second density-valued duals.
Fibrewise evaluation identifies these test fibres with the original form fibres and
gives a diffeomorphism of total spaces. This uses the intrinsic density line and the
native alternating-map bundle, in every degree and without a metric or orientation.
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold Topology

namespace ModelWithCorners

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The fibre of real `k`-forms identified with its double dual with values in the
intrinsic density line. The map from the double dual to the form fibre is the inverse. -/
def formDensityDoubleDualEquiv (k : ℕ) (x : M) :=
  bundleLineDoubleDualEquiv (𝕜 := ℝ) (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ) (DensityBundle I M) x

/-- The image of a form in its test fibre evaluates a density-valued functional on the form. -/
@[simp]
theorem formDensityDoubleDualEquiv_apply (k : ℕ) (x : M)
    (η : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
    (φ : (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x) :
    I.formDensityDoubleDualEquiv k x η φ = φ η := by
  rw [formDensityDoubleDualEquiv, bundleLineDoubleDualEquiv_apply]

-- Supplying the bounded-convergence topology directly lets elaboration resolve inverses
-- on the nested continuous-linear-map space without any new instances.

/-- Evaluating the recovered form against a density-valued functional returns the
evaluation of the original test fibre element. -/
@[simp]
theorem apply_formDensityDoubleDualEquiv_symm (k : ℕ) (x : M)
    (Φ : ((TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x) →L[ℝ] DensityBundle I M x)
    (φ : (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x) :
    letI := ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℝ)
      (E := (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x)
      (F := DensityBundle I M x)
    φ ((I.formDensityDoubleDualEquiv k x).symm Φ) = Φ φ := by
  unfold formDensityDoubleDualEquiv
  exact apply_bundleLineDoubleDualEquiv_symm (𝕜 := ℝ) (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ) (DensityBundle I M) x Φ φ

attribute [local instance] Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
  Bundle.ContinuousLinearMap.fiberBundle Bundle.ContinuousLinearMap.vectorBundle

/-- The real `k`-form bundle and the bundle of test fibres for distributional
`k`-currents have smoothly isomorphic total spaces. -/
def formDensityDoubleDualDiffeomorph (k : ℕ) :=
  bundleLineDoubleDualDiffeomorph (I := I) (n := ∞) (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) (DensityBundle I M)

/-- On total spaces the identification fixes the base point and evaluates in the fibre. -/
@[simp]
theorem formDensityDoubleDualDiffeomorph_apply (k : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    I.formDensityDoubleDualDiffeomorph k p =
      ⟨p.proj, I.formDensityDoubleDualEquiv k p.proj p.snd⟩ :=
  bundleLineDoubleDualDiffeomorph_apply _ _ p

/-- The inverse total-space map recovers the form at the same base point. -/
@[simp]
theorem formDensityDoubleDualDiffeomorph_symm_apply (k : ℕ)
    (p : TotalSpace (((E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ)
      (fun x : M ↦ ((TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x) →L[ℝ]
        DensityBundle I M x)) :
    letI := ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℝ)
      (E := (TangentSpace I p.proj [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M p.proj)
      (F := DensityBundle I M p.proj)
    (I.formDensityDoubleDualDiffeomorph k).symm p =
      ⟨p.proj, (I.formDensityDoubleDualEquiv k p.proj).symm p.snd⟩ := by
  unfold formDensityDoubleDualDiffeomorph formDensityDoubleDualEquiv
  exact bundleLineDoubleDualDiffeomorph_symm_apply _ _ p

end ModelWithCorners
