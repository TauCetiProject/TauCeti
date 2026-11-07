/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.AlongCurve
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# Acceleration and second covariant derivatives under local Riemannian isometries

The differential of a local Riemannian isometry carries the covariant acceleration of a
`C²` curve to that of its image. Since this differential is injective, vanishing acceleration
can also be tested after composing with the local isometry. These statements apply to curves
lifted through Riemannian covering sheets, without a global inverse or a completeness assumption.

The derivatives are taken within an explicit parameter set with unique derivatives, including
closed intervals. The unrestricted forms apply to globally `C²` curves.
For smooth metrics the same naturality holds for the second covariant derivative of any field
with a `C²` tangent-bundle lift, without an assumed Jacobi equation.

The argument specializes the arbitrary-field naturality theorem
`TauCeti.IsLocalRiemannianIsometry.mfderiv_alongCurveWithin` to the curve's velocity.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 2, Theorem 3.6.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.IsLocalRiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 2 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} {γ : ℝ → M} {s : Set ℝ} {t : ℝ}

/-- A local Riemannian isometry preserves covariant acceleration within a parameter set. -/
theorem mfderiv_accelerationWithin (hf : IsLocalRiemannianIsometry I J f)
    (hs : UniqueDiffOn ℝ s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s) (ht : t ∈ s) :
    mfderiv I J f (γ t) (accelerationWithin (leviCivitaConnection I M) γ s t) =
      accelerationWithin (leviCivitaConnection J N) (f ∘ γ) s t := by
  have hvelocity (r : ℝ) (hr : r ∈ s) :
      curveVelocityWithin J (f ∘ γ) s r =
        mfderiv I J f (γ r) (curveVelocityWithin I γ s r) :=
    curveVelocityWithin_map (hf.mdifferentiableAt _)
      ((hγ.mdifferentiableOn (by norm_num)) r hr)
  have hcoord := differentiableWithinAt_sectionCoord_curveVelocityWithin γ hs hγ ht
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  rw [accelerationWithin_def, accelerationWithin_def,
    hf.mfderiv_alongCurveWithin (hs t ht) ((hγ.mdifferentiableOn (by norm_num)) t ht) hcoord,
    alongCurveWithin_congr _ _ _ (eventually_mem_nhdsWithin.mono hvelocity) (hvelocity t ht)]

/-- The acceleration of a `C²` curve vanishes exactly when that of its image under a local
Riemannian isometry vanishes. -/
theorem accelerationWithin_comp_eq_zero_iff (hf : IsLocalRiemannianIsometry I J f)
    (hs : UniqueDiffOn ℝ s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s) (ht : t ∈ s) :
    accelerationWithin (leviCivitaConnection J N) (f ∘ γ) s t = 0 ↔
      accelerationWithin (leviCivitaConnection I M) γ s t = 0 := by
  rw [← hf.mfderiv_accelerationWithin hs hγ ht]
  exact map_eq_zero_iff _ (hf.mfderiv_injective _)

/-- A local Riemannian isometry preserves the unrestricted covariant acceleration. -/
theorem mfderiv_acceleration (hf : IsLocalRiemannianIsometry I J f)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) (t : ℝ) :
    mfderiv I J f (γ t) (acceleration (leviCivitaConnection I M) γ t) =
      acceleration (leviCivitaConnection J N) (f ∘ γ) t := by
  rw [← accelerationWithin_univ, ← accelerationWithin_univ]
  exact hf.mfderiv_accelerationWithin uniqueDiffOn_univ hγ.contMDiffOn (mem_univ t)

/-- A globally `C²` curve has zero acceleration exactly when its image under a local
Riemannian isometry does. -/
theorem acceleration_comp_eq_zero_iff (hf : IsLocalRiemannianIsometry I J f)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) (t : ℝ) :
    acceleration (leviCivitaConnection J N) (f ∘ γ) t = 0 ↔
      acceleration (leviCivitaConnection I M) γ t = 0 := by
  rw [← hf.mfderiv_acceleration hγ t]
  exact map_eq_zero_iff _ (hf.mfderiv_injective _)

section Smooth

variable [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A local Riemannian isometry commutes with the second covariant derivative of a field with
`C²` tangent-bundle lift. No geodesic or Jacobi equation is assumed. -/
theorem mfderiv_alongCurveWithin_alongCurveWithin (hf : IsLocalRiemannianIsometry I J f)
    {V : ∀ r, TangentSpace I (γ r)} (hs : UniqueDiffOn ℝ s)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s) (ht : t ∈ s) :
    mfderiv I J f (γ t) (alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ V s) s t) =
      alongCurveWithin (leviCivitaConnection J N) (f ∘ γ)
        (alongCurveWithin (leviCivitaConnection J N) (f ∘ γ)
          (fun r ↦ mfderiv I J f (γ r) (V r)) s) s t := by
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s :=
    (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I)
      (n := 2)).comp_contMDiffOn hV
  have hfirst (r : ℝ) (hr : r ∈ s) := hf.mfderiv_alongCurveWithin (hs r hr)
    ((hγ.mdifferentiableOn (by norm_num)) r hr)
    (differentiableWithinAt_sectionCoord γ V
      ((hV r hr).mdifferentiableWithinAt (by norm_num))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ r)))
  rw [hf.mfderiv_alongCurveWithin (hs t ht)
    ((hγ.mdifferentiableOn (by norm_num)) t ht)
    (differentiableWithinAt_sectionCoord_alongCurveWithin_leviCivitaConnection hs hV ht)]
  exact alongCurveWithin_congr _ _ _ (eventually_mem_nhdsWithin.mono hfirst) (hfirst t ht)

end Smooth

end TauCeti.IsLocalRiemannianIsometry
