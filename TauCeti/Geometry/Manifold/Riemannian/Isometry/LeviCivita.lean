/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic

/-!
# The Levi-Civita connection under Riemannian isometries

A local Riemannian isometry `f : M → N`, and in particular a smooth Riemannian isometry, transports
the Levi-Civita connection of `N` to that of `M`: for a vector field `Y` on `N`, differentiable at
`f x`, and a tangent vector `v` at `x`,

`df_x (∇ᴹ_v (f^* Y)) = ∇ᴺ_{df_x v} Y`,

where `f^* Y = VectorField.mpullback I J f Y` is the pullback vector field
`x ↦ (df_x)⁻¹ (Y (f x))`. Equivalently, the connection on `M` obtained by transporting `∇ᴺ`
along `f` agrees with `∇ᴹ` on differentiable vector fields. Only the differential of `f` at each
point enters, so `f` need not be injective or surjective: this also covers the inclusion of an
open submanifold with the restricted metric.

This is the connection-level input for transporting geodesics, their maximal intervals, and
exponential maps along Riemannian isometries.

## Main results

In the namespace `TauCeti.IsLocalRiemannianIsometry`:

* `koszul_mpullback`: the Koszul expression is natural under local Riemannian isometries.
* `mfderiv_apply_mpullback_of_isLeviCivitaConnection`: **naturality of Levi-Civita
  connections** under local Riemannian isometries.
* `mfderiv_leviCivitaConnection_mpullback`: the same statement for Mathlib's
  `CovariantDerivative.leviCivitaConnection`.
* `leviCivitaConnection_mpullback_apply_mpullback`: the vector-field form
  `∇ᴹ_{f^* Y} (f^* Z) = f^* (∇ᴺ_Y Z)`.

A Riemannian isometry `Φ` is a local Riemannian isometry
(`TauCeti.RiemannianIsometry.isLocalRiemannianIsometry`), so these apply to it through
`Φ.isLocalRiemannianIsometry`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, Thm. 3.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., GTM 176, 2018, Prop. 5.13.
-/

public section

open Bundle FiberBundle Manifold VectorField CovariantDerivative
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

variable [IsManifold I 2 M] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

namespace IsLocalRiemannianIsometry

variable {f : M → N}

/-- **Naturality of the Koszul expression.** The Koszul expression of the pullbacks of three
vector fields along a local Riemannian isometry `f` is the Koszul expression of the fields
themselves, evaluated at the image point. -/
theorem koszul_mpullback [CompleteSpace E] (hf : IsLocalRiemannianIsometry I J f)
    {X Y Z : Π y : N, TangentSpace J y} {x : M} (hX : MDiffAt (T% X) (f x))
    (hY : MDiffAt (T% Y) (f x)) (hZ : MDiffAt (T% Z) (f x)) :
    koszul I (mpullback I J f X) (mpullback I J f Y) (mpullback I J f Z) x =
      koszul J X Y Z (f x) := by
  have h := koszulBilinear_mpullback (b := fun _ ↦ innerSL ℝ) (b' := fun _ ↦ innerSL ℝ)
    (hf.contMDiff.contMDiffAt.of_le (by simp)) hf.isInvertible_mfderiv
    (fun y v w ↦ by simp only [innerSL_apply_apply ℝ, hf.inner_mfderiv])
    (fun _ _ hV hW ↦ by simpa only [innerSL_apply_apply ℝ] using mdifferentiableAt_inner hV hW)
    hX hY hZ
  rw [koszul_apply, koszul_apply]
  simpa only [koszulBilinear_apply, innerSL_apply_apply ℝ] using h

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **Naturality of Levi-Civita connections under local Riemannian isometries.** If `∇ᴹ` and `∇ᴺ`
are Levi-Civita connections of `M` and `N` and `f : M → N` is a local Riemannian isometry, then
`df_x (∇ᴹ_v (f^* Y)) = ∇ᴺ_{df_x v} Y` for every vector field `Y` on `N` differentiable at
`f x`. -/
theorem mfderiv_apply_mpullback_of_isLeviCivitaConnection (hf : IsLocalRiemannianIsometry I J f)
    {covM : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    {covN : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)}
    (hM : covM.IsLeviCivitaConnection) (hN : covN.IsLeviCivitaConnection)
    {Y : Π y : N, TangentSpace J y} {x : M} (hY : MDiffAt (T% Y) (f x)) (v : TangentSpace I x) :
    mfderiv I J f x (covM (mpullback I J f Y) x v) = covN Y (f x) (mfderiv I J f x v) := by
  -- Realize the direction `df_x v` by a vector field on `N` whose pullback takes the value `v`.
  obtain ⟨X, hX, hXv⟩ : ∃ X : Π y : N, TangentSpace J y,
      MDiffAt (T% X) (f x) ∧ X (f x) = mfderiv I J f x v :=
    ⟨extend F _, mdifferentiableAt_extend J F _, extend_apply_self F _⟩
  have hXx : mpullback I J f X x = v := (hf.mpullback_apply_eq_iff X v).2 hXv
  refine injective_inner_mdifferentiableAt_section J F (TangentSpace J) (f x) ?_
  ext Z hZ
  dsimp only
  have hMk := hM.two_inner_eq_koszul (hf.mdifferentiableAt_mpullback hX)
    (hf.mdifferentiableAt_mpullback hY) (hf.mdifferentiableAt_mpullback hZ)
  have hNk := hN.two_inner_eq_koszul hX hY hZ
  rw [hf.koszul_mpullback hX hY hZ, hXx] at hMk
  rw [hXv] at hNk
  have hinner : inner ℝ (mfderiv I J f x (covM (mpullback I J f Y) x v)) (Z (f x)) =
      inner ℝ (covM (mpullback I J f Y) x v) (mpullback I J f Z x) := by
    rw [← hf.inner_mfderiv x, hf.mfderiv_apply_mpullback]
  linarith

/-- **Naturality of the Levi-Civita connection under local Riemannian isometries**, for Mathlib's
`CovariantDerivative.leviCivitaConnection`:
`df_x (∇ᴹ_v (f^* Y)) = ∇ᴺ_{df_x v} Y` for every vector field `Y` on `N` differentiable at
`f x`. -/
@[simp]
theorem mfderiv_leviCivitaConnection_mpullback (hf : IsLocalRiemannianIsometry I J f)
    {Y : Π y : N, TangentSpace J y} {x : M} (hY : MDiffAt (T% Y) (f x)) (v : TangentSpace I x) :
    mfderiv I J f x (leviCivitaConnection I M (mpullback I J f Y) x v) =
      leviCivitaConnection J N Y (f x) (mfderiv I J f x v) :=
  hf.mfderiv_apply_mpullback_of_isLeviCivitaConnection
    (isLeviCivitaConnection_leviCivitaConnection I) (isLeviCivitaConnection_leviCivitaConnection J)
    hY v

/-- The covariant derivative of a pulled-back vector field in a pulled-back direction is the
pullback of the covariant derivative: `∇ᴹ_{f^* Y} (f^* Z) = f^* (∇ᴺ_Y Z)` at `x`. -/
theorem leviCivitaConnection_mpullback_apply_mpullback (hf : IsLocalRiemannianIsometry I J f)
    {Y Z : Π y : N, TangentSpace J y} {x : M} (hZ : MDiffAt (T% Z) (f x)) :
    leviCivitaConnection I M (mpullback I J f Z) x (mpullback I J f Y x) =
      mpullback I J f (fun y ↦ leviCivitaConnection J N Z y (Y y)) x := by
  apply hf.mfderiv_injective x
  rw [hf.mfderiv_leviCivitaConnection_mpullback hZ, hf.mfderiv_apply_mpullback,
    hf.mfderiv_apply_mpullback]

end IsLocalRiemannianIsometry

end TauCeti

end
