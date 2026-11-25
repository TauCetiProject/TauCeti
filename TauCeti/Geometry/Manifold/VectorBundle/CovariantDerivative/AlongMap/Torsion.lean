/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Coordinate.Frame
public import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# The torsion identity along a map

Let `f : M → N` be a map and `∇` a covariant derivative on the tangent bundle of `N`. For vector
fields `X` and `Y` on `M`, `df Y : x ↦ df_x (Y x)` is a tangent field along `f`, and
`∇_X (df Y)` denotes its covariant derivative along `f` (`CovariantDerivative.alongMap`).

For a torsion-free `∇` and a map `f` which is `C²` at `x`, the pulled-back torsion identity
`∇_X (df Y) - ∇_Y (df X) = df [X, Y]` holds at `x`
(`CovariantDerivative.alongMap_mfderiv_sub_alongMap_mfderiv`). Read in the chart of `N` at `f x`,
`df Y` is the derivative of the coordinate expression `φ ∘ f` of `f` along `Y`
(`TauCeti.Manifold.sectionCoord_mfderiv_eventuallyEq`). The derivative terms then give
`d(φ ∘ f) [X, Y]` by the symmetry of second derivatives (`mvfderiv_mlieBracket`), and the
Christoffel terms cancel because the Christoffel form of a torsion-free connection is symmetric
(`TauCeti.Manifold.christoffelForm_comm`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 8: the symmetry of
  the second fundamental form rests on this identity.
-/

public section

open Bundle Manifold Module Set Filter VectorField
open scoped ContDiff Manifold Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

namespace TauCeti.Manifold

/-- Near `x`, the reading of `df Y` in the chart of `N` at `f x` is the derivative of the
coordinate expression `φ ∘ f` of `f` along `Y`. -/
theorem sectionCoord_mfderiv_eventuallyEq [IsManifold I 1 M] [IsManifold J 1 N] {f : M → N}
    {x : M} (hf : ContMDiffAt I J 1 f x) (Y : Π x : M, TangentSpace I x) :
    sectionCoord ℝ (F := F) f (fun y ↦ mfderiv I J f y (Y y)) (f x) =ᶠ[𝓝 x]
      fun y ↦ mvfderiv I (extChartAt J (f x) ∘ f) y (Y y) := by
  have hsrc : ∀ᶠ y in 𝓝 x, f y ∈ (chartAt G (f x)).source :=
    hf.continuousAt.preimage_mem_nhds ((chartAt G (f x)).open_source.mem_nhds
      (mem_chart_source G (f x)))
  have hdiff : ∀ᶠ y in 𝓝 x, MDifferentiableAt I J f y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hf).mono fun y hy ↦
      hy.mdifferentiableAt one_ne_zero
  filter_upwards [hsrc, hdiff] with y hy hfy
  rw [sectionCoord_apply, TangentBundle.continuousLinearMapAt_trivializationAt hy,
    mvfderiv_apply_eq_mfderiv_apply, mfderiv_comp y (mdifferentiableAt_extChartAt hy) hfy]
  -- Both sides apply the composite derivative to `Y y`; they differ only in whether the middle
  -- space is written `TangentSpace J (f y)` or `F`, equal by definition, so `rw` cannot close
  -- the goal with `ContinuousLinearMap.comp_apply` and `rfl` unfolds it.
  rfl

end TauCeti.Manifold

namespace CovariantDerivative

open TauCeti TauCeti.Manifold

variable [FiniteDimensional ℝ F] [IsManifold J 2 N]
  (cov : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)) {f : M → N}

/-- **The pulled-back torsion identity.** For a torsion-free connection on `N`, a map `f` which is
`C²` at `x` and vector fields `X`, `Y` on `M` differentiable at `x`,
`∇_X (df Y) - ∇_Y (df X) = df [X, Y]` at `x`. -/
theorem alongMap_mfderiv_sub_alongMap_mfderiv [CompleteSpace E] [IsManifold I 2 M]
    (ht : cov.IsTorsionFree) {x : M} (hf : ContMDiffAt I J 2 f x) {X Y : Π x : M, TangentSpace I x}
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x) :
    cov.alongMap I f (fun y ↦ mfderiv I J f y (Y y)) x (X x) -
        cov.alongMap I f (fun y ↦ mfderiv I J f y (X y)) x (Y x) =
      mfderiv I J f x (mlieBracket I X Y x) := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have : IsManifold J (minSmoothness ℝ 2) N := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hf1 : ContMDiffAt I J 1 f x := hf.of_le (by norm_num)
  have hg : ContMDiffAt I 𝓘(ℝ, F) 2 (extChartAt J (f x) ∘ f) x :=
    (contMDiffAt_extChartAt (n := 2)).comp x hf
  have hbr := mvfderiv_mlieBracket hg (by simp) hX hY
  -- The Christoffel terms cancel by symmetry of the Christoffel form at the chart centre.
  have hΓ : christoffelForm (Module.finBasis ℝ F)
        (cov.isCovariantDerivativeOn (s := (trivializationAt F (TangentSpace J) (f x)).baseSet))
        (f x) (mfderiv I J f x (Y x)) (mfderiv I J f x (X x)) =
      christoffelForm (Module.finBasis ℝ F)
        (cov.isCovariantDerivativeOn (s := (trivializationAt F (TangentSpace J) (f x)).baseSet))
        (f x) (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) :=
    christoffelForm_comm ht _ (f x) (mem_extChartAt_source (f x)) _ _
  -- At `x`, the chart at `f x` has the identity as derivative, so `d(φ ∘ f)_x = df_x`.
  have hd (v : TangentSpace I x) :
      mvfderiv I (extChartAt J (f x) ∘ f) x v = mfderiv I J f x v := by
    rw [mvfderiv_apply_eq_mfderiv_apply,
      mfderiv_comp x (mdifferentiableAt_extChartAt (mem_chart_source G (f x)))
        (hf1.mdifferentiableAt one_ne_zero), ContinuousLinearMap.comp_apply,
      mfderiv_extChartAt_eq_id]
    -- `ContinuousLinearMap.id ℝ F` acts on `TangentSpace J (f x)`, which is `F` by definition;
    -- `ContinuousLinearMap.id_apply` does not match through this unfolding, so `rfl` closes it.
    rfl
  rw [alongMap_apply, alongMap_apply, (sectionCoord_mfderiv_eventuallyEq hf1 Y).mvfderiv_eq,
    (sectionCoord_mfderiv_eventuallyEq hf1 X).mvfderiv_eq, hΓ, add_sub_add_right_eq_sub,
    ← map_sub, ← hbr, hd]
  -- `symmL` at the chart centre is the identity on the model fibre `F = TangentSpace J (f x)`;
  -- `rw` cannot use the lemma since its argument `v : F` is typed as a tangent vector here.
  exact symmL_trivializationAt_self (I := J) (f x) _

end CovariantDerivative
