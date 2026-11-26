/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Regularity of covariant differentiation along maps

A fixed target trivialization computes the covariant derivative of a tangent field along a map.
It gives regularity up to the boundary of the source, since the frame expansion uses the full
manifold derivative and does not require a curve through the source point.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 2.
-/

public section

open Bundle FiberBundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N} {V : Π y : M, TangentSpace J (f y)} {x : M} {a : N}

section Coordinates

variable [IsManifold J 2 N]
  (cov : CovariantDerivative J F (TangentSpace J : N → Type _))

/-- In a fixed target tangent trivialization, the covariant derivative along a map is the
derivative of the coordinate reading plus the Christoffel term in that trivialization. -/
theorem alongMap_apply_of_mem_baseSet
    (hV : MDifferentiableAt I J.tangent (fun y ↦ TotalSpace.mk' F (f y) (V y)) x)
    (ha : f x ∈ (trivializationAt F (TangentSpace J) a).baseSet) (v : TangentSpace I x) :
    let e := trivializationAt F (TangentSpace J) a
    let g := sectionCoord ℝ (F := F) f V a
    cov.alongMap I f V x v = e.symmL ℝ (f x) (mvfderiv I g x v +
      christoffelMap (e := e) (Module.finBasis ℝ F)
        (cov.isCovariantDerivativeOn (s := e.baseSet)) (f x) (g x)
          (mvfderiv I (extChartAt J a ∘ f) x v)) := by
  classical
  dsimp only
  have hp := Bundle.contMDiffAt_proj (IB := J) (F := F) (n := 1) (TangentSpace J)
    (p := TotalSpace.mk' F (f x) (V x))
  have hf := (hp.mdifferentiableAt one_ne_zero).comp x hV
  let e := trivializationAt F (TangentSpace J) a
  let b := Module.finBasis ℝ F
  let g := sectionCoord ℝ (F := F) f V a
  let X := e.localFrame b
  let c i := (b.coord i).toContinuousLinearMap ∘ g
  let w := mfderiv I J f x v
  let u := e.continuousLinearMapAt ℝ (f x) w
  have hg : MDifferentiableAt I 𝓘(ℝ, F) g x :=
    mdifferentiableAt_sectionCoord f V hV ha
  have hX (i) : MDifferentiableAt J J.tangent (T% (X i)) (f x) :=
    ((e.contMDiffOn_localFrame_baseSet 1 b i).mdifferentiableOn one_ne_zero).mdifferentiableAt
      (e.open_baseSet.mem_nhds ha)
  have hc (i) : MDifferentiableAt I 𝓘(ℝ, ℝ) (c i) x :=
    mdifferentiableAt_repr_sectionCoord f V b hg i
  have hVeq : ∀ᶠ y in 𝓝 x, V y = ∑ i, c i y • X i (f y) :=
    eventually_eq_sum_repr_sectionCoord_smul_localFrame f V b hf.continuousAt ha
  have hread : mvfderiv I (extChartAt J a ∘ f) x v = u := by
    rw [mvfderiv_comp_apply x (mdifferentiableAt_extChartAt ha) hf]
    exact congrArg (fun L : TangentSpace J (f x) →L[ℝ] F ↦ L w)
      (TangentBundle.continuousLinearMapAt_trivializationAt (I := J) ha).symm
  have hsum : ∑ i, mvfderiv I (c i) x v • X i (f x) =
      e.symmL ℝ (f x) (mvfderiv I g x v) := by
    conv_rhs => rw [← b.sum_repr (mvfderiv I g x v), map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      dsimp only [c, X]
      rw [(b.coord i).toContinuousLinearMap.mvfderiv_comp_apply hg v, map_smul,
        symmL_basis_eq_localFrame b ha]
      simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, e]
  let hcov := cov.isCovariantDerivativeOn (s := e.baseSet)
  have hΓ : e.symmL ℝ (f x) (christoffelMap b hcov (f x) (g x) u) =
      ∑ i, c i x • cov (X i) (f x) w := by
    rw [symmL_christoffelMap_eq_sum b hcov ha, e.symmL_continuousLinearMapAt ha w]
    simp only [c, X, Function.comp_apply, LinearMap.coe_toContinuousLinearMap']
  have hcoord (i) := mdifferentiableAt_sectionCoord f (fun y ↦ X i (f y)) ((hX i).comp x hf)
    (mem_baseSet_trivializationAt F (TangentSpace J) (f x))
  rw [cov.alongMap_congr f V hVeq, cov.alongMap_fun_sum, sum_apply,
    hread, map_add, ← hsum, hΓ, ← Finset.sum_add_distrib]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [cov.alongMap_fun_smul f _ (c i) (hc i) (hcoord i), cov.alongMap_pullback f hf (hX i)]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, add_comm, w]
  · intro i _
    simpa only [sectionCoord_fun_smul] using (hc i).smul (hcoord i)

end Coordinates

variable [IsManifold I 1 M] [IsManifold J ∞ N] [T2Space N]
  (cov : CovariantDerivative J F (TangentSpace J : N → Type _))
  {n : ℕ∞ω} [ENat.LEInfty n] [ContMDiffCovariantDerivative cov n]

/-- Differentiating a tangent field along a map loses one derivative of the map and field.
This also holds at boundary and corner points of the source. -/
theorem contMDiffAt_alongMap_apply
    (hV : ContMDiffAt I J.tangent (n + 1) (fun y ↦ TotalSpace.mk' F (f y) (V y)) x)
    {X : Π y : M, TangentSpace I y} (hX : CMDiffAt n (T% X) x) :
    ContMDiffAt I J.tangent n
      (fun y ↦ TotalSpace.mk' F (f y) (cov.alongMap I f V y (X y))) x := by
  let e := trivializationAt F (TangentSpace J) (f x)
  have he : f x ∈ e.baseSet := mem_baseSet_trivializationAt F (TangentSpace J) (f x)
  have hN : IsManifold J (n + 1 + 1) N := .of_le (n := ∞) (by
    rw [show (∞ : ℕ∞ω) = ∞ + 1 + 1 by simp]
    gcongr
    exact ENat.LEInfty.out)
  have : ContMDiffVectorBundle (n + 1) F (TangentSpace J : N → Type _) J :=
    TangentBundle.contMDiffVectorBundle
  have hf : ContMDiffAt I J (n + 1) f x :=
    (Bundle.contMDiffAt_proj (IB := J) (F := F) (TangentSpace J)).comp x hV
  have : ContMDiffVectorBundle n F (TangentSpace J : N → Type _) J :=
    .of_le (show n ≤ n + 1 from le_self_add)
  have := cov.contMDiffCovariantDerivativeOn_of_isOpen (n := n) e.open_baseSet
  have hΓ := (contMDiffOn_christoffelMap (e := e) (n := n) (Module.finBasis ℝ F)
    (cov.isCovariantDerivativeOn (s := e.baseSet))).contMDiffAt (e.open_baseSet.mem_nhds he)
  have hfn := hf.of_le (show n ≤ n + 1 from le_self_add)
  have hw := ((contMDiffWithinAt_sectionCoord_iff f V
    (hf.contMDiffWithinAt (s := Set.univ)) he).2 hV.contMDiffWithinAt).contMDiffAt Filter.univ_mem
  have hφ : ContMDiffAt I 𝓘(ℝ, F) (n + 1) (extChartAt J (f x) ∘ f) x :=
    contMDiffAt_extChartAt.comp x hf
  have hdw := (hw.contMDiffAt_mvfderiv_apply (p := (X x : TangentBundle I M)) le_rfl).comp x hX
  have hdφ := (hφ.contMDiffAt_mvfderiv_apply (p := (X x : TangentBundle I M)) le_rfl).comp x hX
  refine ContMDiffWithinAt.contMDiffAt (s := Set.univ) ?_ Filter.univ_mem
  apply (contMDiffWithinAt_sectionCoord_iff f _ hfn.contMDiffWithinAt he).1
  refine (hdw.add (((hΓ.comp x hfn).clm_apply (hw.of_le le_self_add)).clm_apply hdφ))
    |>.congr_of_eventuallyEq ?_ |>.contMDiffWithinAt
  have hle : 1 ≤ n + 1 := le_add_self
  have hV₁ := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).1 (hV.of_le hle)
  filter_upwards [hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he), hV₁]
    with y hy hVy
  rw [sectionCoord_apply,
    cov.alongMap_apply_of_mem_baseSet (hVy.mdifferentiableAt one_ne_zero) hy,
    e.continuousLinearMapAt_symmL hy]
  rfl

end CovariantDerivative
