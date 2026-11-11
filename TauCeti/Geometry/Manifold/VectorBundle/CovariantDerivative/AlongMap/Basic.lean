/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
/-!
# Covariant differentiation of tangent sections along a map

The native connection defines a continuous linear map on the source tangent space by reading
an actual section along a map in the target tangent trivialization. The coordinate derivative
and native Christoffel term agree with the existing covariant derivative along every genuine
curve, including one-sided curves. For a pulled-back ambient field the result is exactly its
native covariant derivative in the image tangent direction.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 2.
-/

public section
open Set Filter Bundle
open scoped Manifold Topology
noncomputable section
namespace TauCeti.Manifold
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
/-- Tangent coordinates of a section along an arbitrary map, in a fixed native trivialization. -/
def sectionCoordAlongMap (f : N → M) (V : ∀ x, TangentSpace I (f x)) (a : M) (x : N) : E :=
  (trivializationAt E (TangentSpace I) a).continuousLinearMapAt 𝕜 (f x) (V x)
theorem sectionCoordAlongMap_apply (f : N → M) (V : ∀ x, TangentSpace I (f x))
    (a : M) (x : N) :
    sectionCoordAlongMap f V a x =
      (trivializationAt E (TangentSpace I) a).continuousLinearMapAt 𝕜 (f x) (V x) := by
  unfold sectionCoordAlongMap
  rfl
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} [TopologicalSpace N] [ChartedSpace G N]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
theorem mdifferentiableAt_sectionCoordAlongMap
    {f : N → M} {V : ∀ x, TangentSpace I (f x)} {a : M} {x : N}
    (hV : MDifferentiableAt J I.tangent
      (fun y => TotalSpace.mk' E (f y) (V y)) x)
    (ha : f x ∈ (trivializationAt E (TangentSpace I) a).baseSet) :
    MDifferentiableAt J 𝓘(𝕜, E) (sectionCoordAlongMap f V a) x := by
  let e := trivializationAt E (TangentSpace I) a
  have h := hV.mdifferentiableWithinAt (s := univ)
  rw [e.mdifferentiableWithinAt_totalSpace_iff I] at h
  · obtain ⟨hf, hc⟩ := h
    have hbase : ∀ᶠ y in 𝓝 x, f y ∈ e.baseSet :=
      hf.continuousWithinAt.continuousAt univ_mem |>.preimage_mem_nhds
        (e.open_baseSet.mem_nhds ha)
    apply hc.mdifferentiableAt univ_mem |>.congr_of_eventuallyEq
    filter_upwards [hbase] with y hy
    rw [sectionCoordAlongMap_apply]
    exact e.continuousLinearMapAt_apply_of_mem 𝕜 hy (V y)
  · exact e.coe_mem_source.mpr ha
end TauCeti.Manifold
namespace CovariantDerivative
open TauCeti.Manifold
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} [TopologicalSpace N] [ChartedSpace G N]
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  (f : N → M) (V : ∀ x, TangentSpace I (f x))
/-- Covariant differentiation of a section along a map, as a continuous linear map on tangents. -/
def alongMap (x : N) : TangentSpace J x →L[𝕜] TangentSpace I (f x) :=
  (trivializationAt E (TangentSpace I) (f x)).symmL 𝕜 (f x) ∘L
    (mvfderiv J (sectionCoordAlongMap f V (f x)) x +
      (christoffelMap (Module.finBasis 𝕜 E)
        (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) (f x)).baseSet))
          (f x) (sectionCoordAlongMap f V (f x) x)).comp
        (mvfderiv J (extChartAt I (f x) ∘ f) x))
theorem alongMap_apply (x : N) (v : TangentSpace J x) :
    cov.alongMap (J := J) f V x v =
      (trivializationAt E (TangentSpace I) (f x)).symmL 𝕜 (f x)
        (mvfderiv J (sectionCoordAlongMap f V (f x)) x v +
          christoffelMap (Module.finBasis 𝕜 E)
            (cov.isCovariantDerivativeOn
              (s := (trivializationAt E (TangentSpace I) (f x)).baseSet))
            (f x) (sectionCoordAlongMap f V (f x) x)
              (mvfderiv J (extChartAt I (f x) ∘ f) x v)) := by
  unfold alongMap
  rfl
/-- Along a genuine curve the map derivative is the existing native covariant derivative. -/
theorem alongMap_curveVelocityWithin {γ : 𝕜 → N} {s : Set 𝕜} {t : 𝕜}
    (hs : UniqueDiffWithinAt 𝕜 s t)
    (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) J γ s t)
    (hf : MDifferentiableAt J I f (γ t))
    (hV : MDifferentiableAt J I.tangent
      (fun y => TotalSpace.mk' E (f y) (V y)) (γ t)) :
    cov.alongMap (J := J) f V (γ t) (curveVelocityWithin J γ s t) =
      cov.alongCurveWithin (f ∘ γ) (fun r => V (γ r)) s t := by
  let a := f (γ t)
  have hcoord := mdifferentiableAt_sectionCoordAlongMap hV
    (mem_baseSet_trivializationAt E (TangentSpace I) a)
  have hbase : MDifferentiableAt J 𝓘(𝕜, E) (extChartAt I a ∘ f) (γ t) :=
    (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H a)).comp (γ t) hf
  have hdc := (hasDerivWithinAt_comp_curve hcoord
    (hasMFDerivWithinAt_curveVelocityWithin hγ)).derivWithin hs
  have hdb := (hasDerivWithinAt_comp_curve hbase
    (hasMFDerivWithinAt_curveVelocityWithin hγ)).derivWithin hs
  have heq : sectionCoord (f ∘ γ) (fun r => V (γ r)) a =
      sectionCoordAlongMap f V a ∘ γ := by
    funext r
    simp only [sectionCoord_apply, Function.comp_apply, sectionCoordAlongMap_apply]
  rw [alongMap_apply, alongCurveWithin_apply, alongCurveInChartWithin_apply]
  change _ = (trivializationAt E (TangentSpace I) a).symmL 𝕜 a
    (derivWithin (sectionCoord (f ∘ γ) (fun r => V (γ r)) a) s t +
      christoffelMap (Module.finBasis 𝕜 E)
        (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) a).baseSet))
        a (sectionCoord (f ∘ γ) (fun r => V (γ r)) a t)
          (derivWithin ((extChartAt I a ∘ f) ∘ γ) s t))
  rw [heq, hdc, hdb]
  rfl
/-- Pulling back an ambient field differentiates it in the actual image tangent direction. -/
theorem alongMap_pullback {X : ∀ y, TangentSpace I y} {x : N}
    (hf : MDifferentiableAt J I f x)
    (hX : MDifferentiableAt I I.tangent (T% X) (f x)) (v : TangentSpace J x) :
    cov.alongMap (J := J) f (fun y => X (f y)) x v =
      cov X (f x) (mfderiv J I f x v) := by
  let a := f x
  let e := trivializationAt E (TangentSpace I) a
  let g := sectionCoordAlongMap id X a
  have ha : a ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) a
  have hg : MDifferentiableAt I 𝓘(𝕜, E) g a :=
    mdifferentiableAt_sectionCoordAlongMap hX ha
  have heq : ∀ᶠ y in 𝓝 a, X y = e.symm y (g y) := by
    filter_upwards [e.open_baseSet.mem_nhds ha] with y hy
    exact (e.symmL_continuousLinearMapAt (R := 𝕜) hy (X y)).symm.trans
      (e.symmL_apply (R := 𝕜) hy (g y))
  have hY : MDifferentiableAt I I.tangent (T% (fun y => e.symm y (g y))) a :=
    hX.congr_of_eventuallyEq (heq.mono fun y hy => congrArg (TotalSpace.mk' E y) hy.symm)
  have hcov := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hX hY univ_mem heq
  have hchart := mdifferentiableAt_extChartAt (I := I) (mem_chart_source H a)
  have hcoords : sectionCoordAlongMap f (fun y => X (f y)) a = g ∘ f := by
    funext y
    change sectionCoordAlongMap f (fun y => X (f y)) a y =
      sectionCoordAlongMap id X a (f y)
    simp only [sectionCoordAlongMap_apply, id_eq]
  let w := mfderiv J I f x v
  let u := e.continuousLinearMapAt 𝕜 a w
  have hu : e.symm a u = w := by
    rw [← e.symmL_apply (R := 𝕜) ha]
    exact e.symmL_continuousLinearMapAt (R := 𝕜) ha w
  have hc := covariantDerivative_symm_comp_apply_symm (Module.finBasis 𝕜 E)
    (cov.isCovariantDerivativeOn (s := e.baseSet)) ha hg u
  rw [hu] at hc
  rw [alongMap_apply, hcoords, mvfderiv_comp_apply x hg hf,
    mvfderiv_comp_apply x hchart hf]
  change e.symmL 𝕜 a (mvfderiv I g a w +
    christoffelMap (Module.finBasis 𝕜 E)
      (cov.isCovariantDerivativeOn (s := e.baseSet)) a (g a)
        (mvfderiv I (extChartAt I a) a w)) = _
  have hread : mvfderiv I (extChartAt I a) a = e.continuousLinearMapAt 𝕜 a :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
      (mem_chart_source H a)).symm
  rw [hread]
  rw [e.symmL_apply (R := 𝕜) ha, hcov, hc]
end CovariantDerivative
