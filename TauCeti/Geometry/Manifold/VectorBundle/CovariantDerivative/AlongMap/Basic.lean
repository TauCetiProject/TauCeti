/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
/-!
# Covariant differentiation of tangent sections along a map

The native connection defines a continuous linear map on the source tangent space by reading
an actual section along a map in the target tangent trivialization. The coordinate derivative
and native Christoffel term agree with the existing covariant derivative along every genuine
curve, including one-sided curves. For a pulled-back ambient field the result is exactly its
native covariant derivative in the image tangent direction. In the section variable it is
additive, obeys the Leibniz rule for scalar functions, and vanishes on the zero section.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 2.
-/

public section
open Set Filter Bundle
open scoped Manifold Topology
noncomputable section
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
/-! ### Algebra laws in the section -/

/-- Covariant differentiation along a map is additive in sections with differentiable
coordinate readings. -/
theorem alongMap_add (W : ∀ x, TangentSpace I (f x)) {x : N}
    (hV : MDifferentiableAt J 𝓘(𝕜, E) (sectionCoordAlongMap f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(𝕜, E) (sectionCoordAlongMap f W (f x)) x) :
    cov.alongMap (J := J) f (fun y => V y + W y) x =
      cov.alongMap f V x + cov.alongMap f W x := by
  ext v
  simp only [alongMap_apply, sectionCoordAlongMap_add, mvfderiv_add hV hW, Pi.add_apply,
    map_add, add_apply]
  abel

/-- Covariant differentiation along a map obeys the Leibniz rule for multiplication by a
differentiable scalar function. -/
theorem alongMap_smul (g : N → 𝕜) {x : N} (hg : MDifferentiableAt J 𝓘(𝕜, 𝕜) g x)
    (hV : MDifferentiableAt J 𝓘(𝕜, E) (sectionCoordAlongMap f V (f x)) x) :
    cov.alongMap (J := J) f (fun y => g y • V y) x =
      g x • cov.alongMap f V x + (mvfderiv J g x).smulRight (V x) := by
  ext v
  have hV₀ : (trivializationAt E (TangentSpace I) (f x)).symmL 𝕜 (f x)
      (sectionCoordAlongMap f V (f x) x) = V x := by
    rw [sectionCoordAlongMap_apply]
    exact (trivializationAt E (TangentSpace I) (f x)).symmL_continuousLinearMapAt (R := 𝕜)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (f x)) (V x)
  simp only [alongMap_apply, sectionCoordAlongMap_smul, mvfderiv_smul hg hV, Pi.smul_apply',
    map_smul, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, hV₀, smul_add]
  abel

/-- Covariant differentiation along a map commutes with multiplication by a constant scalar. -/
theorem alongMap_const_smul (c : 𝕜) (x : N) :
    cov.alongMap (J := J) f (fun y => c • V y) x = c • cov.alongMap f V x := by
  ext v
  have hcoord : sectionCoordAlongMap f (fun y => c • V y) (f x) =
      c • sectionCoordAlongMap f V (f x) :=
    sectionCoordAlongMap_smul f (fun _ => c) V (f x)
  simp only [alongMap_apply, hcoord, TauCeti.mvfderiv_const_smul_field, Pi.smul_apply,
    map_smul, smul_apply]
  rw [← smul_add, map_smul]

/-- The zero section along a map has zero covariant derivative. -/
@[simp]
theorem alongMap_zero (x : N) :
    cov.alongMap (J := J) f (fun y => (0 : TangentSpace I (f y))) x = 0 := by
  ext v
  simp only [alongMap_apply, sectionCoordAlongMap_zero, mvfderiv_zero, Pi.zero_apply, map_zero,
    zero_apply, zero_add]

/-- Along a genuine curve the map derivative is the existing native covariant derivative. -/
theorem alongMap_curveVelocityWithin {γ : 𝕜 → N} {s : Set 𝕜} {t : 𝕜}
    (hs : UniqueDiffWithinAt 𝕜 s t)
    (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) J γ s t)
    (hf : MDifferentiableAt J I f (γ t))
    (hV : MDifferentiableAt J I.tangent
      (fun y => TotalSpace.mk' E (f y) (V y)) (γ t)) :
    cov.alongMap (J := J) f V (γ t) (curveVelocityWithin J γ s t) =
      cov.alongCurveWithin (f ∘ γ) (fun r => V (γ r)) s t := by
  have hcoord := mdifferentiableAt_sectionCoordAlongMap hV
    (mem_baseSet_trivializationAt E (TangentSpace I) (f (γ t)))
  have hbase : MDifferentiableAt J 𝓘(𝕜, E) (extChartAt I (f (γ t)) ∘ f) (γ t) :=
    (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (f (γ t)))).comp (γ t) hf
  have hdc := (hasDerivWithinAt_comp_curve hcoord
    (hasMFDerivWithinAt_curveVelocityWithin hγ)).derivWithin hs
  have hdb := (hasDerivWithinAt_comp_curve hbase
    (hasMFDerivWithinAt_curveVelocityWithin hγ)).derivWithin hs
  have heq : sectionCoord (F := E) (f ∘ γ) (fun r => V (γ r)) (f (γ t)) =
      sectionCoordAlongMap f V (f (γ t)) ∘ γ := by
    funext r
    simp only [sectionCoord_apply, Function.comp_apply, sectionCoordAlongMap_apply]
  rw [alongMap_apply, alongCurveWithin_apply, alongCurveInChartWithin_apply]
  simp only [Function.comp_apply]
  rw [heq, ← Function.comp_assoc, hdc, hdb]
  simp only [Function.comp_apply]
/-- Pulling back an ambient field differentiates it in the actual image tangent direction. -/
theorem alongMap_pullback {X : ∀ y, TangentSpace I y} {x : N}
    (hf : MDifferentiableAt J I f x)
    (hX : MDifferentiableAt I I.tangent (T% X) (f x)) (v : TangentSpace J x) :
    cov.alongMap (J := J) f (fun y => X (f y)) x v =
      cov X (f x) (mfderiv J I f x v) := by
  let e := trivializationAt E (TangentSpace I) (f x)
  have ha : f x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (f x)
  have hg : MDifferentiableAt I 𝓘(𝕜, E) (sectionCoordAlongMap id X (f x)) (f x) :=
    mdifferentiableAt_sectionCoordAlongMap hX ha
  have heq : ∀ᶠ y in 𝓝 (f x), X y = e.symm y (sectionCoordAlongMap id X (f x) y) := by
    filter_upwards [e.open_baseSet.mem_nhds ha] with y hy
    rw [sectionCoordAlongMap_apply, id_eq, ← e.symmL_apply (R := 𝕜) hy]
    exact (e.symmL_continuousLinearMapAt (R := 𝕜) hy (X y)).symm
  have hY : MDifferentiableAt I I.tangent
      (T% (fun y => e.symm y (sectionCoordAlongMap id X (f x) y))) (f x) :=
    hX.congr_of_eventuallyEq (heq.mono fun y hy => congrArg (TotalSpace.mk' E y) hy.symm)
  have hcov := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hX hY univ_mem heq
  have hchart := mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (f x))
  have hcoords : sectionCoordAlongMap f (fun y => X (f y)) (f x) =
      sectionCoordAlongMap id X (f x) ∘ f := by
    funext y
    simp only [sectionCoordAlongMap_apply, Function.comp_apply, id_eq]
  have hu : e.symm (f x) (e.continuousLinearMapAt 𝕜 (f x) (mfderiv J I f x v)) =
      mfderiv J I f x v := by
    rw [← e.symmL_apply (R := 𝕜) ha]
    exact e.symmL_continuousLinearMapAt (R := 𝕜) ha _
  have hc := covariantDerivative_symm_comp_apply_symm (Module.finBasis 𝕜 E)
    (cov.isCovariantDerivativeOn (s := e.baseSet)) ha hg
    (e.continuousLinearMapAt 𝕜 (f x) (mfderiv J I f x v))
  rw [hu] at hc
  have hread : mvfderiv I (extChartAt I (f x)) (f x) = e.continuousLinearMapAt 𝕜 (f x) :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
      (mem_chart_source H (f x))).symm
  rw [alongMap_apply, hcoords, mvfderiv_comp_apply x hg hf, mvfderiv_comp_apply x hchart hf,
    hread, Function.comp_apply, e.symmL_apply (R := 𝕜) ha, hcov, hc]
end CovariantDerivative
