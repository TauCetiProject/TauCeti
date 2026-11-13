/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
/-!
# Covariant differentiation of tangent sections along a map

For a map `f : N → M`, a tangent field along `f` assigns a vector in `TangentSpace I (f x)`
to each `x : N`. Differentiating such fields along tangent directions of `N` is needed for
the ambient derivative along an immersion, hence for the second fundamental form and normal
connection in submanifold geometry. The source may also have several parameters.

`CovariantDerivative.alongMap` uses the preferred tangent trivialization at `f x` and the
Christoffel map of the given connection. Additivity and scalar Leibniz hold for differentiable
coordinate readings (and a differentiable scalar function for Leibniz). Restriction to curves
agrees with `alongCurveWithin` when the curve is differentiable within its parameter set and
the total-space section is differentiable at its image point. Pullback of an ambient field
agrees with its covariant derivative when the base map and ambient field are differentiable.

## References

* C. Bär, [*Differential Geometry*, Section 2.4, Proposition 2.4.4]
  (https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Lehrmaterialien/DiffGeo.pdf):
  covariant differentiation of vector fields along maps.
* M. P. do Carmo, *Riemannian Geometry*, Chapter 2: the specialization to curves.
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
variable (J) in
/-- Covariant differentiation of a tangent section along a map, as a continuous linear map on
source tangents. The coordinate formula uses `trivializationAt E (TangentSpace I) (f x)` and
`Module.finBasis 𝕜 E`: differentiate the coordinate reading of the section and add the Christoffel
term applied to the derivative of `extChartAt I (f x) ∘ f`, then invert the trivialization.

Each `mvfderiv` contributes its junk value `0` when its argument is not differentiable. Under the
stated `C¹` manifold assumptions, this file establishes chart independence on pulled-back fields
in `alongMap_pullback`; it does not establish chart independence for general sections. -/
def alongMap (x : N) : TangentSpace J x →L[𝕜] TangentSpace I (f x) :=
  (trivializationAt E (TangentSpace I) (f x)).symmL 𝕜 (f x) ∘L
    (mvfderiv J (sectionCoord 𝕜 (F := E) f V (f x)) x +
      (christoffelMap (Module.finBasis 𝕜 E)
        (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) (f x)).baseSet))
          (f x) (sectionCoord 𝕜 (F := E) f V (f x) x)).comp
        (mvfderiv J (extChartAt I (f x) ∘ f) x))
theorem alongMap_apply (x : N) (v : TangentSpace J x) :
    cov.alongMap J f V x v =
      (trivializationAt E (TangentSpace I) (f x)).symmL 𝕜 (f x)
        (mvfderiv J (sectionCoord 𝕜 (F := E) f V (f x)) x v +
          christoffelMap (Module.finBasis 𝕜 E)
            (cov.isCovariantDerivativeOn
              (s := (trivializationAt E (TangentSpace I) (f x)).baseSet))
            (f x) (sectionCoord 𝕜 (F := E) f V (f x) x)
              (mvfderiv J (extChartAt I (f x) ∘ f) x v)) := by
  unfold alongMap
  rfl
/-! ### Algebra laws in the section -/

/-- Covariant differentiation along a map is additive in sections with differentiable
coordinate readings. -/
theorem alongMap_add (W : ∀ x, TangentSpace I (f x)) {x : N}
    (hV : MDifferentiableAt J 𝓘(𝕜, E) (sectionCoord 𝕜 (F := E) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(𝕜, E) (sectionCoord 𝕜 (F := E) f W (f x)) x) :
    cov.alongMap J f (fun y => V y + W y) x =
      cov.alongMap J f V x + cov.alongMap J f W x := by
  ext v
  simp only [alongMap_apply, sectionCoord_add, mvfderiv_add hV hW, Pi.add_apply,
    map_add, add_apply]
  abel

/-- Covariant differentiation along a map commutes with negation, including junk values. -/
@[simp]
theorem alongMap_neg (x : N) :
    cov.alongMap J f (fun y ↦ -V y) x = -cov.alongMap J f V x := by
  ext v
  simp only [alongMap_apply, sectionCoord_neg, mvfderiv_neg, Pi.neg_apply,
    map_neg, neg_apply, ← neg_add]

/-- Covariant differentiation along a map commutes with subtraction of sections with
differentiable coordinate readings. -/
@[simp]
theorem alongMap_sub (W : ∀ x, TangentSpace I (f x)) {x : N}
    (hV : MDifferentiableAt J 𝓘(𝕜, E) (sectionCoord 𝕜 (F := E) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(𝕜, E) (sectionCoord 𝕜 (F := E) f W (f x)) x) :
    cov.alongMap J f (fun y ↦ V y - W y) x =
      cov.alongMap J f V x - cov.alongMap J f W x := by
  simp only [sub_eq_add_neg]
  rw [alongMap_add cov f V _ hV (by simpa only [sectionCoord_neg] using hW.neg)]
  rw [alongMap_neg]

/-- Covariant differentiation along a map obeys the Leibniz rule when the scalar function and
the coordinate reading of the section are differentiable at the point. -/
theorem alongMap_smul (g : N → 𝕜) {x : N} (hg : MDifferentiableAt J 𝓘(𝕜, 𝕜) g x)
    (hV : MDifferentiableAt J 𝓘(𝕜, E) (sectionCoord 𝕜 (F := E) f V (f x)) x) :
    cov.alongMap J f (fun y => g y • V y) x =
      g x • cov.alongMap J f V x + (mvfderiv J g x).smulRight (V x) := by
  ext v
  have hV₀ := symmL_sectionCoord (𝕜 := 𝕜) f V (f x) x
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (f x))
  simp only [alongMap_apply, sectionCoord_smul, mvfderiv_smul hg hV, Pi.smul_apply',
    map_smul, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, hV₀, smul_add]
  abel

/-- Covariant differentiation along a map commutes with multiplication by a constant scalar. -/
@[simp, to_fun (attr := simp)]
theorem alongMap_const_smul (c : 𝕜) (x : N) :
    cov.alongMap J f (c • V) x = c • cov.alongMap J f V x := by
  ext v
  have hcoord := sectionCoord_const_smul (F := E) f V c (f x)
  simp only [alongMap_apply, hcoord, TauCeti.mvfderiv_const_smul_field, Pi.smul_apply,
    map_smul, smul_apply]
  rw [← smul_add, map_smul]

/-- The zero section along a map has zero covariant derivative. -/
@[simp, to_fun (attr := simp)]
theorem alongMap_zero (x : N) :
    cov.alongMap J f (0 : ∀ y, TangentSpace I (f y)) x = 0 := by
  ext v
  simp only [alongMap_apply, sectionCoord_zero, mvfderiv_zero, Pi.zero_apply, map_zero,
    zero_apply, zero_add]

/-- Covariant differentiation along a map commutes with finite sums of sections with
differentiable coordinate readings. -/
@[simp]
theorem alongMap_sum {ι : Type*} (A : Finset ι)
    (W : ι → ∀ y, TangentSpace I (f y)) {x : N}
    (hW : ∀ i ∈ A, MDifferentiableAt J 𝓘(𝕜, E) (sectionCoord 𝕜 (F := E) f (W i) (f x)) x) :
    cov.alongMap J f (fun y ↦ ∑ i ∈ A, W i y) x =
      ∑ i ∈ A, cov.alongMap J f (W i) x := by
  ext v
  simp only [alongMap_apply, sectionCoord_sum, TauCeti.mvfderiv_fun_sum hW,
    sum_apply, map_sum, map_add, Finset.sum_add_distrib]

/-- Covariant differentiation along a map depends only on the germ of its section. -/
theorem alongMap_congr {W : ∀ y, TangentSpace I (f y)} {x : N}
    (h : ∀ᶠ y in 𝓝 x, V y = W y) :
    cov.alongMap J f V x = cov.alongMap J f W x := by
  have hc : sectionCoord 𝕜 (F := E) f V (f x) =ᶠ[𝓝 x] sectionCoord 𝕜 (F := E) f W (f x) :=
    h.mono fun y hy ↦ by rw [sectionCoord_apply, sectionCoord_apply, hy]
  ext v
  rw [alongMap_apply, alongMap_apply, hc.self_of_nhds]
  congr 2
  simp only [mvfderiv_apply_eq_mfderiv_apply, hc.mfderiv_eq]
  -- The target is a model vector space; its tangent-space cast acts as the identity.
  rfl

/-- Restricting a differentiable section along a differentiable map to a differentiable
parameter map composes the covariant derivative with the differential of that map. -/
theorem alongMap_comp
    {P Q R : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P] [TopologicalSpace Q]
    {K : ModelWithCorners 𝕜 P Q} [TopologicalSpace R] [ChartedSpace Q R]
    {g : R → N} {z : R} (hg : MDifferentiableAt K J g z)
    (hf : MDifferentiableAt J I f (g z))
    (hV : MDifferentiableAt J 𝓘(𝕜, E) (sectionCoord 𝕜 (F := E) f V (f (g z))) (g z)) :
    cov.alongMap K (f ∘ g) (fun p ↦ V (g p)) z =
      (cov.alongMap J f V (g z)).comp (mfderiv K J g z) := by
  have hbase :=
    (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (f (g z)))).comp (g z) hf
  ext v
  simp only [alongMap_apply, sectionCoord_comp, Function.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [← Function.comp_assoc, mvfderiv_comp_apply z hV hg,
    mvfderiv_comp_apply z hbase hg]

/-- Restriction to a curve differentiable within `s` agrees with covariant differentiation
along that curve, provided the section is differentiable into the tangent bundle at `γ t`.
No uniqueness assumption on derivatives within `s` is needed: both sides vanish otherwise. -/
theorem alongMap_curveVelocityWithin {γ : 𝕜 → N} {s : Set 𝕜} {t : 𝕜}
    (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) J γ s t)
    (hV : MDifferentiableAt J I.tangent
      (fun y => TotalSpace.mk' E (f y) (V y)) (γ t)) :
    cov.alongMap J f V (γ t) (curveVelocityWithin J γ s t) =
      cov.alongCurveWithin (f ∘ γ) (fun r => V (γ r)) s t := by
  by_cases hs : UniqueDiffWithinAt 𝕜 s t
  swap
  · rw [curveVelocityWithin_eq_zero_of_not_uniqueDiffWithinAt hs, map_zero,
      alongCurveWithin_of_not_uniqueDiffWithinAt cov _ _ hs]
  have hf := ((mdifferentiableAt_totalSpace I _).mp hV).1
  have hcoord := mdifferentiableAt_sectionCoord f V hV
    (mem_baseSet_trivializationAt E (TangentSpace I) (f (γ t)))
  have hbase : MDifferentiableAt J 𝓘(𝕜, E) (extChartAt I (f (γ t)) ∘ f) (γ t) :=
    (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (f (γ t)))).comp (γ t) hf
  have hdc := (hasDerivWithinAt_comp_curve hcoord
    (hasMFDerivWithinAt_curveVelocityWithin hγ)).derivWithin hs
  have hdb := (hasDerivWithinAt_comp_curve hbase
    (hasMFDerivWithinAt_curveVelocityWithin hγ)).derivWithin hs
  rw [alongMap_apply, alongCurveWithin_apply, alongCurveInChartWithin_apply]
  simp only [Function.comp_apply]
  rw [sectionCoord_comp, ← Function.comp_assoc, hdc, hdb]
  simp only [Function.comp_apply]
/-- Restriction to a differentiable curve agrees with covariant differentiation along that
curve when the section is differentiable into the tangent bundle at the image point. -/
theorem alongMap_curveVelocity {γ : 𝕜 → N} {t : 𝕜}
    (hγ : MDifferentiableAt 𝓘(𝕜, 𝕜) J γ t)
    (hV : MDifferentiableAt J I.tangent
      (fun y ↦ TotalSpace.mk' E (f y) (V y)) (γ t)) :
    cov.alongMap J f V (γ t) (curveVelocity J γ t) =
      cov.alongCurve (f ∘ γ) (fun r ↦ V (γ r)) t := by
  simpa only [curveVelocityWithin_univ, alongCurveWithin_univ] using
    alongMap_curveVelocityWithin cov f V (s := univ) hγ.mdifferentiableWithinAt hV

/-- For a base map differentiable at `x` and an ambient field differentiable into the tangent
bundle at `f x`, differentiation of the pulled-back field is the ambient covariant derivative
composed with `mfderiv J I f x`. -/
theorem alongMap_pullback {X : ∀ y, TangentSpace I y} {x : N}
    (hf : MDifferentiableAt J I f x)
    (hX : MDifferentiableAt I I.tangent (T% X) (f x)) :
    cov.alongMap J f (fun y => X (f y)) x =
      (cov X (f x)).comp (mfderiv J I f x) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply]
  let e := trivializationAt E (TangentSpace I) (f x)
  have ha : f x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (f x)
  have hg : MDifferentiableAt I 𝓘(𝕜, E) (sectionCoord 𝕜 (F := E) id X (f x)) (f x) :=
    mdifferentiableAt_sectionCoord id X hX ha
  have heq : ∀ᶠ y in 𝓝 (f x), X y = e.symm y (sectionCoord 𝕜 (F := E) id X (f x) y) := by
    filter_upwards [e.open_baseSet.mem_nhds ha] with y hy
    rw [← e.symmL_apply (R := 𝕜) hy]
    exact (symmL_sectionCoord id X (f x) y hy).symm
  have hY : MDifferentiableAt I I.tangent
      (T% (fun y => e.symm y (sectionCoord 𝕜 (F := E) id X (f x) y))) (f x) :=
    hX.congr_of_eventuallyEq (heq.mono fun y hy => congrArg (TotalSpace.mk' E y) hy.symm)
  have hcov := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hX hY univ_mem heq
  have hchart := mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (f x))
  have hc := covariantDerivative_symm_comp_apply_symm (Module.finBasis 𝕜 E)
    (cov.isCovariantDerivativeOn (s := e.baseSet)) ha hg
    (mfderiv J I f x v)
  simp only [e] at hc
  rw [TangentBundle.trivializationAt_symm_apply_self (I := I) (f x)
    (mfderiv J I f x v)] at hc
  have hread : mvfderiv I (extChartAt I (f x)) (f x) (mfderiv J I f x v) =
      mfderiv J I f x v := by
    rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_extChartAt_self]
    -- Model-space tangents and their canonical reading are the same carrier here.
    rfl
  have hcoords : sectionCoord 𝕜 (F := E) f (fun y ↦ X (f y)) (f x) =
      sectionCoord 𝕜 (F := E) id X (f x) ∘ f := by
    simpa only [Function.id_comp] using
      (sectionCoord_comp (F := E) id X f (f x))
  rw [alongMap_apply, hcoords, mvfderiv_comp_apply x hg hf,
    mvfderiv_comp_apply x hchart hf, hread, Function.comp_apply,
    symmL_trivializationAt_self, hcov, hc]
  exact (TangentBundle.trivializationAt_symm_apply_self (I := I) (f x) _).symm
end CovariantDerivative
