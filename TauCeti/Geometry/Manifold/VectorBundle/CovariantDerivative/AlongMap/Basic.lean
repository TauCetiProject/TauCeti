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
# Covariant differentiation of vector-bundle sections along a map

For a map `f : N → M`, a section of a bundle `B` along `f` assigns a vector in `B (f x)`
to each `x : N`. Differentiating such fields along tangent directions of `N` is needed for
the ambient derivative along an immersion, hence for the second fundamental form and normal
connection in submanifold geometry. The source may also have several parameters.

`CovariantDerivative.alongMap` uses the preferred bundle trivialization at `f x` and the
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
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀] [FiniteDimensional 𝕜 F₀]
  {B : M → Type*} [TopologicalSpace (TotalSpace F₀ B)]
  [∀ x, AddCommGroup (B x)] [∀ x, Module 𝕜 (B x)] [∀ x, TopologicalSpace (B x)]
  [∀ x, IsTopologicalAddGroup (B x)] [∀ x, ContinuousSMul 𝕜 (B x)]
  [FiberBundle F₀ B] [VectorBundle 𝕜 F₀ B] [ContMDiffVectorBundle 1 F₀ B I]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} [TopologicalSpace N] [ChartedSpace G N]
variable (cov : CovariantDerivative I F₀ B) (f : N → M) (V : ∀ x, B (f x))
variable (J) in
/-- Covariant differentiation of a section along a map, as a continuous linear map on source
tangents. In the preferred bundle trivialization at `f x`, differentiate the coordinate reading
and reconstruct it in the fibre; add the Christoffel form applied to `V x` and the derivative
of `f`. The frame uses `Module.finBasis 𝕜 F₀`.

The coordinate derivative and `mfderiv` each contribute zero when their argument is not
differentiable. The pullback comparison `alongMap_pullback` establishes agreement with the
ambient connection on differentiable pulled-back sections. -/
def alongMap (x : N) : TangentSpace J x →L[𝕜] B (f x) :=
  (trivializationAt F₀ B (f x)).symmL 𝕜 (f x) ∘L
      mvfderiv J (sectionCoord 𝕜 (F := F₀) f V (f x)) x +
    (christoffelForm (Module.finBasis 𝕜 F₀)
      (cov.isCovariantDerivativeOn (s := (trivializationAt F₀ B (f x)).baseSet))
        (f x) (V x)).comp (mfderiv J I f x)

/-- The coordinate derivative and Christoffel terms of covariant differentiation along a map. -/
theorem alongMap_apply (x : N) (v : TangentSpace J x) :
    cov.alongMap J f V x v =
      (trivializationAt F₀ B (f x)).symmL 𝕜 (f x)
        (mvfderiv J (sectionCoord 𝕜 (F := F₀) f V (f x)) x v) +
      christoffelForm (Module.finBasis 𝕜 F₀)
        (cov.isCovariantDerivativeOn (s := (trivializationAt F₀ B (f x)).baseSet))
        (f x) (V x) (mfderiv J I f x v) :=
  (rfl)

/-! ### Algebra laws in the section -/

/-- Covariant differentiation along a map is additive in sections with differentiable
coordinate readings. -/
@[to_fun alongMap_fun_add]
theorem alongMap_add (W : ∀ x, B (f x)) {x : N}
    (hV : MDifferentiableAt J 𝓘(𝕜, F₀) (sectionCoord 𝕜 (F := F₀) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(𝕜, F₀) (sectionCoord 𝕜 (F := F₀) f W (f x)) x) :
    cov.alongMap J f (V + W) x =
      cov.alongMap J f V x + cov.alongMap J f W x := by
  ext v
  simp only [alongMap_apply, sectionCoord_add, mvfderiv_add hV hW, Pi.add_apply,
    map_add, add_apply]
  abel

/-- Covariant differentiation along a map commutes with negation, including junk values. -/
@[simp, to_fun (attr := simp) alongMap_fun_neg]
theorem alongMap_neg (x : N) :
    cov.alongMap J f (-V) x = -cov.alongMap J f V x := by
  ext v
  simp only [alongMap_apply, sectionCoord_neg, mvfderiv_neg, Pi.neg_apply,
    map_neg, neg_apply, neg_add]

/-- Covariant differentiation along a map commutes with subtraction of sections with
differentiable coordinate readings. -/
@[to_fun alongMap_fun_sub]
theorem alongMap_sub (W : ∀ x, B (f x)) {x : N}
    (hV : MDifferentiableAt J 𝓘(𝕜, F₀) (sectionCoord 𝕜 (F := F₀) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(𝕜, F₀) (sectionCoord 𝕜 (F := F₀) f W (f x)) x) :
    cov.alongMap J f (V - W) x =
      cov.alongMap J f V x - cov.alongMap J f W x := by
  simp only [sub_eq_add_neg]
  rw [alongMap_add cov f V _ hV (by simpa only [sectionCoord_neg] using hW.neg)]
  rw [alongMap_neg]

/-- Covariant differentiation along a map obeys the Leibniz rule when the scalar function and
the coordinate reading of the section are differentiable at the point. -/
@[to_fun alongMap_fun_smul]
theorem alongMap_smul (g : N → 𝕜) {x : N} (hg : MDifferentiableAt J 𝓘(𝕜, 𝕜) g x)
    (hV : MDifferentiableAt J 𝓘(𝕜, F₀) (sectionCoord 𝕜 (F := F₀) f V (f x)) x) :
    cov.alongMap J f (g • V) x =
      g x • cov.alongMap J f V x + (mvfderiv J g x).smulRight (V x) := by
  ext v
  have hV₀ := symmL_sectionCoord_self (𝕜 := 𝕜) (F := F₀) f V x
  simp only [alongMap_apply, sectionCoord_smul, mvfderiv_smul hg hV, Pi.smul_apply',
    map_smul, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, hV₀,
    smul_add]
  abel

/-- Covariant differentiation along a map commutes with multiplication by a constant scalar. -/
@[simp, to_fun (attr := simp) alongMap_fun_const_smul]
theorem alongMap_const_smul (c : 𝕜) (x : N) :
    cov.alongMap J f (c • V) x = c • cov.alongMap J f V x := by
  ext v
  simp only [alongMap_apply, sectionCoord_const_smul, TauCeti.mvfderiv_const_smul_field,
    Pi.smul_apply, map_smul, smul_apply, smul_add]

/-- The zero section along a map has zero covariant derivative. -/
@[simp, to_fun (attr := simp) alongMap_fun_zero]
theorem alongMap_zero (x : N) :
    cov.alongMap J f (0 : ∀ y, B (f y)) x = 0 := by
  ext v
  simp only [alongMap_apply, sectionCoord_zero, mvfderiv_zero, Pi.zero_apply, map_zero,
    zero_apply, zero_add]

/-- Covariant differentiation along a map commutes with finite sums of sections with
differentiable coordinate readings. -/
@[to_fun alongMap_fun_sum]
theorem alongMap_sum {ι : Type*} (A : Finset ι)
    (W : ι → ∀ y, B (f y)) {x : N}
    (hW : ∀ i ∈ A, MDifferentiableAt J 𝓘(𝕜, F₀) (sectionCoord 𝕜 (F := F₀) f (W i) (f x)) x) :
    cov.alongMap J f (∑ i ∈ A, W i) x =
      ∑ i ∈ A, cov.alongMap J f (W i) x := by
  ext v
  simp only [alongMap_apply, sectionCoord_sum]
  rw [Finset.sum_fn, TauCeti.mvfderiv_fun_sum hW]
  simp only [Finset.sum_apply, sum_apply, map_sum, alongMap_apply, Finset.sum_add_distrib]

/-- Covariant differentiation along a map depends only on the germ of its section. -/
theorem alongMap_congr {W : ∀ y, B (f y)} {x : N}
    (h : ∀ᶠ y in 𝓝 x, V y = W y) :
    cov.alongMap J f V x = cov.alongMap J f W x := by
  have hc : sectionCoord 𝕜 (F := F₀) f V (f x) =ᶠ[𝓝 x] sectionCoord 𝕜 (F := F₀) f W (f x) :=
    h.mono fun y hy ↦ by rw [sectionCoord_apply, sectionCoord_apply, hy]
  ext v
  rw [alongMap_apply, alongMap_apply, hc.mvfderiv_eq, h.self_of_nhds]

/-- Restricting a differentiable section along a differentiable map to a differentiable
parameter map composes the covariant derivative with the differential of that map. -/
theorem alongMap_comp
    {P Q R : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P] [TopologicalSpace Q]
    {K : ModelWithCorners 𝕜 P Q} [TopologicalSpace R] [ChartedSpace Q R]
    {g : R → N} {z : R} (hg : MDifferentiableAt K J g z)
    (hf : MDifferentiableAt J I f (g z))
    (hV : MDifferentiableAt J 𝓘(𝕜, F₀) (sectionCoord 𝕜 (F := F₀) f V (f (g z))) (g z)) :
    cov.alongMap K (f ∘ g) (fun p ↦ V (g p)) z =
      (cov.alongMap J f V (g z)).comp (mfderiv K J g z) := by
  ext v
  simp only [alongMap_apply, sectionCoord_comp, Function.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [mvfderiv_comp_apply z hV hg, mfderiv_comp z hf hg,
    ContinuousLinearMap.comp_apply]

/-- Differentiation along the identity map agrees with the ambient connection on a section
differentiable into the total space at the point. -/
theorem alongMap_id {X : ∀ y, B y} {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(𝕜, F₀)) (T% X) x) :
    cov.alongMap I id X x = cov X x := by
  let e := trivializationAt F₀ B x
  let b := Module.finBasis 𝕜 F₀
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F₀ B x
  have hg := mdifferentiableAt_sectionCoord (F := F₀) id X hX hx
  have hcoeff (i) : (fun y ↦ e.localFrameCoeff I b i y (X y)) =ᶠ[𝓝 x]
      fun y ↦ b.coord i (sectionCoord 𝕜 (F := F₀) id X x y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [e.localFrameCoeff_eq_coeff (b := b) hy, sectionCoord_apply]
    dsimp only [e, id_eq]
    rw [(trivializationAt F₀ B x).continuousLinearMapAt_apply_of_mem 𝕜 hy,
      Module.Basis.coord_apply]
  rw [covariantDerivative_eq_add_christoffelForm b
    (cov.isCovariantDerivativeOn (s := e.baseSet)) hx hX,
    frameCovariantDerivative_eq_symmL_comp b hg.hasMFDerivAt hcoeff hx]
  dsimp only [e, b]
  ext v
  rw [alongMap_apply, mfderiv_id]
  simp only [add_apply, ContinuousLinearMap.id_apply, mvfderiv_apply_eq_mfderiv_apply]
  -- The codomain is the model fibre, whose tangent identification is the identity.
  rfl

/-- For a base map differentiable at `x` and an ambient section differentiable into the total
space at `f x`, differentiation of the pulled-back section is the ambient covariant derivative
composed with `mfderiv J I f x`. -/
theorem alongMap_pullback {X : ∀ y, B y} {x : N}
    (hf : MDifferentiableAt J I f x)
    (hX : MDifferentiableAt I (I.prod 𝓘(𝕜, F₀)) (T% X) (f x)) :
    cov.alongMap J f (fun y => X (f y)) x =
      (cov X (f x)).comp (mfderiv J I f x) := by
  have hg := mdifferentiableAt_sectionCoord (F := F₀) id X hX
    (mem_baseSet_trivializationAt F₀ B (f x))
  simpa only [Function.id_comp, alongMap_id cov hX] using
    alongMap_comp cov id X hf mdifferentiableAt_id hg

section TangentBundle
variable [FiniteDimensional 𝕜 E] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  (tangentCov : CovariantDerivative I E (TangentSpace I : M → Type _))
  (tangentV : ∀ x, TangentSpace I (f x))

/-- Restriction to a curve differentiable within `s` agrees with covariant differentiation
along that curve, provided the section is differentiable into the tangent bundle at `γ t`.
No uniqueness assumption on derivatives within `s` is needed: both sides vanish otherwise. -/
theorem alongMap_curveVelocityWithin {γ : 𝕜 → N} {s : Set 𝕜} {t : 𝕜}
    (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) J γ s t)
    (hV : MDifferentiableAt J I.tangent
      (fun y => TotalSpace.mk' E (f y) (tangentV y)) (γ t)) :
    tangentCov.alongMap J f tangentV (γ t) (curveVelocityWithin J γ s t) =
      tangentCov.alongCurveWithin (f ∘ γ) (fun r => tangentV (γ r)) s t := by
  by_cases hs : UniqueDiffWithinAt 𝕜 s t
  swap
  · rw [curveVelocityWithin_eq_zero_of_not_uniqueDiffWithinAt hs, map_zero,
      alongCurveWithin_of_not_uniqueDiffWithinAt tangentCov _ _ hs]
  have hf := ((mdifferentiableAt_totalSpace I _).mp hV).1
  have hcoord := mdifferentiableAt_sectionCoord f tangentV hV
    (mem_baseSet_trivializationAt E (TangentSpace I) (f (γ t)))
  have hbase : MDifferentiableAt J 𝓘(𝕜, E) (extChartAt I (f (γ t)) ∘ f) (γ t) :=
    (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (f (γ t)))).comp (γ t) hf
  have hdc := (hasDerivWithinAt_comp_curve hcoord
    (hasMFDerivWithinAt_curveVelocityWithin hγ)).derivWithin hs
  have hdb := (hasDerivWithinAt_comp_curve hbase
    (hasMFDerivWithinAt_curveVelocityWithin hγ)).derivWithin hs
  have hbaseDeriv :
      mvfderiv J (extChartAt I (f (γ t)) ∘ f) (γ t) (curveVelocityWithin J γ s t) =
        mfderiv J I f (γ t) (curveVelocityWithin J γ s t) := by
    rw [mvfderiv_comp_apply (γ t)
      (mdifferentiableAt_extChartAt (mem_chart_source H (f (γ t)))) hf]
    exact TauCeti.mvfderiv_apply_of_eventuallyEq_extChartAt EventuallyEq.rfl _
  rw [alongMap_apply, alongCurveWithin_apply, alongCurveInChartWithin_apply]
  simp only [Function.comp_apply]
  rw [sectionCoord_comp, ← Function.comp_assoc, hdc, hdb]
  dsimp only [Function.comp_apply]
  rw [christoffelMap_apply, symmL_sectionCoord_self, map_add,
    (trivializationAt E (TangentSpace I) (f (γ t))).symmL_continuousLinearMapAt
      (mem_baseSet_trivializationAt E (TangentSpace I) (f (γ t)))]
  congr 2
  rw [symmL_trivializationAt_self, hbaseDeriv]
/-- Restriction to a differentiable curve agrees with covariant differentiation along that
curve when the section is differentiable into the tangent bundle at the image point. -/
theorem alongMap_curveVelocity {γ : 𝕜 → N} {t : 𝕜}
    (hγ : MDifferentiableAt 𝓘(𝕜, 𝕜) J γ t)
    (hV : MDifferentiableAt J I.tangent
      (fun y ↦ TotalSpace.mk' E (f y) (tangentV y)) (γ t)) :
    tangentCov.alongMap J f tangentV (γ t) (curveVelocity J γ t) =
      tangentCov.alongCurve (f ∘ γ) (fun r ↦ tangentV (γ r)) t := by
  simpa only [curveVelocityWithin_univ, alongCurveWithin_univ] using
    alongMap_curveVelocityWithin (f := f) tangentCov tangentV (s := univ)
      hγ.mdifferentiableWithinAt hV

end TangentBundle
end CovariantDerivative
