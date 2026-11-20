/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Integration.Pullback
public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.AddCircle
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.AddCircle
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic

/-!
# Pseudoholomorphic maps from compact surfaces onto a torus

Let `(C, j)` be a compact boundaryless surface with a smooth almost complex structure, oriented so
that every frame `(e, j e)` is positive, and let `v : C → T = ℝ / pℤ × ℝ / qℤ` be a smooth map that
is pseudoholomorphic for the standard structure `a ∂_s + b ∂_t ↦ -b ∂_s + a ∂_t` of the torus
(`TauCeti.SmoothAlmostComplexStructure.addCircleProd`). If the differential of `v` is nonzero
somewhere, then `v` is onto (`TauCeti.surjective_of_isPseudoholomorphicAt_addCircleProd`). When `C`
is connected this holds whenever `v` is not constant, but a map that is constant on each component
of a disconnected `C` need not be onto.

The proof compares two computations of the area `∫_C v^*(ds ∧ dt)`. Write `dv e = (a, b)` in the
real coordinates of the two circles. The Cauchy–Riemann equation gives `dv (j e) = (-b, a)`, so

`(v^*(ds ∧ dt))(e, j e) = a² + b²`

(`TauCeti.eval₂_mpullback_wedge_timeForm_of_isPseudoholomorphicAt`). The pulled back area form
is therefore nonnegative on positive frames and positive where `dv ≠ 0`, and the area of `v` is
positive as soon as `dv` is nonzero somewhere
(`TauCeti.integralTopForm_mpullback_wedge_timeForm_pos`). On the other hand the pullback of a top
form along a map that is not onto has integral zero
(`TauCeti.integralTopForm_mpullback_eq_zero_of_not_surjective`). No integrable complex
coordinates on `C` are used, and `v` may have critical points.

The same area computation measures how many times `v` covers the torus. When `C` is modelled on
the plane `ℝ × ℝ`, like the torus, `v` has a mapping degree, and the degree formula gives
`∫_C v^*(ds ∧ dt) = deg(v) · p q`
(`TauCeti.integralTopForm_mpullback_wedge_timeForm_eq_degree_mul`), so `deg(v) > 0` whenever
`dv ≠ 0` somewhere (`TauCeti.degree_pos_of_isPseudoholomorphicAt_addCircleProd`). The torus is
oriented by its complex frames
(`TauCeti.SmoothAlmostComplexStructure.orientation_eq_orientationAt_of_apply_one_eq_addCircleProd`),
so `v` preserves orientation at every point where `dv ≠ 0`, and every regular value has exactly
`deg(v)` preimages (`TauCeti.degree_eq_ncard_of_isPseudoholomorphicAt_addCircleProd`). An injective
`v` has degree one (`TauCeti.degree_eq_one_of_isPseudoholomorphicAt_addCircleProd_of_injective`).

This is the covering statement for the lift of a pseudoholomorphic horizontal curve with nonzero
differential somewhere in a symplectic suspension to the orbit torus over its closed orbit: such a
lift is onto, so the curve fills the whole orbit torus.

## Main results

* `TauCeti.eval₂_mpullback_wedge_timeForm_of_isPseudoholomorphicAt`: the pulled back area form on
  a complex frame `(e, j e)` is `|dv e|²`.
* `TauCeti.integralTopForm_mpullback_wedge_timeForm_pos`: a pseudoholomorphic map with nonzero
  differential somewhere has positive area.
* `TauCeti.surjective_of_isPseudoholomorphicAt_addCircleProd`: a pseudoholomorphic map from a
  compact surface to the torus with nonzero differential somewhere is onto.
* `TauCeti.integralTopForm_mpullback_wedge_timeForm_eq_degree_mul`: the area of a map to the torus
  is its degree times the area `p q` of the torus.
* `TauCeti.degree_pos_of_isPseudoholomorphicAt_addCircleProd`: such a map has positive degree.
* `TauCeti.degree_eq_ncard_of_isPseudoholomorphicAt_addCircleProd`: its degree is the number of
  preimages of each regular value.
* `TauCeti.degree_eq_one_of_isPseudoholomorphicAt_addCircleProd_of_injective`: an injective one
  has degree one.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (energy and area of holomorphic curves).
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 2.7 (nonconstant holomorphic maps of compact Riemann surfaces are onto).
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I ∞ C] {j : SmoothAlmostComplexStructure I C} {o : Manifold.Orientation I C (Fin 2)}
  {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)] {v : C → AddCircle p × AddCircle q}

omit [FiniteDimensional ℝ E] in
/-- On a complex frame `(e, j e)`, the pullback of the area form `ds ∧ dt` of the torus along a
pseudoholomorphic map `v` is `a² + b²`, where `dv e = (a, b)` in the real coordinates of the two
circles. -/
theorem eval₂_mpullback_wedge_timeForm_of_isPseudoholomorphicAt
    (hv : ContMDiff I (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v) {c : C}
    (hhol : IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd p q) v c)
    (e : TangentSpace I c) :
    SmoothBundleForm.eval₂ (SmoothForm.mpullback v hv (SmoothForm.wedge
        (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm p))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm q)))) c e (j c e) =
      (mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c e).1 ^ 2 + (mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c e).2 ^ 2 := by
  rw [SmoothForm.eval₂_mpullback, hhol.mfderiv_apply_commute,
    SmoothAlmostComplexStructure.addCircleProd_apply]
  exact (AddCircle.eval₂_wedge_timeForm p q (v c) _ _).trans (by dsimp only; ring)

/-- **A pseudoholomorphic map to the torus with nonzero differential has positive area.** Let `C`
be a compact surface with an almost complex structure `j`, oriented so that the frames `(e, j e)`
are positive, and let `v : C → ℝ / pℤ × ℝ / qℤ` be a smooth pseudoholomorphic map for the
standard structure of the torus, with nonzero differential somewhere. Then
`∫_C v^*(ds ∧ dt) > 0`. -/
theorem integralTopForm_mpullback_wedge_timeForm_pos [CompactSpace C]
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hv : ContMDiff I (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hhol : ∀ c, IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd p q) v c)
    {c₀ : C} (hne : mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c₀ ≠ 0) :
    0 < integralTopForm o (SmoothForm.mpullback v hv (SmoothForm.wedge
        (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm p))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm q)))).val := by
  set η := SmoothForm.mpullback v hv (SmoothForm.wedge
    (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm p))
    (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm q)))
  -- On a frame `(e, j e)`, `η` is `|dv e|²`.
  have hη (c : C) (e : TangentSpace I c) :
      η.val c ![e, j c e] = (mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c e).1 ^ 2 +
        (mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c e).2 ^ 2 :=
    (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans
      (eval₂_mpullback_wedge_timeForm_of_isPseudoholomorphicAt hv (hhol c) e)
  obtain ⟨e, he⟩ : ∃ e, mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c₀ e ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (ContinuousLinearMap.ext h)
  refine j.integralTopForm_pos_of_forall_nonneg ho (η.isSmoothForm.of_le (by simp))
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
    (fun c e' ↦ (hη c e').symm ▸ by positivity) (e₀ := e) ?_
  rw [hη]
  have h : (mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c₀ e).1 ≠ 0 ∨
      (mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c₀ e).2 ≠ 0 := by
    by_contra! h
    exact he (Prod.ext h.1 h.2)
  rcases h with h | h <;> positivity

/-- **Pseudoholomorphic maps to the torus with nonzero differential are onto.** Let `C` be a compact
boundaryless surface with an almost complex structure `j`, oriented so that the frames `(e, j e)`
are positive, and let `v : C → ℝ / pℤ × ℝ / qℤ` be a smooth pseudoholomorphic map for the standard
structure of the torus. If the differential of `v` is nonzero somewhere, then `v` is onto. -/
theorem surjective_of_isPseudoholomorphicAt_addCircleProd [BoundarylessManifold I C] [T2Space C]
    [CompactSpace C]
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hv : ContMDiff I (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hhol : ∀ c, IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd p q) v c)
    {c₀ : C} (hne : mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c₀ ≠ 0) : Function.Surjective v :=
  surjective_of_integralTopForm_mpullback_ne_zero o
    ((AddCircle.orientation p).prod (AddCircle.orientation q)) hv hv.continuous.isProperMap
    (by rw [compactlySupportedForms_eq_top]; trivial)
    (integralTopForm_mpullback_wedge_timeForm_pos ho hv hhol hne).ne'

end TauCeti

/-! ### The covering degree -/

namespace TauCeti

variable {H C : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (ℝ × ℝ) H} [TopologicalSpace C]
  [ChartedSpace H C] [IsManifold I ∞ C] [BoundarylessManifold I C] [T2Space C] [CompactSpace C]
  {j : SmoothAlmostComplexStructure I C} {o : Manifold.Orientation I C (Fin 2)}
  {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)] {v : C → AddCircle p × AddCircle q}

/-- **The area of a map to a torus is a multiple of the area of the torus.** For a smooth map `v`
from a compact oriented boundaryless surface to `AddCircle p × AddCircle q`, oriented as the
product of the positive orientations of the circles, `∫_C v^*(ds ∧ dt) = deg(v) · p q`. -/
theorem integralTopForm_mpullback_wedge_timeForm_eq_degree_mul
    (hv : ContMDiff I (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v) :
    integralTopForm o (SmoothForm.mpullback v hv (SmoothForm.wedge
        (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm p))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm q)))).val =
      degree o ((AddCircle.orientation p).prod (AddCircle.orientation q)) v * (p * q) := by
  rw [SmoothForm.coe_mpullback, integralTopForm_mpullback_eq_degree_mul o _ hv
    hv.continuous.isProperMap (SmoothForm.isSmoothForm _)
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)),
    AddCircle.integralTopForm_wedge_timeForm]

/-- **Nonconstant pseudoholomorphic maps to a torus have positive degree.** Let `C` be a compact
boundaryless surface with an almost complex structure `j`, oriented so that the frames `(e, j e)`
are positive, and let `v : C → ℝ / pℤ × ℝ / qℤ` be a smooth pseudoholomorphic map for the standard
structure of the torus. If the differential of `v` is nonzero somewhere, then `v` has positive
degree: its area `deg(v) · p q` is positive. -/
theorem degree_pos_of_isPseudoholomorphicAt_addCircleProd
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hv : ContMDiff I (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hhol : ∀ c, IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd p q) v c)
    {c₀ : C} (hne : mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c₀ ≠ 0) :
    0 < degree o ((AddCircle.orientation p).prod (AddCircle.orientation q)) v := by
  have h := integralTopForm_mpullback_wedge_timeForm_pos ho hv hhol hne
  rw [integralTopForm_mpullback_wedge_timeForm_eq_degree_mul hv] at h
  exact_mod_cast pos_of_mul_pos_left h (mul_pos Fact.out Fact.out).le

/-- **The degree of a pseudoholomorphic map to a torus counts preimages.** Let `C` be a compact
boundaryless surface with an almost complex structure `j`, oriented so that the frames `(e, j e)`
are positive, and let `v : C → ℝ / pℤ × ℝ / qℤ` be a smooth pseudoholomorphic map for the standard
structure of the torus. Then the degree of `v` is the number of preimages of every regular value:
`v` preserves orientation wherever its differential is nonzero. -/
theorem degree_eq_ncard_of_isPseudoholomorphicAt_addCircleProd
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hv : ContMDiff I (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hhol : ∀ c, IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd p q) v c)
    {y : AddCircle p × AddCircle q} (hy : IsRegularValue I (𝓘(ℝ).prod 𝓘(ℝ)) v y) :
    degree o ((AddCircle.orientation p).prod (AddCircle.orientation q)) v = (v ⁻¹' {y}).ncard := by
  rw [degree_eq_degreeAtRegularValue o _ hv hv.continuous.isProperMap hy]
  exact degreeAtRegularValue_eq_ncard_of_isPseudoholomorphicAt ho
    (SmoothAlmostComplexStructure.orientation_eq_orientationAt_of_apply_one_eq_addCircleProd p q)
    hhol hy

/-- **Injective pseudoholomorphic maps onto a torus have degree one.** Let `C` be a compact
boundaryless surface with an almost complex structure `j`, oriented so that the frames `(e, j e)`
are positive, and let `v : C → ℝ / pℤ × ℝ / qℤ` be an injective smooth pseudoholomorphic map for
the standard structure of the torus, with nonzero differential somewhere. Then `v` has degree one:
its degree is positive and counts the preimages of a regular value, of which there is at most
one. -/
theorem degree_eq_one_of_isPseudoholomorphicAt_addCircleProd_of_injective
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hv : ContMDiff I (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hhol : ∀ c, IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd p q) v c)
    {c₀ : C} (hne : mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c₀ ≠ 0) (hinj : Function.Injective v) :
    degree o ((AddCircle.orientation p).prod (AddCircle.orientation q)) v = 1 := by
  obtain ⟨y, hy⟩ := (dense_isRegularValue rfl (hv.mdifferentiable (by simp))).nonempty
  have hpos := degree_pos_of_isPseudoholomorphicAt_addCircleProd ho hv hhol hne
  have hs : (v ⁻¹' {y}).Subsingleton := fun _ ha _ hb ↦ hinj (ha.trans hb.symm)
  have hle : (v ⁻¹' {y}).ncard ≤ 1 := (Set.ncard_le_one hs.finite).2 hs
  rw [degree_eq_ncard_of_isPseudoholomorphicAt_addCircleProd ho hv hhol hy] at hpos ⊢
  omega

end TauCeti
