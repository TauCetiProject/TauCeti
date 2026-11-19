/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Integration.Pullback
public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.RegularValue.Fibre
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

This is the covering statement for the lift of a pseudoholomorphic horizontal curve with nonzero
differential somewhere in a symplectic suspension to the orbit torus over its closed orbit: such a
lift is onto, so the curve fills the whole orbit torus.

The same area computation measures how often `v` covers the torus. For `C` modelled on `ℝ × ℝ`,
like the torus, `v` has a mapping degree `deg v` (`TauCeti.degree`) for the orientation of `C` and
the product of the positive orientations of the two circles, and the degree formula gives
`∫_C v^*(ds ∧ dt) = deg v · p q`. So `deg v` is positive when `v` is not constant
(`TauCeti.degree_pos_of_isPseudoholomorphicAt_addCircleProd`). At a point where `dv` is invertible,
the Cauchy–Riemann equation carries the positive frames `(e, j e)` of `C` to positive frames of the
torus, so `v` preserves orientation there
(`TauCeti.isOrientationPreservingAt_of_isPseudoholomorphicAt_addCircleProd`). The orientation
signs over a regular value are therefore all `+1`, and every regular value has exactly `deg v`
preimages (`TauCeti.ncard_preimage_eq_degree_of_isRegularValue`). When `dv` is injective
everywhere, every value is regular, so `v` has `deg v` sheets over every point of the torus
(`TauCeti.ncard_preimage_eq_degree_of_injective_mfderiv`), and it is injective exactly when its
degree is one (`TauCeti.injective_iff_degree_eq_one_of_injective_mfderiv`).

## Main results

* `TauCeti.eval₂_mpullback_wedge_timeForm_of_isPseudoholomorphicAt`: the pulled back area form on
  a complex frame `(e, j e)` is `|dv e|²`.
* `TauCeti.integralTopForm_mpullback_wedge_timeForm_pos`: a pseudoholomorphic map with nonzero
  differential somewhere has positive area.
* `TauCeti.surjective_of_isPseudoholomorphicAt_addCircleProd`: a pseudoholomorphic map from a
  compact surface to the torus with nonzero differential somewhere is onto.
* `TauCeti.isOrientationPreservingAt_of_mfderiv_almostComplex_apply_eq`: a map to the torus whose
  differential sends complex frames `(e, j e)` to positive frames preserves orientation.
* `TauCeti.isOrientationPreservingAt_of_isPseudoholomorphicAt_addCircleProd`: a pseudoholomorphic
  map to the torus preserves orientation wherever its differential is invertible.
* `TauCeti.degree_pos_of_isPseudoholomorphicAt_addCircleProd`: a pseudoholomorphic map to the
  torus with nonzero differential somewhere has positive degree.
* `TauCeti.ncard_preimage_eq_degree_of_isRegularValue`: every regular value has `deg v` preimages.
* `TauCeti.ncard_preimage_eq_degree_of_injective_mfderiv`,
  `TauCeti.injective_iff_degree_eq_one_of_injective_mfderiv`: an immersion has `deg v` sheets, and
  is injective exactly when `deg v = 1`.

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

section Area

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
        (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm q)))).1 := by
  set η := SmoothForm.mpullback v hv (SmoothForm.wedge
    (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm p))
    (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm q)))
  -- On a frame `(e, j e)`, `η` is `|dv e|²`.
  have hη (c : C) (e : TangentSpace I c) :
      η.1 c ![e, j c e] = (mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c e).1 ^ 2 +
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

/-- **A map to the torus that sends the complex frames to positive frames preserves orientation.**
Let `v : C → ℝ / pℤ × ℝ / qℤ` have invertible differential at `c`, orient `C` so that the frames
`(e, j e)` at `c` are positive, and suppose that `dv e = (1, 0)` implies `dv (j e) = (0, 1)`. Then
`v` preserves orientation at `c`, for the product of the positive orientations of the two circles:
the standard frame `((1, 0), (0, 1))` of the torus pulls back along `dv` to a frame `(e, j e)`. -/
theorem isOrientationPreservingAt_of_mfderiv_almostComplex_apply_eq {c : C}
    (ho : ∀ b : Basis (Fin 2) ℝ (TangentSpace I c), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hinv : (mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c).IsInvertible)
    (hj : ∀ e, mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c e = ((1 : ℝ), (0 : ℝ)) →
      mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c (j c e) = ((0 : ℝ), (1 : ℝ))) :
    Manifold.Orientation.IsOrientationPreservingAt o
      ((AddCircle.orientation p).prod (AddCircle.orientation q)) v c := by
  obtain ⟨L, hL⟩ := hinv
  have hLw (w : TangentSpace I c) : L w = mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c w := by
    rw [← hL, ContinuousLinearEquiv.coe_coe]
  let b : Basis (Fin 2) ℝ (TangentSpace I c) := (Basis.finTwoProd ℝ).map L.symm.toLinearEquiv
  have hLb (i : Fin 2) : L (b i) = Basis.finTwoProd ℝ i :=
    L.apply_symm_apply (Basis.finTwoProd ℝ i)
  have hb : b 1 = j c (b 0) := by
    apply L.injective
    rw [hLb, Basis.finTwoProd_one, hLw]
    exact (hj (b 0) (by rw [← hLw, hLb, Basis.finTwoProd_zero])).symm
  rw [Manifold.Orientation.isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ L hL, ← ho b hb,
    ← Basis.orientation_map, AddCircle.orientationAt_orientation_prod_orientation]
  congr 1
  ext i
  exact hLb i

/-- **A pseudoholomorphic map to the torus preserves orientation where it is a local
diffeomorphism.** Let `v : C → ℝ / pℤ × ℝ / qℤ` be pseudoholomorphic at `c` for the standard
structure of the torus, with invertible differential at `c`, and orient `C` so that the frames
`(e, j e)` at `c` are positive. Then `v` preserves orientation at `c`, for the product of the
positive orientations of the two circles. -/
theorem isOrientationPreservingAt_of_isPseudoholomorphicAt_addCircleProd {c : C}
    (ho : ∀ b : Basis (Fin 2) ℝ (TangentSpace I c), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd p q) v c)
    (hinv : (mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c).IsInvertible) :
    Manifold.Orientation.IsOrientationPreservingAt o
      ((AddCircle.orientation p).prod (AddCircle.orientation q)) v c := by
  refine isOrientationPreservingAt_of_mfderiv_almostComplex_apply_eq ho hinv fun e he ↦ ?_
  -- The Cauchy–Riemann equation `dv (j e) = i · dv e` sends `(1, 0)` to `(-0, 1)`.
  rw [hhol.mfderiv_apply_commute, SmoothAlmostComplexStructure.addCircleProd_apply, he, neg_zero]

end Area

/-! ### The degree of a pseudoholomorphic map to the torus -/

section Degree

variable {H C : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (ℝ × ℝ) H}
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C] [BoundarylessManifold I C]
  [T2Space C] [CompactSpace C] {j : SmoothAlmostComplexStructure I C}
  {o : Manifold.Orientation I C (Fin 2)} {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)]
  {v : C → AddCircle p × AddCircle q}

/-- **A nonconstant pseudoholomorphic map to the torus has positive degree.** Let `C` be a compact
boundaryless surface modelled on `ℝ × ℝ`, with an almost complex structure `j`, oriented so that
the frames `(e, j e)` are positive, and let `v : C → ℝ / pℤ × ℝ / qℤ` be a smooth pseudoholomorphic
map for the standard structure of the torus, with nonzero differential somewhere. Then the degree
of `v`, for the product of the positive orientations of the two circles, is positive. -/
theorem degree_pos_of_isPseudoholomorphicAt_addCircleProd
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hv : ContMDiff I (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hhol : ∀ c, IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd p q) v c)
    {c₀ : C} (hne : mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c₀ ≠ 0) :
    0 < degree o ((AddCircle.orientation p).prod (AddCircle.orientation q)) v := by
  -- The area `∫_C v^*(ds ∧ dt)` is positive, and by the degree formula it is `deg v · p q`.
  have hpos := integralTopForm_mpullback_wedge_timeForm_pos ho hv hhol hne
  rw [SmoothForm.coe_mpullback, integralTopForm_mpullback_eq_degree_mul o
      ((AddCircle.orientation p).prod (AddCircle.orientation q)) hv (SmoothForm.isSmoothForm _)
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)),
    AddCircle.integralTopForm_wedge_timeForm] at hpos
  exact_mod_cast (mul_pos_iff_of_pos_right (mul_pos (Fact.out : 0 < p) Fact.out)).1 hpos

/-- **A pseudoholomorphic map to the torus covers every regular value `deg v` times.** Let `C` be
a compact boundaryless surface modelled on `ℝ × ℝ`, oriented so that the frames `(e, j e)` are
positive, and let `v : C → ℝ / pℤ × ℝ / qℤ` be a smooth pseudoholomorphic map for the standard
structure of the torus. Then every regular value of `v` has exactly `deg v` preimages, for the
product of the positive orientations of the two circles. -/
theorem ncard_preimage_eq_degree_of_isRegularValue
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hv : ContMDiff I (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hhol : ∀ c, IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd p q) v c)
    {y : AddCircle p × AddCircle q} (hy : IsRegularValue I (𝓘(ℝ).prod 𝓘(ℝ)) v y) :
    ((v ⁻¹' {y}).ncard : ℤ) =
      degree o ((AddCircle.orientation p).prod (AddCircle.orientation q)) v := by
  have hfin := hy.finite_preimage rfl hv.continuous
  -- Every point of the fibre is a point of invertible differential, where `v` preserves
  -- orientation, so each contributes `+1` to the signed count.
  rw [degree_eq_degreeAtRegularValue o _ hv hy, degreeAtRegularValue_eq_sum_of_finite hfin,
    Set.ncard_eq_toFinset_card _ hfin, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [Set.Finite.mem_toFinset] at hc
  rw [Manifold.Orientation.orientationSign_of_isOrientationPreservingAt
    (isOrientationPreservingAt_of_isPseudoholomorphicAt_addCircleProd (ho c) (hhol c)
      ((isRegularPoint_iff_isInvertible_mfderiv rfl).1 (hy.isRegularPoint hc))), Nat.cast_one]

/-- **A pseudoholomorphic immersion into the torus has `deg v` sheets.** Let `C` be a compact
boundaryless surface modelled on `ℝ × ℝ`, oriented so that the frames `(e, j e)` are positive, and
let `v : C → ℝ / pℤ × ℝ / qℤ` be a smooth pseudoholomorphic map for the standard structure of the
torus with injective differential at every point. Then every point of the torus has exactly
`deg v` preimages. -/
theorem ncard_preimage_eq_degree_of_injective_mfderiv
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hv : ContMDiff I (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hhol : ∀ c, IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd p q) v c)
    (hinj : ∀ c, Function.Injective (mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c))
    (y : AddCircle p × AddCircle q) :
    ((v ⁻¹' {y}).ncard : ℤ) =
      degree o ((AddCircle.orientation p).prod (AddCircle.orientation q)) v :=
  ncard_preimage_eq_degree_of_isRegularValue ho hv hhol <| isRegularValue_iff.2 fun c _ ↦
    (isRegularPoint_iff_injective_mfderiv rfl).2 (hinj c)

/-- **A pseudoholomorphic immersion into the torus is injective exactly when it has degree one.**
Let `C` be a nonempty compact boundaryless surface modelled on `ℝ × ℝ`, oriented so that the
frames `(e, j e)` are positive, and let `v : C → ℝ / pℤ × ℝ / qℤ` be a smooth pseudoholomorphic
map for the standard structure of the torus with injective differential at every point. Then `v`
is injective if and only if `deg v = 1`. -/
theorem injective_iff_degree_eq_one_of_injective_mfderiv [Nonempty C]
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hv : ContMDiff I (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hhol : ∀ c, IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd p q) v c)
    (hinj : ∀ c, Function.Injective (mfderiv I (𝓘(ℝ).prod 𝓘(ℝ)) v c)) :
    Function.Injective v ↔
      degree o ((AddCircle.orientation p).prod (AddCircle.orientation q)) v = 1 := by
  have hcard := ncard_preimage_eq_degree_of_injective_mfderiv ho hv hhol hinj
  constructor
  · intro hvinj
    obtain ⟨c⟩ := ‹Nonempty C›
    rw [← hcard (v c), Set.ncard_eq_one.2 ⟨c, Set.ext fun c' ↦ ⟨fun h ↦ hvinj h, fun h ↦ h ▸ rfl⟩⟩,
      Nat.cast_one]
  · intro hdeg a b hab
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (by exact_mod_cast (hcard (v b)).trans hdeg)
    have ha : a ∈ v ⁻¹' {v b} := hab
    have hb : b ∈ v ⁻¹' {v b} := rfl
    rw [hc] at ha hb
    exact ha.trans hb.symm

end Degree

end TauCeti
