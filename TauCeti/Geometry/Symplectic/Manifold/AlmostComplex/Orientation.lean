/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic

/-!
# Top forms on the complex frames of an oriented almost complex surface

Let `j` be an almost complex structure on a surface `C`, oriented at a point `c` so that every
frame `(e, j e)` of the tangent plane is positive. Every nonzero `e` gives such a frame
(`TauCeti.SmoothAlmostComplexStructure.complexFrame`), so a top form `η` on the tangent plane is
determined by its values `η (e, j e)`: on any basis `b`,

`η b = η (b₀, j b₀) · det_{(b₀, j b₀)} b`,  `b₀ = b 0`.

The determinant is positive when `b` is positively oriented. Hence a top form that is nonnegative
on every frame `(e, j e)` is nonnegative on every positively oriented basis
(`TauCeti.SmoothAlmostComplexStructure.apply_basis_nonneg_of_forall_nonneg`). This is the
pointwise input to the positivity of energy integrals `∫_C u^* ω` of pseudoholomorphic curves,
whose densities `(u^* ω)(e, j e)` are nonnegative when `ω` tames the target structure. Combined
with the positivity of integration, a continuous compactly supported top form that is nonnegative on
every frame `(e, j e)` and positive on one has positive integral
(`TauCeti.SmoothAlmostComplexStructure.integralTopForm_pos_of_forall_nonneg`).

The same frames make pseudoholomorphic maps orientation preserving. Let `u : C → N` be
pseudoholomorphic between surfaces oriented so that their complex frames are positive. Its
differential is complex linear, so wherever it is nonzero it carries a frame `(e, j e)` with
`du e ≠ 0` to the frame `(du e, J du e)`, and `u` preserves orientation there
(`TauCeti.IsPseudoholomorphicAt.isOrientationPreservingAt`). At a regular value `y` every preimage
is such a point, so the signed count `degreeAtRegularValue` of the fibre over `y` is its
cardinality (`TauCeti.degreeAtRegularValue_eq_ncard_of_isPseudoholomorphicAt`): a pseudoholomorphic
map covers its regular values with no cancellation of signs.

On a Riemann surface with the canonical orientation of its complex structure, every frame
`(e, i e)` is positive
(`SmoothAlmostComplexStructure.orientation_eq_orientationAt_of_apply_one_eq_ofComplexManifold`),
so these results apply to holomorphic curves.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (energy of holomorphic curves).
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I ∞ C] (j : SmoothAlmostComplexStructure I C) {o : Manifold.Orientation I C (Fin 2)}

omit [FiniteDimensional ℝ E] in
/-- The complex frame `(e, j e)` of a nonzero tangent vector `e` of an almost complex surface `C`,
as a basis of the two-dimensional tangent plane. -/
def complexFrame {c : C} {e : TangentSpace I c} (he : e ≠ 0)
    (hc : finrank ℝ (TangentSpace I c) = 2) : Basis (Fin 2) ℝ (TangentSpace I c) :=
  basisOfLinearIndependentOfCardEqFinrank ((j.almostComplexStructureAt c).linearIndependent_pair he)
    (by simp [hc])

omit [FiniteDimensional ℝ E] in
@[simp]
theorem coe_complexFrame {c : C} {e : TangentSpace I c} (he : e ≠ 0)
    (hc : finrank ℝ (TangentSpace I c) = 2) : ⇑(j.complexFrame he hc) = ![e, j c e] := by
  rw [complexFrame, coe_basisOfLinearIndependentOfCardEqFinrank, almostComplexStructureAt_apply]

/-- **Top forms nonnegative on complex frames.** Let `j` be an almost complex structure on a
surface `C`, oriented at `c` so that every frame `(e, j e)` is positive. A top form `η` on the
tangent plane at `c` with `η (e, j e) ≥ 0` for every `e` is nonnegative on every positively
oriented basis. Indeed `η b = η (b₀, j b₀) det_{(b₀, j b₀)} b` for `b₀ = b 0`, and the
determinant is positive because both frames are positive. -/
theorem apply_basis_nonneg_of_forall_nonneg {c : C}
    (ho : ∀ b : Basis (Fin 2) ℝ (TangentSpace I c), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    {η : TangentSpace I c [⋀^Fin 2]→L[ℝ] ℝ} (hη : ∀ e, 0 ≤ η ![e, j c e])
    (b : Basis (Fin 2) ℝ (TangentSpace I c)) (hb : b.orientation = o.orientationAt c) :
    0 ≤ η b := by
  -- The frame `b₀ = (b 0, j (b 0))`.
  set b₀ := j.complexFrame (b.ne_zero 0) (by simpa using o.finrank_tangentSpace_eq c)
  have hb₀ : ⇑b₀ = ![b 0, j c (b 0)] := j.coe_complexFrame _ _
  -- A top form on the plane is its value on the frame `b₀` times `det_{b₀}`.
  have hη' : η b = η b₀ * b₀.det b := by
    simpa using congrArg (fun f ↦ f b) (η.toAlternatingMap.eq_smul_basis_det b₀)
  rw [hη']
  refine mul_nonneg ?_ ((b₀.orientation_eq_iff_det_pos b).1 ?_).le
  · rw [hb₀]
    exact hη (b 0)
  · rw [hb, ho b₀ (by rw [hb₀]; simp)]

/-- **Top forms positive on a complex frame have positive integral.** Let `j` be an almost complex
structure on a surface `C`, oriented so that every frame `(e, j e)` is positive. A continuous,
compactly supported top form `η` with `η (e, j e) ≥ 0` for every frame, and `η (e₀, j e₀) > 0` for
one frame, has positive integral. -/
theorem integralTopForm_pos_of_forall_nonneg
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    {η : RoughForm I C ℝ 2} (hη : IsSmoothForm I 0 η)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin 2]→L[ℝ] ℝ) η))
    (hnn : ∀ c e, 0 ≤ η c ![e, j c e]) {c₀ : C} {e₀ : TangentSpace I c₀}
    (hpos : 0 < η c₀ ![e₀, j c₀ e₀]) : 0 < integralTopForm o η := by
  have he₀ : e₀ ≠ 0 := by
    rintro rfl
    exact hpos.ne ((η c₀).map_coord_zero 0 rfl).symm
  -- The positive frame `(e₀, j e₀)` at `c₀`.
  set b₀ := j.complexFrame he₀ (by simpa using o.finrank_tangentSpace_eq c₀)
  have hb₀ : ⇑b₀ = ![e₀, j c₀ e₀] := j.coe_complexFrame _ _
  exact integralTopForm_pos o hη hc
    (fun c b hb ↦ j.apply_basis_nonneg_of_forall_nonneg (ho c) (hnn c) b hb)
    ⟨c₀, b₀, ho c₀ b₀ (by rw [hb₀]; simp), hb₀ ▸ hpos⟩

/-- **A Riemann surface is oriented by its complex frames.** For the canonical orientation of a
Riemann surface `N`, reindexed from `Fin (2 * finrank ℂ ℂ)` to `Fin 2`, every frame `(e, i e)` of
a tangent plane is positive: in the basis `(1, i)` of the tangent plane `ℂ`, which induces the
canonical orientation, it has determinant `|e|² > 0`. -/
theorem orientation_eq_orientationAt_of_apply_one_eq_ofComplexManifold {N : Type*}
    [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ, ℂ) ∞ N] (h : 2 * finrank ℂ ℂ = 2)
    (c : N) (b : Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) c))
    (hb : b 1 = ofComplexManifold ℂ N c (b 0)) :
    b.orientation = ((complexManifoldOrientation ℂ N).reindex (finCongr h)).orientationAt c := by
  rw [orientationAt_reindex_complexManifoldOrientation_complex]
  -- The tangent plane `TangentSpace 𝓘(ℝ, ℂ) c` is `ℂ` itself.
  let b' : Basis (Fin 2) ℝ ℂ := b
  have hb' : b' 1 = Complex.I * b' 0 := hb.trans (ofComplexManifold_apply (M := N) c (b' 0))
  change b'.orientation = Complex.orientation
  rw [Complex.orientation, eq_comm, Basis.orientation_eq_iff_det_pos, Basis.det_apply,
    Matrix.det_fin_two]
  simp only [Basis.toMatrix_apply, Complex.coe_basisOneI_repr, hb']
  simpa [Complex.normSq_apply] using Complex.normSq_pos.2 (b'.ne_zero 0)

end SmoothAlmostComplexStructure

/-! ### Orientation signs of pseudoholomorphic maps -/

section Pseudoholomorphic

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I ∞ C]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] {j : SmoothAlmostComplexStructure I C} {J : SmoothAlmostComplexStructure I' N}
  {o : Manifold.Orientation I C (Fin 2)} {o' : Manifold.Orientation I' N (Fin 2)} {u : C → N}

open Manifold.Orientation

/-- **Pseudoholomorphic maps preserve orientation where their differential is nonzero.** Let
`(C, j)` and `(N, J)` be almost complex surfaces, oriented at `c` and at `u c` so that their
complex frames `(e, j e)` and `(e', J e')` are positive. If `u` is pseudoholomorphic at `c` with
nonzero differential there, then `u` preserves orientation at `c`: its differential is complex
linear, so it carries a frame `(e, j e)` with `du e ≠ 0` to the frame `(du e, J du e)`. -/
theorem IsPseudoholomorphicAt.isOrientationPreservingAt {c : C}
    (ho : ∀ b : Basis (Fin 2) ℝ (TangentSpace I c), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (ho' : ∀ b : Basis (Fin 2) ℝ (TangentSpace I' (u c)), b 1 = J (u c) (b 0) →
      b.orientation = o'.orientationAt (u c))
    (hu : IsPseudoholomorphicAt j J u c) (hne : mfderiv I I' u c ≠ 0) :
    IsOrientationPreservingAt o o' u c := by
  obtain ⟨e, he⟩ : ∃ e, mfderiv I I' u c e ≠ 0 := by
    by_contra! h
    exact hne (ContinuousLinearMap.ext h)
  have he₀ : e ≠ 0 := by
    rintro rfl
    exact he (map_zero _)
  -- The complex frames `(e, j e)` at `c` and `(du e, J du e)` at `u c`.
  set b := j.complexFrame he₀ (by simpa using o.finrank_tangentSpace_eq c)
  set b' := J.complexFrame he (by simpa using o'.finrank_tangentSpace_eq (u c))
  have hb : ⇑b = ![e, j c e] := j.coe_complexFrame _ _
  have hb' : ⇑b' = ![mfderiv I I' u c e, J (u c) (mfderiv I I' u c e)] := J.coe_complexFrame _ _
  refine (isOrientationPreservingAt_iff_of_basis b b' fun i ↦ ?_).2
    (iff_of_true (ho b (by rw [hb]; simp)) (ho' b' (by rw [hb']; simp)))
  fin_cases i
  · simp [hb, hb']
  · simp [hb, hb', hu.mfderiv_apply_commute]

/-- **A pseudoholomorphic map counts its preimages positively.** Let `u` be a pseudoholomorphic
map between almost complex surfaces oriented so that their complex frames `(e, j e)` are
positive. At every regular value `y`, the signed count of the fibre over `y` is its cardinality:
the differential at each preimage is onto, hence nonzero, so every orientation sign is `1`. For
an infinite fibre both sides are `0` by the `finsum` and `ncard` conventions. -/
theorem degreeAtRegularValue_eq_ncard_of_isPseudoholomorphicAt
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (ho' : ∀ y (b : Basis (Fin 2) ℝ (TangentSpace I' y)), b 1 = J y (b 0) →
      b.orientation = o'.orientationAt y)
    (hu : ∀ c, IsPseudoholomorphicAt j J u c) {y : N} (hy : IsRegularValue I I' u y) :
    degreeAtRegularValue o o' u y = (u ⁻¹' {y}).ncard := by
  refine degreeAtRegularValue_eq_ncard fun c hc ↦
    (hu c).isOrientationPreservingAt (ho c) (ho' (u c)) ?_
  -- The tangent plane at `u c` is nonzero, so the onto differential at `c` is nonzero.
  have : Nontrivial (TangentSpace I' (u c)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simp [o'.finrank_tangentSpace_eq (u c)])
  intro h0
  obtain ⟨w, hw⟩ := exists_ne (0 : TangentSpace I' (u c))
  obtain ⟨e, he⟩ := isRegularPoint_iff.1 (hy.isRegularPoint hc) w
  exact hw (by simpa [h0] using he.symm)

end Pseudoholomorphic

end TauCeti
