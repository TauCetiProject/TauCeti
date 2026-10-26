/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.RestrictScalars
public import TauCeti.Geometry.Manifold.Orientation.Atlas
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.LinearAlgebra.Complex.Orientation
import TauCeti.Analysis.Calculus.TangentCone.Chart
import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# The canonical orientation of a complex manifold

The real Jacobian determinant of a holomorphic map between open subsets of a finite-dimensional
complex vector space `E` is the squared modulus of its complex Jacobian determinant. Hence a
holomorphic map preserves the real orientation of `E` exactly where its complex derivative is
invertible (`TauCeti.orientationPreservingOn_iff_det_fderiv_ne_zero`), and every holomorphic
coordinate change, with holomorphic inverse, preserves orientation
(`TauCeti.contDiffGroupoid_complex_le_orientationPreservingGroupoid`).

Consequently the holomorphic charts of a complex manifold `M` modelled on `𝓘(ℂ, E)` form an
oriented atlas of the underlying real manifold, modelled on `𝓘(ℝ, E)`. Transporting the canonical
real orientation `TauCeti.complexOrientation E` of the model, the orientation of the real basis
`(b₀, I • b₀, b₁, I • b₁, …)` for any complex basis `b`, through these charts gives the canonical
orientation `TauCeti.complexManifoldOrientation E M` of `M`. It is a manifold orientation in the
sense of `TauCeti.Manifold.Orientation`.

The construction involves no choice: the derivative of *every* chart of the maximal holomorphic
atlas carries the canonical orientation of each tangent space to that of the model
(`TauCeti.map_orientationAt_complexManifoldOrientation`), and this property, required of the
preferred charts only, characterizes it (`TauCeti.eq_complexManifoldOrientation_iff`).

## Main declarations

* `TauCeti.orientationPreservingOn_iff_det_fderiv_ne_zero`: a holomorphic map preserves the real
  orientation exactly where its complex derivative has nonzero determinant.
* `TauCeti.contDiffGroupoid_complex_le_orientationPreservingGroupoid`: holomorphic coordinate
  changes preserve orientation; contrast
  `TauCeti.not_contDiffGroupoid_le_orientationPreservingGroupoid`.
* `TauCeti.isOrientedAtlas_maximalAtlas_complex`: the holomorphic charts form an oriented atlas.
* `TauCeti.complexManifoldOrientation`: the canonical orientation of a complex manifold.
* `TauCeti.orientationAt_complexManifoldOrientation`: its tangent orientation at a point, read
  through any holomorphic chart.
* `Diffeomorph.isOrientationPreservingAt_complexManifoldOrientation`: biholomorphisms preserve
  canonical orientations.

## Implementation notes

Tangent orientations are stated for the underlying real manifold structure
`IsManifold 𝓘(ℝ, E) n M`, obtained from the complex one by `IsManifold.restrictScalars`. This
file provides it as the scoped instance `TauCeti.ComplexManifold.isManifold_real`, so callers
enable it with `open scoped TauCeti.ComplexManifold`. Since `IsManifold` is a `Prop`, any other
proof of the real structure works as well.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, §1.
* D. Huybrechts, *Complex Geometry: An Introduction*, §1.2 and §2.1.
-/

public section

noncomputable section

open Set Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-! ### Holomorphic coordinate changes preserve orientation -/

/-- A holomorphic map on an open subset of a finite-dimensional complex vector space preserves the
real orientation exactly where its complex derivative has nonzero determinant: its real Jacobian
determinant is the squared modulus of the complex one. -/
theorem orientationPreservingOn_iff_det_fderiv_ne_zero {f : E → E} {s : Set E} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) :
    OrientationPreservingOn 𝓘(ℝ, E) f s ↔
      ∀ x ∈ s, LinearMap.det (fderiv ℂ f x : E →ₗ[ℂ] E) ≠ 0 := by
  simp only [orientationPreservingOn_iff, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, range_id, fderivWithin_univ, differentiableWithinAt_univ,
    id_eq]
  refine forall₂_congr fun x hx ↦ ?_
  have hfx : DifferentiableAt ℂ f x := hf.differentiableAt (hs.mem_nhds hx)
  rw [hfx.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars_eq_normSq, Complex.normSq_pos]
  simp [hfx.restrictScalars ℝ]

/-- An open partial homeomorphism of a finite-dimensional complex vector space which is
holomorphic on its source, with inverse holomorphic on its target, preserves orientation on its
source. -/
theorem _root_.OpenPartialHomeomorph.orientationPreservingOn_of_differentiableOn
    (e : OpenPartialHomeomorph E E)
    (he : DifferentiableOn ℂ e e.source) (he' : DifferentiableOn ℂ e.symm e.target) :
    OrientationPreservingOn 𝓘(ℝ, E) e e.source := by
  refine (orientationPreservingOn_iff_det_fderiv_ne_zero e.open_source he).2 fun x hx ↦ ?_
  obtain ⟨A, hA⟩ := e.isInvertible_fderiv hx (he.differentiableAt (e.open_source.mem_nhds hx))
    (he'.differentiableAt (e.open_target.mem_nhds (e.map_source hx)))
  rw [← hA]
  exact A.toLinearEquiv.isUnit_det'.ne_zero

/-- Holomorphic coordinate changes preserve orientation: for `n ≠ 0`, the `C^n` groupoid of the
complex model `𝓘(ℂ, E)` is contained in the orientation-preserving groupoid of the underlying real
model `𝓘(ℝ, E)`. For real coordinate changes this fails
(`TauCeti.not_contDiffGroupoid_le_orientationPreservingGroupoid`). -/
theorem contDiffGroupoid_complex_le_orientationPreservingGroupoid (n : ℕ∞ω) [NeZero n] :
    contDiffGroupoid n 𝓘(ℂ, E) ≤ orientationPreservingGroupoid 𝓘(ℝ, E) := by
  intro e he
  have hn : n ≠ 0 := NeZero.ne n
  have hdiff (e : OpenPartialHomeomorph E E) (he : e ∈ contDiffGroupoid n 𝓘(ℂ, E)) :
      DifferentiableOn ℂ e e.source := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at he
    simpa [contDiffPregroupoid] using he.1.differentiableOn hn
  exact mem_orientationPreservingGroupoid_iff.2
    ⟨e.orientationPreservingOn_of_differentiableOn (hdiff e he)
      (hdiff e.symm ((contDiffGroupoid n 𝓘(ℂ, E)).symm he)),
    e.symm.orientationPreservingOn_of_differentiableOn
      (hdiff e.symm ((contDiffGroupoid n 𝓘(ℂ, E)).symm he)) (hdiff e he)⟩

/-! ### The canonical orientation of a complex manifold -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The atlas of a complex manifold has orientation-preserving coordinate changes, as a real
manifold. -/
instance hasGroupoid_orientationPreservingGroupoid_of_complex [IsManifold 𝓘(ℂ, E) 1 M] :
    HasGroupoid M (orientationPreservingGroupoid 𝓘(ℝ, E)) :=
  hasGroupoid_of_le (G₁ := contDiffGroupoid 1 𝓘(ℂ, E)) inferInstance
    (contDiffGroupoid_complex_le_orientationPreservingGroupoid 1)

/-- For `n ≠ 0`, the maximal holomorphic `C^n` atlas of a complex manifold is an oriented atlas of
the underlying real `C^n` manifold. -/
theorem isOrientedAtlas_maximalAtlas_complex (n : ℕ∞ω) [NeZero n] [IsManifold 𝓘(ℂ, E) n M] :
    IsOrientedAtlas 𝓘(ℝ, E) n (IsManifold.maximalAtlas 𝓘(ℂ, E) n M) where
  subset_maximalAtlas := IsManifold.maximalAtlas_subset_restrictScalars ℝ
  exists_mem_source x := ⟨chartAt E x, IsManifold.chart_mem_maximalAtlas x, mem_chart_source E x⟩
  symm_trans_mem he he' := contDiffGroupoid_complex_le_orientationPreservingGroupoid n
    (IsManifold.compatible_of_mem_maximalAtlas he he')

namespace ComplexManifold

/-- A complex `C^n` manifold is, with the same charts, a real `C^n` manifold modelled on
`𝓘(ℝ, E)`. Tangent orientations of a complex manifold are stated for this real structure. It is
a scoped instance, available after `open scoped TauCeti.ComplexManifold`. -/
scoped instance isManifold_real {n : ℕ∞ω} {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [h : IsManifold 𝓘(ℂ, E) n X] : IsManifold 𝓘(ℝ, E) n X :=
  h.restrictScalars ℝ

end ComplexManifold

open scoped ComplexManifold

variable [IsManifold 𝓘(ℂ, E) 1 M]

omit [FiniteDimensional ℂ E] in
/-- The real dimension `finrank ℝ E = 2 * finrank ℂ E` indexes the canonical orientations. -/
private theorem card_fin_two_mul_finrank_complex :
    Fintype.card (Fin (2 * finrank ℂ E)) = finrank ℝ E := by
  rw [Fintype.card_fin, finrank_real_of_complex]

variable (E M) in
/-- The canonical orientation of a complex manifold `M` modelled on `𝓘(ℂ, E)`, as a manifold
orientation of its underlying real manifold. Every holomorphic chart carries it to the canonical
real orientation `TauCeti.complexOrientation E` of the model
(`TauCeti.map_orientationAt_complexManifoldOrientation`). -/
def complexManifoldOrientation : Manifold.Orientation 𝓘(ℝ, E) M (Fin (2 * finrank ℂ E)) :=
  (isOrientedAtlas_maximalAtlas_complex (M := M) 1).orientation (complexOrientation E)
    card_fin_two_mul_finrank_complex

/-- The derivative of a holomorphic chart at `x` is an equivalence carrying the canonical
orientation of the tangent space at `x` to the canonical real orientation of the model. -/
private theorem exists_map_orientationAt_complexManifoldOrientation
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 1 M) {x : M}
    (hx : x ∈ e.source) : ∃ L : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E,
      (L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x ∧
        Orientation.map _ L.toLinearEquiv
          ((complexManifoldOrientation E M).orientationAt x) = complexOrientation E := by
  unfold complexManifoldOrientation
  exact (isOrientedAtlas_maximalAtlas_complex (M := M) 1).orientation_spec
    (complexOrientation E) card_fin_two_mul_finrank_complex he hx

/-- The derivative of every chart of the maximal holomorphic atlas, represented by a real
continuous linear equivalence `L`, carries the canonical orientation of the tangent space to the
canonical real orientation of the model. -/
theorem map_orientationAt_complexManifoldOrientation (n : ℕ∞ω) [NeZero n]
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) n M) {x : M}
    (hx : x ∈ e.source) (L : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E)
    (hL : (L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x) :
    Orientation.map _ L.toLinearEquiv
      ((complexManifoldOrientation E M).orientationAt x) = complexOrientation E := by
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne n)) he
  obtain ⟨L', hL', hmap⟩ := exists_map_orientationAt_complexManifoldOrientation he1 hx
  rwa [ContinuousLinearEquiv.coe_injective (hL'.trans hL.symm)] at hmap

/-- The tangent orientation of the canonical orientation of a complex manifold, read through any
holomorphic chart `e` at `x`: it is the canonical orientation of the model, pulled back by the
derivative `L` of `e` at `x`. -/
theorem orientationAt_complexManifoldOrientation (n : ℕ∞ω) [NeZero n]
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) n M) {x : M}
    (hx : x ∈ e.source) (L : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E)
    (hL : (L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x) :
    (complexManifoldOrientation E M).orientationAt x =
      Orientation.map _ L.symm.toLinearEquiv (complexOrientation E) := by
  rw [← map_orientationAt_complexManifoldOrientation n he hx L hL,
    ContinuousLinearEquiv.toLinearEquiv_symm, ← Orientation.map_symm, Equiv.symm_apply_apply]

/-- A manifold orientation of a complex manifold is its canonical orientation exactly when, at
every point `x`, the derivative of the preferred chart at `x` carries it to the canonical real
orientation of the model. -/
theorem eq_complexManifoldOrientation_iff
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (2 * finrank ℂ E))) :
    o = complexManifoldOrientation E M ↔ ∀ x : M, ∃ L : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E,
      (L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) x ∧
        Orientation.map _ L.toLinearEquiv (o.orientationAt x) = complexOrientation E := by
  constructor
  · rintro rfl x
    exact exists_map_orientationAt_complexManifoldOrientation
      (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source E x)
  · intro h
    ext x
    obtain ⟨L, hL, hmap⟩ := h x
    exact (Orientation.map _ L.toLinearEquiv).injective (hmap.trans
      (map_orientationAt_complexManifoldOrientation 1 (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_source E x) L hL).symm)

/-- A complex manifold is orientable as a real manifold. -/
instance orientable_of_complex : Orientable 𝓘(ℝ, E) M :=
  Orientable.of_hasGroupoid

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℂ, E) 1 N]

/-- Biholomorphisms preserve canonical orientations: at every point `x`, the derivative of a
`C^n` biholomorphism `Φ : M → N`, for `n ≠ 0`, carries the canonical orientation of `M` at `x` to
that of `N` at `Φ x`. -/
theorem _root_.Diffeomorph.isOrientationPreservingAt_complexManifoldOrientation (n : ℕ∞ω)
    [NeZero n] [IsManifold 𝓘(ℂ, E) n M] [IsManifold 𝓘(ℂ, E) n N]
    (Φ : M ≃ₘ^n⟮𝓘(ℂ, E), 𝓘(ℂ, E)⟯ N) (x : M) :
    Manifold.Orientation.IsOrientationPreservingAt (complexManifoldOrientation E M)
      (complexManifoldOrientation E N) Φ x := by
  -- Read both orientations through the holomorphic chart `e` of `N` at `Φ x` and its pullback
  -- `e ∘ Φ`, a holomorphic chart of `M` at `x` whose derivative is that of `e` after that of `Φ`.
  set e := chartAt E (Φ x)
  set e' := Φ.toHomeomorph.transOpenPartialHomeomorph e
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) n M :=
    Φ.transOpenPartialHomeomorph_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (Φ x))
  have hx : x ∈ e'.source := by
    simp only [e', Homeomorph.transOpenPartialHomeomorph_source, Set.mem_preimage,
      Diffeomorph.coe_toHomeomorph]
    exact mem_chart_source E (Φ x)
  obtain ⟨L, hL, hmap⟩ :=
    (eq_complexManifoldOrientation_iff (complexManifoldOrientation E N)).1 rfl (Φ x)
  have hn : n ≠ 0 := NeZero.ne n
  have hΦ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n Φ := Φ.isLocalDiffeomorph.restrictScalars ℝ
  let D := hΦ.mfderivToContinuousLinearEquiv hn x
  have hD : (D : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) (Φ x)) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ x :=
    hΦ.mfderivToContinuousLinearEquiv_coe hn x
  have hDL : ((D.trans L : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e' x := by
    have hcomp : ⇑e' = e ∘ Φ := by
      rw [Homeomorph.transOpenPartialHomeomorph_apply, Diffeomorph.coe_toHomeomorph]
    rw [hcomp, mfderiv_comp x (mdifferentiableAt_atlas (chart_mem_atlas E (Φ x))
      (mem_chart_source E (Φ x))) (hΦ.mdifferentiable hn x), ← hL, ← hD]
    exact (ContinuousLinearEquiv.comp_coe D L).symm
  refine (Manifold.Orientation.isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ D hD).2 ?_
  have hM := map_orientationAt_complexManifoldOrientation n he' hx (D.trans L) hDL
  rw [ContinuousLinearEquiv.trans_toLinearEquiv, Orientation.map_trans] at hM
  exact (Orientation.map _ L.toLinearEquiv).injective (hM.trans hmap.symm)

end TauCeti
