/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Cover
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Geometry.Manifold.Instances.MappingTorus.Vertical
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
import TauCeti.Topology.FiberBundle.Pullback

/-!
# Orientability of the normal bundle of a closed orbit in a mapping torus

Let `φ` be a diffeomorphism of a manifold `M` modelled on a finite-dimensional space `E`, and let
`c : t ↦ [t, x]` be an embedded circle in the mapping torus
`Y_φ = (ℝ × M) / ((t + 1, y) ∼ (t, φ y))`, the closed orbit of the suspension flow through a fixed
point `x` of `φ`. This file shows that the normal bundle `ν` of `c` is orientable exactly when the
differential `dφₓ` preserves orientation, that is, when `det dφₓ > 0`
(`TauCeti.SmoothMappingTorus.nonempty_vectorBundleOrientation_normalSpace_iff`).

The vertical vectors `d[t, ·]ₓ w` along the circle are never tangent to it, since the projection
`[t, y] ↦ [t]` to the base circle kills them and is injective on the velocity of `c`. So their
normal classes identify `TₓM` with each fibre of `ν`, and a basis of `TₓM` gives a frame of `ν` at
every point `[t, x]` of the circle, depending continuously on `t : ℝ`. The identification
`[t + 1, y] = [t, φ y]` carries the frame at `t + 1` to the frame at `t` composed with `dφₓ`. When
`det dφₓ > 0` the orientations of these frames are therefore periodic in `t`, and descend to a
continuous section of the orientation double cover of `ν` over the circle; when `det dφₓ < 0` the
continuous path of orientations ends at the opposite of its start, which no orientation allows.

The whole normal bundle must be distinguished from the negative normal bundle of a critical
circle of a Morse–Bott function induced on `Y_φ`, whose monodromy is that of `dφₓ` on the negative
directions only
(`TauCeti.SmoothMappingTorus.isEmpty_vectorBundleOrientation_negativeNormalSpace_of_det_neg`).
In the mapping torus of `S² × S¹` by a pair of reflections the first is orientable while the
second is not (`TauCeti.Geometry.Manifold.Morse.Bott.Examples.SphereCircle`).

## Main results

* `TauCeti.SmoothMappingTorus.normalClass_mfderiv_mk_eq_zero_iff`: along a circle `t ↦ [t, x]`,
  the normal class of a vertical vector `d[t, ·]ₓ w` vanishes only for `w = 0`.
* `TauCeti.SmoothMappingTorus.continuous_normalClass_mfderiv_mk`: the normal classes of the
  vertical vectors `d[t, ·]ₓ w` along a circle `t ↦ [t, x]` form a continuous path in its normal
  bundle.
* `TauCeti.SmoothMappingTorus.nonempty_vectorBundleOrientation_normalSpace_of_det_pos`: if
  `det dφₓ > 0`, the normal bundle of the circle through `x` is orientable.
* `TauCeti.SmoothMappingTorus.isEmpty_vectorBundleOrientation_normalSpace_of_det_neg`: if
  `det dφₓ < 0`, it is not orientable.
* `TauCeti.SmoothMappingTorus.nonempty_vectorBundleOrientation_normalSpace_iff`: it is orientable
  if and only if `det dφₓ > 0`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (orientations of Morse–Bott trajectory spaces).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover of a vector bundle).
-/

public section

noncomputable section

open Bundle Function Module Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M} {x : M}

variable (hn : (∞ : ℕ∞ω) ≠ 0)
  {c : SmoothEmbedding 𝓘(ℝ) (𝓘(ℝ).prod I) ∞ (AddCircle ((1 : ℕ) : ℝ)) (SmoothMappingTorus φ)}

/-- The normal classes `w ↦ [d[t, ·]ₓ w]` of the vertical vectors at the point `c t` of a circle `c`
in the mapping torus, as a linear map from the model space of `M`. -/
private def verticalNormalMap (t : ℝ) :
    E →ₗ[ℝ] c.isImmersion.NormalSpace (t : AddCircle ((1 : ℕ) : ℝ)) hn :=
  c.isImmersion.normalClass t hn ∘ₗ (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x).toLinearMap

omit [IsManifold I ∞ M] in
private theorem verticalNormalMap_apply (t : ℝ) (w : E) :
    verticalNormalMap (x := x) hn (c := c) t w =
      c.isImmersion.normalClass t hn (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x w) :=
  (rfl)

/-- Along a circle `c : t ↦ [t, x]` in the mapping torus, the normal class of a vertical vector
`d[t, ·]ₓ w` vanishes only for `w = 0`: the projection to the base circle kills `d[t, ·]ₓ w`, and
sends the velocity of `c` to `1`, so a nonzero vertical vector is not tangent to `c`. -/
theorem normalClass_mfderiv_mk_eq_zero_iff (hc : ∀ t : ℝ, c t = mk φ t x) (t : ℝ)
    (w : TangentSpace I x) :
    c.isImmersion.normalClass t hn (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x w) = 0 ↔ w = 0 := by
  refine ⟨fun hw ↦ ?_, fun hw ↦ by rw [hw, map_zero]; exact map_zero _⟩
  obtain ⟨a, ha⟩ := (c.isImmersion.mem_tangentRange_iff _ hn _).1
    ((c.isImmersion.normalClass_eq_zero_iff _ hn _).1 hw)
  have hper : IsPeriodicPt φ 1 x := IsFixedPt.isPeriodicPt (apply_eq_of_forall_eq_mk hc) 1
  have hcc : ⇑c = closedOrbit φ hper := funext fun s ↦ by
    induction s using QuotientAddGroup.induction_on with | H s => rw [hc, closedOrbit_coe]
  -- The projection to the base circle sends the velocity vector `dc a` back to `a`.
  have h1 := congrArg (fun L ↦ L a)
    (mfderiv_proj_comp_mfderiv_closedOrbit hper (n := ∞) hn (t : AddCircle ((1 : ℕ) : ℝ)))
  rw [← hcc] at h1
  -- It kills the vertical vector `d[t, ·]ₓ w`, which is tangent to the fibre through `[t, x]`.
  have h0 : mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) (mk φ t x)
      (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x w) = 0 :=
    LinearMap.mem_ker.1 (range_mfderiv_mk φ t x ▸ ⟨w, rfl⟩)
  -- So `a = 0`; the tangent spaces at `c t = [t, x]` are all `ℝ × E`.
  have ha0 : a = 0 := h1.symm.trans
    ((congrArg (fun L : ℝ × E →L[ℝ] ℝ ↦ L (mfderiv 𝓘(ℝ) (𝓘(ℝ).prod I) c t a))
      (mfderiv_congr_point (hc t))).trans (by rw [ha]; exact h0))
  rw [ha0, map_zero] at ha
  exact injective_mfderiv_mk φ hn t x (ha.symm.trans (map_zero _).symm)

/-- Along a circle `c : t ↦ [t, x]`, a vertical vector `d[t, ·]ₓ w` with `w ≠ 0` is not tangent
to `c`. -/
private theorem injective_verticalNormalMap (hc : ∀ t : ℝ, c t = mk φ t x) (t : ℝ) :
    Injective (verticalNormalMap (x := x) hn (c := c) t) :=
  (injective_iff_map_eq_zero _).2 fun w hw ↦
    (normalClass_mfderiv_mk_eq_zero_iff hn hc t w).1 (by rwa [verticalNormalMap_apply] at hw)

variable [FiniteDimensional ℝ E]

/-- The normal classes of the vertical vectors `d[t, ·]ₓ w` at the points `c t = [t, x]` of a
circle `c` form a continuous path in the normal bundle of `c`. -/
theorem continuous_normalClass_mfderiv_mk (hc : ∀ t : ℝ, c t = mk φ t x)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hdim : finrank ℝ P = finrank ℝ (ℝ × E) - finrank ℝ ℝ) (w : TangentSpace I x) :
    letI := c.normalSpaceFiberBundle hn hdim
    Continuous fun t : ℝ ↦ (⟨(t : AddCircle ((1 : ℕ) : ℝ)),
      c.isImmersion.normalClass t hn (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x w)⟩ :
      TotalSpace P fun s ↦ c.isImmersion.NormalSpace s hn) := by
  let := c.normalSpaceFiberBundle hn hdim
  -- The vertical vectors form a continuous path in the pulled-back tangent bundle.
  have hq : Continuous fun t : ℝ ↦ (⟨(t : AddCircle ((1 : ℕ) : ℝ)),
      mfderiv I (𝓘(ℝ).prod I) (mk φ t) x w⟩ :
        TotalSpace (ℝ × E) (⇑c *ᵖ (TangentSpace (𝓘(ℝ).prod I)))) :=
    Pullback.continuous_iff.2 ⟨AddCircle.continuous_mk' (p := ((1 : ℕ) : ℝ)),
      (continuous_mfderiv_mk φ x w).congr fun t ↦ TotalSpace.ext (hc t).symm HEq.rfl⟩
  refine ((c.contMDiff_normalQuotientMap hn (m := 0) (by simp) hdim).continuous.comp hq).congr
    fun t ↦ ?_
  rw [Function.comp_apply, SmoothEmbedding.normalQuotientMap_apply]

omit [IsManifold I ∞ M] in
/-- The normal space of a circle `t ↦ [t, x]` in the mapping torus has the dimension of `M`. -/
private theorem finrank_normalSpace_eq (s : AddCircle ((1 : ℕ) : ℝ)) :
    finrank ℝ E = finrank ℝ (c.isImmersion.NormalSpace s hn) := by
  rw [c.isImmersion.finrank_normalSpace s hn, finrank_tangentSpace, finrank_tangentSpace,
    finrank_prod, finrank_self, Nat.add_sub_cancel_left]

/-- The frame of the normal space of a circle `c : t ↦ [t, x]` at `[t, x]` formed by the normal
classes of the vertical vectors `d[t, ·]ₓ (b i)`, for a basis `b` of the model space. -/
private def normalFrame (hc : ∀ t : ℝ, c t = mk φ t x) {ι : Type*} (b : Basis ι ℝ E) (t : ℝ) :
    Basis ι ℝ (c.isImmersion.NormalSpace (t : AddCircle ((1 : ℕ) : ℝ)) hn) :=
  b.map ((verticalNormalMap hn t).linearEquivOfInjective
      (injective_verticalNormalMap hn hc t) (finrank_normalSpace_eq hn _))

private theorem normalFrame_apply (hc : ∀ t : ℝ, c t = mk φ t x) {ι : Type*} (b : Basis ι ℝ E)
    (t : ℝ) (i : ι) :
    normalFrame hn hc b t i =
      c.isImmersion.normalClass t hn (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x (b i)) := by
  rw [normalFrame, Basis.map_apply, LinearMap.linearEquivOfInjective_apply,
    verticalNormalMap_apply]

/-- **The seam of a circle in a mapping torus.** At `[t + 1, x] = [t, x]`, the frame at `t + 1` is
the frame at `t` composed with `dφₓ`, as vectors of the total space of the normal bundle. -/
private theorem totalSpaceMk_normalFrame_add_one (hc : ∀ t : ℝ, c t = mk φ t x) {ι : Type*}
    (b : Basis ι ℝ E) (D : E ≃ₗ[ℝ] E) (hD : ∀ w, D w = mfderiv I I φ x w) (t : ℝ) (i : ι)
    (P : Type*) :
    (⟨((t + 1 : ℝ) : AddCircle ((1 : ℕ) : ℝ)), normalFrame hn hc b (t + 1) i⟩ :
        TotalSpace P fun s ↦ c.isImmersion.NormalSpace s hn) =
      ⟨(t : AddCircle ((1 : ℕ) : ℝ)), normalFrame hn hc (b.map D) t i⟩ := by
  have hs : ((t + 1 : ℝ) : AddCircle ((1 : ℕ) : ℝ)) = t := by
    rw [← Nat.cast_one (R := ℝ)]
    exact AddCircle.coe_add_period _ t
  rw [normalFrame_apply, normalFrame_apply, Basis.map_apply, hD]
  -- Normal classes over equal points of the circle with the same representative agree, and
  -- `[t + 1, ·]` and `[t, φ ·]` have the same differential at the fixed point `x`.
  exact (congrArg (fun s ↦ (⟨s, c.isImmersion.normalClass s hn
    (mfderiv I (𝓘(ℝ).prod I) (mk φ (t + 1)) x (b i))⟩ :
      TotalSpace P fun s ↦ c.isImmersion.NormalSpace s hn)) hs).trans
    (congrArg (fun u : ℝ × E ↦ (⟨(t : AddCircle ((1 : ℕ) : ℝ)),
      c.isImmersion.normalClass t hn u⟩ : TotalSpace P fun s ↦ c.isImmersion.NormalSpace s hn))
      (mfderiv_mk_add_one_of_apply_eq φ hn (apply_eq_of_forall_eq_mk hc) t (b i)))

/-- The frames `normalFrame` vary continuously along the circle. -/
private theorem continuous_normalFrame (hc : ∀ t : ℝ, c t = mk φ t x)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hdim : finrank ℝ P = finrank ℝ (ℝ × E) - finrank ℝ ℝ) {ι : Type*} (b : Basis ι ℝ E)
    (i : ι) :
    letI := c.normalSpaceFiberBundle hn hdim
    Continuous fun t : ℝ ↦ (⟨(t : AddCircle ((1 : ℕ) : ℝ)), normalFrame hn hc b t i⟩ :
      TotalSpace P fun s ↦ c.isImmersion.NormalSpace s hn) :=
  (continuous_normalClass_mfderiv_mk hn hc hdim (b i)).congr fun _ ↦ by rw [normalFrame_apply]

/-- The model fibre of the normal bundle of a circle in the mapping torus has the dimension of the
model space of `M`. -/
private theorem finrank_eq_of_finrank_eq_sub {P : Type*} [AddCommGroup P] [Module ℝ P]
    (hdim : finrank ℝ P = finrank ℝ (ℝ × E) - finrank ℝ ℝ) : finrank ℝ P = finrank ℝ E := by
  rw [hdim, finrank_prod, finrank_self, Nat.add_sub_cancel_left]

/-- **The normal bundle of a circle in a mapping torus is orientable when `dφₓ` preserves
orientation.** Let `c` be an embedded circle `t ↦ [t, x]` in the mapping torus of `φ`, so that `x`
is fixed by `φ`. If `det dφₓ > 0`, the normal bundle of `c` is orientable. -/
theorem nonempty_vectorBundleOrientation_normalSpace_of_det_pos
    (hc : ∀ t : ℝ, c t = mk φ t x)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hdim : finrank ℝ P = finrank ℝ (ℝ × E) - finrank ℝ ℝ) {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = finrank ℝ E)
    (hdet : 0 < LinearMap.det ((mfderiv I I φ x).toLinearMap : E →ₗ[ℝ] E)) :
    letI := c.normalSpaceFiberBundle hn hdim
    letI := c.normalSpaceVectorBundle hn hdim
    Nonempty (VectorBundleOrientation P (fun s ↦ c.isImmersion.NormalSpace s hn) ι) := by
  classical
  let := c.normalSpaceFiberBundle hn hdim
  let := c.normalSpaceVectorBundle hn hdim
  let b : Basis ι ℝ E := (Module.finBasis ℝ E).reindex (Fintype.equivFinOfCardEq hι).symm
  let D := LinearMap.equivOfDetNeZero _ hdet.ne'
  let F (t : ℝ) : VectorBundleOrientationCover P (fun s ↦ c.isImmersion.NormalSpace s hn) ι :=
    ⟨t, (normalFrame hn hc b t).orientation⟩
  -- At the seam the frame comes back composed with `dφₓ`, which preserves its orientation.
  have hF : Periodic F ((1 : ℕ) : ℝ) := fun t ↦ by
    rw [show t + ((1 : ℕ) : ℝ) = t + 1 by norm_num]
    refine (VectorBundleOrientationCover.mk_orientation_eq_of_totalSpaceMk_eq (F := P)
      (E := fun s ↦ c.isImmersion.NormalSpace s hn) (by simp) _
      (normalFrame hn hc (b.map D) t) fun i ↦
      totalSpaceMk_normalFrame_add_one hn hc b D (fun _ ↦ rfl) t i P).trans ?_
    simp only [F, normalFrame, Basis.orientation_map]
    rw [(b.orientation_comp_linearEquiv_eq_iff_det_pos D).2 hdet]
  -- So the orientations of the frames descend to a continuous section of the orientation cover.
  refine (VectorBundleOrientation.nonempty_iff_exists_section
    (hι.trans (finrank_eq_of_finrank_eq_sub hdim).symm)).2
      ⟨hF.lift, (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 ?_, fun s ↦ ?_⟩
  · rw [hF.lift_comp_coe]
    exact VectorBundleOrientationCover.continuous_mk_basis_orientation
      (AddCircle.continuous_mk' (p := ((1 : ℕ) : ℝ))) _ (continuous_normalFrame hn hc hdim b)
  induction s using QuotientAddGroup.induction_on with | H t => rw [hF.lift_coe]

/-- **The normal bundle of a circle in a mapping torus is not orientable when `dφₓ` reverses
orientation.** Let `c` be an embedded circle `t ↦ [t, x]` in the mapping torus of `φ`, so that `x`
is fixed by `φ`. If `det dφₓ < 0`, the normal bundle of `c` is not orientable. -/
theorem isEmpty_vectorBundleOrientation_normalSpace_of_det_neg
    (hc : ∀ t : ℝ, c t = mk φ t x)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hdim : finrank ℝ P = finrank ℝ (ℝ × E) - finrank ℝ ℝ) {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = finrank ℝ E)
    (hdet : LinearMap.det ((mfderiv I I φ x).toLinearMap : E →ₗ[ℝ] E) < 0) :
    letI := c.normalSpaceFiberBundle hn hdim
    letI := c.normalSpaceVectorBundle hn hdim
    IsEmpty (VectorBundleOrientation P (fun s ↦ c.isImmersion.NormalSpace s hn) ι) := by
  classical
  let := c.normalSpaceFiberBundle hn hdim
  let := c.normalSpaceVectorBundle hn hdim
  let b : Basis ι ℝ E := (Module.finBasis ℝ E).reindex (Fintype.equivFinOfCardEq hι).symm
  let D := LinearMap.equivOfDetNeZero _ hdet.ne
  -- At the seam the frame comes back composed with `dφₓ`, which reverses its orientation.
  refine VectorBundleOrientation.isEmpty_of_continuous_basis
    (hι.trans (finrank_eq_of_finrank_eq_sub hdim).symm)
    (g := ((↑) : ℝ → AddCircle ((1 : ℕ) : ℝ))) (AddCircle.continuous_mk' (p := ((1 : ℕ) : ℝ)))
    (normalFrame hn hc b) (continuous_normalFrame hn hc hdim b) (x := 0) (y := 0 + 1) (by simp)
    (normalFrame hn hc (b.map D) 0)
    (fun i ↦ totalSpaceMk_normalFrame_add_one hn hc b D (fun _ ↦ rfl) 0 i P) ?_
  simp only [normalFrame, Basis.orientation_map]
  rw [(b.orientation_comp_linearEquiv_eq_neg_iff_det_neg D).2 hdet, Orientation.map_neg]

/-- **Orientability of the normal bundle of a circle in a mapping torus.** Let `c` be an embedded
circle `t ↦ [t, x]` in the mapping torus of `φ`, so that `x` is fixed by `φ`. The normal bundle of
`c` is orientable if and only if `dφₓ` preserves orientation, `det dφₓ > 0`. -/
theorem nonempty_vectorBundleOrientation_normalSpace_iff
    (hc : ∀ t : ℝ, c t = mk φ t x)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hdim : finrank ℝ P = finrank ℝ (ℝ × E) - finrank ℝ ℝ) {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = finrank ℝ E) :
    letI := c.normalSpaceFiberBundle hn hdim
    letI := c.normalSpaceVectorBundle hn hdim
    Nonempty (VectorBundleOrientation P (fun s ↦ c.isImmersion.NormalSpace s hn) ι) ↔
      0 < LinearMap.det ((mfderiv I I φ x).toLinearMap : E →ₗ[ℝ] E) := by
  refine ⟨fun ⟨o⟩ ↦ ?_, nonempty_vectorBundleOrientation_normalSpace_of_det_pos hn hc hdim hι⟩
  -- The differential of the diffeomorphism `φ` is invertible, so its determinant is not zero.
  have h0 : LinearMap.det ((mfderiv I I φ x).toLinearMap : E →ₗ[ℝ] E) ≠ 0 := by
    obtain ⟨e, he⟩ := φ.isInvertible_mfderiv hn (x := x)
    rw [← he]
    exact (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  exact h0.lt_or_gt.resolve_left fun hneg ↦
    (isEmpty_vectorBundleOrientation_normalSpace_of_det_neg hn hc hdim hι hneg).false o

end TauCeti.SmoothMappingTorus
