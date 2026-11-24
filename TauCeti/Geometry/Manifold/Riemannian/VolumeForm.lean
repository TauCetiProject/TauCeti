/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orientation
public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Basic
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# Riemannian volume forms

An orientation and a Riemannian metric determine a top-degree alternating form on every tangent
space.  This file packages Mathlib's oriented inner-product-space volume form fibrewise, giving the
pointwise object for the manifold divergence and Stokes identities.

The construction is total, as are the rough forms in the differential-form API.  Its defining
characterization is that it evaluates to `1` on every positively oriented orthonormal basis, so any
alternating top form bounded by `1` in absolute value on orthonormal frames is dominated pointwise
by the Riemannian volume form (`TauCeti.abs_apply_le_abs_riemannianVolumeForm`,
`TauCeti.abs_apply_le_riemannianVolumeForm`, `TauCeti.apply_le_riemannianVolumeForm`), and pulling
back along a map whose differential preserves orientations and inner products recovers the source
volume form (`TauCeti.mpullback_riemannianVolumeForm_apply_of_isOrientationPreservingAt`,
`TauCeti.mpullback_riemannianVolumeForm_of_isOrientationPreservingAt`).

For a `C^n` metric on a `C^(n+1)` manifold the volume form is a `C^n` form
(`TauCeti.isSmoothForm_riemannianVolumeForm`): in the frame of a tangent trivialization its value
is `±√(det g)`, the chart volume density `TauCeti.chartVolumeDensity`, with a sign that is
locally constant because the orientation is. On the coordinate frame of a chart this is
`TauCeti.exists_eventually_riemannianVolumeForm_chartLocalFrame_eq`; at every point of the chart
source the sign is the chart sign of an orientation lift
(`TauCeti.signBasis_mul_signAt_mul_riemannianVolumeForm_chartLocalFrame`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 15.29.  The normalization on positively oriented orthonormal bases is the
  characterization stated in that proposition.
-/

public section

noncomputable section

open Bundle
open scoped Manifold RealInnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {m : ℕ}

/-- The Riemannian volume form determined by an orientation, defined fibrewise on tangent spaces. -/
noncomputable def riemannianVolumeForm (o : Manifold.Orientation I M (Fin m)) :
    RoughForm I M ℝ m := fun x ↦
  let := o.fact_finrank_tangentSpace x
  (Manifold.Orientation.orientationAt o x).volumeFormL

/-- Unfolding the Riemannian volume form at a point exposes its oriented fibre form. -/
theorem riemannianVolumeForm_def
    (o : Manifold.Orientation I M (Fin m)) (x : M) :
    riemannianVolumeForm o x =
      (letI := o.fact_finrank_tangentSpace x
       (Manifold.Orientation.orientationAt o x).volumeFormL) := by
  simp only [riemannianVolumeForm]

/-- Evaluation of the Riemannian volume form is Mathlib's oriented volume form. -/
@[simp]
theorem riemannianVolumeForm_apply
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (v : Fin m → TangentSpace I x) :
    riemannianVolumeForm o x v =
      (letI := o.fact_finrank_tangentSpace x
       (Manifold.Orientation.orientationAt o x).volumeForm v) := by
  let := o.fact_finrank_tangentSpace x
  simp [riemannianVolumeForm]

/-- Reversing the manifold orientation negates the Riemannian volume form. -/
@[simp]
theorem riemannianVolumeForm_neg (o : Manifold.Orientation I M (Fin m)) :
    riemannianVolumeForm (-o) = -riemannianVolumeForm o := by
  ext x v
  let := o.fact_finrank_tangentSpace x
  let := (-o).fact_finrank_tangentSpace x
  simp [riemannianVolumeForm_apply, _root_.Orientation.volumeForm_neg_orientation]

/-- The volume form takes value `1` on a positively oriented orthonormal tangent basis. -/
theorem riemannianVolumeForm_apply_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x))
    (hb : b.toBasis.orientation = Manifold.Orientation.orientationAt o x) :
    riemannianVolumeForm o x b = 1 := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_def]
  exact Orientation.volumeFormL_apply_orthonormal _ b hb

/-- The Riemannian volume form takes value `1` on a positively oriented tangent `Module.Basis`
whose vectors are orthonormal. -/
theorem riemannianVolumeForm_apply_of_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : Module.Basis (Fin m) ℝ (TangentSpace I x))
    (hb : b.orientation = Manifold.Orientation.orientationAt o x)
    (horth : Orthonormal ℝ b) :
    riemannianVolumeForm o x b = 1 := by
  rw [← b.coe_toOrthonormalBasis horth]
  exact riemannianVolumeForm_apply_orthonormal o x (b.toOrthonormalBasis horth)
    (by rwa [b.toBasis_toOrthonormalBasis])

/-- The Riemannian volume form has absolute value one on every orthonormal basis. -/
theorem abs_riemannianVolumeForm_apply_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x)) :
    |riemannianVolumeForm o x b| = 1 := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_def]
  rw [Orientation.volumeFormL_apply]
  exact (Manifold.Orientation.orientationAt o x).abs_volumeForm_apply_of_orthonormal b

/-- The Riemannian volume form vanishes nowhere. -/
theorem riemannianVolumeForm_apply_ne_zero (o : Manifold.Orientation I M (Fin m)) (x : M) :
    riemannianVolumeForm o x ≠ 0 := by
  intro h
  let := o.fact_finrank_tangentSpace x
  let b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x) :=
    (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex (finCongr Fact.out)
  have habs := abs_riemannianVolumeForm_apply_orthonormal o x b
  rw [h, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, abs_zero] at habs
  exact zero_ne_one habs

/-- Because the Riemannian volume form vanishes nowhere, its topological support is the whole
manifold. -/
@[simp]
theorem tsupport_riemannianVolumeForm (o : Manifold.Orientation I M (Fin m)) :
    _root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) (riemannianVolumeForm o) = Set.univ :=
  Set.eq_univ_iff_forall.2 fun x ↦ subset_tsupport _ (riemannianVolumeForm_apply_ne_zero o x)

/-- The Riemannian volume form is negative on an oppositely oriented orthonormal basis. -/
theorem riemannianVolumeForm_apply_orthonormal_of_opposite
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x))
    (hb : b.toBasis.orientation ≠ Manifold.Orientation.orientationAt o x) :
    riemannianVolumeForm o x b = -1 := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_def]
  rw [Orientation.volumeFormL_apply]
  rw [(Manifold.Orientation.orientationAt o x).volumeForm_robust_neg b hb, neg_apply]
  simpa only [OrthonormalBasis.coe_toBasis] using congrArg Neg.neg b.toBasis.det_self

/-- A top form taking value one on an oriented orthonormal basis is the Riemannian volume form. -/
theorem eq_riemannianVolumeForm_of_apply_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (ω : TangentSpace I x [⋀^Fin m]→L[ℝ] ℝ)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x))
    (hb : b.toBasis.orientation = Manifold.Orientation.orientationAt o x)
    (hω : ω b = 1) :
    ω = riemannianVolumeForm o x := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_def]
  exact Orientation.eq_volumeFormL_of_apply_orthonormal _ ω b hb hω

/-- A top form taking value `1` on a positively oriented tangent `Module.Basis` whose vectors are
orthonormal is the Riemannian volume form. -/
theorem eq_riemannianVolumeForm_of_apply_of_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (ω : TangentSpace I x [⋀^Fin m]→L[ℝ] ℝ)
    (b : Module.Basis (Fin m) ℝ (TangentSpace I x))
    (hb : b.orientation = Manifold.Orientation.orientationAt o x)
    (horth : Orthonormal ℝ b) (hω : ω b = 1) :
    ω = riemannianVolumeForm o x :=
  eq_riemannianVolumeForm_of_apply_orthonormal o x ω (b.toOrthonormalBasis horth)
    (by rwa [b.toBasis_toOrthonormalBasis]) (by rwa [b.coe_toOrthonormalBasis])

/-- **Pointwise comass inequality** on arbitrary tangent `m`-tuples: in every degree `m : ℕ`, if a
continuous alternating form `ω` on `T_x M` has absolute value at most `1` on every orthonormal
`m`-frame, then `|ω(v)| ≤ |dvol_g(v)|` for every `v : Fin m → T_x M`. -/
theorem abs_apply_le_abs_riemannianVolumeForm
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (ω : TangentSpace I x [⋀^Fin m]→L[ℝ] ℝ)
    (hω : ∀ v : Fin m → TangentSpace I x, Orthonormal ℝ v → |ω v| ≤ 1)
    (v : Fin m → TangentSpace I x) :
    |ω v| ≤ |riemannianVolumeForm o x v| := by
  let := o.fact_finrank_tangentSpace x
  let b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x) :=
    (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex (finCongr Fact.out)
  have hωb : |ω b.toBasis| ≤ 1 := by
    rw [b.coe_toBasis]
    exact hω b b.orthonormal
  have hvolb : |riemannianVolumeForm o x b.toBasis| = 1 := by
    rw [b.coe_toBasis]
    exact abs_riemannianVolumeForm_apply_orthonormal o x b
  rw [ContinuousAlternatingMap.apply_eq_det_mul ω b.toBasis v,
    ContinuousAlternatingMap.apply_eq_det_mul (riemannianVolumeForm o x) b.toBasis v,
    abs_mul, abs_mul, hvolb, mul_one]
  exact mul_le_of_le_one_right (abs_nonneg _) hωb

/-- **Pointwise comass inequality** on positively oriented tangent bases: in every degree `m : ℕ`,
if `|ω(v)| ≤ 1` on every orthonormal `m`-frame `v` of `T_x M`, then `|ω(c)| ≤ dvol_g(c)` on every
positively oriented basis `c` of `T_x M`. -/
theorem abs_apply_le_riemannianVolumeForm
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (ω : TangentSpace I x [⋀^Fin m]→L[ℝ] ℝ)
    (hω : ∀ v : Fin m → TangentSpace I x, Orthonormal ℝ v → |ω v| ≤ 1)
    (c : Module.Basis (Fin m) ℝ (TangentSpace I x))
    (hc : c.orientation = Manifold.Orientation.orientationAt o x) :
    |ω c| ≤ riemannianVolumeForm o x c := by
  let := o.fact_finrank_tangentSpace x
  have hpos : 0 < riemannianVolumeForm o x c := by
    rw [riemannianVolumeForm_apply]
    exact _root_.Orientation.volumeForm_apply_pos_iff.2 hc
  exact (abs_apply_le_abs_riemannianVolumeForm o x ω hω c).trans_eq (abs_of_pos hpos)

/-- Signed pointwise comass inequality on positively oriented tangent bases: in every degree
`m : ℕ`, if `|ω(v)| ≤ 1` on every orthonormal `m`-frame `v` of `T_x M`, then `ω(c) ≤ dvol_g(c)` on
every positively oriented basis `c` of `T_x M`. -/
theorem apply_le_riemannianVolumeForm
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (ω : TangentSpace I x [⋀^Fin m]→L[ℝ] ℝ)
    (hω : ∀ v : Fin m → TangentSpace I x, Orthonormal ℝ v → |ω v| ≤ 1)
    (c : Module.Basis (Fin m) ℝ (TangentSpace I x))
    (hc : c.orientation = Manifold.Orientation.orientationAt o x) :
    ω c ≤ riemannianVolumeForm o x c :=
  (le_abs_self _).trans (abs_apply_le_riemannianVolumeForm o x ω hω c hc)

/-- At every point of an oriented Riemannian manifold with nonempty orientation index `ι`, there
exists a positively oriented tangent `Module.Basis` whose vectors are orthonormal. -/
theorem Manifold.Orientation.exists_basis_orientationAt_eq_and_orthonormal
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (o : Manifold.Orientation I M ι) (x : M) :
    ∃ b : Module.Basis ι ℝ (TangentSpace I x),
      b.orientation = o.orientationAt x ∧ Orthonormal ℝ b := by
  let : FiniteDimensional ℝ (TangentSpace I x) :=
    Module.finite_of_finrank_pos (o.finrank_tangentSpace_eq x ▸ Fintype.card_pos)
  let b := ((stdOrthonormalBasis ℝ (TangentSpace I x)).reindex
    (Fintype.equivFinOfCardEq (o.finrank_tangentSpace_eq x).symm).symm).adjustToOrientation
    (o.orientationAt x)
  refine ⟨b.toBasis,
    ((stdOrthonormalBasis ℝ (TangentSpace I x)).reindex _).orientation_adjustToOrientation _, ?_⟩
  rw [b.coe_toBasis]
  exact b.orthonormal

open scoped Classical in
/-- In dimension zero, the Riemannian volume form evaluates to `1` or `-1` according to whether the
tangent orientation is `positiveOrientation` or its opposite. -/
theorem riemannianVolumeForm_zeroDim_apply (o : Manifold.Orientation I M (Fin 0)) (x : M)
    (v : Fin 0 → TangentSpace I x) :
    riemannianVolumeForm o x v =
      if o.orientationAt x = positiveOrientation then 1 else -1 := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_apply]
  rcases (o.orientationAt x).eq_or_eq_neg_of_isEmpty with h | h
  · simp [h]
  · have hne : -(positiveOrientation : Orientation ℝ (TangentSpace I x) (Fin 0)) ≠
        positiveOrientation := (Module.Ray.ne_neg_self _).symm
    simp [h, hne]

/-- In dimension zero, the Riemannian volume form at `x` evaluates to `Orientation.signBasis` of the
tangent orientation relative to any `Fin 0` basis of the model space. -/
theorem riemannianVolumeForm_zeroDim_apply_eq_signBasis (o : Manifold.Orientation I M (Fin 0))
    (b : Module.Basis (Fin 0) ℝ E) (x : M) (v : Fin 0 → TangentSpace I x) :
    riemannianVolumeForm o x v = (Orientation.signBasis (o.orientationAt x) b : ℝ) := by
  classical
  -- `TangentSpace I x` is definitionally the model space `E`, so `b` is also a tangent basis.
  let bT : Module.Basis (Fin 0) ℝ (TangentSpace I x) := b
  have hs : (Orientation.signBasis (o.orientationAt x) b : ℝ) =
      (Orientation.signBasis (o.orientationAt x) bT : ℝ) := rfl
  rw [riemannianVolumeForm_zeroDim_apply, hs, ← bT.orientation_isEmpty]
  split_ifs with h
  · rw [h, _root_.Orientation.signBasis_orientation, Units.val_one, Int.cast_one]
  · have hneg : o.orientationAt x = -bT.orientation := by
      rcases (o.orientationAt x).eq_or_eq_neg_of_isEmpty with hpos | hneg
      · exact False.elim (h (hpos.trans bT.orientation_isEmpty.symm))
      · rwa [bT.orientation_isEmpty]
    rw [hneg, _root_.Orientation.signBasis_neg, _root_.Orientation.signBasis_orientation,
      Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]

/-- At a point where a map's differential preserves both the tangent orientations and the
Riemannian inner products, the pullback of the target Riemannian volume form recovers the source
Riemannian volume form. -/
theorem mpullback_riemannianVolumeForm_apply_of_isOrientationPreservingAt
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
    [FiniteDimensional ℝ E'] [IsManifold I' 1 M']
    [RiemannianBundle (fun y : M' ↦ TangentSpace I' y)]
    {o : Manifold.Orientation I M (Fin m)} {o' : Manifold.Orientation I' M' (Fin m)}
    {f : M → M'} {x : M} (ho : o.IsOrientationPreservingAt o' f x)
    (hinner : ∀ v w : TangentSpace I x,
      inner ℝ (mfderiv I I' f x v) (mfderiv I I' f x w) = inner ℝ v w) :
    mpullback I I' f (riemannianVolumeForm o') x = riemannianVolumeForm o x := by
  ext v
  let := o.fact_finrank_tangentSpace x
  let := o'.fact_finrank_tangentSpace (f x)
  obtain ⟨e, he, hmap⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).1 ho
  have he_apply (u : TangentSpace I x) : e u = mfderiv I I' f x u :=
    DFunLike.congr_fun he u
  let φ : TangentSpace I x ≃ₗᵢ[ℝ] TangentSpace I' (f x) :=
    e.toLinearEquiv.isometryOfInner fun u w ↦ by
      simpa only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, he_apply] using
        hinner u w
  have hcomp : (fun i ↦ mfderiv I I' f x (v i)) = φ ∘ v :=
    funext fun i ↦ (he_apply (v i)).symm
  have hsymm : φ.symm ∘ (φ ∘ v) = v := funext fun i ↦ φ.symm_apply_apply (v i)
  rw [mpullback_apply, riemannianVolumeForm_apply, riemannianVolumeForm_apply, hcomp, ← hmap]
  exact ((o.orientationAt x).volumeForm_map φ (φ ∘ v)).trans
    (congrArg (o.orientationAt x).volumeForm hsymm)

/-- Pulling back the Riemannian volume form along a map whose differential preserves both the
tangent orientations and the Riemannian inner products recovers the source Riemannian volume
form. -/
theorem mpullback_riemannianVolumeForm_of_isOrientationPreservingAt
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
    [FiniteDimensional ℝ E'] [IsManifold I' 1 M']
    [RiemannianBundle (fun y : M' ↦ TangentSpace I' y)]
    {o : Manifold.Orientation I M (Fin m)} {o' : Manifold.Orientation I' M' (Fin m)}
    {f : M → M'} (ho : ∀ x, o.IsOrientationPreservingAt o' f x)
    (hinner : ∀ x (v w : TangentSpace I x),
      inner ℝ (mfderiv I I' f x v) (mfderiv I I' f x w) = inner ℝ v w) :
    mpullback I I' f (riemannianVolumeForm o') = riemannianVolumeForm o :=
  funext fun x ↦ mpullback_riemannianVolumeForm_apply_of_isOrientationPreservingAt (ho x) (hinner x)

section Smooth

open Filter Module
open scoped Topology

open scoped Classical in
/-- The volume of the frame of a tangent trivialization: at a point `y` of the base set of the
trivialization `e` at `x`, the volume form on the basis `e.basisAt b` of the tangent space, for `b`
a reindexing of the standard basis of the model space, is `±√(det G)`, the chart volume density
up to sign, with sign `+` exactly when the frame is positively oriented. -/
private theorem riemannianVolumeForm_basisAt (o : Manifold.Orientation I M (Fin m))
    (σ : Fin (finrank ℝ E) ≃ Fin m) {x y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    riemannianVolumeForm o y
      ((trivializationAt E (TangentSpace I) x).basisAt ((Module.finBasis ℝ E).reindex σ) hy) =
      if ((Module.finBasis ℝ E).reindex σ).orientation =
          (trivializationAt E (TangentSpace I) x).mapOrientation (Fin m) hy (o.orientationAt y)
        then chartVolumeDensity (I := I) x y
        else -chartVolumeDensity (I := I) x y := by
  set e := trivializationAt E (TangentSpace I) x
  set b := (Module.finBasis ℝ E).reindex σ
  let := o.fact_finrank_tangentSpace y
  have hdet : (Matrix.gram ℝ (e.basisAt b hy)).det =
      (Riemannian.Tensor.chartGramMatrix (I := I) x y).det := by
    rw [Riemannian.Tensor.gram_basisAt_finBasis_reindex, Matrix.det_submatrix_equiv_self]
  have hor : (e.basisAt b hy).orientation = o.orientationAt y ↔
      b.orientation = e.mapOrientation (Fin m) hy (o.orientationAt y) := by
    rw [Trivialization.basisAt, Module.Basis.orientation_map, Trivialization.mapOrientation_apply,
      ← Orientation.map_symm, Equiv.symm_apply_eq]
  rw [riemannianVolumeForm_apply, chartVolumeDensity_def, ← hdet]
  split_ifs with h
  · exact (o.orientationAt y).volumeForm_apply_eq_sqrt_det_gram _ (hor.2 h)
  · exact (o.orientationAt y).volumeForm_apply_eq_neg_sqrt_det_gram _ (mt hor.1 h)

/-- **The volume form in a coordinate frame.** Near `x`, the volume form evaluated on the
coordinate frame of the chart at `x`, reindexed along `σ`, is `±√(det g)`: the chart volume
density times a sign that does not depend on the point. -/
theorem exists_eventually_riemannianVolumeForm_chartLocalFrame_eq
    (o : Manifold.Orientation I M (Fin m)) (σ : Fin (finrank ℝ E) ≃ Fin m) (x : M) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ᶠ y in 𝓝 x,
      riemannianVolumeForm o y (fun i ↦ Riemannian.Tensor.chartLocalFrame (I := I) x (σ.symm i) y) =
        c * chartVolumeDensity (I := I) x y := by
  classical
  set e := trivializationAt E (TangentSpace I) x
  set b := (Module.finBasis ℝ E).reindex σ
  have hm : finrank ℝ E = m := by simpa using o.card_eq.symm
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hframe (y : M) (hy : y ∈ e.baseSet) :
      (fun i ↦ Riemannian.Tensor.chartLocalFrame (I := I) x (σ.symm i) y) = e.basisAt b hy :=
    (Riemannian.Tensor.coe_basisAt_reindex_eq_chartLocalFrame σ x hy).symm
  have hconst := o.toVectorBundleOrientation.eventually_mapOrientation_eq (by simp [hm]) e hx
  simp only [Manifold.Orientation.toVectorBundleOrientation_apply] at hconst
  by_cases hP : b.orientation = e.mapOrientation (Fin m) hx (o.orientationAt x)
  · refine ⟨1, Or.inl rfl, ?_⟩
    filter_upwards [hconst, e.open_baseSet.mem_nhds hx] with y hy hyb
    rw [hframe y hyb, riemannianVolumeForm_basisAt o σ hyb, hy hyb, ite_eq_left hP, one_mul]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    filter_upwards [hconst, e.open_baseSet.mem_nhds hx] with y hy hyb
    rw [hframe y hyb, riemannianVolumeForm_basisAt o σ hyb, hy hyb, ite_eq_right hP, neg_one_mul]

/-- **The volume of a coordinate frame.** At every point `y` of the chart source at `x`, the
volume form evaluated on the coordinate frame of the chart at `x`, reindexed along `σ`, has
absolute value `√(det g)`, the chart volume density, whatever the orientation of the frame. -/
theorem abs_riemannianVolumeForm_chartLocalFrame (o : Manifold.Orientation I M (Fin m))
    (σ : Fin (finrank ℝ E) ≃ Fin m) {x y : M} (hy : y ∈ (chartAt H x).source) :
    |riemannianVolumeForm o y (fun i ↦ Riemannian.Tensor.chartLocalFrame (I := I) x (σ.symm i) y)| =
      chartVolumeDensity (I := I) x y := by
  have hy' : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have hframe : (fun i ↦ Riemannian.Tensor.chartLocalFrame (I := I) x (σ.symm i) y) =
      (trivializationAt E (TangentSpace I) x).basisAt ((Module.finBasis ℝ E).reindex σ) hy' :=
    (Riemannian.Tensor.coe_basisAt_reindex_eq_chartLocalFrame σ x hy').symm
  rw [hframe, riemannianVolumeForm_basisAt o σ hy']
  split_ifs
  · exact abs_of_nonneg (chartVolumeDensity_nonneg x y)
  · rw [abs_neg, abs_of_nonneg (chartVolumeDensity_nonneg x y)]

/-- **The signed volume of a coordinate frame.** At every point `y` of the chart source at `x`,
the volume form of the orientation of a lift `l`, evaluated on the coordinate frame of the chart at
`x` reindexed along `σ`, times the sign of the reindexed standard model basis against the model
orientation and the chart sign of `l` at `y`, is `√(det g)`, the chart volume density. This holds
in every dimension, including dimension `0`. -/
theorem signBasis_mul_signAt_mul_riemannianVolumeForm_chartLocalFrame
    (l : Manifold.OrientationLift I M (Fin m)) (σ : Fin (finrank ℝ E) ≃ Fin m) {x y : M}
    (hy : y ∈ (chartAt H x).source) :
    (Orientation.signBasis l.modelOrientation ((Module.finBasis ℝ E).reindex σ) : ℝ) *
        (l.signAt x y : ℝ) *
        riemannianVolumeForm (Manifold.Orientation.mk l) y
          (fun i ↦ Riemannian.Tensor.chartLocalFrame (I := I) x (σ.symm i) y) =
      chartVolumeDensity (I := I) x y := by
  classical
  set b := (Module.finBasis ℝ E).reindex σ
  have hy' : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have hframe : (fun i ↦ Riemannian.Tensor.chartLocalFrame (I := I) x (σ.symm i) y) =
      (trivializationAt E (TangentSpace I) x).basisAt b hy' :=
    (Riemannian.Tensor.coe_basisAt_reindex_eq_chartLocalFrame σ x hy').symm
  rw [hframe, riemannianVolumeForm_basisAt _ σ hy', Manifold.Orientation.orientationAt_mk,
    l.mapOrientation_orientationAt hy, l.chartOrientation_eq_ite, l.signAt_of_mem hy]
  -- Against either orientation `o` of the model, the sign of `b` matches the sign of the volume.
  have key (o : Orientation ℝ E (Fin m)) :
      (Orientation.signBasis o b : ℝ) *
        (if b.orientation = o then chartVolumeDensity (I := I) x y
          else -chartVolumeDensity (I := I) x y) = chartVolumeDensity (I := I) x y := by
    rcases b.orientation_eq_or_eq_neg o with rfl | rfl
    · simp [Orientation.signBasis_orientation]
    · have hne : b.orientation ≠ -b.orientation := Module.Ray.ne_neg_self _
      simp [hne, Orientation.signBasis_neg, Orientation.signBasis_orientation]
  rcases Int.units_eq_one_or (l.sign x ⟨y, hy⟩) with hs | hs
  · simpa [hs] using key l.modelOrientation
  · simpa [hs, Orientation.signBasis_neg] using key (-l.modelOrientation)

variable {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- **The Riemannian volume form is smooth**: for a `C^n` metric on a `C^(n+1)` manifold, the
volume form of an orientation is a `C^n` top form. -/
theorem isSmoothForm_riemannianVolumeForm (o : Manifold.Orientation I M (Fin m)) :
    IsSmoothForm I n (riemannianVolumeForm o) := by
  classical
  rw [isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply]
  intro x v
  set e := trivializationAt E (TangentSpace I) x
  have hm : finrank ℝ E = m := by simpa using o.card_eq.symm
  let σ : Fin (finrank ℝ E) ≃ Fin m := finCongr hm
  let b : Basis (Fin m) ℝ E := (Module.finBasis ℝ E).reindex σ
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hbase : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds hx
  -- The value on `e.symmL y ∘ v` is the volume of the coordinate frame times `b.det v`.
  have hval (y : M) : riemannianVolumeForm o y (e.symmL ℝ y ∘ v) =
      riemannianVolumeForm o y (fun i ↦ Riemannian.Tensor.chartLocalFrame (I := I) x (σ.symm i) y) *
        b.det v := by
    have h := ContinuousAlternatingMap.apply_eq_det_mul
      ((riemannianVolumeForm o y).compContinuousLinearMap (e.symmL ℝ y)) b v
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
    rw [h, mul_comm]
    congr 2
    funext i
    rw [Function.comp_apply, Module.Basis.reindex_apply, Riemannian.Tensor.chartLocalFrame_eq_symmL]
  -- Near `x`, that volume is `±chartVolumeDensity` with a constant sign, and the chart volume
  -- density is `C^n`.
  have hρ : ContMDiffAt I 𝓘(ℝ) n (chartVolumeDensity (I := I) x) x :=
    (contMDiffOn_chartVolumeDensity (I := I) x).contMDiffAt hbase
  obtain ⟨c, -, hc⟩ := exists_eventually_riemannianVolumeForm_chartLocalFrame_eq o σ x
  refine (((contMDiffAt_const (c := c)).mul hρ).mul
    (contMDiffAt_const (c := b.det v))).congr_of_eventuallyEq ?_
  filter_upwards [hc] with y hy
  rw [Pi.mul_apply, Pi.mul_apply, hval y, hy]

end Smooth

end TauCeti
