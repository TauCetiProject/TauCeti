/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# O'Neill's mixed and Codazzi-type curvature equations for a Riemannian submersion

For a smooth Riemannian submersion `f : M → N`, let `h` and `v` be the horizontal and vertical
orthogonal projections on `TM`, and let `A` and `T` be O'Neill's fundamental tensors
(`IsRiemannianSubmersion.oneillA` and `IsRiemannianSubmersion.oneillT`). With the curvature sign
convention `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z` and
`Rm(u, v, w, z) = ⟪R(u, v) w, z⟫_ℝ`, the off-block and mixed components of the curvature of `M`
are expressed in terms of `A`, `T`, and their Hom-bundle covariant derivatives `∇ A` and `∇ T`:

* **Vertical-horizontal Codazzi equation (`{1}`).** For vertical `u, v, w` and horizontal `z`,
  `Rm_M(u, v, w, z) = ⟪(∇_u T)(v, w), z⟫ - ⟪(∇_v T)(u, w), z⟫`.
* **Horizontal-vertical equation (`{4}`).** For horizontal `u, v, w` and vertical `z`,
  `Rm_M(u, v, w, z) = -⟪(∇_w A)(u, v), z⟫ - ⟪A_u v, T_z w⟫ + ⟪A_v w, T_z u⟫ + ⟪A_w u, T_z v⟫`.
* **Mixed curvature (`{2}`) and vertico-horizontal sectional curvature.** For horizontal `u, z`
  and vertical `v, w`,
  `Rm_M(u, v, w, z) = ⟪(∇_u T)(v, w), z⟫ - ⟪(∇_v A)(u, w), z⟫ + ⟪A_u v, A_z w⟫ - ⟪T_v u, T_w z⟫`.
  Specializing to `z = u` and `w = v` (where `⟪(∇_v A)(u, v), u⟫ = 0` by skew-adjointness of `A`
  and metric compatibility) gives
  `K_M(u, v) = (⟪(∇_u T)(v, v), u⟫ + ‖A_u v‖² - ‖T_v u‖²) / (‖u‖² * ‖v‖²)`.
  When the fibres are totally geodesic near the point (`∀ᶠ y in 𝓝 x, T_y = 0`),
  `K_M(u, v) = ‖A_u v‖² / (‖u‖² * ‖v‖²) ≥ 0`.

## Main results

* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_hom_oneillA_apply`,
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_hom_oneillT_apply`: pointwise evaluation of
  the induced Hom-bundle covariant derivatives `∇ A` and `∇ T`.
* `TauCeti.IsRiemannianSubmersion.riemannCurvatureTensor_of_mem_ker_of_mem_orthogonal_ker`:
  O'Neill's vertical-horizontal Codazzi equation `{1}`.
* `TauCeti.IsRiemannianSubmersion.riemannCurvatureTensor_of_mem_orthogonal_ker_of_mem_ker`:
  O'Neill's horizontal-vertical equation `{4}`.
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker`:
  O'Neill's vertico-horizontal sectional curvature formula (derived from `{2}`) and its
  specialization to totally geodesic fibres.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Theorem 2 (`{1}`, `{2}`, `{4}`) and Corollary 1(2)–(3).
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §C, 9.28b–e and 9.29b–c.
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Manifold VectorField
open scoped ContDiff InnerProductSpace Manifold Matrix Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

-- Regularity indices propositionally equal to `∞` or `2`.
private local instance : IsManifold I (∞ + 1) M := by
  simpa using (inferInstance : IsManifold I ∞ M)

private local instance : IsManifold I ((1 : ℕ∞ω) + 1) M := by
  rw [one_add_one_eq_two]
  exact .of_le (by norm_cast)

private local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

private local instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

include h

/-! ### Covariant derivatives of O'Neill's tensors and vertical Codazzi equation (`{1}`) -/

section TensorDerivatives

variable [T2Space M] {x : M}

/-- Every vertical tangent vector extends to a globally smooth vertical vector field. -/
private theorem exists_contMDiff_mem_ker_eq {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) :
    ∃ V : Π y : M, TangentSpace I y, CMDiff ∞ (T% V) ∧ V x = v ∧
      ∀ y, V y ∈ (mfderiv I J f y).ker := by
  obtain ⟨V₀, hV₀, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  refine ⟨fun y ↦ (mfderiv I J f y).ker.starProjection (V₀ y),
    (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply hV₀,
    Submodule.starProjection_eq_self_iff.mpr hv,
    fun _ ↦ Submodule.starProjection_apply_mem _ _⟩

/-- Evaluation of the induced Hom-bundle covariant derivative of O'Neill's horizontal tensor `A`:
`((∇_w A) U) V = ∇_w (A_U V) - A_(∇_w U) V - A_U (∇_w V)`. -/
theorem leviCivitaConnection_hom_oneillA_apply {U V : Π y : M, TangentSpace I y}
    (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) (w : TangentSpace I x) :
    (((leviCivitaConnection I M).hom
        ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
      h.oneillA x w) (U x) (V x) =
      leviCivitaConnection I M (fun y ↦ h.oneillA y (U y) (V y)) x w -
        h.oneillA x (leviCivitaConnection I M U x w) (V x) -
        h.oneillA x (U x) (leviCivitaConnection I M V x w) := by
  let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
  have hA := (h.contMDiff_oneillA x).mdifferentiableAt (by simp)
  rw [hom_apply _ _ hA hU, sub_apply, hom_apply _ _ (hA.clm_bundle_apply hU) hV]
  abel

/-- Evaluation of the induced Hom-bundle covariant derivative of O'Neill's vertical tensor `T`:
`((∇_w T) U) V = ∇_w (T_U V) - T_(∇_w U) V - T_U (∇_w V)`. -/
theorem leviCivitaConnection_hom_oneillT_apply {U V : Π y : M, TangentSpace I y}
    (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) (w : TangentSpace I x) :
    (((leviCivitaConnection I M).hom
        ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
      h.oneillT x w) (U x) (V x) =
      leviCivitaConnection I M (fun y ↦ h.oneillT y (U y) (V y)) x w -
        h.oneillT x (leviCivitaConnection I M U x w) (V x) -
        h.oneillT x (U x) (leviCivitaConnection I M V x w) := by
  let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
  have hT := (h.contMDiff_oneillT x).mdifferentiableAt (by simp)
  rw [hom_apply _ _ hT hU, sub_apply, hom_apply _ _ (hT.clm_bundle_apply hU) hV]
  abel

/-- Horizontal projection of an iterated derivative `∇_A (∇_B W)` of vertical vector fields. -/
private theorem starProjection_orthogonal_ker_iterated_mem_ker
    {A B W : Π y : M, TangentSpace I y} (hB : CMDiff ∞ (T% B)) (hW : CMDiff ∞ (T% W))
    (hAx : A x ∈ (mfderiv I J f x).ker) (hBv : ∀ y, B y ∈ (mfderiv I J f y).ker)
    (hWv : ∀ y, W y ∈ (mfderiv I J f y).ker) :
    (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M (fun y ↦ leviCivitaConnection I M W y (B y)) x (A x)) =
      (mfderiv I J f x).kerᗮ.starProjection
          ((((leviCivitaConnection I M).hom
              ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
            h.oneillT x (A x)) (B x) (W x)) +
        h.oneillT x ((mfderiv I J f x).ker.starProjection
          (leviCivitaConnection I M B x (A x))) (W x) +
        h.oneillT x (B x) ((mfderiv I J f x).ker.starProjection
          (leviCivitaConnection I M W x (A x))) +
        h.oneillT x (A x) ((mfderiv I J f x).ker.starProjection
          (leviCivitaConnection I M W x (B x))) := by
  have hTW : CMDiff ∞ (T% (fun y ↦ h.oneillT y (B y) (W y))) :=
    (h.contMDiff_oneillT.clm_bundle_apply hB).clm_bundle_apply hW
  have hVW : CMDiff ∞ (T% (fun y ↦ (mfderiv I J f y).ker.starProjection
      (leviCivitaConnection I M W y (B y)))) :=
    (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply
      ((leviCivitaConnection I M).contMDiff_apply hB hW)
  have hsplit : (fun y ↦ leviCivitaConnection I M W y (B y)) =
      (fun y ↦ h.oneillT y (B y) (W y)) +
        fun y ↦ (mfderiv I J f y).ker.starProjection (leviCivitaConnection I M W y (B y)) :=
    funext fun y ↦ h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker
      ((hW y).mdifferentiableAt (by simp)) (.of_forall hWv) (hBv y)
  have ht1 := h.oneillT_apply_of_eventually_mem_ker ((hVW x).mdifferentiableAt (by simp))
    (.of_forall fun y ↦ Submodule.starProjection_apply_mem _ _) (A x)
  rw [Submodule.starProjection_eq_self_iff.mpr hAx] at ht1
  have hhom := congrArg (mfderiv I J f x).kerᗮ.starProjection
    (h.leviCivitaConnection_hom_oneillT_apply
      ((hB x).mdifferentiableAt (by simp)) ((hW x).mdifferentiableAt (by simp)) (A x))
  have htW : (mfderiv I J f x).kerᗮ.starProjection
      (h.oneillT x (B x) (leviCivitaConnection I M W x (A x))) =
      h.oneillT x (B x) ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M W x (A x))) := by
    conv_lhs =>
      rw [← Submodule.starProjection_add_starProjection_orthogonal
        (K := (mfderiv I J f x).ker) (leviCivitaConnection I M W x (A x))]
    have hz0 : (mfderiv I J f x).kerᗮ.starProjection
        (h.oneillT x (B x) ((mfderiv I J f x).kerᗮ.starProjection
          (leviCivitaConnection I M W x (A x)))) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).mpr <| by
        rw [Submodule.orthogonal_orthogonal]
        exact h.oneillT_apply_mem_ker _ (Submodule.starProjection_apply_mem _ _)
    rw [map_add, map_add, hz0, add_zero, Submodule.starProjection_eq_self_iff.mpr
      (h.oneillT_apply_mem_orthogonal_ker _ (Submodule.starProjection_apply_mem _ _))]
  rw [map_sub, map_sub, ← h.oneillT_starProjection_ker x (leviCivitaConnection I M B x (A x)),
    Submodule.starProjection_eq_self_iff.mpr
      (h.oneillT_apply_mem_orthogonal_ker _ (hWv x)), htW] at hhom
  have hhom' := eq_add_of_sub_eq (eq_add_of_sub_eq hhom.symm)
  rw [hsplit, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      ((hTW x).mdifferentiableAt (by simp)) ((hVW x).mdifferentiableAt (by simp)),
    add_apply, map_add, ← ht1, hhom']
  abel

/-- **O'Neill's equation `{1}` (horizontal projection).** For vertical vectors `u, v, w`,
`h (R_M(u, v) w) = h ((∇_u T)(v, w) - (∇_v T)(u, w))`. -/
theorem starProjection_orthogonal_ker_curvatureTensor_of_mem_ker
    {u v w : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker)
    (hv : v ∈ (mfderiv I J f x).ker) (hw : w ∈ (mfderiv I J f x).ker) :
    (mfderiv I J f x).kerᗮ.starProjection
        ((leviCivitaConnection I M).curvatureTensor x u v w) =
      (mfderiv I J f x).kerᗮ.starProjection
        ((((leviCivitaConnection I M).hom
            ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillT x u) v w -
        (((leviCivitaConnection I M).hom
            ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillT x v) u w) := by
  obtain ⟨U, hU, hUx, hUv⟩ := h.exists_contMDiff_mem_ker_eq hu
  obtain ⟨V, hV, hVx, hVv⟩ := h.exists_contMDiff_mem_ker_eq hv
  obtain ⟨W, hW, hWx, hWv⟩ := h.exists_contMDiff_mem_ker_eq hw
  have hUVv : mlieBracket I U V x ∈ (mfderiv I J f x).ker :=
    (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv
      (by simp [minSmoothness_of_isRCLikeNormedField])
      ((hU x).mdifferentiableAt (by simp)) ((hV x).mdifferentiableAt (by simp))
      (.of_forall hUv) (.of_forall hVv)
  have hT_tor := ((torsion_eq_zero_iff _).mp (torsion_leviCivitaConnection_eq_zero I))
    ((hU x).mdifferentiableAt (by simp)) ((hV x).mdifferentiableAt (by simp))
  have hbr : (mfderiv I J f x).kerᗮ.starProjection
      (leviCivitaConnection I M W x (mlieBracket I U V x)) =
      h.oneillT x ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M V x (U x))) (W x) -
      h.oneillT x ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M U x (V x))) (W x) := by
    have ht := h.oneillT_apply_of_eventually_mem_ker ((hW x).mdifferentiableAt (by simp))
      (.of_forall hWv) (mlieBracket I U V x)
    rw [Submodule.starProjection_eq_self_iff.mpr hUVv] at ht
    rw [← ht, ← Submodule.starProjection_eq_self_iff.mpr hUVv, ← hT_tor, map_sub, map_sub,
      sub_apply, h.oneillT_starProjection_ker, h.oneillT_starProjection_ker]
  rw [← hUx, ← hVx, ← hWx, (leviCivitaConnection I M).curvatureTensor_apply x hU hV hW,
    curvatureOperator_apply, map_sub, map_sub,
    h.starProjection_orthogonal_ker_iterated_mem_ker hV hW (hUv x) hVv hWv,
    h.starProjection_orthogonal_ker_iterated_mem_ker hU hW (hVv x) hUv hWv,
    hbr, map_sub]
  abel

/-- **O'Neill's equation `{1}` (Codazzi equation of the fibres).** For vertical vectors `u, v, w`
and a horizontal vector `z`,
`Rm_M(u, v, w, z) = ⟪(∇_u T)(v, w), z⟫ - ⟪(∇_v T)(u, w), z⟫`. -/
theorem riemannCurvatureTensor_of_mem_ker_of_mem_orthogonal_ker
    {u v w z : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker)
    (hv : v ∈ (mfderiv I J f x).ker) (hw : w ∈ (mfderiv I J f x).ker)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection I M).riemannCurvatureTensor x u v w z =
      ⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillT x u) v w, z⟫_ℝ -
      ⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillT x v) u w, z⟫_ℝ := by
  have hz' : (mfderiv I J f x).kerᗮ.starProjection z = z :=
    Submodule.starProjection_eq_self_iff.mpr hz
  rw [riemannCurvatureTensor_apply]
  conv_lhs => rw [← hz', ← Submodule.inner_starProjection_left_eq_right]
  rw [h.starProjection_orthogonal_ker_curvatureTensor_of_mem_ker hu hv hw,
    Submodule.inner_starProjection_left_eq_right, hz', inner_sub_left]

/-- On horizontal `v, w` and vertical `z`, `⟪(∇_u A)(v, w), z⟫` is alternating in `(v, w)`. -/
private theorem inner_leviCivitaConnection_hom_oneillA_antisymm
    (u : TangentSpace I x) {v w z : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).ker) :
    ⟪(((leviCivitaConnection I M).hom
        ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
      h.oneillA x u) v w, z⟫_ℝ =
      -⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x u) w v, z⟫_ℝ := by
  have hP := h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)
  obtain ⟨V₀, hV₀, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  obtain ⟨W₀, hW₀, rfl⟩ := exists_contMDiff_section_eq I E ∞ w
  set V : Π y : M, TangentSpace I y := fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (V₀ y)
  set W : Π y : M, TangentSpace I y := fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (W₀ y)
  have hVd : MDiffAt (T% V) x := ((hP x).clm_bundle_apply (hV₀ x)).mdifferentiableAt (by simp)
  have hWd : MDiffAt (T% W) x := ((hP x).clm_bundle_apply (hW₀ x)).mdifferentiableAt (by simp)
  have hVx : V x = V₀ x := Submodule.starProjection_eq_self_iff.mpr hv
  have hWx : W x = W₀ x := Submodule.starProjection_eq_self_iff.mpr hw
  have hsum : (fun y ↦ h.oneillA y (V y) (W y)) + (fun y ↦ h.oneillA y (W y) (V y)) = 0 :=
    funext fun y ↦ add_eq_zero_iff_eq_neg.mpr
      (h.oneillA_antisymm (Submodule.starProjection_apply_mem _ _)
        (Submodule.starProjection_apply_mem _ _))
  have hAVW : MDiffAt (T% (fun y ↦ h.oneillA y (V y) (W y))) x :=
    (((h.contMDiff_oneillA x).mdifferentiableAt (by simp)).clm_bundle_apply hVd).clm_bundle_apply
      hWd
  have hAWV : MDiffAt (T% (fun y ↦ h.oneillA y (W y) (V y))) x :=
    (((h.contMDiff_oneillA x).mdifferentiableAt (by simp)).clm_bundle_apply hWd).clm_bundle_apply
      hVd
  have hd : leviCivitaConnection I M (fun y ↦ h.oneillA y (V y) (W y)) x u +
      leviCivitaConnection I M (fun y ↦ h.oneillA y (W y) (V y)) x u = 0 := by
    have h0 := (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add hAVW hAWV
    rw [hsum, CovariantDerivative.zero] at h0
    simpa only [add_apply, Pi.zero_apply, zero_apply] using (congrArg (fun L ↦ L u) h0).symm
  have horth : ∀ (a b : TangentSpace I x),
      ⟪h.oneillA x a b, z⟫_ℝ =
        ⟪h.oneillA x a ((mfderiv I J f x).kerᗮ.starProjection b), z⟫_ℝ := by
    intro a b
    conv_lhs =>
      rw [← Submodule.starProjection_add_starProjection_orthogonal (K := (mfderiv I J f x).ker) b]
    rw [map_add, inner_add_left,
      (real_inner_comm _ _).trans (Submodule.inner_right_of_mem_orthogonal hz
        (h.oneillA_apply_mem_orthogonal_ker a (Submodule.starProjection_apply_mem _ _))),
      zero_add]
  have hanti : ∀ (q r : TangentSpace I x), r ∈ (mfderiv I J f x).kerᗮ →
      h.oneillA x q r + h.oneillA x r ((mfderiv I J f x).kerᗮ.starProjection q) = 0 := by
    intro q r hr
    rw [← h.oneillA_starProjection_orthogonal_ker x q,
      h.oneillA_antisymm (Submodule.starProjection_apply_mem _ _) hr, neg_add_cancel]
  rw [← hVx, ← hWx, h.leviCivitaConnection_hom_oneillA_apply hVd hWd u,
    h.leviCivitaConnection_hom_oneillA_apply hWd hVd u]
  simp only [inner_sub_left]
  rw [horth (V x), horth (W x)]
  have hc1 := congrArg (fun q ↦ ⟪q, z⟫_ℝ)
    (hanti (leviCivitaConnection I M V x u) (W x) (hWx.symm ▸ hw))
  have hc2 := congrArg (fun q ↦ ⟪q, z⟫_ℝ)
    (hanti (leviCivitaConnection I M W x u) (V x) (hVx.symm ▸ hv))
  have hc3 := congrArg (fun q ↦ ⟪q, z⟫_ℝ) hd
  simp only [inner_add_left, inner_zero_left] at hc1 hc2 hc3
  linarith

end TensorDerivatives

/-! ### Horizontal-vertical and mixed curvature equations (`{4}` and `{2}`) -/

section MixedCurvature

variable [T2Space M] [T2Space N] {x : M}

omit [T2Space N] in
/-- Vertical projection of an iterated derivative `∇_{A'} (∇_{B'} Z')` of basic horizontal
fields. -/
private theorem starProjection_ker_iterated_horizontalLift
    (A : Π y : N, TangentSpace J y) {B Z : Π y : N, TangentSpace J y}
    (hB : CMDiff ∞ (T% B)) (hZ : CMDiff ∞ (T% Z)) :
    (mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M
          (fun y ↦ leviCivitaConnection I M
            (fun z ↦ h.horizontalLift z (Z (f z))) y (h.horizontalLift y (B (f y)))) x
          (h.horizontalLift x (A (f x)))) =
      (mfderiv I J f x).ker.starProjection
          ((((leviCivitaConnection I M).hom
              ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
            h.oneillA x (h.horizontalLift x (A (f x))))
            (h.horizontalLift x (B (f x))) (h.horizontalLift x (Z (f x)))) +
        h.oneillA x (h.horizontalLift x (A (f x)))
          (h.horizontalLift x (leviCivitaConnection J N Z (f x) (B (f x)))) +
        h.oneillA x (h.horizontalLift x (leviCivitaConnection J N B (f x) (A (f x))))
          (h.horizontalLift x (Z (f x))) +
        h.oneillA x (h.horizontalLift x (B (f x)))
          (h.horizontalLift x (leviCivitaConnection J N Z (f x) (A (f x)))) := by
  let : IsManifold J 2 N := .of_le (n := ∞) (by norm_cast)
  set B' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B (f y))
  set Z' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Z (f y))
  have hB' : CMDiff ∞ (T% B') := h.contMDiff_horizontalLift hB (by simp)
  have hZ' : CMDiff ∞ (T% Z') := h.contMDiff_horizontalLift hZ (by simp)
  have hZB : CMDiff ∞ (T% (fun z ↦ leviCivitaConnection J N Z z (B z))) :=
    (leviCivitaConnection J N).contMDiff_apply hB hZ
  have hZB' : CMDiff ∞ (T% (fun y ↦ h.horizontalLift y
      (leviCivitaConnection J N Z (f y) (B (f y))))) :=
    h.contMDiff_horizontalLift hZB (by simp)
  have hABZ : CMDiff ∞ (T% (fun y ↦ h.oneillA y (B' y) (Z' y))) :=
    (h.contMDiff_oneillA.clm_bundle_apply hB').clm_bundle_apply hZ'
  have hsplit : (fun y ↦ leviCivitaConnection I M Z' y (B' y)) =
      (fun y ↦ h.horizontalLift y (leviCivitaConnection J N Z (f y) (B (f y)))) +
        fun y ↦ h.oneillA y (B' y) (Z' y) :=
    funext fun y ↦ h.leviCivitaConnection_horizontalLift ((hZ (f y)).of_le (by simp)) (B (f y))
  have ha1 := h.oneillA_apply_of_eventually_mem_orthogonal_ker
    ((hZB' x).mdifferentiableAt (by simp))
    (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
    (h.horizontalLift x (A (f x)))
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)] at ha1
  have hhom := congrArg (mfderiv I J f x).ker.starProjection
    (h.leviCivitaConnection_hom_oneillA_apply
      ((hB' x).mdifferentiableAt (by simp)) ((hZ' x).mdifferentiableAt (by simp))
      (h.horizontalLift x (A (f x))))
  have haB : (mfderiv I J f x).ker.starProjection
      (h.oneillA x (leviCivitaConnection I M B' x (h.horizontalLift x (A (f x)))) (Z' x)) =
      h.oneillA x (h.horizontalLift x (leviCivitaConnection J N B (f x) (A (f x)))) (Z' x) := by
    have ha0 : h.oneillA x (h.oneillA x (h.horizontalLift x (A (f x))) (B' x)) = 0 := by
      rw [← Submodule.starProjection_eq_self_iff.mpr
          (h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _)),
        h.oneillA_starProjection_ker]
    rw [h.leviCivitaConnection_horizontalLift ((hB (f x)).of_le (by simp)) (A (f x)),
      map_add, ha0, add_zero,
      Submodule.starProjection_eq_self_iff.mpr
        (h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _))]
  have haZ : (mfderiv I J f x).ker.starProjection
      (h.oneillA x (B' x) (leviCivitaConnection I M Z' x (h.horizontalLift x (A (f x))))) =
      h.oneillA x (B' x)
        (h.horizontalLift x (leviCivitaConnection J N Z (f x) (A (f x)))) := by
    rw [h.leviCivitaConnection_horizontalLift ((hZ (f x)).of_le (by simp)) (A (f x)),
      map_add, map_add,
      Submodule.starProjection_eq_self_iff.mpr
        (h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _)),
      (Submodule.starProjection_apply_eq_zero_iff _).mpr
        (h.oneillA_apply_mem_orthogonal_ker _
          (h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _))),
      add_zero]
  rw [map_sub, map_sub, haB, haZ] at hhom
  have hhom' := eq_add_of_sub_eq (eq_add_of_sub_eq hhom.symm)
  rw [hsplit, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      ((hZB' x).mdifferentiableAt (by simp)) ((hABZ x).mdifferentiableAt (by simp)),
    add_apply, map_add, ← ha1, hhom']
  abel

/-- **Vertical projection of horizontal `(1, 3)` curvature.** For horizontal vectors `u, v, w`,
`v (R_M(u, v) w) = v ((∇_u A)(v, w) - (∇_v A)(u, w)) - 2 T_(A_u v) w`. -/
theorem starProjection_ker_curvatureTensor_of_mem_orthogonal_ker
    {u v w : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    (mfderiv I J f x).ker.starProjection
        ((leviCivitaConnection I M).curvatureTensor x u v w) =
      (mfderiv I J f x).ker.starProjection
        ((((leviCivitaConnection I M).hom
            ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x u) v w -
        (((leviCivitaConnection I M).hom
            ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x v) u w) -
        (2 : ℝ) • h.oneillT x (h.oneillA x u v) w := by
  let : IsManifold J 2 N := .of_le (n := ∞) (by norm_cast)
  obtain ⟨X, hX, hXx⟩ := exists_contMDiff_section_eq J F ∞ (mfderiv I J f x u)
  obtain ⟨Y, hY, hYx⟩ := exists_contMDiff_section_eq J F ∞ (mfderiv I J f x v)
  obtain ⟨Z, hZ, hZx⟩ := exists_contMDiff_section_eq J F ∞ (mfderiv I J f x w)
  set X' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (X (f y))
  set Y' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Y (f y))
  set Z' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Z (f y))
  have hX' : CMDiff ∞ (T% X') := h.contMDiff_horizontalLift hX (by simp)
  have hY' : CMDiff ∞ (T% Y') := h.contMDiff_horizontalLift hY (by simp)
  have hZ' : CMDiff ∞ (T% Z') := h.contMDiff_horizontalLift hZ (by simp)
  have hX'x : X' x = u := by simp [X', hXx, h.horizontalLift_mfderiv_of_mem x hu]
  have hY'x : Y' x = v := by simp [Y', hYx, h.horizontalLift_mfderiv_of_mem x hv]
  have hZ'x : Z' x = w := by simp [Z', hZx, h.horizontalLift_mfderiv_of_mem x hw]
  have htorN := ((torsion_eq_zero_iff _).mp (torsion_leviCivitaConnection_eq_zero J))
    ((hX (f x)).mdifferentiableAt (by simp)) ((hY (f x)).mdifferentiableAt (by simp))
  have hbr : (mfderiv I J f x).ker.starProjection
      (leviCivitaConnection I M Z' x (mlieBracket I X' Y' x)) =
      h.oneillA x (h.horizontalLift x (mlieBracket J X Y (f x))) (Z' x) +
        (2 : ℝ) • h.oneillT x (h.oneillA x (X' x) (Y' x)) (Z' x) := by
    have haXY : (mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M Z' x (h.horizontalLift x (mlieBracket J X Y (f x)))) =
        h.oneillA x (h.horizontalLift x (mlieBracket J X Y (f x))) (Z' x) := by
      rw [h.leviCivitaConnection_horizontalLift ((hZ (f x)).of_le (by simp)),
        map_add, (Submodule.starProjection_apply_eq_zero_iff _).mpr
          (h.horizontalLift_mem_orthogonal_ker x _), zero_add,
        Submodule.starProjection_eq_self_iff.mpr
          (h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _))]
    have htXY : (mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M Z' x (h.oneillA x (X' x) (Y' x))) =
        h.oneillT x (h.oneillA x (X' x) (Y' x)) (Z' x) := by
      rw [h.leviCivitaConnection_horizontalLift_of_mem_ker ((hZ (f x)).of_le (by simp))
          (h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _)),
        map_add, (Submodule.starProjection_apply_eq_zero_iff _).mpr
          (h.oneillA_apply_mem_orthogonal_ker _
            (h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _))),
        zero_add, Submodule.starProjection_eq_self_iff.mpr
          (h.oneillT_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _))]
    rw [h.mlieBracket_horizontalLift ((hX (f x)).of_le (by simp)) ((hY (f x)).of_le (by simp)),
      map_add, map_smul, map_add, map_smul, haXY, htXY]
  rw [← hX'x, ← hY'x, ← hZ'x,
    (leviCivitaConnection I M).curvatureTensor_apply x hX' hY' hZ',
    curvatureOperator_apply, map_sub, map_sub,
    h.starProjection_ker_iterated_horizontalLift X hY hZ,
    h.starProjection_ker_iterated_horizontalLift Y hX hZ,
    hbr, ← htorN, map_sub, map_sub, sub_apply, map_sub]
  abel

/-- **O'Neill's equation `{4}`.** For horizontal vectors `u, v, w` and a vertical vector `z`,
`Rm_M(u, v, w, z) = -⟪(∇_w A)(u, v), z⟫ - ⟪A_u v, T_z w⟫ + ⟪A_v w, T_z u⟫ + ⟪A_w u, T_z v⟫`. -/
theorem riemannCurvatureTensor_of_mem_orthogonal_ker_of_mem_ker
    {u v w z : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).ker) :
    (leviCivitaConnection I M).riemannCurvatureTensor x u v w z =
      -⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x w) u v, z⟫_ℝ -
      ⟪h.oneillA x u v, h.oneillT x z w⟫_ℝ +
      ⟪h.oneillA x v w, h.oneillT x z u⟫_ℝ +
      ⟪h.oneillA x w u, h.oneillT x z v⟫_ℝ := by
  have htwo : ∀ (a b c : TangentSpace I x), a ∈ (mfderiv I J f x).kerᗮ →
      b ∈ (mfderiv I J f x).kerᗮ → c ∈ (mfderiv I J f x).kerᗮ →
      (leviCivitaConnection I M).riemannCurvatureTensor x a b c z =
        ⟪(((leviCivitaConnection I M).hom
            ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x a) b c, z⟫_ℝ -
        ⟪(((leviCivitaConnection I M).hom
            ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x b) a c, z⟫_ℝ -
        2 * ⟪h.oneillA x a b, h.oneillT x z c⟫_ℝ := by
    intro a b c ha hb hc
    have hz' : (mfderiv I J f x).ker.starProjection z = z :=
      Submodule.starProjection_eq_self_iff.mpr hz
    have ht : ⟪h.oneillT x (h.oneillA x a b) c, z⟫_ℝ = ⟪h.oneillA x a b, h.oneillT x z c⟫_ℝ := by
      rw [h.inner_oneillT, h.oneillT_comm (h.oneillA_apply_mem_ker a hb) hz,
        real_inner_comm, h.inner_oneillT, neg_neg]
    rw [riemannCurvatureTensor_apply]
    conv_lhs => rw [← hz', ← Submodule.inner_starProjection_left_eq_right]
    rw [h.starProjection_ker_curvatureTensor_of_mem_orthogonal_ker ha hb hc,
      inner_sub_left, Submodule.inner_starProjection_left_eq_right, hz', inner_sub_left,
      real_inner_smul_left, ht]
  have h1 := htwo u v w hu hv hw
  have h2 := htwo v w u hv hw hu
  have h3 := htwo w u v hw hu hv
  have hcyc := (leviCivitaConnection I M).riemannCurvatureTensor_cyclic_eq_zero
    (torsion_leviCivitaConnection_eq_zero I) x u v w z
  have ha1 := h.inner_leviCivitaConnection_hom_oneillA_antisymm u hw hv hz
  have ha2 := h.inner_leviCivitaConnection_hom_oneillA_antisymm v hw hu hz
  have ha3 := h.inner_leviCivitaConnection_hom_oneillA_antisymm w hv hu hz
  linarith

omit [T2Space M] [T2Space N] in
/-- Algebraic identity for `⟪A_(∇_v X') w, z⟫` along a vertical vector `v`, used in both `{2}` and
the vanishing of `⟪(∇_v A)(u, v), u⟫`. -/
private theorem inner_oneillA_leviCivitaConnection_horizontalLift_of_mem_ker
    {X : Π y : N, TangentSpace J y} (hX : CMDiffAt 1 (T% X) (f x))
    {v w z : TangentSpace I x} (hv : v ∈ (mfderiv I J f x).ker)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    ⟪h.oneillA x
        (leviCivitaConnection I M (fun y ↦ h.horizontalLift y (X (f y))) x v) w, z⟫_ℝ =
      -⟪h.oneillA x (h.horizontalLift x (X (f x))) v, h.oneillA x z w⟫_ℝ := by
  have ha0 : h.oneillA x (h.oneillT x v (h.horizontalLift x (X (f x)))) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr
        (h.oneillT_apply_mem_ker v (h.horizontalLift_mem_orthogonal_ker x _)),
      h.oneillA_starProjection_ker]
  rw [h.leviCivitaConnection_horizontalLift_of_mem_ker hX hv, map_add, ha0, add_zero,
    h.inner_oneillA, h.oneillA_antisymm (h.oneillA_apply_mem_orthogonal_ker _ hv) hz,
    inner_neg_right, neg_neg, real_inner_comm, h.inner_oneillA]

omit [T2Space N] in
/-- First iterated-derivative term `⟪∇_{X'} (∇_V W), z⟫` in O'Neill's mixed curvature equation
`{2}`. -/
private theorem inner_iterated_mem_ker_horizontalLift
    {X : Π y : N, TangentSpace J y} {V W : Π y : M, TangentSpace I y} {z : TangentSpace I x}
    (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W))
    (hVv : ∀ y, V y ∈ (mfderiv I J f y).ker) (hWv : ∀ y, W y ∈ (mfderiv I J f y).ker)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    ⟪leviCivitaConnection I M (fun y ↦ leviCivitaConnection I M W y (V y)) x
        (h.horizontalLift x (X (f x))), z⟫_ℝ =
      ⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillT x (h.horizontalLift x (X (f x)))) (V x) (W x), z⟫_ℝ +
      ⟪h.oneillT x ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M V x (h.horizontalLift x (X (f x))))) (W x), z⟫_ℝ +
      ⟪h.oneillT x (V x) ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M W x (h.horizontalLift x (X (f x))))), z⟫_ℝ -
      ⟪(mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x (V x)),
        h.oneillA x (h.horizontalLift x (X (f x))) z⟫_ℝ := by
  set u' := h.horizontalLift x (X (f x))
  have hTW : CMDiff ∞ (T% (fun y ↦ h.oneillT y (V y) (W y))) :=
    (h.contMDiff_oneillT.clm_bundle_apply hV).clm_bundle_apply hW
  have hVW : CMDiff ∞ (T% (fun y ↦ (mfderiv I J f y).ker.starProjection
      (leviCivitaConnection I M W y (V y)))) :=
    (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply
      ((leviCivitaConnection I M).contMDiff_apply hV hW)
  have hsplit : (fun y ↦ leviCivitaConnection I M W y (V y)) =
      (fun y ↦ h.oneillT y (V y) (W y)) +
        fun y ↦ (mfderiv I J f y).ker.starProjection (leviCivitaConnection I M W y (V y)) :=
    funext fun y ↦ h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker
      ((hW y).mdifferentiableAt (by simp)) (.of_forall hWv) (hVv y)
  have hhomT := congrArg (fun q ↦ ⟪q, z⟫_ℝ)
    (h.leviCivitaConnection_hom_oneillT_apply
      ((hV x).mdifferentiableAt (by simp)) ((hW x).mdifferentiableAt (by simp)) u')
  have htW : ⟪h.oneillT x (V x) (leviCivitaConnection I M W x u'), z⟫_ℝ =
      ⟪h.oneillT x (V x) ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M W x u')), z⟫_ℝ := by
    conv_lhs =>
      rw [← Submodule.starProjection_add_starProjection_orthogonal
        (K := (mfderiv I J f x).ker) (leviCivitaConnection I M W x u')]
    rw [map_add, inner_add_left,
      Submodule.inner_right_of_mem_orthogonal
        (h.oneillT_apply_mem_ker _ (Submodule.starProjection_apply_mem _ _)) hz,
      add_zero]
  have haVW : ⟪leviCivitaConnection I M
      (fun y ↦ (mfderiv I J f y).ker.starProjection (leviCivitaConnection I M W y (V y)))
        x u', z⟫_ℝ =
      -⟪(mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x (V x)),
        h.oneillA x u' z⟫_ℝ := by
    have hz' : (mfderiv I J f x).kerᗮ.starProjection z = z :=
      Submodule.starProjection_eq_self_iff.mpr hz
    conv_lhs => rw [← hz', ← Submodule.inner_starProjection_left_eq_right]
    have ha := h.oneillA_apply_of_eventually_mem_ker ((hVW x).mdifferentiableAt (by simp))
      (.of_forall fun y ↦ Submodule.starProjection_apply_mem _ _) u'
    rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)] at ha
    rw [← ha, h.inner_oneillA]
  rw [hsplit, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      ((hTW x).mdifferentiableAt (by simp)) ((hVW x).mdifferentiableAt (by simp)),
    add_apply, inner_add_left, haVW]
  simp only [inner_sub_left, ← h.oneillT_starProjection_ker x (leviCivitaConnection I M V x u'),
    htW] at hhomT
  linarith

omit [T2Space N] in
/-- Second iterated-derivative term `⟪∇_v (∇_{X'} W), z⟫` in O'Neill's mixed curvature equation
`{2}`. -/
private theorem inner_iterated_horizontalLift_mem_ker
    {X : Π y : N, TangentSpace J y} {W : Π y : M, TangentSpace I y} {v z : TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hW : CMDiff ∞ (T% W))
    (hv : v ∈ (mfderiv I J f x).ker) (hWv : ∀ y, W y ∈ (mfderiv I J f y).ker)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    ⟪leviCivitaConnection I M
        (fun y ↦ leviCivitaConnection I M W y (h.horizontalLift y (X (f y)))) x v, z⟫_ℝ =
      ⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x v) (h.horizontalLift x (X (f x))) (W x), z⟫_ℝ -
      ⟪h.oneillA x (h.horizontalLift x (X (f x))) v, h.oneillA x z (W x)⟫_ℝ -
      ⟪(mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x v),
        h.oneillA x (h.horizontalLift x (X (f x))) z⟫_ℝ +
      ⟪h.oneillT x v ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M W x (h.horizontalLift x (X (f x))))), z⟫_ℝ := by
  set X' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (X (f y))
  have hX' : CMDiff ∞ (T% X') := h.contMDiff_horizontalLift hX (by simp)
  have hAW : CMDiff ∞ (T% (fun y ↦ h.oneillA y (X' y) (W y))) :=
    (h.contMDiff_oneillA.clm_bundle_apply hX').clm_bundle_apply hW
  have hXW : CMDiff ∞ (T% (fun y ↦ (mfderiv I J f y).ker.starProjection
      (leviCivitaConnection I M W y (X' y)))) :=
    (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply
      ((leviCivitaConnection I M).contMDiff_apply hX' hW)
  have hsplit : (fun y ↦ leviCivitaConnection I M W y (X' y)) =
      (fun y ↦ h.oneillA y (X' y) (W y)) +
        fun y ↦ (mfderiv I J f y).ker.starProjection (leviCivitaConnection I M W y (X' y)) :=
    funext fun y ↦ h.leviCivitaConnection_of_eventually_mem_ker_of_mem_orthogonal_ker
      ((hW y).mdifferentiableAt (by simp)) (.of_forall hWv)
      (h.horizontalLift_mem_orthogonal_ker y _)
  have hhomA := congrArg (fun q ↦ ⟪q, z⟫_ℝ)
    (h.leviCivitaConnection_hom_oneillA_apply
      ((hX' x).mdifferentiableAt (by simp)) ((hW x).mdifferentiableAt (by simp)) v)
  have haX' : ⟪h.oneillA x (leviCivitaConnection I M X' x v) (W x), z⟫_ℝ =
      -⟪h.oneillA x (X' x) v, h.oneillA x z (W x)⟫_ℝ :=
    h.inner_oneillA_leviCivitaConnection_horizontalLift_of_mem_ker
      ((hX (f x)).of_le (by simp)) hv hz
  have haW' : ⟪h.oneillA x (X' x) (leviCivitaConnection I M W x v), z⟫_ℝ =
      -⟪(mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x v),
        h.oneillA x (X' x) z⟫_ℝ := by
    conv_lhs =>
      rw [h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker
        ((hW x).mdifferentiableAt (by simp)) (.of_forall hWv) hv]
    rw [map_add, inner_add_left,
      Submodule.inner_right_of_mem_orthogonal
        (h.oneillA_apply_mem_ker _ (h.oneillT_apply_mem_orthogonal_ker _ (hWv x))) hz,
      zero_add, h.inner_oneillA]
  have htXW : ⟪leviCivitaConnection I M
      (fun y ↦ (mfderiv I J f y).ker.starProjection (leviCivitaConnection I M W y (X' y)))
        x v, z⟫_ℝ =
      ⟪h.oneillT x v ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M W x (X' x))), z⟫_ℝ := by
    have hz' : (mfderiv I J f x).kerᗮ.starProjection z = z :=
      Submodule.starProjection_eq_self_iff.mpr hz
    conv_lhs => rw [← hz', ← Submodule.inner_starProjection_left_eq_right]
    have ht := h.oneillT_apply_of_eventually_mem_ker ((hXW x).mdifferentiableAt (by simp))
      (.of_forall fun y ↦ Submodule.starProjection_apply_mem _ _) v
    rw [Submodule.starProjection_eq_self_iff.mpr hv] at ht
    rw [← ht]
  rw [hsplit, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      ((hAW x).mdifferentiableAt (by simp)) ((hXW x).mdifferentiableAt (by simp)),
    add_apply, inner_add_left, htXW]
  simp only [inner_sub_left, haX', haW'] at hhomA
  linarith

/-- **O'Neill's equation `{2}` (mixed curvature).** For horizontal vectors `u, z` and vertical
vectors `v, w`,
`Rm_M(u, v, w, z) = ⟪(∇_u T)(v, w), z⟫ - ⟪(∇_v A)(u, w), z⟫ + ⟪A_u v, A_z w⟫ - ⟪T_v u, T_w z⟫`. -/
theorem riemannCurvatureTensor_of_mem_orthogonal_ker_of_mem_ker_of_mem_orthogonal_ker
    {u v w z : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).ker) (hw : w ∈ (mfderiv I J f x).ker)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection I M).riemannCurvatureTensor x u v w z =
      ⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillT x u) v w, z⟫_ℝ -
      ⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x v) u w, z⟫_ℝ +
      ⟪h.oneillA x u v, h.oneillA x z w⟫_ℝ -
      ⟪h.oneillT x v u, h.oneillT x w z⟫_ℝ := by
  obtain ⟨X, hX, hXx⟩ := exists_contMDiff_section_eq J F ∞ (mfderiv I J f x u)
  obtain ⟨V, hV, hVx, hVv⟩ := h.exists_contMDiff_mem_ker_eq hv
  obtain ⟨W, hW, hWx, hWv⟩ := h.exists_contMDiff_mem_ker_eq hw
  set X' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (X (f y))
  have hX' : CMDiff ∞ (T% X') := h.contMDiff_horizontalLift hX (by simp)
  have hX'x : X' x = u := by simp [X', hXx, h.horizontalLift_mfderiv_of_mem x hu]
  have hbr : ⟪leviCivitaConnection I M W x (mlieBracket I X' V x), z⟫_ℝ =
      ⟪h.oneillT x ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M V x (X' x))) (W x), z⟫_ℝ +
      ⟪h.oneillT x (V x) (X' x), h.oneillT x (W x) z⟫_ℝ := by
    have hz' : (mfderiv I J f x).kerᗮ.starProjection z = z :=
      Submodule.starProjection_eq_self_iff.mpr hz
    have hmem := h.mlieBracket_horizontalLift_mem_ker ((hX (f x)).of_le (by simp))
      ((hV x).mdifferentiableAt (by simp)) (.of_forall hVv)
    have ht := h.oneillT_apply_of_eventually_mem_ker ((hW x).mdifferentiableAt (by simp))
      (.of_forall hWv) (mlieBracket I X' V x)
    have ht2 : ⟪h.oneillT x (h.oneillT x (V x) (X' x)) (W x), z⟫_ℝ =
        -⟪h.oneillT x (V x) (X' x), h.oneillT x (W x) z⟫_ℝ := by
      rw [h.oneillT_comm (h.oneillT_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _))
          (hWv x),
        h.inner_oneillT]
    rw [Submodule.starProjection_eq_self_iff.mpr hmem] at ht
    conv_lhs => rw [← hz', ← Submodule.inner_starProjection_left_eq_right]
    rw [← ht, h.mlieBracket_horizontalLift_of_eventually_mem_ker ((hX (f x)).of_le (by simp))
        ((hV x).mdifferentiableAt (by simp)) (.of_forall hVv),
      map_sub, sub_apply, inner_sub_left, ht2, sub_neg_eq_add]
  rw [riemannCurvatureTensor_apply, ← hX'x, ← hVx, ← hWx,
    (leviCivitaConnection I M).curvatureTensor_apply x hX' hV hW,
    curvatureOperator_apply, inner_sub_left, inner_sub_left,
    h.inner_iterated_mem_ker_horizontalLift hV hW hVv hWv hz,
    h.inner_iterated_horizontalLift_mem_ker hX hW (hVv x) hWv hz, hbr]
  linarith

/-! ### Vertico-horizontal sectional curvature -/

/-- For horizontal `u` and vertical `v`, `⟪(∇_v A)(u, v), u⟫ = 0`. -/
private theorem inner_leviCivitaConnection_hom_oneillA_self_eq_zero
    {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).ker) :
    ⟪(((leviCivitaConnection I M).hom
        ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
      h.oneillA x v) u v, u⟫_ℝ = 0 := by
  obtain ⟨X, hX, hXx⟩ := exists_contMDiff_section_eq J F ∞ (mfderiv I J f x u)
  obtain ⟨V, hV, hVx, hVv⟩ := h.exists_contMDiff_mem_ker_eq hv
  set X' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (X (f y))
  have hX' : CMDiff ∞ (T% X') := h.contMDiff_horizontalLift hX (by simp)
  have hX'x : X' x = u := by simp [X', hXx, h.horizontalLift_mfderiv_of_mem x hu]
  have hAV : CMDiff ∞ (T% (fun y ↦ h.oneillA y (X' y) (V y))) :=
    (h.contMDiff_oneillA.clm_bundle_apply hX').clm_bundle_apply hV
  have hzero : (fun y ↦ ⟪h.oneillA y (X' y) (V y), X' y⟫_ℝ) = fun _ ↦ 0 := by
    funext y
    rw [h.inner_oneillA, h.oneillA_self (h.horizontalLift_mem_orthogonal_ker y _),
      inner_zero_right, neg_zero]
  have hm := (isMetricCompatible_leviCivitaConnection I (M := M))
    |>.inner_apply_add_inner_apply_eq_zero_of_eventuallyEq_const
      ((hAV x).mdifferentiableAt (by simp)) ((hX' x).mdifferentiableAt (by simp))
      (EventuallyEq.of_eq hzero) (V x)
  have hhom := congrArg (fun q ↦ ⟪q, X' x⟫_ℝ)
    (h.leviCivitaConnection_hom_oneillA_apply
      ((hX' x).mdifferentiableAt (by simp)) ((hV x).mdifferentiableAt (by simp)) (V x))
  have ha1 : ⟪h.oneillA x (leviCivitaConnection I M X' x (V x)) (V x), X' x⟫_ℝ =
      -‖h.oneillA x (X' x) (V x)‖ ^ 2 := by
    rw [h.inner_oneillA_leviCivitaConnection_horizontalLift_of_mem_ker
        ((hX (f x)).of_le (by simp)) (hVv x) (h.horizontalLift_mem_orthogonal_ker x _),
      real_inner_self_eq_norm_sq]
  have ha2 : ⟪h.oneillA x (X' x) (leviCivitaConnection I M V x (V x)), X' x⟫_ℝ = 0 := by
    rw [h.inner_oneillA, h.oneillA_self (h.horizontalLift_mem_orthogonal_ker x _),
      inner_zero_right, neg_zero]
  have ha3 : ⟪h.oneillA x (X' x) (V x), leviCivitaConnection I M X' x (V x)⟫_ℝ =
      ‖h.oneillA x (X' x) (V x)‖ ^ 2 := by
    rw [h.leviCivitaConnection_horizontalLift_of_mem_ker ((hX (f x)).of_le (by simp)) (hVv x),
      inner_add_right, real_inner_self_eq_norm_sq,
      (real_inner_comm _ _).trans (Submodule.inner_right_of_mem_orthogonal
        (h.oneillT_apply_mem_ker (V x) (h.horizontalLift_mem_orthogonal_ker x _))
        (h.oneillA_apply_mem_orthogonal_ker (X' x) (hVv x))),
      add_zero]
  rw [← hX'x, ← hVx]
  simp only [inner_sub_left] at hhom
  beta_reduce at hm
  linarith

/-- For a horizontal vector `u` and a vertical vector `v`,
`⟪R_M(u, v) v, u⟫ = ⟪(∇_u T)(v, v), u⟫ + ‖A_u v‖² - ‖T_v u‖²` (O'Neill, Corollary 1). -/
theorem inner_curvatureTensor_of_mem_orthogonal_ker_of_mem_ker_self
    {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).ker) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u v v, u⟫_ℝ =
      ⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillT x u) v v, u⟫_ℝ +
      ‖h.oneillA x u v‖ ^ 2 - ‖h.oneillT x v u‖ ^ 2 := by
  have hm :=
    h.riemannCurvatureTensor_of_mem_orthogonal_ker_of_mem_ker_of_mem_orthogonal_ker hu hv hv hu
  rw [riemannCurvatureTensor_apply, h.inner_leviCivitaConnection_hom_oneillA_self_eq_zero hu hv,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hm
  linarith

/-- **O'Neill's vertico-horizontal sectional curvature formula** (O'Neill, Corollary 1(2)).
For a horizontal vector `u` and a vertical vector `v`,
`K_M(u, v) = (⟪(∇_u T)(v, v), u⟫ + ‖A_u v‖² - ‖T_v u‖²) / (‖u‖² * ‖v‖²)`. -/
theorem sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker
    {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).ker) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x u v =
      (⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillT x u) v v, u⟫_ℝ +
        ‖h.oneillA x u v‖ ^ 2 - ‖h.oneillT x v u‖ ^ 2) /
        (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  have horth : ⟪u, v⟫_ℝ = 0 := (real_inner_comm _ _).trans
    (Submodule.inner_right_of_mem_orthogonal hv hu)
  have hg : (Matrix.gram ℝ ![u, v]).det = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [Matrix.real_det_gram_fin_two, horth, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq]
    ring
  rw [sectionalCurvature_apply, hg,
    h.inner_curvatureTensor_of_mem_orthogonal_ker_of_mem_ker_self hu hv]

/-- When the fibres are totally geodesic near `x` (`∀ᶠ y in 𝓝 x, h.oneillT y = 0`), the sectional
curvature of a mixed horizontal-vertical plane is `‖A_u v‖² / (‖u‖² * ‖v‖²)` (O'Neill,
Corollary 1(3)). -/
theorem sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero
    (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x u v =
      ‖h.oneillA x u v‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
  have hdT : (((leviCivitaConnection I M).hom
      ((leviCivitaConnection I M).hom (leviCivitaConnection I M))) h.oneillT x u) v v = 0 := by
    have hc := ((leviCivitaConnection I M).hom
      ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
      |>.isCovariantDerivativeOnUniv.congr_of_eventuallyEq (σ' := 0)
        ((h.contMDiff_oneillT x).mdifferentiableAt (by simp))
        (mdifferentiableAt_zeroSection ..) Filter.univ_mem hT
    rw [hc, CovariantDerivative.zero]
    simp
  have hTx : h.oneillT x v u = 0 := by
    rw [hT.self_of_nhds]
    simp
  rw [h.sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker hu hv, hdT, hTx]
  simp

/-- When the fibres are totally geodesic near `x` (`∀ᶠ y in 𝓝 x, h.oneillT y = 0`), every mixed
horizontal-vertical sectional curvature is nonnegative. -/
theorem sectionalCurvature_nonneg_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero
    (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    0 ≤ (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x u v := by
  rw [h.sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero hT hu hv]
  positivity

end MixedCurvature

end TauCeti.IsRiemannianSubmersion
