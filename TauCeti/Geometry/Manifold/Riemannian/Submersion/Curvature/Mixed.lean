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
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# O'Neill's mixed and Codazzi-type curvature equations for a Riemannian submersion

For a smooth Riemannian submersion `f : M → N`, let `h` and `v` be the horizontal and vertical
orthogonal projections on `TM`, and let `A` and `T` be O'Neill's fundamental tensors
(`IsRiemannianSubmersion.oneillA` and `IsRiemannianSubmersion.oneillT`). With the curvature sign
convention `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z` and
`Rm(u, v, w, z) = ⟪R(u, v) w, z⟫_ℝ`, the off-block and mixed components of the curvature of `M`
are expressed in terms of `A`, `T`, and their Hom-bundle covariant derivatives `∇ A` and `∇ T`
(requiring Hausdorffness of `M`, with no separation assumption on `N`):

* **Vertical-horizontal Codazzi equation (`{1}`, Besse 9.28b).** For vertical `u, v, w` and
  horizontal `z`,
  `Rm_M(u, v, w, z) = ⟪(∇_u T)(v, w), z⟫ - ⟪(∇_v T)(u, w), z⟫`.
* **Horizontal-vertical equation (`{3}`, Besse 9.28c).** For horizontal `u, v, w` and vertical `z`,
  `Rm_M(u, v, w, z) = -⟪(∇_w A)(u, v), z⟫ - ⟪A_u v, T_z w⟫ + ⟪A_v w, T_z u⟫ + ⟪A_w u, T_z v⟫`.
* **Mixed curvature (`{2}`, Besse 9.28e) and `(H, H, V, V)` block (Besse 9.28d).** For horizontal
  `u, z` and vertical `v, w`,
  `Rm_M(u, v, w, z) = ⟪(∇_u T)(v, w), z⟫ - ⟪(∇_v A)(u, w), z⟫ + ⟪A_u v, A_z w⟫ - ⟪T_v u, T_w z⟫`.
  For horizontal `u, v` and vertical `w, z`,
  `Rm_M(u, v, w, z) = -⟪(∇_w A)(u, v), z⟫ + ⟪(∇_z A)(u, v), w⟫ - ⟪A_u w, A_v z⟫`
  `+ ⟪A_u z, A_v w⟫ + ⟪T_w u, T_z v⟫ - ⟪T_z u, T_w v⟫`.
* **Vertico-horizontal sectional curvature (Corollary 1(2), Besse 9.29b).** Specializing `{2}` to
  `z = u` and `w = v` (where `⟪(∇_v A)(u, v), u⟫ = 0` by skew-adjointness and alternating symmetry
  of `∇ A`) gives
  `K_M(u, v) = (⟪(∇_u T)(v, v), u⟫ + ‖A_u v‖² - ‖T_v u‖²) / (‖u‖² * ‖v‖²)`.
  When the fibres are totally geodesic near the point (`∀ᶠ y in 𝓝 x, T_y = 0`),
  `K_M(u, v) = ‖A_u v‖² / (‖u‖² * ‖v‖²) ≥ 0`.

## Main results

* `TauCeti.IsRiemannianSubmersion.inner_hom_leviCivitaConnection_oneillA_antisymm`,
  `TauCeti.IsRiemannianSubmersion.inner_hom_leviCivitaConnection_oneillA_apply_self_eq_zero`,
  `TauCeti.IsRiemannianSubmersion.inner_hom_leviCivitaConnection_oneillA_self_eq_zero`,
  `TauCeti.IsRiemannianSubmersion.inner_hom_leviCivitaConnection_oneillT_comm`: pointwise
  alternating and symmetric identities for `∇ A` and `∇ T` (O'Neill, Lemma 4).
* `TauCeti.IsRiemannianSubmersion.riemannCurvatureTensor_of_mem_ker_of_mem_orthogonal_ker`:
  O'Neill's vertical-horizontal Codazzi equation `{1}` (Besse 9.28b).
* `TauCeti.IsRiemannianSubmersion.riemannCurvatureTensor_of_mem_orthogonal_ker_of_mem_ker`:
  O'Neill's horizontal-vertical equation `{3}` (Besse 9.28c).
* `riemannCurvatureTensor_of_mem_orthogonal_ker_of_mem_ker_of_mem_orthogonal_ker`,
  `riemannCurvatureTensor_of_mem_orthogonal_ker_of_mem_orthogonal_ker_of_mem_ker` (both in
  `TauCeti.IsRiemannianSubmersion`): O'Neill's mixed curvature equation `{2}` (Besse 9.28e) and
  the `(H, H, V, V)` equation (Besse 9.28d).
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker`,
  `sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero` (in
  `TauCeti.IsRiemannianSubmersion`): O'Neill's vertico-horizontal sectional curvature formula
  (Corollary 1(2)) and its specialization to totally geodesic fibres.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Lemma 4, Theorem 2 (`{1}`, `{2}`, `{3}`), and Corollary 1(2).
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §C, 9.28b–e and 9.29b.
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Manifold VectorField
open scoped ContDiff InnerProductSpace Manifold Matrix Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f) {x : M}

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

-- Cache operator-norm instances for the iterated endomorphism bundles on `TM`.
private local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

include h

/-! ### Smooth vertical and horizontal extensions on `M` -/

/-- Every vertical tangent vector extends to a globally smooth vertical vector field on `M`. -/
private theorem exists_contMDiff_mem_ker_eq {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) :
    ∃ V : Π y : M, TangentSpace I y, CMDiff ∞ (T% V) ∧ V x = v ∧
      ∀ y, V y ∈ (mfderiv I J f y).ker := by
  obtain ⟨V₀, hV₀, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  refine ⟨fun y ↦ (mfderiv I J f y).ker.starProjection (V₀ y),
    (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply hV₀,
    Submodule.starProjection_eq_self_iff.mpr hv,
    fun _ ↦ Submodule.starProjection_apply_mem _ _⟩

/-- Every horizontal tangent vector extends to a globally smooth horizontal vector field on `M`. -/
private theorem exists_contMDiff_mem_orthogonal_ker_eq {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    ∃ Y : Π y : M, TangentSpace I y, CMDiff ∞ (T% Y) ∧ Y x = v ∧
      ∀ y, Y y ∈ (mfderiv I J f y).kerᗮ := by
  obtain ⟨Y₀, hY₀, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  refine ⟨fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y₀ y),
    (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).clm_bundle_apply hY₀,
    Submodule.starProjection_eq_self_iff.mpr hv,
    fun _ ↦ Submodule.starProjection_apply_mem _ _⟩

/-! ### Pointwise symmetries of `∇ A` and `∇ T` (O'Neill, Lemma 4) -/

section TensorDerivatives

/-- On horizontal `v, w` and vertical `z`, `⟪(∇_u A)(v, w), z⟫` is alternating in `(v, w)`
(O'Neill, Lemma 4(2)). -/
theorem inner_hom_leviCivitaConnection_oneillA_antisymm
    (u : TangentSpace I x) {v w z : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).ker) :
    ⟪(((leviCivitaConnection I M).hom
        ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
      h.oneillA x u) v w, z⟫_ℝ =
      -⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x u) w v, z⟫_ℝ := by
  obtain ⟨V, hVd, hVx, hVh⟩ := h.exists_horizontal_extension hv
  obtain ⟨W, hWd, hWx, hWh⟩ := h.exists_horizontal_extension hw
  have hA := (h.contMDiff_oneillA x).mdifferentiableAt (by simp)
  -- `A_V W + A_W V = 0` everywhere, so its covariant derivative along `u` vanishes.
  have hsum : (fun y ↦ h.oneillA y (V y) (W y)) + (fun y ↦ h.oneillA y (W y) (V y)) = 0 :=
    funext fun y ↦ add_eq_zero_iff_eq_neg.mpr (h.oneillA_antisymm (hVh y) (hWh y))
  have hd : leviCivitaConnection I M (fun y ↦ h.oneillA y (V y) (W y)) x u +
      leviCivitaConnection I M (fun y ↦ h.oneillA y (W y) (V y)) x u = 0 := by
    have h0 := (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      ((hA.clm_bundle_apply hVd).clm_bundle_apply hWd)
      ((hA.clm_bundle_apply hWd).clm_bundle_apply hVd)
    rw [hsum, CovariantDerivative.zero] at h0
    simpa only [add_apply, Pi.zero_apply, zero_apply] using (congrArg (fun L ↦ L u) h0).symm
  -- Against vertical `z`, `A_a b` sees only the horizontal part of `b`.
  have horth (a b : TangentSpace I x) :
      ⟪h.oneillA x a b, z⟫_ℝ =
        ⟪h.oneillA x a ((mfderiv I J f x).kerᗮ.starProjection b), z⟫_ℝ := by
    conv_lhs =>
      rw [← Submodule.starProjection_eq_self_iff.mpr hz,
        ← Submodule.inner_starProjection_left_eq_right, h.starProjection_ker_oneillA]
  have hanti (q r : TangentSpace I x) (hr : r ∈ (mfderiv I J f x).kerᗮ) :
      h.oneillA x q r + h.oneillA x r ((mfderiv I J f x).kerᗮ.starProjection q) = 0 := by
    rw [← h.oneillA_starProjection_orthogonal_ker x q,
      h.oneillA_antisymm (Submodule.starProjection_apply_mem _ _) hr, neg_add_cancel]
  rw [← hVx, ← hWx, h.hom_leviCivitaConnection_oneillA_apply hVd hWd u,
    h.hom_leviCivitaConnection_oneillA_apply hWd hVd u,
    inner_sub_left, inner_sub_left, inner_sub_left, inner_sub_left,
    horth (V x) (leviCivitaConnection I M W x u),
    horth (W x) (leviCivitaConnection I M V x u)]
  have hc1 := congrArg (fun q ↦ ⟪q, z⟫_ℝ)
    (hanti (leviCivitaConnection I M V x u) (W x) (hWx.symm ▸ hw))
  have hc2 := congrArg (fun q ↦ ⟪q, z⟫_ℝ)
    (hanti (leviCivitaConnection I M W x u) (V x) (hVx.symm ▸ hv))
  have hc3 := congrArg (fun q ↦ ⟪q, z⟫_ℝ) hd
  simp only [inner_add_left, inner_zero_left] at hc1 hc2 hc3
  linarith

/-- On horizontal `v` and vertical `z`, `⟪(∇_u A)(v, v), z⟫ = 0` (O'Neill, Lemma 4(2)). -/
theorem inner_hom_leviCivitaConnection_oneillA_apply_self_eq_zero
    (u : TangentSpace I x) {v z : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hz : z ∈ (mfderiv I J f x).ker) :
    ⟪(((leviCivitaConnection I M).hom
        ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
      h.oneillA x u) v v, z⟫_ℝ = 0 := by
  have ha := h.inner_hom_leviCivitaConnection_oneillA_antisymm u hv hv hz
  linarith

/-- For any tangent direction `w`, horizontal `u`, and vertical `v`, `⟪(∇_w A)(u, v), u⟫ = 0`:
`(∇_w A) u` is skew-adjoint and `⟪(∇_w A)(u, u), v⟫ = 0`. -/
theorem inner_hom_leviCivitaConnection_oneillA_self_eq_zero
    (w : TangentSpace I x) {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    ⟪(((leviCivitaConnection I M).hom
        ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
      h.oneillA x w) u v, u⟫_ℝ = 0 := by
  rw [h.inner_hom_leviCivitaConnection_oneillA x w u v u, real_inner_comm,
    h.inner_hom_leviCivitaConnection_oneillA_apply_self_eq_zero w hu hv, neg_zero]

/-- On vertical `v, w` and horizontal `z`, `⟪(∇_u T)(v, w), z⟫` is symmetric in `(v, w)`
(O'Neill, Lemma 4(1)). -/
theorem inner_hom_leviCivitaConnection_oneillT_comm
    (u : TangentSpace I x) {v w z : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) (hw : w ∈ (mfderiv I J f x).ker)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(((leviCivitaConnection I M).hom
        ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
      h.oneillT x u) v w, z⟫_ℝ =
      ⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillT x u) w v, z⟫_ℝ := by
  obtain ⟨V, hVd, hVx, hVv⟩ := h.exists_vertical_extension hv
  obtain ⟨W, hWd, hWx, hWv⟩ := h.exists_vertical_extension hw
  -- `T_V W = T_W V` everywhere, so their covariant derivatives along `u` coincide.
  have heq : (fun y ↦ h.oneillT y (V y) (W y)) = fun y ↦ h.oneillT y (W y) (V y) :=
    funext fun y ↦ h.oneillT_comm (hVv y) (hWv y)
  -- Against horizontal `z`, `T_a b` sees only the vertical part of `b`.
  have horth (a b : TangentSpace I x) :
      ⟪h.oneillT x a b, z⟫_ℝ =
        ⟪h.oneillT x a ((mfderiv I J f x).ker.starProjection b), z⟫_ℝ := by
    conv_lhs =>
      rw [← Submodule.starProjection_eq_self_iff.mpr hz,
        ← Submodule.inner_starProjection_left_eq_right, h.starProjection_orthogonal_ker_oneillT]
  have hsymm (q r : TangentSpace I x) (hr : r ∈ (mfderiv I J f x).ker) :
      h.oneillT x q r = h.oneillT x r ((mfderiv I J f x).ker.starProjection q) := by
    rw [← h.oneillT_starProjection_ker x q,
      h.oneillT_comm (Submodule.starProjection_apply_mem _ _) hr]
  rw [← hVx, ← hWx, h.hom_leviCivitaConnection_oneillT_apply hVd hWd u,
    h.hom_leviCivitaConnection_oneillT_apply hWd hVd u, heq,
    inner_sub_left, inner_sub_left, inner_sub_left, inner_sub_left,
    horth (V x) (leviCivitaConnection I M W x u),
    horth (W x) (leviCivitaConnection I M V x u),
    hsymm (leviCivitaConnection I M V x u) (W x) (hWx.symm ▸ hw),
    hsymm (leviCivitaConnection I M W x u) (V x) (hVx.symm ▸ hv)]
  ring

end TensorDerivatives

/-! ### Vertical-horizontal Codazzi equation (`{1}`) -/

section VerticalCodazzi

/-- Horizontal projection of an iterated derivative `∇_u (∇_V W)` of smooth vertical vector fields
along an arbitrary tangent direction `u`. -/
private theorem starProjection_orthogonal_ker_iterated_mem_ker
    (u : TangentSpace I x) {V W : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W))
    (hVv : ∀ y, V y ∈ (mfderiv I J f y).ker) (hWv : ∀ y, W y ∈ (mfderiv I J f y).ker) :
    (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M (fun y ↦ leviCivitaConnection I M W y (V y)) x u) =
      (mfderiv I J f x).kerᗮ.starProjection
          ((((leviCivitaConnection I M).hom
              ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
            h.oneillT x u) (V x) (W x)) +
        h.oneillT x ((mfderiv I J f x).ker.starProjection
          (leviCivitaConnection I M V x u)) (W x) +
        h.oneillT x (V x) ((mfderiv I J f x).ker.starProjection
          (leviCivitaConnection I M W x u)) +
        h.oneillA x u ((mfderiv I J f x).ker.starProjection
          (leviCivitaConnection I M W x (V x))) +
        h.oneillT x u ((mfderiv I J f x).ker.starProjection
          (leviCivitaConnection I M W x (V x))) := by
  have hTW : CMDiff ∞ (T% (fun y ↦ h.oneillT y (V y) (W y))) :=
    (h.contMDiff_oneillT.clm_bundle_apply hV).clm_bundle_apply hW
  have hVW : CMDiff ∞ (T% (fun y ↦ (mfderiv I J f y).ker.starProjection
      (leviCivitaConnection I M W y (V y)))) :=
    (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply
      ((leviCivitaConnection I M).contMDiff_apply hV hW)
  -- Split `∇_V W = T_V W + v (∇_V W)` and differentiate both summands along `u`.
  have hsplit : (fun y ↦ leviCivitaConnection I M W y (V y)) =
      (fun y ↦ h.oneillT y (V y) (W y)) +
        fun y ↦ (mfderiv I J f y).ker.starProjection (leviCivitaConnection I M W y (V y)) :=
    funext fun y ↦ h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker
      ((hW y).mdifferentiableAt (by simp)) (.of_forall hWv) (hVv y)
  have hhom := congrArg (mfderiv I J f x).kerᗮ.starProjection
    (h.hom_leviCivitaConnection_oneillT_apply
      ((hV x).mdifferentiableAt (by simp)) ((hW x).mdifferentiableAt (by simp)) u)
  rw [map_sub, map_sub, ← h.oneillT_starProjection_ker x (leviCivitaConnection I M V x u),
    Submodule.starProjection_eq_self_iff.mpr (h.oneillT_apply_mem_orthogonal_ker _ (hWv x)),
    h.starProjection_orthogonal_ker_oneillT] at hhom
  have hhom' := eq_add_of_sub_eq (eq_add_of_sub_eq hhom.symm)
  rw [hsplit, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      ((hTW x).mdifferentiableAt (by simp)) ((hVW x).mdifferentiableAt (by simp)),
    add_apply, map_add,
    h.starProjection_orthogonal_ker_leviCivitaConnection_of_eventually_mem_ker
      ((hVW x).mdifferentiableAt (by simp))
      (.of_forall fun y ↦ Submodule.starProjection_apply_mem _ _) u,
    hhom']
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
    h.starProjection_orthogonal_ker_iterated_mem_ker (U x) hV hW hVv hWv,
    h.starProjection_orthogonal_ker_iterated_mem_ker (V x) hU hW hUv hWv,
    h.oneillA_eq_zero_of_mem_ker (hUv x), h.oneillA_eq_zero_of_mem_ker (hVv x),
    zero_apply, zero_apply, hbr, map_sub]
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

end VerticalCodazzi

/-! ### Horizontal-vertical and mixed curvature equations (`{3}`, `{2}`, and Besse 9.28d) -/

section MixedCurvature

/-- Vertical projection of an iterated derivative `∇_u (∇_Y Z)` of smooth horizontal fields on `M`
along a horizontal vector `u`. -/
private theorem starProjection_ker_iterated_mem_orthogonal_ker
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    {Y Z : Π y : M, TangentSpace I y} (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hYh : ∀ y, Y y ∈ (mfderiv I J f y).kerᗮ) (hZh : ∀ y, Z y ∈ (mfderiv I J f y).kerᗮ) :
    (mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M (fun y ↦ leviCivitaConnection I M Z y (Y y)) x u) =
      (mfderiv I J f x).ker.starProjection
          ((((leviCivitaConnection I M).hom
              ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
            h.oneillA x u) (Y x) (Z x)) +
        h.oneillA x u ((mfderiv I J f x).kerᗮ.starProjection
          (leviCivitaConnection I M Z x (Y x))) +
        h.oneillA x ((mfderiv I J f x).kerᗮ.starProjection
          (leviCivitaConnection I M Y x u)) (Z x) +
        h.oneillA x (Y x) ((mfderiv I J f x).kerᗮ.starProjection
          (leviCivitaConnection I M Z x u)) := by
  have hAZ : CMDiff ∞ (T% (fun y ↦ h.oneillA y (Y y) (Z y))) :=
    (h.contMDiff_oneillA.clm_bundle_apply hY).clm_bundle_apply hZ
  have hHZ : CMDiff ∞ (T% (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection
      (leviCivitaConnection I M Z y (Y y)))) :=
    (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).clm_bundle_apply
      ((leviCivitaConnection I M).contMDiff_apply hY hZ)
  -- Split `∇_Y Z = h (∇_Y Z) + A_Y Z` on `M` and differentiate both summands along `u`.
  have hsplit : (fun y ↦ leviCivitaConnection I M Z y (Y y)) =
      (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (leviCivitaConnection I M Z y (Y y))) +
        fun y ↦ h.oneillA y (Y y) (Z y) :=
    funext fun y ↦ h.leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_orthogonal_ker
      ((hZ y).mdifferentiableAt (by simp)) (.of_forall hZh) (hYh y)
  have ha1 := h.oneillA_apply_of_eventually_mem_orthogonal_ker
    ((hHZ x).mdifferentiableAt (by simp))
    (.of_forall fun y ↦ Submodule.starProjection_apply_mem _ _) u
  rw [Submodule.starProjection_eq_self_iff.mpr hu] at ha1
  have hhom := congrArg (mfderiv I J f x).ker.starProjection
    (h.hom_leviCivitaConnection_oneillA_apply
      ((hY x).mdifferentiableAt (by simp)) ((hZ x).mdifferentiableAt (by simp)) u)
  rw [map_sub, map_sub,
    ← h.oneillA_starProjection_orthogonal_ker x (leviCivitaConnection I M Y x u),
    Submodule.starProjection_eq_self_iff.mpr (h.oneillA_apply_mem_ker _ (hZh x)),
    h.starProjection_ker_oneillA] at hhom
  have hhom' := eq_add_of_sub_eq (eq_add_of_sub_eq hhom.symm)
  rw [hsplit, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      ((hHZ x).mdifferentiableAt (by simp)) ((hAZ x).mdifferentiableAt (by simp)),
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
  obtain ⟨X, hX, hXx, hXh⟩ := h.exists_contMDiff_mem_orthogonal_ker_eq hu
  obtain ⟨Y, hY, hYx, hYh⟩ := h.exists_contMDiff_mem_orthogonal_ker_eq hv
  obtain ⟨Z, hZ, hZx, hZh⟩ := h.exists_contMDiff_mem_orthogonal_ker_eq hw
  have htor := ((torsion_eq_zero_iff _).mp (torsion_leviCivitaConnection_eq_zero I))
    ((hX x).mdifferentiableAt (by simp)) ((hY x).mdifferentiableAt (by simp))
  -- Expand `v (∇_[X, Y] Z) = A_[X, Y] Z + 2 T_(A_X Y) Z` using `v [X, Y] = 2 A_X Y`.
  have hbr : (mfderiv I J f x).ker.starProjection
      (leviCivitaConnection I M Z x (mlieBracket I X Y x)) =
      h.oneillA x ((mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M Y x (X x))) (Z x) -
      h.oneillA x ((mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M X x (Y x))) (Z x) +
      (2 : ℝ) • h.oneillT x (h.oneillA x (X x) (Y x)) (Z x) := by
    rw [h.starProjection_ker_leviCivitaConnection_of_eventually_mem_orthogonal_ker
        ((hZ x).mdifferentiableAt (by simp)) (.of_forall hZh),
      ← h.oneillT_starProjection_ker x (mlieBracket I X Y x),
      h.starProjection_ker_mlieBracket ((hX x).mdifferentiableAt (by simp))
        ((hY x).mdifferentiableAt (by simp)) (.of_forall hXh) (.of_forall hYh),
      ← h.oneillA_starProjection_orthogonal_ker x (mlieBracket I X Y x),
      ← htor, map_sub, map_sub, sub_apply, map_smul, smul_apply]
  rw [← hXx, ← hYx, ← hZx,
    (leviCivitaConnection I M).curvatureTensor_apply x hX hY hZ,
    curvatureOperator_apply, map_sub, map_sub,
    h.starProjection_ker_iterated_mem_orthogonal_ker (hXh x) hY hZ hYh hZh,
    h.starProjection_ker_iterated_mem_orthogonal_ker (hYh x) hX hZ hXh hZh,
    hbr, map_sub]
  abel

/-- **O'Neill's equation `{3}` (Besse 9.28c).** For horizontal vectors `u, v, w` and a vertical
vector `z`,
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
  have htwo (a b c : TangentSpace I x) (ha : a ∈ (mfderiv I J f x).kerᗮ)
      (hb : b ∈ (mfderiv I J f x).kerᗮ) (hc : c ∈ (mfderiv I J f x).kerᗮ) :
      (leviCivitaConnection I M).riemannCurvatureTensor x a b c z =
        ⟪(((leviCivitaConnection I M).hom
            ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x a) b c, z⟫_ℝ -
        ⟪(((leviCivitaConnection I M).hom
            ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x b) a c, z⟫_ℝ -
        2 * ⟪h.oneillA x a b, h.oneillT x z c⟫_ℝ := by
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
  have ha1 := h.inner_hom_leviCivitaConnection_oneillA_antisymm u hw hv hz
  have ha2 := h.inner_hom_leviCivitaConnection_oneillA_antisymm v hw hu hz
  have ha3 := h.inner_hom_leviCivitaConnection_oneillA_antisymm w hv hu hz
  linarith

/-- Second iterated-derivative term `⟪∇_v (∇_{X'} W), z⟫` in O'Neill's mixed curvature equation
`{2}`, requiring only `CMDiffAt ∞` of the base field `X` at `f x`. -/
private theorem inner_iterated_horizontalLift_mem_ker
    {X : Π y : N, TangentSpace J y} {W : Π y : M, TangentSpace I y} {v z : TangentSpace I x}
    (hX : CMDiffAt ∞ (T% X) (f x)) (hW : CMDiff ∞ (T% W))
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
  have hX' : CMDiffAt ∞ (T% X') x := h.contMDiffAt_horizontalLift hX (by simp)
  have hAW : MDiffAt (T% (fun y ↦ h.oneillA y (X' y) (W y))) x :=
    (((h.contMDiff_oneillA x).clm_bundle_apply hX').clm_bundle_apply (hW x)).mdifferentiableAt
      (by simp)
  have hcovW := contMDiffOn_univ.mp
    ((ContMDiffCovariantDerivative.contMDiff
      (cov := leviCivitaConnection I M) (k := ∞)).contMDiff hW.contMDiffOn)
  have hXW : MDiffAt (T% (fun y ↦ (mfderiv I J f y).ker.starProjection
      (leviCivitaConnection I M W y (X' y)))) x :=
    ((h.contMDiff_starProjection_ker (n := ∞) (by simp) x).clm_bundle_apply
      ((hcovW x).clm_bundle_apply hX')).mdifferentiableAt (by simp)
  -- Split `∇_{X'} W = A_{X'} W + v (∇_{X'} W)` and differentiate both summands along vertical `v`.
  have hsplit : (fun y ↦ leviCivitaConnection I M W y (X' y)) =
      (fun y ↦ h.oneillA y (X' y) (W y)) +
        fun y ↦ (mfderiv I J f y).ker.starProjection (leviCivitaConnection I M W y (X' y)) :=
    funext fun y ↦ h.leviCivitaConnection_of_eventually_mem_ker_of_mem_orthogonal_ker
      ((hW y).mdifferentiableAt (by simp)) (.of_forall hWv)
      (h.horizontalLift_mem_orthogonal_ker y _)
  have hhomA := congrArg (fun q ↦ ⟪q, z⟫_ℝ)
    (h.hom_leviCivitaConnection_oneillA_apply
      (hX'.mdifferentiableAt (by simp)) ((hW x).mdifferentiableAt (by simp)) v)
  have haX' : ⟪h.oneillA x (leviCivitaConnection I M X' x v) (W x), z⟫_ℝ =
      -⟪h.oneillA x (X' x) v, h.oneillA x z (W x)⟫_ℝ := by
    rw [h.leviCivitaConnection_horizontalLift_of_mem_ker (hX.of_le (by simp)) hv,
      map_add, h.oneillA_eq_zero_of_mem_ker
        (h.oneillT_apply_mem_ker v (h.horizontalLift_mem_orthogonal_ker x _)),
      add_zero, h.inner_oneillA, h.oneillA_antisymm (h.oneillA_apply_mem_orthogonal_ker _ hv) hz,
      inner_neg_right, neg_neg, real_inner_comm, h.inner_oneillA]
  have haW' : ⟪h.oneillA x (X' x) (leviCivitaConnection I M W x v), z⟫_ℝ =
      -⟪(mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x v),
        h.oneillA x (X' x) z⟫_ℝ := by
    rw [h.inner_oneillA]
    conv_lhs =>
      rw [← Submodule.starProjection_eq_self_iff.mpr (h.oneillA_apply_mem_ker (X' x) hz),
        ← Submodule.inner_starProjection_left_eq_right]
  have htXW : ⟪leviCivitaConnection I M
      (fun y ↦ (mfderiv I J f y).ker.starProjection (leviCivitaConnection I M W y (X' y)))
        x v, z⟫_ℝ =
      ⟪h.oneillT x v ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M W x (X' x))), z⟫_ℝ := by
    have hz' : (mfderiv I J f x).kerᗮ.starProjection z = z :=
      Submodule.starProjection_eq_self_iff.mpr hz
    conv_lhs => rw [← hz', ← Submodule.inner_starProjection_left_eq_right]
    have ht := h.oneillT_apply_of_eventually_mem_ker hXW
      (.of_forall fun y ↦ Submodule.starProjection_apply_mem _ _) v
    rw [Submodule.starProjection_eq_self_iff.mpr hv] at ht
    rw [← ht]
  rw [hsplit, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add hAW hXW,
    add_apply, inner_add_left, htXW]
  simp only [inner_sub_left, haX', haW'] at hhomA
  linarith

/-- **O'Neill's equation `{2}` (mixed curvature, Besse 9.28e).** For horizontal vectors `u, z` and
vertical vectors `v, w`,
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
  -- Extend `df u` locally on `N` via `FiberBundle.extend` (avoiding `[T2Space N]`) and lift to `M`.
  obtain ⟨t, ht, hXt⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) J F (mfderiv I J f x u)
  set X : Π y : N, TangentSpace J y := FiberBundle.extend F (mfderiv I J f x u)
  set O : Set M := f ⁻¹' interior t
  have hO : IsOpen O := isOpen_interior.preimage h.isSubmersion.contMDiff.continuous
  have hxO : x ∈ O := mem_interior_iff_mem_nhds.mpr ht
  have hXx : CMDiffAt ∞ (T% X) (f x) := FiberBundle.contMDiffAt_extend ..
  set X' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (X (f y))
  have hX'O : CMDiff[O] ∞ (T% X') := fun y hy ↦
    (h.contMDiffAt_horizontalLift
      (((hXt.mono interior_subset) (f y) hy).contMDiffAt (isOpen_interior.mem_nhds hy))
      (by simp)).contMDiffWithinAt
  have hX'x : X' x = u := by
    simp [X', X, FiberBundle.extend_apply_self, h.horizontalLift_mfderiv_of_mem x hu]
  obtain ⟨V, hV, hVx, hVv⟩ := h.exists_contMDiff_mem_ker_eq hv
  obtain ⟨W, hW, hWx, hWv⟩ := h.exists_contMDiff_mem_ker_eq hw
  have hz' : (mfderiv I J f x).kerᗮ.starProjection z = z :=
    Submodule.starProjection_eq_self_iff.mpr hz
  -- First iterated-derivative term `⟪∇_{X'} (∇_V W), z⟫`, from the unified vertical helper.
  have h1 : ⟪leviCivitaConnection I M (fun y ↦ leviCivitaConnection I M W y (V y)) x (X' x), z⟫_ℝ =
      ⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillT x (X' x)) (V x) (W x), z⟫_ℝ +
      ⟪h.oneillT x ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M V x (X' x))) (W x), z⟫_ℝ +
      ⟪h.oneillT x (V x) ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M W x (X' x))), z⟫_ℝ -
      ⟪(mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x (V x)),
        h.oneillA x (X' x) z⟫_ℝ := by
    conv_lhs => rw [← hz', ← Submodule.inner_starProjection_left_eq_right]
    rw [h.starProjection_orthogonal_ker_iterated_mem_ker (X' x) hV hW hVv hWv,
      h.oneillT_eq_zero_of_mem_orthogonal_ker (h.horizontalLift_mem_orthogonal_ker x _),
      zero_apply, add_zero]
    simp only [inner_add_left, Submodule.inner_starProjection_left_eq_right, hz', h.inner_oneillA]
    ring
  -- Bracket term `⟪∇_{[X', V]} W, z⟫`.
  have hbr : ⟪leviCivitaConnection I M W x (mlieBracket I X' V x), z⟫_ℝ =
      ⟪h.oneillT x ((mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M V x (X' x))) (W x), z⟫_ℝ +
      ⟪h.oneillT x (V x) (X' x), h.oneillT x (W x) z⟫_ℝ := by
    have hmem := h.mlieBracket_horizontalLift_mem_ker (hXx.of_le (by simp))
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
    rw [← ht, h.mlieBracket_horizontalLift_of_eventually_mem_ker (hXx.of_le (by simp))
        ((hV x).mdifferentiableAt (by simp)) (.of_forall hVv),
      map_sub, sub_apply, inner_sub_left, ht2, sub_neg_eq_add]
  rw [riemannCurvatureTensor_apply, ← hX'x, ← hVx, ← hWx,
    (leviCivitaConnection I M).curvatureTensor_apply_of_contMDiffOn x hO hxO
      hX'O hV.contMDiffOn hW.contMDiffOn,
    curvatureOperator_apply, inner_sub_left, inner_sub_left,
    h1, h.inner_iterated_horizontalLift_mem_ker hXx hW (hVv x) hWv hz, hbr]
  linarith

/-- **O'Neill's `(H, H, V, V)` mixed curvature equation (Besse 9.28d).** For horizontal vectors
`u, v` and vertical vectors `w, z`,
`Rm_M(u, v, w, z) = -⟪(∇_w A)(u, v), z⟫ + ⟪(∇_z A)(u, v), w⟫ - ⟪A_u w, A_v z⟫`
`+ ⟪A_u z, A_v w⟫ + ⟪T_w u, T_z v⟫ - ⟪T_z u, T_w v⟫`. -/
theorem riemannCurvatureTensor_of_mem_orthogonal_ker_of_mem_orthogonal_ker_of_mem_ker
    {u v w z : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).ker)
    (hz : z ∈ (mfderiv I J f x).ker) :
    (leviCivitaConnection I M).riemannCurvatureTensor x u v w z =
      -⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x w) u v, z⟫_ℝ +
      ⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x z) u v, w⟫_ℝ -
      ⟪h.oneillA x u w, h.oneillA x v z⟫_ℝ +
      ⟪h.oneillA x u z, h.oneillA x v w⟫_ℝ +
      ⟪h.oneillT x w u, h.oneillT x z v⟫_ℝ -
      ⟪h.oneillT x z u, h.oneillT x w v⟫_ℝ := by
  let : IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _) := .of_le (n := ∞) (by simp)
  have hswap :=
    (isMetricCompatible_leviCivitaConnection I (M := M)).riemannCurvatureTensor_swap_pairs
      (leviCivitaConnection I M) (torsion_leviCivitaConnection_eq_zero I) x u v w z
  have hcyc := (leviCivitaConnection I M).riemannCurvatureTensor_cyclic_eq_zero
    (torsion_leviCivitaConnection_eq_zero I) x w z u v
  have hanti := (leviCivitaConnection I M).riemannCurvatureTensor_antisymm_first x z u w v
  have hm1 :=
    h.riemannCurvatureTensor_of_mem_orthogonal_ker_of_mem_ker_of_mem_orthogonal_ker hu hz hw hv
  have hm2 :=
    h.riemannCurvatureTensor_of_mem_orthogonal_ker_of_mem_ker_of_mem_orthogonal_ker hu hw hz hv
  have ht := h.inner_hom_leviCivitaConnection_oneillT_comm u hz hw hv
  have ha1 := h.inner_hom_leviCivitaConnection_oneillA x z u w v
  have ha2 := h.inner_hom_leviCivitaConnection_oneillA x w u z v
  rw [real_inner_comm _ w] at ha1
  rw [real_inner_comm _ z] at ha2
  linarith

/-! ### Vertico-horizontal sectional curvature -/

/-- For a horizontal vector `u` and a vertical vector `v`,
`⟪R_M(u, v) v, u⟫ = ⟪(∇_u T)(v, v), u⟫ + ‖A_u v‖² - ‖T_v u‖²` (O'Neill, Corollary 1(2)). -/
theorem inner_curvatureTensor_self_of_mem_orthogonal_ker_of_mem_ker
    {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).ker) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u v v, u⟫_ℝ =
      ⟪(((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillT x u) v v, u⟫_ℝ +
      ‖h.oneillA x u v‖ ^ 2 - ‖h.oneillT x v u‖ ^ 2 := by
  have hm :=
    h.riemannCurvatureTensor_of_mem_orthogonal_ker_of_mem_ker_of_mem_orthogonal_ker hu hv hv hu
  rw [riemannCurvatureTensor_apply, h.inner_hom_leviCivitaConnection_oneillA_self_eq_zero v hu hv,
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
  have hg : (Matrix.gram ℝ ![u, v]).det = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [Matrix.real_det_gram_fin_two, Submodule.inner_left_of_mem_orthogonal hv hu,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  rw [sectionalCurvature_apply, hg,
    h.inner_curvatureTensor_self_of_mem_orthogonal_ker_of_mem_ker hu hv]

/-- When the fibres are totally geodesic near `x` (`∀ᶠ y in 𝓝 x, h.oneillT y = 0`), the sectional
curvature of a mixed horizontal-vertical plane is `‖A_u v‖² / (‖u‖² * ‖v‖²)` (O'Neill,
Corollary 1(2)). -/
theorem sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero
    {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).ker) (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x u v =
      ‖h.oneillA x u v‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
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
    {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).ker) (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) :
    0 ≤ (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x u v := by
  rw [h.sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero hu hv hT]
  positivity

end MixedCurvature

end TauCeti.IsRiemannianSubmersion
