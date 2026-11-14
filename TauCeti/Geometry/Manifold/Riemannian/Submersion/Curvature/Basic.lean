/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Connection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# O'Neill's curvature tensor equations for a Riemannian submersion

Let `f : M → N` be a Riemannian submersion with horizontal and vertical orthogonal projections
`h` and `v`, horizontal lift `horizontalLift`, and fundamental tensors `A` (`oneillA`) and `T`
(`oneillT`). Writing `∇` for the Levi-Civita connection of `M`, `∇^N` for that of `N`, and
`∇A`, `∇T` for the covariant derivatives of `A` and `T` under the induced Hom-bundle connection
`∇.hom (∇.hom ∇)`, this file proves the four curvature equations of O'Neill's Theorem 2 that live
intrinsically on `M` and `N` (under Lee's sign convention
`R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z`, which is opposite to O'Neill's `(1, 3)` sign
while agreeing on sectional-curvature numerators `⟪R(u, v) v, u⟫`):

* `{1}` (three vertical, one horizontal): for vertical `u, v, w` and horizontal `z`,
  `⟪R(u, v) w, z⟫ = ⟪(∇_u T) v w, z⟫ - ⟪(∇_v T) u w, z⟫`.
* `{2}` (mixed horizontal-vertical): for horizontal `u, z` and vertical `v, w`,
  `⟪R(u, v) w, z⟫ = ⟪(∇_u T) v w, z⟫ - ⟪(∇_v A) u w, z⟫ + ⟪A_u v, A_z w⟫ - ⟪T_v u, T_w z⟫`.
* `{3}` (three horizontal, one vertical): for horizontal `u, v, z` and vertical `w`,
  `⟪R(u, v) z, w⟫ = ⟪(∇_u A) v z, w⟫ - ⟪(∇_v A) u z, w⟫ - 2 ⟪T_(A_u v) z, w⟫`, together with
  its single-derivative Bianchi form
  `-⟪(∇_z A) u v, w⟫ - ⟪A_u v, T_w z⟫ + ⟪A_v z, T_w u⟫ + ⟪A_z u, T_w v⟫`.
* `{4}` (four horizontal): for horizontal `u, v, z, w`,
  `⟪R(u, v) z, w⟫ = ⟪R^N(df u, df v)(df z), df w⟫ - ⟪A_v z, A_u w⟫ + ⟪A_u z, A_v w⟫`
  `+ 2 ⟪A_u v, A_z w⟫`, along with the horizontal-projection identity for `h (R(u, v) z)`.

The purely vertical Gauss equation (`{0}`), which compares four vertical arguments with the
intrinsic curvature of a fibre submanifold, requires endowing the fibres with a submanifold
structure and is not treated here. Neither surjectivity of `f` nor completeness or connectedness
is assumed; equations `{1}`–`{3}` require `[T2Space M]` only, and `[T2Space N]` enters only in
equation `{4}` where `curvatureTensor` on `N` appears.

## Main results

* `TauCeti.IsRiemannianSubmersion.inner_curvatureTensor_vertical_horizontal`: O'Neill's `{1}`.
* `TauCeti.IsRiemannianSubmersion.inner_curvatureTensor_horizontal_vertical_vertical_horizontal`:
  O'Neill's `{2}`.
* `TauCeti.IsRiemannianSubmersion.inner_curvatureTensor_horizontal_vertical` and
  `TauCeti.IsRiemannianSubmersion.inner_curvatureTensor_horizontal_vertical_eq_neg`:
  O'Neill's `{3}` in commutator and single-derivative forms.
* `TauCeti.IsRiemannianSubmersion.starProjection_orthogonal_ker_curvatureTensor_horizontal`,
  `TauCeti.IsRiemannianSubmersion.inner_curvatureTensor_horizontal`, and
  `TauCeti.IsRiemannianSubmersion.inner_curvatureTensor_eq_horizontalLift`: O'Neill's `{4}`.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Theorem 2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §D (9.28).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 7.47.
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Manifold VectorField
open scoped ContDiff InnerProductSpace Manifold Topology

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

-- These regularity indices are propositionally, but not definitionally, equal to `2`.
private instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

private instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

include h

/-! ### Total-space curvature equations `{1}`, `{2}`, `{3}` -/

section TotalCurvature

omit [FiniteDimensional ℝ F] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] h in
private theorem contMDiffOn_leviCivitaConnection_apply_of_isOpen {u : Set M} (hu : IsOpen u)
    {X σ : Π y : M, TangentSpace I y} (hX : CMDiff[u] ∞ (T% X)) (hσ : CMDiff[u] ∞ (T% σ)) :
    CMDiff[u] ∞ (T% (fun y ↦ leviCivitaConnection I M σ y (X y))) :=
  (contMDiffOn_leviCivitaConnection (I := I) (n := ∞) (m := ∞) (k := ∞) hu le_rfl le_rfl
    (by simpa using hσ)).clm_bundle_apply hX

variable [T2Space M] {x : M}

private theorem leviCivitaConnection_oneillA_eq {Y Z : Π y : M, TangentSpace I y}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (w : TangentSpace I x) :
    leviCivitaConnection I M (fun y ↦ h.oneillA y (Y y) (Z y)) x w =
      ((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x w (Y x) (Z x) +
        h.oneillA x (leviCivitaConnection I M Y x w) (Z x) +
        h.oneillA x (Y x) (leviCivitaConnection I M Z x w) := by
  rw [h.hom_oneillA_apply hY hZ w]
  abel

private theorem leviCivitaConnection_oneillT_eq {Y Z : Π y : M, TangentSpace I y}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (w : TangentSpace I x) :
    leviCivitaConnection I M (fun y ↦ h.oneillT y (Y y) (Z y)) x w =
      ((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillT x w (Y x) (Z x) +
        h.oneillT x (leviCivitaConnection I M Y x w) (Z x) +
        h.oneillT x (Y x) (leviCivitaConnection I M Z x w) := by
  rw [h.hom_oneillT_apply hY hZ w]
  abel

/-- Extend a vertical vector at `x` to a globally smooth vertical vector field on `M`. -/
private theorem exists_contMDiff_mem_ker {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).ker) :
    ∃ U : Π y : M, TangentSpace I y, CMDiff ∞ (T% U) ∧ U x = u ∧
      ∀ y, U y ∈ (mfderiv I J f y).ker := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  obtain ⟨U₀, hU₀, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  refine ⟨fun y ↦ (mfderiv I J f y).ker.starProjection (U₀ y),
    (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply hU₀,
    Submodule.starProjection_eq_self_iff.mpr hu,
    fun _ ↦ Submodule.starProjection_apply_mem _ _⟩

/-- Evaluate the horizontal inner product of `∇_A (∇_B W)` for smooth vertical fields `A, B, W`. -/
private theorem inner_leviCivitaConnection_mem_ker_iterated
    {A B W : Π y : M, TangentSpace I y} {z : TangentSpace I x}
    (hB : CMDiff ∞ (T% B)) (hW : CMDiff ∞ (T% W))
    (hAx : A x ∈ (mfderiv I J f x).ker)
    (hBv : ∀ y, B y ∈ (mfderiv I J f y).ker) (hWv : ∀ y, W y ∈ (mfderiv I J f y).ker)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    ⟪leviCivitaConnection I M (fun y ↦ leviCivitaConnection I M W y (B y)) x (A x), z⟫_ℝ =
      ⟪((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillT x (A x) (B x) (W x), z⟫_ℝ +
        ⟪h.oneillT x (leviCivitaConnection I M B x (A x)) (W x), z⟫_ℝ +
        ⟪h.oneillT x (B x)
          ((mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x (A x))), z⟫_ℝ +
        ⟪h.oneillT x (A x)
          ((mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x (B x))), z⟫_ℝ := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let cov := leviCivitaConnection I M
  have hWd := hW.mdifferentiable (by simp)
  have hQ := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  have hsplit : (fun y ↦ cov W y (B y)) =
      (fun y ↦ h.oneillT y (B y) (W y)) +
        fun y ↦ (mfderiv I J f y).ker.starProjection (cov W y (B y)) :=
    funext fun y ↦ h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker (hWd y)
      (.of_forall hWv) (hBv y)
  have hTW : MDiffAt (T% (fun y ↦ h.oneillT y (B y) (W y))) x :=
    ((h.contMDiff_oneillT.clm_bundle_apply hB).clm_bundle_apply hW).mdifferentiableAt (by simp)
  have hQW : MDiffAt (T% (fun y ↦ (mfderiv I J f y).ker.starProjection (cov W y (B y)))) x :=
    (hQ.clm_bundle_apply (cov.contMDiff_apply hB hW)).mdifferentiableAt (by simp)
  rw [hsplit, cov.isCovariantDerivativeOnUniv.add hTW hQW, add_apply,
    h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker hQW
      (.of_forall fun _ ↦ Submodule.starProjection_apply_mem _ _) hAx]
  have hev := h.leviCivitaConnection_oneillT_eq
    (hB.mdifferentiableAt (by simp)) (hWd x) (A x)
  have hAW := h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker (hWd x) (.of_forall hWv) hAx
  conv_lhs => rw [hev, hAW]
  have horth (q : TangentSpace I x) :
      ⟪(mfderiv I J f x).ker.starProjection q, z⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hz
  have horth₂ : ⟪h.oneillT x (B x) (h.oneillT x (A x) (W x)), z⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (h.oneillT_apply_mem_ker (B x) (h.oneillT_apply_mem_orthogonal_ker (A x) (hWv x))) hz
  simp only [map_add, inner_add_left, horth, horth₂]
  linarith

/-- **O'Neill's curvature equation `{1}`.** For vertical vectors `u, v, w` and a horizontal vector
`z`, `⟪R(u, v) w, z⟫ = ⟪(∇_u T) v w, z⟫ - ⟪(∇_v T) u w, z⟫`. -/
theorem inner_curvatureTensor_vertical_horizontal
    {u v w z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).ker) (hv : v ∈ (mfderiv I J f x).ker)
    (hw : w ∈ (mfderiv I J f x).ker) (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u v w, z⟫_ℝ =
      ⟪((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillT x u v w, z⟫_ℝ -
        ⟪((leviCivitaConnection I M).hom
            ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillT x v u w, z⟫_ℝ := by
  set cov := leviCivitaConnection I M
  obtain ⟨U, hU, rfl, hUv⟩ := h.exists_contMDiff_mem_ker hu
  obtain ⟨V, hV, rfl, hVv⟩ := h.exists_contMDiff_mem_ker hv
  obtain ⟨W, hW, rfl, hWv⟩ := h.exists_contMDiff_mem_ker hw
  have hUd := hU.mdifferentiable (by simp)
  have hVd := hV.mdifferentiable (by simp)
  have hWd := hW.mdifferentiable (by simp)
  have hbrv : mlieBracket I U V x ∈ (mfderiv I J f x).ker :=
    (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv
      (by simp [minSmoothness_of_isRCLikeNormedField]) (hUd x) (hVd x)
      (.of_forall hUv) (.of_forall hVv)
  have hbr : ⟪cov W x (mlieBracket I U V x), z⟫_ℝ =
      ⟪h.oneillT x (cov V x (U x)) (W x), z⟫_ℝ - ⟪h.oneillT x (cov U x (V x)) (W x), z⟫_ℝ := by
    rw [h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker (hWd x) (.of_forall hWv) hbrv,
      inner_add_left,
      Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hz,
      add_zero,
      ← ((torsion_eq_zero_iff cov).mp (torsion_leviCivitaConnection_eq_zero I)) (hUd x) (hVd x),
      map_sub, sub_apply, inner_sub_left]
  rw [curvatureTensor_apply cov x hU hV hW, curvatureOperator_apply, inner_sub_left,
    inner_sub_left,
    h.inner_leviCivitaConnection_mem_ker_iterated hV hW (hUv x) hVv hWv hz,
    h.inner_leviCivitaConnection_mem_ker_iterated hU hW (hVv x) hUv hWv hz, hbr]
  linarith

/-- Evaluate `⟪∇_u (∇_V W), z⟫` for smooth vertical fields `V, W` and horizontal `u, z`. -/
private theorem inner_leviCivitaConnection_mem_ker_of_mem_orthogonal_ker
    {V W : Π y : M, TangentSpace I y} {u v w z : TangentSpace I x}
    (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W))
    (hVx : V x = v) (hWx : W x = w)
    (hVv : ∀ y, V y ∈ (mfderiv I J f y).ker) (hWv : ∀ y, W y ∈ (mfderiv I J f y).ker)
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).ker)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    ⟪leviCivitaConnection I M (fun y ↦ leviCivitaConnection I M W y (V y)) x u, z⟫_ℝ =
      ⟪((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillT x u v w, z⟫_ℝ +
        ⟪h.oneillT x
          ((mfderiv I J f x).ker.starProjection (leviCivitaConnection I M V x u)) w, z⟫_ℝ +
        ⟪h.oneillT x v
          ((mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x u)), z⟫_ℝ -
        ⟪(mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x v),
          h.oneillA x u z⟫_ℝ := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let cov := leviCivitaConnection I M
  have hVd := hV.mdifferentiable (by simp)
  have hWd := hW.mdifferentiable (by simp)
  have hQ := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  have hsplitVW : (fun y ↦ cov W y (V y)) =
      (fun y ↦ h.oneillT y (V y) (W y)) +
        fun y ↦ (mfderiv I J f y).ker.starProjection (cov W y (V y)) :=
    funext fun y ↦ h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker (hWd y)
      (.of_forall hWv) (hVv y)
  have hTVW : MDiffAt (T% (fun y ↦ h.oneillT y (V y) (W y))) x :=
    ((h.contMDiff_oneillT.clm_bundle_apply hV).clm_bundle_apply hW).mdifferentiableAt (by simp)
  have hQVW : MDiffAt (T% (fun y ↦ (mfderiv I J f y).ker.starProjection (cov W y (V y)))) x :=
    (hQ.clm_bundle_apply (cov.contMDiff_apply hV hW)).mdifferentiableAt (by simp)
  rw [hsplitVW, cov.isCovariantDerivativeOnUniv.add hTVW hQVW, add_apply,
    h.leviCivitaConnection_of_eventually_mem_ker_of_mem_orthogonal_ker hQVW
      (.of_forall fun _ ↦ Submodule.starProjection_apply_mem _ _) hu]
  have hev := h.leviCivitaConnection_oneillT_eq (hVd x) (hWd x) u
  have hXW := h.leviCivitaConnection_of_eventually_mem_ker_of_mem_orthogonal_ker (hWd x)
    (.of_forall hWv) hu
  rw [hVx, hWx] at hev
  rw [hWx] at hXW
  conv_lhs => rw [hev, hXW, ← h.oneillT_starProjection_ker x (leviCivitaConnection I M V x u)]
  have horth (q : TangentSpace I x) :
      ⟪(mfderiv I J f x).ker.starProjection q, z⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hz
  have horth₂ : ⟪h.oneillT x v (h.oneillA x u w), z⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (h.oneillT_apply_mem_ker v (h.oneillA_apply_mem_orthogonal_ker u hw)) hz
  simp only [map_add, inner_add_left, horth, horth₂, hVx, h.inner_oneillA x u _ z]
  linarith

/-- Evaluate `⟪∇_v (∇_X W), z⟫` for a local basic horizontal lift `X` and vertical field `W`. -/
private theorem inner_leviCivitaConnection_horizontalLift_mem_ker
    {W₀ : Set N} {B : Π q : N, TangentSpace J q} {W : Π y : M, TangentSpace I y}
    {u v w z : TangentSpace I x}
    (hW₀ : IsOpen W₀) (hfxW₀ : f x ∈ W₀) (hBW₀ : CMDiff[W₀] ∞ (T% B))
    (hXW₀ : CMDiff[f ⁻¹' W₀] ∞ (T% (fun y ↦ h.horizontalLift y (B (f y)))))
    (hXx : h.horizontalLift x (B (f x)) = u)
    (hW : CMDiff ∞ (T% W)) (hWx : W x = w) (hWv : ∀ y, W y ∈ (mfderiv I J f y).ker)
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker)
    (hw : w ∈ (mfderiv I J f x).ker) (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    ⟪leviCivitaConnection I M
        (fun y ↦ leviCivitaConnection I M W y (h.horizontalLift y (B (f y)))) x v, z⟫_ℝ =
      ⟪((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x v u w, z⟫_ℝ -
        ⟪h.oneillA x u v, h.oneillA x z w⟫_ℝ -
        ⟪(mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x v),
          h.oneillA x u z⟫_ℝ +
        ⟪h.oneillT x v
          ((mfderiv I J f x).ker.starProjection (leviCivitaConnection I M W x u)), z⟫_ℝ := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let cov := leviCivitaConnection I M
  let X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B (f y))
  have hUopen : IsOpen (f ⁻¹' W₀) := hW₀.preimage h.isSubmersion.contMDiff.continuous
  have hXd : MDiffAt (T% X) x :=
    (hXW₀.contMDiffAt (hUopen.mem_nhds hfxW₀)).mdifferentiableAt (by simp)
  have hB1 : CMDiffAt 1 (T% B) (f x) :=
    (hBW₀.contMDiffAt (hW₀.mem_nhds hfxW₀)).of_le (m := 1) (by simp)
  have hWd := hW.mdifferentiable (by simp)
  have hQ := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  have hsplitXW : ∀ᶠ y in 𝓝 x, cov W y (X y) =
      h.oneillA y (X y) (W y) + (mfderiv I J f y).ker.starProjection (cov W y (X y)) :=
    .of_forall fun y ↦ h.leviCivitaConnection_of_eventually_mem_ker_of_mem_orthogonal_ker (hWd y)
      (.of_forall hWv) (h.horizontalLift_mem_orthogonal_ker y _)
  have hcovXW : CMDiff[f ⁻¹' W₀] ∞ (T% (fun y ↦ cov W y (X y))) :=
    contMDiffOn_leviCivitaConnection_apply_of_isOpen hUopen hXW₀ hW.contMDiffOn
  have hAXW : MDiffAt (T% (fun y ↦ h.oneillA y (X y) (W y))) x :=
    (((h.contMDiff_oneillA.contMDiffOn.clm_bundle_apply hXW₀).clm_bundle_apply
      hW.contMDiffOn).contMDiffAt (hUopen.mem_nhds hfxW₀)).mdifferentiableAt (by simp)
  have hQXW : MDiffAt (T% (fun y ↦ (mfderiv I J f y).ker.starProjection (cov W y (X y)))) x :=
    ((hQ.contMDiffOn.clm_bundle_apply hcovXW).contMDiffAt
      (hUopen.mem_nhds hfxW₀)).mdifferentiableAt (by simp)
  rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ((hcovXW.contMDiffAt (hUopen.mem_nhds hfxW₀)).mdifferentiableAt (by simp))
      (mdifferentiableAt_add_section hAXW hQXW) univ_mem hsplitXW,
    cov.isCovariantDerivativeOnUniv.add hAXW hQXW, add_apply,
    h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker hQXW
      (.of_forall fun _ ↦ Submodule.starProjection_apply_mem _ _) hv]
  have hev := h.leviCivitaConnection_oneillA_eq hXd (hWd x) v
  have hVW := h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker (hWd x) (.of_forall hWv) hv
  have hVX : cov X x v = h.oneillA x u v + h.oneillT x v u := by
    simpa only [X, hXx] using h.leviCivitaConnection_horizontalLift_of_mem_ker hB1 hv
  rw [show X x = u from hXx, hWx] at hev
  rw [hWx] at hVW
  conv_lhs => rw [hev, hVW, hVX]
  have hAT0 : h.oneillA x (h.oneillT x v u) w = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr (h.oneillT_apply_mem_ker v hu),
      h.oneillA_starProjection_ker, zero_apply]
  have hAA : ⟪h.oneillA x (h.oneillA x u v) w, z⟫_ℝ = -⟪h.oneillA x u v, h.oneillA x z w⟫_ℝ := by
    conv_lhs =>
      rw [h.inner_oneillA, h.oneillA_antisymm (h.oneillA_apply_mem_orthogonal_ker u hv) hz,
        inner_neg_right, neg_neg, real_inner_comm, h.inner_oneillA]
  have horth (q : TangentSpace I x) :
      ⟪(mfderiv I J f x).ker.starProjection q, z⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hz
  have horth₂ : ⟪h.oneillA x u (h.oneillT x v w), z⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (h.oneillA_apply_mem_ker u (h.oneillT_apply_mem_orthogonal_ker v hw)) hz
  simp only [cov, X, map_add, add_apply, inner_add_left, hAT0, inner_zero_left, hAA, horth,
    horth₂, hXx, h.inner_oneillA x u _ z]
  linarith

/-- **O'Neill's curvature equation `{2}`.** For horizontal vectors `u, z` and vertical vectors
`v, w`,
`⟪R(u, v) w, z⟫ = ⟪(∇_u T) v w, z⟫ - ⟪(∇_v A) u w, z⟫ + ⟪A_u v, A_z w⟫ - ⟪T_v u, T_w z⟫`. -/
theorem inner_curvatureTensor_horizontal_vertical_vertical_horizontal
    {u v w z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker)
    (hw : w ∈ (mfderiv I J f x).ker) (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u v w, z⟫_ℝ =
      ⟪((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillT x u v w, z⟫_ℝ -
        ⟪((leviCivitaConnection I M).hom
            ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x v u w, z⟫_ℝ +
        ⟪h.oneillA x u v, h.oneillA x z w⟫_ℝ -
        ⟪h.oneillT x v u, h.oneillT x w z⟫_ℝ := by
  set cov := leviCivitaConnection I M
  obtain ⟨W₀, B, hW₀, hfxW₀, hBW₀, hXW₀, hXx⟩ := h.exists_contMDiffOn_horizontalLift hu
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B (f y))
  have hUopen : IsOpen (f ⁻¹' W₀) := hW₀.preimage h.isSubmersion.contMDiff.continuous
  obtain ⟨V, hV, hVx, hVv⟩ := h.exists_contMDiff_mem_ker hv
  obtain ⟨W, hW, hWx, hWv⟩ := h.exists_contMDiff_mem_ker hw
  have hXd : MDiffAt (T% X) x :=
    (hXW₀.contMDiffAt (hUopen.mem_nhds hfxW₀)).mdifferentiableAt (by simp)
  have hB1 : CMDiffAt 1 (T% B) (f x) :=
    (hBW₀.contMDiffAt (hW₀.mem_nhds hfxW₀)).of_le (m := 1) (by simp)
  have hVd := hV.mdifferentiable (by simp)
  have hWd := hW.mdifferentiable (by simp)
  have hbrv : mlieBracket I X V x ∈ (mfderiv I J f x).ker :=
    (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv_of_eventually_related
      (by simp [minSmoothness_of_isRCLikeNormedField]) hXd (hVd x)
      (hB1.mdifferentiableAt one_ne_zero)
      (.of_forall fun y ↦ h.mfderiv_horizontalLift y _) (.of_forall hVv)
  have hbr_eq : mlieBracket I X V x =
      (mfderiv I J f x).ker.starProjection (cov V x u) - h.oneillT x v u := by
    have hT := ((torsion_eq_zero_iff cov).mp (torsion_leviCivitaConnection_eq_zero I)) hXd (hVd x)
    have hXV := h.leviCivitaConnection_of_eventually_mem_ker_of_mem_orthogonal_ker (hVd x)
      (.of_forall hVv) hu
    have hVX : cov X x v = h.oneillA x u v + h.oneillT x v u := by
      simpa only [X, hXx] using h.leviCivitaConnection_horizontalLift_of_mem_ker hB1 hv
    rw [show X x = u from hXx, hVx] at hT
    rw [hVx] at hXV
    rw [← hT, hVX]
    conv_lhs => rw [hXV]
    abel
  have ht₃ : ⟪cov W x (mlieBracket I X V x), z⟫_ℝ =
      ⟪h.oneillT x ((mfderiv I J f x).ker.starProjection (cov V x u)) w, z⟫_ℝ +
        ⟪h.oneillT x v u, h.oneillT x w z⟫_ℝ := by
    rw [h.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker (hWd x) (.of_forall hWv) hbrv,
      inner_add_left,
      Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hz,
      add_zero, hWx, hbr_eq, map_sub, sub_apply, inner_sub_left,
      h.oneillT_comm (h.oneillT_apply_mem_ker v hu) hw, h.inner_oneillT x w _ z, sub_neg_eq_add]
  have hcurv := curvatureTensor_apply_of_contMDiffOn cov x hUopen hfxW₀ hXW₀ hV.contMDiffOn
    hW.contMDiffOn
  rw [hXx, hVx, hWx] at hcurv
  rw [hcurv, curvatureOperator_apply, hXx, hVx, inner_sub_left, inner_sub_left,
    h.inner_leviCivitaConnection_mem_ker_of_mem_orthogonal_ker hV hW hVx hWx hVv hWv hu hw hz,
    h.inner_leviCivitaConnection_horizontalLift_mem_ker hW₀ hfxW₀ hBW₀ hXW₀ hXx hW hWx hWv hu hv
      hw hz,
    ht₃]
  linarith

/-- Evaluate `⟪∇_(L BA x) (∇_(L BB) (L B₃)), w⟫` for three local base fields `BA, BB, B₃` on an
open set `W₀` (with basic horizontal lifts `L BA`, `L BB`, `L B₃`) and a vertical vector `w`. -/
private theorem inner_leviCivitaConnection_horizontalLift_iterated_mem_ker
    {W₀ : Set N} {BA BB B₃ : Π q : N, TangentSpace J q} {w : TangentSpace I x}
    (hW₀ : IsOpen W₀) (hfx₀ : f x ∈ W₀)
    (hBB : CMDiff[W₀] ∞ (T% BB)) (hB₃ : CMDiff[W₀] ∞ (T% B₃))
    (hBon : CMDiff[f ⁻¹' W₀] ∞ (T% (fun y ↦ h.horizontalLift y (BB (f y)))))
    (hZon : CMDiff[f ⁻¹' W₀] ∞ (T% (fun y ↦ h.horizontalLift y (B₃ (f y)))))
    (hw : w ∈ (mfderiv I J f x).ker) :
    ⟪leviCivitaConnection I M
        (fun y ↦ leviCivitaConnection I M (fun q ↦ h.horizontalLift q (B₃ (f q))) y
          (h.horizontalLift y (BB (f y)))) x
        (h.horizontalLift x (BA (f x))), w⟫_ℝ =
      ⟪((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x (h.horizontalLift x (BA (f x))) (h.horizontalLift x (BB (f x)))
          (h.horizontalLift x (B₃ (f x))), w⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x (BA (f x)))
          (h.horizontalLift x (leviCivitaConnection J N B₃ (f x) (BB (f x)))), w⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x (BB (f x)))
          (h.horizontalLift x (leviCivitaConnection J N B₃ (f x) (BA (f x)))), w⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x (leviCivitaConnection J N BB (f x) (BA (f x))))
          (h.horizontalLift x (B₃ (f x))), w⟫_ℝ := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let cov := leviCivitaConnection I M
  have hUopen : IsOpen (f ⁻¹' W₀) := hW₀.preimage h.isSubmersion.contMDiff.continuous
  let B := fun y ↦ h.horizontalLift y (BB (f y))
  let Z := fun y ↦ h.horizontalLift y (B₃ (f y))
  let NBZ : Π q : N, TangentSpace J q := fun q ↦ leviCivitaConnection J N B₃ q (BB q)
  have hNBZon : CMDiff[W₀] ∞ (T% NBZ) :=
    contMDiffOn_leviCivitaConnection_apply_of_isOpen (I := J) hW₀ hBB hB₃
  have hLNBZ : CMDiff[f ⁻¹' W₀] ∞ (T% (fun y ↦ h.horizontalLift y (NBZ (f y)))) :=
    fun y hy ↦ (h.contMDiffAt_horizontalLift
      (hNBZon.contMDiffAt (hW₀.mem_nhds hy)) (by simp)).contMDiffWithinAt
  have hABZ : CMDiff[f ⁻¹' W₀] ∞ (T% (fun y ↦ h.oneillA y (B y) (Z y))) :=
    (h.contMDiff_oneillA.contMDiffOn.clm_bundle_apply hBon).clm_bundle_apply hZon
  have hsplit : ∀ᶠ y in 𝓝 x, cov Z y (B y) =
      h.horizontalLift y (NBZ (f y)) + h.oneillA y (B y) (Z y) := by
    filter_upwards [hUopen.mem_nhds hfx₀] with y hy
    exact h.leviCivitaConnection_horizontalLift
      ((hB₃.contMDiffAt (hW₀.mem_nhds hy)).of_le (m := 1) (by simp)) (BB (f y))
  have hcovBZ : CMDiff[f ⁻¹' W₀] ∞ (T% (fun y ↦ cov Z y (B y))) :=
    contMDiffOn_leviCivitaConnection_apply_of_isOpen hUopen hBon hZon
  have hLNBZd := (hLNBZ.contMDiffAt (hUopen.mem_nhds hfx₀)).mdifferentiableAt (by simp)
  have hABZd := (hABZ.contMDiffAt (hUopen.mem_nhds hfx₀)).mdifferentiableAt (by simp)
  rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ((hcovBZ.contMDiffAt (hUopen.mem_nhds hfx₀)).mdifferentiableAt (by simp))
      (mdifferentiableAt_add_section hLNBZd hABZd) univ_mem hsplit,
    cov.isCovariantDerivativeOnUniv.add hLNBZd hABZd, add_apply,
    h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
      ((hNBZon.contMDiffAt (hW₀.mem_nhds hfx₀)).of_le (m := 1) (by simp))
      (h.horizontalLift_mem_orthogonal_ker x _)]
  have hev := h.leviCivitaConnection_oneillA_eq
    ((hBon.contMDiffAt (hUopen.mem_nhds hfx₀)).mdifferentiableAt (by simp))
    ((hZon.contMDiffAt (hUopen.mem_nhds hfx₀)).mdifferentiableAt (by simp))
    (h.horizontalLift x (BA (f x)))
  have hAB := h.leviCivitaConnection_horizontalLift
    ((hBB.contMDiffAt (hW₀.mem_nhds hfx₀)).of_le (m := 1) (by simp)) (BA (f x))
  have hAZ := h.leviCivitaConnection_horizontalLift
    ((hB₃.contMDiffAt (hW₀.mem_nhds hfx₀)).of_le (m := 1) (by simp)) (BA (f x))
  rw [hev, hAB, hAZ]
  have hAA0 : h.oneillA x
      (h.oneillA x (h.horizontalLift x (BA (f x))) (h.horizontalLift x (BB (f x))))
      (h.horizontalLift x (B₃ (f x))) = 0 := by
    have hm := h.oneillA_apply_mem_ker (h.horizontalLift x (BA (f x)))
      (h.horizontalLift_mem_orthogonal_ker x (BB (f x)))
    rw [← Submodule.starProjection_eq_self_iff.mpr hm, h.oneillA_starProjection_ker, zero_apply]
  have horth (q : TangentSpace J (f x)) : ⟪h.horizontalLift x q, w⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hw (h.horizontalLift_mem_orthogonal_ker x q)
  have horth₂ : ⟪h.oneillA x (h.horizontalLift x (BB (f x)))
      (h.oneillA x (h.horizontalLift x (BA (f x))) (h.horizontalLift x (B₃ (f x)))), w⟫_ℝ =
      0 :=
    Submodule.inner_left_of_mem_orthogonal hw
      (h.oneillA_apply_mem_orthogonal_ker _
        (h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _)))
  simp only [NBZ, map_add, add_apply, inner_add_left, hAA0, inner_zero_left, horth, horth₂]
  linarith

/-- **O'Neill's curvature equation `{3}` (commutator form).** For horizontal vectors `u, v, z` and
a vertical vector `w`,
`⟪R(u, v) z, w⟫ = ⟪(∇_u A) v z, w⟫ - ⟪(∇_v A) u z, w⟫ - 2 ⟪T_(A_u v) z, w⟫`. -/
theorem inner_curvatureTensor_horizontal_vertical
    {u v z w : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).ker) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u v z, w⟫_ℝ =
      ⟪((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x u v z, w⟫_ℝ -
        ⟪((leviCivitaConnection I M).hom
            ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x v u z, w⟫_ℝ -
        2 * ⟪h.oneillT x (h.oneillA x u v) z, w⟫_ℝ := by
  let cov := leviCivitaConnection I M
  obtain ⟨W₁, B₁, hW₁, hfx₁, hB₁, hX₁, hXx₁⟩ := h.exists_contMDiffOn_horizontalLift hu
  obtain ⟨W₂, B₂, hW₂, hfx₂, hB₂, hX₂, hXx₂⟩ := h.exists_contMDiffOn_horizontalLift hv
  obtain ⟨W₃, B₃, hW₃, hfx₃, hB₃, hX₃, hXx₃⟩ := h.exists_contMDiffOn_horizontalLift hz
  set W₀ := W₁ ∩ W₂ ∩ W₃
  have hW₀ : IsOpen W₀ := (hW₁.inter hW₂).inter hW₃
  have hfx₀ : f x ∈ W₀ := ⟨⟨hfx₁, hfx₂⟩, hfx₃⟩
  have hUopen : IsOpen (f ⁻¹' W₀) := hW₀.preimage h.isSubmersion.contMDiff.continuous
  let X := fun y ↦ h.horizontalLift y (B₁ (f y))
  let Y := fun y ↦ h.horizontalLift y (B₂ (f y))
  let Z := fun y ↦ h.horizontalLift y (B₃ (f y))
  have hXon : CMDiff[f ⁻¹' W₀] ∞ (T% X) :=
    hX₁.mono (Set.preimage_mono (Set.inter_subset_left.trans Set.inter_subset_left))
  have hYon : CMDiff[f ⁻¹' W₀] ∞ (T% Y) :=
    hX₂.mono (Set.preimage_mono (Set.inter_subset_left.trans Set.inter_subset_right))
  have hZon : CMDiff[f ⁻¹' W₀] ∞ (T% Z) :=
    hX₃.mono (Set.preimage_mono Set.inter_subset_right)
  have hB₁on : CMDiff[W₀] ∞ (T% B₁) :=
    hB₁.mono (Set.inter_subset_left.trans Set.inter_subset_left)
  have hB₂on : CMDiff[W₀] ∞ (T% B₂) :=
    hB₂.mono (Set.inter_subset_left.trans Set.inter_subset_right)
  have hB₃on : CMDiff[W₀] ∞ (T% B₃) := hB₃.mono Set.inter_subset_right
  have hXd := (hXon.contMDiffAt (hUopen.mem_nhds hfx₀)).mdifferentiableAt (by simp)
  have hYd := (hYon.contMDiffAt (hUopen.mem_nhds hfx₀)).mdifferentiableAt (by simp)
  have hB₁_1 := (hB₁on.contMDiffAt (hW₀.mem_nhds hfx₀)).of_le (m := 1) (by simp)
  have hB₂_1 := (hB₂on.contMDiffAt (hW₀.mem_nhds hfx₀)).of_le (m := 1) (by simp)
  have hB₃_1 := (hB₃on.contMDiffAt (hW₀.mem_nhds hfx₀)).of_le (m := 1) (by simp)
  have hbr_split : mlieBracket I X Y x =
      h.horizontalLift x (mlieBracket J B₁ B₂ (f x)) + (2 : ℝ) • h.oneillA x u v := by
    conv_lhs =>
      rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal
        (mlieBracket I X Y x)]
    rw [← h.horizontalLift_mfderiv, h.mfderiv_mlieBracket_horizontalLift hB₁_1 hB₂_1,
      h.starProjection_ker_mlieBracket hXd hYd
        (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
        (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _),
      show X x = u from hXx₁, show Y x = v from hXx₂, add_comm]
  have hbr : ⟪cov Z x (mlieBracket I X Y x), w⟫_ℝ =
      ⟪h.oneillA x (h.horizontalLift x (leviCivitaConnection J N B₂ (f x) (B₁ (f x)))) z, w⟫_ℝ -
        ⟪h.oneillA x (h.horizontalLift x (leviCivitaConnection J N B₁ (f x) (B₂ (f x)))) z, w⟫_ℝ +
        2 * ⟪h.oneillT x (h.oneillA x u v) z, w⟫_ℝ := by
    rw [hbr_split, map_add, map_smul, h.leviCivitaConnection_horizontalLift hB₃_1,
      h.leviCivitaConnection_horizontalLift_of_mem_ker hB₃_1 (h.oneillA_apply_mem_ker u hv),
      hXx₃,
      ← ((torsion_eq_zero_iff (leviCivitaConnection J N)).mp
        (torsion_leviCivitaConnection_eq_zero J))
        (hB₁_1.mdifferentiableAt one_ne_zero) (hB₂_1.mdifferentiableAt one_ne_zero)]
    have horth (q : TangentSpace J (f x)) : ⟪h.horizontalLift x q, w⟫_ℝ = 0 :=
      Submodule.inner_left_of_mem_orthogonal hw (h.horizontalLift_mem_orthogonal_ker x q)
    have horth₂ : ⟪h.oneillA x z (h.oneillA x u v), w⟫_ℝ = 0 :=
      Submodule.inner_left_of_mem_orthogonal hw
        (h.oneillA_apply_mem_orthogonal_ker z (h.oneillA_apply_mem_ker u hv))
    simp only [map_sub, sub_apply, smul_add, inner_add_left, inner_sub_left, real_inner_smul_left,
      horth, horth₂]
    linarith
  have hcurv := curvatureTensor_apply_of_contMDiffOn cov x hUopen hfx₀ hXon hYon hZon
  have htXY := h.inner_leviCivitaConnection_horizontalLift_iterated_mem_ker (BA := B₁)
    hW₀ hfx₀ hB₂on hB₃on hYon hZon hw
  have htYX := h.inner_leviCivitaConnection_horizontalLift_iterated_mem_ker (BA := B₂)
    hW₀ hfx₀ hB₁on hB₃on hXon hZon hw
  rw [show X x = u from hXx₁, show Y x = v from hXx₂, show Z x = z from hXx₃] at hcurv
  rw [hXx₁, hXx₂, hXx₃] at htXY htYX
  rw [hcurv, curvatureOperator_apply, inner_sub_left, inner_sub_left,
    show X x = u from hXx₁, show Y x = v from hXx₂,
    show ⟪cov (fun y ↦ cov Z y (Y y)) x u, w⟫_ℝ = _ from htXY,
    show ⟪cov (fun y ↦ cov Z y (X y)) x v, w⟫_ℝ = _ from htYX, hbr]
  linarith

/-- **O'Neill's curvature equation `{3}` (single-derivative form).** Using the first Bianchi
identity, `{3}` rewrites with a single derivative `(∇_z A) u v`:
`⟪R(u, v) z, w⟫ = -⟪(∇_z A) u v, w⟫ - ⟪A_u v, T_w z⟫ + ⟪A_v z, T_w u⟫ + ⟪A_z u, T_w v⟫`. -/
theorem inner_curvatureTensor_horizontal_vertical_eq_neg
    {u v z w : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).ker) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u v z, w⟫_ℝ =
      -⟪((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillA x z u v, w⟫_ℝ -
        ⟪h.oneillA x u v, h.oneillT x w z⟫_ℝ +
        ⟪h.oneillA x v z, h.oneillT x w u⟫_ℝ +
        ⟪h.oneillA x z u, h.oneillT x w v⟫_ℝ := by
  have hbianchi : ⟪(leviCivitaConnection I M).curvatureTensor x u v z, w⟫_ℝ +
      ⟪(leviCivitaConnection I M).curvatureTensor x v z u, w⟫_ℝ +
      ⟪(leviCivitaConnection I M).curvatureTensor x z u v, w⟫_ℝ = 0 := by
    simpa only [inner_add_left, inner_zero_left] using
      congrArg (fun q ↦ ⟪q, w⟫_ℝ)
        ((leviCivitaConnection I M).curvatureTensor_cyclic_eq_zero
          (torsion_leviCivitaConnection_eq_zero I) x u v z)
  have h₁ := h.inner_curvatureTensor_horizontal_vertical hu hv hz hw
  have h₂ := h.inner_curvatureTensor_horizontal_vertical hv hz hu hw
  have h₃ := h.inner_curvatureTensor_horizontal_vertical hz hu hv hw
  have ha₁ := h.inner_hom_oneillA_antisymm u hv hz hw
  have ha₂ := h.inner_hom_oneillA_antisymm v hz hu hw
  have ha₃ := h.inner_hom_oneillA_antisymm z hu hv hw
  have hTswap (q c : TangentSpace I x) (hq : q ∈ (mfderiv I J f x).ker) :
      ⟪h.oneillT x q c, w⟫_ℝ = ⟪q, h.oneillT x w c⟫_ℝ := by
    rw [h.inner_oneillT, h.oneillT_comm hq hw, ← h.inner_oneillT, real_inner_comm]
  rw [hTswap _ z (h.oneillA_apply_mem_ker u hv)] at h₁
  rw [hTswap _ u (h.oneillA_apply_mem_ker v hz)] at h₂
  rw [hTswap _ v (h.oneillA_apply_mem_ker z hu)] at h₃
  linarith

end TotalCurvature

/-! ### Horizontal curvature equation `{4}` -/

section HorizontalCurvature

variable [T2Space M] [T2Space N] {x : M}

omit [T2Space N] in
/-- Evaluate the horizontal projection of the iterated covariant derivative along basic horizontal
lifts `L BA`, `L BB`, and `L B₃` for smooth base fields. -/
private theorem starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_iterated
    (x : M) {BA BB B₃ : Π q : N, TangentSpace J q}
    (hBB : CMDiff ∞ (T% BB)) (hB₃ : CMDiff ∞ (T% B₃)) :
    (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M
          (fun y ↦ leviCivitaConnection I M (fun q ↦ h.horizontalLift q (B₃ (f q))) y
            (h.horizontalLift y (BB (f y)))) x
          (h.horizontalLift x (BA (f x)))) =
      h.horizontalLift x
          (leviCivitaConnection J N (fun q ↦ leviCivitaConnection J N B₃ q (BB q)) (f x)
            (BA (f x))) +
        h.oneillA x (h.horizontalLift x (BA (f x)))
          (h.oneillA x (h.horizontalLift x (BB (f x))) (h.horizontalLift x (B₃ (f x)))) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set covM := leviCivitaConnection I M
  set covN := leviCivitaConnection J N
  have hlift (B : Π q : N, TangentSpace J q) (hB : CMDiff ∞ (T% B)) :
      CMDiff ∞ (T% (fun y ↦ h.horizontalLift y (B (f y)))) :=
    fun y ↦ h.contMDiffAt_horizontalLift (hB (f y)) (by simp)
  set Z : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₃ (f y))
  set NBZ : Π q : N, TangentSpace J q := fun q ↦ covN B₃ q (BB q)
  have hNBZ : CMDiff ∞ (T% NBZ) := covN.contMDiff_apply hBB hB₃
  have hLNBZ := hlift NBZ hNBZ
  have hABZ : CMDiff ∞ (T% (fun y ↦ h.oneillA y (h.horizontalLift y (BB (f y))) (Z y))) :=
    (h.contMDiff_oneillA.clm_bundle_apply (hlift BB hBB)).clm_bundle_apply (hlift B₃ hB₃)
  have hsplit : (fun y ↦ covM Z y (h.horizontalLift y (BB (f y)))) =
      (fun y ↦ h.horizontalLift y (NBZ (f y))) +
        fun y ↦ h.oneillA y (h.horizontalLift y (BB (f y))) (Z y) :=
    funext fun y ↦
      h.leviCivitaConnection_horizontalLift ((hB₃ (f y)).of_le (m := 1) (by simp)) (BB (f y))
  rw [hsplit, covM.isCovariantDerivativeOnUniv.add (hLNBZ.mdifferentiableAt (by simp))
      (hABZ.mdifferentiableAt (by simp)),
    add_apply, map_add,
    h.starProjection_covariantDerivative_horizontalLift
      (isLeviCivitaConnection_leviCivitaConnection I)
      (isLeviCivitaConnection_leviCivitaConnection J)
      ((hNBZ (f x)).of_le (m := 1) (by simp)) (BA (f x))]
  have hA_term := h.oneillA_apply_of_eventually_mem_ker (hABZ.mdifferentiableAt (by simp))
    (.of_forall fun y ↦ h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker y _))
    (h.horizontalLift x (BA (f x)))
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)]
    at hA_term
  rw [← hA_term]

/-- **O'Neill's curvature equation `{4}` (horizontal-projection form).** For horizontal vectors
`u, v, z`, writing `L_x = h.horizontalLift x`,
`h (R(u, v) z) = L_x (R^N(df u, df v)(df z)) + A_u (A_v z) - A_v (A_u z) - 2 A_z (A_u v)`. -/
theorem starProjection_orthogonal_ker_curvatureTensor_horizontal
    {u v z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    (mfderiv I J f x).kerᗮ.starProjection
        ((leviCivitaConnection I M).curvatureTensor x u v z) =
      h.horizontalLift x ((leviCivitaConnection J N).curvatureTensor (f x)
          (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x z)) +
        h.oneillA x u (h.oneillA x v z) -
        h.oneillA x v (h.oneillA x u z) -
        (2 : ℝ) • h.oneillA x z (h.oneillA x u v) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set covM := leviCivitaConnection I M
  set covN := leviCivitaConnection J N
  obtain ⟨B₁, hB₁, hB₁x⟩ := exists_contMDiff_section_eq J F ∞ (mfderiv I J f x u)
  obtain ⟨B₂, hB₂, hB₂x⟩ := exists_contMDiff_section_eq J F ∞ (mfderiv I J f x v)
  obtain ⟨B₃, hB₃, hB₃x⟩ := exists_contMDiff_section_eq J F ∞ (mfderiv I J f x z)
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
  set Y : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₂ (f y))
  set Z : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₃ (f y))
  have hlift (B : Π q : N, TangentSpace J q) (hB : CMDiff ∞ (T% B)) :
      CMDiff ∞ (T% (fun y ↦ h.horizontalLift y (B (f y)))) :=
    fun y ↦ h.contMDiffAt_horizontalLift (hB (f y)) (by simp)
  have hX := hlift B₁ hB₁
  have hY := hlift B₂ hB₂
  have hZ := hlift B₃ hB₃
  have hXx : h.horizontalLift x (B₁ (f x)) = u := by
    rw [hB₁x, h.horizontalLift_mfderiv_of_mem x hu]
  have hYx : h.horizontalLift x (B₂ (f x)) = v := by
    rw [hB₂x, h.horizontalLift_mfderiv_of_mem x hv]
  have hZx : h.horizontalLift x (B₃ (f x)) = z := by
    rw [hB₃x, h.horizontalLift_mfderiv_of_mem x hz]
  have hbr_split : mlieBracket I X Y x =
      h.horizontalLift x (mlieBracket J B₁ B₂ (f x)) + (2 : ℝ) • h.oneillA x u v := by
    conv_lhs =>
      rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal
        (mlieBracket I X Y x)]
    rw [← h.horizontalLift_mfderiv,
      h.mfderiv_mlieBracket_horizontalLift ((hB₁ (f x)).of_le (m := 1) (by simp))
        ((hB₂ (f x)).of_le (m := 1) (by simp)),
      h.starProjection_ker_mlieBracket (hX.mdifferentiableAt (by simp))
        (hY.mdifferentiableAt (by simp))
        (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
        (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _),
      hXx, hYx, add_comm]
  have hbr : (mfderiv I J f x).kerᗮ.starProjection (covM Z x (mlieBracket I X Y x)) =
      h.horizontalLift x (covN B₃ (f x) (mlieBracket J B₁ B₂ (f x))) +
        (2 : ℝ) • h.oneillA x z (h.oneillA x u v) := by
    rw [hbr_split, map_add, map_add, map_smul, map_smul,
      h.starProjection_covariantDerivative_horizontalLift
        (isLeviCivitaConnection_leviCivitaConnection I)
        (isLeviCivitaConnection_leviCivitaConnection J) ((hB₃ (f x)).of_le (m := 1) (by simp)),
      h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
        ((hB₃ (f x)).of_le (m := 1) (by simp)) (h.oneillA_apply_mem_ker u hv),
      hZx]
  have hcurvM := curvatureTensor_apply covM x hX hY hZ
  have hcurvN := curvatureTensor_apply covN (f x) hB₁ hB₂ hB₃
  rw [hXx, hYx, hZx] at hcurvM
  rw [hB₁x, hB₂x, hB₃x] at hcurvN
  have htXY := h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_iterated x
    (BA := B₁) hB₂ hB₃
  have htYX := h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_iterated x
    (BA := B₂) hB₁ hB₃
  simp only [hXx, hYx, hZx] at htXY htYX
  rw [hcurvM, hcurvN, curvatureOperator_apply, curvatureOperator_apply, map_sub, map_sub,
    map_sub, map_sub, hXx, hYx]
  rw [show (mfderiv I J f x).kerᗮ.starProjection (covM (fun y ↦ covM Z y (Y y)) x u) = _ from htXY,
    show (mfderiv I J f x).kerᗮ.starProjection (covM (fun y ↦ covM Z y (X y)) x v) = _ from htYX,
    hbr]
  abel

/-- **O'Neill's curvature equation `{4}`.** For horizontal tangent vectors `u, v, z, w`,
`⟪R(u, v) z, w⟫ = ⟪R^N(df u, df v)(df z), df w⟫ - ⟪A_v z, A_u w⟫ + ⟪A_u z, A_v w⟫`
`+ 2 ⟪A_u v, A_z w⟫`. -/
theorem inner_curvatureTensor_horizontal
    {u v z w : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u v z, w⟫_ℝ =
      ⟪(leviCivitaConnection J N).curvatureTensor (f x)
          (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x z),
        mfderiv I J f x w⟫_ℝ -
        ⟪h.oneillA x v z, h.oneillA x u w⟫_ℝ +
        ⟪h.oneillA x u z, h.oneillA x v w⟫_ℝ +
        2 * ⟪h.oneillA x u v, h.oneillA x z w⟫_ℝ := by
  have hp : ⟪(leviCivitaConnection I M).curvatureTensor x u v z, w⟫_ℝ =
      ⟪(mfderiv I J f x).kerᗮ.starProjection
        ((leviCivitaConnection I M).curvatureTensor x u v z), w⟫_ℝ := by
    rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hw]
  have hl : ⟪h.horizontalLift x ((leviCivitaConnection J N).curvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x z)), w⟫_ℝ =
      ⟪(leviCivitaConnection J N).curvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x z),
        mfderiv I J f x w⟫_ℝ := by
    conv_lhs => rw [← h.horizontalLift_mfderiv_of_mem x hw]
    exact (h.horizontalLift x).inner_map_map _ _
  rw [hp, h.starProjection_orthogonal_ker_curvatureTensor_horizontal hu hv hz]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hl, h.inner_oneillA]
  linarith

/-- Base metric-lowered curvature expressed on arbitrary base tangent vectors via
`horizontalLift`. -/
theorem inner_curvatureTensor_eq_horizontalLift
    (u v z w : TangentSpace J (f x)) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x) u v z, w⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x
          (h.horizontalLift x u) (h.horizontalLift x v) (h.horizontalLift x z),
        h.horizontalLift x w⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x v) (h.horizontalLift x z),
          h.oneillA x (h.horizontalLift x u) (h.horizontalLift x w)⟫_ℝ -
        ⟪h.oneillA x (h.horizontalLift x u) (h.horizontalLift x z),
          h.oneillA x (h.horizontalLift x v) (h.horizontalLift x w)⟫_ℝ -
        2 * ⟪h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v),
          h.oneillA x (h.horizontalLift x z) (h.horizontalLift x w)⟫_ℝ := by
  have h₄ := h.inner_curvatureTensor_horizontal
    (h.horizontalLift_mem_orthogonal_ker x u) (h.horizontalLift_mem_orthogonal_ker x v)
    (h.horizontalLift_mem_orthogonal_ker x z) (h.horizontalLift_mem_orthogonal_ker x w)
  simp only [h.mfderiv_horizontalLift] at h₄
  linarith

end HorizontalCurvature

end TauCeti.IsRiemannianSubmersion
