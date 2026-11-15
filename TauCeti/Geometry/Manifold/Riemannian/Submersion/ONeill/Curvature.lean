/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# O'Neill's curvature equations for a Riemannian submersion

Let `f : M → N` be a Riemannian submersion between smooth Riemannian manifolds, with Levi-Civita
connections `cov := leviCivitaConnection I M` and `covN := leviCivitaConnection J N`, fundamental
tensors `A` and `T` (`IsRiemannianSubmersion.oneillA` and `IsRiemannianSubmersion.oneillT`), and
iterated induced connection `cov₂ := cov.hom (cov.hom cov)` on `(1, 2)`-tensor fields.

With Lee's curvature sign convention `R(X, Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z` (so the unit
sphere has sectional curvature `+1`), this file establishes O'Neill's curvature equations:

* **Three vertical, one horizontal** (`inner_curvatureTensor_of_mem_ker_of_mem_orthogonal_ker`):
  for vertical `v₁, v₂, v₃` and horizontal `u`,
  `⟪R(v₁, v₂)v₃, u⟫ = ⟪(∇_{v₁} T)_{v₂} v₃, u⟫ - ⟪(∇_{v₂} T)_{v₁} v₃, u⟫`.
* **Two horizontal, two vertical** (`inner_curvatureTensor_horizontal_vertical_vertical_horizontal`
  and `inner_curvatureTensor_horizontal_horizontal_vertical_vertical`):
  for horizontal `u₁, u₂` and vertical `v₁, v₂`, `⟪R(u₁, v₁)v₂, u₂⟫` equals
  `⟪(∇_{u₁} T)_{v₁} v₂, u₂⟫ + ⟪(∇_{v₁} A)_{u₁} u₂, v₂⟫ + ⟪A_{u₁} v₁, A_{u₂} v₂⟫`
  minus `⟪T_{v₁} u₁, T_{v₂} u₂⟫`, together with the companion formula for `⟪R(u₁, u₂)v₁, v₂⟫`
  via the first Bianchi identity.
* **Mixed sectional curvature** (`sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker`):
  for horizontal `u` and vertical `v`,
  `K_M(u, v) = (⟪(∇_u T)_v v, u⟫ + ‖A_u v‖² - ‖T_v u‖²) / (‖u‖² ‖v‖²)`, reducing to
  `‖A_u v‖² / (‖u‖² ‖v‖²) ≥ 0` when `T` vanishes near `x` (totally geodesic fibres).
* **Three horizontal, one vertical** (`inner_curvatureTensor_of_mem_orthogonal_ker_of_mem_ker`):
  for horizontal `u, v, w` and vertical `z`,
  `⟪R(u, v)w, z⟫ = -⟪(∇_w A)_u v, z⟫ - ⟪A_u v, T_z w⟫ + ⟪A_v w, T_z u⟫ + ⟪A_w u, T_z v⟫`.
* **Four horizontal and horizontal sectional curvature**
  (`starProjection_orthogonal_ker_curvatureTensor_of_mem_orthogonal_ker`,
  `inner_curvatureTensor_of_mem_orthogonal_ker`, and
  `sectionalCurvature_mfderiv_of_mem_orthogonal_ker`):
  for horizontal `u, v, w, z`, `⟪R(u, v)w, z⟫` equals
  `⟪R^N(df u, df v)(df w), df z⟫ + 2⟪A_u v, A_w z⟫ - ⟪A_v w, A_u z⟫ + ⟪A_u w, A_v z⟫`,
  whence `K_N(df u, df v) = K_M(u, v) + 3 ‖A_u v‖² / det(Gram(u, v))` and, on orthonormal
  horizontal fields `X, Y`, `K_N(df X, df Y) = K_M(X, Y) + (3 / 4) ‖v [X, Y]‖²`. In particular, a
  Riemannian submersion never decreases sectional curvature on horizontal planes.

Equations involving only `M`'s curvature tensor or covariant derivatives of `A` and `T` assume
`[T2Space M]` without `[T2Space N]`; `[T2Space N]` enters only when `N`'s pointwise curvature
tensor or sectional curvature is formed.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Theorem 1 and Corollaries 1–2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §D (Theorem 9.28 and
  Corollary 9.29).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7–8 (sign conventions for curvature and sectional curvature).
-/

public section

open Bundle FiberBundle Filter Manifold Set VectorField
open scoped ContDiff InnerProductSpace Manifold Matrix Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

section Preliminaries

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

section Projections

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N} {x : M}

variable (I J) in
private theorem starProjection_orthogonal_ker_add_starProjection_ker
    (f : M → N) (v : TangentSpace I x) :
    (mfderiv I J f x).kerᗮ.starProjection v + (mfderiv I J f x).ker.starProjection v = v := by
  simp [Submodule.starProjection_orthogonal]

private theorem inner_starProjection_orthogonal_ker_left
    (z : TangentSpace I x) {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(mfderiv I J f x).kerᗮ.starProjection z, u⟫_ℝ = ⟪z, u⟫_ℝ := by
  rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hu]

section Gram

variable [FiniteDimensional ℝ F] [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  (h : IsRiemannianSubmersion I J f)
include h

private theorem det_gram_horizontalLift (a b : TangentSpace J (f x)) :
    (Matrix.gram ℝ ![h.horizontalLift x a, h.horizontalLift x b]).det =
      (Matrix.gram ℝ ![a, b]).det := by
  simp only [Matrix.real_det_gram_fin_two, (h.horizontalLift x).inner_map_map]

private theorem det_gram_mfderiv_of_mem_orthogonal_ker {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (Matrix.gram ℝ ![mfderiv I J f x u, mfderiv I J f x v]).det =
      (Matrix.gram ℝ ![u, v]).det := by
  rw [← h.det_gram_horizontalLift, h.horizontalLift_mfderiv_of_mem x hu,
    h.horizontalLift_mfderiv_of_mem x hv]

end Gram

end Projections

section TensorDerivative

variable [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] {x : M}

local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

private theorem hom_hom_apply
    {B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y}
    (hB : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) y (B y)) x)
    {U V : Π y : M, TangentSpace I y} (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x)
    (w : TangentSpace I x) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    cov.hom (cov.hom cov) B x w (U x) (V x) =
      cov (fun y ↦ B y (U y) (V y)) x w - B x (cov U x w) (V x) - B x (U x) (cov V x w) := by
  dsimp only
  set cov := CovariantDerivative.leviCivitaConnection I M
  have houter := congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x ↦ L (V x))
    (CovariantDerivative.hom_apply cov (cov.hom cov) hB hU w)
  simp only [sub_apply] at houter
  rw [houter, CovariantDerivative.hom_apply cov cov (hB.clm_bundle_apply hU) hV w]
  abel

private theorem inner_hom_hom_of_skew
    {B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y}
    (hB : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) y (B y)) x)
    (hskew : ∀ y (a b c : TangentSpace I y), ⟪B y a b, c⟫_ℝ = -⟪b, B y a c⟫_ℝ)
    (w u v z : TangentSpace I x) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.hom (cov.hom cov) B x w u v, z⟫_ℝ = -⟪v, cov.hom (cov.hom cov) B x w u z⟫_ℝ := by
  dsimp only
  set U := FiberBundle.extend E u
  set V := FiberBundle.extend E v
  set Z := FiberBundle.extend E z
  set W := FiberBundle.extend E w
  have hUx : U x = u := FiberBundle.extend_apply_self E u
  have hVx : V x = v := FiberBundle.extend_apply_self E v
  have hZx : Z x = z := FiberBundle.extend_apply_self E z
  have hWx : W x = w := FiberBundle.extend_apply_self E w
  have hU : MDiffAt (T% U) x := FiberBundle.mdifferentiableAt_extend I E u
  have hV : MDiffAt (T% V) x := FiberBundle.mdifferentiableAt_extend I E v
  have hZ : MDiffAt (T% Z) x := FiberBundle.mdifferentiableAt_extend I E z
  have hBUV : MDiffAt (T% (fun y ↦ B y (U y) (V y))) x :=
    (hB.clm_bundle_apply hU).clm_bundle_apply hV
  have hBUZ : MDiffAt (T% (fun y ↦ B y (U y) (Z y))) x :=
    (hB.clm_bundle_apply hU).clm_bundle_apply hZ
  have hmetric := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have heq : (fun y ↦ ⟪B y (U y) (V y), Z y⟫_ℝ) =
      fun y ↦ ⟪(-(fun q ↦ B q (U q) (Z q))) y, V y⟫_ℝ := by
    funext y
    rw [Pi.neg_apply, hskew y (U y) (V y) (Z y), inner_neg_left, real_inner_comm]
  have hd₁ := hmetric.mvfderiv_inner_eq W hBUV hZ
  have hd₂ := hmetric.mvfderiv_inner_eq W (mdifferentiableAt_neg_section hBUZ) hV
  rw [heq] at hd₁
  have hd := hd₁.symm.trans hd₂
  dsimp only at hd
  rw [Pi.neg_apply, (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.neg
    hBUZ, neg_apply, inner_neg_left, inner_neg_left, hUx, hVx, hZx, hWx] at hd
  have h₁ := hom_hom_apply hB hU hV w
  have h₂ := hom_hom_apply hB hU hZ w
  dsimp only at h₁ h₂
  rw [hUx, hVx] at h₁
  rw [hUx, hZx] at h₂
  set cov := CovariantDerivative.leviCivitaConnection I M
  rw [hskew x u v (cov Z x w)] at hd
  rw [h₁, h₂, inner_sub_left, inner_sub_left, inner_sub_right, inner_sub_right,
    hskew x (cov U x w) v z, hskew x u (cov V x w) z,
    real_inner_comm (B x u z) (cov V x w),
    real_inner_comm (cov (fun y ↦ B y (U y) (Z y)) x w) v]
  linarith

end TensorDerivative

end Preliminaries

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

-- Regularity conversions used by `mlieBracket` and `IsMetricCompatible`.
local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

local instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

/-! ### Local extensions and covariant derivatives of the fundamental tensors -/

section LocalHelpers

variable {x : M}
include h

/-- Extend a horizontal vector at `x` to a basic horizontal lift that is smooth on an open
neighbourhood of `x`, without requiring `[T2Space N]`. -/
private theorem exists_contMDiffOn_horizontalLift_eq {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    ∃ (W : Set N) (B : Π z : N, TangentSpace J z),
      IsOpen W ∧ f x ∈ W ∧ CMDiff[W] ∞ (T% B) ∧
      CMDiff[f ⁻¹' W] ∞ (T% (fun y ↦ h.horizontalLift y (B (f y)))) ∧
      h.horizontalLift x (B (f x)) = u := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let : ContMDiffVectorBundle ∞ F (TangentSpace J : N → Type _) J :=
    TangentBundle.contMDiffVectorBundle
  set B : Π z : N, TangentSpace J z := FiberBundle.extend F (mfderiv I J f x u)
  obtain ⟨s, hs, hBs⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) J F (mfderiv I J f x u)
  refine ⟨interior s, B, isOpen_interior, mem_interior_iff_mem_nhds.mpr hs,
    hBs.mono interior_subset, fun y hy ↦ ?_,
    by simp [B, FiberBundle.extend_apply_self, h.horizontalLift_mfderiv_of_mem x hu]⟩
  exact (h.contMDiffAt_horizontalLift
    ((hBs.mono interior_subset).contMDiffAt (isOpen_interior.mem_nhds hy))
    (by simp)).contMDiffWithinAt

/-- Decompose `P x (∇_v W)` along a vertical vector `v` into `P x (∇_v (P W)) + T_v (Q x (W x))`. -/
private theorem starProjection_orthogonal_ker_leviCivitaConnection_of_mem_ker
    {W : Π y : M, TangentSpace I y} (hW : MDiffAt (T% W) x) {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    (mfderiv I J f x).kerᗮ.starProjection (cov W x v) =
      (mfderiv I J f x).kerᗮ.starProjection
          (cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (W y)) x v) +
        h.oneillT x v ((mfderiv I J f x).ker.starProjection (W x)) := by
  dsimp only
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hPW : MDiffAt (T% (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (W y))) x :=
    ((h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
      (by simp)).clm_bundle_apply hW
  have hQW : MDiffAt (T% (fun y ↦ (mfderiv I J f y).ker.starProjection (W y))) x :=
    ((h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
      (by simp)).clm_bundle_apply hW
  have hsplit : W = (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (W y)) +
      fun y ↦ (mfderiv I J f y).ker.starProjection (W y) :=
    funext fun y ↦ (starProjection_orthogonal_ker_add_starProjection_ker I J f (W y)).symm
  have hTQ := h.oneillT_apply_of_eventually_mem_ker hQW
    (.of_forall fun y ↦ Submodule.starProjection_apply_mem _ _) v
  rw [Submodule.starProjection_eq_self_iff.mpr hv] at hTQ
  conv_lhs => rw [hsplit]
  rw [(CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.add hPW hQW,
    add_apply, map_add, ← hTQ]

/-- Decompose `P x (∇_u W)` along a horizontal vector `u` into
`P x (∇_u (P W)) + A_u (Q x (W x))`. -/
private theorem starProjection_orthogonal_ker_leviCivitaConnection_of_mem_orthogonal_ker
    {W : Π y : M, TangentSpace I y} (hW : MDiffAt (T% W) x) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    (mfderiv I J f x).kerᗮ.starProjection (cov W x u) =
      (mfderiv I J f x).kerᗮ.starProjection
          (cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (W y)) x u) +
        h.oneillA x u ((mfderiv I J f x).ker.starProjection (W x)) := by
  dsimp only
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hPW : MDiffAt (T% (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (W y))) x :=
    ((h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
      (by simp)).clm_bundle_apply hW
  have hQW : MDiffAt (T% (fun y ↦ (mfderiv I J f y).ker.starProjection (W y))) x :=
    ((h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
      (by simp)).clm_bundle_apply hW
  have hsplit : W = (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (W y)) +
      fun y ↦ (mfderiv I J f y).ker.starProjection (W y) :=
    funext fun y ↦ (starProjection_orthogonal_ker_add_starProjection_ker I J f (W y)).symm
  have hAQ := h.oneillA_apply_of_eventually_mem_ker hQW
    (.of_forall fun y ↦ Submodule.starProjection_apply_mem _ _) u
  rw [Submodule.starProjection_eq_self_iff.mpr hu] at hAQ
  conv_lhs => rw [hsplit]
  rw [(CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.add hPW hQW,
    add_apply, map_add, ← hAQ]

end LocalHelpers

variable [T2Space M]

section TensorHelpers

variable {x : M}
include h

private theorem mdifferentiableAt_oneillA :
    MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) y
        (h.oneillA y)) x := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  exact (h.contMDiff_oneillA x).mdifferentiableAt (by simp)

private theorem mdifferentiableAt_oneillT :
    MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) y
        (h.oneillT y)) x := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  exact (h.contMDiff_oneillT x).mdifferentiableAt (by simp)

private theorem hom_hom_oneillA_apply {U V : Π y : M, TangentSpace I y}
    (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) (w : TangentSpace I x) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    cov.hom (cov.hom cov) h.oneillA x w (U x) (V x) =
      cov (fun y ↦ h.oneillA y (U y) (V y)) x w -
        h.oneillA x (cov U x w) (V x) - h.oneillA x (U x) (cov V x w) :=
  hom_hom_apply h.mdifferentiableAt_oneillA hU hV w

private theorem hom_hom_oneillT_apply {U V : Π y : M, TangentSpace I y}
    (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) (w : TangentSpace I x) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    cov.hom (cov.hom cov) h.oneillT x w (U x) (V x) =
      cov (fun y ↦ h.oneillT y (U y) (V y)) x w -
        h.oneillT x (cov U x w) (V x) - h.oneillT x (U x) (cov V x w) :=
  hom_hom_apply h.mdifferentiableAt_oneillT hU hV w

/-- The covariant derivative of O'Neill's `A`-tensor remains skew-adjoint in its last two
arguments. -/
theorem inner_hom_hom_oneillA (w u v z : TangentSpace I x) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.hom (cov.hom cov) h.oneillA x w u v, z⟫_ℝ =
      -⟪v, cov.hom (cov.hom cov) h.oneillA x w u z⟫_ℝ :=
  inner_hom_hom_of_skew h.mdifferentiableAt_oneillA h.inner_oneillA w u v z

/-- The covariant derivative of O'Neill's `T`-tensor remains skew-adjoint in its last two
arguments. -/
theorem inner_hom_hom_oneillT (w u v z : TangentSpace I x) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.hom (cov.hom cov) h.oneillT x w u v, z⟫_ℝ =
      -⟪v, cov.hom (cov.hom cov) h.oneillT x w u z⟫_ℝ :=
  inner_hom_hom_of_skew h.mdifferentiableAt_oneillT h.inner_oneillT w u v z

private theorem inner_hom_hom_oneillA_self_of_mem_orthogonal_ker_of_mem_ker
    (w : TangentSpace I x) {u z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hz : z ∈ (mfderiv I J f x).ker) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.hom (cov.hom cov) h.oneillA x w u u, z⟫_ℝ = 0 := by
  dsimp only
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set X : Π y : M, TangentSpace I y :=
    fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (FiberBundle.extend E u y)
  have hXd : MDiffAt (T% X) x :=
    ((h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
      (by simp)).clm_bundle_apply (FiberBundle.mdifferentiableAt_extend I E u)
  have hXx : X x = u := by
    dsimp only [X]
    rw [FiberBundle.extend_apply_self, Submodule.starProjection_eq_self_iff.mpr hu]
  have hAA : (fun y ↦ h.oneillA y (X y) (X y)) = 0 :=
    funext fun y ↦ h.oneillA_self (Submodule.starProjection_apply_mem _ _)
  have heval := h.hom_hom_oneillA_apply hXd hXd w
  dsimp only at heval
  rw [hAA, (CovariantDerivative.leviCivitaConnection I M).zero, Pi.zero_apply, zero_apply,
    hXx] at heval
  set cov := CovariantDerivative.leviCivitaConnection I M
  set p := (mfderiv I J f x).kerᗮ.starProjection (cov X x w)
  set q := (mfderiv I J f x).ker.starProjection (cov X x w)
  have hp : p ∈ (mfderiv I J f x).kerᗮ := Submodule.starProjection_apply_mem _ _
  have hq : q ∈ (mfderiv I J f x).ker := Submodule.starProjection_apply_mem _ _
  have hsplit : cov X x w = p + q :=
    (starProjection_orthogonal_ker_add_starProjection_ker I J f (cov X x w)).symm
  rw [heval, hsplit, map_add, add_apply, map_add,
    h.oneillA_starProjection_ker, zero_apply, add_zero,
    h.oneillA_antisymm hp hu]
  have hcancel : (0 : TangentSpace I x) - -h.oneillA x u p - (h.oneillA x u p + h.oneillA x u q) =
      -h.oneillA x u q := by abel
  rw [hcancel, inner_neg_left,
    Submodule.inner_left_of_mem_orthogonal hz (h.oneillA_apply_mem_orthogonal_ker u hq),
    neg_zero]

private theorem inner_hom_hom_oneillA_antisymm_of_mem_orthogonal_ker_of_mem_ker
    (w : TangentSpace I x) {u₁ u₂ z : TangentSpace I x}
    (hu₁ : u₁ ∈ (mfderiv I J f x).kerᗮ) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).ker) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.hom (cov.hom cov) h.oneillA x w u₁ u₂, z⟫_ℝ =
      -⟪cov.hom (cov.hom cov) h.oneillA x w u₂ u₁, z⟫_ℝ := by
  dsimp only
  have hsum := h.inner_hom_hom_oneillA_self_of_mem_orthogonal_ker_of_mem_ker w (add_mem hu₁ hu₂) hz
  dsimp only at hsum
  simp only [map_add, add_apply, inner_add_left,
    h.inner_hom_hom_oneillA_self_of_mem_orthogonal_ker_of_mem_ker w hu₁ hz,
    h.inner_hom_hom_oneillA_self_of_mem_orthogonal_ker_of_mem_ker w hu₂ hz,
    zero_add, add_zero] at hsum
  linarith

end TensorHelpers

/-! ### Three vertical vectors and one horizontal vector -/

section VerticalThree

variable {x : M}
include h

/-- Extend a vertical vector at `x` to a globally smooth vertical vector field on `M`. -/
private theorem exists_contMDiff_mem_ker {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) :
    ∃ V : Π y : M, TangentSpace I y, CMDiff ∞ (T% V) ∧ V x = v ∧
      ∀ y, V y ∈ (mfderiv I J f y).ker := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  obtain ⟨s, hs, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  refine ⟨fun y ↦ (mfderiv I J f y).ker.starProjection (s y),
    (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply hs,
    Submodule.starProjection_eq_self_iff.mpr hv,
    fun _ ↦ Submodule.starProjection_apply_mem _ _⟩

/-- Evaluate `P x (∇_{V₁ x} (∇_{V₂} V₃))` for globally smooth vertical fields `V₁, V₂, V₃`. -/
private theorem starProjection_orthogonal_ker_second_vertical
    {V₁ V₂ V₃ : Π y : M, TangentSpace I y}
    (hV₂ : CMDiff ∞ (T% V₂)) (hV₃ : CMDiff ∞ (T% V₃))
    (hV₁v : ∀ y, V₁ y ∈ (mfderiv I J f y).ker)
    (hV₂v : ∀ y, V₂ y ∈ (mfderiv I J f y).ker)
    (hV₃v : ∀ y, V₃ y ∈ (mfderiv I J f y).ker) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    (mfderiv I J f x).kerᗮ.starProjection (cov (fun y ↦ cov V₃ y (V₂ y)) x (V₁ x)) =
      (mfderiv I J f x).kerᗮ.starProjection
          (cov.hom (cov.hom cov) h.oneillT x (V₁ x) (V₂ x) (V₃ x)) +
        h.oneillT x ((mfderiv I J f x).ker.starProjection (cov V₂ x (V₁ x))) (V₃ x) +
        h.oneillT x (V₂ x) ((mfderiv I J f x).ker.starProjection (cov V₃ x (V₁ x))) +
        h.oneillT x (V₁ x) ((mfderiv I J f x).ker.starProjection (cov V₃ x (V₂ x))) := by
  intro cov
  have hW : MDiffAt (T% (fun y ↦ cov V₃ y (V₂ y))) x :=
    ((cov.contMDiff_apply hV₂ hV₃) x).mdifferentiableAt (by simp)
  have hPW : (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (cov V₃ y (V₂ y))) =
      fun y ↦ h.oneillT y (V₂ y) (V₃ y) := by
    funext y
    have hT := h.oneillT_apply_of_eventually_mem_ker ((hV₃ y).mdifferentiableAt (by simp))
      (.of_forall hV₃v) (V₂ y)
    rw [Submodule.starProjection_eq_self_iff.mpr (hV₂v y)] at hT
    exact hT.symm
  have hstep := h.starProjection_orthogonal_ker_leviCivitaConnection_of_mem_ker hW (hV₁v x)
  have heval := h.hom_hom_oneillT_apply ((hV₂ x).mdifferentiableAt (by simp))
    ((hV₃ x).mdifferentiableAt (by simp)) (V₁ x)
  have hTcov : cov (fun y ↦ h.oneillT y (V₂ y) (V₃ y)) x (V₁ x) =
      cov.hom (cov.hom cov) h.oneillT x (V₁ x) (V₂ x) (V₃ x) +
        h.oneillT x (cov V₂ x (V₁ x)) (V₃ x) +
        h.oneillT x (V₂ x) (cov V₃ x (V₁ x)) := by
    rw [heval]
    abel
  have hsplit₃ := (starProjection_orthogonal_ker_add_starProjection_ker I J f
    (cov V₃ x (V₁ x))).symm
  have hp₁ : (mfderiv I J f x).kerᗮ.starProjection
      (h.oneillT x (cov V₂ x (V₁ x)) (V₃ x)) =
      h.oneillT x ((mfderiv I J f x).ker.starProjection (cov V₂ x (V₁ x))) (V₃ x) := by
    rw [← h.oneillT_starProjection_ker,
      Submodule.starProjection_eq_self_iff.mpr
        (h.oneillT_apply_mem_orthogonal_ker _ (hV₃v x))]
  have hp₂ : (mfderiv I J f x).kerᗮ.starProjection (h.oneillT x (V₂ x) (cov V₃ x (V₁ x))) =
      h.oneillT x (V₂ x) ((mfderiv I J f x).ker.starProjection (cov V₃ x (V₁ x))) := by
    conv_lhs => rw [hsplit₃]
    rw [map_add, map_add,
      (Submodule.starProjection_apply_eq_zero_iff _).mpr (by
        rw [Submodule.orthogonal_orthogonal]
        exact h.oneillT_apply_mem_ker (V₂ x) (Submodule.starProjection_apply_mem _ _)),
      zero_add,
      Submodule.starProjection_eq_self_iff.mpr
        (h.oneillT_apply_mem_orthogonal_ker (V₂ x) (Submodule.starProjection_apply_mem _ _))]
  rw [hstep, hPW, hTcov, map_add, map_add, hp₁, hp₂]

/-- **O'Neill's horizontal-vertical curvature equation on three vertical vectors (vector form).**
For vertical tangent vectors `v₁, v₂, v₃`, the horizontal component of `R(v₁, v₂)v₃` equals the
horizontal component of `(∇_{v₁} T)_{v₂} v₃ - (∇_{v₂} T)_{v₁} v₃`. -/
theorem starProjection_orthogonal_ker_curvatureTensor_of_mem_ker
    {v₁ v₂ v₃ : TangentSpace I x}
    (hv₁ : v₁ ∈ (mfderiv I J f x).ker) (hv₂ : v₂ ∈ (mfderiv I J f x).ker)
    (hv₃ : v₃ ∈ (mfderiv I J f x).ker) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    (mfderiv I J f x).kerᗮ.starProjection (cov.curvatureTensor x v₁ v₂ v₃) =
      (mfderiv I J f x).kerᗮ.starProjection
        (cov.hom (cov.hom cov) h.oneillT x v₁ v₂ v₃ -
          cov.hom (cov.hom cov) h.oneillT x v₂ v₁ v₃) := by
  intro cov
  obtain ⟨V₁, hV₁, rfl, hV₁v⟩ := h.exists_contMDiff_mem_ker hv₁
  obtain ⟨V₂, hV₂, rfl, hV₂v⟩ := h.exists_contMDiff_mem_ker hv₂
  obtain ⟨V₃, hV₃, rfl, hV₃v⟩ := h.exists_contMDiff_mem_ker hv₃
  have h₁₂ := h.starProjection_orthogonal_ker_second_vertical hV₂ hV₃ hV₁v hV₂v hV₃v (x := x)
  have h₂₁ := h.starProjection_orthogonal_ker_second_vertical hV₁ hV₃ hV₂v hV₁v hV₃v (x := x)
  have htor := ((CovariantDerivative.torsion_eq_zero_iff cov).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I))
    ((hV₁ x).mdifferentiableAt (by simp)) ((hV₂ x).mdifferentiableAt (by simp))
  have hbr_mem : mlieBracket I V₁ V₂ x ∈ (mfderiv I J f x).ker :=
    (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv
      (by simp [minSmoothness_of_isRCLikeNormedField])
      ((hV₁ x).mdifferentiableAt (by simp)) ((hV₂ x).mdifferentiableAt (by simp))
      (.of_forall hV₁v) (.of_forall hV₂v)
  have hbr : (mfderiv I J f x).kerᗮ.starProjection (cov V₃ x (mlieBracket I V₁ V₂ x)) =
      h.oneillT x ((mfderiv I J f x).ker.starProjection (cov V₂ x (V₁ x))) (V₃ x) -
        h.oneillT x ((mfderiv I J f x).ker.starProjection (cov V₁ x (V₂ x))) (V₃ x) := by
    have hT := h.oneillT_apply_of_eventually_mem_ker ((hV₃ x).mdifferentiableAt (by simp))
      (.of_forall hV₃v) (mlieBracket I V₁ V₂ x)
    rw [Submodule.starProjection_eq_self_iff.mpr hbr_mem] at hT
    rw [← hT, ← htor, ← h.oneillT_starProjection_ker, map_sub, map_sub,
      sub_apply]
  rw [cov.curvatureTensor_apply x hV₁ hV₂ hV₃, CovariantDerivative.curvatureOperator_apply,
    map_sub, map_sub, h₁₂, h₂₁, hbr, map_sub]
  abel

/-- **O'Neill's first curvature equation.** For vertical `v₁, v₂, v₃` and horizontal `u`,
`⟪R(v₁, v₂)v₃, u⟫ = ⟪(∇_{v₁} T)_{v₂} v₃, u⟫ - ⟪(∇_{v₂} T)_{v₁} v₃, u⟫`. -/
theorem inner_curvatureTensor_of_mem_ker_of_mem_orthogonal_ker
    {v₁ v₂ v₃ u : TangentSpace I x}
    (hv₁ : v₁ ∈ (mfderiv I J f x).ker) (hv₂ : v₂ ∈ (mfderiv I J f x).ker)
    (hv₃ : v₃ ∈ (mfderiv I J f x).ker) (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.curvatureTensor x v₁ v₂ v₃, u⟫_ℝ =
      ⟪cov.hom (cov.hom cov) h.oneillT x v₁ v₂ v₃, u⟫_ℝ -
        ⟪cov.hom (cov.hom cov) h.oneillT x v₂ v₁ v₃, u⟫_ℝ := by
  intro cov
  rw [← inner_starProjection_orthogonal_ker_left _ hu,
    h.starProjection_orthogonal_ker_curvatureTensor_of_mem_ker hv₁ hv₂ hv₃,
    inner_starProjection_orthogonal_ker_left _ hu, inner_sub_left]

end VerticalThree

/-! ### Two horizontal and two vertical vectors, and mixed sectional curvature -/

section Mixed

variable {x : M}
include h

private theorem inner_second_cov_vertical_along_horizontal
    {V₁ V₂ : Π y : M, TangentSpace I y}
    (hV₁ : CMDiff ∞ (T% V₁)) (hV₂ : CMDiff ∞ (T% V₂))
    (hV₁v : ∀ y, V₁ y ∈ (mfderiv I J f y).ker)
    (hV₂v : ∀ y, V₂ y ∈ (mfderiv I J f y).ker)
    {u₁ u₂ : TangentSpace I x}
    (hu₁ : u₁ ∈ (mfderiv I J f x).kerᗮ) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov (fun y ↦ cov V₂ y (V₁ y)) x u₁, u₂⟫_ℝ =
      ⟪cov.hom (cov.hom cov) h.oneillT x u₁ (V₁ x) (V₂ x), u₂⟫_ℝ +
        ⟪h.oneillT x ((mfderiv I J f x).ker.starProjection (cov V₁ x u₁)) (V₂ x), u₂⟫_ℝ +
        ⟪h.oneillT x (V₁ x) ((mfderiv I J f x).ker.starProjection (cov V₂ x u₁)), u₂⟫_ℝ +
        ⟪h.oneillA x u₁ ((mfderiv I J f x).ker.starProjection (cov V₂ x (V₁ x))), u₂⟫_ℝ := by
  intro cov
  have hW : MDiffAt (T% (fun y ↦ cov V₂ y (V₁ y))) x :=
    ((cov.contMDiff_apply hV₁ hV₂) x).mdifferentiableAt (by simp)
  have hPW : (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (cov V₂ y (V₁ y))) =
      fun y ↦ h.oneillT y (V₁ y) (V₂ y) := by
    funext y
    have hT := h.oneillT_apply_of_eventually_mem_ker ((hV₂ y).mdifferentiableAt (by simp))
      (.of_forall hV₂v) (V₁ y)
    rw [Submodule.starProjection_eq_self_iff.mpr (hV₁v y)] at hT
    exact hT.symm
  have hstep := h.starProjection_orthogonal_ker_leviCivitaConnection_of_mem_orthogonal_ker hW hu₁
  have heval := h.hom_hom_oneillT_apply ((hV₁ x).mdifferentiableAt (by simp))
    ((hV₂ x).mdifferentiableAt (by simp)) u₁
  have hTcov : cov (fun y ↦ h.oneillT y (V₁ y) (V₂ y)) x u₁ =
      cov.hom (cov.hom cov) h.oneillT x u₁ (V₁ x) (V₂ x) +
        h.oneillT x (cov V₁ x u₁) (V₂ x) + h.oneillT x (V₁ x) (cov V₂ x u₁) := by
    rw [heval]
    abel
  have hsplit := (starProjection_orthogonal_ker_add_starProjection_ker I J f (cov V₂ x u₁)).symm
  have hTorth : ⟪h.oneillT x (V₁ x) (cov V₂ x u₁), u₂⟫_ℝ =
      ⟪h.oneillT x (V₁ x) ((mfderiv I J f x).ker.starProjection (cov V₂ x u₁)), u₂⟫_ℝ := by
    conv_lhs => rw [hsplit]
    rw [map_add, inner_add_left,
      Submodule.inner_right_of_mem_orthogonal
        (h.oneillT_apply_mem_ker (V₁ x) (Submodule.starProjection_apply_mem _ _)) hu₂,
      zero_add]
  rw [← inner_starProjection_orthogonal_ker_left _ hu₂, hstep, hPW, inner_add_left,
    inner_starProjection_orthogonal_ker_left _ hu₂, hTcov, inner_add_left, inner_add_left,
    ← h.oneillT_starProjection_ker x (cov V₁ x u₁), hTorth]

private theorem inner_second_cov_vertical_along_basic_horizontal
    {W : Set N} (hWopen : IsOpen W) (hfxW : f x ∈ W)
    {B₁ : Π z : N, TangentSpace J z} (hB₁W : CMDiff[W] ∞ (T% B₁))
    {V₂ : Π y : M, TangentSpace I y} (hV₂ : CMDiff ∞ (T% V₂))
    (hV₂v : ∀ y, V₂ y ∈ (mfderiv I J f y).ker)
    {v₁ u₂ : TangentSpace I x}
    (hv₁ : v₁ ∈ (mfderiv I J f x).ker) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    let X₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
    ⟪cov (fun y ↦ cov V₂ y (X₁ y)) x v₁, u₂⟫_ℝ =
      -⟪cov.hom (cov.hom cov) h.oneillA x v₁ (X₁ x) u₂, V₂ x⟫_ℝ -
        ⟪h.oneillA x (X₁ x) v₁, h.oneillA x u₂ (V₂ x)⟫_ℝ +
        ⟪h.oneillA x (X₁ x) ((mfderiv I J f x).ker.starProjection (cov V₂ x v₁)), u₂⟫_ℝ +
        ⟪h.oneillT x v₁ ((mfderiv I J f x).ker.starProjection (cov V₂ x (X₁ x))), u₂⟫_ℝ := by
  intro cov X₁
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set U : Set M := f ⁻¹' W
  have hUopen : IsOpen U := hWopen.preimage h.isSubmersion.contMDiff.continuous
  have hX₁U : CMDiff[U] ∞ (T% X₁) := fun y hy ↦
    (h.contMDiffAt_horizontalLift (hB₁W.contMDiffAt (hWopen.mem_nhds hy))
      (by simp)).contMDiffWithinAt
  have hX₁d : MDiffAt (T% X₁) x :=
    (hX₁U.contMDiffAt (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp)
  have hV₂X₁d : MDiffAt (T% (fun y ↦ cov V₂ y (X₁ y))) x :=
    ((((CovariantDerivative.contMDiffOn_leviCivitaConnection (n := ∞) (m := ∞) (k := ∞)
      hUopen le_rfl le_rfl (by simpa using hV₂.contMDiffOn.mono (subset_univ U))).clm_bundle_apply
      hX₁U).contMDiffAt (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp))
  have hPW : (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (cov V₂ y (X₁ y))) =
      fun y ↦ h.oneillA y (X₁ y) (V₂ y) := by
    funext y
    have hA := h.oneillA_apply_of_eventually_mem_ker ((hV₂ y).mdifferentiableAt (by simp))
      (.of_forall hV₂v) (X₁ y)
    rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker y _)] at hA
    exact hA.symm
  have hstep := h.starProjection_orthogonal_ker_leviCivitaConnection_of_mem_ker hV₂X₁d hv₁
  have heval := h.hom_hom_oneillA_apply hX₁d ((hV₂ x).mdifferentiableAt (by simp)) v₁
  have hAcov : cov (fun y ↦ h.oneillA y (X₁ y) (V₂ y)) x v₁ =
      cov.hom (cov.hom cov) h.oneillA x v₁ (X₁ x) (V₂ x) +
        h.oneillA x (cov X₁ x v₁) (V₂ x) + h.oneillA x (X₁ x) (cov V₂ x v₁) := by
    rw [heval]
    abel
  have hskewA : ⟪cov.hom (cov.hom cov) h.oneillA x v₁ (X₁ x) (V₂ x), u₂⟫_ℝ =
      -⟪cov.hom (cov.hom cov) h.oneillA x v₁ (X₁ x) u₂, V₂ x⟫_ℝ := by
    rw [h.inner_hom_hom_oneillA, real_inner_comm]
  have hX₁v₁ := h.leviCivitaConnection_horizontalLift_of_mem_ker
    ((hB₁W.contMDiffAt (hWopen.mem_nhds hfxW)).of_le (by simp)) hv₁
  have hAA : ⟪h.oneillA x (cov X₁ x v₁) (V₂ x), u₂⟫_ℝ =
      -⟪h.oneillA x (X₁ x) v₁, h.oneillA x u₂ (V₂ x)⟫_ℝ := by
    have hTker : h.oneillA x (h.oneillT x v₁ (X₁ x)) = 0 := by
      rw [← Submodule.starProjection_eq_self_iff.mpr
        (h.oneillT_apply_mem_ker v₁ (h.horizontalLift_mem_orthogonal_ker x _)),
        h.oneillA_starProjection_ker]
    rw [hX₁v₁, map_add, add_apply, hTker, zero_apply,
      add_zero, h.inner_oneillA,
      h.oneillA_antisymm (h.oneillA_apply_mem_orthogonal_ker (X₁ x) hv₁) hu₂,
      inner_neg_right, neg_neg, real_inner_comm (h.oneillA x u₂ (V₂ x)),
      h.inner_oneillA, neg_neg]
  have hsplit := (starProjection_orthogonal_ker_add_starProjection_ker I J f (cov V₂ x v₁)).symm
  have hAorth : ⟪h.oneillA x (X₁ x) (cov V₂ x v₁), u₂⟫_ℝ =
      ⟪h.oneillA x (X₁ x) ((mfderiv I J f x).ker.starProjection (cov V₂ x v₁)), u₂⟫_ℝ := by
    conv_lhs => rw [hsplit]
    rw [map_add, inner_add_left,
      Submodule.inner_right_of_mem_orthogonal
        (h.oneillA_apply_mem_ker (X₁ x) (Submodule.starProjection_apply_mem _ _)) hu₂,
      zero_add]
  rw [← inner_starProjection_orthogonal_ker_left _ hu₂, hstep, hPW, inner_add_left,
    inner_starProjection_orthogonal_ker_left _ hu₂, hAcov, inner_add_left, inner_add_left,
    hskewA, hAA, hAorth]
  ring

/-- **O'Neill's mixed curvature equation (`⟨R(u₁, v₁)v₂, u₂⟩`).** For horizontal `u₁, u₂` and
vertical `v₁, v₂`, `⟪R(u₁, v₁)v₂, u₂⟫` equals
`⟪(∇_{u₁} T)_{v₁} v₂, u₂⟫ + ⟪(∇_{v₁} A)_{u₁} u₂, v₂⟫ + ⟪A_{u₁} v₁, A_{u₂} v₂⟫`
minus `⟪T_{v₁} u₁, T_{v₂} u₂⟫`. -/
theorem inner_curvatureTensor_horizontal_vertical_vertical_horizontal
    {u₁ u₂ v₁ v₂ : TangentSpace I x}
    (hu₁ : u₁ ∈ (mfderiv I J f x).kerᗮ) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ)
    (hv₁ : v₁ ∈ (mfderiv I J f x).ker) (hv₂ : v₂ ∈ (mfderiv I J f x).ker) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.curvatureTensor x u₁ v₁ v₂, u₂⟫_ℝ =
      ⟪cov.hom (cov.hom cov) h.oneillT x u₁ v₁ v₂, u₂⟫_ℝ +
        ⟪cov.hom (cov.hom cov) h.oneillA x v₁ u₁ u₂, v₂⟫_ℝ +
        ⟪h.oneillA x u₁ v₁, h.oneillA x u₂ v₂⟫_ℝ -
        ⟪h.oneillT x v₁ u₁, h.oneillT x v₂ u₂⟫_ℝ := by
  intro cov
  obtain ⟨W, B₁, hWopen, hfxW, hB₁W, hX₁U, hX₁x⟩ := h.exists_contMDiffOn_horizontalLift_eq hu₁
  obtain ⟨V₁, hV₁, rfl, hV₁v⟩ := h.exists_contMDiff_mem_ker hv₁
  obtain ⟨V₂, hV₂, rfl, hV₂v⟩ := h.exists_contMDiff_mem_ker hv₂
  set X₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
  have hX₁x' : X₁ x = u₁ := hX₁x
  have hUopen : IsOpen (f ⁻¹' W) := hWopen.preimage h.isSubmersion.contMDiff.continuous
  have hcurv : cov.curvatureTensor x u₁ (V₁ x) (V₂ x) = cov.curvatureOperator X₁ V₁ V₂ x := by
    rw [← hX₁x]
    exact cov.curvatureTensor_apply_of_contMDiffOn x hUopen hfxW hX₁U hV₁.contMDiffOn
      hV₂.contMDiffOn
  have ht₁ := h.inner_second_cov_vertical_along_horizontal hV₁ hV₂ hV₁v hV₂v hu₁ hu₂
  have ht₂ := h.inner_second_cov_vertical_along_basic_horizontal hWopen hfxW hB₁W hV₂ hV₂v hv₁ hu₂
  have hbr := h.mlieBracket_horizontalLift_of_eventually_mem_ker
    ((hB₁W.contMDiffAt (hWopen.mem_nhds hfxW)).of_le (by simp))
    ((hV₁ x).mdifferentiableAt (by simp)) (.of_forall hV₁v)
  have hbr_mem : mlieBracket I X₁ V₁ x ∈ (mfderiv I J f x).ker := by
    rw [hbr]
    exact sub_mem (Submodule.starProjection_apply_mem _ _)
      (h.oneillT_apply_mem_ker (V₁ x) (h.horizontalLift_mem_orthogonal_ker x _))
  have ht₃ : ⟪cov V₂ x (mlieBracket I X₁ V₁ x), u₂⟫_ℝ =
      ⟪h.oneillT x ((mfderiv I J f x).ker.starProjection (cov V₁ x u₁)) (V₂ x), u₂⟫_ℝ +
        ⟪h.oneillT x (V₁ x) u₁, h.oneillT x (V₂ x) u₂⟫_ℝ := by
    have hTV₂ := h.oneillT_apply_of_eventually_mem_ker ((hV₂ x).mdifferentiableAt (by simp))
      (.of_forall hV₂v) (mlieBracket I X₁ V₁ x)
    rw [Submodule.starProjection_eq_self_iff.mpr hbr_mem] at hTV₂
    have hTT : ⟪h.oneillT x (h.oneillT x (V₁ x) u₁) (V₂ x), u₂⟫_ℝ =
        -⟪h.oneillT x (V₁ x) u₁, h.oneillT x (V₂ x) u₂⟫_ℝ := by
      rw [h.oneillT_comm (h.oneillT_apply_mem_ker (V₁ x) hu₁) hv₂, h.inner_oneillT]
    rw [← inner_starProjection_orthogonal_ker_left _ hu₂, ← hTV₂, hbr, hX₁x, map_sub,
      sub_apply, inner_sub_left, hTT, sub_neg_eq_add]
  dsimp only at ht₁ ht₂
  rw [hX₁x] at ht₂
  rw [hcurv, CovariantDerivative.curvatureOperator_apply, hX₁x', inner_sub_left, inner_sub_left,
    ht₁, ht₂, ht₃]
  linarith

/-- **O'Neill's companion mixed curvature equation (`⟨R(u₁, u₂)v₁, v₂⟩`).** Obtained by combining
`inner_curvatureTensor_horizontal_vertical_vertical_horizontal` with the first Bianchi identity and
the alternating property of `v ((∇_{v₁} A)_{u₁} u₂)`. -/
theorem inner_curvatureTensor_horizontal_horizontal_vertical_vertical
    {u₁ u₂ v₁ v₂ : TangentSpace I x}
    (hu₁ : u₁ ∈ (mfderiv I J f x).kerᗮ) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ)
    (hv₁ : v₁ ∈ (mfderiv I J f x).ker) (hv₂ : v₂ ∈ (mfderiv I J f x).ker) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.curvatureTensor x u₁ u₂ v₁, v₂⟫_ℝ =
      ⟪cov.hom (cov.hom cov) h.oneillT x u₂ v₁ v₂, u₁⟫_ℝ -
        ⟪cov.hom (cov.hom cov) h.oneillT x u₁ v₁ v₂, u₂⟫_ℝ -
        2 * ⟪cov.hom (cov.hom cov) h.oneillA x v₁ u₁ u₂, v₂⟫_ℝ +
        ⟪h.oneillA x u₂ v₁, h.oneillA x u₁ v₂⟫_ℝ -
        ⟪h.oneillA x u₁ v₁, h.oneillA x u₂ v₂⟫_ℝ +
        ⟪h.oneillT x v₁ u₁, h.oneillT x v₂ u₂⟫_ℝ -
        ⟪h.oneillT x v₁ u₂, h.oneillT x v₂ u₁⟫_ℝ := by
  intro cov
  have hmetric := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hbianchi := congrArg (fun q ↦ ⟪q, v₂⟫_ℝ)
    (cov.curvatureTensor_cyclic_eq_zero (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)
      x u₁ u₂ v₁)
  simp only [inner_add_left, inner_zero_left] at hbianchi
  have hs₁ : ⟪cov.curvatureTensor x u₂ v₁ u₁, v₂⟫_ℝ =
      -⟪cov.curvatureTensor x u₂ v₁ v₂, u₁⟫_ℝ := by
    rw [hmetric.inner_curvatureTensor_eq_neg, real_inner_comm]
  have hs₂ : ⟪cov.curvatureTensor x v₁ u₁ u₂, v₂⟫_ℝ =
      ⟪cov.curvatureTensor x u₁ v₁ v₂, u₂⟫_ℝ := by
    rw [cov.curvatureTensor_antisymm x v₁ u₁, LinearMap.neg_apply, inner_neg_left,
      hmetric.inner_curvatureTensor_eq_neg, neg_neg, real_inner_comm]
  have hAalt := h.inner_hom_hom_oneillA_antisymm_of_mem_orthogonal_ker_of_mem_ker v₁ hu₂ hu₁ hv₂
  rw [hs₁, hs₂,
    h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hu₂ hu₁ hv₁ hv₂,
    h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hu₁ hu₂ hv₁ hv₂,
    hAalt] at hbianchi
  linarith

/-- Specialization of O'Neill's mixed curvature equation to the sectional-curvature numerator
`⟪R(u, v)v, u⟫` of a horizontal vector `u` and a vertical vector `v`. -/
theorem inner_curvatureTensor_self_of_mem_orthogonal_ker_of_mem_ker
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.curvatureTensor x u v v, u⟫_ℝ =
      ⟪cov.hom (cov.hom cov) h.oneillT x u v v, u⟫_ℝ +
        ‖h.oneillA x u v‖ ^ 2 - ‖h.oneillT x v u‖ ^ 2 := by
  intro cov
  rw [h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hu hu hv hv,
    h.inner_hom_hom_oneillA_self_of_mem_orthogonal_ker_of_mem_ker v hu hv,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, add_zero]

/-- **O'Neill's mixed sectional curvature formula.** For a horizontal vector `u` and a vertical
vector `v`,
`K_M(u, v) = (⟪(∇_u T)_v v, u⟫ + ‖A_u v‖² - ‖T_v u‖²) / (‖u‖² ‖v‖²)`.
When either vector is zero, both sides vanish by the totalized quotient convention. -/
theorem sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    cov.sectionalCurvature (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v =
      (⟪cov.hom (cov.hom cov) h.oneillT x u v v, u⟫_ℝ +
        ‖h.oneillA x u v‖ ^ 2 - ‖h.oneillT x v u‖ ^ 2) / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  intro cov
  rw [CovariantDerivative.sectionalCurvature_apply,
    h.inner_curvatureTensor_self_of_mem_orthogonal_ker_of_mem_ker hu hv,
    Matrix.real_det_gram_fin_two, Submodule.inner_left_of_mem_orthogonal hv hu,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, zero_pow two_ne_zero, sub_zero]

/-- When O'Neill's vertical tensor `T` vanishes in a neighbourhood of `x` (totally geodesic fibres
near `x`), the sectional curvature of a mixed horizontal-vertical plane at `x` is
`‖A_u v‖² / (‖u‖² ‖v‖²)`. -/
theorem sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero
    (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v =
      ‖h.oneillA x u v‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  set V := FiberBundle.extend E v
  have hVx : V x = v := FiberBundle.extend_apply_self E v
  have hVd : MDiffAt (T% V) x := FiberBundle.mdifferentiableAt_extend I E v
  have hTVV : MDiffAt (T% (fun y ↦ h.oneillT y (V y) (V y))) x :=
    (h.mdifferentiableAt_oneillT.clm_bundle_apply hVd).clm_bundle_apply hVd
  have heq0 : ∀ᶠ y in 𝓝 x, h.oneillT y (V y) (V y) = (0 : Π z : M, TangentSpace I z) y := by
    filter_upwards [hT] with y hy
    simp [hy]
  have hcov0 : CovariantDerivative.leviCivitaConnection I M
      (fun y ↦ h.oneillT y (V y) (V y)) x u = 0 := by
    let cov := CovariantDerivative.leviCivitaConnection I M
    rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq (σ' := 0) hTVV
      (mdifferentiableAt_zeroSection ℝ _) univ_mem heq0, cov.zero, Pi.zero_apply, zero_apply]
  have heval := h.hom_hom_oneillT_apply hVd hVd u
  dsimp only at heval
  rw [hVx, hcov0, hT.self_of_nhds] at heval
  simp only [zero_apply, sub_zero] at heval
  rw [h.sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker hu hv, heval, hT.self_of_nhds]
  simp

/-- When O'Neill's vertical tensor `T` vanishes near `x`, every mixed horizontal-vertical plane at
`x` has nonnegative sectional curvature. -/
theorem sectionalCurvature_nonneg_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero
    (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    0 ≤ (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v := by
  rw [h.sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero hT hu hv]
  positivity

end Mixed

/-! ### Three horizontal vectors and one vertical vector -/

section HorizontalThree

variable {x : M}
include h

private theorem inner_second_cov_basic_horizontal_along_vertical_along_horizontal
    {W : Set N} (hWopen : IsOpen W) (hfxW : f x ∈ W)
    {B₁ : Π z : N, TangentSpace J z} (hB₁W : CMDiff[W] ∞ (T% B₁))
    {V : Π y : M, TangentSpace I y} (hV : CMDiff ∞ (T% V))
    (hVv : ∀ y, V y ∈ (mfderiv I J f y).ker)
    {u₃ u₂ : TangentSpace I x}
    (hu₃ : u₃ ∈ (mfderiv I J f x).kerᗮ) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covN := CovariantDerivative.leviCivitaConnection J N
    let X₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
    ⟪cov (fun y ↦ cov X₁ y (V y)) x u₃, u₂⟫_ℝ =
      -⟪cov.hom (cov.hom cov) h.oneillA x u₃ (X₁ x) u₂, V x⟫_ℝ -
        ⟪V x, h.oneillA x (h.horizontalLift x (covN B₁ (f x) (mfderiv I J f x u₃))) u₂⟫_ℝ +
        ⟪h.oneillA x (X₁ x) ((mfderiv I J f x).ker.starProjection (cov V x u₃)), u₂⟫_ℝ +
        ⟪h.oneillA x u₂ u₃, h.oneillT x (V x) (X₁ x)⟫_ℝ := by
  intro cov covN X₁
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set U : Set M := f ⁻¹' W
  have hUopen : IsOpen U := hWopen.preimage h.isSubmersion.contMDiff.continuous
  have hX₁U : CMDiff[U] ∞ (T% X₁) := fun y hy ↦
    (h.contMDiffAt_horizontalLift (hB₁W.contMDiffAt (hWopen.mem_nhds hy))
      (by simp)).contMDiffWithinAt
  have hX₁d : MDiffAt (T% X₁) x :=
    (hX₁U.contMDiffAt (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp)
  have hVd : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hAd : MDiffAt (T% (fun y ↦ h.oneillA y (X₁ y) (V y))) x :=
    (h.mdifferentiableAt_oneillA.clm_bundle_apply hX₁d).clm_bundle_apply hVd
  have hTd : MDiffAt (T% (fun y ↦ h.oneillT y (V y) (X₁ y))) x :=
    (h.mdifferentiableAt_oneillT.clm_bundle_apply hVd).clm_bundle_apply hX₁d
  have hX₁Vd : MDiffAt (T% (fun y ↦ cov X₁ y (V y))) x :=
    ((((CovariantDerivative.contMDiffOn_leviCivitaConnection (n := ∞) (m := ∞) (k := ∞)
      hUopen le_rfl le_rfl (by simpa using hX₁U)).clm_bundle_apply
      (hV.contMDiffOn.mono (subset_univ U))).contMDiffAt
      (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp))
  have heqU : (fun y ↦ cov X₁ y (V y)) =ᶠ[𝓝 x]
      (fun y ↦ h.oneillA y (X₁ y) (V y)) + fun y ↦ h.oneillT y (V y) (X₁ y) := by
    filter_upwards [hUopen.mem_nhds hfxW] with y hy
    exact h.leviCivitaConnection_horizontalLift_of_mem_ker
      ((hB₁W.contMDiffAt (hWopen.mem_nhds hy)).of_le (by simp)) (hVv y)
  have hcongr := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hX₁Vd (mdifferentiableAt_add_section hAd hTd) univ_mem heqU
  have heval := h.hom_hom_oneillA_apply hX₁d hVd u₃
  have hAcov : cov (fun y ↦ h.oneillA y (X₁ y) (V y)) x u₃ =
      cov.hom (cov.hom cov) h.oneillA x u₃ (X₁ x) (V x) +
        h.oneillA x (cov X₁ x u₃) (V x) + h.oneillA x (X₁ x) (cov V x u₃) := by
    rw [heval]
    abel
  have hX₁u₃ := h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
    ((hB₁W.contMDiffAt (hWopen.mem_nhds hfxW)).of_le (by simp)) hu₃
  have hA_X₁u₃ : ⟪h.oneillA x (cov X₁ x u₃) (V x), u₂⟫_ℝ =
      -⟪V x, h.oneillA x (h.horizontalLift x (covN B₁ (f x) (mfderiv I J f x u₃))) u₂⟫_ℝ := by
    have hAker : h.oneillA x (h.oneillA x u₃ (X₁ x)) = 0 := by
      rw [← Submodule.starProjection_eq_self_iff.mpr
        (h.oneillA_apply_mem_ker u₃ (h.horizontalLift_mem_orthogonal_ker x _)),
        h.oneillA_starProjection_ker]
    rw [hX₁u₃, map_add, add_apply, hAker, zero_apply,
      add_zero, h.inner_oneillA]
  have hsplit := (starProjection_orthogonal_ker_add_starProjection_ker I J f (cov V x u₃)).symm
  have hAorth : ⟪h.oneillA x (X₁ x) (cov V x u₃), u₂⟫_ℝ =
      ⟪h.oneillA x (X₁ x) ((mfderiv I J f x).ker.starProjection (cov V x u₃)), u₂⟫_ℝ := by
    conv_lhs => rw [hsplit]
    rw [map_add, inner_add_left,
      Submodule.inner_right_of_mem_orthogonal
        (h.oneillA_apply_mem_ker (X₁ x) (Submodule.starProjection_apply_mem _ _)) hu₂,
      zero_add]
  have hTcov : ⟪cov (fun y ↦ h.oneillT y (V y) (X₁ y)) x u₃, u₂⟫_ℝ =
      ⟪h.oneillA x u₂ u₃, h.oneillT x (V x) (X₁ x)⟫_ℝ := by
    have hAT := h.oneillA_apply_of_eventually_mem_ker hTd
      (.of_forall fun y ↦ h.oneillT_apply_mem_ker (V y) (h.horizontalLift_mem_orthogonal_ker y _))
      u₃
    rw [Submodule.starProjection_eq_self_iff.mpr hu₃] at hAT
    rw [← inner_starProjection_orthogonal_ker_left _ hu₂, ← hAT, h.inner_oneillA,
      h.oneillA_antisymm hu₃ hu₂, inner_neg_right, neg_neg, real_inner_comm]
  rw [hcongr, cov.isCovariantDerivativeOnUniv.add hAd hTd, add_apply,
    inner_add_left, hAcov, inner_add_left, inner_add_left,
    h.inner_hom_hom_oneillA, real_inner_comm (V x), hA_X₁u₃, hAorth, hTcov]
  ring

private theorem inner_second_cov_basic_horizontal_along_horizontal_along_vertical
    {W : Set N} (hWopen : IsOpen W) (hfxW : f x ∈ W)
    {B₁ B₃ : Π z : N, TangentSpace J z}
    (hB₁W : CMDiff[W] ∞ (T% B₁)) (hB₃W : CMDiff[W] ∞ (T% B₃))
    {v u₂ : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covN := CovariantDerivative.leviCivitaConnection J N
    let X₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
    let X₃ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₃ (f y))
    ⟪cov (fun y ↦ cov X₁ y (X₃ y)) x v, u₂⟫_ℝ =
      -⟪v, h.oneillA x (h.horizontalLift x (covN B₁ (f x) (B₃ (f x)))) u₂⟫_ℝ -
        ⟪h.oneillA x (X₃ x) (X₁ x), h.oneillT x v u₂⟫_ℝ := by
  intro cov covN X₁ X₃
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  set U : Set M := f ⁻¹' W
  have hUopen : IsOpen U := hWopen.preimage h.isSubmersion.contMDiff.continuous
  have hX₁U : CMDiff[U] ∞ (T% X₁) := fun y hy ↦
    (h.contMDiffAt_horizontalLift (hB₁W.contMDiffAt (hWopen.mem_nhds hy))
      (by simp)).contMDiffWithinAt
  have hX₃U : CMDiff[U] ∞ (T% X₃) := fun y hy ↦
    (h.contMDiffAt_horizontalLift (hB₃W.contMDiffAt (hWopen.mem_nhds hy))
      (by simp)).contMDiffWithinAt
  have hB₁₃W : CMDiff[W] ∞ (T% (fun z ↦ covN B₁ z (B₃ z))) :=
    (CovariantDerivative.contMDiffOn_leviCivitaConnection (n := ∞) (m := ∞) (k := ∞)
      hWopen le_rfl le_rfl (by simpa using hB₁W)).clm_bundle_apply hB₃W
  have hL₁₃d : MDiffAt (T% (fun y ↦ h.horizontalLift y (covN B₁ (f y) (B₃ (f y))))) x :=
    (h.contMDiffAt_horizontalLift (hB₁₃W.contMDiffAt (hWopen.mem_nhds hfxW))
      (by simp)).mdifferentiableAt (by simp)
  have hAd : MDiffAt (T% (fun y ↦ h.oneillA y (X₃ y) (X₁ y))) x :=
    (h.mdifferentiableAt_oneillA.clm_bundle_apply
      ((hX₃U.contMDiffAt (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp))).clm_bundle_apply
      ((hX₁U.contMDiffAt (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp))
  have hX₁₃d : MDiffAt (T% (fun y ↦ cov X₁ y (X₃ y))) x :=
    ((((CovariantDerivative.contMDiffOn_leviCivitaConnection (n := ∞) (m := ∞) (k := ∞)
      hUopen le_rfl le_rfl (by simpa using hX₁U)).clm_bundle_apply hX₃U).contMDiffAt
      (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp))
  have heqU : (fun y ↦ cov X₁ y (X₃ y)) =ᶠ[𝓝 x]
      (fun y ↦ h.horizontalLift y (covN B₁ (f y) (B₃ (f y)))) +
        fun y ↦ h.oneillA y (X₃ y) (X₁ y) := by
    filter_upwards [hUopen.mem_nhds hfxW] with y hy
    have hstep := h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
      ((hB₁W.contMDiffAt (hWopen.mem_nhds hy)).of_le (by simp))
      (h.horizontalLift_mem_orthogonal_ker y (B₃ (f y)))
    rw [h.mfderiv_horizontalLift] at hstep
    exact hstep
  have hcongr := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hX₁₃d (mdifferentiableAt_add_section hL₁₃d hAd) univ_mem heqU
  have hLpart := h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
    (B := fun z ↦ covN B₁ z (B₃ z))
    ((hB₁₃W.contMDiffAt (hWopen.mem_nhds hfxW)).of_le (by simp)) hv
  have hApart := h.oneillT_apply_of_eventually_mem_ker hAd
    (.of_forall fun y ↦ h.oneillA_apply_mem_ker (X₃ y) (h.horizontalLift_mem_orthogonal_ker y _)) v
  rw [Submodule.starProjection_eq_self_iff.mpr hv] at hApart
  rw [hcongr, cov.isCovariantDerivativeOnUniv.add hL₁₃d hAd, add_apply,
    ← inner_starProjection_orthogonal_ker_left _ hu₂, map_add, hLpart, ← hApart,
    inner_add_left, h.inner_oneillA, h.inner_oneillT]
  ring

/-- **O'Neill's third curvature equation.** For horizontal `u, v, w` and vertical `z`,
`⟪R(u, v)w, z⟫ = -⟪(∇_w A)_u v, z⟫ - ⟪A_u v, T_z w⟫ + ⟪A_v w, T_z u⟫ + ⟪A_w u, T_z v⟫`. -/
theorem inner_curvatureTensor_of_mem_orthogonal_ker_of_mem_ker
    {u v w z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) (hz : z ∈ (mfderiv I J f x).ker) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.curvatureTensor x u v w, z⟫_ℝ =
      -⟪cov.hom (cov.hom cov) h.oneillA x w u v, z⟫_ℝ -
        ⟪h.oneillA x u v, h.oneillT x z w⟫_ℝ +
        ⟪h.oneillA x v w, h.oneillT x z u⟫_ℝ +
        ⟪h.oneillA x w u, h.oneillT x z v⟫_ℝ := by
  intro cov
  have hswap := (CovariantDerivative.isMetricCompatible_leviCivitaConnection
    (I := I) (M := M)).inner_curvatureTensor_swap_pairs
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) x u v w z
  obtain ⟨W₁, B₁, hW₁, hfxW₁, hB₁, hX₁U₁, hX₁x⟩ := h.exists_contMDiffOn_horizontalLift_eq hu
  obtain ⟨W₃, B₃, hW₃, hfxW₃, hB₃, hX₃U₃, hX₃x⟩ := h.exists_contMDiffOn_horizontalLift_eq hw
  obtain ⟨V, hV, rfl, hVv⟩ := h.exists_contMDiff_mem_ker hz
  set W : Set N := W₁ ∩ W₃
  have hWopen : IsOpen W := hW₁.inter hW₃
  have hfxW : f x ∈ W := ⟨hfxW₁, hfxW₃⟩
  have hUopen : IsOpen (f ⁻¹' W) := hWopen.preimage h.isSubmersion.contMDiff.continuous
  set X₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
  set X₃ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₃ (f y))
  have hX₃x' : X₃ x = w := hX₃x
  have hcurv : cov.curvatureTensor x w (V x) u = cov.curvatureOperator X₃ V X₁ x := by
    rw [← hX₃x, ← hX₁x]
    exact cov.curvatureTensor_apply_of_contMDiffOn x hUopen hfxW
      (hX₃U₃.mono (preimage_mono inter_subset_right)) hV.contMDiffOn
      (hX₁U₁.mono (preimage_mono inter_subset_left))
  have ht₁ := h.inner_second_cov_basic_horizontal_along_vertical_along_horizontal hWopen hfxW
    (hB₁.mono inter_subset_left) hV hVv hw hv
  have ht₂ := h.inner_second_cov_basic_horizontal_along_horizontal_along_vertical hWopen hfxW
    (hB₁.mono inter_subset_left) (hB₃.mono inter_subset_right) hz hv
  have hdfw : B₃ (f x) = mfderiv I J f x w := by
    rw [← hX₃x, h.mfderiv_horizontalLift]
  have hbr := h.mlieBracket_horizontalLift_of_eventually_mem_ker
    ((hB₃.contMDiffAt (hW₃.mem_nhds hfxW₃)).of_le (by simp))
    ((hV x).mdifferentiableAt (by simp)) (.of_forall hVv)
  have hbr_mem : mlieBracket I X₃ V x ∈ (mfderiv I J f x).ker := by
    rw [hbr]
    exact sub_mem (Submodule.starProjection_apply_mem _ _)
      (h.oneillT_apply_mem_ker (V x) (h.horizontalLift_mem_orthogonal_ker x _))
  have ht₃ : ⟪cov X₁ x (mlieBracket I X₃ V x), v⟫_ℝ =
      ⟪h.oneillA x u ((mfderiv I J f x).ker.starProjection (cov V x w)), v⟫_ℝ +
        ⟪h.oneillA x u v, h.oneillT x (V x) w⟫_ℝ := by
    have hAX₁ := h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
      ((hB₁.contMDiffAt (hW₁.mem_nhds hfxW₁)).of_le (by simp)) hbr_mem
    have hAT : ⟪h.oneillA x u (h.oneillT x (V x) w), v⟫_ℝ =
        -⟪h.oneillA x u v, h.oneillT x (V x) w⟫_ℝ := by
      rw [h.inner_oneillA, real_inner_comm]
    rw [← inner_starProjection_orthogonal_ker_left _ hv, hAX₁, hbr, hX₁x, hX₃x, map_sub,
      inner_sub_left, hAT, sub_neg_eq_add]
  dsimp only at ht₁ ht₂
  rw [hX₁x] at ht₁
  rw [hX₁x, hX₃x, hdfw] at ht₂
  rw [hswap, hcurv, CovariantDerivative.curvatureOperator_apply, hX₃x',
    inner_sub_left, inner_sub_left, ht₁, ht₂, ht₃]
  linarith

end HorizontalThree

/-! ### Four horizontal vectors and horizontal sectional curvature -/

section HorizontalFour

variable {x : M}
include h

private theorem starProjection_orthogonal_ker_second_basic_horizontal
    (B₁ : Π z : N, TangentSpace J z) {B₂ Bw : Π z : N, TangentSpace J z}
    (hB₂ : CMDiff ∞ (T% B₂)) (hBw : CMDiff ∞ (T% Bw)) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covN := CovariantDerivative.leviCivitaConnection J N
    let U₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
    let U₂ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₂ (f y))
    let Z : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Bw (f y))
    (mfderiv I J f x).kerᗮ.starProjection (cov (fun y ↦ cov Z y (U₂ y)) x (U₁ x)) =
      h.horizontalLift x (covN (fun z ↦ covN Bw z (B₂ z)) (f x) (B₁ (f x))) +
        h.oneillA x (U₁ x) (h.oneillA x (U₂ x) (Z x)) := by
  intro cov covN U₁ U₂ Z
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  have hU₂ : CMDiff ∞ (T% U₂) := fun y ↦ h.contMDiffAt_horizontalLift (hB₂ (f y)) (by simp)
  have hZ : CMDiff ∞ (T% Z) := fun y ↦ h.contMDiffAt_horizontalLift (hBw (f y)) (by simp)
  have hBw₂ : CMDiff ∞ (T% (fun z ↦ covN Bw z (B₂ z))) := covN.contMDiff_apply hB₂ hBw
  have hL : CMDiff ∞ (T% (fun y ↦ h.horizontalLift y (covN Bw (f y) (B₂ (f y))))) :=
    fun y ↦ h.contMDiffAt_horizontalLift (hBw₂ (f y)) (by simp)
  have hA : MDiffAt (T% (fun y ↦ h.oneillA y (U₂ y) (Z y))) x :=
    (h.mdifferentiableAt_oneillA.clm_bundle_apply
      ((hU₂ x).mdifferentiableAt (by simp))).clm_bundle_apply ((hZ x).mdifferentiableAt (by simp))
  have hsplit : (fun y ↦ cov Z y (U₂ y)) =
      (fun y ↦ h.horizontalLift y (covN Bw (f y) (B₂ (f y)))) +
        fun y ↦ h.oneillA y (U₂ y) (Z y) := by
    funext y
    have hstep := h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
      ((hBw (f y)).of_le (by simp)) (h.horizontalLift_mem_orthogonal_ker y (B₂ (f y)))
    rw [h.mfderiv_horizontalLift] at hstep
    exact hstep
  have hAterm := h.oneillA_apply_of_eventually_mem_ker hA
    (.of_forall fun y ↦ h.oneillA_apply_mem_ker (U₂ y) (h.horizontalLift_mem_orthogonal_ker y _))
    (U₁ x)
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)]
    at hAterm
  rw [hsplit, cov.isCovariantDerivativeOnUniv.add ((hL x).mdifferentiableAt (by simp)) hA,
    add_apply, map_add,
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
      (B := fun z ↦ covN Bw z (B₂ z)) ((hBw₂ (f x)).of_le (by simp))
      (h.horizontalLift_mem_orthogonal_ker x _),
    h.mfderiv_horizontalLift, ← hAterm]

variable [T2Space N]

/-- **O'Neill's horizontal curvature equation (vector form).** For horizontal `u, v, w`,
`h (R(u, v)w)` equals
`horizontalLift (R^N(df u, df v)(df w)) - 2 A_w (A_u v) + A_u (A_v w) - A_v (A_u w)`. -/
theorem starProjection_orthogonal_ker_curvatureTensor_of_mem_orthogonal_ker
    {u v w : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covN := CovariantDerivative.leviCivitaConnection J N
    (mfderiv I J f x).kerᗮ.starProjection (cov.curvatureTensor x u v w) =
      h.horizontalLift x
          (covN.curvatureTensor (f x) (mfderiv I J f x u) (mfderiv I J f x v)
            (mfderiv I J f x w)) -
        (2 : ℝ) • h.oneillA x w (h.oneillA x u v) +
        h.oneillA x u (h.oneillA x v w) -
        h.oneillA x v (h.oneillA x u w) := by
  intro cov covN
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  obtain ⟨Bu, hBu, hBux⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ (mfderiv I J f x u)
  obtain ⟨Bv, hBv, hBvx⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ (mfderiv I J f x v)
  obtain ⟨Bw, hBw, hBwx⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ (mfderiv I J f x w)
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Bu (f y))
  set Y : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Bv (f y))
  set Z : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Bw (f y))
  have hX : CMDiff ∞ (T% X) := fun y ↦ h.contMDiffAt_horizontalLift (hBu (f y)) (by simp)
  have hY : CMDiff ∞ (T% Y) := fun y ↦ h.contMDiffAt_horizontalLift (hBv (f y)) (by simp)
  have hZ : CMDiff ∞ (T% Z) := fun y ↦ h.contMDiffAt_horizontalLift (hBw (f y)) (by simp)
  have hXx : X x = u := by simp [X, hBux, h.horizontalLift_mfderiv_of_mem x hu]
  have hYx : Y x = v := by simp [Y, hBvx, h.horizontalLift_mfderiv_of_mem x hv]
  have hZx : Z x = w := by simp [Z, hBwx, h.horizontalLift_mfderiv_of_mem x hw]
  have hXx' : h.horizontalLift x (Bu (f x)) = u := hXx
  have hYx' : h.horizontalLift x (Bv (f x)) = v := hYx
  have hZx' : h.horizontalLift x (Bw (f x)) = w := hZx
  have hbr_decomp : mlieBracket I X Y x =
      h.horizontalLift x (mlieBracket J Bu Bv (f x)) +
        (2 : ℝ) • h.oneillA x (X x) (Y x) := by
    conv_lhs => rw [← starProjection_orthogonal_ker_add_starProjection_ker I J f
      (mlieBracket I X Y x)]
    rw [← h.horizontalLift_mfderiv,
      h.mfderiv_mlieBracket_horizontalLift ((hBu (f x)).of_le (by simp))
        ((hBv (f x)).of_le (by simp)),
      h.starProjection_ker_mlieBracket ((hX x).mdifferentiableAt (by simp))
        ((hY x).mdifferentiableAt (by simp))
        (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
        (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)]
  have hbr_term : (mfderiv I J f x).kerᗮ.starProjection (cov Z x (mlieBracket I X Y x)) =
      h.horizontalLift x (covN Bw (f x) (mlieBracket J Bu Bv (f x))) +
        (2 : ℝ) • h.oneillA x (Z x) (h.oneillA x (X x) (Y x)) := by
    rw [hbr_decomp, map_add, map_smul, map_add, map_smul,
      h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
        ((hBw (f x)).of_le (by simp)) (h.horizontalLift_mem_orthogonal_ker x _),
      h.mfderiv_horizontalLift,
      h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
        ((hBw (f x)).of_le (by simp))
        (h.oneillA_apply_mem_ker (X x) (h.horizontalLift_mem_orthogonal_ker x _))]
  have hcovN_curv :
      covN.curvatureTensor (f x) (mfderiv I J f x u) (mfderiv I J f x v)
        (mfderiv I J f x w) =
        covN (fun z ↦ covN Bw z (Bv z)) (f x) (Bu (f x)) -
          covN (fun z ↦ covN Bw z (Bu z)) (f x) (Bv (f x)) -
          covN Bw (f x) (mlieBracket J Bu Bv (f x)) := by
    rw [← hBux, ← hBvx, ← hBwx, covN.curvatureTensor_apply (f x) hBu hBv hBw,
      CovariantDerivative.curvatureOperator_apply]
  have h₁ := h.starProjection_orthogonal_ker_second_basic_horizontal Bu hBv hBw (x := x)
  have h₂ := h.starProjection_orthogonal_ker_second_basic_horizontal Bv hBu hBw (x := x)
  dsimp only at h₁ h₂
  conv_lhs => rw [← hXx, ← hYx, ← hZx, cov.curvatureTensor_apply x hX hY hZ,
    CovariantDerivative.curvatureOperator_apply, map_sub, map_sub]
  rw [h₁, h₂, hbr_term, hXx, hYx, hZx, hXx', hYx', hZx', hcovN_curv, map_sub, map_sub]
  abel

/-- **O'Neill's fourth curvature equation (metric form).** For horizontal `u, v, w, z`,
`⟪R(u, v)w, z⟫` equals
`⟪R^N(df u, df v)(df w), df z⟫ + 2⟪A_u v, A_w z⟫ - ⟪A_v w, A_u z⟫ + ⟪A_u w, A_v z⟫`. -/
theorem inner_curvatureTensor_of_mem_orthogonal_ker
    {u v w z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covN := CovariantDerivative.leviCivitaConnection J N
    ⟪cov.curvatureTensor x u v w, z⟫_ℝ =
      ⟪covN.curvatureTensor (f x) (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w),
          mfderiv I J f x z⟫_ℝ +
        2 * ⟪h.oneillA x u v, h.oneillA x w z⟫_ℝ -
        ⟪h.oneillA x v w, h.oneillA x u z⟫_ℝ +
        ⟪h.oneillA x u w, h.oneillA x v z⟫_ℝ := by
  intro cov covN
  have hliftz : ⟪h.horizontalLift x
      (covN.curvatureTensor (f x) (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w)),
      z⟫_ℝ =
      ⟪covN.curvatureTensor (f x) (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w),
        mfderiv I J f x z⟫_ℝ := by
    conv_lhs => rw [← h.horizontalLift_mfderiv_of_mem x hz]
    exact (h.horizontalLift x).inner_map_map _ _
  rw [← inner_starProjection_orthogonal_ker_left _ hz,
    h.starProjection_orthogonal_ker_curvatureTensor_of_mem_orthogonal_ker hu hv hw,
    inner_sub_left, inner_add_left, inner_sub_left, real_inner_smul_left, hliftz,
    h.inner_oneillA x w (h.oneillA x u v) z,
    h.inner_oneillA x u (h.oneillA x v w) z,
    h.inner_oneillA x v (h.oneillA x u w) z]
  ring

/-- O'Neill's horizontal curvature equation phrased directly on horizontal lifts of four base
tangent vectors. -/
theorem inner_curvatureTensor_horizontalLift (a b c d : TangentSpace J (f x)) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covN := CovariantDerivative.leviCivitaConnection J N
    ⟪cov.curvatureTensor x (h.horizontalLift x a) (h.horizontalLift x b) (h.horizontalLift x c),
        h.horizontalLift x d⟫_ℝ =
      ⟪covN.curvatureTensor (f x) a b c, d⟫_ℝ +
        2 * ⟪h.oneillA x (h.horizontalLift x a) (h.horizontalLift x b),
          h.oneillA x (h.horizontalLift x c) (h.horizontalLift x d)⟫_ℝ -
        ⟪h.oneillA x (h.horizontalLift x b) (h.horizontalLift x c),
          h.oneillA x (h.horizontalLift x a) (h.horizontalLift x d)⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x a) (h.horizontalLift x c),
          h.oneillA x (h.horizontalLift x b) (h.horizontalLift x d)⟫_ℝ := by
  simpa only [h.mfderiv_horizontalLift] using
    h.inner_curvatureTensor_of_mem_orthogonal_ker
      (h.horizontalLift_mem_orthogonal_ker x a) (h.horizontalLift_mem_orthogonal_ker x b)
      (h.horizontalLift_mem_orthogonal_ker x c) (h.horizontalLift_mem_orthogonal_ker x d)

/-- Specialization of O'Neill's fourth curvature equation to the sectional-curvature numerator:
`⟪R^N(df u, df v)(df v), df u⟫ = ⟪R(u, v)v, u⟫ + 3 ‖A_u v‖²`. -/
theorem inner_curvatureTensor_self_of_mem_orthogonal_ker {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covN := CovariantDerivative.leviCivitaConnection J N
    ⟪covN.curvatureTensor (f x) (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x v),
        mfderiv I J f x u⟫_ℝ =
      ⟪cov.curvatureTensor x u v v, u⟫_ℝ + 3 * ‖h.oneillA x u v‖ ^ 2 := by
  intro cov covN
  have hcurv := h.inner_curvatureTensor_of_mem_orthogonal_ker hu hv hv hu
  rw [h.oneillA_self hv, inner_zero_left, h.oneillA_antisymm hv hu, inner_neg_right,
    real_inner_self_eq_norm_sq] at hcurv
  linarith

/-- **O'Neill's horizontal sectional curvature formula.** For any horizontal tangent vectors
`u, v`,
`K_N(df u, df v) = K_M(u, v) + 3 ‖A_u v‖² / det(Gram(u, v))`.
No linear-independence hypothesis is needed: on linearly dependent pairs the Gram determinant
vanishes and both sides are zero. -/
theorem sectionalCurvature_mfderiv_of_mem_orthogonal_ker {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (CovariantDerivative.leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 / (Matrix.gram ℝ ![u, v]).det := by
  rw [CovariantDerivative.sectionalCurvature_apply, CovariantDerivative.sectionalCurvature_apply,
    h.inner_curvatureTensor_self_of_mem_orthogonal_ker hu hv,
    h.det_gram_mfderiv_of_mem_orthogonal_ker hu hv, add_div]

/-- **O'Neill's horizontal sectional curvature formula on horizontal lifts.** -/
theorem sectionalCurvature_horizontalLift (a b : TangentSpace J (f x)) :
    (CovariantDerivative.leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x) a b =
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x
          (h.horizontalLift x a) (h.horizontalLift x b) +
        3 * ‖h.oneillA x (h.horizontalLift x a) (h.horizontalLift x b)‖ ^ 2 /
          (Matrix.gram ℝ ![a, b]).det := by
  simpa only [h.mfderiv_horizontalLift, h.det_gram_horizontalLift] using
    h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker
      (h.horizontalLift_mem_orthogonal_ker x a) (h.horizontalLift_mem_orthogonal_ker x b)

/-- **O'Neill's horizontal sectional curvature formula on an orthonormal horizontal pair:**
`K_N(df u, df v) = K_M(u, v) + 3 ‖A_u v‖²`. -/
theorem sectionalCurvature_mfderiv_of_orthonormal {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (huv : Orthonormal ℝ ![u, v]) :
    (CovariantDerivative.leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hu hv,
    Matrix.gram_eq_one_iff_orthonormal.mpr huv, Matrix.det_one, div_one]

/-- **O'Neill's horizontal sectional curvature formula in Lie-bracket form.** For vector fields
`X, Y` differentiable at `x` and horizontal near `x`,
`K_N(df (X x), df (Y x)) = K_M(X x, Y x) + (3 / 4) ‖v [X, Y]‖² / det(Gram(X x, Y x))`. -/
theorem sectionalCurvature_mfderiv_eq_add_three_quarters_norm_mlieBracket_sq_div
    {X Y : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) :
    (CovariantDerivative.leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x (X x) (Y x) +
        3 / 4 * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 /
          (Matrix.gram ℝ ![X x, Y x]).det := by
  rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hXh.self_of_nhds hYh.self_of_nhds,
    h.starProjection_ker_mlieBracket hX hY hXh hYh, norm_smul, Real.norm_ofNat]
  ring

/-- **O'Neill's horizontal sectional curvature formula on orthonormal horizontal fields:**
`K_N(df (X x), df (Y x)) = K_M(X x, Y x) + (3 / 4) ‖v [X, Y]‖²`. -/
theorem sectionalCurvature_mfderiv_eq_add_three_quarters_norm_mlieBracket_sq
    {X Y : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    (hXY : Orthonormal ℝ ![X x, Y x]) :
    (CovariantDerivative.leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x (X x) (Y x) +
        3 / 4 * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv_eq_add_three_quarters_norm_mlieBracket_sq_div hX hY hXh hYh,
    Matrix.gram_eq_one_iff_orthonormal.mpr hXY, Matrix.det_one, div_one]

/-- **A Riemannian submersion is sectional-curvature nondecreasing on horizontal planes.** -/
theorem sectionalCurvature_le_sectionalCurvature_mfderiv {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v ≤
      (CovariantDerivative.leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) := by
  rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hu hv]
  exact le_add_of_nonneg_right
    (div_nonneg (by positivity) (Matrix.posSemidef_gram ℝ ![u, v]).det_nonneg)

/-- On linearly independent horizontal vectors `u, v`, the base sectional curvature equals the
ambient sectional curvature if and only if O'Neill's integrability tensor `A_u v` vanishes. -/
theorem sectionalCurvature_mfderiv_eq_iff {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (huv : LinearIndependent ℝ ![u, v]) :
    (CovariantDerivative.leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v ↔
      h.oneillA x u v = 0 := by
  have hdet : 0 < (Matrix.gram ℝ ![u, v]).det :=
    (Matrix.posDef_gram_of_linearIndependent huv).det_pos
  rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hu hv, add_eq_left,
    div_eq_zero_iff, or_iff_left hdet.ne', mul_eq_zero, or_iff_right (by norm_num),
    sq_eq_zero_iff, norm_eq_zero]

/-- A lower sectional-curvature bound on horizontal two-planes at `x` passes to all two-planes of
the base at `f x`. -/
theorem le_sectionalCurvature_of_forall_mem_orthogonal_ker {κ : ℝ}
    (hκ : ∀ u v : TangentSpace I x,
      u ∈ (mfderiv I J f x).kerᗮ → v ∈ (mfderiv I J f x).kerᗮ →
      LinearIndependent ℝ ![u, v] →
      κ ≤ (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v)
    {a b : TangentSpace J (f x)} (hab : LinearIndependent ℝ ![a, b]) :
    κ ≤ (CovariantDerivative.leviCivitaConnection J N).sectionalCurvature
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x) a b := by
  have hlift_ind : LinearIndependent ℝ ![h.horizontalLift x a, h.horizontalLift x b] := by
    rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, h.det_gram_horizontalLift]
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hab
  refine (hκ _ _ (h.horizontalLift_mem_orthogonal_ker x a)
    (h.horizontalLift_mem_orthogonal_ker x b) hlift_ind).trans ?_
  simpa only [h.mfderiv_horizontalLift] using
    h.sectionalCurvature_le_sectionalCurvature_mfderiv
      (h.horizontalLift_mem_orthogonal_ker x a) (h.horizontalLift_mem_orthogonal_ker x b)

end HorizontalFour

end TauCeti.IsRiemannianSubmersion
