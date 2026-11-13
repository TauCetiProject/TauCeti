/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Basic
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection

/-!
# Symmetries of O'Neill's tensors and integrability of the horizontal distribution

For a Riemannian submersion `f : M → N`, write `h` and `v` for the horizontal and vertical
orthogonal projections. O'Neill's tensors `A` and `T` (`IsRiemannianSubmersion.oneillA` and
`IsRiemannianSubmersion.oneillT`) satisfy the following identities.

* On fields which are horizontal or vertical near the point, the tensors are single components of
  the Levi-Civita derivative: `A_X Y = v ∇_X Y` and `T_U X = v ∇_U X` for a horizontal field `X`
  or `Y`, and `A_X V = h ∇_X V` and `T_U V = h ∇_U V` for a vertical field `V`.
* `A_X` and `T_U` exchange the horizontal and vertical spaces.
* `A` is alternating on horizontal vectors: `A_X Y = -A_Y X`.
* The vertical part of the bracket of two horizontal fields is `v [X, Y] = 2 A_X Y`. So `A`
  measures the failure of the horizontal distribution to be closed under brackets; by
  skew-adjointness, `A` vanishes at `x` precisely when it vanishes on horizontal pairs there.
* `T` is symmetric on vertical vectors: `T_U V = T_V U`. This expresses the integrability of the
  vertical distribution, whose leaves are the fibres; on vertical vectors, `T` is the second
  fundamental form of the fibres.
* On basic horizontal fields (horizontal lifts of fields on the base), the Lie bracket decomposes
  into the lifted base bracket plus `2 A_X Y`, the Levi-Civita derivative along a horizontal lift
  decomposes into the lifted base derivative plus `A_X Y`, and the horizontal part of the
  Levi-Civita derivative along a vertical vector `U` is `A_Y U`.

These are the algebraic and connection inputs to O'Neill's curvature equations. For instance, they
are used to compare the sectional curvature of a horizontal plane with that of its image in the
base.

The alternating property and the vertical-direction basic-lift formula are proved with basic
horizontal fields, whose bracket with a vertical field is vertical by naturality of the Lie
bracket (`ContMDiffAt.mlieBracket_mem_ker_mfderiv_of_eventually_related`) and whose squared norm
is constant along the fibres.

## Main results

* `TauCeti.IsRiemannianSubmersion.oneillA_apply_of_eventually_mem_orthogonal_ker`,
  `TauCeti.IsRiemannianSubmersion.oneillA_apply_of_eventually_mem_ker`,
  `TauCeti.IsRiemannianSubmersion.oneillT_apply_of_eventually_mem_orthogonal_ker`,
  `TauCeti.IsRiemannianSubmersion.oneillT_apply_of_eventually_mem_ker`: the tensors on horizontal
  and vertical fields.
* `TauCeti.IsRiemannianSubmersion.oneillA_apply_mem_ker`,
  `TauCeti.IsRiemannianSubmersion.oneillA_apply_mem_orthogonal_ker`,
  `TauCeti.IsRiemannianSubmersion.oneillT_apply_mem_ker`,
  `TauCeti.IsRiemannianSubmersion.oneillT_apply_mem_orthogonal_ker`: `A_X` and `T_U` exchange
  the horizontal and vertical spaces.
* `TauCeti.IsRiemannianSubmersion.oneillA_self`, `TauCeti.IsRiemannianSubmersion.oneillA_antisymm`:
  `A` is alternating on horizontal vectors.
* `TauCeti.IsRiemannianSubmersion.starProjection_ker_mlieBracket`: `v [X, Y] = 2 A_X Y` for
  horizontal fields `X` and `Y`.
* `TauCeti.IsRiemannianSubmersion.oneillA_eq_zero_iff`,
  `TauCeti.IsRiemannianSubmersion.oneillA_eq_zero_iff_horizontalLift`, and
  `TauCeti.IsRiemannianSubmersion.oneillT_eq_zero_iff`: `A` and `T` vanish at a point precisely
  when they vanish on horizontal (respectively vertical) pairs there.
* `TauCeti.IsRiemannianSubmersion.oneillT_comm`: `T` is symmetric on vertical vectors.
* `TauCeti.IsRiemannianSubmersion.mlieBracket_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift`, and
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift_of_mem_ker`: the Lie bracket
  and Levi-Civita derivative of basic horizontal lifts.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Lemmas 1, 2, and 3.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §C.
-/

public section

open Bundle Filter Manifold VectorField
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

-- These regularity indices are propositionally, but not definitionally, equal to two.
local instance : IsManifold I ((1 : ℕ∞ω) + 1) M := by
  rw [one_add_one_eq_two]
  exact .of_le (by norm_cast)

local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

local instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

include h

/-! ### Horizontal and vertical fields -/

section Fields

variable {x : M}

private theorem mdifferentiableAt_starProjection_orthogonal_ker_apply
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    MDiffAt (T% (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y))) x := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  exact ((h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp)).clm_bundle_apply hY

private theorem mdifferentiableAt_starProjection_ker_apply
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    MDiffAt (T% (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y))) x := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  exact ((h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp)).clm_bundle_apply hY

/-- Differentiating the horizontal part of a field which is horizontal near `x`. -/
private theorem leviCivitaConnection_starProjection_orthogonal_ker_of_eventually_mem
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x =
      CovariantDerivative.leviCivitaConnection I M Y x :=
  (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (h.mdifferentiableAt_starProjection_orthogonal_ker_apply hY) hY univ_mem
    (hYh.mono fun _ hy ↦ Submodule.starProjection_eq_self_iff.mpr hy)

/-- Differentiating the vertical part of a field which is horizontal near `x`. -/
private theorem leviCivitaConnection_starProjection_ker_of_eventually_mem_orthogonal
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x = 0 := by
  rw [(CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv
    |>.congr_of_eventuallyEq (h.mdifferentiableAt_starProjection_ker_apply hY)
      (mdifferentiableAt_zeroSection ..) univ_mem
    (hYh.mono fun _ hy ↦ (Submodule.starProjection_apply_eq_zero_iff _).mpr hy)]
  exact congrFun (CovariantDerivative.zero _) x

/-- Differentiating the vertical part of a field which is vertical near `x`. -/
private theorem leviCivitaConnection_starProjection_ker_of_eventually_mem
    {V : Π x : M, TangentSpace I x} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ (mfderiv I J f y).ker.starProjection (V y)) x =
      CovariantDerivative.leviCivitaConnection I M V x :=
  (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (h.mdifferentiableAt_starProjection_ker_apply hV) hV univ_mem
    (hVv.mono fun _ hy ↦ Submodule.starProjection_eq_self_iff.mpr hy)

/-- Differentiating the horizontal part of a field which is vertical near `x`. -/
private theorem leviCivitaConnection_starProjection_orthogonal_ker_of_eventually_mem_ker
    {V : Π x : M, TangentSpace I x} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (V y)) x = 0 := by
  rw [(CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv
    |>.congr_of_eventuallyEq (h.mdifferentiableAt_starProjection_orthogonal_ker_apply hV)
    (mdifferentiableAt_zeroSection ..) univ_mem
    (hVv.mono fun _ hy ↦ (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (by rwa [Submodule.orthogonal_orthogonal]))]
  exact congrFun (CovariantDerivative.zero _) x

/-- On a field `Y` which is horizontal near `x`, O'Neill's horizontal tensor is the vertical part
of the Levi-Civita derivative in the horizontal direction: `A_X Y = v ∇_(hX) Y`. -/
theorem oneillA_apply_of_eventually_mem_orthogonal_ker {Y : Π x : M, TangentSpace I x}
    (hY : MDiffAt (T% Y) x) (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    (v : TangentSpace I x) :
    h.oneillA x v (Y x) =
      (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M Y x
          ((mfderiv I J f x).kerᗮ.starProjection v)) := by
  rw [h.oneillA_apply hY, h.leviCivitaConnection_starProjection_orthogonal_ker_of_eventually_mem hY
    hYh, h.leviCivitaConnection_starProjection_ker_of_eventually_mem_orthogonal hY hYh]
  simp

/-- On a field `V` which is vertical near `x`, O'Neill's horizontal tensor is the horizontal part
of the Levi-Civita derivative in the horizontal direction: `A_X V = h ∇_(hX) V`. -/
theorem oneillA_apply_of_eventually_mem_ker {V : Π x : M, TangentSpace I x}
    (hV : MDiffAt (T% V) x) (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker)
    (v : TangentSpace I x) :
    h.oneillA x v (V x) =
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M V x
          ((mfderiv I J f x).kerᗮ.starProjection v)) := by
  rw [h.oneillA_apply hV, h.leviCivitaConnection_starProjection_ker_of_eventually_mem hV hVv,
    h.leviCivitaConnection_starProjection_orthogonal_ker_of_eventually_mem_ker hV hVv]
  simp

/-- On a field `Y` which is horizontal near `x`, O'Neill's vertical tensor is the vertical part of
the Levi-Civita derivative in the vertical direction: `T_U Y = v ∇_(vU) Y`. -/
theorem oneillT_apply_of_eventually_mem_orthogonal_ker {Y : Π x : M, TangentSpace I x}
    (hY : MDiffAt (T% Y) x) (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    (v : TangentSpace I x) :
    h.oneillT x v (Y x) =
      (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M Y x
          ((mfderiv I J f x).ker.starProjection v)) := by
  rw [h.oneillT_apply hY, h.leviCivitaConnection_starProjection_orthogonal_ker_of_eventually_mem hY
    hYh, h.leviCivitaConnection_starProjection_ker_of_eventually_mem_orthogonal hY hYh]
  simp

/-- On a field `V` which is vertical near `x`, O'Neill's vertical tensor is the horizontal part of
the Levi-Civita derivative in the vertical direction: `T_U V = h ∇_(vU) V`. On vertical vectors
this is the second fundamental form of the fibre. -/
theorem oneillT_apply_of_eventually_mem_ker {V : Π x : M, TangentSpace I x}
    (hV : MDiffAt (T% V) x) (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker)
    (v : TangentSpace I x) :
    h.oneillT x v (V x) =
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M V x
          ((mfderiv I J f x).ker.starProjection v)) := by
  rw [h.oneillT_apply hV, h.leviCivitaConnection_starProjection_ker_of_eventually_mem hV hVv,
    h.leviCivitaConnection_starProjection_orthogonal_ker_of_eventually_mem_ker hV hVv]
  simp

/-- A horizontal vector extends to a field which is horizontal everywhere and differentiable at
the base point: the horizontal part of `FiberBundle.extend`. -/
private theorem exists_horizontal_extension {w : TangentSpace I x}
    (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    ∃ Y : Π y : M, TangentSpace I y, MDiffAt (T% Y) x ∧ Y x = w ∧
      ∀ y, Y y ∈ (mfderiv I J f y).kerᗮ :=
  ⟨fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (FiberBundle.extend E w y),
    h.mdifferentiableAt_starProjection_orthogonal_ker_apply
      (FiberBundle.mdifferentiableAt_extend I E w),
    by simp [Submodule.starProjection_eq_self_iff.mpr hw],
    fun _ ↦ Submodule.starProjection_apply_mem _ _⟩

/-- A vertical vector extends to a field which is vertical everywhere and differentiable at the
base point: the vertical part of `FiberBundle.extend`. -/
private theorem exists_vertical_extension {w : TangentSpace I x}
    (hw : w ∈ (mfderiv I J f x).ker) :
    ∃ V : Π y : M, TangentSpace I y, MDiffAt (T% V) x ∧ V x = w ∧
      ∀ y, V y ∈ (mfderiv I J f y).ker :=
  ⟨fun y ↦ (mfderiv I J f y).ker.starProjection (FiberBundle.extend E w y),
    h.mdifferentiableAt_starProjection_ker_apply (FiberBundle.mdifferentiableAt_extend I E w),
    by simp [Submodule.starProjection_eq_self_iff.mpr hw],
    fun _ ↦ Submodule.starProjection_apply_mem _ _⟩

/-- `A_X` maps horizontal vectors to vertical vectors. -/
theorem oneillA_apply_mem_ker (u : TangentSpace I x) {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    h.oneillA x u v ∈ (mfderiv I J f x).ker := by
  obtain ⟨Y, hYd, rfl, hYh⟩ := h.exists_horizontal_extension hv
  rw [h.oneillA_apply_of_eventually_mem_orthogonal_ker hYd (.of_forall hYh)]
  exact Submodule.starProjection_apply_mem _ _

/-- `A_X` maps vertical vectors to horizontal vectors. -/
theorem oneillA_apply_mem_orthogonal_ker (u : TangentSpace I x) {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) :
    h.oneillA x u v ∈ (mfderiv I J f x).kerᗮ := by
  obtain ⟨V, hVd, rfl, hVv⟩ := h.exists_vertical_extension hv
  rw [h.oneillA_apply_of_eventually_mem_ker hVd (.of_forall hVv)]
  exact Submodule.starProjection_apply_mem _ _

/-- `T_U` maps horizontal vectors to vertical vectors. -/
theorem oneillT_apply_mem_ker (u : TangentSpace I x) {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    h.oneillT x u v ∈ (mfderiv I J f x).ker := by
  obtain ⟨Y, hYd, rfl, hYh⟩ := h.exists_horizontal_extension hv
  rw [h.oneillT_apply_of_eventually_mem_orthogonal_ker hYd (.of_forall hYh)]
  exact Submodule.starProjection_apply_mem _ _

/-- `T_U` maps vertical vectors to horizontal vectors. -/
theorem oneillT_apply_mem_orthogonal_ker (u : TangentSpace I x) {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) :
    h.oneillT x u v ∈ (mfderiv I J f x).kerᗮ := by
  obtain ⟨V, hVd, rfl, hVv⟩ := h.exists_vertical_extension hv
  rw [h.oneillT_apply_of_eventually_mem_ker hVd (.of_forall hVv)]
  exact Submodule.starProjection_apply_mem _ _

end Fields

/-! ### Symmetries -/

section Symmetry

variable {x : M}

/-- The Levi-Civita derivative of a basic horizontal field `X`, the horizontal lift of a field `B`
on the base, along itself has no vertical part. The two inputs are that `[X, V]` is vertical for
every vertical field `V`, and that `|X|²` is pulled back from the base, so it is constant along the
fibres. -/
private theorem inner_leviCivitaConnection_horizontalLift_self {B : Π y : N, TangentSpace J y}
    (hB : CMDiffAt ∞ (T% B) (f x)) {w : TangentSpace I x} (hw : w ∈ (mfderiv I J f x).ker) :
    ⟪CovariantDerivative.leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x
        (h.horizontalLift x (B (f x))), w⟫_ℝ = 0 := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set cov := CovariantDerivative.leviCivitaConnection I M
  have hmetric := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B (f y))
  have hXd : MDiffAt (T% X) x :=
    (h.contMDiffAt_horizontalLift hB (by simp)).mdifferentiableAt (by simp)
  have hXh (y : M) : X y ∈ (mfderiv I J f y).kerᗮ := h.horizontalLift_mem_orthogonal_ker y _
  obtain ⟨V, hVd, rfl, hVv⟩ := h.exists_vertical_extension hw
  -- `⟨X, V⟩ = 0`, so `⟨∇_X X, V⟩ = -⟨X, ∇_X V⟩`.
  have h₁ := hmetric.mvfderiv_inner_eq X hXd hVd
  have hXV : (fun y ↦ ⟪X y, V y⟫_ℝ) = fun _ ↦ 0 := funext fun y ↦
    Submodule.inner_right_of_mem_orthogonal (hVv y) (hXh y) |> (real_inner_comm _ _).trans
  -- `|X|²` is pulled back from the base, so its derivative along `V` vanishes and
  -- `⟨X, ∇_V X⟩ = 0`.
  have h₂ := hmetric.mvfderiv_inner_eq V hXd hXd
  have hXX : (fun y ↦ ⟪X y, X y⟫_ℝ) = (fun z ↦ ⟪B z, B z⟫_ℝ) ∘ f := funext fun y ↦
    (h.horizontalLift y).inner_map_map _ _
  have hfV : mfderiv I J f x (V x) = 0 := hVv x
  have hd : mvfderiv I (fun y ↦ ⟪X y, X y⟫_ℝ) x (V x) = 0 := by
    rw [hXX, mvfderiv_comp_apply x
      (TauCeti.Manifold.mdifferentiableAt_inner (hB.mdifferentiableAt (by simp))
        (hB.mdifferentiableAt (by simp)))
      (h.isSubmersion.contMDiff.mdifferentiableAt (by simp)), hfV, map_zero]
  -- `∇_X V - ∇_V X = [X, V]` is vertical, since `X` is basic and `V` is vertical.
  have h₃ := ((CovariantDerivative.torsion_eq_zero_iff cov).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)) hXd hVd
  have hbr : ⟪X x, mlieBracket I X V x⟫_ℝ = 0 :=
    (real_inner_comm _ _).trans <| Submodule.inner_right_of_mem_orthogonal
      ((h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv_of_eventually_related
        (by simp [minSmoothness_of_isRCLikeNormedField]) hXd hVd (hB.mdifferentiableAt (by simp))
        (.of_forall fun y ↦ h.mfderiv_horizontalLift y _) (.of_forall hVv)) (hXh x)
  have hXx : X x = h.horizontalLift x (B (f x)) := rfl
  rw [hXV, mvfderiv_const, zero_apply] at h₁
  rw [hd] at h₂
  rw [← h₃, inner_sub_right] at hbr
  beta_reduce at h₁ h₂
  rw [real_inner_comm] at h₂
  rw [← hXx]
  linarith

/-- **O'Neill's tensor `A` vanishes on the diagonal of the horizontal space.** -/
@[simp]
theorem oneillA_self {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    h.oneillA x u u = 0 := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  -- Extend `u` to the basic horizontal field `X`, the lift of a field `B` on the base.
  set B : Π y : N, TangentSpace J y := FiberBundle.extend F (mfderiv I J f x u)
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B (f y))
  have hB : CMDiffAt ∞ (T% B) (f x) := FiberBundle.contMDiffAt_extend ..
  have hXd : MDiffAt (T% X) x :=
    (h.contMDiffAt_horizontalLift hB (by simp)).mdifferentiableAt (by simp)
  have hXx : X x = u := by
    simp [X, B, FiberBundle.extend_apply_self, h.horizontalLift_mfderiv_of_mem x hu]
  -- Then `A_u u = v ∇_X X`, which vanishes.
  conv_lhs => rw [← hXx]
  rw [h.oneillA_apply_of_eventually_mem_orthogonal_ker hXd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _),
    Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _),
    Submodule.starProjection_apply_eq_zero_iff]
  intro w hw
  rw [real_inner_comm]
  exact h.inner_leviCivitaConnection_horizontalLift_self hB hw

/-- **O'Neill's tensor `A` is alternating on horizontal vectors.** -/
theorem oneillA_antisymm {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    h.oneillA x u v = -h.oneillA x v u := by
  have huv := h.oneillA_self (add_mem hu hv)
  simp only [map_add, add_apply, h.oneillA_self hu, h.oneillA_self hv,
    zero_add, add_zero] at huv
  exact eq_neg_of_add_eq_zero_right huv

/-- **Integrability tensor.** For vector fields `X` and `Y` which are horizontal near `x`, the
vertical part of their bracket is `v [X, Y] = 2 A_X Y`. -/
theorem starProjection_ker_mlieBracket {X Y : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) :
    (mfderiv I J f x).ker.starProjection (mlieBracket I X Y x) =
      (2 : ℝ) • h.oneillA x (X x) (Y x) := by
  have hT := ((CovariantDerivative.torsion_eq_zero_iff _).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)) hX hY
  have hXY := h.oneillA_apply_of_eventually_mem_orthogonal_ker hY hYh (X x)
  have hYX := h.oneillA_apply_of_eventually_mem_orthogonal_ker hX hXh (Y x)
  rw [Submodule.starProjection_eq_self_iff.mpr hXh.self_of_nhds] at hXY
  rw [Submodule.starProjection_eq_self_iff.mpr hYh.self_of_nhds] at hYX
  rw [← hT, map_sub, ← hXY, ← hYX,
    h.oneillA_antisymm hYh.self_of_nhds hXh.self_of_nhds, sub_neg_eq_add, two_smul]

/-- **O'Neill's tensor `T` is symmetric on vertical vectors.** This expresses the integrability
of the vertical distribution. -/
theorem oneillT_comm {u w : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker)
    (hw : w ∈ (mfderiv I J f x).ker) :
    h.oneillT x u w = h.oneillT x w u := by
  obtain ⟨U, hUd, hUx, hUv⟩ := h.exists_vertical_extension hu
  obtain ⟨W, hWd, hWx, hWv⟩ := h.exists_vertical_extension hw
  have hUW := h.oneillT_apply_of_eventually_mem_ker hWd (.of_forall hWv) u
  have hWU := h.oneillT_apply_of_eventually_mem_ker hUd (.of_forall hUv) w
  rw [Submodule.starProjection_eq_self_iff.mpr hu, ← hUx] at hUW
  rw [Submodule.starProjection_eq_self_iff.mpr hw, ← hWx] at hWU
  have hT := ((CovariantDerivative.torsion_eq_zero_iff _).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)) hUd hWd
  -- The bracket of two vertical fields is vertical, so it has no horizontal part.
  have hbr : (mfderiv I J f x).kerᗮ.starProjection (mlieBracket I U W x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr <| by
      rw [Submodule.orthogonal_orthogonal]
      exact (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv
        (by simp [minSmoothness_of_isRCLikeNormedField]) hUd hWd (.of_forall hUv) (.of_forall hWv)
  rw [← hT, map_sub, sub_eq_zero, ← hUW, ← hWU, hUx, hWx] at hbr
  exact hbr

/-- O'Neill's horizontal tensor `A` vanishes at `x` if and only if it vanishes on every pair of
horizontal vectors at `x`. Skew-adjointness controls vertical second arguments from horizontal
ones, and the first argument factors through its horizontal projection. -/
theorem oneillA_eq_zero_iff :
    h.oneillA x = 0 ↔
      ∀ u v : TangentSpace I x, u ∈ (mfderiv I J f x).kerᗮ →
        v ∈ (mfderiv I J f x).kerᗮ → h.oneillA x u v = 0 := by
  refine ⟨fun h0 u v _ _ ↦ by simp [h0], fun h0 ↦ ?_⟩
  ext u v
  simp only [zero_apply]
  rw [← h.oneillA_starProjection_orthogonal_ker x u,
    ← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal v, map_add,
    h0 _ _ (Submodule.starProjection_apply_mem _ _) (Submodule.starProjection_apply_mem _ _),
    add_zero]
  set p := (mfderiv I J f x).kerᗮ.starProjection u
  set q := (mfderiv I J f x).ker.starProjection v
  have hpq : h.oneillA x p q ∈ (mfderiv I J f x).kerᗮ :=
    h.oneillA_apply_mem_orthogonal_ker p (Submodule.starProjection_apply_mem _ _)
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [h.inner_oneillA, h0 p (h.oneillA x p q) (Submodule.starProjection_apply_mem _ _) hpq,
    inner_zero_right, neg_zero]

/-- O'Neill's horizontal tensor `A` vanishes at `x` if and only if it vanishes on every pair of
horizontal lifts at `x`. -/
theorem oneillA_eq_zero_iff_horizontalLift :
    h.oneillA x = 0 ↔
      ∀ u v : TangentSpace J (f x),
        h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v) = 0 := by
  rw [h.oneillA_eq_zero_iff]
  refine ⟨fun h0 u v ↦ h0 _ _ (h.horizontalLift_mem_orthogonal_ker x u)
    (h.horizontalLift_mem_orthogonal_ker x v), fun h0 u v hu hv ↦ ?_⟩
  rw [← h.horizontalLift_mfderiv_of_mem x hu, ← h.horizontalLift_mfderiv_of_mem x hv]
  exact h0 _ _

/-- O'Neill's vertical tensor `T` vanishes at `x` if and only if it vanishes on every pair of
vertical vectors at `x`. Skew-adjointness controls horizontal second arguments from vertical ones,
and the first argument factors through its vertical projection. -/
theorem oneillT_eq_zero_iff :
    h.oneillT x = 0 ↔
      ∀ u v : TangentSpace I x, u ∈ (mfderiv I J f x).ker →
        v ∈ (mfderiv I J f x).ker → h.oneillT x u v = 0 := by
  refine ⟨fun h0 u v _ _ ↦ by simp [h0], fun h0 ↦ ?_⟩
  ext u v
  simp only [zero_apply]
  rw [← h.oneillT_starProjection_ker x u,
    ← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal v, map_add,
    h0 _ _ (Submodule.starProjection_apply_mem _ _) (Submodule.starProjection_apply_mem _ _),
    zero_add]
  set p := (mfderiv I J f x).ker.starProjection u
  set q := (mfderiv I J f x).kerᗮ.starProjection v
  have hpq : h.oneillT x p q ∈ (mfderiv I J f x).ker :=
    h.oneillT_apply_mem_ker p (Submodule.starProjection_apply_mem _ _)
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [h.inner_oneillT, h0 p (h.oneillT x p q) (Submodule.starProjection_apply_mem _ _) hpq,
    inner_zero_right, neg_zero]

/-- When the vertical kernel at `x` is trivial, O'Neill's horizontal tensor vanishes at `x`. -/
theorem oneillA_eq_zero_of_ker_eq_bot (hker : (mfderiv I J f x).ker = ⊥) :
    h.oneillA x = 0 := by
  rw [h.oneillA_eq_zero_iff]
  intro u v _ hv
  have hmem := h.oneillA_apply_mem_ker u hv
  rwa [hker, Submodule.mem_bot] at hmem

end Symmetry

/-! ### Basic horizontal lifts -/

section BasicLift

variable {x : M}

/-- The Lie bracket of two basic horizontal lifts decomposes into the horizontal lift of the base
bracket plus `2 A_X Y` vertically. -/
theorem mlieBracket_horizontalLift {X Y : Π y : N, TangentSpace J y}
    (hX : CMDiffAt 1 (T% X) (f x)) (hY : CMDiffAt 1 (T% Y) (f x)) :
    mlieBracket I (fun y ↦ h.horizontalLift y (X (f y)))
        (fun y ↦ h.horizontalLift y (Y (f y))) x =
      h.horizontalLift x (mlieBracket J X Y (f x)) +
        (2 : ℝ) • h.oneillA x (h.horizontalLift x (X (f x)))
          (h.horizontalLift x (Y (f x))) := by
  have hXd := (h.contMDiffAt_horizontalLift hX (by norm_num)).mdifferentiableAt one_ne_zero
  have hYd := (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal
      (mlieBracket I (fun y ↦ h.horizontalLift y (X (f y)))
        (fun y ↦ h.horizontalLift y (Y (f y))) x),
    add_comm, ← h.horizontalLift_mfderiv, h.mfderiv_mlieBracket_horizontalLift hX hY,
    h.starProjection_ker_mlieBracket hXd hYd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)]

/-- **O'Neill's connection equation on basic horizontal lifts.** Along a horizontally lifted
vector, the Levi-Civita derivative of a basic horizontal lift decomposes into the lifted base
Levi-Civita derivative plus O'Neill's `A` tensor vertically. -/
theorem leviCivitaConnection_horizontalLift {Y : Π y : N, TangentSpace J y}
    (hY : CMDiffAt 1 (T% Y) (f x)) (v : TangentSpace J (f x)) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ h.horizontalLift y (Y (f y))) x (h.horizontalLift x v) =
      h.horizontalLift x (CovariantDerivative.leviCivitaConnection J N Y (f x) v) +
        h.oneillA x (h.horizontalLift x v) (h.horizontalLift x (Y (f x))) := by
  have hYd := (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  have hA := h.oneillA_apply_of_eventually_mem_orthogonal_ker hYd
    (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _) (h.horizontalLift x v)
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x v)] at hA
  rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal
      (CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ h.horizontalLift y (Y (f y))) x (h.horizontalLift x v)),
    add_comm,
    h.starProjection_covariantDerivative_horizontalLift
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection J) hY v,
    ← hA]

/-- **O'Neill's Lemma 3.** The horizontal part of the Levi-Civita derivative of a basic horizontal
lift `Y` in a vertical direction `u` equals `A_Y u`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
    {Y : Π y : N, TangentSpace J y} (hY : CMDiffAt 1 (T% Y) (f x))
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker) :
    (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ h.horizontalLift y (Y (f y))) x u) =
      h.oneillA x (h.horizontalLift x (Y (f x))) u := by
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Y (f y))
  have hXd : MDiffAt (T% X) x :=
    (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  obtain ⟨V, hVd, rfl, hVv⟩ := h.exists_vertical_extension hu
  have hT := ((CovariantDerivative.torsion_eq_zero_iff _).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)) hXd hVd
  -- Since `X` is `f`-related to `Y` and `V` is vertical, `[X, V]` is vertical.
  have hbr : (mfderiv I J f x).kerᗮ.starProjection (mlieBracket I X V x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr <| by
      rw [Submodule.orthogonal_orthogonal]
      exact (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv_of_eventually_related
        (by simp [minSmoothness_of_isRCLikeNormedField]) hXd hVd
        (hY.mdifferentiableAt one_ne_zero)
        (.of_forall fun y ↦ h.mfderiv_horizontalLift y _) (.of_forall hVv)
  have hA := h.oneillA_apply_of_eventually_mem_ker hVd (.of_forall hVv) (X x)
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)] at hA
  rw [← hT, map_sub, sub_eq_zero] at hbr
  exact hbr.symm.trans hA.symm

/-- Along a vertical vector `u`, the Levi-Civita derivative of a basic horizontal lift `Y`
decomposes into `A_Y u` horizontally plus `T_u Y` vertically. -/
theorem leviCivitaConnection_horizontalLift_of_mem_ker
    {Y : Π y : N, TangentSpace J y} (hY : CMDiffAt 1 (T% Y) (f x))
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ h.horizontalLift y (Y (f y))) x u =
      h.oneillA x (h.horizontalLift x (Y (f x))) u +
        h.oneillT x u (h.horizontalLift x (Y (f x))) := by
  have hYd := (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  have hT := h.oneillT_apply_of_eventually_mem_orthogonal_ker hYd
    (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _) u
  rw [Submodule.starProjection_eq_self_iff.mpr hu] at hT
  rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal
      (CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ h.horizontalLift y (Y (f y))) x u),
    add_comm,
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker hY hu, ← hT]

/-- The horizontal part of the Levi-Civita derivative of a basic horizontal lift `Y` along an
arbitrary tangent vector `w` is the lifted base derivative along `df_x w` plus `A_Y (v w)`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift
    {Y : Π y : N, TangentSpace J y} (hY : CMDiffAt 1 (T% Y) (f x))
    (w : TangentSpace I x) :
    (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ h.horizontalLift y (Y (f y))) x w) =
      h.horizontalLift x
          (CovariantDerivative.leviCivitaConnection J N Y (f x) (mfderiv I J f x w)) +
        h.oneillA x (h.horizontalLift x (Y (f x)))
          ((mfderiv I J f x).ker.starProjection w) := by
  conv_lhs => rw [← h.starProjection_ker_add_horizontalLift_mfderiv x w]
  rw [map_add, map_add,
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker hY
      (Submodule.starProjection_apply_mem _ _),
    h.starProjection_covariantDerivative_horizontalLift
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection J) hY,
    add_comm]

/-- Along an arbitrary tangent vector `w`, the Levi-Civita derivative of a basic horizontal lift
`Y` decomposes into its lifted base derivative, horizontal-horizontal `A`, horizontal-vertical `A`,
and vertical-horizontal `T` components. -/
theorem leviCivitaConnection_horizontalLift_apply
    {Y : Π y : N, TangentSpace J y} (hY : CMDiffAt 1 (T% Y) (f x))
    (w : TangentSpace I x) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ h.horizontalLift y (Y (f y))) x w =
      h.horizontalLift x
          (CovariantDerivative.leviCivitaConnection J N Y (f x) (mfderiv I J f x w)) +
        h.oneillA x w (h.horizontalLift x (Y (f x))) +
        h.oneillA x (h.horizontalLift x (Y (f x)))
          ((mfderiv I J f x).ker.starProjection w) +
        h.oneillT x w (h.horizontalLift x (Y (f x))) := by
  conv_lhs => rw [← h.starProjection_ker_add_horizontalLift_mfderiv x w]
  rw [map_add, h.leviCivitaConnection_horizontalLift_of_mem_ker hY
      (Submodule.starProjection_apply_mem _ _),
    h.leviCivitaConnection_horizontalLift hY, h.horizontalLift_mfderiv,
    h.oneillA_starProjection_orthogonal_ker,
    ← h.oneillT_starProjection_ker x w]
  abel

end BasicLift

end TauCeti.IsRiemannianSubmersion
