/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Basic
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Levi-Civita decomposition and covariant derivatives of O'Neill's tensors

Let `f : M → N` be a Riemannian submersion with horizontal lift `horizontalLift` and fundamental
tensors `A` (`oneillA`) and `T` (`oneillT`). Writing `∇` for the Levi-Civita connection of `M`,
`∇^N` for that of `N`, and `∇A`, `∇T` for the covariant derivatives of `A` and `T` under the
induced Hom-bundle connection `∇.hom (∇.hom ∇)`, this file establishes O'Neill's connection
decomposition (Lemmas 1 and 2) together with the evaluation and symmetry formulas for `∇A` and
`∇T`.

First, for fields horizontal or vertical near `x`, `∇` decomposes into its tangential projection and
a single application of `A` or `T`. When `X = L B` is the basic horizontal lift of a `C¹` vector
field `B` on `N`, its bracket with any vertical field is vertical, so `h (∇_u X) = A_X u` for
vertical `u`, giving the full derivative formula
`∇_w X = L (∇^N_(df w) B) + A_w X + A_X (v w) + T_w X` for every tangent vector `w`.

Second, differentiating the pointwise skew-adjointness of `A` and `T` shows that `∇A` and `∇T`
remain skew-adjoint in their last two arguments, and differentiating `A_X X = 0` along local basic
horizontal lifts shows that `⟪(∇_a A) u v, w⟫` is alternating in horizontal `u, v` when `w` is
vertical. `[T2Space N]` is never assumed, and `[T2Space M]` enters only in the Hom-bundle
derivatives `∇A` and `∇T` via `contMDiff_oneillA` and `contMDiff_oneillT`.

## Main results

* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_of_eventually_mem_ker_of_mem_ker` and its
  three horizontal/vertical companions: O'Neill's Lemma 1 decomposing `∇` via `A` and `T`.
* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift_of_mem_ker`,
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift`, and
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift_apply`: O'Neill's Lemma 2
  and the full Levi-Civita derivative of a basic horizontal lift.
* `TauCeti.IsRiemannianSubmersion.exists_contMDiffOn_horizontalLift`: local extension of a
  horizontal vector to a smooth basic horizontal lift without `[T2Space N]`.
* `TauCeti.IsRiemannianSubmersion.hom_oneillA_apply`,
  `TauCeti.IsRiemannianSubmersion.hom_oneillT_apply`,
  `TauCeti.IsRiemannianSubmersion.inner_hom_oneillA`,
  `TauCeti.IsRiemannianSubmersion.inner_hom_oneillT`, and
  `TauCeti.IsRiemannianSubmersion.inner_hom_oneillA_antisymm`: Leibniz evaluation and symmetries
  of `∇A` and `∇T`.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Lemmas 1–3.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §D (9.24–9.27).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7.
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
  {f : M → N} (h : IsRiemannianSubmersion I J f) {x : M}

-- These regularity indices are propositionally, but not definitionally, equal to `2`.
private instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

private instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

include h

/-! ### Levi-Civita decomposition and basic horizontal lifts -/

/-- **O'Neill's Lemma 1 (horizontal field, horizontal direction).** On a field `Y` horizontal near
`x`, the Levi-Civita derivative along a horizontal vector splits into its horizontal projection and
`A_u (Y x)`. -/
theorem leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_orthogonal_ker
    {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    leviCivitaConnection I M Y x u =
      (mfderiv I J f x).kerᗮ.starProjection (leviCivitaConnection I M Y x u) +
        h.oneillA x u (Y x) := by
  rw [h.oneillA_apply_of_eventually_mem_orthogonal_ker hY hYh u,
    Submodule.starProjection_eq_self_iff.mpr hu, add_comm,
    Submodule.starProjection_add_starProjection_orthogonal]

/-- **O'Neill's Lemma 1 (horizontal field, vertical direction).** On a field `Y` horizontal near
`x`, the Levi-Civita derivative along a vertical vector splits into its horizontal projection and
`T_u (Y x)`. -/
theorem leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_ker
    {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker) :
    leviCivitaConnection I M Y x u =
      (mfderiv I J f x).kerᗮ.starProjection (leviCivitaConnection I M Y x u) +
        h.oneillT x u (Y x) := by
  rw [h.oneillT_apply_of_eventually_mem_orthogonal_ker hY hYh u,
    Submodule.starProjection_eq_self_iff.mpr hu, add_comm,
    Submodule.starProjection_add_starProjection_orthogonal]

/-- **O'Neill's Lemma 1 (vertical field, horizontal direction).** On a field `V` vertical near `x`,
the Levi-Civita derivative along a horizontal vector splits into `A_u (V x)` and its vertical
projection. -/
theorem leviCivitaConnection_of_eventually_mem_ker_of_mem_orthogonal_ker
    {V : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker)
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    leviCivitaConnection I M V x u =
      h.oneillA x u (V x) +
        (mfderiv I J f x).ker.starProjection (leviCivitaConnection I M V x u) := by
  rw [h.oneillA_apply_of_eventually_mem_ker hV hVv u,
    Submodule.starProjection_eq_self_iff.mpr hu, add_comm,
    Submodule.starProjection_add_starProjection_orthogonal]

/-- **O'Neill's Lemma 1 (vertical field, vertical direction).** On a field `V` vertical near `x`,
the Levi-Civita derivative along a vertical vector splits into `T_u (V x)` and its vertical
projection. -/
theorem leviCivitaConnection_of_eventually_mem_ker_of_mem_ker
    {V : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker)
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker) :
    leviCivitaConnection I M V x u =
      h.oneillT x u (V x) +
        (mfderiv I J f x).ker.starProjection (leviCivitaConnection I M V x u) := by
  rw [h.oneillT_apply_of_eventually_mem_ker hV hVv u,
    Submodule.starProjection_eq_self_iff.mpr hu, add_comm,
    Submodule.starProjection_add_starProjection_orthogonal]

/-- **O'Neill's Lemma 2.** For a basic horizontal lift `X : y ↦ h.horizontalLift y (B (f y))` of a
`C¹` base field `B` and a vertical tangent vector `u`, the horizontal part of its Levi-Civita
derivative along `u` is `A_(X x) u`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
    {B : Π z : N, TangentSpace J z} (hB : CMDiffAt 1 (T% B) (f x))
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker) :
    (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x u) =
      h.oneillA x (h.horizontalLift x (B (f x))) u := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := .of_le (n := ∞) (by simp)
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B (f y))
  have hXd : MDiffAt (T% X) x :=
    (h.contMDiffAt_horizontalLift hB (by norm_num)).mdifferentiableAt one_ne_zero
  set U : Π y : M, TangentSpace I y :=
    fun y ↦ (mfderiv I J f y).ker.starProjection (extend E u y)
  have hUd : MDiffAt (T% U) x :=
    ((h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
      (by simp)).clm_bundle_apply (mdifferentiableAt_extend I E u)
  have hUx : U x = u := by
    simp [U, extend_apply_self, Submodule.starProjection_eq_self_iff.mpr hu]
  have hUv (y : M) : U y ∈ (mfderiv I J f y).ker := Submodule.starProjection_apply_mem _ _
  -- `[X, U]` is vertical since `X` is `f`-related to `B` and `U` is vertical.
  have hbr : (mfderiv I J f x).kerᗮ.starProjection (mlieBracket I X U x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr <| by
      rw [Submodule.orthogonal_orthogonal]
      exact (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv_of_eventually_related
        (by simp [minSmoothness_of_isRCLikeNormedField]) hXd hUd
        (hB.mdifferentiableAt one_ne_zero)
        (.of_forall fun y ↦ h.mfderiv_horizontalLift y _) (.of_forall hUv)
  have hT := ((torsion_eq_zero_iff (leviCivitaConnection I M)).mp
    (torsion_leviCivitaConnection_eq_zero I)) hXd hUd
  rw [← hT, map_sub, sub_eq_zero] at hbr
  rw [← hUx, ← hbr, h.oneillA_apply_of_eventually_mem_ker hUd (.of_forall hUv),
    Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)]

/-- The Levi-Civita derivative of a basic horizontal lift `X : y ↦ h.horizontalLift y (B (f y))`
along a vertical tangent vector `u` is `A_(X x) u + T_u (X x)`. -/
theorem leviCivitaConnection_horizontalLift_of_mem_ker
    {B : Π z : N, TangentSpace J z} (hB : CMDiffAt 1 (T% B) (f x))
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker) :
    leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x u =
      h.oneillA x (h.horizontalLift x (B (f x))) u +
        h.oneillT x u (h.horizontalLift x (B (f x))) := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := .of_le (n := ∞) (by simp)
  have hXd : MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x :=
    (h.contMDiffAt_horizontalLift hB (by norm_num)).mdifferentiableAt one_ne_zero
  rw [h.leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_ker hXd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _) hu,
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker hB hu]

/-- The Levi-Civita derivative of a basic horizontal lift `X : y ↦ h.horizontalLift y (B (f y))`
along `h.horizontalLift x v` is the horizontal lift of `∇^N_v B` plus
`A_(h.horizontalLift x v) (X x)`. -/
theorem leviCivitaConnection_horizontalLift
    {B : Π z : N, TangentSpace J z} (hB : CMDiffAt 1 (T% B) (f x))
    (v : TangentSpace J (f x)) :
    leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x (h.horizontalLift x v) =
      h.horizontalLift x (leviCivitaConnection J N B (f x) v) +
        h.oneillA x (h.horizontalLift x v) (h.horizontalLift x (B (f x))) := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := .of_le (n := ∞) (by simp)
  have hXd : MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x :=
    (h.contMDiffAt_horizontalLift hB (by norm_num)).mdifferentiableAt one_ne_zero
  rw [h.leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_orthogonal_ker hXd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
      (h.horizontalLift_mem_orthogonal_ker x v),
    h.starProjection_covariantDerivative_horizontalLift
      (isLeviCivitaConnection_leviCivitaConnection I)
      (isLeviCivitaConnection_leviCivitaConnection J) hB v]

/-- The Levi-Civita derivative of a basic horizontal lift `X : y ↦ h.horizontalLift y (B (f y))`
along a horizontal vector `u` is the horizontal lift of `∇^N_(df u) B` plus `A_u (X x)`. -/
theorem leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
    {B : Π z : N, TangentSpace J z} (hB : CMDiffAt 1 (T% B) (f x))
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x u =
      h.horizontalLift x (leviCivitaConnection J N B (f x) (mfderiv I J f x u)) +
        h.oneillA x u (h.horizontalLift x (B (f x))) := by
  conv_lhs => rw [← h.horizontalLift_mfderiv_of_mem x hu]
  rw [h.leviCivitaConnection_horizontalLift hB, h.horizontalLift_mfderiv_of_mem x hu]

/-- Full Levi-Civita derivative of a basic horizontal lift in an arbitrary tangent direction `w`. -/
theorem leviCivitaConnection_horizontalLift_apply
    {B : Π z : N, TangentSpace J z} (hB : CMDiffAt 1 (T% B) (f x))
    (w : TangentSpace I x) :
    leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x w =
      h.horizontalLift x (leviCivitaConnection J N B (f x) (mfderiv I J f x w)) +
        h.oneillA x w (h.horizontalLift x (B (f x))) +
        h.oneillA x (h.horizontalLift x (B (f x))) ((mfderiv I J f x).ker.starProjection w) +
        h.oneillT x w (h.horizontalLift x (B (f x))) := by
  conv_lhs => rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal w]
  rw [map_add,
    h.leviCivitaConnection_horizontalLift_of_mem_ker hB
      (Submodule.starProjection_apply_mem _ _),
    h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker hB
      (Submodule.starProjection_apply_mem _ _),
    ← h.horizontalLift_mfderiv, h.mfderiv_horizontalLift, h.horizontalLift_mfderiv,
    h.oneillA_starProjection_orthogonal_ker, h.oneillT_starProjection_ker]
  abel

/-- Extend a horizontal vector at `x` locally to a basic horizontal lift that is smooth on an open
neighbourhood of `x`, without assuming `[T2Space N]`. -/
theorem exists_contMDiffOn_horizontalLift {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    ∃ (W : Set N) (B : Π z : N, TangentSpace J z),
      IsOpen W ∧ f x ∈ W ∧ CMDiff[W] ∞ (T% B) ∧
      CMDiff[f ⁻¹' W] ∞ (T% (fun y ↦ h.horizontalLift y (B (f y)))) ∧
      h.horizontalLift x (B (f x)) = u := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  obtain ⟨s, hs, hBs⟩ := exists_contMDiffOn_extend (k := ∞) J F (mfderiv I J f x u)
  refine ⟨interior s, extend F (mfderiv I J f x u), isOpen_interior,
    mem_interior_iff_mem_nhds.2 hs, hBs.mono interior_subset, fun y hy ↦ ?_, ?_⟩
  · exact (h.contMDiffAt_horizontalLift
      ((hBs.mono interior_subset).contMDiffAt (isOpen_interior.mem_nhds hy))
      (by simp)).contMDiffWithinAt
  · simp [extend_apply_self, h.horizontalLift_mfderiv_of_mem x hu]

/-! ### Covariant derivatives of `A` and `T` -/

omit [FiniteDimensional ℝ F] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] h in
private theorem hom_hom_apply
    {S : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) y (S y)))
    {Y Z : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (w : TangentSpace I x) :
    ((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        S x w (Y x) (Z x) =
      leviCivitaConnection I M (fun y ↦ S y (Y y) (Z y)) x w -
        S x (leviCivitaConnection I M Y x w) (Z x) -
        S x (Y x) (leviCivitaConnection I M Z x w) := by
  let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
  have hSd := hS.mdifferentiableAt (by simp) (x := x)
  rw [CovariantDerivative.hom_apply _ _ hSd hY w, sub_apply,
    CovariantDerivative.hom_apply _ _ (hSd.clm_bundle_apply hY) hZ w]
  abel

omit [FiniteDimensional ℝ F] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] h in
/-- Skew-adjointness of a smooth bilinear bundle section in its last two slots passes to its
covariant derivative under the induced Hom-bundle connection. -/
private theorem inner_hom_hom_of_skew
    {S : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) y (S y)))
    (hskew : ∀ y u a b, ⟪S y u a, b⟫_ℝ = -⟪a, S y u b⟫_ℝ)
    (w u a b : TangentSpace I x) :
    ⟪((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        S x w u a, b⟫_ℝ =
      -⟪a, ((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M))) S x w u b⟫_ℝ := by
  let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hSd := hS.mdifferentiableAt (by simp) (x := x)
  have hU := mdifferentiableAt_extend I E u
  have hA := mdifferentiableAt_extend I E a
  have hB := mdifferentiableAt_extend I E b
  have hSUA := (hSd.clm_bundle_apply hU).clm_bundle_apply hA
  have hSUB := (hSd.clm_bundle_apply hU).clm_bundle_apply hB
  set φ₁ : M → ℝ := fun y ↦ ⟪S y (extend E u y) (extend E a y), extend E b y⟫_ℝ
  set φ₂ : M → ℝ := fun y ↦ ⟪extend E a y, S y (extend E u y) (extend E b y)⟫_ℝ
  have hzero : φ₁ + φ₂ = fun _ ↦ 0 :=
    funext fun y ↦ by simp only [Pi.add_apply, φ₁, φ₂, hskew, neg_add_cancel]
  have hmetric := isMetricCompatible_leviCivitaConnection I (M := M)
  have hm₁ := hmetric.mvfderiv_inner_eq (extend E w) hSUA hB
  have hm₂ := hmetric.mvfderiv_inner_eq (extend E w) hA hSUB
  have hd : mvfderiv I (φ₁ + φ₂) x (extend E w x) = 0 := by
    rw [hzero, mvfderiv_const, zero_apply]
  rw [mvfderiv_add (TauCeti.Manifold.mdifferentiableAt_inner hSUA hB)
      (TauCeti.Manifold.mdifferentiableAt_inner hA hSUB), add_apply, hm₁, hm₂] at hd
  have hevalA := hom_hom_apply hS hU hA w
  have hevalB := hom_hom_apply hS hU hB w
  simp only [extend_apply_self, hskew] at hd hevalA hevalB
  rw [hevalA, hevalB]
  simp only [inner_sub_left, inner_sub_right, hskew]
  linarith

variable [T2Space M]

/-- Leibniz evaluation of the covariant derivative `∇A` on differentiable vector fields. -/
theorem hom_oneillA_apply {Y Z : Π y : M, TangentSpace I y}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (w : TangentSpace I x) :
    ((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x w (Y x) (Z x) =
      leviCivitaConnection I M (fun y ↦ h.oneillA y (Y y) (Z y)) x w -
        h.oneillA x (leviCivitaConnection I M Y x w) (Z x) -
        h.oneillA x (Y x) (leviCivitaConnection I M Z x w) :=
  hom_hom_apply h.contMDiff_oneillA hY hZ w

/-- Leibniz evaluation of the covariant derivative `∇T` on differentiable vector fields. -/
theorem hom_oneillT_apply {Y Z : Π y : M, TangentSpace I y}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (w : TangentSpace I x) :
    ((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillT x w (Y x) (Z x) =
      leviCivitaConnection I M (fun y ↦ h.oneillT y (Y y) (Z y)) x w -
        h.oneillT x (leviCivitaConnection I M Y x w) (Z x) -
        h.oneillT x (Y x) (leviCivitaConnection I M Z x w) :=
  hom_hom_apply h.contMDiff_oneillT hY hZ w

/-- The covariant derivative `∇A` remains skew-adjoint in its last two arguments. -/
theorem inner_hom_oneillA (w u a b : TangentSpace I x) :
    ⟪((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x w u a, b⟫_ℝ =
      -⟪a, ((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M))) h.oneillA x w u b⟫_ℝ :=
  inner_hom_hom_of_skew h.contMDiff_oneillA h.inner_oneillA w u a b

/-- The covariant derivative `∇T` remains skew-adjoint in its last two arguments. -/
theorem inner_hom_oneillT (w u a b : TangentSpace I x) :
    ⟪((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillT x w u a, b⟫_ℝ =
      -⟪a, ((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M))) h.oneillT x w u b⟫_ℝ :=
  inner_hom_hom_of_skew h.contMDiff_oneillT h.inner_oneillT w u a b

/-- Differentiating `A_X X = 0` along any tangent vector `a` shows that `(∇_a A) u u` has no
vertical component when `u` is horizontal. -/
theorem inner_hom_oneillA_self (a : TangentSpace I x)
    {u w : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).ker) :
    ⟪((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x a u u, w⟫_ℝ = 0 := by
  obtain ⟨W, B, hW, hfxW, hBW, hXW, hXx⟩ := h.exists_contMDiffOn_horizontalLift hu
  have hUopen : IsOpen (f ⁻¹' W) := hW.preimage h.isSubmersion.contMDiff.continuous
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B (f y))
  have hXd : MDiffAt (T% X) x :=
    (hXW.contMDiffAt (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp)
  have hB1 : CMDiffAt 1 (T% B) (f x) :=
    (hBW.contMDiffAt (hW.mem_nhds hfxW)).of_le (m := 1) (by simp)
  have hzero : (fun y ↦ h.oneillA y (X y) (X y)) = 0 :=
    funext fun y ↦ h.oneillA_self (h.horizontalLift_mem_orthogonal_ker y _)
  have heval := h.hom_oneillA_apply hXd hXd a
  rw [show X x = u from hXx] at heval
  rw [heval, hzero, CovariantDerivative.zero, Pi.zero_apply, zero_apply,
    zero_sub, h.leviCivitaConnection_horizontalLift_apply hB1 a, hXx]
  set hpart := h.horizontalLift x (leviCivitaConnection J N B (f x) (mfderiv I J f x a)) +
    h.oneillA x u ((mfderiv I J f x).ker.starProjection a)
  set vpart := h.oneillA x a u + h.oneillT x a u
  have hhpart : hpart ∈ (mfderiv I J f x).kerᗮ :=
    add_mem (h.horizontalLift_mem_orthogonal_ker x _)
      (h.oneillA_apply_mem_orthogonal_ker _ (Submodule.starProjection_apply_mem _ _))
  have hvpart : vpart ∈ (mfderiv I J f x).ker :=
    add_mem (h.oneillA_apply_mem_ker a hu) (h.oneillT_apply_mem_ker a hu)
  have hv0 : h.oneillA x vpart u = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hvpart, h.oneillA_starProjection_ker,
      zero_apply]
  have hrew : h.horizontalLift x (leviCivitaConnection J N B (f x) (mfderiv I J f x a)) +
      h.oneillA x a u + h.oneillA x u ((mfderiv I J f x).ker.starProjection a) +
      h.oneillT x a u = hpart + vpart := by
    dsimp only [hpart, vpart]; abel
  have horth : ⟪h.oneillA x u vpart, w⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hw (h.oneillA_apply_mem_orthogonal_ker u hvpart)
  rw [hrew, (h.oneillA x).map_add hpart vpart, add_apply, (h.oneillA x u).map_add hpart vpart,
    hv0, add_zero, h.oneillA_antisymm hhpart hu]
  simp only [sub_eq_add_neg, neg_add_rev, neg_neg, inner_add_left, inner_neg_left, horth]
  linarith

/-- Paired with a vertical vector `w`, `(∇_a A) u v` is alternating in horizontal arguments
`u, v`. -/
theorem inner_hom_oneillA_antisymm (a : TangentSpace I x)
    {u v w : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).ker) :
    ⟪((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x a u v, w⟫_ℝ =
      -⟪((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
        h.oneillA x a v u, w⟫_ℝ := by
  have huv := h.inner_hom_oneillA_self a (add_mem hu hv) hw
  simp only [map_add, add_apply, inner_add_left,
    h.inner_hom_oneillA_self a hu hw, h.inner_hom_oneillA_self a hv hw] at huv
  linarith

end TauCeti.IsRiemannianSubmersion
