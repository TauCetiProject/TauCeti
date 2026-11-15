/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection

/-!
# O'Neill's connection equations for a Riemannian submersion

For a smooth Riemannian submersion `f : M → N`, write `h` and `v` for the orthogonal horizontal
and vertical projections on `TM`, and `A` and `T` for O'Neill's fundamental tensors
(`IsRiemannianSubmersion.oneillA` and `IsRiemannianSubmersion.oneillT`). Decomposing the
Levi-Civita derivative `∇` of `M` into its horizontal and vertical components yields O'Neill's
four connection equations:

* `∇_U V = T_U V + v (∇_U V)` for vertical `U` and a vertical field `V`;
* `∇_U Y = h (∇_U Y) + T_U Y` for vertical `U` and a horizontal field `Y`;
* `∇_X V = A_X V + v (∇_X V)` for horizontal `X` and a vertical field `V`;
* `∇_X Y = h (∇_X Y) + A_X Y` for horizontal `X` and a horizontal field `Y`.

When `Y'` is a basic horizontal field (writing `B'` for the horizontal lift of a vector field `B`
on `N`), every component of `∇ Y'` reduces to base differentiation and O'Neill's tensors:

* `[X', Y'] = [X, Y]' + 2 A_X' Y'` for basic horizontal fields `X'` and `Y'`;
* `[X', V] = v (∇_X' V) - T_V X'` for a basic horizontal field `X'` and a vertical field `V`;
* `h (∇_U Y') = A_Y' U`, and hence `∇_U Y' = A_Y' U + T_U Y'`, for vertical `U`;
* `∇_X' Y' = (∇^N_X Y)' + A_X' Y'` for basic horizontal directions.

These formulas express iterated covariant derivatives of basic horizontal and vertical fields in
terms of the base connection and the algebraic tensors `A` and `T`, supplying the connection step
in O'Neill's curvature equations and in the horizontal geodesic equations.

## Main results

* `TauCeti.IsRiemannianSubmersion.contMDiff_horizontalLift`: horizontal lifting preserves global
  `C^n` regularity of vector fields.
* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_of_eventually_mem_orthogonal_ker`,
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_of_eventually_mem_ker`: decomposition of
  `∇_u Y` and `∇_u V` for arbitrary tangent directions `u`, with directional specializations for
  horizontal and vertical `u`.
* `TauCeti.IsRiemannianSubmersion.mlieBracket_horizontalLift`: horizontal-vertical decomposition
  of the Lie bracket of two basic horizontal fields.
* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift_of_mem_ker`: O'Neill's
  formula `∇_u Y' = A_Y' u + T_u Y'` along a vertical vector `u`, proved from
  `h (∇_u Y') = A_Y' u`.
* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift_apply`: full Levi-Civita
  derivative of a basic horizontal field along horizontal lifts and arbitrary tangent vectors.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Lemmas 1 and 2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §C, Lemmas 9.24 and 9.25.
-/

public section

open Bundle Filter Manifold VectorField
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

section Regularity

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsManifold I 1 M] [IsManifold J 1 N]
  {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

include h

/-- Horizontal lifting of a `C^n` vector field on the base gives a `C^n` vector field on the
total space, for `C^n` metrics and `n + 1 ≤ ∞`. -/
theorem contMDiff_horizontalLift {X : Π y : N, TangentSpace J y}
    (hX : ContMDiff J (J.prod 𝓘(ℝ, F)) n (T% X)) (hn : n + 1 ≤ ∞) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) n (T% (fun y ↦ h.horizontalLift y (X (f y)))) :=
  fun x ↦ h.contMDiffAt_horizontalLift (hX (f x)) hn

end Regularity

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

/-! ### Decomposition of the Levi-Civita connection on horizontal and vertical fields -/

section Decomposition

variable {x : M}

/-- For a vector field `Y` which is horizontal near `x` and an arbitrary tangent vector `u`, the
vertical component of `∇_u Y` is `A_u Y + T_u Y`. -/
theorem starProjection_ker_leviCivitaConnection_of_eventually_mem_orthogonal_ker
    {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) (u : TangentSpace I x) :
    (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M Y x u) =
      h.oneillA x u (Y x) + h.oneillT x u (Y x) := by
  conv_lhs =>
    rw [← Submodule.starProjection_add_starProjection_orthogonal (K := (mfderiv I J f x).ker) u]
  rw [map_add, map_add, add_comm,
    ← h.oneillA_apply_of_eventually_mem_orthogonal_ker hY hYh u,
    ← h.oneillT_apply_of_eventually_mem_orthogonal_ker hY hYh u]

/-- For a vector field `V` which is vertical near `x` and an arbitrary tangent vector `u`, the
horizontal component of `∇_u V` is `A_u V + T_u V`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_of_eventually_mem_ker
    {V : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) (u : TangentSpace I x) :
    (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M V x u) =
      h.oneillA x u (V x) + h.oneillT x u (V x) := by
  conv_lhs =>
    rw [← Submodule.starProjection_add_starProjection_orthogonal (K := (mfderiv I J f x).ker) u]
  rw [map_add, map_add, add_comm,
    ← h.oneillA_apply_of_eventually_mem_ker hV hVv u,
    ← h.oneillT_apply_of_eventually_mem_ker hV hVv u]

/-- For a vector field `Y` which is horizontal near `x` and any tangent vector `u`,
`∇_u Y = h (∇_u Y) + A_u Y + T_u Y`. -/
theorem leviCivitaConnection_of_eventually_mem_orthogonal_ker
    {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) (u : TangentSpace I x) :
    CovariantDerivative.leviCivitaConnection I M Y x u =
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M Y x u) +
      h.oneillA x u (Y x) + h.oneillT x u (Y x) := by
  conv_lhs =>
    rw [← Submodule.starProjection_add_starProjection_orthogonal
      (K := (mfderiv I J f x).ker) (CovariantDerivative.leviCivitaConnection I M Y x u)]
  rw [add_comm, h.starProjection_ker_leviCivitaConnection_of_eventually_mem_orthogonal_ker hY hYh,
    add_assoc]

/-- For a vector field `V` which is vertical near `x` and any tangent vector `u`,
`∇_u V = A_u V + T_u V + v (∇_u V)`. -/
theorem leviCivitaConnection_of_eventually_mem_ker
    {V : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) (u : TangentSpace I x) :
    CovariantDerivative.leviCivitaConnection I M V x u =
      h.oneillA x u (V x) + h.oneillT x u (V x) +
      (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M V x u) := by
  conv_lhs =>
    rw [← Submodule.starProjection_add_starProjection_orthogonal
      (K := (mfderiv I J f x).ker) (CovariantDerivative.leviCivitaConnection I M V x u)]
  rw [add_comm, h.starProjection_orthogonal_ker_leviCivitaConnection_of_eventually_mem_ker hV hVv]

/-- **O'Neill's first connection equation.** For a vertical field `V` and a vertical vector `u`,
`∇_u V = T_u V + v (∇_u V)`. -/
theorem leviCivitaConnection_of_eventually_mem_ker_of_mem_ker
    {V : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker)
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker) :
    CovariantDerivative.leviCivitaConnection I M V x u =
      h.oneillT x u (V x) +
        (mfderiv I J f x).ker.starProjection
          (CovariantDerivative.leviCivitaConnection I M V x u) := by
  have ha : h.oneillA x u (V x) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hu, h.oneillA_starProjection_ker, zero_apply]
  conv_lhs => rw [h.leviCivitaConnection_of_eventually_mem_ker hV hVv u]
  rw [ha, zero_add]

/-- **O'Neill's second connection equation.** For a horizontal field `Y` and a vertical vector `u`,
`∇_u Y = h (∇_u Y) + T_u Y`. -/
theorem leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_ker
    {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker) :
    CovariantDerivative.leviCivitaConnection I M Y x u =
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M Y x u) +
      h.oneillT x u (Y x) := by
  have ha : h.oneillA x u (Y x) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hu, h.oneillA_starProjection_ker, zero_apply]
  conv_lhs => rw [h.leviCivitaConnection_of_eventually_mem_orthogonal_ker hY hYh u]
  rw [ha, add_zero]

/-- **O'Neill's third connection equation.** For a vertical field `V` and a horizontal vector `u`,
`∇_u V = A_u V + v (∇_u V)`. -/
theorem leviCivitaConnection_of_eventually_mem_ker_of_mem_orthogonal_ker
    {V : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker)
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    CovariantDerivative.leviCivitaConnection I M V x u =
      h.oneillA x u (V x) +
        (mfderiv I J f x).ker.starProjection
          (CovariantDerivative.leviCivitaConnection I M V x u) := by
  have ht : h.oneillT x u (V x) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hu, h.oneillT_starProjection_orthogonal_ker,
      zero_apply]
  conv_lhs => rw [h.leviCivitaConnection_of_eventually_mem_ker hV hVv u]
  rw [ht, add_zero]

/-- **O'Neill's fourth connection equation.** For a horizontal field `Y` and a horizontal
vector `u`, `∇_u Y = h (∇_u Y) + A_u Y`. -/
theorem leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_orthogonal_ker
    {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    CovariantDerivative.leviCivitaConnection I M Y x u =
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M Y x u) +
      h.oneillA x u (Y x) := by
  have ht : h.oneillT x u (Y x) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hu, h.oneillT_starProjection_orthogonal_ker,
      zero_apply]
  conv_lhs => rw [h.leviCivitaConnection_of_eventually_mem_orthogonal_ker hY hYh u]
  rw [ht, add_zero]

end Decomposition

/-! ### Brackets and covariant derivatives of basic horizontal fields -/

section BasicFields

variable {X Y : Π y : N, TangentSpace J y} {x : M}

/-- The Lie bracket of two basic horizontal fields `X'` and `Y'` decomposes into the horizontal lift
of the base bracket and `2 A_X' Y'`. -/
theorem mlieBracket_horizontalLift
    (hX : CMDiffAt 1 (T% X) (f x)) (hY : CMDiffAt 1 (T% Y) (f x)) :
    mlieBracket I (fun y ↦ h.horizontalLift y (X (f y)))
        (fun y ↦ h.horizontalLift y (Y (f y))) x =
      h.horizontalLift x (mlieBracket J X Y (f x)) +
        (2 : ℝ) • h.oneillA x (h.horizontalLift x (X (f x)))
          (h.horizontalLift x (Y (f x))) := by
  set X' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (X (f y))
  set Y' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Y (f y))
  have hXd : MDiffAt (T% X') x :=
    (h.contMDiffAt_horizontalLift hX (by norm_num)).mdifferentiableAt one_ne_zero
  have hYd : MDiffAt (T% Y') x :=
    (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  conv_lhs =>
    rw [← Submodule.starProjection_add_starProjection_orthogonal
      (K := (mfderiv I J f x).ker) (mlieBracket I X' Y' x)]
  rw [add_comm, ← h.horizontalLift_mfderiv, h.mfderiv_mlieBracket_horizontalLift hX hY,
    h.starProjection_ker_mlieBracket hXd hYd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)]

/-- The Lie bracket of a basic horizontal field with a vertical field is vertical. -/
theorem mlieBracket_horizontalLift_mem_ker
    (hX : CMDiffAt 1 (T% X) (f x)) {V : Π y : M, TangentSpace I y}
    (hV : MDiffAt (T% V) x) (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) :
    mlieBracket I (fun y ↦ h.horizontalLift y (X (f y))) V x ∈ (mfderiv I J f x).ker :=
  (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv_of_eventually_related
    (by simp [minSmoothness_of_isRCLikeNormedField])
    ((h.contMDiffAt_horizontalLift hX (by norm_num)).mdifferentiableAt one_ne_zero)
    hV (hX.mdifferentiableAt one_ne_zero)
    (.of_forall fun y ↦ h.mfderiv_horizontalLift y _) hVv

/-- For a basic horizontal field `Y'` and a vertical vector `u`, the horizontal part of `∇_u Y'`
equals `A_Y' u` (O'Neill, Lemma 2(3)). -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
    (hY : CMDiffAt 1 (T% Y) (f x)) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).ker) :
    (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ h.horizontalLift y (Y (f y))) x u) =
      h.oneillA x (h.horizontalLift x (Y (f x))) u := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set Y' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Y (f y))
  have hYd : MDiffAt (T% Y') x :=
    (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  set V : Π y : M, TangentSpace I y :=
    fun y ↦ (mfderiv I J f y).ker.starProjection (FiberBundle.extend E u y)
  have hVd : MDiffAt (T% V) x :=
    ((h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
      (by simp)).clm_bundle_apply (FiberBundle.mdifferentiableAt_extend I E u)
  have hVx : V x = u := by
    simp [V, FiberBundle.extend_apply_self, Submodule.starProjection_eq_self_iff.mpr hu]
  have hVv : ∀ y, V y ∈ (mfderiv I J f y).ker := fun _ ↦ Submodule.starProjection_apply_mem _ _
  have hT := ((CovariantDerivative.torsion_eq_zero_iff _).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)) hYd hVd
  have hbr : (mfderiv I J f x).kerᗮ.starProjection (mlieBracket I Y' V x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr <| by
      rw [Submodule.orthogonal_orthogonal]
      exact h.mlieBracket_horizontalLift_mem_ker hY hVd (.of_forall hVv)
  have ha := h.oneillA_apply_of_eventually_mem_ker hVd (.of_forall hVv) (Y' x)
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _),
    hVx] at ha
  rw [← hT, map_sub, sub_eq_zero, hVx] at hbr
  exact hbr.symm.trans ha.symm

/-- Along a vertical vector `u`, the Levi-Civita derivative of a basic horizontal field `Y'` is
purely algebraic: `∇_u Y' = A_Y' u + T_u Y'`. -/
theorem leviCivitaConnection_horizontalLift_of_mem_ker
    (hY : CMDiffAt 1 (T% Y) (f x)) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).ker) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ h.horizontalLift y (Y (f y))) x u =
      h.oneillA x (h.horizontalLift x (Y (f x))) u +
        h.oneillT x u (h.horizontalLift x (Y (f x))) := by
  have hYd : MDiffAt (T% (fun y ↦ h.horizontalLift y (Y (f y)))) x :=
    (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  rw [h.leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_ker hYd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _) hu,
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker hY hu]

/-- For a basic horizontal field `X'` and a vertical field `V`, the Lie bracket `[X', V]` equals
`v (∇_X' V) - T_V X'`. -/
theorem mlieBracket_horizontalLift_of_eventually_mem_ker
    (hX : CMDiffAt 1 (T% X) (f x)) {V : Π y : M, TangentSpace I y}
    (hV : MDiffAt (T% V) x) (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) :
    mlieBracket I (fun y ↦ h.horizontalLift y (X (f y))) V x =
      (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M V x
          (h.horizontalLift x (X (f x)))) -
      h.oneillT x (V x) (h.horizontalLift x (X (f x))) := by
  set X' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (X (f y))
  have hXd : MDiffAt (T% X') x :=
    (h.contMDiffAt_horizontalLift hX (by norm_num)).mdifferentiableAt one_ne_zero
  have hT := ((CovariantDerivative.torsion_eq_zero_iff _).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)) hXd hV
  have hmem := h.mlieBracket_horizontalLift_mem_ker hX hV hVv
  have ha0 : (mfderiv I J f x).ker.starProjection (h.oneillA x (X' x) (V x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (h.oneillA_apply_mem_orthogonal_ker _ hVv.self_of_nhds)
  have ht0 : (mfderiv I J f x).ker.starProjection (h.oneillT x (V x) (X' x)) =
      h.oneillT x (V x) (X' x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (h.oneillT_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _))
  conv_lhs => rw [← Submodule.starProjection_eq_self_iff.mpr hmem, ← hT]
  rw [map_sub, h.leviCivitaConnection_horizontalLift_of_mem_ker hX hVv.self_of_nhds,
    map_add, ha0, zero_add, ht0]

/-- Along a lifted base vector `v'`, the Levi-Civita derivative of a basic horizontal field `Y'`
is the lift of `∇^N_v Y` plus `A_v' Y'` (O'Neill, Lemma 1(3)). -/
theorem leviCivitaConnection_horizontalLift
    (hY : CMDiffAt 1 (T% Y) (f x)) (v : TangentSpace J (f x)) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ h.horizontalLift y (Y (f y))) x (h.horizontalLift x v) =
      h.horizontalLift x (CovariantDerivative.leviCivitaConnection J N Y (f x) v) +
        h.oneillA x (h.horizontalLift x v) (h.horizontalLift x (Y (f x))) := by
  let : IsManifold J 2 N := .of_le (n := ∞) (by norm_cast)
  let : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    .of_le (n := ∞) (by simp)
  let : IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y) :=
    .of_le (n := ∞) (by simp)
  have hYd : MDiffAt (T% (fun y ↦ h.horizontalLift y (Y (f y)))) x :=
    (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  rw [h.leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_orthogonal_ker hYd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
      (h.horizontalLift_mem_orthogonal_ker x v),
    h.starProjection_covariantDerivative_horizontalLift
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection J) hY v]

/-- Along any horizontal vector `u`, the Levi-Civita derivative of a basic horizontal field `Y'`
decomposes as `(∇^N_(df u) Y)' + A_u Y'`. -/
theorem leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
    (hY : CMDiffAt 1 (T% Y) (f x)) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ h.horizontalLift y (Y (f y))) x u =
      h.horizontalLift x
          (CovariantDerivative.leviCivitaConnection J N Y (f x) (mfderiv I J f x u)) +
        h.oneillA x u (h.horizontalLift x (Y (f x))) := by
  conv_lhs => rw [← h.horizontalLift_mfderiv_of_mem x hu]
  rw [h.leviCivitaConnection_horizontalLift hY, h.horizontalLift_mfderiv_of_mem x hu]

/-- Along an arbitrary tangent vector `w`, the Levi-Civita derivative of a basic horizontal field
`Y'` decomposes completely into the lifted base derivative and O'Neill's tensors `A` and `T`. -/
theorem leviCivitaConnection_horizontalLift_apply
    (hY : CMDiffAt 1 (T% Y) (f x)) (w : TangentSpace I x) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ h.horizontalLift y (Y (f y))) x w =
      h.horizontalLift x
          (CovariantDerivative.leviCivitaConnection J N Y (f x) (mfderiv I J f x w)) +
        h.oneillA x w (h.horizontalLift x (Y (f x))) +
        h.oneillA x (h.horizontalLift x (Y (f x))) ((mfderiv I J f x).ker.starProjection w) +
        h.oneillT x w (h.horizontalLift x (Y (f x))) := by
  conv_lhs =>
    rw [← Submodule.starProjection_add_starProjection_orthogonal (K := (mfderiv I J f x).ker) w]
  have hm : mfderiv I J f x ((mfderiv I J f x).kerᗮ.starProjection w) = mfderiv I J f x w := by
    rw [← h.horizontalLift_mfderiv, h.mfderiv_horizontalLift]
  rw [map_add,
    h.leviCivitaConnection_horizontalLift_of_mem_ker hY (Submodule.starProjection_apply_mem _ _),
    h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker hY
      (Submodule.starProjection_apply_mem _ _),
    hm, h.oneillT_starProjection_ker, h.oneillA_starProjection_orthogonal_ker]
  abel

end BasicFields

end TauCeti.IsRiemannianSubmersion
