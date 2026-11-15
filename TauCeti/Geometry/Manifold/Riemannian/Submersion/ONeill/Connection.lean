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
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Prod

/-!
# O'Neill's Levi-Civita connection equations for a Riemannian submersion

For a Riemannian submersion `f : M → N` with orthogonal horizontal and vertical projections
`h` and `v`, O'Neill's tensors `A` and `T` (`IsRiemannianSubmersion.oneillA` and
`IsRiemannianSubmersion.oneillT`) decompose the Levi-Civita connection of `M` on horizontal and
vertical vector fields:

* If `Y` is horizontal near `x` and `u : TangentSpace I x`, then
  `∇_u Y = h (∇_u Y) + A_u (Y x) + T_u (Y x)`. In particular, `∇_u Y = h (∇_u Y) + A_u (Y x)` when
  `u` is horizontal and `∇_u Y = h (∇_u Y) + T_u (Y x)` when `u` is vertical.
* If `V` is vertical near `x` and `u : TangentSpace I x`, then
  `∇_u V = A_u (V x) + T_u (V x) + v (∇_u V)`. In particular, `∇_u V = A_u (V x) + v (∇_u V)` when
  `u` is horizontal and `∇_u V = T_u (V x) + v (∇_u V)` when `u` is vertical.
* If `X = B̂ ∘ f` is the basic horizontal lift of a `C¹` vector field `B` on `N`, then along a
  horizontal lift `v̂` one has `∇_v̂ X = (∇^N_v B)^ + A_v̂ (X x)`, while along a vertical vector `u`
  one has `h (∇_u X) = A_(X x) u` and `∇_u X = A_(X x) u + T_u (X x)`. Combining both components
  yields the full derivative `∇_w X` along an arbitrary tangent vector `w` at `x`.

For the first projection of a Riemannian product `M × N → M`, the horizontal and vertical
projections read off the two factor components and both `oneillA` and `oneillT` vanish identically.

## Main results

* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_of_eventually_mem_orthogonal_ker`,
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_of_eventually_mem_ker`: O'Neill's
  decomposition of `∇_u Y` and `∇_u V` for arbitrary direction vectors `u`.
* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift_of_mem_ker`,
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift_apply`: Levi-Civita
  derivatives of basic horizontal lifts along horizontal, vertical, and arbitrary tangent vectors.
* `TauCeti.starProjection_orthogonal_ker_fst`, `TauCeti.starProjection_ker_fst`,
  `TauCeti.oneillA_fst`, `TauCeti.oneillT_fst`: explicit projections and vanishing of O'Neill's
  tensors for a Riemannian product projection.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Lemma 2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §C, Proposition 9.24.
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
local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

local instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

include h

/-! ### General horizontal and vertical vector fields -/

section Fields

variable {x : M}

/-- For a vector field `Y` which is horizontal near `x`, the vertical part of `∇_u Y` in any
direction `u` is the sum `A_u (Y x) + T_u (Y x)`. -/
theorem starProjection_ker_leviCivitaConnection_of_eventually_mem_orthogonal_ker
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) (u : TangentSpace I x) :
    (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M Y x u) =
      h.oneillA x u (Y x) + h.oneillT x u (Y x) := by
  conv_lhs => rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal u]
  rw [map_add, map_add, add_comm,
    ← h.oneillA_apply_of_eventually_mem_orthogonal_ker hY hYh u,
    ← h.oneillT_apply_of_eventually_mem_orthogonal_ker hY hYh u]

/-- **O'Neill's connection decomposition on a horizontal field.** If `Y` is horizontal near `x`,
then `∇_u Y = h (∇_u Y) + A_u (Y x) + T_u (Y x)` for every tangent vector `u` at `x`. -/
theorem leviCivitaConnection_of_eventually_mem_orthogonal_ker
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) (u : TangentSpace I x) :
    CovariantDerivative.leviCivitaConnection I M Y x u =
      (mfderiv I J f x).kerᗮ.starProjection
          (CovariantDerivative.leviCivitaConnection I M Y x u) +
        h.oneillA x u (Y x) + h.oneillT x u (Y x) := by
  conv_lhs =>
    rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal
      (CovariantDerivative.leviCivitaConnection I M Y x u)]
  rw [h.starProjection_ker_leviCivitaConnection_of_eventually_mem_orthogonal_ker hY hYh u]
  abel

/-- On a field `Y` which is horizontal near `x` and a horizontal vector `u`,
`∇_u Y = h (∇_u Y) + A_u (Y x)`. -/
theorem leviCivitaConnection_of_mem_orthogonal_ker_of_eventually_mem_orthogonal_ker
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    CovariantDerivative.leviCivitaConnection I M Y x u =
      (mfderiv I J f x).kerᗮ.starProjection
          (CovariantDerivative.leviCivitaConnection I M Y x u) +
        h.oneillA x u (Y x) := by
  have hu0 : h.oneillT x u (Y x) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hu, h.oneillT_starProjection_orthogonal_ker,
      zero_apply]
  conv_lhs => rw [h.leviCivitaConnection_of_eventually_mem_orthogonal_ker hY hYh u]
  rw [hu0, add_zero]

/-- On a field `Y` which is horizontal near `x` and a vertical vector `u`,
`∇_u Y = h (∇_u Y) + T_u (Y x)`. -/
theorem leviCivitaConnection_of_mem_ker_of_eventually_mem_orthogonal_ker
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).ker) :
    CovariantDerivative.leviCivitaConnection I M Y x u =
      (mfderiv I J f x).kerᗮ.starProjection
          (CovariantDerivative.leviCivitaConnection I M Y x u) +
        h.oneillT x u (Y x) := by
  have hu0 : h.oneillA x u (Y x) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hu, h.oneillA_starProjection_ker,
      zero_apply]
  conv_lhs => rw [h.leviCivitaConnection_of_eventually_mem_orthogonal_ker hY hYh u]
  rw [hu0, add_zero]

/-- For a vector field `V` which is vertical near `x`, the horizontal part of `∇_u V` in any
direction `u` is the sum `A_u (V x) + T_u (V x)`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_of_eventually_mem_ker
    {V : Π x : M, TangentSpace I x} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) (u : TangentSpace I x) :
    (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M V x u) =
      h.oneillA x u (V x) + h.oneillT x u (V x) := by
  conv_lhs => rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal u]
  rw [map_add, map_add, add_comm,
    ← h.oneillA_apply_of_eventually_mem_ker hV hVv u,
    ← h.oneillT_apply_of_eventually_mem_ker hV hVv u]

/-- **O'Neill's connection decomposition on a vertical field.** If `V` is vertical near `x`,
then `∇_u V = A_u (V x) + T_u (V x) + v (∇_u V)` for every tangent vector `u` at `x`. -/
theorem leviCivitaConnection_of_eventually_mem_ker
    {V : Π x : M, TangentSpace I x} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) (u : TangentSpace I x) :
    CovariantDerivative.leviCivitaConnection I M V x u =
      h.oneillA x u (V x) + h.oneillT x u (V x) +
        (mfderiv I J f x).ker.starProjection
          (CovariantDerivative.leviCivitaConnection I M V x u) := by
  conv_lhs =>
    rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal
      (CovariantDerivative.leviCivitaConnection I M V x u)]
  rw [h.starProjection_orthogonal_ker_leviCivitaConnection_of_eventually_mem_ker hV hVv u]
  abel

/-- On a field `V` which is vertical near `x` and a horizontal vector `u`,
`∇_u V = A_u (V x) + v (∇_u V)`. -/
theorem leviCivitaConnection_of_mem_orthogonal_ker_of_eventually_mem_ker
    {V : Π x : M, TangentSpace I x} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    CovariantDerivative.leviCivitaConnection I M V x u =
      h.oneillA x u (V x) +
        (mfderiv I J f x).ker.starProjection
          (CovariantDerivative.leviCivitaConnection I M V x u) := by
  have hu0 : h.oneillT x u (V x) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hu, h.oneillT_starProjection_orthogonal_ker,
      zero_apply]
  conv_lhs => rw [h.leviCivitaConnection_of_eventually_mem_ker hV hVv u]
  rw [hu0, add_zero]

/-- On a field `V` which is vertical near `x` and a vertical vector `u`,
`∇_u V = T_u (V x) + v (∇_u V)`. -/
theorem leviCivitaConnection_of_mem_ker_of_eventually_mem_ker
    {V : Π x : M, TangentSpace I x} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).ker) :
    CovariantDerivative.leviCivitaConnection I M V x u =
      h.oneillT x u (V x) +
        (mfderiv I J f x).ker.starProjection
          (CovariantDerivative.leviCivitaConnection I M V x u) := by
  have hu0 : h.oneillA x u (V x) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hu, h.oneillA_starProjection_ker,
      zero_apply]
  conv_lhs => rw [h.leviCivitaConnection_of_eventually_mem_ker hV hVv u]
  rw [hu0, zero_add]

end Fields

/-! ### Basic horizontal lifts -/

section HorizontalLift

variable {x : M} {B : Π y : N, TangentSpace J y}

-- This regularity index is propositionally, but not definitionally, equal to two.
local instance : IsManifold I ((1 : ℕ∞ω) + 1) M := by
  rw [one_add_one_eq_two]
  exact .of_le (n := ∞) (by simp)

/-- **O'Neill's horizontal-lift derivative along a horizontal vector.** For a `C¹` vector field
`B` on `N`, differentiating its horizontal lift along the horizontal lift of `v` gives the
horizontal lift of `∇^N_v B` plus `A_v̂ (B̂ (f x))`. -/
theorem leviCivitaConnection_horizontalLift (hB : CMDiffAt 1 (T% B) (f x))
    (v : TangentSpace J (f x)) :
    CovariantDerivative.leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x
        (h.horizontalLift x v) =
      h.horizontalLift x (CovariantDerivative.leviCivitaConnection J N B (f x) v) +
        h.oneillA x (h.horizontalLift x v) (h.horizontalLift x (B (f x))) := by
  have hXd : MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x :=
    (h.contMDiffAt_horizontalLift hB (by norm_num)).mdifferentiableAt one_ne_zero
  rw [h.leviCivitaConnection_of_mem_orthogonal_ker_of_eventually_mem_orthogonal_ker hXd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
      (h.horizontalLift_mem_orthogonal_ker x v),
    h.starProjection_covariantDerivative_horizontalLift
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection J) hB v]

/-- For a `C¹` vector field `B` on `N` and a vertical vector `u` at `x`, the horizontal part of
`∇_u (B̂ ∘ f)` is `A_(B̂ (f x)) u`. This is O'Neill's identity `h (∇_V X) = A_X V` for basic
horizontal fields `X`, reflecting the verticality of `[X, V]`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
    (hB : CMDiffAt 1 (T% B) (f x)) {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker) :
    (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ h.horizontalLift y (B (f y))) x u) =
      h.oneillA x (h.horizontalLift x (B (f x))) u := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B (f y))
  have hXd : MDiffAt (T% X) x :=
    (h.contMDiffAt_horizontalLift hB (by norm_num)).mdifferentiableAt one_ne_zero
  set V : Π y : M, TangentSpace I y :=
    fun y ↦ (mfderiv I J f y).ker.starProjection (FiberBundle.extend E u y)
  have hQ := (h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hVd : MDiffAt (T% V) x := hQ.clm_bundle_apply (FiberBundle.mdifferentiableAt_extend I E u)
  have hVx : V x = u := by
    simp [V, FiberBundle.extend_apply_self, Submodule.starProjection_eq_self_iff.mpr hu]
  have hVv (y : M) : V y ∈ (mfderiv I J f y).ker := Submodule.starProjection_apply_mem _ _
  have hT := ((CovariantDerivative.torsion_eq_zero_iff _).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)) hXd hVd
  have hbr : (mfderiv I J f x).kerᗮ.starProjection (mlieBracket I X V x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr <| by
      rw [Submodule.orthogonal_orthogonal]
      exact (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv_of_eventually_related
        (by simp [minSmoothness_of_isRCLikeNormedField]) hXd hVd
        (hB.mdifferentiableAt one_ne_zero) (.of_forall fun y ↦ h.mfderiv_horizontalLift y _)
        (.of_forall hVv)
  have hXV := h.oneillA_apply_of_eventually_mem_ker hVd (.of_forall hVv) (X x)
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _),
    hVx] at hXV
  rw [← hT, map_sub, sub_eq_zero, hVx] at hbr
  exact hbr.symm.trans hXV.symm

/-- **O'Neill's horizontal-lift derivative along a vertical vector.** For a `C¹` vector field `B`
on `N` and a vertical vector `u` at `x`, `∇_u (B̂ ∘ f) = A_(B̂ (f x)) u + T_u (B̂ (f x))`. -/
theorem leviCivitaConnection_horizontalLift_of_mem_ker (hB : CMDiffAt 1 (T% B) (f x))
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker) :
    CovariantDerivative.leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x u =
      h.oneillA x (h.horizontalLift x (B (f x))) u +
        h.oneillT x u (h.horizontalLift x (B (f x))) := by
  have hXd : MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x :=
    (h.contMDiffAt_horizontalLift hB (by norm_num)).mdifferentiableAt one_ne_zero
  rw [h.leviCivitaConnection_of_mem_ker_of_eventually_mem_orthogonal_ker hXd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _) hu,
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker hB hu]

/-- **Full Levi-Civita derivative of a basic horizontal lift.** For a `C¹` vector field `B` on `N`
and any tangent vector `w` at `x`,
`∇_w (B̂ ∘ f) = (∇^N_(df w) B)^ + A_w (B̂ (f x)) + A_(B̂ (f x)) (v w) + T_w (B̂ (f x))`. -/
theorem leviCivitaConnection_horizontalLift_apply (hB : CMDiffAt 1 (T% B) (f x))
    (w : TangentSpace I x) :
    CovariantDerivative.leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x w =
      h.horizontalLift x
          (CovariantDerivative.leviCivitaConnection J N B (f x) (mfderiv I J f x w)) +
        h.oneillA x w (h.horizontalLift x (B (f x))) +
        h.oneillA x (h.horizontalLift x (B (f x)))
          ((mfderiv I J f x).ker.starProjection w) +
        h.oneillT x w (h.horizontalLift x (B (f x))) := by
  conv_lhs =>
    rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal w,
      ← h.horizontalLift_mfderiv x w]
  rw [map_add,
    h.leviCivitaConnection_horizontalLift_of_mem_ker hB (Submodule.starProjection_apply_mem _ _),
    h.leviCivitaConnection_horizontalLift hB (mfderiv I J f x w),
    h.horizontalLift_mfderiv x w, h.oneillA_starProjection_orthogonal_ker,
    h.oneillT_starProjection_ker]
  abel

end HorizontalLift

end TauCeti.IsRiemannianSubmersion

/-! ### Riemannian product projection -/

namespace TauCeti

section Product

open scoped TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- For the first projection of a Riemannian product `M × N → M`, the horizontal orthogonal
projection keeps the first tangent component and zeroes the second. -/
theorem starProjection_orthogonal_ker_fst (p : M × N) (v : TangentSpace (I.prod J) p) :
    (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ.starProjection v =
      (Manifold.tangentSpaceProdEquiv p).symm ((Manifold.tangentSpaceProdEquiv p v).1, 0) := by
  set hsub := isRiemannianSubmersion_fst (I := I) (J := J) (M := M) (N := N)
  set v₁ := (Manifold.tangentSpaceProdEquiv p v).1
  set v₂ := (Manifold.tangentSpaceProdEquiv p v).2
  have hv₁ : (Manifold.tangentSpaceProdEquiv p).symm (v₁, 0) ∈
      (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ := by
    rw [← horizontalLift_fst]
    exact hsub.horizontalLift_mem_orthogonal_ker p v₁
  have hv₂ : (Manifold.tangentSpaceProdEquiv p).symm (0, v₂) ∈
      (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨b, rfl⟩ := hsub.range_horizontalLift p ▸ hu
    rw [LinearIsometry.coe_toLinearMap, horizontalLift_fst, Manifold.inner_tangentSpace_prod,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    simp
  have hdecomp : v = (Manifold.tangentSpaceProdEquiv p).symm (v₁, 0) +
      (Manifold.tangentSpaceProdEquiv p).symm (0, v₂) := by
    apply (Manifold.tangentSpaceProdEquiv p).injective
    rw [map_add, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext (add_zero v₁).symm (zero_add v₂).symm
  conv_lhs => rw [hdecomp]
  rw [map_add, Submodule.starProjection_eq_self_iff.mpr hv₁,
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hv₂, add_zero]

/-- For the first projection of a Riemannian product `M × N → M`, the vertical orthogonal
projection zeroes the first tangent component and keeps the second. -/
theorem starProjection_ker_fst (p : M × N) (v : TangentSpace (I.prod J) p) :
    (mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection v =
      (Manifold.tangentSpaceProdEquiv p).symm (0, (Manifold.tangentSpaceProdEquiv p v).2) := by
  rw [eq_sub_of_add_eq
    ((mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection_add_starProjection_orthogonal v),
    starProjection_orthogonal_ker_fst]
  apply (Manifold.tangentSpaceProdEquiv p).injective
  rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact Prod.ext (sub_self _) (sub_zero _)

variable
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

private theorem leviCivitaConnection_projections_fst_eq_zero (p : M × N)
    (u v : TangentSpace (I.prod J) p) :
    ∃ Y : Π q : M × N, TangentSpace (I.prod J) q,
      MDiffAt (T% Y) p ∧ Y p = v ∧
      (mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection
        (CovariantDerivative.leviCivitaConnection (I.prod J) (M × N)
          (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).kerᗮ.starProjection (Y q)) p u) = 0 ∧
      (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection (I.prod J) (M × N)
          (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).ker.starProjection (Y q)) p u) = 0 := by
  let Y₁ := FiberBundle.extend E (Manifold.tangentSpaceProdEquiv p v).1
  let Y₂ := FiberBundle.extend F (Manifold.tangentSpaceProdEquiv p v).2
  let Y := Manifold.prodVectorField (J := J) Y₁ Y₂
  have hY₁ : MDiffAt (T% Y₁) p.1 := FiberBundle.mdifferentiableAt_extend I E _
  have hY₂ : MDiffAt (T% Y₂) p.2 := FiberBundle.mdifferentiableAt_extend J F _
  have h0₁ : MDiffAt (T% (0 : Π x : M, TangentSpace I x)) p.1 := mdifferentiableAt_zeroSection ..
  have h0₂ : MDiffAt (T% (0 : Π y : N, TangentSpace J y)) p.2 := mdifferentiableAt_zeroSection ..
  have hH : (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).kerᗮ.starProjection (Y q)) =
      Manifold.prodVectorField Y₁ 0 := by
    funext q
    rw [starProjection_orthogonal_ker_fst]
    apply (Manifold.tangentSpaceProdEquiv q).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, Manifold.tangentSpaceProdEquiv_prodVectorField,
      Manifold.tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply]
  have hV : (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).ker.starProjection (Y q)) =
      Manifold.prodVectorField 0 Y₂ := by
    funext q
    rw [starProjection_ker_fst]
    apply (Manifold.tangentSpaceProdEquiv q).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, Manifold.tangentSpaceProdEquiv_prodVectorField,
      Manifold.tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply]
  refine ⟨Y, Manifold.mdifferentiableAt_prodVectorField hY₁ hY₂, ?_, ?_, ?_⟩
  · apply (Manifold.tangentSpaceProdEquiv p).injective
    rw [Manifold.tangentSpaceProdEquiv_prodVectorField]
    exact Prod.ext (FiberBundle.extend_apply_self ..) (FiberBundle.extend_apply_self ..)
  · rw [hH, starProjection_ker_fst]
    apply (Manifold.tangentSpaceProdEquiv p).injective
    rw [ContinuousLinearEquiv.apply_symm_apply,
      Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField hY₁ h0₂, map_zero]
    exact Prod.ext rfl (by simp [CovariantDerivative.zero])
  · rw [hV, starProjection_orthogonal_ker_fst]
    apply (Manifold.tangentSpaceProdEquiv p).injective
    rw [ContinuousLinearEquiv.apply_symm_apply,
      Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField h0₁ hY₂, map_zero]
    exact Prod.ext (by simp [CovariantDerivative.zero]) rfl

/-- O'Neill's horizontal tensor `A` vanishes identically on a Riemannian product projection. -/
@[simp]
theorem oneillA_fst (p : M × N) :
    (isRiemannianSubmersion_fst (I := I) (J := J) (M := M) (N := N)).oneillA p = 0 := by
  ext u v
  obtain ⟨Y, hY, rfl, h₁, h₂⟩ := leviCivitaConnection_projections_fst_eq_zero p
    ((mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ.starProjection u) v
  rw [zero_apply, zero_apply,
    (isRiemannianSubmersion_fst (I := I) (J := J)).oneillA_apply hY u, h₁, h₂, add_zero]

/-- O'Neill's vertical tensor `T` vanishes identically on a Riemannian product projection,
reflecting that the product fibres are totally geodesic. -/
@[simp]
theorem oneillT_fst (p : M × N) :
    (isRiemannianSubmersion_fst (I := I) (J := J) (M := M) (N := N)).oneillT p = 0 := by
  ext u v
  obtain ⟨Y, hY, rfl, h₁, h₂⟩ := leviCivitaConnection_projections_fst_eq_zero p
    ((mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection u) v
  rw [zero_apply, zero_apply,
    (isRiemannianSubmersion_fst (I := I) (J := J)).oneillT_apply hY u, h₂, h₁, add_zero]

end Product

end TauCeti
