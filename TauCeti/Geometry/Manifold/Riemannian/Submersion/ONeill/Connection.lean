/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Prod
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# O'Neill's Levi-Civita connection equations and integrability criterion

For a Riemannian submersion `f : M → N`, the total-space Levi-Civita connection splits along the
horizontal and vertical distributions into tangential components and O'Neill's fundamental tensors
`A` and `T` (`IsRiemannianSubmersion.oneillA` and `IsRiemannianSubmersion.oneillT`).

On general horizontal or vertical vector fields near a point, the mixed horizontal-vertical parts
of the Levi-Civita derivative are given by `A` along horizontal directions and by `T` along
vertical directions. On basic horizontal vector fields—horizontal lifts of vector fields on `N`—both
components are explicit:
* along a horizontal lift `hLift v`, the horizontal component is the lift of the base Levi-Civita
  derivative and the vertical component is `A_(hLift v) (hLift Y)`;
* along a vertical vector `v`, torsion-freeness and verticality of `[hLift X, V]` identify the
  horizontal component with `A_(hLift X) v`, while the vertical component is `T_v (hLift X)`.

By skew-adjointness of `A` and `T` and their exchange of the horizontal and vertical spaces, `A_x`
vanishes on `T_x M × T_x M` as soon as it vanishes on horizontal pairs, and `T_x` vanishes as soon
as it vanishes on vertical pairs (or on vertical diagonals, by symmetry of `T`). Consequently, the
horizontal distribution `x ↦ (ker df_x)ᗮ` is involutive on an open set precisely when `A` vanishes
there. For the first projection of a Riemannian product, both `A` and `T` vanish identically.

No separation or second-countability hypothesis is used.

## Main results

* `TauCeti.IsRiemannianSubmersion.oneillA_eq_zero_iff`,
  `TauCeti.IsRiemannianSubmersion.oneillT_eq_zero_iff`,
  `TauCeti.IsRiemannianSubmersion.oneillT_eq_zero_iff_self`: subspace vanishing criteria for `A`
  and `T`.
* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift_of_mem_ker`,
  `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift_apply`: O'Neill's connection
  formulas for basic horizontal vector fields along horizontal, vertical, and arbitrary directions.
* `TauCeti.IsRiemannianSubmersion.isInvolutiveDistributionOn_orthogonal_ker_iff`,
  `TauCeti.IsRiemannianSubmersion.isInvolutiveDistribution_orthogonal_ker_iff`: the horizontal
  distribution is involutive precisely when `A` vanishes.
* `TauCeti.oneillA_fst`, `TauCeti.oneillT_fst`: both fundamental tensors vanish for the projection
  of a Riemannian product.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966), 459–469,
  Lemmas 2 and 3.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Chapter 9, §C.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5.
-/

public section

open Bundle CovariantDerivative Filter Manifold Set VectorField
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

section Connection

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

-- These regularity indices are propositionally, but not definitionally, bounded by `∞`.
local instance : IsManifold I ((1 : ℕ∞ω) + 1) M := .of_le (n := ∞) (by simp)
local instance : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
local instance : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := ∞) (by simp)
local instance : IsManifold J (minSmoothness ℝ 2) N := .of_le (n := ∞) (by simp)

include h

/-! ### Projections and vanishing criteria for `A` and `T` -/

section Algebraic

variable {x : M}

omit [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] in
/-- `A` vanishes when its first argument is vertical. -/
theorem oneillA_eq_zero_of_mem_ker {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).ker) :
    h.oneillA x u = 0 := by
  rw [← Submodule.starProjection_eq_self_iff.mpr hu, h.oneillA_starProjection_ker]

omit [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] in
/-- `T` vanishes when its first argument is horizontal. -/
theorem oneillT_eq_zero_of_mem_orthogonal_ker {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    h.oneillT x u = 0 := by
  rw [← Submodule.starProjection_eq_self_iff.mpr hu, h.oneillT_starProjection_orthogonal_ker]

/-- The vertical part of `A_u v` is `A_u` applied to the horizontal part of `v`. -/
theorem starProjection_ker_oneillA (u v : TangentSpace I x) :
    (mfderiv I J f x).ker.starProjection (h.oneillA x u v) =
      h.oneillA x u ((mfderiv I J f x).kerᗮ.starProjection v) := by
  conv_lhs => rw [← Submodule.starProjection_add_starProjection_orthogonal
    (K := (mfderiv I J f x).ker) v]
  rw [map_add, map_add, Submodule.starProjection_eq_self_iff.mpr
      (h.oneillA_apply_mem_ker u (Submodule.starProjection_apply_mem _ _)),
    (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (h.oneillA_apply_mem_orthogonal_ker u (Submodule.starProjection_apply_mem _ _)),
    zero_add]

/-- The horizontal part of `A_u v` is `A_u` applied to the vertical part of `v`. -/
theorem starProjection_orthogonal_ker_oneillA (u v : TangentSpace I x) :
    (mfderiv I J f x).kerᗮ.starProjection (h.oneillA x u v) =
      h.oneillA x u ((mfderiv I J f x).ker.starProjection v) := by
  conv_lhs => rw [← Submodule.starProjection_add_starProjection_orthogonal
    (K := (mfderiv I J f x).ker) v]
  rw [map_add, map_add, Submodule.starProjection_eq_self_iff.mpr
      (h.oneillA_apply_mem_orthogonal_ker u (Submodule.starProjection_apply_mem _ _)),
    (Submodule.starProjection_apply_eq_zero_iff (mfderiv I J f x).kerᗮ).mpr (by
      rw [Submodule.orthogonal_orthogonal]
      exact h.oneillA_apply_mem_ker u (Submodule.starProjection_apply_mem _ _)),
    add_zero]

/-- The vertical part of `T_u v` is `T_u` applied to the horizontal part of `v`. -/
theorem starProjection_ker_oneillT (u v : TangentSpace I x) :
    (mfderiv I J f x).ker.starProjection (h.oneillT x u v) =
      h.oneillT x u ((mfderiv I J f x).kerᗮ.starProjection v) := by
  conv_lhs => rw [← Submodule.starProjection_add_starProjection_orthogonal
    (K := (mfderiv I J f x).ker) v]
  rw [map_add, map_add, Submodule.starProjection_eq_self_iff.mpr
      (h.oneillT_apply_mem_ker u (Submodule.starProjection_apply_mem _ _)),
    (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (h.oneillT_apply_mem_orthogonal_ker u (Submodule.starProjection_apply_mem _ _)),
    zero_add]

/-- The horizontal part of `T_u v` is `T_u` applied to the vertical part of `v`. -/
theorem starProjection_orthogonal_ker_oneillT (u v : TangentSpace I x) :
    (mfderiv I J f x).kerᗮ.starProjection (h.oneillT x u v) =
      h.oneillT x u ((mfderiv I J f x).ker.starProjection v) := by
  conv_lhs => rw [← Submodule.starProjection_add_starProjection_orthogonal
    (K := (mfderiv I J f x).ker) v]
  rw [map_add, map_add, Submodule.starProjection_eq_self_iff.mpr
      (h.oneillT_apply_mem_orthogonal_ker u (Submodule.starProjection_apply_mem _ _)),
    (Submodule.starProjection_apply_eq_zero_iff (mfderiv I J f x).kerᗮ).mpr (by
      rw [Submodule.orthogonal_orthogonal]
      exact h.oneillT_apply_mem_ker u (Submodule.starProjection_apply_mem _ _)),
    add_zero]

/-- **Horizontal vanishing criterion for `A`.** Since `A` vanishes on vertical first arguments and
is skew-adjoint between the horizontal and vertical spaces, `A_x` vanishes on `T_x M × T_x M`
precisely when it vanishes on pairs of horizontal vectors. -/
theorem oneillA_eq_zero_iff :
    h.oneillA x = 0 ↔
      ∀ u ∈ (mfderiv I J f x).kerᗮ, ∀ v ∈ (mfderiv I J f x).kerᗮ, h.oneillA x u v = 0 := by
  refine ⟨fun h0 u _ v _ ↦ by simp [h0], fun h0 ↦ ?_⟩
  ext u v
  rw [← h.oneillA_starProjection_orthogonal_ker]
  set u' := (mfderiv I J f x).kerᗮ.starProjection u
  have hu' : u' ∈ (mfderiv I J f x).kerᗮ := Submodule.starProjection_apply_mem _ _
  rw [← Submodule.starProjection_add_starProjection_orthogonal (K := (mfderiv I J f x).ker) v,
    map_add, h0 u' hu' _ (Submodule.starProjection_apply_mem _ _), add_zero]
  apply ext_inner_right ℝ fun w ↦ ?_
  simp only [zero_apply]
  have hmem := h.oneillA_apply_mem_orthogonal_ker u'
    (Submodule.starProjection_apply_mem (mfderiv I J f x).ker v)
  rw [← Submodule.starProjection_eq_self_iff.mpr hmem,
    Submodule.inner_starProjection_left_eq_right, h.inner_oneillA,
    h0 u' hu' _ (Submodule.starProjection_apply_mem _ _), inner_zero_right, neg_zero,
    inner_zero_left]

/-- `A_x` vanishes precisely when it vanishes on horizontal lifts of base tangent vectors. -/
theorem oneillA_eq_zero_iff_horizontalLift :
    h.oneillA x = 0 ↔
      ∀ u v : TangentSpace J (f x),
        h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v) = 0 := by
  rw [h.oneillA_eq_zero_iff]
  refine ⟨fun h0 u v ↦ h0 _ (h.horizontalLift_mem_orthogonal_ker x u) _
      (h.horizontalLift_mem_orthogonal_ker x v),
    fun h0 u hu v hv ↦ ?_⟩
  rw [← h.horizontalLift_mfderiv_of_mem x hu, ← h.horizontalLift_mfderiv_of_mem x hv]
  exact h0 _ _

/-- Because `A` vanishes on horizontal diagonals, `A_x u v` vanishes whenever `u` is horizontal and
`u, v` are linearly dependent. -/
theorem oneillA_eq_zero_of_not_linearIndependent {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (huv : ¬LinearIndependent ℝ ![u, v]) :
    h.oneillA x u v = 0 := by
  by_cases hu0 : u = 0
  · simp [hu0]
  · obtain ⟨c, hc⟩ := not_forall.mp ((LinearIndependent.pair_iff' hu0).not.mp huv)
    rw [← not_not.mp hc, map_smul, h.oneillA_self hu, smul_zero]

/-- When the base has dimension at most one, the horizontal spaces are at most one-dimensional, so
O'Neill's alternating horizontal tensor `A` vanishes identically. -/
theorem oneillA_eq_zero_of_finrank_le_one (hdim : Module.finrank ℝ (TangentSpace J (f x)) ≤ 1) :
    h.oneillA x = 0 := by
  rw [h.oneillA_eq_zero_iff_horizontalLift]
  intro u v
  apply h.oneillA_eq_zero_of_not_linearIndependent (h.horizontalLift_mem_orthogonal_ker x u)
  intro huv
  have hli : LinearIndependent ℝ ![u, v] :=
    .of_comp (h.horizontalLift x).toLinearMap (by convert huv; ext i; fin_cases i <;> rfl)
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

/-- **Vertical vanishing criterion for `T`.** Since `T` vanishes on horizontal first arguments and
is skew-adjoint between the vertical and horizontal spaces, `T_x` vanishes on `T_x M × T_x M`
precisely when it vanishes on pairs of vertical vectors. -/
theorem oneillT_eq_zero_iff :
    h.oneillT x = 0 ↔
      ∀ u ∈ (mfderiv I J f x).ker, ∀ v ∈ (mfderiv I J f x).ker, h.oneillT x u v = 0 := by
  refine ⟨fun h0 u _ v _ ↦ by simp [h0], fun h0 ↦ ?_⟩
  ext u v
  rw [← h.oneillT_starProjection_ker]
  set u' := (mfderiv I J f x).ker.starProjection u
  have hu' : u' ∈ (mfderiv I J f x).ker := Submodule.starProjection_apply_mem _ _
  rw [← Submodule.starProjection_add_starProjection_orthogonal (K := (mfderiv I J f x).ker) v,
    map_add, h0 u' hu' _ (Submodule.starProjection_apply_mem _ _), zero_add]
  apply ext_inner_right ℝ fun w ↦ ?_
  simp only [zero_apply]
  have hmem := h.oneillT_apply_mem_ker u'
    (Submodule.starProjection_apply_mem (mfderiv I J f x).kerᗮ v)
  rw [← Submodule.starProjection_eq_self_iff.mpr hmem,
    Submodule.inner_starProjection_left_eq_right, h.inner_oneillT,
    h0 u' hu' _ (Submodule.starProjection_apply_mem _ _), inner_zero_right, neg_zero,
    inner_zero_left]

/-- Since `T` is symmetric on vertical vectors, `T_x` vanishes precisely when `T_u u = 0` for
every vertical vector `u`. -/
theorem oneillT_eq_zero_iff_self :
    h.oneillT x = 0 ↔ ∀ u ∈ (mfderiv I J f x).ker, h.oneillT x u u = 0 := by
  rw [h.oneillT_eq_zero_iff]
  refine ⟨fun h0 u hu ↦ h0 u hu u hu, fun h0 u hu v hv ↦ ?_⟩
  have hsum := h0 (u + v) (add_mem hu hv)
  simp only [map_add, add_apply, h0 u hu, h0 v hv, zero_add, add_zero,
    h.oneillT_comm hv hu, ← two_smul ℝ (h.oneillT x u v), smul_eq_zero, OfNat.ofNat_ne_zero,
    false_or] at hsum
  exact hsum

end Algebraic

/-! ### Smoothness of fundamental tensor evaluations -/

section SmoothApply

/-- Evaluating O'Neill's horizontal tensor `A` on two smooth vector fields gives a smooth vector
field, without any separation assumption on the manifolds. -/
theorem contMDiff_oneillA_apply {X Y : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) :
    CMDiff ∞ (T% (fun x ↦ h.oneillA x (X x) (Y x))) := by
  have hP := h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)
  have hQ := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  let cov := leviCivitaConnection I M
  have hD₁ := cov.contMDiff_apply (hP.clm_bundle_apply hX) (hP.clm_bundle_apply hY)
  have hD₂ := cov.contMDiff_apply (hP.clm_bundle_apply hX) (hQ.clm_bundle_apply hY)
  refine ((hQ.clm_bundle_apply hD₁).add_section (hP.clm_bundle_apply hD₂)).congr fun x ↦ ?_
  exact congrArg (TotalSpace.mk' E x) (h.oneillA_apply (hY.mdifferentiableAt (by simp)) (X x))

/-- Evaluating O'Neill's vertical tensor `T` on two smooth vector fields gives a smooth vector
field, without any separation assumption on the manifolds. -/
theorem contMDiff_oneillT_apply {X Y : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) :
    CMDiff ∞ (T% (fun x ↦ h.oneillT x (X x) (Y x))) := by
  have hP := h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)
  have hQ := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  let cov := leviCivitaConnection I M
  have hD₁ := cov.contMDiff_apply (hQ.clm_bundle_apply hX) (hQ.clm_bundle_apply hY)
  have hD₂ := cov.contMDiff_apply (hQ.clm_bundle_apply hX) (hP.clm_bundle_apply hY)
  refine ((hP.clm_bundle_apply hD₁).add_section (hQ.clm_bundle_apply hD₂)).congr fun x ↦ ?_
  exact congrArg (TotalSpace.mk' E x) (h.oneillT_apply (hY.mdifferentiableAt (by simp)) (X x))

end SmoothApply

/-! ### Decomposition of the Levi-Civita connection -/

section Decompositions

variable {x : M}

/-- **O'Neill's connection equation** for a horizontal field along a horizontal direction:
`∇_u Y = h(∇_u Y) + A_u Y`. -/
theorem leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_orthogonal_ker
    {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    leviCivitaConnection I M Y x u =
      (mfderiv I J f x).kerᗮ.starProjection (leviCivitaConnection I M Y x u) +
        h.oneillA x u (Y x) := by
  rw [h.oneillA_apply_of_eventually_mem_orthogonal_ker hY hYh u,
    Submodule.starProjection_eq_self_iff.mpr hu, add_comm,
    Submodule.starProjection_add_starProjection_orthogonal]

/-- **O'Neill's connection equation** for a vertical field along a horizontal direction:
`∇_u V = A_u V + v(∇_u V)`. -/
theorem leviCivitaConnection_of_eventually_mem_ker_of_mem_orthogonal_ker
    {V : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    leviCivitaConnection I M V x u =
      h.oneillA x u (V x) +
        (mfderiv I J f x).ker.starProjection (leviCivitaConnection I M V x u) := by
  rw [h.oneillA_apply_of_eventually_mem_ker hV hVv u,
    Submodule.starProjection_eq_self_iff.mpr hu, add_comm,
    Submodule.starProjection_add_starProjection_orthogonal]

/-- **O'Neill's connection equation** for a horizontal field along a vertical direction:
`∇_v Y = h(∇_v Y) + T_v Y`. -/
theorem leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_ker
    {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) :
    leviCivitaConnection I M Y x v =
      (mfderiv I J f x).kerᗮ.starProjection (leviCivitaConnection I M Y x v) +
        h.oneillT x v (Y x) := by
  rw [h.oneillT_apply_of_eventually_mem_orthogonal_ker hY hYh v,
    Submodule.starProjection_eq_self_iff.mpr hv, add_comm,
    Submodule.starProjection_add_starProjection_orthogonal]

/-- **O'Neill's connection equation** for a vertical field along a vertical direction:
`∇_v V = T_v V + v(∇_v V)`. -/
theorem leviCivitaConnection_of_eventually_mem_ker_of_mem_ker
    {V : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) :
    leviCivitaConnection I M V x v =
      h.oneillT x v (V x) +
        (mfderiv I J f x).ker.starProjection (leviCivitaConnection I M V x v) := by
  rw [h.oneillT_apply_of_eventually_mem_ker hV hVv v,
    Submodule.starProjection_eq_self_iff.mpr hv, add_comm,
    Submodule.starProjection_add_starProjection_orthogonal]

/-- **Lie bracket of basic horizontal fields (O'Neill, Lemma 3(1)).** The bracket of two basic
horizontal lifts splits into the horizontal lift of the base bracket and `2 A` on the lifts. -/
theorem mlieBracket_horizontalLift {X Y : Π y : N, TangentSpace J y}
    (hX : CMDiffAt 1 (T% X) (f x)) (hY : CMDiffAt 1 (T% Y) (f x)) :
    mlieBracket I (fun y ↦ h.horizontalLift y (X (f y)))
        (fun y ↦ h.horizontalLift y (Y (f y))) x =
      h.horizontalLift x (mlieBracket J X Y (f x)) +
        (2 : ℝ) • h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x (Y (f x))) := by
  have hXd := (h.contMDiffAt_horizontalLift hX (by norm_num)).mdifferentiableAt one_ne_zero
  have hYd := (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  conv_lhs => rw [← Submodule.starProjection_add_starProjection_orthogonal
    (K := (mfderiv I J f x).ker)
    (mlieBracket I (fun y ↦ h.horizontalLift y (X (f y)))
      (fun y ↦ h.horizontalLift y (Y (f y))) x)]
  rw [add_comm, ← h.horizontalLift_mfderiv, h.mfderiv_mlieBracket_horizontalLift hX hY,
    h.starProjection_ker_mlieBracket hXd hYd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)]

/-- **O'Neill's connection equation for basic horizontal fields along horizontal lifts
(O'Neill, Lemma 3(3)).** -/
theorem leviCivitaConnection_horizontalLift {Y : Π y : N, TangentSpace J y}
    (hY : CMDiffAt 1 (T% Y) (f x)) (v : TangentSpace J (f x)) :
    leviCivitaConnection I M (fun y ↦ h.horizontalLift y (Y (f y))) x (h.horizontalLift x v) =
      h.horizontalLift x (leviCivitaConnection J N Y (f x) v) +
        h.oneillA x (h.horizontalLift x v) (h.horizontalLift x (Y (f x))) := by
  have hYd := (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  rw [h.leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_orthogonal_ker hYd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
      (h.horizontalLift_mem_orthogonal_ker x v),
    h.starProjection_covariantDerivative_horizontalLift
      (isLeviCivitaConnection_leviCivitaConnection I)
      (isLeviCivitaConnection_leviCivitaConnection J) hY v]

/-- **O'Neill's connection equation for a basic horizontal field along a horizontal vector.** -/
theorem leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
    {Y : Π y : N, TangentSpace J y} (hY : CMDiffAt 1 (T% Y) (f x))
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    leviCivitaConnection I M (fun y ↦ h.horizontalLift y (Y (f y))) x u =
      h.horizontalLift x (leviCivitaConnection J N Y (f x) (mfderiv I J f x u)) +
        h.oneillA x u (h.horizontalLift x (Y (f x))) := by
  conv_lhs => rw [← h.horizontalLift_mfderiv_of_mem x hu]
  rw [h.leviCivitaConnection_horizontalLift hY, h.horizontalLift_mfderiv_of_mem x hu]

/-- **Horizontal part of `∇_v (hLift X)` for vertical `v` (O'Neill, Lemma 3(2)).** Because the
bracket of a basic horizontal field with a vertical field is vertical, torsion-freeness equates
`h(∇_v (hLift X))` with `h(∇_(hLift X) V) = A_(hLift X) v`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
    {X : Π y : N, TangentSpace J y} (hX : CMDiffAt 1 (T% X) (f x))
    {v : TangentSpace I x} (hv : v ∈ (mfderiv I J f x).ker) :
    (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M (fun y ↦ h.horizontalLift y (X (f y))) x v) =
      h.oneillA x (h.horizontalLift x (X (f x))) v := by
  set X' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (X (f y))
  have hX'd : MDiffAt (T% X') x :=
    (h.contMDiffAt_horizontalLift hX (by norm_num)).mdifferentiableAt one_ne_zero
  set V : Π y : M, TangentSpace I y :=
    fun y ↦ (mfderiv I J f y).ker.starProjection (FiberBundle.extend E v y)
  have hVd : MDiffAt (T% V) x :=
    ((h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt (by simp))
      |>.clm_bundle_apply (FiberBundle.mdifferentiableAt_extend I E v)
  have hVx : V x = v := by simp [V, Submodule.starProjection_eq_self_iff.mpr hv]
  have hVv (y : M) : V y ∈ (mfderiv I J f y).ker := Submodule.starProjection_apply_mem _ _
  have htor := ((torsion_eq_zero_iff (leviCivitaConnection I M)).mp
    (torsion_leviCivitaConnection_eq_zero I)) hX'd hVd
  have hbr : (mfderiv I J f x).kerᗮ.starProjection (mlieBracket I X' V x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr <| by
      rw [Submodule.orthogonal_orthogonal]
      exact (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv_of_eventually_related
        (by simp [minSmoothness_of_isRCLikeNormedField]) hX'd hVd
        (hX.mdifferentiableAt one_ne_zero)
        (.of_forall fun y ↦ h.mfderiv_horizontalLift y _) (.of_forall hVv)
  rw [← htor, map_sub, sub_eq_zero] at hbr
  rw [← hVx, ← hbr, h.oneillA_apply_of_eventually_mem_ker hVd (.of_forall hVv) (X' x),
    Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)]

/-- **O'Neill's connection equation for a basic horizontal field along a vertical vector
(O'Neill, Lemma 3(2)).** -/
theorem leviCivitaConnection_horizontalLift_of_mem_ker
    {X : Π y : N, TangentSpace J y} (hX : CMDiffAt 1 (T% X) (f x))
    {v : TangentSpace I x} (hv : v ∈ (mfderiv I J f x).ker) :
    leviCivitaConnection I M (fun y ↦ h.horizontalLift y (X (f y))) x v =
      h.oneillA x (h.horizontalLift x (X (f x))) v +
        h.oneillT x v (h.horizontalLift x (X (f x))) := by
  have hX'd := (h.contMDiffAt_horizontalLift hX (by norm_num)).mdifferentiableAt one_ne_zero
  rw [h.leviCivitaConnection_of_eventually_mem_orthogonal_ker_of_mem_ker hX'd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _) hv,
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker hX hv]

/-- **Full connection decomposition for a basic horizontal field** along an arbitrary tangent
vector `v : TangentSpace I x`. -/
theorem leviCivitaConnection_horizontalLift_apply
    {X : Π y : N, TangentSpace J y} (hX : CMDiffAt 1 (T% X) (f x)) (v : TangentSpace I x) :
    leviCivitaConnection I M (fun y ↦ h.horizontalLift y (X (f y))) x v =
      h.horizontalLift x (leviCivitaConnection J N X (f x) (mfderiv I J f x v)) +
        h.oneillA x v (h.horizontalLift x (X (f x))) +
        h.oneillA x (h.horizontalLift x (X (f x))) ((mfderiv I J f x).ker.starProjection v) +
        h.oneillT x v (h.horizontalLift x (X (f x))) := by
  conv_lhs => rw [← Submodule.starProjection_add_starProjection_orthogonal
    (K := (mfderiv I J f x).ker) v]
  rw [map_add,
    h.leviCivitaConnection_horizontalLift_of_mem_ker hX (Submodule.starProjection_apply_mem _ _),
    h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker hX
      (Submodule.starProjection_apply_mem _ _),
    ← h.horizontalLift_mfderiv, h.mfderiv_horizontalLift, h.horizontalLift_mfderiv,
    h.oneillA_starProjection_orthogonal_ker, h.oneillT_starProjection_ker]
  abel

end Decompositions

/-! ### Integrability of the horizontal distribution -/

section Integrability

variable {x : M}

/-- For two vector fields horizontal near `x` and differentiable at `x`, their Lie bracket at `x`
is horizontal precisely when `A_x (X x) (Y x) = 0`. -/
theorem mlieBracket_mem_orthogonal_ker_iff {X Y : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) :
    mlieBracket I X Y x ∈ (mfderiv I J f x).kerᗮ ↔ h.oneillA x (X x) (Y x) = 0 := by
  simp [← Submodule.starProjection_apply_eq_zero_iff,
    h.starProjection_ker_mlieBracket hX hY hXh hYh]

/-- If O'Neill's horizontal tensor `A` vanishes on a set `s`, then the horizontal distribution
`x ↦ (ker df_x)ᗮ` is involutive on `s`. -/
theorem isInvolutiveDistributionOn_orthogonal_ker_of_oneillA_eq_zero {s : Set M}
    (hA : ∀ x ∈ s, h.oneillA x = 0) :
    IsInvolutiveDistributionOn I (fun x ↦ (mfderiv I J f x).kerᗮ) s := by
  rw [isInvolutiveDistributionOn_iff]
  intro U hU hUs V W hV hW hVD hWD x hx
  have hUx := hU.mem_nhds hx
  rw [h.mlieBracket_mem_orthogonal_ker_iff ((hV x hx).mdifferentiableAt hUx)
    ((hW x hx).mdifferentiableAt hUx) (eventually_of_mem hUx hVD) (eventually_of_mem hUx hWD),
    hA x (hUs hx)]
  simp

/-- **Integrability criterion on an open set.** On an open set `s`, the horizontal distribution
`x ↦ (ker df_x)ᗮ` is involutive precisely when O'Neill's tensor `A` vanishes at every point of
`s`. -/
theorem isInvolutiveDistributionOn_orthogonal_ker_iff {s : Set M} (hs : IsOpen s) :
    IsInvolutiveDistributionOn I (fun x ↦ (mfderiv I J f x).kerᗮ) s ↔
      ∀ x ∈ s, h.oneillA x = 0 := by
  refine ⟨fun hinv x hxs ↦ h.oneillA_eq_zero_iff.mpr fun u hu v hv ↦ ?_,
    h.isInvolutiveDistributionOn_orthogonal_ker_of_oneillA_eq_zero⟩
  obtain ⟨U₁, hU₁, hext₁⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) I E u
  obtain ⟨U₂, hU₂, hext₂⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) I E v
  set U := s ∩ (interior U₁ ∩ interior U₂)
  have hUopen : IsOpen U := hs.inter (isOpen_interior.inter isOpen_interior)
  have hxU : x ∈ U := ⟨hxs, mem_interior_iff_mem_nhds.mpr hU₁, mem_interior_iff_mem_nhds.mpr hU₂⟩
  have hP := (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).contMDiffOn (s := U)
  set V : Π y : M, TangentSpace I y :=
    fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (FiberBundle.extend E u y)
  set W : Π y : M, TangentSpace I y :=
    fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (FiberBundle.extend E v y)
  have hVd : MDiff[U] (T% V) := (hP.clm_bundle_apply
    (hext₁.mono (inter_subset_right.trans (inter_subset_left.trans interior_subset))))
    |>.mdifferentiableOn (by simp)
  have hWd : MDiff[U] (T% W) := (hP.clm_bundle_apply
    (hext₂.mono (inter_subset_right.trans (inter_subset_right.trans interior_subset))))
    |>.mdifferentiableOn (by simp)
  have hmem := hinv.mlieBracket_mem hUopen inter_subset_left hVd hWd
    (fun _ _ ↦ Submodule.starProjection_apply_mem _ _)
    (fun _ _ ↦ Submodule.starProjection_apply_mem _ _) hxU
  have hUx := hUopen.mem_nhds hxU
  have hzero := (h.mlieBracket_mem_orthogonal_ker_iff ((hVd x hxU).mdifferentiableAt hUx)
    ((hWd x hxU).mdifferentiableAt hUx)
    (.of_forall fun _ ↦ Submodule.starProjection_apply_mem _ _)
    (.of_forall fun _ ↦ Submodule.starProjection_apply_mem _ _)).mp hmem
  simpa only [V, W, FiberBundle.extend_apply_self, Submodule.starProjection_eq_self_iff.mpr hu,
    Submodule.starProjection_eq_self_iff.mpr hv] using hzero

/-- **Global integrability criterion.** The horizontal distribution `x ↦ (ker df_x)ᗮ` of a
Riemannian submersion is involutive precisely when O'Neill's horizontal tensor `A` vanishes
everywhere. -/
theorem isInvolutiveDistribution_orthogonal_ker_iff :
    IsInvolutiveDistribution I (fun x ↦ (mfderiv I J f x).kerᗮ) ↔ ∀ x, h.oneillA x = 0 := by
  rw [← isInvolutiveDistributionOn_univ,
    h.isInvolutiveDistributionOn_orthogonal_ker_iff isOpen_univ]
  simp

end Integrability

end Connection

end TauCeti.IsRiemannianSubmersion

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

private theorem starProjection_orthogonal_ker_fst (p : M × N) (v : TangentSpace (I.prod J) p) :
    (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ.starProjection v =
      (Manifold.tangentSpaceProdEquiv p).symm ((Manifold.tangentSpaceProdEquiv p v).1, 0) := by
  rw [← (isRiemannianSubmersion_fst (I := I) (J := J)).horizontalLift_mfderiv, horizontalLift_fst]
  congr 1
  simp only [mfderiv_fst, Manifold.tangentSpaceProdEquiv_apply]
  erw [ContinuousLinearMap.coe_fst']

private theorem starProjection_ker_fst (p : M × N) (v : TangentSpace (I.prod J) p) :
    (mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection v =
      (Manifold.tangentSpaceProdEquiv p).symm (0, (Manifold.tangentSpaceProdEquiv p v).2) := by
  apply (Manifold.tangentSpaceProdEquiv p).injective
  have hsum := Submodule.starProjection_add_starProjection_orthogonal
    (K := (mfderiv (I.prod J) I (@Prod.fst M N) p).ker) v
  rw [eq_sub_of_add_eq hsum, map_sub, starProjection_orthogonal_ker_fst,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  ext
  · exact sub_self _
  · exact sub_zero _

variable
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

private theorem leviCivitaConnection_projections_prodVectorField_fst (p : M × N)
    (v w : TangentSpace (I.prod J) p) :
    let Y₁ := FiberBundle.extend E (Manifold.tangentSpaceProdEquiv p w).1
    let Y₂ := FiberBundle.extend F (Manifold.tangentSpaceProdEquiv p w).2
    (mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection
        (leviCivitaConnection (I.prod J) (M × N)
          (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).kerᗮ.starProjection
            (Manifold.prodVectorField Y₁ Y₂ q)) p v) = 0 ∧
      (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ.starProjection
        (leviCivitaConnection (I.prod J) (M × N)
          (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).ker.starProjection
            (Manifold.prodVectorField Y₁ Y₂ q)) p v) = 0 := by
  intro Y₁ Y₂
  have hY₁ : MDiffAt (T% Y₁) p.1 := FiberBundle.mdifferentiableAt_extend I E _
  have hY₂ : MDiffAt (T% Y₂) p.2 := FiberBundle.mdifferentiableAt_extend J F _
  have h0M : MDiffAt (T% (0 : Π x : M, TangentSpace I x)) p.1 :=
    (contMDiff_zeroSection ℝ (TangentSpace I) (n := 1)).mdifferentiable one_ne_zero p.1
  have h0N : MDiffAt (T% (0 : Π y : N, TangentSpace J y)) p.2 :=
    (contMDiff_zeroSection ℝ (TangentSpace J) (n := 1)).mdifferentiable one_ne_zero p.2
  have hH : (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).kerᗮ.starProjection
      (Manifold.prodVectorField Y₁ Y₂ q)) = Manifold.prodVectorField Y₁ 0 := by
    funext q
    apply (Manifold.tangentSpaceProdEquiv q).injective
    rw [starProjection_orthogonal_ker_fst, ContinuousLinearEquiv.apply_symm_apply,
      Manifold.tangentSpaceProdEquiv_prodVectorField,
      Manifold.tangentSpaceProdEquiv_prodVectorField]
    rfl
  have hV : (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).ker.starProjection
      (Manifold.prodVectorField Y₁ Y₂ q)) = Manifold.prodVectorField 0 Y₂ := by
    funext q
    apply (Manifold.tangentSpaceProdEquiv q).injective
    rw [starProjection_ker_fst, ContinuousLinearEquiv.apply_symm_apply,
      Manifold.tangentSpaceProdEquiv_prodVectorField,
      Manifold.tangentSpaceProdEquiv_prodVectorField]
    rfl
  constructor
  · rw [hH, starProjection_ker_fst,
      Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField hY₁ h0N v,
      CovariantDerivative.zero]
    exact (Manifold.tangentSpaceProdEquiv p).symm.map_zero
  · rw [hV, starProjection_orthogonal_ker_fst,
      Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField h0M hY₂ v,
      CovariantDerivative.zero]
    exact (Manifold.tangentSpaceProdEquiv p).symm.map_zero

/-- O'Neill's horizontal tensor `A` vanishes for the first projection of a Riemannian product. -/
@[simp]
theorem oneillA_fst (p : M × N) :
    (isRiemannianSubmersion_fst (I := I) (J := J)).oneillA p = 0 := by
  ext u w
  set Y₁ := FiberBundle.extend E (Manifold.tangentSpaceProdEquiv p w).1
  set Y₂ := FiberBundle.extend F (Manifold.tangentSpaceProdEquiv p w).2
  have hY : MDiffAt (T% (Manifold.prodVectorField Y₁ Y₂)) p :=
    Manifold.mdifferentiableAt_prodVectorField (FiberBundle.mdifferentiableAt_extend I E _)
      (FiberBundle.mdifferentiableAt_extend J F _)
  have hYp : Manifold.prodVectorField Y₁ Y₂ p = w := by
    apply (Manifold.tangentSpaceProdEquiv p).injective
    rw [Manifold.tangentSpaceProdEquiv_prodVectorField]
    simp only [Y₁, Y₂, FiberBundle.extend_apply_self, Prod.mk.eta]
  rw [← hYp, (isRiemannianSubmersion_fst (I := I) (J := J)).oneillA_apply hY u]
  obtain ⟨h₁, h₂⟩ := leviCivitaConnection_projections_prodVectorField_fst p
    ((mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ.starProjection u) w
  dsimp only [Y₁, Y₂]
  rw [h₁, h₂, add_zero]
  simp only [zero_apply]

/-- O'Neill's vertical tensor `T` vanishes for the first projection of a Riemannian product. -/
@[simp]
theorem oneillT_fst (p : M × N) :
    (isRiemannianSubmersion_fst (I := I) (J := J)).oneillT p = 0 := by
  ext u w
  set Y₁ := FiberBundle.extend E (Manifold.tangentSpaceProdEquiv p w).1
  set Y₂ := FiberBundle.extend F (Manifold.tangentSpaceProdEquiv p w).2
  have hY : MDiffAt (T% (Manifold.prodVectorField Y₁ Y₂)) p :=
    Manifold.mdifferentiableAt_prodVectorField (FiberBundle.mdifferentiableAt_extend I E _)
      (FiberBundle.mdifferentiableAt_extend J F _)
  have hYp : Manifold.prodVectorField Y₁ Y₂ p = w := by
    apply (Manifold.tangentSpaceProdEquiv p).injective
    rw [Manifold.tangentSpaceProdEquiv_prodVectorField]
    simp only [Y₁, Y₂, FiberBundle.extend_apply_self, Prod.mk.eta]
  rw [← hYp, (isRiemannianSubmersion_fst (I := I) (J := J)).oneillT_apply hY u]
  obtain ⟨h₁, h₂⟩ := leviCivitaConnection_projections_prodVectorField_fst p
    ((mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection u) w
  dsimp only [Y₁, Y₂]
  rw [h₁, h₂, add_zero]
  simp only [zero_apply]

end Product

end TauCeti
