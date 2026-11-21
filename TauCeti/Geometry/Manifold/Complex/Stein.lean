/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Complex
public import TauCeti.Analysis.Complex.Runge.Hull
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Topology.ContinuousMap.Separation

/-!
# Holomorphic hulls and Stein manifolds

Let `M` be a complex manifold modelled on `I : ModelWithCorners ℂ E H`. Its *holomorphic hull*
`TauCeti.mholomorphicHull I K` of a set `K ⊆ M` consists of the points `x` at which every global
holomorphic function `f : M → ℂ` satisfies every modulus bound it satisfies on `K`. For compact
`K` this is the set of `x` with `‖f x‖ ≤ sup_K ‖f‖` for all holomorphic `f`; the hull of the empty
set is empty. Holomorphic functions are `MDifferentiable I 𝓘(ℂ)` maps.

A *Stein manifold* (`TauCeti.IsSteinManifold I M`) is a complex manifold which is
* holomorphically convex: the holomorphic hull of every compact set is compact;
* holomorphically separable: global holomorphic functions separate points;
* at every point some global holomorphic map `M → E` to the model space has injective
  differential.

We show that a complex normed space with compact closed balls, that is a finite-dimensional one
such as `ℂⁿ` for every `n`, is a Stein manifold: continuous linear functionals separate points
and bound compact hulls, and the identity is a global coordinate. A complex manifold of
dimension zero is Stein, since there every function is holomorphic and the hull of a set is the
set itself. Conversely, holomorphic functions on a compact complex manifold without boundary are
locally constant, so a compact Stein manifold without boundary is finite; for instance the Riemann
sphere is not Stein.
The separation axiom also forces every Stein manifold to be Hausdorff.

## Main declarations

* `TauCeti.mholomorphicHull`: the holomorphic hull of a subset of a complex manifold, with
  `IsCompact.mem_mholomorphicHull_iff` characterizing it on compact sets by suprema.
* `TauCeti.mholomorphicHull_eq_holomorphicHull_univ`: on `ℂ` it is the planar holomorphic hull
  `TauCeti.holomorphicHull Set.univ`.
* `TauCeti.IsSteinManifold`: the class of Stein manifolds.
* `TauCeti.IsSteinManifold.self`: a complex normed space with compact closed balls is Stein.
* `TauCeti.IsSteinManifold.of_subsingleton`: a complex manifold of dimension zero is Stein.
* `TauCeti.IsSteinManifold.t2Space`: a Stein manifold is Hausdorff.
* `TauCeti.IsSteinManifold.finite_of_compactSpace`: a compact Stein manifold without boundary is
  finite.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Definition 5.1.3.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter I, §6.
-/

public section

open Set Function Topology
open scoped Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Holomorphic hulls -/

/-- The holomorphic hull of a subset `K` of a complex manifold `M`: the points at which every
global holomorphic function `M → ℂ` satisfies every real modulus bound it satisfies on `K`. For
compact `K` these are the points `x` with `‖f x‖ ≤ sup_K ‖f‖` for every holomorphic `f`
(`IsCompact.mem_mholomorphicHull_iff`); the hull of the empty set is empty. -/
def mholomorphicHull (K : Set M) : Set M :=
  {x | ∀ f : M → ℂ, MDifferentiable I 𝓘(ℂ) f → ∀ B : ℝ, (∀ y ∈ K, ‖f y‖ ≤ B) → ‖f x‖ ≤ B}

variable {I} {K L : Set M} {x : M}

/-- Membership in `TauCeti.mholomorphicHull`. -/
theorem mem_mholomorphicHull_iff :
    x ∈ mholomorphicHull I K ↔
      ∀ f : M → ℂ, MDifferentiable I 𝓘(ℂ) f → ∀ B : ℝ, (∀ y ∈ K, ‖f y‖ ≤ B) → ‖f x‖ ≤ B :=
  Iff.rfl

/-- Any modulus bound satisfied on `K` by a global holomorphic function also holds on the
holomorphic hull of `K`. -/
theorem norm_le_of_mem_mholomorphicHull (hx : x ∈ mholomorphicHull I K) {f : M → ℂ}
    (hf : MDifferentiable I 𝓘(ℂ) f) {B : ℝ} (hB : ∀ y ∈ K, ‖f y‖ ≤ B) : ‖f x‖ ≤ B :=
  hx f hf B hB

/-- A set is contained in its holomorphic hull. -/
theorem subset_mholomorphicHull : K ⊆ mholomorphicHull I K :=
  fun x hx _ _ _ hB ↦ hB x hx

/-- The holomorphic hull is monotone. -/
@[gcongr]
theorem mholomorphicHull_mono (h : K ⊆ L) : mholomorphicHull I K ⊆ mholomorphicHull I L :=
  fun _ hx f hf B hB ↦ hx f hf B fun y hy ↦ hB y (h hy)

/-- The holomorphic hull of the empty set is empty. -/
@[simp]
theorem mholomorphicHull_empty : mholomorphicHull I (∅ : Set M) = ∅ :=
  eq_empty_of_forall_notMem fun _ hx ↦ by
    -- The constant function `1` is bounded by `0` on the empty set.
    have := norm_le_of_mem_mholomorphicHull hx mdifferentiable_const (f := fun _ ↦ 1) (B := 0)
      (by simp)
    norm_num at this

/-- The holomorphic hull is idempotent. -/
@[simp]
theorem mholomorphicHull_idem : mholomorphicHull I (mholomorphicHull I K) = mholomorphicHull I K :=
  subset_mholomorphicHull.antisymm' fun _ hx f hf B hB ↦
    hx f hf B fun _ hy ↦ hy f hf B hB

/-- The holomorphic hull is closed, as an intersection of sublevel sets of the continuous
functions `‖f‖`. -/
theorem isClosed_mholomorphicHull : IsClosed (mholomorphicHull I K) := by
  have : mholomorphicHull I K = ⋂ f : {f : M → ℂ // MDifferentiable I 𝓘(ℂ) f},
      ⋂ B : {B : ℝ // ∀ y ∈ K, ‖f.val y‖ ≤ B}, {x | ‖f.val x‖ ≤ B.val} := by
    ext x
    simp [mem_mholomorphicHull_iff]
  rw [this]
  exact isClosed_iInter fun f ↦ isClosed_iInter fun B ↦
    isClosed_le f.property.continuous.norm continuous_const

/-- On a compact set `K`, the holomorphic hull consists of the points at which every global
holomorphic function has modulus at most its supremum on `K`. For empty `K` both sides are
empty, the supremum of the empty set of reals being `0`. -/
theorem _root_.IsCompact.mem_mholomorphicHull_iff (hK : IsCompact K) :
    x ∈ mholomorphicHull I K ↔
      ∀ f : M → ℂ, MDifferentiable I 𝓘(ℂ) f → ‖f x‖ ≤ sSup ((‖f ·‖) '' K) := by
  refine ⟨fun hx f hf ↦ hx f hf _ fun y hy ↦ ?_, fun h f hf B hB ↦ ?_⟩
  · exact le_csSup ((hK.image hf.continuous.norm).bddAbove) (mem_image_of_mem _ hy)
  · rcases K.eq_empty_or_nonempty with rfl | hne
    · have := h (fun _ ↦ 1) mdifferentiable_const
      norm_num at this
    · exact (h f hf).trans (csSup_le (hne.image _) (forall_mem_image.2 hB))

/-- On the complex line, the holomorphic hull is the planar holomorphic hull in `ℂ`. -/
theorem mholomorphicHull_eq_holomorphicHull_univ (K : Set ℂ) :
    mholomorphicHull 𝓘(ℂ) K = holomorphicHull univ K := by
  ext z
  simp [mem_mholomorphicHull_iff, mem_holomorphicHull_iff, mdifferentiable_iff_differentiable,
    differentiableOn_univ]

/-- In dimension zero the holomorphic hull of a set is the set itself. -/
@[simp]
theorem mholomorphicHull_eq_self_of_subsingleton [Subsingleton E] (K : Set M) :
    mholomorphicHull I K = K := by
  classical
  refine subset_antisymm (fun x hx ↦ ?_) subset_mholomorphicHull
  by_contra hxK
  -- Every function is holomorphic, in particular the indicator function of `x`, which vanishes
  -- on `K`.
  have := norm_le_of_mem_mholomorphicHull hx (f := fun y ↦ if y = x then 1 else 0)
    mdifferentiable_of_subsingleton (B := 0) fun y hy ↦ by
      have hyx : y ≠ x := fun h ↦ hxK (h ▸ hy)
      simp [hyx]
  norm_num at this

/-! ### Stein manifolds -/

variable (I M) in
/-- A complex manifold `M` modelled on `I` is a *Stein manifold* if it is holomorphically convex,
global holomorphic functions separate its points, and at every point some global holomorphic map
to the model space `E` has injective differential. Holomorphic maps are `MDifferentiable` maps. -/
class IsSteinManifold : Prop where
  /-- Holomorphic convexity: the holomorphic hull of a compact set is compact. -/
  isCompact_mholomorphicHull {K : Set M} : IsCompact K → IsCompact (mholomorphicHull I K)
  /-- Holomorphic separability: distinct points are separated by a global holomorphic
  function. -/
  exists_mdifferentiable_apply_ne {x y : M} :
    x ≠ y → ∃ f : M → ℂ, MDifferentiable I 𝓘(ℂ) f ∧ f x ≠ f y
  /-- Injective differentials: at every point, some global holomorphic map to the model
  space has injective differential. -/
  exists_mdifferentiable_injective_mfderiv (x : M) :
    ∃ F : M → E, MDifferentiable I 𝓘(ℂ, E) F ∧ Injective (mfderiv I 𝓘(ℂ, E) F x)

namespace IsSteinManifold

/-- A complex normed space with compact closed balls, for instance `ℂⁿ`, is a Stein manifold. -/
instance self [ProperSpace E] : IsSteinManifold 𝓘(ℂ, E) E where
  isCompact_mholomorphicHull {K} hK := by
    -- By Hahn–Banach, the hull of a set bounded by `R` is bounded by `R`.
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    refine (isCompact_closedBall (0 : E) R).of_isClosed_subset isClosed_mholomorphicHull
      fun x hx ↦ ?_
    obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' ℂ x
    have := norm_le_of_mem_mholomorphicHull hx
      (mdifferentiable_iff_differentiable.2 g.differentiable) (B := R) fun y hy ↦
        (g.le_of_opNorm_le hg y).trans (by simpa using mem_closedBall_zero_iff.1 (hR hy))
    simpa [hgx] using this
  exists_mdifferentiable_apply_ne {x y} hxy := by
    obtain ⟨g, hg⟩ := SeparatingDual.exists_separating_of_ne (R := ℂ) hxy
    exact ⟨g, mdifferentiable_iff_differentiable.2 g.differentiable, hg⟩
  exists_mdifferentiable_injective_mfderiv x :=
    ⟨id, mdifferentiable_id, by simpa [mfderiv_id] using injective_id⟩

/-- A complex manifold of dimension zero is a Stein manifold. -/
instance (priority := 100) of_subsingleton [Subsingleton E] : IsSteinManifold I M where
  isCompact_mholomorphicHull hK := by rwa [mholomorphicHull_eq_self_of_subsingleton]
  exists_mdifferentiable_apply_ne {x y} hxy := by
    classical
    exact ⟨fun z ↦ if z = x then 1 else 0, mdifferentiable_of_subsingleton, by simp [hxy.symm]⟩
  exists_mdifferentiable_injective_mfderiv x :=
    -- The tangent space is a type synonym for the model; its subsingleton instance is not
    -- inferred.
    let : Subsingleton (TangentSpace I x) := inferInstanceAs (Subsingleton E)
    ⟨fun _ ↦ 0, mdifferentiable_const, injective_of_subsingleton _⟩

variable (I)

/-- A Stein manifold is Hausdorff. -/
theorem t2Space [IsSteinManifold I M] : T2Space M :=
  -- Global holomorphic functions are continuous and separate points.
  Set.SeparatesPoints.t2Space (B := {g : C(M, ℂ) | MDifferentiable I 𝓘(ℂ) g}) fun _ _ hxy ↦
    let ⟨f, hf, hfxy⟩ := exists_mdifferentiable_apply_ne (I := I) hxy
    ⟨f, ⟨⟨f, hf.continuous⟩, hf, rfl⟩, hfxy⟩

/-- A compact Stein manifold without boundary is finite. -/
theorem finite_of_compactSpace [IsSteinManifold I M] [I.Boundaryless] [IsManifold I 1 M]
    [CompactSpace M] : Finite M := by
  -- Holomorphic functions on a compact complex manifold without boundary are locally constant,
  -- hence constant on connected components; as they separate points, every connected component,
  -- which is open, is a single point.
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  have : DiscreteTopology M := discreteTopology_iff_isOpen_singleton.2 fun x ↦ by
    convert isOpen_connectedComponent (x := x)
    refine (eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy ↦ ?_⟩).symm
    by_contra hne
    obtain ⟨f, hf, hfxy⟩ := exists_mdifferentiable_apply_ne (I := I) hne
    exact hfxy (hf.isLocallyConstant.apply_eq_of_isPreconnected isPreconnected_connectedComponent
      hy mem_connectedComponent)
  exact finite_of_compact_of_discrete

end IsSteinManifold

end TauCeti
