/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Sign
public import TauCeti.LinearAlgebra.Orientation.ShortExact

/-!
# Orientations of the spaces of Morse trajectories

Let `f` be a Morse function on a compact boundaryless manifold, `X` a Morse–Smale pseudo-gradient
adapted to `f`, and `p ≠ r` critical points. The trajectories from `p` to `r` form the set
`W^u(p) ∩ W^s(r)`, of dimension `ind p - ind r`, and the space of unparametrized trajectories is
read on a regular level `{f = c}` as the slice `W^u(p) ∩ W^s(r) ∩ {f = c}`, of dimension
`k = ind p - ind r - 1`. The integral Morse complex needs these spaces oriented, once the unstable
manifolds of `p` and `r` are. This file constructs the orientation of the tangent space of the
slice at each of its points, following the convention

`T W^u(p) = T 𝓜(p, r) ⊕ ℝ (-X) ⊕ T W^u(r)`,

with the space of trajectories first, then the negative-flow direction, then the unstable manifold
of `r`, standing for the normal space of `W^s(r)`.

Fix Morse charts `φp` at `p` and `φr` at `r` in which `X` is linear, and orientations `op` and
`or` of their spaces `Vp` and `Vr` of coordinates of negative weight. At a point `y` of a
trajectory, the comparison map `C : Vp → ℝ × Vr`,
`v ↦ (df_y (Fp v), Nr (Fp v))` (`TauCeti.IsAdaptedPseudoGradient.trajectoryComparison`), reads a
vector `Fp v` tangent to `W^u(p)` through the derivative of `f` and the normal coordinates of
`W^s(r)`. Under the Morse–Smale condition:

* `C` is onto (`TauCeti.IsAdaptedPseudoGradient.surjective_trajectoryComparison`): transversality
  makes its second component onto, and the velocity `X y`, tangent to both manifolds, is a vector
  on which `df_y` does not vanish;
* its kernel is the tangent space of the slice, read through the unstable frame: `Fp v` is
  tangent to `W^u(p) ∩ W^s(r)` and to the level of `f` exactly when `C v = 0`
  (`TauCeti.IsAdaptedPseudoGradient.mem_ker_trajectoryComparison_iff`), and it has dimension `k`
  (`TauCeti.IsAdaptedPseudoGradient.finrank_ker_trajectoryComparison_add`).

So `0 → ker C → Vp → ℝ × Vr → 0` is a short exact sequence, and the orientation `op` of `Vp`
together with the orientation of `ℝ × Vr` given by the standard orientation of `ℝ` followed by
`or` (`TauCeti.MorseChart.flowNormalOrientation`) induce an orientation of `ker C`, subspace first
(`Orientation.shortExactLeft`). This is the orientation of the trajectory space at `y`
(`TauCeti.IsAdaptedPseudoGradient.trajectorySpaceOrientation`). Concretely, a basis of `ker C` is
positive exactly when it is followed to an `op`-positive basis of `Vp` by lifts along `C` of
`(1, 0)`, for instance the vector whose frame is a positive multiple of the negative velocity, and
of the vectors `(0, e j)` for an `or`-positive basis `e` of `Vr`
(`TauCeti.IsAdaptedPseudoGradient.trajectorySpaceOrientation_eq_orientation_iff`).

When `ind p = ind r + 1` the kernel is zero and the comparison map is an isomorphism; whether it
carries `op` to the orientation of `ℝ × Vr` is the sign of the trajectory,
`TauCeti.IsAdaptedPseudoGradient.trajectorySign`. When `ind p = ind r + 2` the slice is a curve and
the orientation is a direction along it at `y`. The construction here is pointwise: how the
orientation varies along the slice is not treated in this file.

The orientation reverses when either of `op` and `or` does
(`TauCeti.IsAdaptedPseudoGradient.trajectorySpaceOrientation_neg_left`,
`TauCeti.IsAdaptedPseudoGradient.trajectorySpaceOrientation_neg_right`), and it does not depend on
the Morse charts: changing them and transporting `op` and `or` along the changes of negative
coordinates transports the orientation along the induced isomorphism of the kernels
(`TauCeti.IsAdaptedPseudoGradient.trajectorySpaceOrientation_map_negativeChange`).

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.trajectorySpaceOrientation`: the orientation of the tangent
  space of the space of trajectories, read on a level of `f`, at a point of a trajectory.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `mem_ker_trajectoryComparison_iff`: the kernel of the comparison map is the tangent space of the
  level slice.
* `finrank_ker_trajectoryComparison_add`, `finrank_ker_trajectoryComparison`: where the comparison
  map is onto, its kernel has dimension `ind p - ind r - 1`.
* `shortExact_trajectorySpaceOrientation`, `trajectorySpaceOrientation_eq_iff`: the orientation is
  the unique one inducing `op` with the subspace first.
* `trajectorySpaceOrientation_eq_orientation_iff`: its positive bases.
* `trajectorySpaceOrientation_neg_left`, `trajectorySpaceOrientation_neg_right`: reversing an
  orientation of an unstable manifold reverses it.
* `map_ker_trajectoryComparison_negativeChange`,
  `trajectorySpaceOrientation_map_negativeChange`: it does not depend on the Morse charts.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds and of the
  moduli spaces of flow lines).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (orientations of the spaces of trajectories).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {p r : M} {φp : MorseChart E f p}
  {φr : MorseChart E f r}

/-! ### The comparison map along a trajectory -/

section Comparison

variable (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφr : ∀ y ∈ φr.toChart.source,
    φr.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φr.toChart y (X y)) =
      fun i ↦ -(φr.weight i * φr.coord (φr.toChart y) i))
include hφp hφr

/-- **The kernel of the comparison map is the tangent space of the level slice.** At a point `y`
of a trajectory from `p` to `r`, the unstable frame carries a vector `v` to a vector tangent to
`W^u(p) ∩ W^s(r)` and to the level of `f` through `y` exactly when the comparison map vanishes
on `v`. -/
theorem mem_ker_trajectoryComparison_iff (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {y : M} (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r)
    (v : {i // φp.weight i < 0} → ℝ) :
    v ∈ LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap ↔
      hX.unstableFrame φp y v ∈ Submodule.span ℝ
          (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet p ∩ hX.flow.stableSet r) y) ∧
        mvfderiv 𝓘(ℝ, E) f y (hX.unstableFrame φp y v) = 0 := by
  have hu : hX.unstableFrame φp y v ∈
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet p) y) :=
    (Set.ext_iff.1 (hX.range_unstableFrame hφp hf hy.1) _).1 ⟨v, rfl⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, trajectoryComparison_apply, Prod.mk_eq_zero,
    hX.span_mtangentConeAt_unstableSet_inter_stableSet hf hy
      (hMS.span_mtangentConeAt_sup_eq_top hy)]
  exact ⟨fun h ↦ ⟨⟨hu, (stableNormal_eq_zero_iff hφr hy.2 _).1 h.2⟩, h.1⟩,
    fun h ↦ ⟨h.2, (stableNormal_eq_zero_iff hφr hy.2 _).2 h.1.2⟩⟩

end Comparison

/-- **The dimension of the kernel of the comparison map.** Where the comparison map is onto, as
along every trajectory from `p` to `r ≠ p` of a Morse–Smale pseudo-gradient
(`TauCeti.IsAdaptedPseudoGradient.surjective_trajectoryComparison`), its kernel, the tangent space
of the level slice of the trajectories, has dimension `ind p - ind r - 1`. -/
theorem finrank_ker_trajectoryComparison_add {y : M}
    (hC : Surjective (hX.trajectoryComparison φp φr y)) :
    Module.finrank ℝ (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap) +
      (1 + manifoldMorseIndex 𝓘(ℝ, E) f r) = manifoldMorseIndex 𝓘(ℝ, E) f p := by
  have h := LinearMap.finrank_range_add_finrank_ker (hX.trajectoryComparison φp φr y).toLinearMap
  rw [LinearMap.range_eq_top.2 hC, finrank_top, φr.finrank_prod_negativeWeight_fun,
    φp.finrank_negativeWeight_fun] at h
  omega

/-! ### The orientation of the space of trajectories -/

section Orientation

variable {y : M} {k : ℕ}

/-- **The dimension of the space of trajectories.** Where the comparison map is onto, its kernel
has dimension `k` when `ind p = k + (1 + ind r)`. This is the dimension at which
`TauCeti.IsAdaptedPseudoGradient.trajectorySpaceOrientation` orients the kernel. -/
theorem finrank_ker_trajectoryComparison (hC : Surjective (hX.trajectoryComparison φp φr y))
    (hk : manifoldMorseIndex 𝓘(ℝ, E) f p = k + (1 + manifoldMorseIndex 𝓘(ℝ, E) f r)) :
    Module.finrank ℝ (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap) = k := by
  have := finrank_ker_trajectoryComparison_add hC
  omega

variable (hX φp φr)

/-- The **orientation of the space of trajectories** from `p` to `r` at a point `y` of a
trajectory, read on the level of `f` through `y`: the orientation of the kernel of the comparison
map `C : Vp → ℝ × Vr` induced, subspace first, by the orientation `op` of `Vp` and the orientation
of `ℝ × Vr` given by the standard orientation of `ℝ` followed by `or`
(`TauCeti.MorseChart.flowNormalOrientation`). This is the convention
`T W^u(p) = T 𝓜(p, r) ⊕ ℝ (-X) ⊕ T W^u(r)`. It is defined when `C` is onto, which holds along
every trajectory between distinct critical points of a Morse–Smale pseudo-gradient
(`TauCeti.IsAdaptedPseudoGradient.surjective_trajectoryComparison`), and `k` is the dimension
`ind p - ind r - 1` of the trajectory space. -/
noncomputable def trajectorySpaceOrientation
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (or : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f r)))
    (hk : manifoldMorseIndex 𝓘(ℝ, E) f p = k + (1 + manifoldMorseIndex 𝓘(ℝ, E) f r)) (y : M)
    (hC : Surjective (hX.trajectoryComparison φp φr y)) :
    Orientation ℝ (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap) (Fin k) :=
  Orientation.shortExactLeft
    (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap).subtype_injective
    (LinearMap.exact_subtype_ker_map _) hC (finrank_ker_trajectoryComparison hC hk)
    φr.finrank_prod_negativeWeight_fun
    (Orientation.reindex ℝ _ (finCongr hk) op) (φr.flowNormalOrientation or)

/-- The defining formula of `TauCeti.IsAdaptedPseudoGradient.trajectorySpaceOrientation`. -/
theorem trajectorySpaceOrientation_def
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (or : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f r)))
    (hk : manifoldMorseIndex 𝓘(ℝ, E) f p = k + (1 + manifoldMorseIndex 𝓘(ℝ, E) f r)) (y : M)
    (hC : Surjective (hX.trajectoryComparison φp φr y)) :
    hX.trajectorySpaceOrientation φp φr op or hk y hC =
      Orientation.shortExactLeft
        (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap).subtype_injective
        (LinearMap.exact_subtype_ker_map _) hC (finrank_ker_trajectoryComparison hC hk)
        φr.finrank_prod_negativeWeight_fun
        (Orientation.reindex ℝ _ (finCongr hk) op) (φr.flowNormalOrientation or) :=
  (rfl)

variable {hX φp φr}

variable {op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))}
  {or : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f r))}
  {hk : manifoldMorseIndex 𝓘(ℝ, E) f p = k + (1 + manifoldMorseIndex 𝓘(ℝ, E) f r)}

/-- The orientation of the space of trajectories, followed by the standard orientation of `ℝ` and
`or`, induces `op` on `Vp`. -/
@[simp]
theorem shortExact_trajectorySpaceOrientation
    (hC : Surjective (hX.trajectoryComparison φp φr y))
    (ha : Module.finrank ℝ (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap) = k)
    (hc : Module.finrank ℝ (ℝ × ({i // φr.weight i < 0} → ℝ)) =
      1 + manifoldMorseIndex 𝓘(ℝ, E) f r) :
    Orientation.shortExact
        (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap).subtype_injective
        (LinearMap.exact_subtype_ker_map _) hC
        (hX.trajectorySpaceOrientation φp φr op or hk y hC) (φr.flowNormalOrientation or)
        ha hc = Orientation.reindex ℝ _ (finCongr hk) op :=
  Orientation.shortExact_shortExactLeft _ _ _ _ _ _ _

/-- **The characterization of the orientation of the space of trajectories**: it is the unique
orientation of the kernel of the comparison map which, followed by the standard orientation of
`ℝ` and `or`, induces `op`. -/
theorem trajectorySpaceOrientation_eq_iff (hC : Surjective (hX.trajectoryComparison φp φr y))
    (ha : Module.finrank ℝ (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap) = k)
    (hc : Module.finrank ℝ (ℝ × ({i // φr.weight i < 0} → ℝ)) =
      1 + manifoldMorseIndex 𝓘(ℝ, E) f r)
    (o : Orientation ℝ (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap) (Fin k)) :
    hX.trajectorySpaceOrientation φp φr op or hk y hC = o ↔
      Orientation.shortExact
        (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap).subtype_injective
          (LinearMap.exact_subtype_ker_map _) hC o (φr.flowNormalOrientation or)
          ha hc = Orientation.reindex ℝ _ (finCongr hk) op :=
  Orientation.shortExactLeft_eq_iff _ _ _ _ _ _ _ _

/-- **The positive bases of the space of trajectories.** Let `b` be a basis of the kernel of the
comparison map `C`, `e` a basis of `Vr`, and `B` a basis of `Vp` made of `b` followed by lifts along
`C` of `(1, 0)` and of the vectors `(0, e j)`. Then `b` is positive for the orientation of the
space of trajectories defined by `op` and the orientation of `e` exactly when `B` is positive for
`op`. -/
theorem trajectorySpaceOrientation_eq_orientation_iff
    (hC : Surjective (hX.trajectoryComparison φp φr y))
    (b : Module.Basis (Fin k) ℝ (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap))
    (e : Module.Basis (Fin (manifoldMorseIndex 𝓘(ℝ, E) f r)) ℝ ({i // φr.weight i < 0} → ℝ))
    (B : Module.Basis (Fin (k + (1 + manifoldMorseIndex 𝓘(ℝ, E) f r))) ℝ
      ({i // φp.weight i < 0} → ℝ))
    (hB₁ : ∀ i, B (Fin.castAdd _ i) = b i)
    (hB₂ : ∀ j, hX.trajectoryComparison φp φr y (B (Fin.natAdd k j)) =
      (((Module.Basis.singleton (Fin 1) ℝ).prod e).reindex finSumFinEquiv) j) :
    hX.trajectorySpaceOrientation φp φr op e.orientation hk y hC = b.orientation ↔
      B.orientation = Orientation.reindex ℝ _ (finCongr hk) op := by
  rw [trajectorySpaceOrientation_eq_iff hC (finrank_ker_trajectoryComparison hC hk)
      φr.finrank_prod_negativeWeight_fun,
    MorseChart.flowNormalOrientation_def,
    Orientation.prod_basis_orientation,
    Orientation.shortExact_basis_orientation _ _ _ _ _ b _ B hB₁ hB₂]

/-- **Reversing the orientation at the source reverses the orientation of the space of
trajectories.** -/
@[simp]
theorem trajectorySpaceOrientation_neg_left (hC : Surjective (hX.trajectoryComparison φp φr y)) :
    hX.trajectorySpaceOrientation φp φr (-op) or hk y hC =
      -hX.trajectorySpaceOrientation φp φr op or hk y hC := by
  rw [trajectorySpaceOrientation_def, trajectorySpaceOrientation_def, Orientation.reindex_neg,
    Orientation.shortExactLeft_neg_left]

/-- **Reversing the orientation at the target reverses the orientation of the space of
trajectories.** -/
@[simp]
theorem trajectorySpaceOrientation_neg_right (hC : Surjective (hX.trajectoryComparison φp φr y)) :
    hX.trajectorySpaceOrientation φp φr op (-or) hk y hC =
      -hX.trajectorySpaceOrientation φp φr op or hk y hC := by
  rw [trajectorySpaceOrientation_def, trajectorySpaceOrientation_def,
    MorseChart.flowNormalOrientation_neg, Orientation.shortExactLeft_neg_right]

end Orientation

/-! ### Changing the Morse charts -/

section ChartChange

variable {φp' : MorseChart E f p} {φr' : MorseChart E f r} {y : M} {k : ℕ}
  (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφp' : ∀ y ∈ φp'.toChart.source,
    φp'.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp'.toChart y (X y)) =
      fun i ↦ -(φp'.weight i * φp'.coord (φp'.toChart y) i))
  (hφr : ∀ y ∈ φr.toChart.source,
    φr.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φr.toChart y (X y)) =
      fun i ↦ -(φr.weight i * φr.coord (φr.toChart y) i))
  (hφr' : ∀ y ∈ φr'.toChart.source,
    φr'.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φr'.toChart y (X y)) =
      fun i ↦ -(φr'.weight i * φr'.coord (φr'.toChart y) i))
include hφp hφp' hφr hφr'

/-- **The kernel of the comparison map in other Morse charts.** On a trajectory from `p` to `r`,
the change of negative coordinates at `p` carries the kernel of the comparison map in the charts
`φp`, `φr` onto the kernel of the comparison map in the charts `φp'`, `φr'`. -/
theorem map_ker_trajectoryComparison_negativeChange (hf : IsMorse 𝓘(ℝ, E) f)
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r) :
    (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap).map
        (φp.negativeChange φp' : ({i // φp.weight i < 0} → ℝ) →ₗ[ℝ] {i // φp'.weight i < 0} → ℝ) =
      LinearMap.ker (hX.trajectoryComparison φp' φr' y).toLinearMap := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext v
  obtain ⟨w, rfl⟩ := (φp.negativeChange φp').surjective v
  simp [-trajectoryComparison_apply, trajectoryComparison_negativeChange hφp hφp' hφr hφr' hf hy,
    Prod.ext_iff]

/-- **The orientation of the space of trajectories does not depend on the Morse charts.** On a
trajectory from `p` to `r`, replacing the Morse charts `φp` and `φr` by `φp'` and `φr'` and
transporting `op` and `or` along the changes of negative coordinates transports the orientation of
the space of trajectories along the isomorphism of the kernels of the comparison maps induced by
the change of negative coordinates at `p`. -/
theorem trajectorySpaceOrientation_map_negativeChange (hf : IsMorse 𝓘(ℝ, E) f)
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (or : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f r)))
    (hk : manifoldMorseIndex 𝓘(ℝ, E) f p = k + (1 + manifoldMorseIndex 𝓘(ℝ, E) f r))
    (hC : Surjective (hX.trajectoryComparison φp φr y))
    (hC' : Surjective (hX.trajectoryComparison φp' φr' y)) :
    hX.trajectorySpaceOrientation φp' φr' (Orientation.map _ (φp.negativeChange φp') op)
        (Orientation.map _ (φr.negativeChange φr') or) hk y hC' =
      Orientation.map _ ((φp.negativeChange φp').ofSubmodules _ _
          (map_ker_trajectoryComparison_negativeChange hφp hφp' hφr hφr' hf hy))
        (hX.trajectorySpaceOrientation φp φr op or hk y hC) := by
  have hK := map_ker_trajectoryComparison_negativeChange hφp hφp' hφr hφr' hf hy
  set eK := (φp.negativeChange φp').ofSubmodules _ _ hK
  rw [trajectorySpaceOrientation_eq_iff hC' (finrank_ker_trajectoryComparison hC' hk)
      φr'.finrank_prod_negativeWeight_fun,
    MorseChart.flowNormalOrientation_map,
    ← Orientation.map_shortExact
      (LinearMap.ker (hX.trajectoryComparison φp φr y).toLinearMap).subtype_injective
      (LinearMap.exact_subtype_ker_map _) hC (finrank_ker_trajectoryComparison hC hk)
      φr.finrank_prod_negativeWeight_fun _ _ _ eK
      (φp.negativeChange φp') ((LinearEquiv.refl ℝ ℝ).prodCongr (φr.negativeChange φr'))
      (LinearMap.ext fun v ↦ (LinearEquiv.ofSubmodules_apply _ hK v).symm)
      (LinearMap.ext fun v ↦ trajectoryComparison_negativeChange hφp hφp' hφr hφr' hf hy v),
    shortExact_trajectorySpaceOrientation, Orientation.map_reindex]

end ChartChange

end IsAdaptedPseudoGradient

end TauCeti
