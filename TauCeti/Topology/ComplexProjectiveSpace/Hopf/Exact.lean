/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.SerreFibration.Exact
import TauCeti.AlgebraicTopology.NotSimplyConnected
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy
import TauCeti.Analysis.Complex.Circle
import TauCeti.Topology.Homotopy.HomotopyGroup.Basic

/-!
# The exact homotopy sequence of the Hopf fibration `S¹ → S²ⁿ⁺¹ → CPⁿ`

The Hopf fibration `S²ⁿ⁺¹ → CPⁿ`, `v ↦ [v]`, is a Serre fibration whose fibre over `[v]` is the
unit circle, through `u ↦ u • v` (`TauCeti.ComplexProjectiveSpace.mk_mem_serreFibrations`,
`TauCeti.ComplexProjectiveSpace.hopfFiberHomeomorph`). Since the circle is path connected and
has no homotopy groups above degree one, its exact homotopy sequence gives:

* for `k ≥ 3`, the projection induces isomorphisms `π_k(S²ⁿ⁺¹) ≅ π_k(CPⁿ)`
  (`TauCeti.ComplexProjectiveSpace.homotopyGroupMulEquiv`);
* `CPⁿ` is simply connected (`TauCeti.ComplexProjectiveSpace.simplyConnectedSpace`);
* for `n ≥ 1`, the boundary map `π₂(CPⁿ) → π₁(S¹)` is an isomorphism
  (`TauCeti.ComplexProjectiveSpace.hopfBoundaryMulEquiv`). More generally, for `1 ≤ k < 2n` the
  boundary `π_{k+1}(CPⁿ) → π_k(S¹)` is bijective, so `π_k(CPⁿ)` vanishes for `3 ≤ k ≤ 2n`.

For `n ≥ 1` the last two use that `S²ⁿ⁺¹` is `2n`-connected
(`TauCeti.subsingleton_homotopyGroup_sphere_of_lt`).

Homotopy groups are indexed as in `TauCeti.TopCat.fibrationBoundary`: `π_k` is modelled on the
cube `I^N` for a finite type `N` of cardinality `k`, and `π_{k+1}` on `I^(Option N)`. All groups
are based at a unit vector `v` and at its class `[v]`; in the circle the base point is `1`.

## Main definitions

* `TauCeti.ComplexProjectiveSpace.hopfBoundary`: the boundary map `π_{k+1}(CPⁿ, [v]) → π_k(S¹, 1)`.
* `TauCeti.ComplexProjectiveSpace.homotopyGroupMulEquiv`: for `k ≥ 3`, the isomorphism
  `π_k(S²ⁿ⁺¹, v) ≃* π_k(CPⁿ, [v])` induced by the projection.
* `TauCeti.ComplexProjectiveSpace.hopfBoundaryMulEquiv`: for `1 ≤ k < 2n`, the boundary map as an
  isomorphism `π_{k+1}(CPⁿ, [v]) ≃* π_k(S¹, 1)`.

## Main results

* `TauCeti.ComplexProjectiveSpace.bijective_homotopyGroupMap_mk`: for `k ≥ 3`, the projection
  induces a bijection `π_k(S²ⁿ⁺¹, v) → π_k(CPⁿ, [v])`.
* `TauCeti.ComplexProjectiveSpace.simplyConnectedSpace`: `CPⁿ` is simply connected.
* `TauCeti.ComplexProjectiveSpace.bijective_hopfBoundary`: for `1 ≤ k < 2n`, the boundary map is
  bijective.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 and Example 4.45.
-/

public section

noncomputable section

open CategoryTheory Metric Set
open scoped Topology.Homotopy

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} {N : Type*}

section Higher

variable (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)

/-- The unit vector `v`, as the base point of the fibre of the Hopf fibration over `[v]`. -/
private abbrev fiberPoint : (hopfHom n).fiber (mk n v) :=
  ⟨v, rfl⟩

/-- The fibre of the Hopf fibration over `[v]`, homeomorphic to the unit circle. -/
private def fiberHomeomorph : (hopfHom n).fiber (mk n v) ≃ₜ sphere (0 : ℂ) 1 :=
  (hopfFiberHomeomorph v).symm

private theorem fiberHomeomorph_fiberPoint : fiberHomeomorph v (fiberPoint v) = 1 :=
  (hopfFiberHomeomorph v).symm_apply_eq.2 (hopfFiberHomeomorph_one v).symm

/-- The higher homotopy groups of the fibre of the Hopf fibration vanish. -/
private instance subsingleton_homotopyGroup_fiber [Nontrivial N]
    (x : (hopfHom n).fiber (mk n v)) :
    Subsingleton (HomotopyGroup N ((hopfHom n).fiber (mk n v)) x) :=
  (HomotopyGroup.homeomorphEquiv (N := N)
    ((fiberHomeomorph v).trans Circle.homeomorphSphere.symm) x).subsingleton_congr.2 inferInstance

/-- The fibre of the Hopf fibration is path connected. -/
private instance pathConnectedSpace_fiber : PathConnectedSpace ((hopfHom n).fiber (mk n v)) :=
  ((fiberHomeomorph v).trans Circle.homeomorphSphere.symm).symm.surjective.pathConnectedSpace
    ((fiberHomeomorph v).trans Circle.homeomorphSphere.symm).symm.continuous

/-- The unit sphere `S²ⁿ⁺¹` of `ℂⁿ⁺¹` is `2n`-connected. -/
private theorem subsingleton_homotopyGroup_sphere [Finite N] (hN : Nat.card N < 2 * n + 1)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    Subsingleton (HomotopyGroup N (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) x) :=
  subsingleton_homotopyGroup_sphere_of_lt (by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]; ring) hN x

/-! ### Higher homotopy groups -/

/-- **`π_k(S²ⁿ⁺¹) ≅ π_k(CPⁿ)` for `k ≥ 3`.** The Hopf fibration induces a bijection on homotopy
groups modelled on `I^(Option N)` whenever `N` has at least two elements. -/
theorem bijective_homotopyGroupMap_mk [Finite N] [Nontrivial N] :
    Function.Bijective (HomotopyGroup.map (N := Option N) (x := v) ⟨mk n, continuous_mk n⟩ rfl) :=
  ⟨TopCat.injective_homotopyGroupMap_of_subsingleton (mk_mem_serreFibrations n)
      (e := fiberPoint v),
    TopCat.surjective_homotopyGroupMap_of_subsingleton (mk_mem_serreFibrations n)
      (e := fiberPoint v)⟩

/-- For `k ≥ 3`, the isomorphism `π_k(S²ⁿ⁺¹, v) ≃* π_k(CPⁿ, [v])` induced by the Hopf fibration,
with `π_k` modelled on `I^(Option N)` for a type `N` with at least two elements. -/
def homotopyGroupMulEquiv [Finite N] [Nontrivial N] [DecidableEq N] :
    HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v ≃*
      HomotopyGroup (Option N) (ComplexProjectiveSpace n) (mk n v) :=
  MulEquiv.ofBijective (HomotopyGroup.mapHom ⟨mk n, continuous_mk n⟩ rfl)
    (bijective_homotopyGroupMap_mk v)

@[simp]
theorem homotopyGroupMulEquiv_apply [Finite N] [Nontrivial N] [DecidableEq N]
    (a : HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v) :
    homotopyGroupMulEquiv v a = HomotopyGroup.map ⟨mk n, continuous_mk n⟩ rfl a :=
  (rfl)

end Higher

/-! ### Simple connectivity -/

/-- **`CPⁿ` is simply connected.** For `n ≥ 1`, every loop lifts, up to homotopy, to the simply
connected sphere `S²ⁿ⁺¹`, because the fibre of the Hopf fibration is path connected; `CP⁰` is a
point. -/
instance simplyConnectedSpace : SimplyConnectedSpace (ComplexProjectiveSpace n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · infer_instance
  refine simplyConnectedSpace_iff_forall_subsingleton_fundamentalGroup.2
    ⟨inferInstance, fun p ↦ ?_⟩
  obtain ⟨w, rfl⟩ := mk_surjective n p
  have : Subsingleton (HomotopyGroup (Fin 0) ((hopfHom n).fiber (mk n w)) (fiberPoint w)) :=
    (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero _).1 inferInstance
  have := subsingleton_homotopyGroup_sphere (N := Option (Fin 0)) (by simp; omega) w
  have hsurj := TopCat.surjective_homotopyGroupMap_of_subsingleton (N := Fin 0)
    (mk_mem_serreFibrations n) (e := fiberPoint w)
  exact (homotopyGroupEquivFundamentalGroupOfUnique (Option (Fin 0))).subsingleton_congr.1
    hsurj.subsingleton

/-! ### The boundary map -/

variable (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)

/-- The identification of the homotopy groups of the fibre of the Hopf fibration over `[v]`,
based at `v`, with those of the unit circle, based at `1`. -/
private def fiberEquiv (N : Type*) :
    HomotopyGroup N ((hopfHom n).fiber (mk n v)) (fiberPoint v) ≃
      HomotopyGroup N (sphere (0 : ℂ) 1) 1 :=
  HomotopyGroup.homeomorphEquivOfEq (fiberHomeomorph v) (fiberHomeomorph_fiberPoint v)

private theorem fiberEquiv_mk_const :
    fiberEquiv v N ⟦GenLoop.const⟧ = (⟦GenLoop.const⟧ : HomotopyGroup N (sphere (0 : ℂ) 1) 1) :=
  congrArg _ (GenLoop.map_const _ _)

/-- The **boundary map** `π_{k+1}(CPⁿ, [v]) → π_k(S¹, 1)` of the Hopf fibration, where `k` is the
cardinality of `N`. It is the boundary map of the Serre fibration `S²ⁿ⁺¹ → CPⁿ`
(`TauCeti.TopCat.fibrationBoundary`), read in the circle through the identification
`u ↦ u • v` of the circle with the fibre over `[v]`. -/
def hopfBoundary (N : Type*) [Finite N] :
    HomotopyGroup (Option N) (ComplexProjectiveSpace n) (mk n v) →
      HomotopyGroup N (sphere (0 : ℂ) 1) 1 :=
  fiberEquiv v N ∘ TopCat.fibrationBoundary (mk_mem_serreFibrations n) (fiberPoint v)

variable [Finite N]

/-- For `k ≥ 1`, the boundary map of the Hopf fibration is multiplicative. -/
theorem hopfBoundary_mul [DecidableEq N] [Nonempty N]
    (a a' : HomotopyGroup (Option N) (ComplexProjectiveSpace n) (mk n v)) :
    hopfBoundary v N (a * a') = hopfBoundary v N a * hopfBoundary v N a' := by
  -- The group structures on the homotopy groups of `TopCat.of X` and of `X` agree only after
  -- unfolding `TopCat.of`, which `rw` does not do, so the multiplicativity of the boundary is
  -- applied with `erw`.
  simp only [hopfBoundary, Function.comp_apply]
  erw [TopCat.fibrationBoundary_mul]
  exact HomotopyGroup.map_mul _ _ _ _

/-- **Exactness at `π_{k+1}(CPⁿ)`.** A class of `π_{k+1}(CPⁿ, [v])` comes from `S²ⁿ⁺¹` exactly
when its boundary in `π_k(S¹)` is trivial. -/
theorem mem_range_homotopyGroupMap_mk_iff
    {a : HomotopyGroup (Option N) (ComplexProjectiveSpace n) (mk n v)} :
    a ∈ range (HomotopyGroup.map (x := v) ⟨mk n, continuous_mk n⟩ rfl) ↔
      hopfBoundary v N a = (⟦GenLoop.const⟧ : HomotopyGroup N (sphere (0 : ℂ) 1) 1) :=
  (TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq _).trans
    ((fiberEquiv v N).injective.eq_iff' (fiberEquiv_mk_const v)).symm

/-- **The boundary map `π_{k+1}(CPⁿ) → π_k(S¹)` is bijective for `1 ≤ k < 2n`.** In particular
`π₂(CPⁿ) ≅ π₁(S¹)` for `n ≥ 1`. -/
theorem bijective_hopfBoundary [Nonempty N] (hN : Nat.card N < 2 * n) :
    Function.Bijective (hopfBoundary v N) := by
  classical
  have hp := mk_mem_serreFibrations n
  refine ⟨?_, fun c ↦ ?_⟩
  · -- The kernel of the boundary is the image of `π_{k+1}(S²ⁿ⁺¹)`, which is trivial.
    have := subsingleton_homotopyGroup_sphere (N := Option N) (by simp; omega) v
    refine (injective_iff_map_eq_one (MonoidHom.mk' (hopfBoundary v N) (hopfBoundary_mul v))).2
      fun a ha ↦ ?_
    rw [MonoidHom.mk'_apply, _root_.HomotopyGroup.one_def] at ha
    obtain ⟨b, rfl⟩ := (mem_range_homotopyGroupMap_mk_iff v).2 ha
    rw [Subsingleton.elim b 1, HomotopyGroup.map_one]
  · -- Every class of the fibre dies in `π_k(S²ⁿ⁺¹)`, which is trivial, so it is a boundary.
    have := subsingleton_homotopyGroup_sphere (N := N) (by omega) v
    obtain ⟨a, ha⟩ := (TopCat.mem_range_fibrationBoundary_iff hp).2
      (Subsingleton.elim _ _ : HomotopyGroup.map _ _ ((fiberEquiv v N).symm c) = _)
    exact ⟨a, by rw [hopfBoundary, Function.comp_apply, ha, Equiv.apply_symm_apply]⟩

/-- For `1 ≤ k < 2n`, the boundary map of the Hopf fibration as an isomorphism
`π_{k+1}(CPⁿ, [v]) ≃* π_k(S¹, 1)`. For `k = 1` this is `π₂(CPⁿ) ≅ π₁(S¹)`. -/
def hopfBoundaryMulEquiv [DecidableEq N] [Nonempty N] (hN : Nat.card N < 2 * n) :
    HomotopyGroup (Option N) (ComplexProjectiveSpace n) (mk n v) ≃*
      HomotopyGroup N (sphere (0 : ℂ) 1) 1 :=
  MulEquiv.ofBijective (MonoidHom.mk' (hopfBoundary v N) (hopfBoundary_mul v))
    (bijective_hopfBoundary v hN)

@[simp]
theorem hopfBoundaryMulEquiv_apply [DecidableEq N] [Nonempty N] (hN : Nat.card N < 2 * n)
    (a : HomotopyGroup (Option N) (ComplexProjectiveSpace n) (mk n v)) :
    hopfBoundaryMulEquiv v hN a = hopfBoundary v N a :=
  (rfl)

/-- **`π_k(CPⁿ)` vanishes for `3 ≤ k ≤ 2n`**: the boundary identifies it with `π_{k-1}(S¹)`, which
is trivial. -/
theorem subsingleton_homotopyGroup [Nontrivial N] (hN : Nat.card N < 2 * n) :
    Subsingleton (HomotopyGroup (Option N) (ComplexProjectiveSpace n) (mk n v)) :=
  have : Subsingleton (HomotopyGroup N (sphere (0 : ℂ) 1) 1) :=
    (HomotopyGroup.homeomorphEquiv (N := N) Circle.homeomorphSphere.symm 1).subsingleton_congr.2
      inferInstance
  (bijective_hopfBoundary v hN).1.subsingleton

end TauCeti.ComplexProjectiveSpace
