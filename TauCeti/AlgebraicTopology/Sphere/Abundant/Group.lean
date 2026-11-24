/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Aspherical
public import TauCeti.AlgebraicTopology.Sphere.Abundant.Basic
public import TauCeti.Topology.MappingSpace.Group
public import TauCeti.Topology.MappingSpace.Sphere.Basic
public import Mathlib.Analysis.Quaternion
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
import TauCeti.AlgebraicTopology.Sphere.Abundant.Action
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.Topology.MappingSpace.Sphere.PathComponent

/-!
# Topological groups abundant with two-spheres

Let `G` be a compact oriented `n`-manifold which is a topological group, such as a compact
connected Lie group. Maps of the sphere into `G` split off their value at the north pole: the
homeomorphism `G × Map_*(S², G) ≃ₜ Map(S², G)`, `(g, f) ↦ g · f`
(`TauCeti.mappingSpaceGroupHomeomorph`), lies over `G`, where `Map_*(S², G)` consists of the maps
sending the north pole to `1`, a model of `Ω²G`. Barraud, Damian, Humilière and Oancea observe
(their Example 6.30) that for every nonzero class `α` of the reduced homology of `Ω²G`, the image
of the cross product `[G] × α` under this homeomorphism witnesses that `G` is abundant with
2-spheres.

This file proves this. For a class of positive degree
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_ne_zero`), the cross product
`[G] × α` lives over the fundamental class of `G` for the projection `G × Ω²G → G`
(`HomologicalOrientation.livesOverFundamentalClass_singularHomologyCross_fundamentalClass_iff`),
its coefficients `ℤ ⊗ ℤ` are identified with `ℤ`
(`TauCeti.livesOverFundamentalClass_homologyMap_coefficient_iff`), and it is carried to
`Map(S², G)` by a homeomorphism over `G`
(`TauCeti.livesOverFundamentalClass_homologyMap_iff_of_comp_eq_id`). Its degree is `n + deg α`,
above the dimension. This homeomorphism is the action map of `G` acting on itself, so the image of
`[G] × α` is the class `TauCeti.BasedMap.actionClass` of that action.

In degree zero (`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_homologyMap_const_ne`)
the reduced homology `H₀(Ω²G, pt)` is the quotient of `H₀(Ω²G)` by the multiples of the class of
the base point `1`, so the hypothesis on `α` is that it is not fixed by the map `c_*` induced by
the constant self-map `c` of `Map_*(S², G)` at the constant sphere `1`. The class `[G] × α` then has
degree `n`, and the second condition of Definition 6.11 asks that its localization at the fibre
over `b` is not that of a class of constant spheres. The self-map `f ↦ const (f(north))` of
`Map(S², G)` lies over `G`, so it preserves localizations, and it fixes the constant spheres. If
the localization of `[G] × α` came from the constant spheres, it would therefore agree with that
of the image of `[G] × α`, which is `[G] × c_* α` because under `G × Map_*(S², G) ≃ₜ Map(S², G)`
this self-map is the identity times `c`. Then `[G] × (α - c_* α)` would not live over the
fundamental class, contradicting `α - c_* α ≠ 0`
(`TauCeti.isAbundantWithTwoSpheres_of_livesOverFundamentalClass_sub`).

By Lemma 3.41 of the source (`TauCeti.isAspherical_iff_doubleLoopSpace_singularHomology`), a
path-connected space is aspherical exactly when its double loop space is path connected with
vanishing positive-degree integral homology. So if `G` is path-connected and not aspherical, then
either `π₂(G)` is nontrivial, in which case `Ω²G` is not path connected and the class of a point
outside the path component of the constant sphere is a class of degree zero as above, or `Ω²G` has
a nonzero class of positive degree. Either way `G` is abundant with 2-spheres
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_not_isAspherical`). No hypothesis on
`π₂(G)` is needed; for compact connected Lie groups `π₂` vanishes anyway, by a classical theorem
of Cartan, but that theorem is not used.

The unit quaternions `S³ = SU(2)` are simply connected, hence orientable, with `π₃(S³) ≅ ℤ`, so
they are not aspherical and are abundant with 2-spheres
(`TauCeti.isAbundantWithTwoSpheres_sphere_quaternion`).

## Main results

* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_ne_zero`: a nonzero class of
  positive degree of `Ω²G` makes `G` abundant with 2-spheres.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_homologyMap_const_ne`: so does a
  class of degree zero which is not a multiple of the class of the constant sphere `1` (the base
  point).
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_not_isAspherical`: a
  path-connected `G` which is not aspherical is abundant with 2-spheres.
* `TauCeti.isAbundantWithTwoSpheres_sphere_quaternion`: the unit quaternions `S³` are abundant
  with 2-spheres.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 6.11, Lemma 3.41,
  Example 6.30 and Proposition 6.31.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory TensorProduct Metric Module
open scoped Topology Quaternion

namespace TauCeti

namespace HomologicalOrientation

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {n : ℕ}
  {G : Type} [TopologicalSpace G] [T2Space G] [CompactSpace G] [ChartedSpace V G] [Group G]
  [IsTopologicalGroup G] (o : HomologicalOrientation G V n) (hn : Module.finrank ℝ V = n)

/-- The class `[G] × α` of `Map(S², G)`, the class `TauCeti.BasedMap.actionClass` of `G` acting on
itself with `A = [G]`, lives over the fundamental class of `G`, for evaluation at the north pole,
exactly when `α ≠ 0`. -/
private theorem livesOverFundamentalClass_actionClass_iff (b : G) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)} :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north) b
      (BasedMap.actionClass Sphere2.north (1 : G) (o.fundamentalClass hn) α) ↔ α ≠ 0 := by
  let Ψ := mappingSpaceGroupHomeomorph (G := G) Sphere2.north
  let Φ : C(G × BasedMap Sphere2 G Sphere2.north 1, C(Sphere2, G)) :=
    BasedMap.actionMap Sphere2.north 1
  -- The action map of `G` on itself is the homeomorphism `(g, f) ↦ g · f`.
  have hτ : (Ψ.symm : C(C(Sphere2, G), G × BasedMap Sphere2 G Sphere2.north 1)).comp Φ =
      ContinuousMap.id _ := by
    have hΦ : Φ = Ψ := by
      ext p s
      simp [Φ, Ψ, mappingSpaceGroupHomeomorph_apply]
    rw [hΦ]
    exact Ψ.symm_comp_toContinuousMap
  have h : mappingSpaceEval Sphere2.north ∘ Φ = id ∘ Prod.fst := funext fun x ↦ by
    simp [Φ, x.2.property]
  have h' : (id ∘ Prod.fst) ∘ Ψ.symm = mappingSpaceEval Sphere2.north := funext fun f ↦ by
    simp [Ψ]
  -- Carry the class back along the homeomorphism over `G`, identify the coefficients `ℤ ⊗ ℤ`
  -- with `ℤ`, and use that the cross product with `[G]` is injective.
  rw [BasedMap.actionClass_def]
  refine (livesOverFundamentalClass_homologyMap_iff_of_comp_eq_id (ModuleCat.of ℤ (ULift.{0} ℤ))
    Φ (Ψ.symm : C(C(Sphere2, G), G × BasedMap Sphere2 G Sphere2.north 1)) hτ h h'
      (b := b)).trans ?_
  exact (livesOverFundamentalClass_homologyMap_coefficient_iff _
    (ModuleCat.uliftTensorSelfIso ℤ)).trans
      (o.livesOverFundamentalClass_singularHomologyCross_fundamentalClass_iff hn b rfl)

include o hn in
/-- **A topological group with a nonzero class of positive degree in its double loop space is
abundant with 2-spheres** (Barraud–Damian–Humilière–Oancea, Example 6.30). Let `G` be a compact
oriented `n`-manifold which is a topological group, and let `α` be a nonzero class of positive
degree `k` of the based mapping space `Map_*(S², G)` of maps sending the north pole to `1`, a
model of `Ω²G`. Then the image of `[G] × α` under `G × Map_*(S², G) ≃ₜ Map(S², G)` lives over the
fundamental class of `G` at every point `b`, so `G` is abundant with 2-spheres at `b`. -/
theorem isAbundantWithTwoSpheres_of_ne_zero (b : G) {k : ℕ} (hk : 0 < k)
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)} (hα : α ≠ 0) :
    IsAbundantWithTwoSpheres G n b :=
  isAbundantWithTwoSpheres_of_lt ((o.livesOverFundamentalClass_actionClass_iff hn b).2 hα)
    (by omega)

include o hn in
/-- **A topological group with a class of degree zero in its double loop space that is not a
multiple of the class of the base point is abundant with 2-spheres**
(Barraud–Damian–Humilière–Oancea, Example 6.30). Let `G` be a compact oriented `n`-manifold which
is a topological group, and let `α ∈ H₀(Map_*(S², G); ℤ)` be a class of the based mapping space of
maps sending the north pole to `1`, a model of `Ω²G`, which is not fixed by the map `c_*` induced
by the constant self-map at the constant sphere `1`; equivalently, `α` is not a multiple of the
class of the constant sphere `1` (the base point), that is, it is nonzero in `H₀(Ω²G, pt)`. Then
the image of `[G] × α` under `G × Map_*(S², G) ≃ₜ Map(S², G)` lives over the fundamental class of
`G` at every point `b` and its localization is not that of a class of constant spheres, so `G` is
abundant with 2-spheres at `b`. -/
theorem isAbundantWithTwoSpheres_of_homologyMap_const_ne (b : G)
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 0 : ModuleCat.{0} ℤ)}
    (hα : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
      (ContinuousMap.const (BasedMap Sphere2 G Sphere2.north 1) ⟨1, ContinuousMap.one_apply _⟩)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) 0).hom α ≠ α) :
    IsAbundantWithTwoSpheres G n b := by
  refine isAbundantWithTwoSpheres_of_livesOverFundamentalClass_sub
    (α := BasedMap.actionClass Sphere2.north (1 : G) (o.fundamentalClass hn) α)
    ((o.livesOverFundamentalClass_actionClass_iff hn b).2 fun h ↦ hα (by rw [h, map_zero])) ?_
  -- The self-map `f ↦ const (f(north))` sends `[G] × α` to `[G] × c_* α`, and `α - c_* α ≠ 0`.
  have h := (o.livesOverFundamentalClass_actionClass_iff hn b).2 (sub_ne_zero.2 hα.symm)
  rwa [BasedMap.actionClass_sub,
    ← BasedMap.homologyMap_const'_comp_mappingSpaceEval_actionClass] at h

include o hn in
/-- **A non-aspherical topological group is abundant with 2-spheres**
(Barraud–Damian–Humilière–Oancea, Example 6.30). Let `G` be a path-connected compact oriented
`n`-manifold which is a topological group, for instance a compact connected Lie group. If `G` is
not aspherical, then `G` is abundant with 2-spheres at every point. -/
theorem isAbundantWithTwoSpheres_of_not_isAspherical [PathConnectedSpace G] (b : G)
    (hG : ¬IsAspherical G 1) : IsAbundantWithTwoSpheres G n b := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let Y := BasedMap Sphere2 G Sphere2.north 1
  let y₀ : Y := ⟨1, ContinuousMap.one_apply _⟩
  by_cases h₂ : Subsingleton (π_ 2 G 1)
  · -- By Lemma 3.41 of the source the double loop space of `G` has a nonzero integral homology
    -- class of positive degree, to which `isAbundantWithTwoSpheres_of_ne_zero` applies.
    rw [isAspherical_iff_doubleLoopSpace_singularHomology] at hG
    push Not at hG
    obtain ⟨m, hm₀, hm⟩ := hG ((pathConnectedSpace_doubleLoopSpace_iff (1 : G)).2 h₂)
    -- Transport the nonzero homology group of `Ω (Ω G 1) (Path.refl 1)` to `Map_*(S², G)`, with
    -- coefficients `ULift ℤ`.
    have hY : ¬IsZero ((TopCat.toSSet.obj (TopCat.of Y)).homology R m) := fun h ↦
      hm (h.of_iso (doubleLoopSpaceHomologyIsoBasedMap (1 : G) m))
    rw [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial] at hY
    obtain ⟨α, hα⟩ := exists_ne (0 : ((TopCat.toSSet.obj (TopCat.of Y)).homology R m :
      ModuleCat ℤ))
    exact o.isAbundantWithTwoSpheres_of_ne_zero hn b (Nat.pos_of_ne_zero hm₀) hα
  · -- `π₂(G) ≠ 0`, so `Map_*(S², G) ≃ₜ Ω²G` has a point `y₁` not joined to the constant
    -- sphere `1`, and the class of `y₁` is not fixed by the constant self-map at `1`.
    have := not_subsingleton_iff_nontrivial.1 h₂
    obtain ⟨y₁, hy₁⟩ := exists_not_joined_of_nontrivial_homotopyGroup 2 (1 : G) Sphere2.north y₀
    have hr : (ULift.up 1 : R) ≠ 0 := fun h ↦ one_ne_zero (congrArg ULift.down h)
    refine o.isAbundantWithTwoSpheres_of_homologyMap_const_ne hn b
      (α := (singularHomology₀Section R (X := TopCat.of Y) y₁).hom (ULift.up 1)) ?_
    -- `c_* [y₁] = [c y₁] = [1]`, so the hypothesis says that `[1] = [y₁]`.
    rw [homologyMap_singularHomology₀Section_apply]
    simp only [TopCat.hom_ofHom, ContinuousMap.const_apply]
    exact fun h ↦ hy₁ ((singularHomology₀Section_apply_eq_iff hr).1 h.symm)

end HomologicalOrientation

/-- **The unit quaternions are abundant with 2-spheres.** The sphere `S³ ⊆ ℍ`, the group `SU(2)`,
is a compact simply connected `3`-manifold and a topological group with `π₃(S³) ≠ 0`, so it is
not aspherical and is abundant with 2-spheres at every point. -/
theorem isAbundantWithTwoSpheres_sphere_quaternion (b : sphere (0 : ℍ) 1) :
    IsAbundantWithTwoSpheres (sphere (0 : ℍ) 1) 3 b := by
  have : Fact (finrank ℝ ℍ = 3 + 1) := ⟨Quaternion.finrank_eq_four⟩
  have hrank : 2 < Module.rank ℝ ℍ := by
    rw [← Module.finrank_eq_rank, Quaternion.finrank_eq_four]
    norm_num
  have : SimplyConnectedSpace (sphere (0 : ℍ) 1) := simplyConnectedSpace_sphere hrank 0 zero_le_one
  -- A simply connected manifold is orientable.
  obtain ⟨o⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace
    (M := sphere (0 : ℍ) 1) (finrank_euclideanSpace_fin (n := 3))
  refine o.isAbundantWithTwoSpheres_of_not_isAspherical (finrank_euclideanSpace_fin (n := 3)) b
    fun h ↦ ?_
  -- `π₃(S³)` is nontrivial, so `S³` is not aspherical.
  have := nontrivial_homotopyGroup_sphere (n := 1) Quaternion.finrank_eq_four
    (1 : sphere (0 : ℍ) 1)
  exact not_subsingleton _ ((isAspherical_iff.1 h).2 1)

end TauCeti
