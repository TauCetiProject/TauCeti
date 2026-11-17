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
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected

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

This file proves this for classes of positive degree
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_ne_zero`). The cross product
`[G] × α` lives over the fundamental class of `G` for the projection `G × Ω²G → G`
(`HomologicalOrientation.livesOverFundamentalClass_singularHomologyCross_fundamentalClass_iff`),
its coefficients `ℤ ⊗ ℤ` are identified with `ℤ`
(`TauCeti.livesOverFundamentalClass_homologyMap_coefficient_iff`), and it is carried to
`Map(S², G)` by a homeomorphism over `G`
(`TauCeti.livesOverFundamentalClass_homologyMap_iff_of_comp_eq_id`). Its degree is `n + deg α`,
above the dimension.

By Lemma 3.41 of the source (`TauCeti.isAspherical_iff_doubleLoopSpace_singularHomology`), a
path-connected space is aspherical exactly when its double loop space is path connected with
vanishing positive-degree integral homology. So if `π₂(G)` is trivial, which holds for compact Lie
groups by a classical theorem of Cartan, and `G` is not aspherical, then `Ω²G` has a nonzero class
of positive degree, and `G` is abundant with 2-spheres
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_not_isAspherical`). This applies to
every `G` meeting these hypotheses, for example to compact connected Lie groups which are not
tori: these have `π₂ = 0` by Cartan's theorem and are not aspherical.

The unit quaternions `S³ = SU(2)` are simply connected, hence orientable, with `π₂(S³) = 0` and
`π₃(S³) ≅ ℤ`, so they are abundant with 2-spheres
(`TauCeti.isAbundantWithTwoSpheres_sphere_quaternion`).

Classes of degree zero, which are nonzero in reduced homology only when `π₂(G)` is nontrivial,
are not treated here. For them the second condition of Definition 6.11 has to be checked, which
needs the comparison of the cross product with the class of a point and the inclusion of `G`.

## Main results

* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_ne_zero`: a nonzero class of
  positive degree of `Ω²G` makes `G` abundant with 2-spheres.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_not_isAspherical`: a
  path-connected `G` with `π₂(G) = 0` which is not aspherical is abundant with 2-spheres.
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
    IsAbundantWithTwoSpheres G n b := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let Ψ := mappingSpaceGroupHomeomorph (G := G) Sphere2.north
  -- The cross product `[G] × α`, with coefficients `ℤ ⊗ ℤ`, lives over the fundamental class.
  let x : ((TopCat.toSSet.obj (TopCat.of (G × BasedMap Sphere2 G Sphere2.north 1))).homology
      (R ⊗ R) (n + k) : ModuleCat ℤ) := (TopCat.singularHomologyCross (TopCat.of G)
    (TopCat.of (BasedMap Sphere2 G Sphere2.north 1)) R R n k (n + k) rfl).hom
      (o.fundamentalClass hn ⊗ₜ α)
  have hx : LivesOverFundamentalClass (R ⊗ R) (id ∘ Prod.fst) b x :=
    (o.livesOverFundamentalClass_singularHomologyCross_fundamentalClass_iff hn b rfl).2 hα
  -- Identify the coefficients `ℤ ⊗ ℤ` with `ℤ`.
  have hy := (livesOverFundamentalClass_homologyMap_coefficient_iff (R ⊗ R)
    (ModuleCat.uliftTensorSelfIso ℤ)).2 hx
  -- Carry the class to `Map(S², G)` along the homeomorphism over `G`.
  have hτ : (Ψ.symm : C(C(Sphere2, G), G × BasedMap Sphere2 G Sphere2.north 1)).comp Ψ =
      ContinuousMap.id _ :=
    Ψ.symm_comp_toContinuousMap
  have h : mappingSpaceEval Sphere2.north ∘ Ψ = id ∘ Prod.fst := funext fun x ↦ by
    simp [Ψ, x.2.2]
  have h' : (id ∘ Prod.fst) ∘ Ψ.symm = mappingSpaceEval Sphere2.north := funext fun f ↦ by
    simp [Ψ]
  have hz := (livesOverFundamentalClass_homologyMap_iff_of_comp_eq_id R
    (Ψ : C(G × BasedMap Sphere2 G Sphere2.north 1, C(Sphere2, G)))
    (Ψ.symm : C(C(Sphere2, G), G × BasedMap Sphere2 G Sphere2.north 1)) hτ h h' (b := b)).2 hy
  exact isAbundantWithTwoSpheres_of_lt hz (by omega)

include o hn in
/-- **A non-aspherical topological group with `π₂ = 0` is abundant with 2-spheres**
(Barraud–Damian–Humilière–Oancea, Example 6.30). Let `G` be a path-connected compact oriented
`n`-manifold which is a topological group with trivial `π₂(G)`, for instance a compact connected
Lie group. If `G` is not aspherical, then `G` is abundant with 2-spheres at every point. -/
theorem isAbundantWithTwoSpheres_of_not_isAspherical [PathConnectedSpace G] (b : G)
    (h₂ : Subsingleton (π_ 2 G 1)) (hG : ¬IsAspherical G 1) :
    IsAbundantWithTwoSpheres G n b := by
  -- By Lemma 3.41 of the source the double loop space of `G` has a nonzero integral homology class
  -- of positive degree, to which `isAbundantWithTwoSpheres_of_ne_zero` applies.
  rw [isAspherical_iff_doubleLoopSpace_singularHomology] at hG
  push Not at hG
  obtain ⟨m, hm₀, hm⟩ := hG ((pathConnectedSpace_doubleLoopSpace_iff (1 : G)).2 h₂)
  -- Transport the nonzero homology group of `Ω (Ω G 1) (Path.refl 1)` to `Map_*(S², G)`, with
  -- coefficients `ULift ℤ`.
  let e := BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 ⟨G, 1⟩
    Sphere2.north
  have hY : ¬IsZero ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) m) := fun h ↦ hm (h.of_iso
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) m).mapIso
      (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso.symm).app _ ≪≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) m).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).mapIso (TopCat.isoOfHomeo e.symm)))
  rw [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial] at hY
  obtain ⟨α, hα⟩ := exists_ne (0 : ((TopCat.toSSet.obj
    (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) m :
      ModuleCat ℤ))
  exact o.isAbundantWithTwoSpheres_of_ne_zero hn b (Nat.pos_of_ne_zero hm₀) hα

end HomologicalOrientation

/-- **The unit quaternions are abundant with 2-spheres.** The sphere `S³ ⊆ ℍ`, the group `SU(2)`,
is a compact simply connected `3`-manifold and a topological group with `π₂(S³) = 0` and
`π₃(S³) ≠ 0`, so it is abundant with 2-spheres at every point. -/
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
    (subsingleton_homotopyGroup_sphere_quaternion (by simp) 1) fun h ↦ ?_
  -- `π₃(S³)` is nontrivial, so `S³` is not aspherical.
  have := nontrivial_homotopyGroup_sphere (n := 1) Quaternion.finrank_eq_four
    (1 : sphere (0 : ℍ) 1)
  exact not_subsingleton _ ((isAspherical_iff.1 h).2 1)

end TauCeti
