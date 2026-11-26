/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
public import TauCeti.Topology.ComplexProjectiveSpace.Sphere2
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# The higher homotopy groups of `S²` and the Hopf map `S³ → S²`

The Hopf map `h : S³ → S²` (`TauCeti.hopfSphere2`) is the Hopf fibration `S³ → CP¹` followed by
the homeomorphism `CP¹ ≃ₜ S²` (`TauCeti.ComplexProjectiveSpace.homeomorphSphere2`). Its fibres are
circles, whose homotopy groups vanish above degree one, so the exact homotopy sequence of the Hopf
fibration makes `h` induce isomorphisms

`π_k(S³) ≅ π_k(S²)` for every `k ≥ 3`

(`TauCeti.bijective_homotopyGroupMap_hopfSphere2`, `TauCeti.hopfSphere2HomotopyGroupMulEquiv`).
Here `π_k` is modelled on the cube `I^N` for any finite type `N` of cardinality `k`, such as `Fin k`
in Mathlib's notation `π_ k`.

In degree three the source is `π₃(S³) ≅ ℤ`, so

`π₃(S²) ≅ ℤ`

at every base point (`TauCeti.nonempty_addEquiv_int_homotopyGroup_three_sphere2`). So, unlike its
homology, the homotopy of `S²` does not vanish above its dimension. The bound `k ≥ 3` is needed:
in degree two the same exact sequence gives instead the boundary isomorphism
`π₂(CP¹) ≅ π₁(S¹)` (`TauCeti.ComplexProjectiveSpace.hopfBoundaryMulEquiv`), while `π₂(S³)`
vanishes.

## Main declarations

* `TauCeti.bijective_homotopyGroupMap_hopfSphere2`: the Hopf map induces a bijection
  `π_k(S³) → π_k(S²)` for `k ≥ 3`.
* `TauCeti.hopfSphere2HomotopyGroupMulEquiv`: the induced isomorphism of homotopy groups.
* `TauCeti.nonempty_addEquiv_int_homotopyGroup_three_sphere2`: `π₃(S²) ≅ ℤ`.
* `TauCeti.hopfSphere2Hom_mem_serreFibrations`: the Hopf map `S³ → S²` is a Serre fibration.
* `TauCeti.hopfSphere2FiberHomeomorph`: its fibres are circles, those of the Hopf fibration
  `S³ → CP¹` (`TauCeti.preimage_hopfSphere2_singleton`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 4.45 (the Hopf
  fibration and `π₃(S²) ≅ ℤ`) and Theorem 4.41 (the exact homotopy sequence of a fibration).
* H. Hopf, *Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche*, Math. Ann.
  104 (1931), 637–665.
-/

public section

noncomputable section

open Metric
open scoped Topology

namespace TauCeti

open ComplexProjectiveSpace

/-- **`π_k(S³) ≅ π_k(S²)` for `k ≥ 3`.** The Hopf map induces a bijection on the homotopy groups
modelled on `I^N` for every finite type `N` with at least three elements, at every base point. -/
theorem bijective_homotopyGroupMap_hopfSphere2 {N : Type*} [Finite N] (hN : 3 ≤ Nat.card N)
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    Function.Bijective (HomotopyGroup.map (N := N) hopfSphere2 (rfl : hopfSphere2 v = _)) := by
  -- The exact sequence of the Hopf fibration indexes `π_{k+1}` by `Option (Fin k)`.
  obtain ⟨k, hk⟩ : ∃ k, Nat.card N = k + 1 := ⟨Nat.card N - 1, by omega⟩
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
  -- The Hopf map is the Hopf fibration `S³ → CP¹` followed by `CP¹ ≃ₜ S²`.
  have hcomp : (⟨homeomorphSphere2, homeomorphSphere2.continuous⟩ :
      C(ComplexProjectiveSpace 1, Sphere2)).comp ⟨mk 1, continuous_mk 1⟩ = hopfSphere2 :=
    ContinuousMap.ext homeomorphSphere2_mk
  rw [HomotopyGroup.bijective_map_iff_of_equiv _ _
    ((Finite.equivFinOfCardEq hk).trans (finSuccEquiv k)),
    ← HomotopyGroup.map_comp_map_of_comp_eq hcomp (homeomorphSphere2_mk v) rfl]
  exact (HomotopyGroup.homeomorphEquivOfEq homeomorphSphere2
    (homeomorphSphere2_mk v)).bijective.comp (bijective_homotopyGroupMap_mk v)

/-- For `k ≥ 3`, the isomorphism `π_k(S³, v) ≃* π_k(S², h v)` induced by the Hopf map `h`, with
`π_k` modelled on `I^N` for a finite type `N` of cardinality `k`. -/
def hopfSphere2HomotopyGroupMulEquiv {N : Type*} [Finite N] [DecidableEq N] [Nonempty N]
    (hN : 3 ≤ Nat.card N) (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    HomotopyGroup N (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) v ≃*
      HomotopyGroup N Sphere2 (hopfSphere2 v) :=
  MulEquiv.ofBijective (HomotopyGroup.mapHom hopfSphere2 rfl)
    (bijective_homotopyGroupMap_hopfSphere2 hN v)

@[simp]
theorem hopfSphere2HomotopyGroupMulEquiv_apply {N : Type*} [Finite N] [DecidableEq N] [Nonempty N]
    (hN : 3 ≤ Nat.card N) (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)
    (a : HomotopyGroup N (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) v) :
    hopfSphere2HomotopyGroupMulEquiv hN v a = HomotopyGroup.map hopfSphere2 rfl a :=
  (rfl)

/-- **`π₃(S²) ≅ ℤ`**, at every base point of the two-sphere: the Hopf map identifies `π₃(S²)` with
`π₃(S³)`, which is infinite cyclic. -/
theorem nonempty_addEquiv_int_homotopyGroup_three_sphere2 (x : Sphere2) :
    Nonempty (Additive (π_ 3 Sphere2 x) ≃+ ℤ) := by
  obtain ⟨v, rfl⟩ := hopfSphere2_surjective x
  -- Read the unit sphere of `ℂ²` as the unit sphere of `ℝ⁴`, where `π₃(S³) ≅ ℤ` is available.
  let e := sphereHomeomorphOfFinrankEq (finrank_real_euclideanSpace_complex 1 |>.trans
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 4)).symm)
  exact ⟨((hopfSphere2HomotopyGroupMulEquiv (by simp) v).symm.trans
    (HomotopyGroup.homeomorphMulEquiv e v)).toAdditive.trans
      (homotopyGroupSphereAddEquiv (n := 1) (EuclideanSpace.basisFun (Fin 4) ℝ) (e v))⟩

/-! ### The Hopf map as a fibration -/

/-- The Hopf map `S³ → S²` (`TauCeti.hopfSphere2`), as a morphism of topological spaces. -/
abbrev hopfSphere2Hom : TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) ⟶ TopCat.of Sphere2 :=
  TopCat.ofHom hopfSphere2

open CategoryTheory in
/-- **The Hopf map `S³ → S²` is a Serre fibration**: it is the Hopf fibration `S³ → CP¹` followed
by the homeomorphism `CP¹ ≃ₜ S²`. -/
theorem hopfSphere2Hom_mem_serreFibrations : TopCat.serreFibrations hopfSphere2Hom := by
  have : hopfHom 1 ≫ (TopCat.isoOfHomeo homeomorphSphere2).hom = hopfSphere2Hom := by
    ext v : 1
    rw [TopCat.comp_app, TopCat.isoOfHomeo_hom, TopCat.ofHom_apply, TopCat.ofHom_apply,
      TopCat.ofHom_apply]
    exact homeomorphSphere2_mk v
  rw [← this]
  exact MorphismProperty.RespectsIso.postcomp _ _ _ (mk_mem_serreFibrations 1)

/-- The preimage of a set under the Hopf map `S³ → S²` as a morphism of topological spaces is its
preimage under the Hopf map. -/
theorem preimage_hopfSphere2Hom (s : Set Sphere2) : hopfSphere2Hom ⁻¹' s = hopfSphere2 ⁻¹' s := by
  ext v
  rw [Set.mem_preimage, Set.mem_preimage, TopCat.ofHom_apply]

/-- The fibre of the Hopf map `S³ → S²` over `x` is the fibre of the Hopf fibration `S³ → CP¹`
over the point of `CP¹` corresponding to `x` under `CP¹ ≃ₜ S²`. -/
theorem preimage_hopfSphere2_singleton (x : Sphere2) :
    hopfSphere2 ⁻¹' {x} = mk 1 ⁻¹' {homeomorphSphere2.symm x} := by
  ext w
  simp [homeomorphSphere2.eq_symm_apply]

/-- **The fibres of the Hopf map `S³ → S²` are circles**: the fibre over `x` is homeomorphic to the
unit circle, through the orbit map `u ↦ u • v` of a point `v` of the fibre. It is the fibre of the
Hopf fibration `S³ → CP¹` (`TauCeti.ComplexProjectiveSpace.hopfFiberHomeomorph`), carried along
`CP¹ ≃ₜ S²` (`TauCeti.preimage_hopfSphere2_singleton`). -/
def hopfSphere2FiberHomeomorph {x : Sphere2} (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)
    (hv : hopfSphere2 v = x) : sphere (0 : ℂ) 1 ≃ₜ (hopfSphere2 ⁻¹' {x} : Set _) :=
  (hopfFiberHomeomorph v).trans (Homeomorph.setCongr (by
    rw [preimage_hopfSphere2_singleton, ← hv, homeomorphSphere2_symm_hopfSphere2]))

/-- The homeomorphism of the unit circle with a fibre of the Hopf map is the orbit map
`u ↦ u • v`. -/
@[simp]
theorem coe_hopfSphere2FiberHomeomorph_apply {x : Sphere2}
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) (hv : hopfSphere2 v = x)
    (u : sphere (0 : ℂ) 1) :
    (hopfSphere2FiberHomeomorph v hv u : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) = u • v :=
  coe_hopfFiberHomeomorph_apply v u

/-- The unit `1` of the circle corresponds to `v` itself in the fibre of the Hopf map. -/
@[simp]
theorem hopfSphere2FiberHomeomorph_one {x : Sphere2}
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) (hv : hopfSphere2 v = x) :
    hopfSphere2FiberHomeomorph v hv 1 = ⟨v, hv⟩ :=
  Subtype.ext ((coe_hopfSphere2FiberHomeomorph_apply v hv 1).trans (one_smul _ v))

end TauCeti
