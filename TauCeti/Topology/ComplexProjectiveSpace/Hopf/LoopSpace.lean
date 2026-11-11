/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.SerreFibration.LoopSplitting
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy
import TauCeti.Analysis.Complex.Circle
import TauCeti.Topology.Homotopy.HomotopyGroup.Basic

/-!
# The loop space of complex projective space

Let `q : S²ⁿ⁺¹ → CPⁿ` be the Hopf fibration, `v` a unit vector of `ℂⁿ⁺¹`, and
`j : S¹ → Ω CPⁿ [v]` a based map. The **based Hopf product**
(`TauCeti.ComplexProjectiveSpace.hopfLoopProduct`) is the map

`S¹ × Ω S²ⁿ⁺¹ v → Ω CPⁿ [v]`, `(z, γ) ↦ j z ⋀ q ∘ γ`,

concatenating the loop `j z` with the image of `γ`. For `n ≥ 1` it is a weak homotopy equivalence
as soon as `j` has degree `±1`, in the sense that the composite

`π₁(S¹) → π₁(Ω CPⁿ) ≅ π₂(CPⁿ) → π₁(S¹)`

of the map induced by `j`, the loop-space shift `HomotopyGroup.loopSpaceOptionMulEquiv` and the
boundary map of the Hopf fibration (`TauCeti.ComplexProjectiveSpace.hopfBoundary`) is bijective
(`TauCeti.ComplexProjectiveSpace.isWeakHomotopyEquivalence_hopfLoopProduct`). Thus, given such a
`j`, `Ω CPⁿ ≃ S¹ × Ω S²ⁿ⁺¹` up to weak equivalence.

This is the splitting of the loop space of the base of a Serre fibration
(`TauCeti.TopCat.bijective_homotopyGroupMap_loopProduct`) applied to the Hopf fibration, whose
fibre inclusion `S¹ → S²ⁿ⁺¹` is trivial on all homotopy groups in positive degrees: the higher
homotopy groups of the circle vanish, and `S²ⁿ⁺¹` is simply connected for `n ≥ 1`. In degree
`k ≥ 2` the composite `π_k(S¹) → π_(k+1)(CPⁿ) → π_k(S¹)` has trivial source and target, since
`π_k(S¹)` vanishes, so only the degree-one condition on `j` remains. In degree zero both spaces
are path connected, since `S²ⁿ⁺¹` and `CPⁿ` are simply connected.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.hopfLoopProduct`: the based Hopf product
  `(z, γ) ↦ j z ⋀ q ∘ γ`.
* `TauCeti.ComplexProjectiveSpace.isWeakHomotopyEquivalence_hopfLoopProduct`: for `n ≥ 1` and `j`
  of degree `±1`, the based Hopf product is a weak homotopy equivalence.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 and Example 4.45.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.38.
-/

public section

noncomputable section

open CategoryTheory Metric Set
open scoped Topology.Homotopy HSpaces

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)

/-- The **based Hopf product** of a map `j : S¹ → Ω CPⁿ [v]`: the map
`S¹ × Ω S²ⁿ⁺¹ v → Ω CPⁿ [v]` concatenating the loop `j z` with the image of a loop `γ` under the
Hopf fibration. -/
def hopfLoopProduct (j : C(sphere (0 : ℂ) 1, Ω (ComplexProjectiveSpace n) (mk n v))) :
    C(sphere (0 : ℂ) 1 × Ω (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v,
      Ω (ComplexProjectiveSpace n) (mk n v)) :=
  TopCat.loopProduct (hopfHom n) ⟨v, rfl⟩ j

@[simp]
theorem hopfLoopProduct_apply (j : C(sphere (0 : ℂ) 1, Ω (ComplexProjectiveSpace n) (mk n v)))
    (z : sphere (0 : ℂ) 1) (γ : Ω (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v) :
    hopfLoopProduct v j (z, γ) = (j z).trans (γ.map (continuous_mk n)) := by
  rw [hopfLoopProduct, TopCat.loopProduct_apply]
  refine congrArg _ (Path.ext (funext fun t ↦ ?_))
  rw [Path.map_coe, Function.comp_apply]
  -- `hopfHom n` is the abbreviation `TopCat.ofHom ⟨mk n, _⟩`, so applied to `γ t` it is
  -- `mk n (γ t)` by definition.
  exact TopCat.loopSpaceMap_apply (p := hopfHom n) ⟨v, rfl⟩ γ t

/-- For `n ≥ 1`, the based Hopf product is defined on a path-connected space. -/
private theorem pathConnectedSpace_prod_loopSpace (hn : 0 < n) :
    PathConnectedSpace (sphere (0 : ℂ) 1 × Ω (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v) :=
  have : PathConnectedSpace (sphere (0 : ℂ) 1) :=
    Circle.homeomorphSphere.surjective.pathConnectedSpace Circle.homeomorphSphere.continuous
  have : PathConnectedSpace (Ω (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v) :=
    (pathConnectedSpace_loopSpace_iff_subsingleton_pi1 v).2
      (subsingleton_homotopyGroup_sphere_of_lt (n := 2 * n + 1) (by
        rw [finrank_real_of_complex, finrank_euclideanSpace_fin]; ring) (by simp; omega) v)
  inferInstance

/-- **The loop space of `CPⁿ` splits as `S¹ × Ω S²ⁿ⁺¹`.** For `n ≥ 1`, let `j : S¹ → Ω CPⁿ [v]` be
a based map of degree `±1`: the composite `π₁(S¹) → π₁(Ω CPⁿ) ≅ π₂(CPⁿ) → π₁(S¹)` of the map
induced by `j`, the loop-space shift and the boundary map of the Hopf fibration is bijective. Then
the based Hopf product `(z, γ) ↦ j z ⋀ q ∘ γ` is a weak homotopy equivalence
`S¹ × Ω S²ⁿ⁺¹ → Ω CPⁿ`. -/
theorem isWeakHomotopyEquivalence_hopfLoopProduct (hn : 0 < n)
    {j : C(sphere (0 : ℂ) 1, Ω (ComplexProjectiveSpace n) (mk n v))}
    (hj : j 1 = Path.refl (mk n v))
    (hjdeg : Function.Bijective fun a : HomotopyGroup (Fin 1) (sphere (0 : ℂ) 1) 1 ↦
      hopfBoundary v (Fin 1) (HomotopyGroup.loopSpaceOptionMulEquiv (HomotopyGroup.map j hj a))) :
    (hopfLoopProduct v j).IsWeakHomotopyEquivalence := by
  have := pathConnectedSpace_prod_loopSpace v hn
  have hbase := TopCat.loopProduct_apply_refl (p := hopfHom n) ⟨v, rfl⟩ hj
  refine (ContinuousMap.isWeakHomotopyEquivalence_iff_forall_bijective (1, Path.refl v)).2
    fun k ↦ ?_
  -- Bijectivity does not depend on the name of the base point of the target.
  have key : ∀ y (h : hopfLoopProduct v j (1, Path.refl v) = y),
      Function.Bijective (HomotopyGroup.map (N := Fin k) (hopfLoopProduct v j) h) →
      Function.Bijective (HomotopyGroup.map (N := Fin k) (hopfLoopProduct v j)
        (rfl : hopfLoopProduct v j (1, Path.refl v) = _)) := by
    rintro y rfl hb
    exact hb
  refine key _ hbase ?_
  rcases k with _ | m
  · -- In degree zero both spaces are path connected.
    have : PathConnectedSpace (Ω (ComplexProjectiveSpace n) (mk n v)) :=
      (pathConnectedSpace_loopSpace_iff _).2 inferInstance
    have := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (Path.refl (mk n v))).1
      inferInstance
    have := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero
      ((1 : sphere (0 : ℂ) 1), Path.refl v)).1 inferInstance
    refine ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ?_⟩
    exact ⟨⟦GenLoop.const⟧, Subsingleton.elim _ _⟩
  · -- In positive degree, apply the splitting of the loop space of the base of a fibration.
    refine TopCat.bijective_homotopyGroupMap_loopProduct (N := Fin (m + 1))
      (mk_mem_serreFibrations n)
      (φ := (hopfFiberHomeomorph v).symm) (e := ⟨v, rfl⟩)
      ((hopfFiberHomeomorph v).symm_apply_eq.2 (hopfFiberHomeomorph_one v).symm)
      (i := ⟨fun u : sphere (0 : ℂ) 1 ↦ u • v, continuous_id.smul continuous_const⟩)
      (fun u ↦ (coe_hopfFiberHomeomorph_apply v u).symm) (one_smul _ v) hj
      (fun c ↦ by rw [Subsingleton.elim c 1, HomotopyGroup.map_one]) ?_
    rcases m with _ | m
    · convert hjdeg using 2 with a
      rw [hopfBoundary_apply, TopCat.fibrationBoundaryOfHomeomorph_apply]
    · -- `π_k(S¹)` is trivial for `k ≥ 2`.
      refine ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ?_⟩
      exact ⟨1, Subsingleton.elim _ _⟩

end TauCeti.ComplexProjectiveSpace
