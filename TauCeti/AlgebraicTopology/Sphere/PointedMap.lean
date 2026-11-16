/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Geometry.Sphere.LinearIsometry
import TauCeti.Algebra.Group.ZMultiples

/-!
# Pointed maps out of a sphere are classified by homology

Let `X` be an `(n + 1)`-connected space. Pointed maps `(Sⁿ⁺², N) → (X, x)` out of the sphere,
pointed at its north pole `N`, are the generalized loops of `X` (`GenLoop.sphereEquiv`), and their
pointed homotopy classes form `πₙ₊₂(X, x)` (`HomotopyGroup.sphereEquiv`). The Hurewicz class of
such a map is the image of the fundamental class of the sphere, and the Hurewicz map is injective
on `πₙ₊₂(X, x)` by the Hurewicz theorem. So two pointed maps inducing the same map on
`Hₙ₊₂(-; ℤ)` are homotopic relative to the north pole
(`ContinuousMap.homotopicRel_of_singularHomologyMap_eq`).

For `X = Sⁿ⁺²` this is the pointed form of Hopf's theorem for self-maps of a sphere of dimension at
least two: the homotopy class of a pointed self-map is determined by its degree. In particular a
pointed self-map `δ` of degree `±1`, that is, one inducing a surjection on `Hₙ₊₂(Sⁿ⁺²; ℤ) ≅ ℤ`,
satisfies `δ ∘ δ ≃ id` relative to the north pole: the induced map on `ℤ` is multiplication by
`±1`, so its square is the identity. Since the sphere is homogeneous
(`TauCeti.Sphere.exists_homeomorph_apply_eq`), conjugating by a homeomorphism extends this to
self-maps fixing any point `y`, with `δ ∘ δ ≃ id` relative to `y`
(`ContinuousMap.homotopicRel_comp_self_id_of_surjective_singularHomologyMap`). Barraud, Damian,
Humilière and Oancea use this to retract the double loop space of a sphere off that of a manifold
in the proof of their Lemma 7.6.

## Main results

* `ContinuousMap.homotopicRel_of_singularHomologyMap_eq`: pointed maps from `Sⁿ⁺²` to an
  `(n + 1)`-connected space are homotopic relative to the north pole when they agree on
  `Hₙ₊₂(-; ℤ)`.
* `ContinuousMap.homotopicRel_comp_self_id_of_surjective_singularHomologyMap`: a pointed self-map
  of `Sⁿ⁺²` of degree `±1`, at any base point, squares to the identity up to pointed homotopy.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2, Theorem 4.32 and Corollary 4.25.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, proof of Lemma 7.6.
-/

public section

open CategoryTheory AlgebraicTopology Metric TauCeti
open scoped Topology.Homotopy

namespace ContinuousMap

variable {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}

/-- **Pointed maps out of a sphere are classified by homology.** If `πₖ(X, x)` is trivial for every
`k < n + 2`, two pointed maps `(Sⁿ⁺², N) → (X, x)` that induce the same map on `Hₙ₊₂(-; ℤ)` are
homotopic relative to the north pole `N`. -/
theorem homotopicRel_of_singularHomologyMap_eq
    {f g : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, X)}
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (hf : f (sphereNorthPole (n + 2)) = x) (hg : g (sphereNorthPole (n + 2)) = x)
    (h : singularHomologyMap ℤ (n + 2) f = singularHomologyMap ℤ (n + 2) g) :
    f.HomotopicRel g {sphereNorthPole (n + 2)} := by
  -- Read `f` and `g` as generalized loops of `X`.
  let e := GenLoop.sphereEquiv (n + 2) X x
  have hp : GenLoop.toSphere (e.symm ⟨f, hf⟩) = f :=
    (GenLoop.coe_sphereEquiv_apply _).symm.trans (congrArg Subtype.val (e.apply_symm_apply _))
  have hq : GenLoop.toSphere (e.symm ⟨g, hg⟩) = g :=
    (GenLoop.coe_sphereEquiv_apply _).symm.trans (congrArg Subtype.val (e.apply_symm_apply _))
  -- Their Hurewicz classes are the images of that of the tautological loop of the sphere, so they
  -- agree, and the Hurewicz map is injective on `πₙ₊₂(X, x)`.
  have hpq : (⟦e.symm ⟨f, hf⟩⟧ : HomotopyGroup (Fin (n + 2)) X x) = ⟦e.symm ⟨g, hg⟩⟧ := by
    refine (HomotopyGroup.bijective_hurewicz hX).1 ?_
    simp only [HomotopyGroup.hurewicz_mk]
    rw [GenLoop.hurewicz_eq_hurewicz_sphereGenLoop_comp _ (e.symm ⟨f, hf⟩),
      GenLoop.hurewicz_eq_hurewicz_sphereGenLoop_comp _ (e.symm ⟨g, hg⟩), hp, hq,
      ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
    -- `singularHomologyMap ℤ (n + 2) f` is by definition the underlying linear map of the morphism
    -- that the singular homology functor assigns to `f`.
    exact LinearMap.congr_fun h _
  simpa only [hp, hq] using GenLoop.homotopic_iff_toSphere.1 (Quotient.exact hpq)

/-- The case of `homotopicRel_comp_self_id_of_surjective_singularHomologyMap` at the north pole,
where the homology classification of pointed maps applies directly. -/
private theorem homotopicRel_comp_self_id_of_surjective_singularHomologyMap_northPole
    {δ : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1,
      sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)}
    (hδ : δ (sphereNorthPole (n + 2)) = sphereNorthPole (n + 2))
    (h : Function.Surjective (singularHomologyMap ℤ (n + 2) δ)) :
    (δ.comp δ).HomotopicRel (ContinuousMap.id _) {sphereNorthPole (n + 2)} := by
  refine homotopicRel_of_singularHomologyMap_eq
    (fun k hk ↦
      subsingleton_homotopyGroup_sphere_of_lt (n := n + 2) (by simp) (by simpa using hk) _)
    (by rw [comp_apply, hδ, hδ]) (id_apply _) ?_
  -- The Hurewicz class of the tautological loop generates `Hₙ₊₂(Sⁿ⁺²; ℤ)`, which is therefore
  -- infinite cyclic, so the surjection `δ_*` on it squares to the identity.
  let ι := GenLoop.hurewicz (ModuleCat.of ℤ ℤ) (sphereGenLoop (n + 2))
  have hg : Function.Bijective fun k : ℤ ↦ k • ι.hom 1 := by
    convert (ConcreteCategory.bijective_of_isIso ι) using 1
    funext k
    rw [← map_zsmul, smul_eq_mul, mul_one]
  have hinv := (singularHomologyMap ℤ (n + 2) δ).toAddMonoidHom.involutive_of_surjective hg h
  ext y
  rw [singularHomologyMap_comp, singularHomologyMap_id]
  exact hinv y

/-- **A pointed self-map of a sphere of degree `±1` is an involution up to pointed homotopy.** If
a self-map `δ` of `Sⁿ⁺²` fixing a point `y` induces a surjection on `Hₙ₊₂(Sⁿ⁺²; ℤ) ≅ ℤ`, then
`δ ∘ δ` is homotopic to the identity relative to `y`. -/
theorem homotopicRel_comp_self_id_of_surjective_singularHomologyMap
    {y : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1}
    {δ : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1,
      sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)}
    (hδ : δ y = y) (h : Function.Surjective (singularHomologyMap ℤ (n + 2) δ)) :
    (δ.comp δ).HomotopicRel (ContinuousMap.id _) {y} := by
  -- Conjugating by a homeomorphism `a` with `a N = y` gives a self-map `ε = a⁻¹ ∘ δ ∘ a` fixing
  -- the north pole `N`, still of degree `±1`, so `ε ∘ ε ≃ id` relative to `N`.
  obtain ⟨a, ha⟩ := Sphere.exists_homeomorph_apply_eq (sphereNorthPole (n + 2)) y
  let A : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1,
    sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) := a
  let A' : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1,
    sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) := a.symm
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = A'.comp (δ.comp A) := ⟨_, rfl⟩
  have hεε := homotopicRel_comp_self_id_of_surjective_singularHomologyMap_northPole
    (δ := ε) (by simp [hεdef, A, A', ha, hδ, a.symm_apply_eq]) (by
      have hcomp : ⇑(singularHomologyMap ℤ (n + 2) ε) = singularHomologyMap ℤ (n + 2) A' ∘
          singularHomologyMap ℤ (n + 2) δ ∘ singularHomologyMap ℤ (n + 2) A := by
        funext z
        simp only [hεdef, Function.comp_apply, singularHomologyMap_comp]
      rw [hcomp]
      exact (a.symm.toHomotopyEquiv.bijective_singularHomologyMap ℤ (n + 2)).2.comp
        (h.comp (a.toHomotopyEquiv.bijective_singularHomologyMap ℤ (n + 2)).2))
  -- Conjugating back by `a` gives `δ ∘ δ = a ∘ ε ∘ ε ∘ a⁻¹ ≃ id` relative to `y`.
  have hr : A.comp ((ε.comp ε).comp A') = δ.comp δ := by
    ext1 z
    simp [hεdef, A, A']
  have hpre : A' ⁻¹' {sphereNorthPole (n + 2)} = {y} := by
    ext z
    simp [A', ← ha, a.symm_apply_eq]
  have hid : A.comp ((ContinuousMap.id _).comp A') = ContinuousMap.id _ := by
    ext1 z
    simp [A, A']
  simpa only [hr, hpre, hid] using (hεε.precomp A').comp_continuousMap A

end ContinuousMap
