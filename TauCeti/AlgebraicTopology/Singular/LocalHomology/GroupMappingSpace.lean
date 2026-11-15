/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Aspherical
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.MappingSpace.Group
public import TauCeti.Topology.MappingSpace.Sphere.Basic
public import TauCeti.Topology.Sphere.Suspension

/-!
# Classes of maps into a manifold group living over its fundamental class

Let `G` be a topological group which is a compact oriented `n`-manifold, and `X` a space with a
base point `x`. Evaluation `ev : Map(X, G) → G` at `x` is a trivial fibration: the homeomorphism
`Ψ : G × Map_*(X, G) ≃ₜ Map(X, G)`, `(g, f) ↦ g · f` (`TauCeti.mappingSpaceGroupHomeomorph`), where
`Map_*(X, G)` is the space of maps sending `x` to `1`, satisfies `ev ∘ Ψ = fst`. So for a class
`β ∈ Hⱼ(Map_*(X, G); ℤ)` the image `Ψ_*([G] × β)` of the cross product with the fundamental class
lives over the fundamental class of `G`, in the sense of Barraud, Damian, Humilière and Oancea
(`TauCeti.LivesOverFundamentalClass`), exactly when `β ≠ 0`
(`HomologicalOrientation.livesOverFundamentalClass_homologyMap_mappingSpaceGroupHomeomorph_iff`).
This is the cross-product statement
`HomologicalOrientation.livesOverFundamentalClass_singularHomologyCross_fundamentalClass_iff`
transported along `Ψ`, which is a homeomorphism over `G`.

For `X = S²` this is the source's Example 6.30: the classes `[G] × α` of `Map(S², G)`, for `α`
a nonzero class of the double loop space `Map_*(S², G) ≅ Ω²G` of positive degree, have degree
above `n` and live over the fundamental class. They witness that `G` is abundant with 2-spheres
(the source's Definition 6.11), the hypothesis of its Theorem H. By Lemma 3.41 of the source
(`TauCeti.isAspherical_iff_doubleLoopSpace_singularHomology`), a path-connected such `G` with
`π₂(G) = 0` that is not aspherical has such a class `α`, so `Map(S², G)` carries a class of degree
above `n` that lives over the fundamental class of `G`
(`TauCeti.HomologicalOrientation.exists_lt_livesOverFundamentalClass_of_not_isAspherical`). For
compact Lie groups `π₂` vanishes by a theorem of Cartan; here it is kept as a hypothesis.

The classes are stated with the coefficients `ℤ ⊗ ℤ` of the cross product, which the
multiplication identifies with `ℤ`.

## Main results

* `HomologicalOrientation.livesOverFundamentalClass_homologyMap_mappingSpaceGroupHomeomorph_iff`:
  `Ψ_*([G] × β)` lives over the fundamental class of `G` exactly when `β ≠ 0`.
* `TauCeti.HomologicalOrientation.exists_lt_livesOverFundamentalClass_of_not_isAspherical`: for a
  path-connected non-aspherical `G` with `π₂(G) = 0`, some class of `Map(S², G)` of degree above
  `n` lives over the fundamental class.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.3 (Definition 6.11), Lemma 3.41 and
  §6.4.3 (Example 6.30).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module
open scoped Topology

namespace TauCeti

namespace HomologicalOrientation

variable {G V : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [T2Space G]
  [CompactSpace G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [ChartedSpace V G] {n : ℕ} (o : HomologicalOrientation G V n) (hn : finrank ℝ V = n)

include hn in
/-- **Maps into a manifold group living over the fundamental class.** Let `G` be a compact
oriented `n`-manifold which is a topological group, `X` a space with base point `x`, and
`Ψ : G × Map_*(X, G) ≃ₜ Map(X, G)` the product decomposition of evaluation at `x`. For a class
`β ∈ Hⱼ(Map_*(X, G); ℤ)`, the class `Ψ_*([G] × β) ∈ Hₙ₊ⱼ(Map(X, G); ℤ ⊗ ℤ)` lives over the
fundamental class of `G` at `b` for evaluation at `x` exactly when `β ≠ 0`. -/
theorem livesOverFundamentalClass_homologyMap_mappingSpaceGroupHomeomorph_iff {X : Type}
    [TopologicalSpace X] (x : X) (b : G) {j k : ℕ} (h : n + j = k)
    (β : ((TopCat.toSSet.obj (TopCat.of {f : C(X, G) // f x = 1})).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) j : ModuleCat.{0} ℤ)) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
        (mappingSpaceEval (X := G) x) b
        ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
          (mappingSpaceGroupHomeomorph (G := G) x : C(G × {f : C(X, G) // f x = 1}, C(X, G)))))
            (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom
          ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of {f : C(X, G) // f x = 1})
            (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) n j k h).hom
              (o.fundamentalClass hn ⊗ₜ β))) ↔
      β ≠ 0 := by
  let Ψ := mappingSpaceGroupHomeomorph (G := G) x
  -- `Ψ` and its inverse are maps over `G`, from the first projection to evaluation and back.
  have hΨ : mappingSpaceEval x ∘ Ψ = id ∘ Prod.fst := by
    ext p
    simp [Ψ, p.2.2]
  have hΨsymm : (id ∘ Prod.fst) ∘ Ψ.symm = mappingSpaceEval x := by
    ext f
    simp [Ψ]
  -- `Ψ⁻¹ ∘ Ψ` is the identity, so `Ψ⁻¹_* Ψ_* γ = γ`.
  have hΨΨ (γ : ((TopCat.toSSet.obj (TopCat.of (G × {f : C(X, G) // f x = 1}))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)) :
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
        (Ψ.symm : C(C(X, G), G × {f : C(X, G) // f x = 1}))))
          (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom
        ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
          (Ψ : C(G × {f : C(X, G) // f x = 1}, C(X, G)))))
            (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom γ) = γ := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← SSet.homologyMap_comp,
      ← Functor.map_comp, ← TopCat.ofHom_comp, Homeomorph.symm_comp_toContinuousMap,
      TopCat.ofHom_id]
    erw [TopCat.toSSet.map_id, SSet.homologyMap_id]
    rfl
  rw [← o.livesOverFundamentalClass_singularHomologyCross_fundamentalClass_iff hn b h β]
  refine ⟨fun hα ↦ ?_, fun hγ ↦ ?_⟩
  · exact LivesOverFundamentalClass.of_homologyMap _
      (Ψ : C(G × {f : C(X, G) // f x = 1}, C(X, G))) hΨ hα
  · refine LivesOverFundamentalClass.of_homologyMap _
      (Ψ.symm : C(C(X, G), G × {f : C(X, G) // f x = 1})) hΨsymm
      ((livesOverFundamentalClass_iff _ _ _ _).2 fun h₀ ↦ ?_)
    exact (livesOverFundamentalClass_iff _ _ _ _).1 hγ ((congrArg (fiberLocalization
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
      (id ∘ Prod.fst : G × {f : C(X, G) // f x = 1} → G) b k).hom (hΨΨ _)).symm.trans h₀)

include o hn in
/-- **Non-aspherical manifold groups** (Barraud–Damian–Humilière–Oancea, Example 6.30). Let `G` be
a path-connected compact oriented `n`-manifold which is a topological group, with `π₂(G) = 0`,
and which is not aspherical. Then some class of `Hₖ(Map(S², G); ℤ ⊗ ℤ)` of degree `k > n` lives
over the fundamental class of `G` at `b`, for evaluation at the north pole. By Lemma 3.41 of the
source (`TauCeti.isAspherical_iff_doubleLoopSpace_singularHomology`), the path-connected double
loop space `Ω²G ≅ Map_*(S², G)` has a nonzero integral class `β` of positive degree, and
`Ψ_*([G] × β)` is such a class. -/
theorem exists_lt_livesOverFundamentalClass_of_not_isAspherical [PathConnectedSpace G] (b : G)
    (hπ : Subsingleton (π_ 2 G 1)) (h : ¬IsAspherical G 1) :
    ∃ k, n < k ∧ ∃ α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, G))).homology
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ),
      LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
        (mappingSpaceEval (X := G) Sphere2.north) b α := by
  obtain ⟨m, hm, hne⟩ : ∃ m ≠ 0, ¬IsZero (((singularChains ℤ).obj
      (TopCat.of (LoopSpace (LoopSpace G 1) (Path.refl 1)))).homology m) := by
    by_contra! H
    exact h ((isAspherical_iff_doubleLoopSpace_singularHomology 1).2
      ⟨(pathConnectedSpace_doubleLoopSpace_iff (1 : G)).2 hπ, H⟩)
  -- Transport the class to `Map_*(S², G)` and to the coefficients `ULift ℤ`.
  let e : TopCat.of {f : C(Sphere2, G) // f Sphere2.north = 1} ≅
      TopCat.of (LoopSpace (LoopSpace G 1) (Path.refl 1)) :=
    TopCat.isoOfHomeo (BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 ⟨G, 1⟩
      Sphere2.north)
  let c : ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ (ULift.{0} ℤ) := ULift.moduleEquiv.toModuleIso.symm
  have hne' : ¬IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) m).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of {f : C(Sphere2, G) // f Sphere2.north = 1})) :=
    fun hz ↦ hne (hz.of_iso (((AlgebraicTopology.singularHomologyFunctor _ m).obj _).mapIso
      e.symm ≪≫ ((AlgebraicTopology.singularHomologyFunctor _ m).mapIso c).app _))
  rw [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial] at hne'
  obtain ⟨β, hβ⟩ := exists_ne (0 : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ)
    m).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of {f : C(Sphere2, G) // f Sphere2.north = 1}))
  exact ⟨n + m, by lia, _,
    (o.livesOverFundamentalClass_homologyMap_mappingSpaceGroupHomeomorph_iff hn Sphere2.north b
      rfl β).2 hβ⟩

end HomologicalOrientation

end TauCeti
