/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Retract
public import TauCeti.Geometry.Manifold.PontryaginThom.Degree

/-!
# Double loops of a sphere meeting a framed submanifold once

Let `τ : S × ℝⁿ⁺² → Q` be a framed tube around `f : S → Q` with compact core `S`, in a Hausdorff
space `Q`, and let `c : Q → Sⁿ⁺²` be its Pontryagin–Thom collapse onto the sphere
(`TauCeti.pontryaginThomSphereMap`). Let `σ : Sⁿ⁺² → Q` be a sphere meeting the core in exactly
one point `x`, at which `c ∘ σ` is a local homeomorphism; for a smooth tube this holds when `σ` is
smooth and transverse to the core at `x`. Then the map of Moore double loop spaces
`Ω²σ : Ω²Sⁿ⁺² → Ω²Q`, based at the north pole `N` and at `σ N`, is injective on singular homology
in every degree and with coefficients in any ring
(`TauCeti.IsFramedTube.injective_singularHomologyMap_map_map`).

No condition is put on the base point: it may be the meeting point `x` itself, as in the source,
where the base point of the sphere is its intersection with the submanifold. The composite
`c ∘ σ` has degree `±1`
(`TauCeti.IsFramedTube.bijective_singularHomologyMap_pontryaginThomSphereMap_comp`). Following it
by a rotation `g` of the sphere which moves `c (σ N)` to `N` gives a pointed map
`g ∘ c : Q → Sⁿ⁺²` such that `g ∘ c ∘ σ` still has degree `±1`, so `σ` is a pointed homotopy
retract of the sphere and `Ω²σ` has a left inverse on homology
(`TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap`).

This is the homotopy-theoretic content of Lemma 7.6 of Barraud–Damian–Humilière–Oancea, where a
sphere `X ≅ Sᵏ` in a closed manifold `Q` meets a closed submanifold `Y` with trivial normal bundle
transversely in one point, and the injectivity of `Ω²X → Ω²Q` on homology shows that classes of
`H_*(Ω²Sᵏ)` which are not torsion stay so in `H_*(Ω²Q)`.

## Main results

* `TauCeti.IsFramedTube.injective_singularHomologyMap_map_map`: the double loops of a sphere
  meeting the core of a framed tube once, where its collapse is a local homeomorphism, are
  injective on singular homology.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, Lemma 7.6.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia,
  1965, §7.
-/

public section

open CategoryTheory AlgebraicTopology Metric Set

namespace TauCeti

namespace IsFramedTube

variable {S Q : Type} [TopologicalSpace S] [CompactSpace S] [TopologicalSpace Q] [T2Space Q]
  {n : ℕ} {f : S → Q} {τ : S × (Fin (n + 2) → ℝ) → Q}

/-- **Double loops of a sphere meeting a framed submanifold once (BDHO, Lemma 7.6).** Let
`σ : Sⁿ⁺² → Q` meet the core of a framed tube with fibre `ℝⁿ⁺²` in the single point `x`, and
suppose that the composite of `σ` with the Pontryagin–Thom collapse onto `Sⁿ⁺²` is a local
homeomorphism at `x`. Then `Ω²σ`, on Moore double loop spaces based at the north pole and at its
image, is injective on singular homology in every degree and with coefficients in any ring. -/
theorem injective_singularHomologyMap_map_map (h : IsFramedTube f τ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)
    (σ : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Q)) {x : sphere (0 : EuclideanSpace ℝ
      (Fin (n + 3))) 1} (hx : σ ⁻¹' range f = {x})
    (hσ : IsLocalHomeomorphOn (pontryaginThomSphereMap h.isOpenEmbedding s₀ ∘ σ) {x})
    {q : Q} (hq : σ (sphereNorthPole (n + 2)) = q) (k : Type) [Ring k] (m : ℕ) :
    Function.Injective (ContinuousMap.singularHomologyMap k m
      (MooreLoopSpace.map (MooreLoopSpace.map σ hq : C(MooreLoopSpace _ (sphereNorthPole (n + 2)),
          MooreLoopSpace Q q)) (map_one (MooreLoopSpace.map σ hq)) :
        C(MooreLoopSpace (MooreLoopSpace _ (sphereNorthPole (n + 2))) 1,
          MooreLoopSpace (MooreLoopSpace Q q) 1))) := by
  set c := pontryaginThomSphereMap h.isOpenEmbedding s₀
  -- A rotation `g` of the sphere moving `c q` to the north pole makes `g ∘ c` pointed.
  obtain ⟨A, hA⟩ := MulAction.exists_smul_eq (EuclideanSpace ℝ (Fin (n + 3)) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (n + 3))) (c q) (sphereNorthPole (n + 2))
  let g : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, sphere (0 : EuclideanSpace ℝ
      (Fin (n + 3))) 1) := (LinearIsometryEquiv.unitSphereIsometryEquiv A).toHomeomorph
  let g' : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, sphere (0 : EuclideanSpace ℝ
      (Fin (n + 3))) 1) := (LinearIsometryEquiv.unitSphereIsometryEquiv A).toHomeomorph.symm
  have hg : g.comp c q = sphereNorthPole (n + 2) :=
    (LinearIsometryEquiv.unitSphereIsometryEquiv_apply_eq_smul A _).trans hA
  refine MooreLoopSpace.injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap hq
    hg ?_ k m
  -- `c ∘ σ` has degree `±1`. Its homology map with coefficients in `ULift ℤ`, in which the degree
  -- is stated, is conjugate to the one with coefficients in `ℤ` by the coefficient isomorphism.
  have hcσ := h.bijective_singularHomologyMap_pontryaginThomSphereMap_comp s₀ (by omega) σ hx hσ
  let α := (singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).mapIso
    (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso
  have hsurj : Function.Surjective (ContinuousMap.singularHomologyMap ℤ (n + 2) (c.comp σ)) := by
    intro y
    obtain ⟨z, hz⟩ := hcσ.2 ((α.inv.app _).hom y)
    refine ⟨(α.hom.app _).hom z, ?_⟩
    have := congr_arg (fun φ ↦ φ.hom z) (α.hom.naturality (TopCat.ofHom (c.comp σ)))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    refine this.symm.trans ?_
    rw [hz]
    exact Iso.inv_hom_id_app_apply α _ y
  -- `g` is invertible, hence surjective on homology.
  have hgg' : g.comp g' = ContinuousMap.id _ := ContinuousMap.ext fun _ ↦
    (LinearIsometryEquiv.unitSphereIsometryEquiv A).toHomeomorph.apply_symm_apply _
  have hg_surj : Function.Surjective (ContinuousMap.singularHomologyMap ℤ (n + 2) g) := fun y ↦
    ⟨ContinuousMap.singularHomologyMap ℤ (n + 2) g' y, by
      rw [← ContinuousMap.singularHomologyMap_comp, hgg', ContinuousMap.singularHomologyMap_id]⟩
  rw [ContinuousMap.comp_assoc]
  intro y
  obtain ⟨z, rfl⟩ := hg_surj y
  obtain ⟨w, rfl⟩ := hsurj z
  exact ⟨w, ContinuousMap.singularHomologyMap_comp _ _ _⟩

end IsFramedTube

end TauCeti
