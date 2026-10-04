/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.LensSpace.Basic
public import TauCeti.Geometry.Manifold.Riemannian.ModelGeometry
public import TauCeti.Geometry.Manifold.SMulGroupoid

/-!
# Geometric structures modelled on Thurston's eight geometries

A space `M` has a *geometric structure* modelled on one of Thurston's eight geometries `G`, with
model space `X = G.Space`, when `M` is homeomorphic to an orbit space `X / Γ` of a subgroup `Γ` of
the full isometry group `Isom X` acting freely and properly discontinuously on `X`. This is the
notion in the statement of the geometrization theorem: each piece of the prime and torus
decomposition of a closed orientable 3-manifold admits a geometric structure.

Thurston and Scott equivalently describe a geometric structure as a complete `(Isom X, X)`-structure
on `M`, that is, a complete locally homogeneous metric locally isometric to `X`. Every model space
`X` is simply connected, so the developing map of a complete structure identifies `M` with such a
quotient `X / Γ`; the quotient description is therefore taken as the definition here. In the other
direction, the orbit space `X / Γ` carries the `(Isom X, X)`-atlas pushed forward from `X`
(`TauCeti.hasGroupoid_smulGroupoid_quotient_subgroup`), so a space with a geometric structure is an
`(Isom X, X)`-manifold (`TauCeti.HasGeometricStructure.exists_hasGroupoid`). In particular it is a
smooth manifold and inherits a Riemannian metric from `X`
(`TauCeti.Geometry.Manifold.Riemannian.SMulGroupoid`).

The structure is defined for a topological space `M`, up to homeomorphism. For 3-manifolds this
agrees with the smooth notion, since by Moise's theorem every topological 3-manifold has a smooth
structure, unique up to diffeomorphism.

As a first family of examples, every three-dimensional lens space `L(m; ℓ₀, ℓ₁)` is a spherical
manifold: its lens group acts on the unit sphere of `ℂ²` by unitary rotations, which a real linear
isometry `ℂ² ≃ ℝ⁴` turns into isometries of the round three-sphere.

## Main definitions

* `TauCeti.HasGeometricStructure M G`: `M` is homeomorphic to `G.Space / Γ` for a subgroup `Γ` of
  `Isom G.Space` acting freely and properly discontinuously.

## Main results

* `TauCeti.hasGeometricStructure_iff_exists_isQuotientMap`: a geometric structure is a quotient map
  `G.Space → M` whose fibres are the orbits of such a subgroup.
* `TauCeti.hasGeometricStructure_quotient` and `TauCeti.hasGeometricStructure_space`: every such
  orbit space, and in particular the model space itself, has a geometric structure.
* `Homeomorph.hasGeometricStructure_iff`: having a geometric structure is invariant under
  homeomorphism.
* `TauCeti.HasGeometricStructure.exists_hasGroupoid`: a space with a geometric structure is an
  `(Isom X, X)`-manifold.
* `TauCeti.LensSpace.hasGeometricStructure_spherical`: three-dimensional lens spaces are spherical
  manifolds.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983), 401–487,
  Sections 1 and 4.
* W. P. Thurston, *Three-Dimensional Geometry and Topology*, Vol. 1, Princeton University
  Press (1997), Sections 3.4 (complete `(G, X)`-structures and the developing map) and 3.8
  (model geometries and geometric manifolds).
-/

public section

open Metric Topology Filter
open scoped Manifold ContDiff EuclideanSpace

namespace TauCeti

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {G : ModelGeometry}

/-- A topological space `M` has a **geometric structure** modelled on the Thurston geometry `G` if
it is homeomorphic to the orbit space `X / Γ` of a subgroup `Γ` of the isometry group of the model
space `X = G.Space` acting freely and properly discontinuously on `X`. -/
def HasGeometricStructure (M : Type*) [TopologicalSpace M] (G : ModelGeometry) : Prop :=
  ∃ Γ : Subgroup (Isom G.model G.Space), ProperlyDiscontinuousSMul Γ G.Space ∧
    IsCancelSMul Γ G.Space ∧ Nonempty (M ≃ₜ MulAction.orbitRel.Quotient Γ G.Space)

/-- The orbit space of a free, properly discontinuous action of a group of isometries of a model
space has a geometric structure modelled on that geometry. -/
theorem hasGeometricStructure_quotient (Γ : Subgroup (Isom G.model G.Space))
    [ProperlyDiscontinuousSMul Γ G.Space] [IsCancelSMul Γ G.Space] :
    HasGeometricStructure (MulAction.orbitRel.Quotient Γ G.Space) G :=
  ⟨Γ, ‹_›, ‹_›, ⟨Homeomorph.refl _⟩⟩

/-- Having a geometric structure modelled on `G` is invariant under homeomorphism. -/
theorem _root_.Homeomorph.hasGeometricStructure_iff (e : M ≃ₜ N) :
    HasGeometricStructure M G ↔ HasGeometricStructure N G := by
  constructor
  · rintro ⟨Γ, hΓ, hfree, ⟨f⟩⟩
    exact ⟨Γ, hΓ, hfree, ⟨e.symm.trans f⟩⟩
  · rintro ⟨Γ, hΓ, hfree, ⟨f⟩⟩
    exact ⟨Γ, hΓ, hfree, ⟨e.trans f⟩⟩

/-- If a quotient map from the model space `G.Space` onto `M` identifies exactly the points in the
same orbit of a group of isometries acting freely and properly discontinuously, then `M` has a
geometric structure modelled on `G`. -/
theorem hasGeometricStructure_of_isQuotientMap (Γ : Subgroup (Isom G.model G.Space))
    [ProperlyDiscontinuousSMul Γ G.Space] [IsCancelSMul Γ G.Space] {f : G.Space → M}
    (hf : IsQuotientMap f) (hfib : ∀ x y, f x = f y ↔ MulAction.orbitRel Γ G.Space x y) :
    HasGeometricStructure M G := by
  let q : MulAction.orbitRel.Quotient Γ G.Space → M :=
    Quotient.lift f fun x y hxy ↦ (hfib x y).2 hxy
  have hq : IsHomeomorph q := isHomeomorph_iff_isQuotientMap_injective.2
    ⟨isQuotientMap_quotient_mk'.of_comp_isQuotientMap hf, fun x y ↦
      Quotient.inductionOn₂ x y fun x y hxy ↦ Quotient.sound ((hfib x y).1 hxy)⟩
  exact ⟨Γ, ‹_›, ‹_›, ⟨(hq.homeomorph q).symm⟩⟩

/-- A space has a geometric structure modelled on `G` exactly when it is the target of a quotient
map from the model space `G.Space` whose fibres are the orbits of a group of isometries acting
freely and properly discontinuously. -/
theorem hasGeometricStructure_iff_exists_isQuotientMap :
    HasGeometricStructure M G ↔ ∃ Γ : Subgroup (Isom G.model G.Space),
      ProperlyDiscontinuousSMul Γ G.Space ∧ IsCancelSMul Γ G.Space ∧
        ∃ f : G.Space → M, IsQuotientMap f ∧
          ∀ x y, f x = f y ↔ MulAction.orbitRel Γ G.Space x y := by
  constructor
  · rintro ⟨Γ, hΓ, hfree, ⟨e⟩⟩
    refine ⟨Γ, hΓ, hfree, e.symm ∘ Quotient.mk _,
      e.symm.isQuotientMap.comp isQuotientMap_quotient_mk', fun x y ↦ ?_⟩
    rw [Function.comp_apply, Function.comp_apply, e.symm.injective.eq_iff, Quotient.eq]
  · rintro ⟨Γ, hΓ, hfree, f, hf, hfib⟩
    exact hasGeometricStructure_of_isQuotientMap Γ hf hfib

variable (G) in
/-- Each model space has a geometric structure modelled on its own geometry. -/
theorem hasGeometricStructure_space : HasGeometricStructure G.Space G :=
  have : IsCancelSMul (⊥ : Subgroup (Isom G.model G.Space)) G.Space :=
    isCancelSMul_iff_eq_one_of_smul_eq.2 fun γ _ _ ↦ Subsingleton.elim γ 1
  hasGeometricStructure_of_isQuotientMap ⊥ .id fun x y ↦ by
    rw [MulAction.orbitRel_apply]
    refine ⟨fun (h : x = y) ↦ h ▸ MulAction.mem_orbit_self x, ?_⟩
    rintro ⟨γ, rfl⟩
    simp [Subsingleton.elim γ 1]

/-- A space with a geometric structure modelled on `G` is an `(Isom X, X)`-manifold for the model
space `X = G.Space`: it has an `X`-valued atlas whose transition maps are locally restrictions of
isometries of `X`. -/
theorem HasGeometricStructure.exists_hasGroupoid (h : HasGeometricStructure M G) :
    ∃ _ : ChartedSpace G.Space M, HasGroupoid M (smulGroupoid (Isom G.model G.Space) G.Space) := by
  obtain ⟨Γ, hΓ, hfree, ⟨e⟩⟩ := h
  -- Push the charts of `X` forward along the covering map `X → X / Γ ≃ₜ M`.
  have hf : IsLocalHomeomorph (e.symm ∘ Quotient.mk (MulAction.orbitRel Γ G.Space)) :=
    e.symm.isLocalHomeomorph.comp isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul
  obtain ⟨s, hs⟩ := (e.symm.surjective.comp Quotient.mk_surjective).hasRightInverse
  refine ⟨hf.chartedSpaceOfRightInverse hs,
    hf.hasGroupoid_smulGroupoid_chartedSpaceOfRightInverse hs fun z w hzw ↦ ?_⟩
  obtain ⟨γ, hγ⟩ := Quotient.exact (e.symm.injective hzw).symm
  exact ⟨γ, hγ, Eventually.of_forall fun y ↦
    congrArg e.symm (Quotient.sound ⟨γ, rfl⟩)⟩

namespace LensSpace

variable (m : ℕ) [NeZero m] (ℓ : Fin 2 → (ZMod m)ˣ)

/-- **Three-dimensional lens spaces are spherical manifolds.** A real linear isometry `ℂ² ≃ ℝ⁴`
carries the lens group, acting on the unit sphere of `ℂ²`, to a finite group of isometries of the
round three-sphere acting freely, and the lens space is its orbit space. -/
theorem hasGeometricStructure_spherical :
    HasGeometricStructure (LensSpace m ℓ) .spherical := by
  have hrank : Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 4 := by
    simp [finrank_real_of_complex]
  let e : EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
    ((stdOrthonormalBasis ℝ _).reindex (finCongr hrank)).repr
  -- The lens rotations, conjugated by `e`, as isometries of the round three-sphere.
  let ρ : Multiplicative (ZMod m) →* Isom (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    (LinearIsometryEquiv.unitSphereIsomHom (n := 3)).comp
      { toFun g := (e.symm.trans g).trans e
        map_one' := by ext; simp
        map_mul' g g' := by ext; simp [LinearIsometryEquiv.mul_def] } |>.comp
      (lensRotation m ℓ)
  let ψ := (LinearIsometryEquiv.unitSphereIsometryEquiv e.symm).toHomeomorph
  have hρ (a : Multiplicative (ZMod m)) (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
      ψ (ρ a • x) = lensRotation m ℓ a • ψ x := by
    ext1
    simp [ψ, ρ]
  have : Finite ρ.range := (Set.finite_range ρ).to_subtype
  have : IsCancelSMul ρ.range (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
    refine isCancelSMul_iff_eq_one_of_smul_eq.2 fun γ x hx ↦ Subtype.ext ?_
    obtain ⟨a, ha⟩ := γ.2
    have hfix := congrArg ψ hx
    rw [Subgroup.smul_def, ← ha, hρ] at hfix
    have h1 : lensGroupEquiv m ℓ a = 1 :=
      isCancelSMul_iff_eq_one_of_smul_eq.1 (lensGroup_isCancelSMul m ℓ) _ _
        (by rwa [Subgroup.smul_def, coe_lensGroupEquiv_apply])
    rw [← ha, (map_eq_one_iff _ (lensGroupEquiv m ℓ).injective).1 h1, map_one,
      OneMemClass.coe_one]
  refine hasGeometricStructure_of_isQuotientMap (M := LensSpace m ℓ) (G := .spherical) ρ.range
    (f := mk m ℓ ∘ ψ) ?_ fun x y ↦ ?_
  · exact mk_def m ℓ ▸ isQuotientMap_quotient_mk'.comp ψ.isQuotientMap
  · rw [Function.comp_apply, Function.comp_apply, mk_eq_mk_iff, MulAction.orbitRel_apply,
      MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨⟨ρ a, MonoidHom.mem_range.2 ⟨a, rfl⟩⟩, ψ.injective ?_⟩
      rw [Subgroup.smul_def, Subgroup.coe_mk, hρ]
      exact Subtype.ext ((LinearIsometryEquiv.coe_smul_unitSphere _ _).trans ha)
    · rintro ⟨γ, hγ⟩
      obtain ⟨a, ha⟩ := γ.2
      refine ⟨a, ?_⟩
      rw [← hγ, Subgroup.smul_def, ← ha, hρ, LinearIsometryEquiv.coe_smul_unitSphere]

end LensSpace

end TauCeti
