/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Invariance
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer
public import TauCeti.Geometry.Lie.Functor

/-!
# Coadjoint orbits along homomorphisms and through central covers

Let `φ : K →* G` be a homomorphism of Lie groups with differential `dφ : 𝔨 → 𝔤` at the identity
(`MonoidHom.groupLieAlgebraMap`). Pulling functionals back along `dφ`, `ν ↦ ν ∘ dφ`, intertwines
the coadjoint representations:

`Ad*_k (ν ∘ dφ) = (Ad*_{φ k} ν) ∘ dφ`

(`MonoidHom.coadjointRepresentation_comp_groupLieAlgebraMap`). This file draws the consequences
for coadjoint orbits and stabilizers, aimed at homomorphisms `φ` whose differential is
bijective. For finite-dimensional Lie groups with connected target such a homomorphism is a
covering map (`ContMDiffMonoidMorphism.isCoveringMap_of_lieMap_bijective`). Such a `φ` identifies
`𝔨` with `𝔤`, and `ν ↦ ν ∘ dφ` identifies `𝔤*` with `𝔨*`.

* If `φ` is surjective, the `K`-orbit of `ν ∘ dφ` is the image of the `G`-orbit of `ν`
  (`MonoidHom.range_coadjointRepresentation_comp_groupLieAlgebraMap`), and when moreover `dφ` is
  surjective two pulled-back functionals lie in one `K`-orbit exactly when the functionals lie in
  one `G`-orbit (`MonoidHom.exists_coadjointRepresentation_comp_groupLieAlgebraMap_eq_iff`).
  So a surjective cover has the same coadjoint orbits as its base.
* If `dφ` is surjective, the coadjoint stabilizer of `ν ∘ dφ` is the preimage of that of `ν`,
  `K_{ν ∘ dφ} = φ⁻¹(G_ν)` (`MonoidHom.stabilizer_coadjointRepresentation_comp_groupLieAlgebraMap`).
* If `dφ` is injective, the kernel of `φ` acts trivially on `𝔨*`
  (`MonoidHom.coadjointRepresentation_eq_one_of_mem_ker`), so it lies in every coadjoint
  stabilizer (`MonoidHom.ker_le_stabilizer_coadjointRepresentation`). For connected `K` this
  kernel is central (`MonoidHom.ker_le_center_of_injective_groupLieAlgebraMap`).

Hence for a surjective cover `K → G = K / Γ` with discrete central kernel `Γ`, the coadjoint orbit
of `K` through `ν ∘ dφ` is the image of the coadjoint orbit of `G` through `ν`, and its isotropy
group `K_{ν ∘ dφ} = φ⁻¹(G_ν)` contains `Γ`. Passing to the cover thus changes neither the orbits
nor, up to the central factor `Γ` in every isotropy group, their homogeneous models `K / K_{ν ∘ dφ}`
and `G / G_ν`. At the level of Lie algebras, for a smooth homomorphism with surjective
differential the infinitesimal stabilizers correspond,
`𝔨_{ν ∘ dφ} = dφ⁻¹(𝔤_ν)` (`ContMDiffMonoidMorphism.lieAnnihilator_comp_groupLieAlgebraMap`), and
`[ξ] ↦ [dφ ξ]` is a symplectomorphism of the algebraic tangent models of the two orbits for their
Kirillov–Kostant–Souriau forms
(`ContMDiffMonoidMorphism.isSymplectomorphism_quotientLieAnnihilatorEquiv_groupLieAlgebraLieHom`).
The standard example is the double cover `SU(2) → SO(3)`, whose coadjoint orbits are the same
spheres, while their isotropy groups differ by the kernel `{±1}`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Sections 1.1–1.2.
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §14.1–14.3 (coadjoint orbits and their symplectic structure).
-/

public section

noncomputable section

open Module
open scoped ContDiff

namespace MonoidHom

open TauCeti TauCeti.Lie

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I 1 G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace HK]
  {J : ModelWithCorners 𝕜 F HK} {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]
  [LieGroup J 1 K]
  (φ : K →* G)

/-- **Pullback along a homomorphism intertwines the coadjoint representations.** For
`φ : K →* G` with differential `dφ` at the identity, `Ad*_k (ν ∘ dφ) = (Ad*_{φ k} ν) ∘ dφ`. -/
@[simp]
theorem coadjointRepresentation_comp_groupLieAlgebraMap (k : K)
    (ν : Dual 𝕜 (GroupLieAlgebra I G)) :
    coadjointRepresentation 𝕜 J K k (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) =
      (coadjointRepresentation 𝕜 I G (φ k) ν).comp (φ.groupLieAlgebraMap J I).toLinearMap := by
  ext ξ
  have hAd := φ.groupLieAlgebraMap_adjointContinuousLinearMap (I := I) (J := J) k⁻¹ ξ
  rw [map_inv] at hAd
  simp only [LinearMap.comp_apply, coadjointRepresentation_apply, ContinuousLinearMap.coe_coe, hAd]

/-- **Coadjoint orbits of a surjective homomorphism.** If `φ : K →* G` is surjective, the coadjoint
orbit of `ν ∘ dφ` under `K` is the image of the coadjoint orbit of `ν` under `G` by the pullback
`ν' ↦ ν' ∘ dφ`. -/
theorem range_coadjointRepresentation_comp_groupLieAlgebraMap (hφ : Function.Surjective φ)
    (ν : Dual 𝕜 (GroupLieAlgebra I G)) :
    Set.range (fun k : K ↦
        coadjointRepresentation 𝕜 J K k (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)) =
      (fun ν' : Dual 𝕜 (GroupLieAlgebra I G) ↦ ν'.comp (φ.groupLieAlgebraMap J I).toLinearMap) ''
        Set.range (fun g : G ↦ coadjointRepresentation 𝕜 I G g ν) := by
  rw [← Set.range_comp, ← hφ.range_comp]
  congr 1
  funext k
  exact φ.coadjointRepresentation_comp_groupLieAlgebraMap k ν

/-- **A surjective homomorphism with surjective differential has the same coadjoint orbits.** The
pullbacks `ν₁ ∘ dφ` and `ν₂ ∘ dφ` lie in one coadjoint orbit of `K` exactly when `ν₁` and `ν₂` lie
in one coadjoint orbit of `G`. -/
theorem exists_coadjointRepresentation_comp_groupLieAlgebraMap_eq_iff
    (hφ : Function.Surjective φ) (hdφ : Function.Surjective (φ.groupLieAlgebraMap J I))
    {ν₁ ν₂ : Dual 𝕜 (GroupLieAlgebra I G)} :
    (∃ k : K, coadjointRepresentation 𝕜 J K k (ν₁.comp (φ.groupLieAlgebraMap J I).toLinearMap) =
        ν₂.comp (φ.groupLieAlgebraMap J I).toLinearMap) ↔
      ∃ g : G, coadjointRepresentation 𝕜 I G g ν₁ = ν₂ := by
  -- Pulling back along the surjective `dφ` is injective.
  have hinj : Function.Injective fun ν : Dual 𝕜 (GroupLieAlgebra I G) ↦
      ν.comp (φ.groupLieAlgebraMap J I).toLinearMap :=
    LinearMap.dualMap_injective_of_surjective (f := (φ.groupLieAlgebraMap J I).toLinearMap) hdφ
  simp only [coadjointRepresentation_comp_groupLieAlgebraMap, hinj.eq_iff]
  exact (hφ.exists (p := fun g ↦ coadjointRepresentation 𝕜 I G g ν₁ = ν₂)).symm

/-- **Coadjoint stabilizers along a homomorphism with surjective differential.** If `dφ` is
surjective, the coadjoint stabilizer of `ν ∘ dφ` in `K` is the preimage under `φ` of the coadjoint
stabilizer of `ν` in `G`: `K_{ν ∘ dφ} = φ⁻¹(G_ν)`. -/
theorem stabilizer_coadjointRepresentation_comp_groupLieAlgebraMap
    (hdφ : Function.Surjective (φ.groupLieAlgebraMap J I)) (ν : Dual 𝕜 (GroupLieAlgebra I G)) :
    (coadjointRepresentation 𝕜 J K).stabilizer (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) =
      ((coadjointRepresentation 𝕜 I G).stabilizer ν).comap φ := by
  -- Pulling back along the surjective `dφ` is injective.
  have hinj : Function.Injective fun ν : Dual 𝕜 (GroupLieAlgebra I G) ↦
      ν.comp (φ.groupLieAlgebraMap J I).toLinearMap :=
    LinearMap.dualMap_injective_of_surjective (f := (φ.groupLieAlgebraMap J I).toLinearMap) hdφ
  ext k
  simp only [Subgroup.mem_comap, Representation.mem_stabilizer,
    coadjointRepresentation_comp_groupLieAlgebraMap, hinj.eq_iff]

/-- **The kernel of a homomorphism with injective differential acts trivially on `𝔨*`.** -/
theorem coadjointRepresentation_eq_one_of_mem_ker
    (hdφ : Function.Injective (φ.groupLieAlgebraMap J I)) {k : K} (hk : k ∈ φ.ker) :
    coadjointRepresentation 𝕜 J K k = 1 := by
  ext ν ξ
  rw [coadjointRepresentation_apply,
    φ.adjointContinuousLinearMap_eq_id_of_mem_ker hdφ (inv_mem hk), ContinuousLinearMap.id_apply,
    one_apply_eq_self]

/-- **The kernel of a homomorphism with injective differential lies in every coadjoint
stabilizer.** -/
theorem ker_le_stabilizer_coadjointRepresentation
    (hdφ : Function.Injective (φ.groupLieAlgebraMap J I)) (ν : Dual 𝕜 (GroupLieAlgebra J K)) :
    φ.ker ≤ (coadjointRepresentation 𝕜 J K).stabilizer ν := fun _ hk ↦ by
  rw [Representation.mem_stabilizer, φ.coadjointRepresentation_eq_one_of_mem_ker hdφ hk,
    one_apply_eq_self]

end General

end MonoidHom

namespace ContMDiffMonoidMorphism

open TauCeti TauCeti.Lie

section Real

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace HK] {J : ModelWithCorners ℝ F HK}
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup J ∞ K]
  (φ : ContMDiffMonoidMorphism J I ∞ K G)

/-- **Infinitesimal coadjoint stabilizers along a homomorphism with surjective differential.**
The infinitesimal stabilizer of `ν ∘ dφ` in `𝔨` is the preimage under `dφ` of that of `ν` in `𝔤`:
`𝔨_{ν ∘ dφ} = dφ⁻¹(𝔤_ν)`. -/
theorem lieAnnihilator_comp_groupLieAlgebraMap
    (hdφ : Function.Surjective (φ.toMonoidHom.groupLieAlgebraMap J I))
    (ν : Dual ℝ (GroupLieAlgebra I G)) :
    lieAnnihilator ℝ (GroupLieAlgebra J K)
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap) =
      (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).comap φ.groupLieAlgebraLieHom :=
  Dual.lieAnnihilator_eq_comap (by rwa [coe_groupLieAlgebraLieHom])
    (by rw [toLinearMap_groupLieAlgebraLieHom])

/-- **The Kirillov–Kostant–Souriau forms of a homomorphism with surjective differential agree.**
The equivalence `[ξ] ↦ [dφ ξ]` from the algebraic tangent model `𝔨 ⧸ 𝔨_{ν ∘ dφ}` of the coadjoint
orbit of `K` through `ν ∘ dφ` to the algebraic tangent model `𝔤 ⧸ 𝔤_ν` of the coadjoint orbit of
`G` through `ν` is a symplectomorphism of their Kirillov–Kostant–Souriau forms. -/
theorem isSymplectomorphism_quotientLieAnnihilatorEquiv_groupLieAlgebraLieHom
    (hdφ : Function.Surjective (φ.toMonoidHom.groupLieAlgebraMap J I))
    (ν : Dual ℝ (GroupLieAlgebra I G)) :
    SymplecticForm.IsSymplectomorphism
      (Dual.kksSymplecticForm (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap))
      ν.kksSymplecticForm
      (Dual.quotientLieAnnihilatorEquiv (f := φ.groupLieAlgebraLieHom)
        (ν := ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap) ν
        (by rwa [coe_groupLieAlgebraLieHom]) (by rw [toLinearMap_groupLieAlgebraLieHom])) :=
  Dual.isSymplectomorphism_quotientLieAnnihilatorEquiv _ _ _

end Real

end ContMDiffMonoidMorphism
