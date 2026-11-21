/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Map
public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit

/-!
# Coadjoint orbits along homomorphisms and through central covers

Let `φ : K →* G` be a smooth homomorphism of real Lie groups with finite-dimensional boundaryless
models, with differential `dφ : 𝔨 → 𝔤` at the identity (`MonoidHom.groupLieAlgebraMap`), and fix
`ν ∈ 𝔤*`. When `dφ` is surjective, the coadjoint stabilizer of the pulled-back functional
`ν ∘ dφ ∈ 𝔨*` is the preimage of that of `ν`, `K_{ν ∘ dφ} = φ⁻¹(G_ν)`
(`MonoidHom.stabilizer_coadjointRepresentation_comp_groupLieAlgebraMap`). So `φ` induces a map of
homogeneous coadjoint orbits

`Φ : K ⧸ K_{ν ∘ dφ} → G ⧸ G_ν`, `[k] ↦ [φ k]`

(`MonoidHom.coadjointOrbitQuotientMap`). This file shows that `Φ` is compatible with all the
structure of the two orbits:

* it is smooth, and equivariant along `φ`: `Φ (k • x) = φ k • Φ x`;
* it intertwines the orbit maps into the duals: `Ad*_{φ k} ν ∘ dφ = Ad*_k (ν ∘ dφ)`, that is,
  the orbit map of `ν ∘ dφ` is the orbit map of `ν` followed by the pullback `μ ↦ μ ∘ dφ`;
* it pulls the Kirillov–Kostant–Souriau form `ω_ν` back to `ω_{ν ∘ dφ}`
  (`MonoidHom.mpullback_coadjointOrbitQuotientMap_coadjointOrbitForm`);
* it is injective, and it is surjective when `φ` is.

The form identity is checked on `K`. The KKS form is characterized by its pullback to the group,
the left-invariant Kirillov form (`Module.Dual.eq_coadjointOrbitForm_iff`), and `Φ` composed with
the projection of `K` is the projection of `G` composed with `φ`, which pulls the left-invariant
Kirillov form `σ_ν` back to `σ_{ν ∘ dφ}` (`MonoidHom.mpullback_leftInvariantKirillovForm`).

The main application is to coverings. A surjective smooth homomorphism `φ : K → G = K / Γ` with
bijective differential, whose kernel `Γ` is then discrete and, for connected `K`, central
(`MonoidHom.ker_le_center_of_injective_groupLieAlgebraMap`), identifies `𝔤*` with `𝔨*` by
`ν ↦ ν ∘ dφ`. Under this identification every coadjoint orbit of `K` is a coadjoint orbit of `G`,
and `Φ` is a bijective smooth symplectic map between the two homogeneous models
(`MonoidHom.bijective_coadjointOrbitQuotientMap`), although their isotropy groups differ by `Γ`.
For instance the coadjoint orbits of `SU(2)` and `SO(3)` are the same symplectic spheres.

## Main definitions

* `MonoidHom.coadjointOrbitQuotientMap`: the map `[k] ↦ [φ k]` of homogeneous coadjoint orbits.

## Main results

* `MonoidHom.contMDiff_coadjointOrbitQuotientMap`: it is smooth.
* `MonoidHom.coadjointOrbitQuotientMap_smul`: it is equivariant along `φ`.
* `MonoidHom.coadjointOrbitMap_coadjointOrbitQuotientMap`: it intertwines the orbit maps.
* `MonoidHom.mpullback_coadjointOrbitQuotientMap_coadjointOrbitForm`: it pulls the KKS form of `ν`
  back to the KKS form of `ν ∘ dφ`.
* `MonoidHom.injective_coadjointOrbitQuotientMap`,
  `MonoidHom.surjective_coadjointOrbitQuotientMap`, `MonoidHom.bijective_coadjointOrbitQuotientMap`:
  it is injective, and bijective for a surjective homomorphism.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Sections 1.1–1.2.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 14.
-/

public section

noncomputable section

open Function Module Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace MonoidHom

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace HK] {J : ModelWithCorners ℝ F HK}
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup J ∞ K]
  (φ : K →* G) (hdφ : Surjective (φ.groupLieAlgebraMap J I))
  (ν : Module.Dual ℝ (GroupLieAlgebra I G))

/-- **The map of coadjoint orbits induced by a homomorphism.** For `φ : K →* G` with surjective
differential `dφ` at the identity, the map `[k] ↦ [φ k]` from the coadjoint orbit
`K ⧸ K_{ν ∘ dφ}` of `ν ∘ dφ` to the coadjoint orbit `G ⧸ G_ν` of `ν`. It is well defined because
`K_{ν ∘ dφ} = φ⁻¹(G_ν)` (`MonoidHom.stabilizer_coadjointRepresentation_comp_groupLieAlgebraMap`). -/
def coadjointOrbitQuotientMap :
    K ⧸ (coadjointRepresentation ℝ J K).stabilizer (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) →
      G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν :=
  Quotient.map' φ fun a b hab ↦ by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have h := (φ.stabilizer_coadjointRepresentation_comp_groupLieAlgebraMap hdφ ν).le hab
    rwa [Subgroup.mem_comap, map_mul, map_inv] at h

/-- The induced map of coadjoint orbits sends the coset of `k` to the coset of `φ k`. -/
@[simp]
theorem coadjointOrbitQuotientMap_mk (k : K) :
    φ.coadjointOrbitQuotientMap hdφ ν (k : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)) =
      (φ k : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  (rfl)

/-- The induced map of coadjoint orbits composed with the projection of `K` is the projection of
`G` composed with `φ`. -/
theorem coadjointOrbitQuotientMap_comp_mk :
    φ.coadjointOrbitQuotientMap hdφ ν ∘ (QuotientGroup.mk : K → K ⧸
        (coadjointRepresentation ℝ J K).stabilizer
          (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)) =
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) ∘ φ :=
  funext fun k ↦ φ.coadjointOrbitQuotientMap_mk hdφ ν k

/-- **The induced map of coadjoint orbits is equivariant along `φ`.** -/
theorem coadjointOrbitQuotientMap_smul (k : K)
    (x : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
      (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)) :
    φ.coadjointOrbitQuotientMap hdφ ν (k • x) = φ k • φ.coadjointOrbitQuotientMap hdφ ν x := by
  induction x using QuotientGroup.induction_on with
  | H a => rw [MulAction.Quotient.smul_coe, coadjointOrbitQuotientMap_mk,
      coadjointOrbitQuotientMap_mk, MulAction.Quotient.smul_coe, smul_eq_mul, smul_eq_mul, map_mul]

/-- **The induced map intertwines the orbit maps.** The orbit map of `ν ∘ dφ` is the orbit map of
`ν` read through the induced map of coadjoint orbits and pulled back along `dφ`. -/
theorem coadjointOrbitMap_coadjointOrbitQuotientMap
    (x : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
      (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)) :
    (ν.coadjointOrbitMap (φ.coadjointOrbitQuotientMap hdφ ν x)).comp
        (φ.groupLieAlgebraMap J I).toLinearMap =
      Module.Dual.coadjointOrbitMap (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) x := by
  induction x using QuotientGroup.induction_on with
  | H k => rw [coadjointOrbitQuotientMap_mk, Module.Dual.coadjointOrbitMap_mk,
      Module.Dual.coadjointOrbitMap_mk, coadjointRepresentation_comp_groupLieAlgebraMap]

/-- **The induced map of coadjoint orbits is injective**, since `K_{ν ∘ dφ}` is the full preimage
`φ⁻¹(G_ν)`. -/
theorem injective_coadjointOrbitQuotientMap :
    Injective (φ.coadjointOrbitQuotientMap hdφ ν) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with | H a =>
  induction y using QuotientGroup.induction_on with | H b =>
  rw [coadjointOrbitQuotientMap_mk, coadjointOrbitQuotientMap_mk, QuotientGroup.eq] at hxy
  rw [QuotientGroup.eq, φ.stabilizer_coadjointRepresentation_comp_groupLieAlgebraMap hdφ ν,
    Subgroup.mem_comap, map_mul, map_inv]
  exact hxy

/-- The induced map of coadjoint orbits of a surjective homomorphism is surjective. -/
theorem surjective_coadjointOrbitQuotientMap (hφ : Surjective φ) :
    Surjective (φ.coadjointOrbitQuotientMap hdφ ν) := by
  intro x
  induction x using QuotientGroup.induction_on with | H g =>
  obtain ⟨k, rfl⟩ := hφ g
  exact ⟨k, φ.coadjointOrbitQuotientMap_mk hdφ ν k⟩

/-- **Coadjoint orbits of a covering.** For a surjective homomorphism with surjective differential,
the induced map of coadjoint orbits is a bijection. -/
theorem bijective_coadjointOrbitQuotientMap (hφ : Surjective φ) :
    Bijective (φ.coadjointOrbitQuotientMap hdφ ν) :=
  ⟨φ.injective_coadjointOrbitQuotientMap hdφ ν, φ.surjective_coadjointOrbitQuotientMap hdφ ν hφ⟩

/-! ### Smoothness and the Kirillov–Kostant–Souriau forms -/

variable [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ F] [J.Boundaryless] {φ}

/-- **The induced map of coadjoint orbits is smooth** when `φ` is, by descent along the
submersion `K → K ⧸ K_{ν ∘ dφ}`. -/
theorem contMDiff_coadjointOrbitQuotientMap (hφ : ContMDiff J I ∞ φ) :
    ContMDiff
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (φ.coadjointOrbitQuotientMap hdφ ν) :=
  ((Module.Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
    (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)).contMDiff_comp_iff
      QuotientGroup.mk_surjective le_rfl).1 (by
      rw [coadjointOrbitQuotientMap_comp_mk]
      exact ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff.comp hφ)

/-- **The induced map of coadjoint orbits is symplectic**: it pulls the Kirillov–Kostant–Souriau
form of `ν` back to the Kirillov–Kostant–Souriau form of `ν ∘ dφ`. -/
@[simp]
theorem mpullback_coadjointOrbitQuotientMap_coadjointOrbitForm (hφ : ContMDiff J I ∞ φ) :
    SmoothForm.mpullback (φ.coadjointOrbitQuotientMap hdφ ν)
        (contMDiff_coadjointOrbitQuotientMap hdφ ν hφ) ν.coadjointOrbitForm =
      Module.Dual.coadjointOrbitForm (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) := by
  have hπK := (Module.Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
    (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)).contMDiff
  have hπG := ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff
  -- Both sides are determined by their pullbacks to `K`, and the square
  -- `Φ ∘ π_K = π_G ∘ φ` reduces the left side to the pullback of `σ_ν` along `φ`.
  rw [Module.Dual.eq_coadjointOrbitForm_iff _ hπK, SmoothForm.mpullback_mpullback_of_comp_eq hπK
    (contMDiff_coadjointOrbitQuotientMap hdφ ν hφ) hφ hπG
    (φ.coadjointOrbitQuotientMap_comp_mk hdφ ν),
    Module.Dual.mpullback_quotientMk_coadjointOrbitForm, mpullback_leftInvariantKirillovForm]

end MonoidHom
