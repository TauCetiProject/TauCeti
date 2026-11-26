/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Map
public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit

import TauCeti.Geometry.Lie.AutomaticSmoothness
import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Dual
import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent

/-!
# Coadjoint orbits along homomorphisms of Lie groups

Let `φ : K →* G` be a homomorphism of real Lie groups with finite-dimensional boundaryless
models, with differential `dφ : 𝔨 → 𝔤` at the identity (`MonoidHom.groupLieAlgebraMap`), and let
`ν ∈ 𝔤*`. When `dφ` is surjective, `φ` induces the injective map of coadjoint orbits

`Φ : K ⧸ K_{ν ∘ dφ} → G ⧸ G_ν`, `[k] ↦ [φ k]`

(`MonoidHom.coadjointOrbitQuotientMap`, in
`TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Map`), well defined because
`K_{ν ∘ dφ} = φ⁻¹(G_ν)`. This file upgrades it to a map of the homogeneous symplectic manifolds of
`TauCeti.Geometry.Symplectic.Coadjoint.Orbit`.

**Along a homomorphism.** The map `Φ` is smooth, it pulls the Kirillov–Kostant–Souriau form `ω_ν`
back to `ω_{ν ∘ dφ}`, and it is a local diffeomorphism. No smoothness of `φ` is assumed. The
differential `dφ` is by definition zero when `φ` is not differentiable at the identity. So when
`𝔤 ≠ 0`, the surjectivity of `dφ` makes `φ` differentiable at the identity, hence continuous,
hence smooth (`TauCeti.Lie.contMDiff_of_surjective_groupLieAlgebraMap`). The form identity is then
checked on `K`: the KKS form is characterized by its pullback to the group
(`Module.Dual.eq_coadjointOrbitForm_iff`), and the smooth homomorphism `φ` pulls the left-invariant
Kirillov form of `ν` back to that of `ν ∘ dφ` (`Module.Dual.mpullback_leftInvariantKirillovForm`).
When `𝔤 = 0`, `φ` need not be smooth, but then `ν = 0` and `ν ∘ dφ = 0`, both orbits are points,
and both KKS forms vanish (`Module.Dual.coadjointOrbitForm_zero`).

The two orbits have the same dimension, since `[ξ] ↦ [dφ ξ]` identifies their tangent models
`𝔨 ⧸ 𝔨_{ν ∘ dφ}` and `𝔤 ⧸ 𝔤_ν`, and the differentials of `Φ` are injective, since `Φ` pulls the
nondegenerate form `ω_ν` back to the nondegenerate form `ω_{ν ∘ dφ}`. So `Φ` is a local
diffeomorphism.

**Homomorphisms meeting every coset.** If moreover `φ` meets every coset of `G_ν`, for instance if
`φ` is surjective, then `Φ` is bijective, hence a diffeomorphism

`K ⧸ K_{ν ∘ dφ} ≃ G ⧸ G_ν`

(`MonoidHom.coadjointOrbitDiffeomorph`), and a symplectomorphism of the Kirillov–Kostant–Souriau
forms (`MonoidHom.mpullback_coadjointOrbitDiffeomorph_coadjointOrbitForm`). Besides surjective
homomorphisms, this covers the inclusion of an open subgroup `H` with `H · G_ν = G`, that is, one
meeting every coset of `G_ν`.

The main example of a surjective homomorphism with surjective differential is a covering
homomorphism `K → G = K ⧸ Γ` by a discrete central subgroup `Γ`, such as `SU(2) → SO(3)`. Then
`dφ` is bijective, the isotropy groups `K_{ν ∘ dφ} ⊇ Γ` and `G_ν` differ, but the coadjoint orbits
are the same symplectic manifolds. Injectivity of `dφ` is not needed: the projection `G × L → G`
of a product identifies the orbit of `(ν, 0)` with that of `ν`.

## Main definitions

* `MonoidHom.coadjointOrbitDiffeomorph`: the map `[k] ↦ [φ k]` as a diffeomorphism
  `K ⧸ K_{ν ∘ dφ} ≃ G ⧸ G_ν`, for `φ` meeting every coset of `G_ν`.

## Main results

* `MonoidHom.contMDiff_coadjointOrbitQuotientMap`: the induced map of coadjoint orbits is smooth.
* `MonoidHom.mpullback_coadjointOrbitQuotientMap_coadjointOrbitForm`: it pulls the KKS form of `ν`
  back to the KKS form of `ν ∘ dφ`.
* `MonoidHom.isLocalDiffeomorph_coadjointOrbitQuotientMap`: it is a local diffeomorphism.
* `MonoidHom.mpullback_coadjointOrbitDiffeomorph_coadjointOrbitForm`: the diffeomorphism is a
  symplectomorphism of the Kirillov–Kostant–Souriau forms.
* `MonoidHom.orbitMap_coadjointOrbitDiffeomorph_comp_groupLieAlgebraMap`: it intertwines the orbit
  maps into `𝔨*` and `𝔤*`.

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

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace HK] {J : ModelWithCorners ℝ F HK} [J.Boundaryless]
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup J ∞ K]
  (φ : K →* G) (hdφ : Surjective (φ.groupLieAlgebraMap J I))
  (ν : Dual ℝ (GroupLieAlgebra I G))

/-! ### Smoothness and the Kirillov–Kostant–Souriau forms -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ F] [J.Boundaryless]
  [LieGroup I ∞ G] [LieGroup J ∞ K] in
/-- If the model space `E` of `G` is trivial, then `ν = 0`, so `ν ∘ dφ = 0`. -/
private theorem comp_groupLieAlgebraMap_eq_zero (hE : Subsingleton E) :
    ν.comp (φ.groupLieAlgebraMap J I).toLinearMap = 0 := by
  rw [Subsingleton.elim ν 0, LinearMap.zero_comp]

/-- The Kirillov–Kostant–Souriau form of a functional equal to zero vanishes. -/
private theorem coadjointOrbitForm_eq_zero {μ : Dual ℝ (GroupLieAlgebra I G)} (hμ : μ = 0) :
    μ.coadjointOrbitForm = 0 := by
  subst hμ
  exact Dual.coadjointOrbitForm_zero

/-- **The induced map of coadjoint orbits is smooth.** A surjective differential at the identity
suffices: `φ` need not be smooth or surjective. -/
theorem contMDiff_coadjointOrbitQuotientMap :
    ContMDiff
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (φ.coadjointOrbitQuotientMap hdφ ν) :=
  -- Descend along the submersion `K → K ⧸ K_{ν ∘ dφ}`: it suffices that `π_G ∘ φ` is smooth.
  ((Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
    (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)).contMDiff_comp_iff
      QuotientGroup.mk_surjective le_rfl).1 (by
      rw [coadjointOrbitQuotientMap_comp_mk]
      rcases subsingleton_or_nontrivial E with hE | hE
      · -- If `𝔤 = 0`, then `G_ν = G`, so the projection of `G` is constant.
        refine (contMDiff_const (c := ((1 : G) : G ⧸
          (coadjointRepresentation ℝ I G).stabilizer ν))).congr fun k ↦ ?_
        exact QuotientGroup.eq.2 (Representation.mem_stabilizer.2 (Subsingleton.elim _ _))
      · exact ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff.comp
          (contMDiff_of_surjective_groupLieAlgebraMap hdφ))

/-- **The induced map of coadjoint orbits is symplectic**: it pulls the Kirillov–Kostant–Souriau
form of `ν` back to the Kirillov–Kostant–Souriau form of `ν ∘ dφ`. -/
@[simp]
theorem mpullback_coadjointOrbitQuotientMap_coadjointOrbitForm :
    SmoothForm.mpullback (φ.coadjointOrbitQuotientMap hdφ ν)
        (φ.contMDiff_coadjointOrbitQuotientMap hdφ ν) ν.coadjointOrbitForm =
      Dual.coadjointOrbitForm (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- If `𝔤 = 0`, then `ν = 0` and `ν ∘ dφ = 0`, whose KKS forms vanish.
    rw [coadjointOrbitForm_eq_zero (Subsingleton.elim ν 0), map_zero,
      coadjointOrbitForm_eq_zero (comp_groupLieAlgebraMap_eq_zero φ ν hE)]
  -- If `𝔤 ≠ 0`, then `φ` is smooth, and pulled back to `K` both sides are `φ^* σ_ν = σ_{ν ∘ dφ}`.
  have hφ := contMDiff_of_surjective_groupLieAlgebraMap hdφ
  have hπK := (Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
    (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)).contMDiff
  have hπG := ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff
  rw [Dual.eq_coadjointOrbitForm_iff _ hπK, SmoothForm.mpullback_mpullback_of_comp_eq hπK
    (φ.contMDiff_coadjointOrbitQuotientMap hdφ ν) hφ hπG
    (φ.coadjointOrbitQuotientMap_comp_mk hdφ ν),
    Dual.mpullback_quotientMk_coadjointOrbitForm]
  exact ν.mpullback_leftInvariantKirillovForm ⟨φ, hφ⟩

/-! ### The local diffeomorphism -/

include hdφ in
/-- The coadjoint orbits `K ⧸ K_{ν ∘ dφ}` and `G ⧸ G_ν` have the same dimension: `[ξ] ↦ [dφ ξ]`
identifies their tangent models `𝔨 ⧸ 𝔨_{ν ∘ dφ}` and `𝔤 ⧸ 𝔤_ν`. -/
private theorem finrank_quotientModelSpace_eq :
    finrank ℝ (Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap))) =
      finrank ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) := by
  rw [Dual.finrank_quotientModelSpace_eq_finrank_quotient_lieAnnihilator,
    Dual.finrank_quotientModelSpace_eq_finrank_quotient_lieAnnihilator]
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- If `𝔤 = 0`, then `ν ∘ dφ = 0`, whose infinitesimal stabilizer is all of `𝔨`.
    rw [comp_groupLieAlgebraMap_eq_zero φ ν hE, lieAnnihilator_zero, LieSubalgebra.top_toSubmodule,
      finrank_zero_of_subsingleton, finrank_zero_of_subsingleton]
  · -- If `𝔤 ≠ 0`, then `φ` is smooth, and `dφ` is a homomorphism of Lie algebras.
    let ψ : ContMDiffMonoidMorphism J I ∞ K G :=
      ⟨φ, contMDiff_of_surjective_groupLieAlgebraMap hdφ⟩
    exact (Dual.quotientLieAnnihilatorEquiv (f := ψ.groupLieAlgebraLieHom)
      (ν := ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) ν
      (by rwa [ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom])
      (by rw [ContMDiffMonoidMorphism.toLinearMap_groupLieAlgebraLieHom])).finrank_eq

/-- The differentials of the map `[k] ↦ [φ k]` of coadjoint orbits are injective: it pulls the
nondegenerate KKS form `ω_ν` back to the nondegenerate KKS form `ω_{ν ∘ dφ}`. -/
private theorem injective_mfderiv_coadjointOrbitQuotientMap
    (x : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
      (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)) :
    Injective (mfderiv
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (φ.coadjointOrbitQuotientMap hdφ ν) x) :=
  ((ν.isSymplectic_coadjointOrbitForm.isNondegenerate.isNondegenerate_mpullback_iff
    (φ.contMDiff_coadjointOrbitQuotientMap hdφ ν)).1
    (φ.mpullback_coadjointOrbitQuotientMap_coadjointOrbitForm hdφ ν ▸
      (Dual.isSymplectic_coadjointOrbitForm _).isNondegenerate)).2 x

/-- **The induced map of coadjoint orbits is a local diffeomorphism.** A surjective differential at
the identity suffices: `φ` need not be smooth or surjective. -/
theorem isLocalDiffeomorph_coadjointOrbitQuotientMap :
    IsLocalDiffeomorph
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (φ.coadjointOrbitQuotientMap hdφ ν) := fun x ↦
  isLocalDiffeomorphAt_of_injective_mfderiv (s := Set.univ)
    (φ.contMDiff_coadjointOrbitQuotientMap hdφ ν).contMDiffOn isOpen_univ
    (Set.mem_univ x) BoundarylessManifold.isInteriorPoint (by simp)
    (injective_mfderiv_coadjointOrbitQuotientMap φ hdφ ν x) (finrank_quotientModelSpace_eq φ hdφ ν)

/-! ### The diffeomorphism of coadjoint orbits -/

variable (hφ : Surjective
  ((QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) ∘ φ))

/-- **Coadjoint orbits along a homomorphism meeting every coset.** If the differential
`dφ : 𝔨 → 𝔤` of `φ : K →* G` at the identity is surjective and `φ` meets every coset of `G_ν`, for
instance if `φ` is surjective, then `[k] ↦ [φ k]` is a diffeomorphism from the coadjoint orbit
`K ⧸ K_{ν ∘ dφ}` of `ν ∘ dφ ∈ 𝔨*` onto the coadjoint orbit `G ⧸ G_ν` of `ν ∈ 𝔤*`. It pulls the
Kirillov–Kostant–Souriau form back to the Kirillov–Kostant–Souriau form
(`MonoidHom.mpullback_coadjointOrbitDiffeomorph_coadjointOrbitForm`). -/
def coadjointOrbitDiffeomorph :
    Diffeomorph
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (K ⧸ (coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap))
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) ∞ :=
  (φ.isLocalDiffeomorph_coadjointOrbitQuotientMap hdφ ν).diffeomorphOfBijective
    (φ.bijective_coadjointOrbitQuotientMap hdφ ν hφ)

/-- The diffeomorphism of coadjoint orbits is the map `[k] ↦ [φ k]` induced by `φ`. -/
theorem coe_coadjointOrbitDiffeomorph :
    ⇑(φ.coadjointOrbitDiffeomorph hdφ ν hφ) = φ.coadjointOrbitQuotientMap hdφ ν :=
  IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

/-- The diffeomorphism of coadjoint orbits sends the coset `[k]` to the coset `[φ k]`. -/
@[simp]
theorem coadjointOrbitDiffeomorph_mk (k : K) :
    φ.coadjointOrbitDiffeomorph hdφ ν hφ k =
      (φ k : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) := by
  rw [coe_coadjointOrbitDiffeomorph, coadjointOrbitQuotientMap_mk]

/-- The inverse of the diffeomorphism of coadjoint orbits sends the coset `[φ k]` to the coset
`[k]`. -/
@[simp]
theorem coadjointOrbitDiffeomorph_symm_mk (k : K) :
    (φ.coadjointOrbitDiffeomorph hdφ ν hφ).symm
        (φ k : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) = k := by
  rw [← φ.coadjointOrbitDiffeomorph_mk hdφ ν hφ k, Diffeomorph.symm_apply_apply]

/-- The diffeomorphism of coadjoint orbits is equivariant along `φ`:
`[φ (k k')] = φ k • [φ k']`. -/
@[simp]
theorem coadjointOrbitDiffeomorph_smul (k : K)
    (x : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
      (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)) :
    φ.coadjointOrbitDiffeomorph hdφ ν hφ (k • x) =
      φ k • φ.coadjointOrbitDiffeomorph hdφ ν hφ x := by
  rw [coe_coadjointOrbitDiffeomorph, coadjointOrbitQuotientMap_smul]

/-- **The diffeomorphism of coadjoint orbits intertwines the orbit maps.** The image in `𝔨*` of a
point `x` of the coadjoint orbit of `ν ∘ dφ` is the pullback along `dφ` of the image in `𝔤*` of the
corresponding point of the coadjoint orbit of `ν`: `Ad*_k (ν ∘ dφ) = (Ad*_{φ k} ν) ∘ dφ`. -/
@[simp]
theorem orbitMap_coadjointOrbitDiffeomorph_comp_groupLieAlgebraMap
    (x : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
      (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)) :
    ((coadjointRepresentation ℝ I G).orbitMap ν (φ.coadjointOrbitDiffeomorph hdφ ν hφ x)).comp
        (φ.groupLieAlgebraMap J I).toLinearMap =
      (coadjointRepresentation ℝ J K).orbitMap
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) x := by
  rw [coe_coadjointOrbitDiffeomorph, orbitMap_coadjointOrbitQuotientMap_comp_groupLieAlgebraMap]

/-- **The diffeomorphism of coadjoint orbits is a symplectomorphism.** It pulls the
Kirillov–Kostant–Souriau form of `G ⧸ G_ν` back to that of `K ⧸ K_{ν ∘ dφ}`. -/
@[simp]
theorem mpullback_coadjointOrbitDiffeomorph_coadjointOrbitForm :
    SmoothForm.mpullback (φ.coadjointOrbitDiffeomorph hdφ ν hφ)
        (φ.coadjointOrbitDiffeomorph hdφ ν hφ).contMDiff ν.coadjointOrbitForm =
      Dual.coadjointOrbitForm (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) := by
  -- The diffeomorphism is the induced map of coadjoint orbits, which is symplectic.
  simp_rw [coe_coadjointOrbitDiffeomorph]
  exact φ.mpullback_coadjointOrbitQuotientMap_coadjointOrbitForm hdφ ν

end MonoidHom
