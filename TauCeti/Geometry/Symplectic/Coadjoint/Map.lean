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

/-!
# Coadjoint orbits along homomorphisms and through covering homomorphisms

Let `φ : K →* G` be a homomorphism of real Lie groups with finite-dimensional boundaryless
models, with differential `dφ : 𝔨 → 𝔤` at the identity (`MonoidHom.groupLieAlgebraMap`), and let
`ν ∈ 𝔤*`. Pulling functionals back along `dφ` intertwines the coadjoint representations, so when
`dφ` is surjective the coadjoint stabilizer of `ν ∘ dφ` is `K_{ν ∘ dφ} = φ⁻¹(G_ν)`
(`MonoidHom.stabilizer_coadjointRepresentation_comp_groupLieAlgebraMap`). This file upgrades that
statement about orbits and stabilizers to the homogeneous symplectic manifolds `K ⧸ K_{ν ∘ dφ}` and
`G ⧸ G_ν` of `TauCeti.Geometry.Symplectic.Coadjoint.Orbit`.

**Along a homomorphism.** When `dφ` is surjective, `φ` induces the map of coadjoint orbits

`Φ : K ⧸ K_{ν ∘ dφ} → G ⧸ G_ν`, `[k] ↦ [φ k]`

(`MonoidHom.coadjointOrbitQuotientMap`). It is well defined and injective because
`K_{ν ∘ dφ} = φ⁻¹(G_ν)`, and surjective when `φ` is. It is smooth, and it

* pulls the Kirillov–Kostant–Souriau form `ω_ν` back to `ω_{ν ∘ dφ}`
  (`MonoidHom.mpullback_coadjointOrbitQuotientMap_coadjointOrbitForm`);
* is equivariant along `φ`, `Φ (k • x) = φ k • Φ x` (`MonoidHom.coadjointOrbitQuotientMap_smul`);
* intertwines the orbit maps: the point `Ad*_k (ν ∘ dφ)` of `𝔨*` is the pullback along `dφ` of the
  point `Ad*_{φ k} ν` of `𝔤*` (`MonoidHom.orbitMap_coadjointOrbitQuotientMap`).

No smoothness of `φ` is assumed: when `𝔤 ≠ 0`, the surjectivity of `dφ` makes `φ` differentiable
at the identity, hence continuous, hence smooth (`TauCeti.Lie.contMDiff_of_continuous_monoidHom`);
when `𝔤 = 0`, the orbit `G ⧸ G_ν` is a point. The form identity is checked on `K`: the KKS form is
characterized by its pullback to the group (`Module.Dual.eq_coadjointOrbitForm_iff`), and `φ` pulls
the left-invariant Kirillov form of `ν` back to that of `ν ∘ dφ`
(`Module.Dual.mpullback_leftInvariantKirillovForm`).

**Through a covering homomorphism.** If the smooth homomorphism `φ` is also surjective, then `Φ`
is a diffeomorphism

`K ⧸ K_{ν ∘ dφ} ≃ G ⧸ G_ν`

(`ContMDiffMonoidMorphism.coadjointOrbitDiffeomorph`). The two orbits have the same dimension,
since `[ξ] ↦ [dφ ξ]` identifies their tangent models `𝔨 ⧸ 𝔨_{ν ∘ dφ}` and `𝔤 ⧸ 𝔤_ν`, and the
differentials of `Φ` are onto, so it is a local diffeomorphism. The diffeomorphism is therefore a
symplectomorphism of the Kirillov–Kostant–Souriau forms
(`ContMDiffMonoidMorphism.mpullback_coadjointOrbitDiffeomorph_coadjointOrbitForm`).

The main example is a covering homomorphism `K → G = K ⧸ Γ` by a discrete central subgroup `Γ`,
such as `SU(2) → SO(3)`. Then `dφ` is bijective, the isotropy groups `K_{ν ∘ dφ} ⊇ Γ` and `G_ν`
differ, but the coadjoint orbits are the same symplectic manifolds. Injectivity of `dφ` is not
needed: the projection `G × L → G` of a product identifies the orbit of `(ν, 0)` with that of `ν`.

## Main definitions

* `MonoidHom.coadjointOrbitQuotientMap`: the map `K ⧸ K_{ν ∘ dφ} → G ⧸ G_ν`, `[k] ↦ [φ k]`.
* `ContMDiffMonoidMorphism.coadjointOrbitDiffeomorph`: the same map as a diffeomorphism, for
  `φ` smooth and surjective.

## Main results

* `MonoidHom.contMDiff_coadjointOrbitQuotientMap`: the induced map of coadjoint orbits is smooth.
* `MonoidHom.mpullback_coadjointOrbitQuotientMap_coadjointOrbitForm`: it pulls the KKS form of `ν`
  back to the KKS form of `ν ∘ dφ`.
* `MonoidHom.injective_coadjointOrbitQuotientMap`, `MonoidHom.bijective_coadjointOrbitQuotientMap`:
  it is injective, and bijective for a surjective homomorphism.
* `ContMDiffMonoidMorphism.mpullback_coadjointOrbitDiffeomorph_coadjointOrbitForm`: the
  diffeomorphism is a symplectomorphism of the Kirillov–Kostant–Souriau forms.
* `ContMDiffMonoidMorphism.orbitMap_coadjointRepresentation_comp_groupLieAlgebraMap`: it
  intertwines the orbit maps into `𝔨*` and `𝔤*`.

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
  (ν : Dual ℝ (GroupLieAlgebra I G))

/-! ### The induced map of coadjoint orbits -/

include hdφ in
/-- Two cosets of `K_{ν ∘ dφ}` agree exactly when their images under `φ` are equal cosets of
`G_ν`, since `K_{ν ∘ dφ} = φ⁻¹(G_ν)` when `dφ` is surjective. -/
private theorem quotientMk_eq_iff_map_quotientMk_eq (a b : K) :
    (a : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)) = b ↔
      (φ a : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) = φ b := by
  rw [QuotientGroup.eq, QuotientGroup.eq,
    φ.stabilizer_coadjointRepresentation_comp_groupLieAlgebraMap hdφ ν,
    Subgroup.mem_comap, map_mul, map_inv]

/-- **The map of coadjoint orbits induced by a homomorphism.** For `φ : K →* G` with surjective
differential `dφ` at the identity, the map `[k] ↦ [φ k]` from the coadjoint orbit
`K ⧸ K_{ν ∘ dφ}` of `ν ∘ dφ` to the coadjoint orbit `G ⧸ G_ν` of `ν`. It is well defined because
`K_{ν ∘ dφ} = φ⁻¹(G_ν)` (`MonoidHom.stabilizer_coadjointRepresentation_comp_groupLieAlgebraMap`). -/
def coadjointOrbitQuotientMap :
    K ⧸ (coadjointRepresentation ℝ J K).stabilizer (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) →
      G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν :=
  Quotient.lift (fun k : K ↦ (φ k : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν))
    fun a b hab ↦ (quotientMk_eq_iff_map_quotientMk_eq φ hdφ ν a b).1 (Quotient.sound hab)

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

/-- **The induced map of coadjoint orbits is equivariant along `φ`:** `[φ (k k')] = φ k • [φ k']`.
-/
theorem coadjointOrbitQuotientMap_smul (k : K)
    (x : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
      (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)) :
    φ.coadjointOrbitQuotientMap hdφ ν (k • x) = φ k • φ.coadjointOrbitQuotientMap hdφ ν x := by
  induction x using QuotientGroup.induction_on with
  | H a => rw [MulAction.Quotient.smul_coe, coadjointOrbitQuotientMap_mk,
      coadjointOrbitQuotientMap_mk, MulAction.Quotient.smul_coe, smul_eq_mul, smul_eq_mul, map_mul]

/-- **The induced map intertwines the orbit maps.** The image in `𝔨*` of a point `x` of the
coadjoint orbit of `ν ∘ dφ` is the pullback along `dφ` of the image in `𝔤*` of its image in the
coadjoint orbit of `ν`: `Ad*_k (ν ∘ dφ) = (Ad*_{φ k} ν) ∘ dφ`. -/
theorem orbitMap_coadjointOrbitQuotientMap
    (x : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
      (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)) :
    ((coadjointRepresentation ℝ I G).orbitMap ν (φ.coadjointOrbitQuotientMap hdφ ν x)).comp
        (φ.groupLieAlgebraMap J I).toLinearMap =
      (coadjointRepresentation ℝ J K).orbitMap
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) x := by
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [coadjointOrbitQuotientMap_mk, Representation.orbitMap_mk, Representation.orbitMap_mk]
    exact (φ.coadjointRepresentation_comp_groupLieAlgebraMap k ν).symm

/-- **The induced map of coadjoint orbits is injective**, since `K_{ν ∘ dφ}` is the full preimage
`φ⁻¹(G_ν)`. -/
theorem injective_coadjointOrbitQuotientMap :
    Injective (φ.coadjointOrbitQuotientMap hdφ ν) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with | H a =>
  induction y using QuotientGroup.induction_on with | H b =>
  rw [coadjointOrbitQuotientMap_mk, coadjointOrbitQuotientMap_mk] at hxy
  exact (quotientMk_eq_iff_map_quotientMk_eq φ hdφ ν a b).2 hxy

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

omit [I.Boundaryless] [J.Boundaryless] in
include hdφ in
/-- A homomorphism whose differential at the identity is surjective onto a nonzero Lie algebra is
smooth: it is differentiable, hence continuous, at the identity, so continuous, and continuous
homomorphisms of Lie groups are smooth. -/
private theorem contMDiff_of_surjective_groupLieAlgebraMap [Nontrivial E] :
    ContMDiff J I ∞ φ := by
  have hd : MDifferentiableAt J I φ 1 := by
    by_contra h
    obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
    obtain ⟨η, hη⟩ := hdφ ξ
    rw [groupLieAlgebraMap_apply, mfderiv_zero_of_not_mdifferentiableAt h] at hη
    exact hξ hη.symm
  have := topologicalGroup_of_lieGroup (G := K) J ∞
  have := topologicalGroup_of_lieGroup (G := G) I ∞
  exact Lie.contMDiff_of_continuous_monoidHom φ (continuous_of_continuousAt_one φ hd.continuousAt)

/-- The Kirillov–Kostant–Souriau form of the zero functional vanishes. -/
private theorem coadjointOrbitForm_eq_zero {μ : Dual ℝ (GroupLieAlgebra I G)}
    (hμ : μ = 0) : μ.coadjointOrbitForm = 0 := by
  subst hμ
  have hα : (0 : Dual ℝ (GroupLieAlgebra I G)).leftInvariantForm = 0 :=
    Subtype.ext <| funext fun g ↦ by
      ext v
      exact Dual.leftInvariantForm_apply _ g v
  rw [eq_comm, Dual.eq_coadjointOrbitForm_iff _
    (Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
      (0 : Dual ℝ (GroupLieAlgebra I G))).contMDiff,
    map_zero, Dual.leftInvariantKirillovForm_def, hα, map_zero, neg_zero]

/-- **The induced map of coadjoint orbits is smooth**, by descent along the submersion
`K → K ⧸ K_{ν ∘ dφ}`. -/
theorem contMDiff_coadjointOrbitQuotientMap :
    ContMDiff
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (φ.coadjointOrbitQuotientMap hdφ ν) :=
  ((Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
    (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)).contMDiff_comp_iff
      QuotientGroup.mk_surjective le_rfl).1 (by
      rw [coadjointOrbitQuotientMap_comp_mk]
      rcases subsingleton_or_nontrivial E with hE | hE
      · -- If `𝔤 = 0`, then `G_ν = G`, so the projection of `G` is constant.
        have : Subsingleton (GroupLieAlgebra I G) := hE
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
        (contMDiff_coadjointOrbitQuotientMap hdφ ν) ν.coadjointOrbitForm =
      Dual.coadjointOrbitForm (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- If `𝔤 = 0`, then `ν = 0` and `ν ∘ dφ = 0`, whose KKS forms vanish.
    have : Subsingleton (GroupLieAlgebra I G) := hE
    have hν : ν = 0 := Subsingleton.elim ν 0
    rw [coadjointOrbitForm_eq_zero hν, map_zero,
      coadjointOrbitForm_eq_zero (by rw [hν, LinearMap.zero_comp])]
  have hφ := contMDiff_of_surjective_groupLieAlgebraMap hdφ
  have hπK := (Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
    (ν.comp (φ.groupLieAlgebraMap J I).toLinearMap)).contMDiff
  have hπG := ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff
  -- Pulled back to `K`, both sides are `φ^* σ_ν = σ_{ν ∘ dφ}`.
  rw [Dual.eq_coadjointOrbitForm_iff _ hπK, SmoothForm.mpullback_mpullback_of_comp_eq hπK
    (contMDiff_coadjointOrbitQuotientMap hdφ ν) hφ hπG
    (φ.coadjointOrbitQuotientMap_comp_mk hdφ ν),
    Dual.mpullback_quotientMk_coadjointOrbitForm]
  exact ν.mpullback_leftInvariantKirillovForm ⟨φ, hφ⟩

end MonoidHom

namespace ContMDiffMonoidMorphism

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace HK] {J : ModelWithCorners ℝ F HK} [J.Boundaryless]
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup J ∞ K]
  (φ : ContMDiffMonoidMorphism J I ∞ K G) (hφ : Surjective φ)
  (hdφ : Surjective (φ.toMonoidHom.groupLieAlgebraMap J I)) (ν : Dual ℝ (GroupLieAlgebra I G))

/-! ### The orbits as symplectic manifolds -/

include hdφ in
/-- The coadjoint orbits `K ⧸ K_{ν ∘ dφ}` and `G ⧸ G_ν` have the same dimension: `[ξ] ↦ [dφ ξ]`
identifies their tangent models `𝔨 ⧸ 𝔨_{ν ∘ dφ}` and `𝔤 ⧸ 𝔤_ν`. -/
private theorem finrank_quotientModelSpace_eq :
    finrank ℝ (Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap))) =
      finrank ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) := by
  rw [Dual.finrank_quotientModelSpace_eq_finrank_quotient_lieAnnihilator,
    Dual.finrank_quotientModelSpace_eq_finrank_quotient_lieAnnihilator]
  exact (Dual.quotientLieAnnihilatorEquiv (f := φ.groupLieAlgebraLieHom)
    (ν := ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap) ν
    (by rwa [coe_groupLieAlgebraLieHom]) (by rw [toLinearMap_groupLieAlgebraLieHom])).finrank_eq

/-- The differentials of the map `[k] ↦ [φ k]` of coadjoint orbits are surjective. -/
private theorem surjective_mfderiv_coadjointOrbitQuotientMap
    (x : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
      (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)) :
    Surjective (mfderiv
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (φ.toMonoidHom.coadjointOrbitQuotientMap hdφ ν) x) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  have hπK := Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation (I := J) (G := K)
    (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)
  have hπG := ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
  -- Differentiate `Φ ∘ π_K = π_G ∘ φ` at `k`.
  have hcomp := mfderiv_comp k
    ((φ.toMonoidHom.contMDiff_coadjointOrbitQuotientMap hdφ ν).mdifferentiableAt (by simp))
    (hπK.contMDiff.mdifferentiableAt (by simp))
  have hcomp' := mfderiv_comp k (hπG.contMDiff.mdifferentiableAt (by simp))
    (φ.contMDiff_toFun.mdifferentiableAt (by simp))
  have hfun : φ.toMonoidHom.coadjointOrbitQuotientMap hdφ ν ∘ QuotientGroup.mk =
      QuotientGroup.mk ∘ φ :=
    funext (φ.toMonoidHom.coadjointOrbitQuotientMap_mk hdφ ν)
  rw [hfun] at hcomp
  intro w
  obtain ⟨u, rfl⟩ := hπG.surjective_mfderiv (by simp) (φ k) w
  obtain ⟨v, rfl⟩ := φ.surjective_mfderiv_of_surjective_groupLieAlgebraMap hdφ k u
  refine ⟨mfderiv J _ QuotientGroup.mk k v, ?_⟩
  exact congrArg (· v) (hcomp.symm.trans hcomp')

/-- The map `[k] ↦ [φ k]` of coadjoint orbits is a local diffeomorphism. -/
private theorem isLocalDiffeomorph_coadjointOrbitQuotientMap :
    IsLocalDiffeomorph
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (φ.toMonoidHom.coadjointOrbitQuotientMap hdφ ν) := fun x ↦
  TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv (s := Set.univ)
    (φ.toMonoidHom.contMDiff_coadjointOrbitQuotientMap hdφ ν).contMDiffOn isOpen_univ
    (Set.mem_univ x) BoundarylessManifold.isInteriorPoint (by simp)
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_quotientModelSpace_eq φ hdφ ν)).2
        (surjective_mfderiv_coadjointOrbitQuotientMap φ hdφ ν x))
    (finrank_quotientModelSpace_eq φ hdφ ν)

/-- **Coadjoint orbits through a covering homomorphism.** If the smooth homomorphism `φ : K → G`
and its differential `dφ : 𝔨 → 𝔤` at the identity are surjective, then `[k] ↦ [φ k]` is a
diffeomorphism from the coadjoint orbit `K ⧸ K_{ν ∘ dφ}` of `ν ∘ dφ ∈ 𝔨*` onto the coadjoint orbit
`G ⧸ G_ν` of `ν ∈ 𝔤*`. It pulls the Kirillov–Kostant–Souriau form back to the
Kirillov–Kostant–Souriau form
(`ContMDiffMonoidMorphism.mpullback_coadjointOrbitDiffeomorph_coadjointOrbitForm`). -/
def coadjointOrbitDiffeomorph :
    Diffeomorph
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (K ⧸ (coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap))
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) ∞ :=
  (isLocalDiffeomorph_coadjointOrbitQuotientMap φ hdφ ν).diffeomorphOfBijective
    (φ.toMonoidHom.bijective_coadjointOrbitQuotientMap hdφ ν hφ)

/-- The diffeomorphism of coadjoint orbits is the map `[k] ↦ [φ k]` induced by `φ`. -/
theorem coe_coadjointOrbitDiffeomorph :
    ⇑(φ.coadjointOrbitDiffeomorph hφ hdφ ν) = φ.toMonoidHom.coadjointOrbitQuotientMap hdφ ν :=
  IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

/-- The diffeomorphism of coadjoint orbits sends the coset `[k]` to the coset `[φ k]`. -/
@[simp]
theorem coadjointOrbitDiffeomorph_mk (k : K) :
    φ.coadjointOrbitDiffeomorph hφ hdφ ν k =
      (φ k : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) := by
  rw [coe_coadjointOrbitDiffeomorph, MonoidHom.coadjointOrbitQuotientMap_mk]
  rfl

/-- The inverse of the diffeomorphism of coadjoint orbits sends the coset `[φ k]` to the coset
`[k]`. -/
@[simp]
theorem coadjointOrbitDiffeomorph_symm_mk (k : K) :
    (φ.coadjointOrbitDiffeomorph hφ hdφ ν).symm
        (φ k : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) = k := by
  rw [← coadjointOrbitDiffeomorph_mk φ hφ hdφ ν k, Diffeomorph.symm_apply_apply]

/-- The diffeomorphism of coadjoint orbits is equivariant along `φ`:
`[φ (k k')] = φ k • [φ k']`. -/
theorem coadjointOrbitDiffeomorph_smul (k : K)
    (x : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
      (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)) :
    φ.coadjointOrbitDiffeomorph hφ hdφ ν (k • x) =
      φ k • φ.coadjointOrbitDiffeomorph hφ hdφ ν x := by
  rw [coe_coadjointOrbitDiffeomorph]
  exact φ.toMonoidHom.coadjointOrbitQuotientMap_smul hdφ ν k x

/-- **The diffeomorphism of coadjoint orbits intertwines the orbit maps.** The image in `𝔨*` of a
point `x` of the coadjoint orbit of `ν ∘ dφ` is the pullback along `dφ` of the image in `𝔤*` of the
corresponding point of the coadjoint orbit of `ν`: `Ad*_k (ν ∘ dφ) = (Ad*_{φ k} ν) ∘ dφ`. -/
theorem orbitMap_coadjointRepresentation_comp_groupLieAlgebraMap
    (x : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
      (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)) :
    (coadjointRepresentation ℝ J K).orbitMap
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap) x =
      ((coadjointRepresentation ℝ I G).orbitMap ν (φ.coadjointOrbitDiffeomorph hφ hdφ ν x)).comp
        (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap := by
  rw [coe_coadjointOrbitDiffeomorph]
  exact (φ.toMonoidHom.orbitMap_coadjointOrbitQuotientMap hdφ ν x).symm

/-- **The diffeomorphism of coadjoint orbits is a symplectomorphism.** It pulls the
Kirillov–Kostant–Souriau form of `G ⧸ G_ν` back to that of `K ⧸ K_{ν ∘ dφ}`. -/
@[simp]
theorem mpullback_coadjointOrbitDiffeomorph_coadjointOrbitForm :
    SmoothForm.mpullback (φ.coadjointOrbitDiffeomorph hφ hdφ ν)
        (φ.coadjointOrbitDiffeomorph hφ hdφ ν).contMDiff ν.coadjointOrbitForm =
      Dual.coadjointOrbitForm (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap) := by
  -- The diffeomorphism is the induced map of coadjoint orbits, which is symplectic.
  simp_rw [coe_coadjointOrbitDiffeomorph]
  exact φ.toMonoidHom.mpullback_coadjointOrbitQuotientMap_coadjointOrbitForm hdφ ν

end ContMDiffMonoidMorphism
