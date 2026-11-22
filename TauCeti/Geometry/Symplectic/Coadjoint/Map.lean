/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Map
public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit

import TauCeti.Geometry.Lie.Functor

/-!
# Coadjoint orbits as symplectic manifolds through a covering homomorphism

Let `φ : K → G` be a smooth homomorphism of real Lie groups with finite-dimensional boundaryless
models, with differential `dφ : 𝔨 → 𝔤` at the identity, and let `ν ∈ 𝔤*`. Pulling functionals back
along `dφ` intertwines the coadjoint representations, so when `dφ` is surjective the coadjoint
stabilizer of `ν ∘ dφ` is `K_{ν ∘ dφ} = φ⁻¹(G_ν)`
(`MonoidHom.stabilizer_coadjointRepresentation_comp_groupLieAlgebraMap`). This file upgrades that
statement about orbits and stabilizers to the homogeneous symplectic manifolds `K ⧸ K_{ν ∘ dφ}` and
`G ⧸ G_ν` of `TauCeti.Geometry.Symplectic.Coadjoint.Orbit`.

**On the groups.** For every smooth homomorphism `φ`, the left-invariant one-form and the
left-invariant Kirillov form of `ν` on `G` pull back along `φ` to those of `ν ∘ dφ` on `K`
(`ContMDiffMonoidMorphism.mpullback_leftInvariantForm`,
`ContMDiffMonoidMorphism.mpullback_leftInvariantKirillovForm`), because `φ` carries the
left-invariant vector field of `ξ` to that of `dφ ξ`.

**On the orbits.** If `φ` and `dφ` are both surjective, then `[k] ↦ [φ k]` is a diffeomorphism

`K ⧸ K_{ν ∘ dφ} ≃ G ⧸ G_ν`

(`ContMDiffMonoidMorphism.coadjointOrbitDiffeomorph`). It is well defined and injective because
`K_{ν ∘ dφ} = φ⁻¹(G_ν)`, and surjective because `φ` is. The two orbits have the same dimension,
since `[ξ] ↦ [dφ ξ]` identifies their tangent models `𝔨 ⧸ 𝔨_{ν ∘ dφ}` and `𝔤 ⧸ 𝔤_ν`, and its
differentials are onto, so it is a local diffeomorphism. The diffeomorphism

* pulls the Kirillov–Kostant–Souriau form of `G ⧸ G_ν` back to that of `K ⧸ K_{ν ∘ dφ}`
  (`ContMDiffMonoidMorphism.mpullback_coadjointOrbitDiffeomorph_coadjointOrbitForm`);
* is equivariant along `φ`, `[φ (k k')] = φ k • [φ k']`
  (`ContMDiffMonoidMorphism.coadjointOrbitDiffeomorph_smul`);
* intertwines the orbit maps: the point `Ad*_k (ν ∘ dφ)` of `𝔨*` is the pullback along `dφ` of the
  point `Ad*_{φ k} ν` of `𝔤*`
  (`ContMDiffMonoidMorphism.orbitMap_coadjointRepresentation_comp_groupLieAlgebraMap`).

The main example is a covering homomorphism `K → G = K ⧸ Γ` by a discrete central subgroup `Γ`,
such as `SU(2) → SO(3)`. Then `dφ` is bijective, the isotropy groups `K_{ν ∘ dφ} ⊇ Γ` and `G_ν`
differ, but the coadjoint orbits are the same symplectic manifolds. Injectivity of `dφ` is not
needed: the projection `G × L → G` of a product identifies the orbit of `(ν, 0)` with that of `ν`.

## Main definitions

* `ContMDiffMonoidMorphism.coadjointOrbitDiffeomorph`: the diffeomorphism
  `K ⧸ K_{ν ∘ dφ} ≃ G ⧸ G_ν`, `[k] ↦ [φ k]`.

## Main results

* `ContMDiffMonoidMorphism.mpullback_leftInvariantKirillovForm`: `φ^* σ_ν = σ_{ν ∘ dφ}`.
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

namespace ContMDiffMonoidMorphism

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace HK] {J : ModelWithCorners ℝ F HK}
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup J ∞ K]
  (φ : ContMDiffMonoidMorphism J I ∞ K G)

/-! ### The Kirillov forms on the groups -/

/-- **The left-invariant one-form along a homomorphism.** A smooth homomorphism `φ : K → G` pulls
the left-invariant one-form of `ν ∈ 𝔤*` back to the left-invariant one-form of `ν ∘ dφ ∈ 𝔨*`. -/
@[simp]
theorem mpullback_leftInvariantForm (ν : Dual ℝ (GroupLieAlgebra I G)) :
    SmoothForm.mpullback φ φ.contMDiff_toFun ν.leftInvariantForm =
      Dual.leftInvariantForm (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap) := by
  apply Subtype.ext
  funext k
  ext v
  obtain ⟨ξ, hξ⟩ := exists_mulInvariantVectorField_eq (v 0)
  rw [SmoothForm.coe_mpullback, TauCeti.mpullback_apply, Dual.leftInvariantForm_apply,
    Dual.leftInvariantForm_apply, ← hξ, φ.mfderiv_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField, mfderiv_inv_mul_mulInvariantVectorField,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe]

/-- **The left-invariant Kirillov form along a homomorphism.** A smooth homomorphism `φ : K → G`
pulls the left-invariant Kirillov form `σ_ν` of `ν ∈ 𝔤*` back to the left-invariant Kirillov form
`σ_{ν ∘ dφ}` of `ν ∘ dφ ∈ 𝔨*`. -/
@[simp]
theorem mpullback_leftInvariantKirillovForm (ν : Dual ℝ (GroupLieAlgebra I G)) :
    SmoothForm.mpullback φ φ.contMDiff_toFun ν.leftInvariantKirillovForm =
      Dual.leftInvariantKirillovForm
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap) := by
  rw [Dual.leftInvariantKirillovForm_def, Dual.leftInvariantKirillovForm_def, map_neg,
    ← SmoothForm.mextDerivₗ_mpullback, mpullback_leftInvariantForm]

/-! ### The orbit map along a homomorphism -/

variable [I.Boundaryless] [J.Boundaryless] (hφ : Surjective φ)
  (hdφ : Surjective (φ.toMonoidHom.groupLieAlgebraMap J I)) (ν : Dual ℝ (GroupLieAlgebra I G))

include hdφ in
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless] in
/-- Two cosets of `K_{ν ∘ dφ}` agree exactly when their images under `φ` are equal cosets of
`G_ν`, since `K_{ν ∘ dφ} = φ⁻¹(G_ν)` when `dφ` is surjective. -/
private theorem quotientMk_eq_iff_map_quotientMk_eq (a b : K) :
    (a : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)) = b ↔
      (φ a : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) = φ b := by
  rw [QuotientGroup.eq, QuotientGroup.eq,
    φ.toMonoidHom.stabilizer_coadjointRepresentation_comp_groupLieAlgebraMap hdφ ν,
    Subgroup.mem_comap, map_mul, map_inv]
  -- `φ.toMonoidHom` and `φ` have the same underlying function.
  rfl

/-- The map `[k] ↦ [φ k]` from the coadjoint orbit `K ⧸ K_{ν ∘ dφ}` to `G ⧸ G_ν`, well defined
because `K_{ν ∘ dφ} = φ⁻¹(G_ν)` when `dφ` is surjective. -/
private def orbitQuotientMap :
    K ⧸ (coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap) →
      G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν :=
  Quotient.lift (fun k : K ↦ (φ k : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν))
    fun a b hab ↦ (quotientMk_eq_iff_map_quotientMk_eq φ hdφ ν a b).1 (Quotient.sound hab)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless] in
private theorem orbitQuotientMap_mk (k : K) :
    orbitQuotientMap φ hdφ ν k = (φ k : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  (rfl)

/-- The map `[k] ↦ [φ k]` of coadjoint orbits is smooth, since composed with the submersion
`K → K ⧸ K_{ν ∘ dφ}` it is the smooth map `k ↦ [φ k]`. -/
private theorem contMDiff_orbitQuotientMap :
    ContMDiff
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (orbitQuotientMap φ hdφ ν) :=
  ((Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation _).contMDiff_comp_iff
    QuotientGroup.mk_surjective le_rfl).1
    ((ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation).contMDiff.comp
      φ.contMDiff_toFun)

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
private theorem surjective_mfderiv_orbitQuotientMap
    (x : K ⧸ (coadjointRepresentation ℝ J K).stabilizer
      (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)) :
    Surjective (mfderiv
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (orbitQuotientMap φ hdφ ν) x) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  have hπK := Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation (I := J) (G := K)
    (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)
  have hπG := ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation
  -- Differentiate `orbitQuotientMap ∘ π_K = π_G ∘ φ` at `k`.
  have hcomp := mfderiv_comp k
    ((contMDiff_orbitQuotientMap φ hdφ ν).mdifferentiableAt (by simp))
    (hπK.contMDiff.mdifferentiableAt (by simp))
  have hcomp' := mfderiv_comp k (hπG.contMDiff.mdifferentiableAt (by simp))
    (φ.contMDiff_toFun.mdifferentiableAt (by simp))
  have hfun : orbitQuotientMap φ hdφ ν ∘ QuotientGroup.mk = QuotientGroup.mk ∘ φ :=
    funext (orbitQuotientMap_mk φ hdφ ν)
  rw [hfun] at hcomp
  intro w
  obtain ⟨u, rfl⟩ := hπG.surjective_mfderiv (by simp) (φ k) w
  obtain ⟨v, rfl⟩ := φ.surjective_mfderiv_of_surjective_groupLieAlgebraMap hdφ k u
  refine ⟨mfderiv J _ QuotientGroup.mk k v, ?_⟩
  exact congrArg (· v) (hcomp.symm.trans hcomp')

/-- The map `[k] ↦ [φ k]` of coadjoint orbits is a local diffeomorphism. -/
private theorem isLocalDiffeomorph_orbitQuotientMap :
    IsLocalDiffeomorph
      𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer
        (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (orbitQuotientMap φ hdφ ν) := fun x ↦
  TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv (s := Set.univ)
    (contMDiff_orbitQuotientMap φ hdφ ν).contMDiffOn isOpen_univ (Set.mem_univ x)
    BoundarylessManifold.isInteriorPoint (by simp)
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_quotientModelSpace_eq φ hdφ ν)).2 (surjective_mfderiv_orbitQuotientMap φ hdφ ν x))
    (finrank_quotientModelSpace_eq φ hdφ ν)

include hφ in
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless] in
/-- The map `[k] ↦ [φ k]` of coadjoint orbits is bijective when `φ` is surjective. -/
private theorem bijective_orbitQuotientMap :
    Bijective (orbitQuotientMap φ hdφ ν) := by
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · induction x using QuotientGroup.induction_on with | H a =>
    induction y using QuotientGroup.induction_on with | H b =>
    rw [orbitQuotientMap_mk, orbitQuotientMap_mk] at hxy
    exact (quotientMk_eq_iff_map_quotientMk_eq φ hdφ ν a b).2 hxy
  · induction y using QuotientGroup.induction_on with | H g =>
    obtain ⟨k, rfl⟩ := hφ g
    exact ⟨k, orbitQuotientMap_mk φ hdφ ν k⟩

/-! ### The orbits as symplectic manifolds -/

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
  (isLocalDiffeomorph_orbitQuotientMap φ hdφ ν).diffeomorphOfBijective
    (bijective_orbitQuotientMap φ hφ hdφ ν)

/-- The diffeomorphism of coadjoint orbits sends the coset `[k]` to the coset `[φ k]`. -/
@[simp]
theorem coadjointOrbitDiffeomorph_mk (k : K) :
    φ.coadjointOrbitDiffeomorph hφ hdφ ν k =
      (φ k : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) := by
  rw [coadjointOrbitDiffeomorph, IsLocalDiffeomorph.coe_diffeomorphOfBijective,
    orbitQuotientMap_mk]

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
  induction x using QuotientGroup.induction_on with
  | H k' => rw [MulAction.Quotient.smul_coe, coadjointOrbitDiffeomorph_mk,
      coadjointOrbitDiffeomorph_mk, smul_eq_mul, map_mul, MulAction.Quotient.smul_coe, smul_eq_mul]

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
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [coadjointOrbitDiffeomorph_mk, Representation.orbitMap_mk, Representation.orbitMap_mk]
    -- The coercion of `φ` to a function is that of `φ.toMonoidHom` by definition.
    exact φ.toMonoidHom.coadjointRepresentation_comp_groupLieAlgebraMap k ν

/-- **The diffeomorphism of coadjoint orbits is a symplectomorphism.** It pulls the
Kirillov–Kostant–Souriau form of `G ⧸ G_ν` back to that of `K ⧸ K_{ν ∘ dφ}`. -/
@[simp]
theorem mpullback_coadjointOrbitDiffeomorph_coadjointOrbitForm :
    SmoothForm.mpullback (φ.coadjointOrbitDiffeomorph hφ hdφ ν)
        (φ.coadjointOrbitDiffeomorph hφ hdφ ν).contMDiff ν.coadjointOrbitForm =
      Dual.coadjointOrbitForm (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap) := by
  have hπK := (Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation (I := J) (G := K)
    (ν.comp (φ.toMonoidHom.groupLieAlgebraMap J I).toLinearMap)).contMDiff
  have hπG := ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff
  -- Pulled back to `K`, both sides are `φ^* σ_ν = σ_{ν ∘ dφ}`.
  rw [Dual.eq_coadjointOrbitForm_iff _ hπK, SmoothForm.mpullback_mpullback_of_comp_eq hπK
    (φ.coadjointOrbitDiffeomorph hφ hdφ ν).contMDiff φ.contMDiff_toFun hπG
    (funext fun k ↦ coadjointOrbitDiffeomorph_mk φ hφ hdφ ν k),
    Dual.mpullback_quotientMk_coadjointOrbitForm]
  exact φ.mpullback_leftInvariantKirillovForm ν

end ContMDiffMonoidMorphism
