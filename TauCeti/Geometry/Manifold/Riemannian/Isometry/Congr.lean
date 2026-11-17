/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Topology

/-!
# Transporting the isometry group along a Riemannian isometry

A smooth Riemannian isometry `Φ : RiemannianIsometry I J M N` conjugates self-isometries of `M`
into self-isometries of `N` by `Ψ ↦ Φ ∘ Ψ ∘ Φ⁻¹`. Because this preserves composition, it is a
group isomorphism `Isom I M ≃* Isom J N` between the isometry groups built in
`TauCeti.Geometry.Manifold.Riemannian.Isometry.Group`. This file records that isomorphism,
`RiemannianIsometry.isomCongr`, its pointwise action, its functoriality with respect to
`RiemannianIsometry.refl`, `trans`, and `symm`, and its naturality against the forgetful
homomorphism `toDiff` into the self-diffeomorphism group through `Diffeomorph.diffCongr`.

For compact manifolds with locally compact model spaces, conjugation is continuous in the weak
Whitney topology inherited from diffeomorphisms (`TauCeti.RiemannianIsometryWeakWhitney`). Thus
`RiemannianIsometry.isomCongrContinuousMulEquiv` upgrades the algebraic isomorphism to a
homeomorphic group isomorphism.

The construction mirrors `Diffeomorph.diffCongr` (`TauCeti.Geometry.Diffeomorphism.Congr`) and
Mathlib's `Equiv.permCongr`.

## Main definitions

* `TauCeti.RiemannianIsometry.isomCongr Φ`: the group isomorphism `Isom I M ≃* Isom J N`
  conjugating by a smooth Riemannian isometry `Φ : RiemannianIsometry I J M N`.
* `TauCeti.RiemannianIsometry.isomCongrContinuousMulEquiv Φ`: the same conjugation as a
  homeomorphic group isomorphism for the weak Whitney topologies, when the manifolds are compact
  and their models locally compact.

## Main results

* `TauCeti.RiemannianIsometry.isomCongr_apply_apply`: pointwise action
  `isomCongr Φ Ψ y = Φ (Ψ (Φ.symm y))`.
* `TauCeti.RiemannianIsometry.isomCongr_refl`, `isomCongr_trans`, `isomCongr_symm`:
  functoriality on the groupoid of Riemannian isometries.
* `TauCeti.RiemannianIsometry.toDiff_comp_isomCongr` and
  `TauCeti.RiemannianIsometry.toDiff_isomCongr`: naturality against `Diffeomorph.diffCongr`.
* `TauCeti.RiemannianIsometry.continuous_isomCongr`: continuity in the weak Whitney topology.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, Chapter 2
  (isometries and isometry groups).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]

/-- Conjugation by a smooth Riemannian isometry `Φ : RiemannianIsometry I J M N` as a group
isomorphism between the isometry groups: `isomCongr Φ Ψ = Φ ∘ Ψ ∘ Φ⁻¹`. This is the Riemannian
analogue of `Diffeomorph.diffCongr` and `Equiv.permCongr`. -/
def isomCongr (Φ : RiemannianIsometry I J M N) : Isom I M ≃* Isom J N where
  toFun Ψ := (Φ.symm.trans Ψ).trans Φ
  invFun Θ := (Φ.trans Θ).trans Φ.symm
  left_inv Ψ := by
    ext x
    simp
  right_inv Θ := by
    ext y
    simp
  map_mul' Ψ₁ Ψ₂ := by
    ext y
    simp

/-- The conjugating isomorphism acts pointwise by `isomCongr Φ Ψ y = Φ (Ψ (Φ.symm y))`. -/
@[simp, grind =]
theorem isomCongr_apply_apply (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) (y : N) :
    isomCongr Φ Ψ y = Φ (Ψ (Φ.symm y)) := by
  simp [isomCongr]

/-- The underlying isometry of `isomCongr Φ Ψ` is `(Φ.symm.trans Ψ).trans Φ`. -/
theorem isomCongr_apply (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    isomCongr Φ Ψ = (Φ.symm.trans Ψ).trans Φ := by
  rfl

/-- The inverse of `isomCongr Φ Ψ` is `isomCongr Φ Ψ⁻¹`, since conjugation is a homomorphism. -/
theorem isomCongr_inv (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    (isomCongr Φ Ψ)⁻¹ = isomCongr Φ Ψ⁻¹ :=
  (map_inv (isomCongr Φ) Ψ).symm

/-- Conjugating by the identity isometry is the identity group isomorphism. -/
@[simp]
theorem isomCongr_refl :
    isomCongr (RiemannianIsometry.refl I M) = MulEquiv.refl (Isom I M) := by
  ext Ψ x
  simp

/-- Conjugation is functorial: conjugating by a composite isometry is the composite of the
conjugating isomorphisms. -/
@[simp]
theorem isomCongr_trans (Φ : RiemannianIsometry I J M N) (Φ' : RiemannianIsometry J K N P) :
    isomCongr (Φ.trans Φ') = (isomCongr Φ).trans (isomCongr Φ') := by
  ext Ψ z
  simp

/-- The isomorphism conjugating by `Φ.symm` is the inverse of the one conjugating by `Φ`. -/
@[simp, grind =]
theorem isomCongr_symm (Φ : RiemannianIsometry I J M N) :
    (isomCongr Φ).symm = isomCongr Φ.symm := by
  ext Θ x
  simp [isomCongr]

/-- Naturality of `isomCongr` against the forgetful homomorphism `toDiff` to self-diffeomorphisms,
as a commutative square of group homomorphisms intertwining `isomCongr` with
`Diffeomorph.diffCongr`. -/
theorem toDiff_comp_isomCongr (Φ : RiemannianIsometry I J M N) :
    toDiff.comp (isomCongr Φ).toMonoidHom =
      (Diffeomorph.diffCongr Φ.toDiffeomorph).toMonoidHom.comp toDiff := by
  ext Ψ y
  simp [Diffeomorph.diffCongr_apply_apply, coe_symm]

/-- Forgetting the metric condition sends `isomCongr Φ Ψ` to the conjugate `Diffeomorph.diffCongr`
of the underlying self-diffeomorphisms; the elementwise shadow of `toDiff_comp_isomCongr`. -/
theorem toDiff_isomCongr (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    toDiff (isomCongr Φ Ψ) = Diffeomorph.diffCongr Φ.toDiffeomorph (toDiff Ψ) :=
  DFunLike.congr_fun (toDiff_comp_isomCongr Φ) Ψ

section Topology

open scoped TauCeti.DiffeomorphWeakWhitney TauCeti.RiemannianIsometryWeakWhitney

variable [CompactSpace M] [CompactSpace N] [LocallyCompactSpace E] [LocallyCompactSpace F]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- Conjugation by a fixed Riemannian isometry is continuous for the weak Whitney topologies on
the isometry groups. -/
theorem continuous_isomCongr (Φ : RiemannianIsometry I J M N) :
    Continuous (isomCongr Φ) := by
  rw [continuous_weakWhitney_iff]
  have h : (fun Ψ : Isom I M ↦ (isomCongr Φ Ψ).toDiffeomorph) =
      (Diffeomorph.diffCongr Φ.toDiffeomorph) ∘ toDiffeomorph := by
    funext Ψ
    simpa [toDiff_apply] using toDiff_isomCongr Φ Ψ
  rw [h]
  exact (Diffeomorph.continuous_diffCongr Φ.toDiffeomorph).comp
    isEmbedding_toDiffeomorph.continuous

/-- A Riemannian isometry gives a homeomorphic group isomorphism between the weak-Whitney spaces
of self-isometries of its source and target by conjugation. -/
def isomCongrContinuousMulEquiv (Φ : RiemannianIsometry I J M N) :
    Isom I M ≃ₜ* Isom J N where
  toMulEquiv := isomCongr Φ
  continuous_toFun := continuous_isomCongr Φ
  continuous_invFun := (continuous_isomCongr Φ.symm).congr fun Θ ↦ by
    ext x
    simp [isomCongr]

/-- Topological conjugation applies the underlying algebraic conjugation. -/
@[simp]
theorem isomCongrContinuousMulEquiv_apply (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    isomCongrContinuousMulEquiv Φ Ψ = isomCongr Φ Ψ := by
  ext y
  simp [isomCongrContinuousMulEquiv]

/-- Conjugation by the identity isometry is the identity topological group isomorphism. -/
@[simp]
theorem isomCongrContinuousMulEquiv_refl :
    isomCongrContinuousMulEquiv (RiemannianIsometry.refl I M) =
      ContinuousMulEquiv.refl (Isom I M) := by
  ext Ψ x
  simp

/-- Topological conjugation is functorial under composition of Riemannian isometries. -/
@[simp]
theorem isomCongrContinuousMulEquiv_trans (Φ : RiemannianIsometry I J M N)
    (Φ' : RiemannianIsometry J K N P) [CompactSpace P] [LocallyCompactSpace G] [IsManifold K ∞ P] :
    isomCongrContinuousMulEquiv (Φ.trans Φ') =
      (isomCongrContinuousMulEquiv Φ).trans (isomCongrContinuousMulEquiv Φ') := by
  ext Ψ z
  simp

/-- The inverse topological group isomorphism conjugates by the inverse isometry. -/
@[simp]
theorem isomCongrContinuousMulEquiv_symm (Φ : RiemannianIsometry I J M N) :
    (isomCongrContinuousMulEquiv Φ).symm = isomCongrContinuousMulEquiv Φ.symm := by
  ext Θ
  have h : (isomCongrContinuousMulEquiv Φ).symm Θ = (isomCongr Φ).symm Θ := rfl
  rw [h, isomCongr_symm, isomCongrContinuousMulEquiv_apply]

end Topology

end TauCeti.RiemannianIsometry

end
