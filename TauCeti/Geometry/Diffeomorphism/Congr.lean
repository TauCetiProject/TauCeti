/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Diffeomorphism.Topology
public import TauCeti.Topology.Algebra.Homeomorph.Congr
import TauCeti.Geometry.Diffeomorphism.Composition

/-!
# Transporting the self-diffeomorphism group along a diffeomorphism

A diffeomorphism `e : M ≃ₘ^n⟮I, J⟯ N` conjugates self-diffeomorphisms of `M` into
self-diffeomorphisms of `N` by `φ ↦ e ∘ φ ∘ e⁻¹`. Because this preserves composition, it is a
group isomorphism `Diff I M n ≃* Diff J N n` between the self-diffeomorphism groups built in
`TauCeti.Geometry.Diffeomorphism.Group`. This file records that isomorphism,
`Diffeomorph.diffCongr`, its pointwise action, and its functoriality: it is the identity on
`Diffeomorph.refl`, respects `Diffeomorph.trans` and `Diffeomorph.symm`, and commutes with the
forgetful homomorphism to the permutation group (`Diffeomorph.toPerm`) through Mathlib's
`Equiv.permCongr`.

For compact manifolds with locally compact model spaces, conjugation is continuous in the weak
Whitney topology: composition on either side by the fixed diffeomorphisms `e` and `e.symm` is
continuous. Thus `Diffeomorph.diffCongrContinuousMulEquiv` upgrades the algebraic isomorphism to
a homeomorphic group isomorphism. In particular, homotopy invariants of diffeomorphism groups do
not depend on replacing a manifold by a diffeomorphic model. The construction works for every
smoothness exponent `n`; when the manifolds are Hausdorff, the existing instances make its source
and target topological groups.

The construction is the diffeomorphism analogue of `Equiv.permCongr`
(`Mathlib/Logic/Equiv/Defs.lean`), the conjugation isomorphism of permutation groups, and reuses it
for the naturality statement.

## Main definitions

* `Diffeomorph.diffCongr e`: the group isomorphism `Diff I M n ≃* Diff J N n` conjugating by
  a diffeomorphism `e : M ≃ₘ^n⟮I, J⟯ N`.
* `Diffeomorph.diffCongrContinuousMulEquiv e`: the same conjugation as a homeomorphic group
  isomorphism for the weak Whitney topologies, when the manifolds are compact and their models
  locally compact.

The analogous self-homeomorphism-group isomorphism `Homeomorph.homeoCongr`, the target of
the forgetful naturality below, lives in `TauCeti.Topology.Algebra.Homeomorph.Congr`.

## Main results

* `Diffeomorph.diffCongr_apply_apply`: the pointwise action
  `diffCongr e φ x = e (φ (e.symm x))`.
* `Diffeomorph.diffCongr_refl`: conjugating by the identity is the identity isomorphism.
* `Diffeomorph.diffCongr_trans`: `diffCongr` turns `Diffeomorph.trans` into
  `MulEquiv.trans`, so it is functorial on the groupoid of diffeomorphisms.
* `Diffeomorph.diffCongr_symm`: the inverse isomorphism conjugates by `e.symm`.
* `Diffeomorph.toHomeomorphHom_comp_diffCongr` and
  `Diffeomorph.toPerm_comp_diffCongr`: naturality of `diffCongr` against the forgetful
  homomorphisms `toHomeomorphHom` and `toPerm`, as commutative squares of group homomorphisms
  intertwining `diffCongr` with `Homeomorph.homeoCongr` and `Equiv.permCongrHom` respectively.
* `Diffeomorph.toHomeomorph_diffCongr` and `Diffeomorph.toPerm_diffCongr`: the
  elementwise shadows of those squares.
* `Diffeomorph.continuous_diffCongr`: conjugation is continuous in the weak Whitney topology.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E'' H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω}

namespace Diffeomorph

/-- Conjugation by a diffeomorphism `e : M ≃ₘ^n⟮I, J⟯ N` as a group isomorphism between the
self-diffeomorphism groups: `diffCongr e φ = e ∘ φ ∘ e⁻¹`. This is the diffeomorphism analogue of
`Equiv.permCongr` and expresses that diffeomorphic manifolds have isomorphic self-diffeomorphism
groups. -/
def diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) : (M ≃ₘ^n⟮I, I⟯ M) ≃* (N ≃ₘ^n⟮J, J⟯ N) where
  toFun φ := (e.symm.trans φ).trans e
  invFun ψ := (e.trans ψ).trans e.symm
  left_inv φ := by
    ext x
    simp [Diffeomorph.coe_trans]
  right_inv ψ := by
    ext x
    simp [Diffeomorph.coe_trans]
  map_mul' φ ψ := by
    ext x
    simp [mul_def, Diffeomorph.coe_trans]

/-- The conjugating isomorphism acts pointwise by `diffCongr e φ x = e (φ (e.symm x))`. -/
@[simp, grind =]
theorem diffCongr_apply_apply (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) (x : N) :
    diffCongr e φ x = e (φ (e.symm x)) := (rfl)

/-- The underlying diffeomorphism of `diffCongr e φ` is `e ∘ φ ∘ e⁻¹`. -/
theorem diffCongr_apply (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    diffCongr e φ = (e.symm.trans φ).trans e := (rfl)

/-- The inverse of `diffCongr e φ` is `diffCongr e φ⁻¹`, since conjugation is a homomorphism. -/
theorem diffCongr_inv (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    (diffCongr e φ)⁻¹ = diffCongr e φ⁻¹ := (map_inv (diffCongr e) φ).symm

/-- Conjugating by the identity diffeomorphism is the identity isomorphism. -/
@[simp]
theorem diffCongr_refl :
    diffCongr (Diffeomorph.refl I M n) = MulEquiv.refl (M ≃ₘ^n⟮I, I⟯ M) := by
  ext φ x
  simp

/-- Conjugation is functorial: conjugating by a composite diffeomorphism is the composite of the
conjugating isomorphisms. -/
@[simp]
theorem diffCongr_trans (e : M ≃ₘ^n⟮I, J⟯ N) (e' : N ≃ₘ^n⟮J, K⟯ P) :
    diffCongr (e.trans e') = (diffCongr e).trans (diffCongr e') := by
  ext φ x
  simp [Diffeomorph.coe_trans, Diffeomorph.symm_trans']

/-- The isomorphism conjugating by `e.symm` is the inverse of the one conjugating by `e`. -/
@[simp, grind =]
theorem diffCongr_symm (e : M ≃ₘ^n⟮I, J⟯ N) : (diffCongr e).symm = diffCongr e.symm := by
  ext ψ x
  rfl

/-- Naturality of `diffCongr` against the forgetful homomorphism to self-homeomorphisms, as a
commutative square of group homomorphisms: conjugating diffeomorphisms by `e` and then forgetting
smoothness equals forgetting smoothness and then conjugating homeomorphisms by `e` through
`Homeomorph.homeoCongr`. This is the naturality of `diffCongr` against the stronger forgetful
homomorphism `Diffeomorph.toHomeomorphHom`, refining `toPerm_comp_diffCongr`. -/
theorem toHomeomorphHom_comp_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) :
    toHomeomorphHom.comp (diffCongr e).toMonoidHom =
      (Homeomorph.homeoCongr e.toHomeomorph).toMonoidHom.comp toHomeomorphHom := by
  ext φ x
  simp [toHomeomorphHom_apply]

/-- Naturality of `diffCongr` against the forgetful homomorphism to permutations, as a commutative
square of group homomorphisms intertwining `diffCongr` with `Equiv.permCongrHom`; this is the
`toPerm`-level shadow of `toHomeomorphHom_comp_diffCongr`. -/
theorem toPerm_comp_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) :
    toPerm.comp (diffCongr e).toMonoidHom = e.toEquiv.permCongrHom.toMonoidHom.comp toPerm := by
  ext φ x
  simp [Equiv.permCongr_apply]

/-- Forgetting only smoothness (keeping the topology) sends `diffCongr e φ` to the conjugate
`homeoCongr` of the underlying self-homeomorphisms; the elementwise shadow of
`toHomeomorphHom_comp_diffCongr`. -/
theorem toHomeomorph_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    (diffCongr e φ).toHomeomorph = e.toHomeomorph.homeoCongr φ.toHomeomorph := by
  have h := DFunLike.congr_fun (toHomeomorphHom_comp_diffCongr e) φ
  simpa using h

/-- Forgetting all topology intertwines `diffCongr` with `Equiv.permCongr` on the permutation
groups; the elementwise shadow of `toPerm_comp_diffCongr`. -/
theorem toPerm_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    toPerm (diffCongr e φ) = e.toEquiv.permCongr (toPerm φ) := by
  have h := DFunLike.congr_fun (toPerm_comp_diffCongr e) φ
  simpa using h

section Topology

open scoped TauCeti.DiffeomorphWeakWhitney

variable [CompactSpace M] [CompactSpace N] [LocallyCompactSpace E] [LocallyCompactSpace E']
  [IsManifold I n M] [IsManifold J n N]

/-- Conjugation by a fixed diffeomorphism is continuous for the weak Whitney topologies on the
self-diffeomorphism groups. -/
theorem continuous_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) : Continuous (diffCongr e) := by
  have hleft : Continuous fun φ : M ≃ₘ^n⟮I, I⟯ M ↦ e.symm.trans φ :=
    continuous_trans.comp (continuous_const.prodMk continuous_id)
  have hright : Continuous fun ψ : N ≃ₘ^n⟮J, I⟯ M ↦ ψ.trans e :=
    continuous_trans.comp (continuous_id.prodMk continuous_const)
  exact hright.comp hleft

/-- A diffeomorphism gives a homeomorphic group isomorphism between the weak-Whitney spaces of
self-diffeomorphisms of its source and target by conjugation. -/
def diffCongrContinuousMulEquiv (e : M ≃ₘ^n⟮I, J⟯ N) :
    (M ≃ₘ^n⟮I, I⟯ M) ≃ₜ* (N ≃ₘ^n⟮J, J⟯ N) where
  toMulEquiv := diffCongr e
  continuous_toFun := continuous_diffCongr e
  continuous_invFun :=
    (continuous_diffCongr e.symm).congr fun _ ↦ (rfl)

/-- Topological conjugation applies the underlying algebraic conjugation. -/
@[simp]
theorem diffCongrContinuousMulEquiv_apply (e : M ≃ₘ^n⟮I, J⟯ N)
    (φ : M ≃ₘ^n⟮I, I⟯ M) : diffCongrContinuousMulEquiv e φ = diffCongr e φ :=
  (rfl)

/-- Conjugation by the identity diffeomorphism is the identity topological group isomorphism. -/
@[simp]
theorem diffCongrContinuousMulEquiv_refl :
    diffCongrContinuousMulEquiv (Diffeomorph.refl I M n) =
      ContinuousMulEquiv.refl (M ≃ₘ^n⟮I, I⟯ M) := by
  ext φ x
  simp

/-- Topological conjugation is functorial under composition of diffeomorphisms. -/
@[simp]
theorem diffCongrContinuousMulEquiv_trans (e : M ≃ₘ^n⟮I, J⟯ N)
    (e' : N ≃ₘ^n⟮J, K⟯ P) [CompactSpace P] [LocallyCompactSpace E''] [IsManifold K n P] :
    diffCongrContinuousMulEquiv (e.trans e') =
      (diffCongrContinuousMulEquiv e).trans (diffCongrContinuousMulEquiv e') := by
  ext φ x
  simp

/-- The inverse topological group isomorphism conjugates by the inverse diffeomorphism. -/
@[simp]
theorem diffCongrContinuousMulEquiv_symm (e : M ≃ₘ^n⟮I, J⟯ N) :
    (diffCongrContinuousMulEquiv e).symm = diffCongrContinuousMulEquiv e.symm := by
  ext ψ x
  rfl

end Topology

end Diffeomorph
