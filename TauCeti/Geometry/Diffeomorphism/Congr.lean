/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group

/-!
# Transporting the self-diffeomorphism group along a diffeomorphism

A diffeomorphism `e : M ≃ₘ^n⟮I, J⟯ N` conjugates self-diffeomorphisms of `M` into
self-diffeomorphisms of `N` by `φ ↦ e ∘ φ ∘ e⁻¹`. Because this preserves composition, it is a
group isomorphism `Diff I M n ≃* Diff J N n` between the self-diffeomorphism groups built in
`TauCeti.Geometry.Diffeomorphism.Group`. This file records that isomorphism, `Diffeomorph.congr`,
its pointwise action, and its functoriality: it is the identity on `Diffeomorph.refl`, respects
`Diffeomorph.trans` and `Diffeomorph.symm`, and commutes with the forgetful homomorphism to the
permutation group (`Diffeomorph.toPerm`) through Mathlib's `Equiv.permCongr`.

This is the sense in which the group object of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3, "diffeomorphism groups with the C^∞
topology") is a diffeomorphism invariant: diffeomorphic manifolds have isomorphic
self-diffeomorphism groups, so the homotopy-type statements the layer targets — the Smale
conjecture `Diff(S³) ≃ O(4)`, `[Kir97, Problem 4.34]`, and Watanabe's `π_k(Diff(D⁴, ∂))` classes,
`[Kir97, Problem 4.126]` — transport along a chosen diffeomorphism of the underlying manifold. The
construction is purely algebraic and stops at the bare group isomorphism; the `C^∞` topology making
it a topological-group isomorphism is a separate, later layer-3 deliverable. It works for every
smoothness exponent `n`.

The construction is the diffeomorphism analogue of `Equiv.permCongr`
(`Mathlib/Logic/Equiv/Defs.lean`), the conjugation isomorphism of permutation groups, and reuses it
for the naturality statement.

## Main definitions

* `TauCeti.Diffeomorph.congr e`: the group isomorphism `Diff I M n ≃* Diff J N n` conjugating by a
  diffeomorphism `e : M ≃ₘ^n⟮I, J⟯ N`.

## Main results

* `TauCeti.Diffeomorph.congr_apply_apply`: the pointwise action `congr e φ x = e (φ (e.symm x))`.
* `TauCeti.Diffeomorph.congr_refl`: conjugating by the identity is the identity isomorphism.
* `TauCeti.Diffeomorph.congr_trans`: `congr` turns `Diffeomorph.trans` into `MulEquiv.trans`, so it
  is functorial on the groupoid of diffeomorphisms.
* `TauCeti.Diffeomorph.congr_symm`: the inverse isomorphism conjugates by `e.symm`.
* `TauCeti.Diffeomorph.toPerm_congr`: the forgetful homomorphism to the permutation group
  intertwines `congr` with `Equiv.permCongr`.
-/

public section

namespace TauCeti

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
self-diffeomorphism groups: `congr e φ = e ∘ φ ∘ e⁻¹`. This is the diffeomorphism analogue of
`Equiv.permCongr` and expresses that diffeomorphic manifolds have isomorphic self-diffeomorphism
groups. -/
@[expose] def congr (e : M ≃ₘ^n⟮I, J⟯ N) : (M ≃ₘ^n⟮I, I⟯ M) ≃* (N ≃ₘ^n⟮J, J⟯ N) where
  toFun φ := (e.symm.trans φ).trans e
  invFun ψ := (e.trans ψ).trans e.symm
  left_inv φ := by
    ext x
    simp [_root_.Diffeomorph.coe_trans]
  right_inv ψ := by
    ext x
    simp [_root_.Diffeomorph.coe_trans]
  map_mul' φ ψ := by
    ext x
    simp [mul_def, _root_.Diffeomorph.coe_trans]

/-- The conjugating isomorphism acts pointwise by `congr e φ x = e (φ (e.symm x))`. -/
@[simp]
theorem congr_apply_apply (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) (x : N) :
    congr e φ x = e (φ (e.symm x)) := rfl

/-- The underlying diffeomorphism of `congr e φ` is `e ∘ φ ∘ e⁻¹`. -/
theorem congr_apply (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    congr e φ = (e.symm.trans φ).trans e := rfl

/-- The inverse of `congr e φ` is `congr e φ⁻¹`, since conjugation is a homomorphism. -/
theorem congr_inv (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    (congr e φ)⁻¹ = congr e φ⁻¹ := (map_inv (congr e) φ).symm

/-- Conjugating by the identity diffeomorphism is the identity isomorphism. -/
@[simp]
theorem congr_refl : congr (_root_.Diffeomorph.refl I M n) = MulEquiv.refl (M ≃ₘ^n⟮I, I⟯ M) := by
  ext φ x
  simp

/-- Conjugation is functorial: conjugating by a composite diffeomorphism is the composite of the
conjugating isomorphisms. -/
@[simp]
theorem congr_trans (e : M ≃ₘ^n⟮I, J⟯ N) (e' : N ≃ₘ^n⟮J, K⟯ P) :
    congr (e.trans e') = (congr e).trans (congr e') := by
  ext φ x
  simp [_root_.Diffeomorph.coe_trans, _root_.Diffeomorph.symm_trans']

/-- The isomorphism conjugating by `e.symm` is the inverse of the one conjugating by `e`. -/
@[simp]
theorem congr_symm (e : M ≃ₘ^n⟮I, J⟯ N) : (congr e).symm = congr e.symm := by
  ext ψ x
  rfl

/-- Forgetting smoothness intertwines `congr` with `Equiv.permCongr` on the permutation groups. -/
theorem toPerm_congr (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    toPerm (congr e φ) = e.toEquiv.permCongr (toPerm φ) := by
  ext x
  simp [toPerm, Equiv.permCongr_apply]

end Diffeomorph

end TauCeti
