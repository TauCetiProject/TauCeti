/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FiberTransport

/-!
# Stabilizers of deck actions on fibres

This file records the stabilizer bookkeeping for the restricted action of `Deck p` on one
fibre of a map `p : E → B`. It is deliberately a thin layer over Mathlib's generic
`MulAction.stabilizer`: the point is to give the universal-covers development compatibility
lemmas for changing the total-space cover by an over-base homeomorphism.

For the pointed classification of connected covers, changing the chosen lift changes the
associated subgroup by conjugacy; for unpointed covers, this is the source of conjugacy
classes of subgroups. The declarations here isolate the corresponding deck-action
bookkeeping before the later construction of covers attached to subgroups.

## Main declarations

* `TauCeti.Deck.FiberStabilizer`: the stabilizer of a chosen point in a fibre.
* `TauCeti.Deck.fiberStabilizerConjMulEquiv`: an over-base homeomorphism identifies the
  stabilizers of corresponding fibre points.

## References

This supplies a bookkeeping prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`,
Stage 2: the pointed/unpointed connected-cover correspondence and the basepoint-change
conjugacy statement for recovered subgroups.
-/

public section

namespace TauCeti

namespace Deck

variable {E F B : Type*} [TopologicalSpace E] [TopologicalSpace F] {p : E → B} {q : F → B}
  {b : B}

/-- The subgroup of deck transformations fixing a chosen point in the fibre over `b`. -/
abbrev FiberStabilizer (e : p ⁻¹' {b}) : Subgroup (Deck p) :=
  MulAction.stabilizer (Deck p) e

namespace FiberStabilizer

/-- Membership in the fibre stabilizer is pointwise fixedness in the restricted fibre action. -/
@[simp]
lemma mem_iff (e : p ⁻¹' {b}) (φ : Deck p) :
    φ ∈ FiberStabilizer e ↔ φ • e = e :=
  Iff.rfl

/-- Membership in the fibre stabilizer can be checked on the underlying point of the total
space. -/
lemma mem_iff_apply_coe (e : p ⁻¹' {b}) (φ : Deck p) :
    φ ∈ FiberStabilizer e ↔ φ.1 e.1 = e.1 := by
  rw [mem_iff]
  constructor
  · intro h
    simpa [fiber_smul_coe] using congrArg Subtype.val h
  · intro h
    ext
    simpa [fiber_smul_coe] using h

/-- A member of the fibre stabilizer fixes the underlying point of the total space. -/
lemma apply_coe_eq (e : p ⁻¹' {b}) (φ : FiberStabilizer e) :
    φ.1.1 e.1 = e.1 :=
  (mem_iff_apply_coe e φ.1).mp φ.2

end FiberStabilizer

/-- Under an over-base homeomorphism, conjugating deck transformations carries the stabilizer
of a fibre point onto the stabilizer of the transported point. -/
lemma map_fiberStabilizer_conjMulEquiv (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (e : p ⁻¹' {b}) :
    (FiberStabilizer e).map (conjMulEquiv h hpq : Deck p →* Deck q) =
      FiberStabilizer (fiberMap h hpq b e) := by
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact (FiberStabilizer.mem_iff (fiberMap h hpq b e) (conjMulEquiv h hpq φ)).2 (by
      rw [← fiberMap_smul h hpq φ e, (FiberStabilizer.mem_iff e φ).mp hφ])
  · intro hψ
    refine ⟨(conjMulEquiv h hpq).symm ψ, ?_, by simp⟩
    exact (FiberStabilizer.mem_iff e ((conjMulEquiv h hpq).symm ψ)).2 (by
      apply (fiberMap h hpq b).injective
      rw [fiberMap_smul h hpq ((conjMulEquiv h hpq).symm ψ) e]
      simpa using (FiberStabilizer.mem_iff (fiberMap h hpq b e) ψ).mp hψ)

/-- An over-base homeomorphism identifies the stabilizers of corresponding fibre points by
conjugating deck transformations. -/
def fiberStabilizerConjMulEquiv (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (e : p ⁻¹' {b}) :
    FiberStabilizer e ≃* FiberStabilizer (fiberMap h hpq b e) :=
  (conjMulEquiv h hpq).subgroupMap (FiberStabilizer e) |>.trans <|
    MulEquiv.subgroupCongr (map_fiberStabilizer_conjMulEquiv h hpq e)

/-- The stabilizer equivalence induced by an over-base homeomorphism is implemented by
conjugating deck transformations along that homeomorphism. -/
@[simp]
lemma fiberStabilizerConjMulEquiv_apply (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (e : p ⁻¹' {b}) (φ : FiberStabilizer e) :
    (fiberStabilizerConjMulEquiv h hpq e φ : Deck q) = conjMulEquiv h hpq φ := by
  rfl

/-- The inverse stabilizer equivalence induced by an over-base homeomorphism is implemented by
inverse conjugation of deck transformations. -/
@[simp]
lemma fiberStabilizerConjMulEquiv_symm_apply (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (e : p ⁻¹' {b}) (ψ : FiberStabilizer (fiberMap h hpq b e)) :
    ((fiberStabilizerConjMulEquiv h hpq e).symm ψ : Deck p) =
      (conjMulEquiv h hpq).symm ψ := by
  rfl

/-- The identity over-base homeomorphism induces the identity equivalence on a fibre
stabilizer. -/
@[simp]
lemma fiberStabilizerConjMulEquiv_refl (e : p ⁻¹' {b}) :
    fiberStabilizerConjMulEquiv (Homeomorph.refl E) (p := p) (q := p) (fun _ => rfl) e =
      MulEquiv.refl (FiberStabilizer e) := by
  apply MulEquiv.ext
  intro φ
  apply Subtype.ext
  change (fiberStabilizerConjMulEquiv (Homeomorph.refl E) (p := p) (q := p)
      (fun _ => rfl) e φ : Deck p) = φ
  simp

end Deck

end TauCeti
