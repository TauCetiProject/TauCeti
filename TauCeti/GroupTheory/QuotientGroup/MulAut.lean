/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Automorphisms of a quotient by a characteristic subgroup

Every automorphism of a group `G` maps a characteristic subgroup `N` onto itself, so it induces an
automorphism of the quotient `G ⧸ N`. This gives the homomorphism
`MulAut.mapQuotient N : MulAut G →* MulAut (G ⧸ N)`, the quotient counterpart of Mathlib's
`MulAut.characteristic N : MulAut G →* MulAut N`. Its kernel consists of the automorphisms acting
trivially on `G ⧸ N`. For the Frattini subgroup of a finite `p`-group this kernel is a `p`-group,
see `TauCeti/GroupTheory/Frattini.lean`.

## Main definitions

* `MulAut.mapQuotient N`: the automorphism of `G ⧸ N` induced by an automorphism of `G`, for a
  characteristic subgroup `N`.

## Main statements

* `MulAut.mapQuotient_mk`: the induced automorphism sends the class of `x` to the class of `φ x`.
* `MulAut.mem_ker_mapQuotient_iff`: an automorphism induces the identity on `G ⧸ N` exactly when
  it fixes every class modulo `N`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] (N : Subgroup G) [N.Characteristic]

/-- The automorphism of the quotient `G ⧸ N` by a characteristic subgroup `N` induced by an
automorphism of `G`. -/
def _root_.MulAut.mapQuotient : MulAut G →* MulAut (G ⧸ N) where
  toFun φ := QuotientGroup.congr N N φ
    (φ.toMonoidHom_eq_coe ▸ Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]

/-- The automorphism induced on `G ⧸ N` sends the class of `x` to the class of `φ x`. -/
@[simp]
theorem _root_.MulAut.mapQuotient_mk (φ : MulAut G) (x : G) :
    MulAut.mapQuotient N φ (x : G ⧸ N) = (φ x : G ⧸ N) :=
  QuotientGroup.congr_mk _ _ _
    (φ.toMonoidHom_eq_coe ▸ Subgroup.characteristic_iff_map_eq.mp inferInstance φ) x

/-- An automorphism of `G` induces the identity on `G ⧸ N` exactly when it fixes every class
modulo `N`. -/
theorem _root_.MulAut.mem_ker_mapQuotient_iff {φ : MulAut G} :
    φ ∈ (MulAut.mapQuotient N).ker ↔ ∀ x : G, (φ x : G ⧸ N) = x := by
  refine ⟨fun h x ↦ ?_, fun h ↦ MulEquiv.ext fun q ↦ ?_⟩
  · simpa using congrArg (fun α : MulAut (G ⧸ N) ↦ α (x : G ⧸ N)) (MonoidHom.mem_ker.mp h)
  · induction q using QuotientGroup.induction_on with
    | H x => simpa using h x

end TauCeti
