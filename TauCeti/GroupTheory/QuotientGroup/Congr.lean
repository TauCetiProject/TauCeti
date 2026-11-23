/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Coset-space maps along homomorphisms and their equivariance

For `ψ : G →* G'` and a subgroup `B ≤ G'`, with no normality assumed, `ψ` induces the map
`G ⧸ ψ⁻¹(B) → G' ⧸ B`, `[g] ↦ [ψ g]` (`TauCeti.QuotientGroup.mapComap`). It is always injective,
since the denominator is the full preimage of `B`, and it is surjective exactly when `ψ` meets
every coset of `B`. It is then the bijection `TauCeti.QuotientGroup.congrComapOfSurjectiveMk`.

The coset-space bijections `TauCeti.QuotientGroup.congrComapOfSurjectiveMk` and
`TauCeti.QuotientGroup.congrOfMapEq` (defined in `TauCeti.Algebra.Group.Subgroup.Map`) act on
representatives by the underlying group homomorphism or isomorphism, so they are equivariant for
left translation on cosets.

This API lives in its own lightweight module so that:
* `TauCeti.Algebra.Group.Subgroup.Map` does not pull in `Mathlib.GroupTheory.GroupAction.Quotient`,
* `TauCeti.GroupTheory.QuotientGroup.Basic` does not publicly expose the `TauCeti.Subgroup`
  namespace (which would make `open Subgroup` ambiguous inside `namespace TauCeti` in downstream
  files), and
* callers needing only the coset-space map and its equivariance do not depend on the
  permutation-representation and centralizer machinery in
  `TauCeti.Algebra.GroupAction.CosetRepresentation`.

## Main definitions

* `TauCeti.QuotientGroup.mapComap`: the map `G ⧸ ψ⁻¹(B) → G' ⧸ B`, `[g] ↦ [ψ g]`.

## Main statements

* `TauCeti.QuotientGroup.injective_mapComap`, `TauCeti.QuotientGroup.surjective_mapComap_iff`:
  the map is injective, and surjective exactly when `ψ` meets every coset of `B`.
* `TauCeti.QuotientGroup.coe_congrComapOfSurjectiveMk`: when it is surjective, it is
  `congrComapOfSurjectiveMk`.
* `TauCeti.QuotientGroup.mapComap_smul`: it intertwines left translation by `g` with left
  translation by `ψ g`.
* `TauCeti.QuotientGroup.congrComapOfSurjectiveMk_smul`: `congrComapOfSurjectiveMk` intertwines
  left translation by `g` with left translation by `ψ g`.
* `TauCeti.QuotientGroup.congrOfMapEq_smul`: `congrOfMapEq` intertwines left translation by `g`
  with left translation by `φ g`.
-/

public section

namespace TauCeti.QuotientGroup

variable {G G' : Type*} [Group G] [Group G']

/-- **The coset-space map along a homomorphism.** For `ψ : G →* G'` and a subgroup `B ≤ G'`, the
map `G ⧸ ψ⁻¹(B) → G' ⧸ B`, `[g] ↦ [ψ g]`. Neither subgroup need be normal, which is what
distinguishes it from Mathlib's `QuotientGroup.map`. It is injective
(`TauCeti.QuotientGroup.injective_mapComap`), and when `ψ` meets every coset of `B` it is the
bijection `TauCeti.QuotientGroup.congrComapOfSurjectiveMk`
(`TauCeti.QuotientGroup.coe_congrComapOfSurjectiveMk`). -/
def mapComap (ψ : G →* G') (B : Subgroup G') : G ⧸ B.comap ψ → G' ⧸ B :=
  Quotient.map' ψ fun a b h ↦ by
    rwa [QuotientGroup.leftRel_apply, Subgroup.mem_comap, map_mul, map_inv,
      ← QuotientGroup.leftRel_apply] at h

/-- `TauCeti.QuotientGroup.mapComap` sends the coset of `g` to the coset of `ψ g`. -/
@[simp] theorem mapComap_mk (ψ : G →* G') (B : Subgroup G') (g : G) :
    mapComap ψ B (g : G ⧸ B.comap ψ) = (ψ g : G' ⧸ B) :=
  (rfl)

/-- `TauCeti.QuotientGroup.mapComap` composed with the projection of `G` is the projection of `G'`
composed with `ψ`. -/
theorem mapComap_comp_mk (ψ : G →* G') (B : Subgroup G') :
    mapComap ψ B ∘ (_root_.QuotientGroup.mk : G → G ⧸ B.comap ψ) =
      (_root_.QuotientGroup.mk : G' → G' ⧸ B) ∘ ψ :=
  funext (mapComap_mk ψ B)

/-- `TauCeti.QuotientGroup.mapComap` is injective, since `ψ⁻¹(B)` is the full preimage of `B`. -/
theorem injective_mapComap (ψ : G →* G') (B : Subgroup G') :
    Function.Injective (mapComap ψ B) := by
  intro x y hxy
  induction x using _root_.QuotientGroup.induction_on with | H a =>
  induction y using _root_.QuotientGroup.induction_on with | H b =>
  simpa only [mapComap_mk, QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv] using hxy

/-- `TauCeti.QuotientGroup.mapComap` is surjective exactly when `ψ` meets every coset of `B`. -/
theorem surjective_mapComap_iff (ψ : G →* G') (B : Subgroup G') :
    Function.Surjective (mapComap ψ B) ↔
      Function.Surjective ((_root_.QuotientGroup.mk : G' → G' ⧸ B) ∘ ψ) := by
  rw [← mapComap_comp_mk]
  exact ⟨fun h ↦ h.comp _root_.QuotientGroup.mk_surjective, Function.Surjective.of_comp⟩

/-- When `ψ` meets every coset of `B`, the bijection
`TauCeti.QuotientGroup.congrComapOfSurjectiveMk` is `TauCeti.QuotientGroup.mapComap`. -/
theorem coe_congrComapOfSurjectiveMk (ψ : G →* G') (B : Subgroup G')
    (hψ : Function.Surjective fun g : G ↦ (ψ g : G' ⧸ B)) :
    ⇑(congrComapOfSurjectiveMk ψ B hψ) = mapComap ψ B :=
  funext fun q ↦ _root_.QuotientGroup.induction_on q fun _ ↦ by
    rw [congrComapOfSurjectiveMk_mk, mapComap_mk]

/-- `TauCeti.QuotientGroup.mapComap` intertwines left translation by `g` with left translation by
`ψ g`. -/
@[simp] theorem mapComap_smul (ψ : G →* G') (B : Subgroup G') (g : G) (q : G ⧸ B.comap ψ) :
    mapComap ψ B (g • q) = ψ g • mapComap ψ B q :=
  _root_.QuotientGroup.induction_on q fun _ ↦ by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mapComap_mk, mapComap_mk, map_mul,
      MulAction.Quotient.smul_mk, smul_eq_mul]

/-- `TauCeti.QuotientGroup.congrComapOfSurjectiveMk` intertwines left translation by `g` with left
translation by `ψ g`. -/
@[simp] theorem congrComapOfSurjectiveMk_smul (ψ : G →* G') (B : Subgroup G')
    (hψ : Function.Surjective fun g : G ↦ (ψ g : G' ⧸ B)) (g : G) (q : G ⧸ B.comap ψ) :
    congrComapOfSurjectiveMk ψ B hψ (g • q) = ψ g • congrComapOfSurjectiveMk ψ B hψ q := by
  rw [coe_congrComapOfSurjectiveMk, mapComap_smul]

/-- `TauCeti.QuotientGroup.congrOfMapEq` intertwines left translation by `g` with left translation
by `φ g`. -/
@[simp] theorem congrOfMapEq_smul (φ : G ≃* G') {A : Subgroup G} {B : Subgroup G'}
    (h : A.map (φ : G →* G') = B) (g : G) (q : G ⧸ A) :
    congrOfMapEq φ h (g • q) = φ g • congrOfMapEq φ h q :=
  _root_.QuotientGroup.induction_on q fun _ ↦ by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, congrOfMapEq_mk, congrOfMapEq_mk, map_mul,
      MulAction.Quotient.smul_mk, smul_eq_mul]

end TauCeti.QuotientGroup
