/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import TauCeti.Algebra.Group.Equiv.Pi
public import TauCeti.Data.Finset.Pi

/-!
# Products of monoids indexed by finite sets

For a family of monoids `π i` and finite sets `s ⊆ t` of indices, restricting a family indexed by
`t` to `s` is a monoid homomorphism
`Finset.restrict₂MonoidHom π h : (∀ i : t, π i) →* ∀ i : s, π i`.
For disjoint `s` and `t`, gluing a family on `s` and a family on `t` is a multiplicative
equivalence `MulEquiv.piFinsetUnion π h : (∀ i : s, π i) × (∀ i : t, π i) ≃* ∀ i : s ∪ t, π i`.
Under it the restrictions to `s` and to `t` are the two projections of the product. Gluing is
associative: this is the statement on underlying functions, `Equiv.restrict₂_piFinsetUnion_assoc`.
For an embedding `f : ι' ↪ ι`, a family indexed by `s` with values in `π (f i)` is a family indexed
by `s.map f`, by the multiplicative equivalence
`MulEquiv.piFinsetMap π f s : (∀ i : s, π (f i)) ≃* ∀ j : s.map f, π j`, which commutes with
restriction.

These are the projections `Γ_J → Γ_I`, the disjoint-union identifications
`Γ_(I ⊔ J) ≅ Γ_I × Γ_J` and the injective-reindexing identifications `Γ_I ≅ Γ_(f I)` of the groups
`Γ_I = ∏_(α ∈ I) Γ_α` attached to the finite sets `I` of charts of an implicit atlas, in the sense
of Pardon.

## Main definitions

* `Finset.restrict₂MonoidHom`: restriction to a smaller finite set, as a monoid homomorphism.
* `MulEquiv.piFinsetUnion`: `Equiv.piFinsetUnion` as a multiplicative equivalence.
* `MulEquiv.piFinsetMap`: relabelling along an embedding, as a multiplicative equivalence.

## Main results

* `Finset.restrict₂_mul`, `Finset.restrict₂_add` and `Finset.restrict₂_smul`: restriction commutes
  with the pointwise operations.
* `MulEquiv.restrict₂MonoidHom_comp_piFinsetUnion_left` and
  `MulEquiv.restrict₂MonoidHom_comp_piFinsetUnion_right`: the restrictions to the two pieces are
  the projections of the product.
* `MulEquiv.restrict₂_piFinsetMap`: relabelling along an embedding commutes with restriction.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Definition 3.1.1.
-/

public section

namespace Finset

section Mul

variable {ι : Type*} {π : ι → Type*} {s t : Finset ι}

/-- Restriction to a smaller finite set commutes with multiplication. -/
@[to_additive (attr := simp) /-- Restriction to a smaller finite set commutes with addition. -/]
theorem restrict₂_mul [∀ i, Mul (π i)] (h : s ⊆ t) (f g : ∀ i : t, π i) :
    restrict₂ h (f * g) = restrict₂ h f * restrict₂ h g :=
  (rfl)

/-- Restriction to a smaller finite set commutes with scalar multiplication. -/
@[simp]
theorem restrict₂_smul {M : Type*} [∀ i, SMul M (π i)] (h : s ⊆ t) (c : M) (f : ∀ i : t, π i) :
    restrict₂ h (c • f) = c • restrict₂ h f :=
  (rfl)

end Mul

variable {ι : Type*} (π : ι → Type*) [∀ i, MulOneClass (π i)] {s t u : Finset ι}

/-- Restricting a family indexed by `t` to `s ⊆ t`, as a monoid homomorphism. -/
@[to_additive /-- Restricting a family indexed by `t` to `s ⊆ t`, as an additive monoid
homomorphism. -/]
def restrict₂MonoidHom (h : s ⊆ t) : (∀ i : t, π i) →* ∀ i : s, π i where
  toFun := restrict₂ h
  map_one' := (rfl)
  map_mul' _ _ := (rfl)

@[to_additive (attr := simp)]
theorem coe_restrict₂MonoidHom (h : s ⊆ t) : ⇑(restrict₂MonoidHom π h) = restrict₂ h :=
  (rfl)

@[to_additive (attr := simp)]
theorem restrict₂MonoidHom_refl : restrict₂MonoidHom π (subset_refl s) = MonoidHom.id _ :=
  (rfl)

/-- Restricting from `u` to `t` and then to `s` is restricting from `u` to `s`. -/
@[to_additive (attr := simp) /-- Restricting from `u` to `t` and then to `s` is restricting from
`u` to `s`. -/]
theorem restrict₂MonoidHom_comp_restrict₂MonoidHom (hst : s ⊆ t) (htu : t ⊆ u) :
    (restrict₂MonoidHom π hst).comp (restrict₂MonoidHom π htu) =
      restrict₂MonoidHom π (hst.trans htu) :=
  (rfl)

end Finset

namespace MulEquiv

open Finset

variable {ι : Type*} [DecidableEq ι] (π : ι → Type*) {s t : Finset ι}

section Mul

variable [∀ i, Mul (π i)]

/-- Gluing a family on `s` and a family on `t` into a family on `s ∪ t`, for disjoint `s` and
`t`. This is `Equiv.piFinsetUnion` as a `MulEquiv`. -/
@[to_additive /-- Gluing a family on `s` and a family on `t` into a family on `s ∪ t`, for
disjoint `s` and `t`. This is `Equiv.piFinsetUnion` as an `AddEquiv`. -/]
def piFinsetUnion (h : Disjoint s t) :
    ((∀ i : s, π i) × ∀ i : t, π i) ≃* ∀ i : (s ∪ t : Finset ι), π i where
  __ := Equiv.piFinsetUnion π h
  map_mul' _ _ := restrict₂_union_ext (by simp) (by simp)

@[to_additive (attr := simp)]
theorem coe_piFinsetUnion (h : Disjoint s t) :
    ⇑(piFinsetUnion π h) = Equiv.piFinsetUnion π h :=
  (rfl)

@[to_additive (attr := simp)]
theorem coe_piFinsetUnion_symm (h : Disjoint s t) :
    ⇑(piFinsetUnion π h).symm = (Equiv.piFinsetUnion π h).symm :=
  (rfl)

end Mul

variable [∀ i, MulOneClass (π i)]

/-- Under `MulEquiv.piFinsetUnion`, restricting to `s` is the first projection. -/
@[to_additive (attr := simp) /-- Under `AddEquiv.piFinsetUnion`, restricting to `s` is the first
projection. -/]
theorem restrict₂MonoidHom_comp_piFinsetUnion_left (h : Disjoint s t) :
    (restrict₂MonoidHom π subset_union_left).comp
        (piFinsetUnion π h : ((∀ i : s, π i) × ∀ i : t, π i) →* ∀ i : (s ∪ t : Finset ι), π i) =
      MonoidHom.fst _ _ :=
  MonoidHom.ext fun x ↦ Equiv.restrict₂_piFinsetUnion_left π h x

/-- Under `MulEquiv.piFinsetUnion`, restricting to `t` is the second projection. -/
@[to_additive (attr := simp) /-- Under `AddEquiv.piFinsetUnion`, restricting to `t` is the second
projection. -/]
theorem restrict₂MonoidHom_comp_piFinsetUnion_right (h : Disjoint s t) :
    (restrict₂MonoidHom π subset_union_right).comp
        (piFinsetUnion π h : ((∀ i : s, π i) × ∀ i : t, π i) →* ∀ i : (s ∪ t : Finset ι), π i) =
      MonoidHom.snd _ _ :=
  MonoidHom.ext fun x ↦ Equiv.restrict₂_piFinsetUnion_right π h x

end MulEquiv

namespace MulEquiv

open Finset

section Map

variable {ι ι' : Type*} (π : ι → Type*) (f : ι' ↪ ι) (s t : Finset ι')

/-- Relabelling a family indexed by `s` along an embedding `f`, as a family indexed by `s.map f`.
Its inverse reads the coordinate at `i` in position `f i`. -/
@[to_additive /-- Relabelling a family indexed by `s` along an embedding `f`, as a family indexed by
`s.map f`. Its inverse reads the coordinate at `i` in position `f i`. -/]
noncomputable def piFinsetMap [∀ i, Mul (π i)] : (∀ i : s, π (f i)) ≃* ∀ j : s.map f, π j :=
  piCongrLeft (fun j : s.map f ↦ π j) (s.equivMap f)

/-- The inverse of `MulEquiv.piFinsetMap` reads the coordinate at `i` in position `f i`. -/
@[to_additive (attr := simp) /-- The inverse of `AddEquiv.piFinsetMap` reads the coordinate at `i`
in position `f i`. -/]
theorem piFinsetMap_symm_apply [∀ i, Mul (π i)] (g : ∀ j : s.map f, π j) (i : s) :
    (piFinsetMap π f s).symm g i = g ⟨f i, mem_map_of_mem f i.property⟩ :=
  piCongrLeft_symm_apply (fun j : s.map f ↦ π j) (s.equivMap f) g i

/-- `MulEquiv.piFinsetMap` puts the coordinate at `i` in position `f i`. -/
@[to_additive (attr := simp) /-- `AddEquiv.piFinsetMap` puts the coordinate at `i` in position
`f i`. -/]
theorem piFinsetMap_apply_mk [∀ i, Mul (π i)] (g : ∀ i : s, π (f i)) (i : s) :
    piFinsetMap π f s g ⟨f i, mem_map_of_mem f i.property⟩ = g i := by
  rw [← piFinsetMap_symm_apply π f s (piFinsetMap π f s g), symm_apply_apply]

variable {s t}

/-- Relabelling along an embedding commutes with restriction to a smaller finite set. -/
@[to_additive (attr := simp) /-- Relabelling along an embedding commutes with restriction to a
smaller finite set. -/]
theorem restrict₂_piFinsetMap [∀ i, Mul (π i)] (h : s ⊆ t) (g : ∀ i : t, π (f i)) :
    restrict₂ (map_subset_map.2 h) (piFinsetMap π f t g) =
      piFinsetMap π f s (restrict₂ (π := fun i ↦ π (f i)) h g) := by
  ext ⟨j, hj⟩
  obtain ⟨i, hi, rfl⟩ := mem_map.1 hj
  exact (piFinsetMap_apply_mk π f t g ⟨i, h hi⟩).trans
    (piFinsetMap_apply_mk π f s (restrict₂ (π := fun i ↦ π (f i)) h g) ⟨i, hi⟩).symm

end Map

end MulEquiv
