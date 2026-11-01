/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Data.Finset.Order

/-!
# Directed colimits of monoids and algebras

Basic API for Mathlib's generic `DirectLimit G f` of a directed system of monoids or algebras.

Mathlib equips `DirectLimit G f` with the algebraic structure of its components, and bundles the
canonical maps into it and its universal property for modules and rings. This file does the same
for monoids and groups: the canonical maps `G i →* DirectLimit G f` and the monoid homomorphism
out of the direct limit induced by a compatible family. Every element of the direct limit, and
more generally every finite subset of it, comes from a single component.

## Main declarations

* `TauCeti.DirectLimit.Monoid.of`: the canonical monoid homomorphism from a component into a
  direct limit of monoids.
* `TauCeti.DirectLimit.Monoid.lift`: the universal property, the monoid homomorphism out of a direct
  limit induced by a compatible family of monoid homomorphisms.
* `TauCeti.DirectLimit.Monoid.exists_subset_range_of`: every finite subset of a direct limit of
  monoids lies in the range of a single canonical map.
* `TauCeti.DirectLimit.Algebra.of_comp_f`: the canonical maps into a direct limit of algebras are
  compatible with the transition maps. This is the algebra version of
  `Ring.DirectLimit.of_comp_f` in `TauCeti/Algebra/Colimit/Ring.lean`.
-/

public section

namespace TauCeti

namespace DirectLimit.Monoid

variable {ι : Type*} [Preorder ι] {G : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
  {f : ∀ i j (h : i ≤ j), T h} [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  [DirectedSystem G (f · · ·)] [IsDirectedOrder ι] [Nonempty ι] [∀ i, MulOneClass (G i)]
  [∀ i j h, MonoidHomClass (T h) (G i) (G j)]

variable (G f) in
/-- The canonical map from a component to the direct limit of a directed system of monoids. -/
def of (i : ι) : G i →* DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (_root_.DirectLimit.one_def i).symm
  map_mul' _ _ := (_root_.DirectLimit.mul_def ..).symm

/-- The canonical map sends `x : G i` to its class in the direct limit. -/
theorem of_apply (i : ι) (x : G i) : of G f i x = ⟦⟨i, x⟩⟧ :=
  (rfl)

/-- The canonical maps into the direct limit are compatible with the transition maps. -/
@[simp]
theorem of_f {i j : ι} (hij : i ≤ j) (x : G i) : of G f j (f i j hij x) = of G f i x :=
  _root_.DirectLimit.mk_apply i j x hij

/-- Every element of a direct limit of monoids is the image of an element of some component. -/
theorem exists_of (z : DirectLimit G f) : ∃ i x, of G f i x = z := by
  obtain ⟨i, x, rfl⟩ := _root_.DirectLimit.exists_eq_mk f z
  exact ⟨i, x, rfl⟩

/-- Every finite subset of a direct limit of monoids lies in the range of the canonical map from a
single component. -/
theorem exists_subset_range_of (s : Finset (DirectLimit G f)) :
    ∃ i, (s : Set (DirectLimit G f)) ⊆ Set.range (of G f i) := by
  classical
  choose k x hx using exists_of (G := G) (f := f)
  obtain ⟨i, hi⟩ := (s.image k).exists_le
  refine ⟨i, fun z hz => ⟨f (k z) i (hi _ (Finset.mem_image_of_mem k hz)) (x z), ?_⟩⟩
  rw [of_f, hx]

variable {P : Type*} [MulOneClass P]

/-- The universal property of the direct limit of monoids: a family of monoid homomorphisms
`g i : G i →* P` compatible with the transition maps induces a monoid homomorphism out of the
direct limit. -/
def lift (g : ∀ i, G i →* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →* P where
  toFun := _root_.DirectLimit.lift f (g · ·) fun i j hij x => (Hg i j hij x).symm
  map_one' := _root_.DirectLimit.lift_one _ _
  map_mul' := _root_.DirectLimit.lift_mul _ _

/-- The homomorphism induced by a compatible family restricts to that family on each component. -/
@[simp]
theorem lift_of (g : ∀ i, G i →* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) (i : ι)
    (x : G i) : lift g Hg (of G f i x) = g i x :=
  (rfl)

/-- The homomorphism induced by a compatible family, composed with a canonical map, is the
corresponding member of the family. -/
@[simp]
theorem lift_comp_of (g : ∀ i, G i →* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) (i : ι) :
    (lift g Hg).comp (of G f i) = g i :=
  MonoidHom.ext (lift_of g Hg i)

/-- Two monoid homomorphisms out of a direct limit agree once they agree on every component. -/
@[ext]
theorem hom_ext {g₁ g₂ : DirectLimit G f →* P} (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ := by
  ext z
  obtain ⟨i, x, rfl⟩ := exists_of z
  exact DFunLike.congr_fun (h i) x

end DirectLimit.Monoid

namespace DirectLimit.Algebra

variable {A ι : Type*} [CommSemiring A] [Preorder ι] {B : ι → Type*} [∀ i, Semiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  [IsDirectedOrder ι] [Nonempty ι]

open _root_.DirectLimit.Algebra

/-- The canonical maps into a direct limit of algebras are compatible with the transition
maps. -/
@[simp]
theorem of_comp_f {i j : ι} (hij : i ≤ j) : (of B f j).comp (f i j hij) = of B f i :=
  AlgHom.ext fun _ ↦ of_f _ _

end DirectLimit.Algebra

end TauCeti
