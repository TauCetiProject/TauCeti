/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Group.Units.Defs

/-!
# Centralizers, multiplicative equivalences, conjugation by units, and commutative magmas

Basic lemmas for `Set.centralizer`:

* `Set.centralizer_image` (and its additive counterpart `Set.addCentralizer_image`): multiplicative
  equivalences commute with taking centralizers.
* `Set.conj_mem_centralizer`: if conjugation by the inverse of a unit `u` maps a set `S` of a
  monoid into itself, then conjugation by `u` maps the centralizer of `S` into itself. Applying
  this twice shows that a double commutant is preserved by every unit whose conjugations preserve
  the original set in both directions, which is how spatially implemented automorphisms extend to
  von Neumann algebras.
* `Set.apply_mem_centralizer_range` (and its additive counterpart
  `Set.apply_mem_addCentralizer_range`): every value of a multiplicative homomorphism from a
  commutative magma lies in the centralizer of its range.
* `Set.mem_centralizer_iff_fst_snd` and `Set.centralizer_eq_prod_centralizer_image` (with their
  additive counterparts): an element of `M × N` centralizes a set `S` exactly when its components
  centralize the projections of `S`, so `C(S) = C(S₁) × C(S₂)`.
-/

public section

namespace Set

/-- A multiplicative equivalence maps the centralizer of a set onto the centralizer of its
image. -/
@[to_additive addCentralizer_image
  /-- An additive equivalence maps the additive centralizer of a set onto the additive centralizer
  of its image. -/]
theorem centralizer_image {A B F : Type*} [Mul A] [Mul B] [EquivLike F A B]
    [MulEquivClass F A B] (e : F) (s : Set A) : (e '' s).centralizer = e '' s.centralizer := by
  ext b; refine ⟨fun hb ↦ ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := EquivLike.surjective e b
    exact ⟨c, fun a ha ↦ EquivLike.injective e <| by
      rw [map_mul, map_mul]; exact hb (e a) ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩; rw [← map_mul, ← map_mul, ha x hx]

section Monoid

variable {M : Type*} [Monoid M] {S : Set M}

/-- Conjugation by a unit `u` maps the centralizer of `S` into itself when conjugation by `u⁻¹`
maps `S` into itself. -/
theorem conj_mem_centralizer (u : Mˣ) (hS : ∀ s ∈ S, ↑u⁻¹ * s * ↑u ∈ S) {x : M}
    (hx : x ∈ S.centralizer) : ↑u * x * ↑u⁻¹ ∈ S.centralizer := by
  intro s hs
  have h := hx _ (hS s hs)
  calc s * (↑u * x * ↑u⁻¹) = ↑u * ((↑u⁻¹ * s * ↑u) * x) * ↑u⁻¹ := by
        simp only [mul_assoc, Units.mul_inv_cancel_left]
    _ = ↑u * (x * (↑u⁻¹ * s * ↑u)) * ↑u⁻¹ := by rw [h]
    _ = ↑u * x * ↑u⁻¹ * s := by
        simp only [mul_assoc, Units.mul_inv, mul_one]

end Monoid

/-- Every value of a multiplicative homomorphism from a commutative magma lies in the centralizer
of its range. -/
@[to_additive (attr := simp) apply_mem_addCentralizer_range
  /-- Every value of an additive homomorphism from a commutative additive magma lies in the
  additive centralizer of its range. -/]
theorem apply_mem_centralizer_range {F M N : Type*} [Mul M] [IsMulCommutative M] [Mul N]
    [FunLike F M N] [MulHomClass F M N] (f : F) (x : M) :
    f x ∈ Set.centralizer (Set.range f) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨y, rfl⟩
  rw [← map_mul, mul_comm' y x, map_mul]

section Prod

variable {M N : Type*} [Mul M] [Mul N]

/-- **Centralizers in a product.** An element `c` of `M × N` centralizes a set `S` exactly when
its components centralize the projections of `S`. -/
@[to_additive mem_addCentralizer_iff_fst_snd
  /-- An element `c` of `M × N` additively centralizes a set `S` exactly when its components
  additively centralize the projections of `S`. -/]
theorem mem_centralizer_iff_fst_snd {S : Set (M × N)} {c : M × N} :
    c ∈ S.centralizer ↔ c.1 ∈ (Prod.fst '' S).centralizer ∧ c.2 ∈ (Prod.snd '' S).centralizer := by
  simp only [mem_centralizer_iff, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Prod.ext_iff, Prod.fst_mul, Prod.snd_mul]
  exact ⟨fun h ↦ ⟨fun q hq ↦ (h q hq).1, fun q hq ↦ (h q hq).2⟩, fun h q hq ↦ ⟨h.1 q hq, h.2 q hq⟩⟩

/-- The centralizer of a set `S` in `M × N` is the product of the centralizers of the projections
of `S`. -/
@[to_additive addCentralizer_eq_prod_addCentralizer_image
  /-- The additive centralizer of a set `S` in `M × N` is the product of the additive centralizers
  of the projections of `S`. -/]
theorem centralizer_eq_prod_centralizer_image (S : Set (M × N)) :
    S.centralizer = (Prod.fst '' S).centralizer ×ˢ (Prod.snd '' S).centralizer :=
  ext fun _ ↦ mem_centralizer_iff_fst_snd

end Prod

end Set
