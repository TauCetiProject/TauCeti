/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import TauCeti.RepresentationTheory.GroupAlgebra.Average
public import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The rational group algebra of a group of prime order

Let `p` be a prime, `G` a group of order `p`, `K` a `p`-th cyclotomic field and `χ : G →* K` a
nontrivial character. The map `x ↦ (ε(x), χ(x))`, where `ε` is the augmentation, is an isomorphism
of `ℚ`-algebras `ℚ[G] ≃ ℚ × K`: it is surjective since the averaging idempotent `e₁ = p⁻¹ ∑_g g`
maps to `(1, 0)` and `χ(g)` generates `K`, and both sides have dimension `p`.

## Main definitions

* `TauCeti.groupAlgebraEquivProd`: the isomorphism `ℚ[G] ≃ₐ[ℚ] ℚ × K`, `x ↦ (ε(x), χ(x))`.

## Main results

* `TauCeti.groupAlgebraEquivProd_single`, `TauCeti.groupAlgebraEquivProd_average`: the
  isomorphism sends `g` to `(1, χ g)` and `e₁` to `(1, 0)`.

## References

* H. Johnston, *Notes on Galois modules*, Example 13.9.
-/

public section

open Module Polynomial MonoidAlgebra

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G]

namespace TauCeti

variable {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K] {χ : G →* K}

omit [IsCyclotomicExtension {p} ℚ K] in
private theorem prod_lift_single (g : G) :
    (lift ℚ ℚ G 1).prod (lift ℚ K G χ) (single g 1) = (1, χ g) := by
  simp

omit [IsCyclotomicExtension {p} ℚ K] in
private theorem prod_lift_average [Fintype G] (hχ : χ ≠ 1) :
    (lift ℚ ℚ G 1).prod (lift ℚ K G χ) (GroupAlgebra.average ℚ G) = (1, 0) := by
  ext <;> simp [GroupAlgebra.lift_average_of_ne_one hχ]

private theorem bijective_prod_lift (hG : Nat.card G = p) (hχ : χ ≠ 1) :
    Function.Bijective ((lift ℚ ℚ G 1).prod (lift ℚ K G χ)) := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact hp.out.ne_zero)
  have := Fintype.ofFinite G
  set f := (lift ℚ ℚ G 1).prod (lift ℚ K G χ)
  obtain ⟨g, hg⟩ := DFunLike.ne_iff.1 hχ
  have hζ := χ.isPrimitiveRoot_apply_of_card_eq_prime hG hg
  -- `χ` maps `ℚ[G]` onto `K = ℚ(χ g)`, and `e₁ ↦ (1, 0)` corrects the augmentation
  have hsurj : Function.Surjective f := by
    rintro ⟨a, b⟩
    have hb : b ∈ (lift ℚ K G χ).range := by
      have hle : Algebra.adjoin ℚ {χ g} ≤ (lift ℚ K G χ).range :=
        Algebra.adjoin_le <| Set.singleton_subset_iff.2 <|
          (AlgHom.mem_range _).2 ⟨single g 1, by simp⟩
      refine hle ?_
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
      trivial
    obtain ⟨y, hy⟩ := (AlgHom.mem_range _).1 hb
    refine ⟨y + (a - lift ℚ ℚ G 1 y) • GroupAlgebra.average ℚ G, ?_⟩
    rw [map_add, map_smul, prod_lift_average hχ]
    ext <;> simp [f, hy]
  have := IsCyclotomicExtension.finiteDimensional {p} ℚ K
  refine ⟨?_, hsurj⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) ?_).2 hsurj
  rw [finrank_eq_card_basis (MonoidAlgebra.basis G ℚ), finrank_prod, finrank_self,
    IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat hp.out.pos),
    Nat.totient_prime hp.out, ← Nat.card_eq_fintype_card, hG]
  have := hp.out.one_lt
  omega

variable (K) in
/-- For a group `G` of prime order `p`, a `p`-th cyclotomic field `K` and a nontrivial character
`χ : G →* K`, the `ℚ`-algebra isomorphism `ℚ[G] ≃ ℚ × K` sending `x` to its augmentation and its
image under `χ`. -/
noncomputable def groupAlgebraEquivProd (hG : Nat.card G = p) (hχ : χ ≠ 1) :
    MonoidAlgebra ℚ G ≃ₐ[ℚ] ℚ × K :=
  AlgEquiv.ofBijective _ (bijective_prod_lift hG hχ)

variable (hG : Nat.card G = p) (hχ : χ ≠ 1)

/-- The isomorphism `ℚ[G] ≃ ℚ × K` is the augmentation in the first component and `χ` in the
second. -/
theorem groupAlgebraEquivProd_apply (x : MonoidAlgebra ℚ G) :
    groupAlgebraEquivProd K hG hχ x = (lift ℚ ℚ G 1 x, lift ℚ K G χ x) :=
  (rfl)

/-- The isomorphism `ℚ[G] ≃ ℚ × K` sends a group element `g` to `(1, χ g)`. -/
@[simp]
theorem groupAlgebraEquivProd_single (g : G) :
    groupAlgebraEquivProd K hG hχ (single g 1) = (1, χ g) :=
  prod_lift_single g

/-- The isomorphism `ℚ[G] ≃ ℚ × K` sends the averaging idempotent `e₁` to `(1, 0)`. -/
@[simp]
theorem groupAlgebraEquivProd_average [Fintype G] :
    groupAlgebraEquivProd K hG hχ (GroupAlgebra.average ℚ G) = (1, 0) :=
  prod_lift_average hχ

end TauCeti
