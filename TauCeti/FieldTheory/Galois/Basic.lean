/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# The Galois theory of quadratic extensions

Material complementing `Mathlib/FieldTheory/Galois/Basic.lean` for a quadratic extension `L/K`:
it has at most two automorphisms, so the identity and any one nontrivial automorphism exhaust
`Gal(L/K)` and every automorphism is an involution. A nontrivial automorphism makes `L/K` Galois,
so an element it fixes lies in the base field. Only the existence of a nontrivial automorphism
(equivalently, `Gal(L/K)` having exactly two elements) assumes separability.
`Algebra.IsQuadraticExtension.quadraticCharacter` records the resulting `Gal(L/K) →* ℤˣ` — the
identity to `1`, a nontrivial automorphism to `-1`. It is there so that a quantity alternating
with the Galois action can be described uniformly in `σ` rather than by cases;
`WeierstrassCurve.quadraticTwistPointEquiv_map_eq_quadraticCharacter_smul_map` is the intended
consumer. Mathlib's `quadraticChar` is a different object — the Legendre symbol of a
finite field, not a character of a Galois group.

Mathlib already supplies the surrounding structure: `Algebra.IsQuadraticExtension` makes `L/K`
finite and normal (`Algebra.IsQuadraticExtension.normal`), hence Galois with separability
(`Algebra.IsQuadraticExtension.isGalois`); `IsGalois.card_aut_eq_finrank` counts the
automorphisms and `IsGalois.mem_range_algebraMap_iff_fixed` characterises the base field.

These are the descent inputs for quadratic twists, consumed by
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisDescent.lean` and by
`TauCeti/RingTheory/Norm/Quadratic.lean`, which expresses the trace and norm of a
quadratic extension through a nontrivial automorphism.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/FieldTheory/Galois/Basic.lean` at `bc2fe8ff7396`, FLT PR #1088,
Apache 2.0). That file's own header reads `Authors: Kevin Buzzard, Claude`; following this
repository's convention for adapted material, the upstream authorship is credited here rather
than in the copyright header. Only the results consumed downstream are adapted here.
-/

public section

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L]

namespace Algebra.IsQuadraticExtension

/-- A quadratic extension has at most two automorphisms. -/
theorem card_algEquiv_le_two : Nat.card (L ≃ₐ[K] L) ≤ 2 := by
  simpa [Nat.card_eq_fintype_card, finrank_eq_two] using AlgEquiv.card_le (F := K) (K := L)

/-- A separable quadratic extension has exactly two automorphisms. -/
theorem card_algEquiv_eq_two [Algebra.IsSeparable K L] : Nat.card (L ≃ₐ[K] L) = 2 :=
  (IsGalois.card_aut_eq_finrank K L).trans (finrank_eq_two K L)

/-- The only automorphisms of a quadratic extension are the identity and any given nontrivial
automorphism. -/
theorem algEquiv_eq_one_or_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (φ : L ≃ₐ[K] L) : φ = 1 ∨ φ = σ := by
  have : Nontrivial (L ≃ₐ[K] L) := ⟨σ, 1, hσ⟩
  have h2 := (card_algEquiv_le_two K L).antisymm Finite.one_lt_card
  exact or_iff_not_imp_left.mpr fun h1 ↦ ((Nat.card_eq_two_iff' 1).mp h2).unique h1 hσ

/-- **Every automorphism of a quadratic extension is an involution.** `Gal(L/K)` has order at
most two, so this needs no nontriviality hypothesis: it holds for the identity as well. -/
@[simp]
theorem algEquiv_mul_self (σ : L ≃ₐ[K] L) : σ * σ = 1 := by
  rcases eq_or_ne σ 1 with rfl | hσ
  · exact one_mul 1
  · exact (algEquiv_eq_one_or_eq K L hσ (σ * σ)).resolve_right (by simpa using hσ)

/-- A quadratic extension with a nontrivial automorphism is Galois: `Gal(L/K)` then has order
`2 = [L : K]`. This is how the results below avoid assuming separability. -/
theorem isGalois_of_algEquiv_ne_one {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) : IsGalois K L :=
  have : Nontrivial (L ≃ₐ[K] L) := ⟨σ, 1, hσ⟩
  .of_card_aut_eq_finrank K L <|
    ((card_algEquiv_le_two K L).antisymm Finite.one_lt_card).trans (finrank_eq_two K L).symm

/-- **The base field of a quadratic extension is the fixed field of any nontrivial
automorphism.** An element fixed by a nontrivial automorphism — hence, `Gal(L/K)` having order
two, by all of `Gal(L/K)` — lies in the base field, and conversely. -/
theorem mem_range_algebraMap_iff_apply_eq_self {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {x : L} :
    x ∈ Set.range (algebraMap K L) ↔ σ x = x := by
  refine ⟨fun ⟨y, hy⟩ ↦ hy ▸ σ.commutes y, fun hx ↦ ?_⟩
  have := isGalois_of_algEquiv_ne_one K L hσ
  refine (IsGalois.mem_range_algebraMap_iff_fixed x).mpr fun φ ↦ ?_
  rcases algEquiv_eq_one_or_eq K L hσ φ with rfl | rfl <;> simp_all

/-- **A nontrivial automorphism of a quadratic extension moves every element outside the base
field.** The difference `σ x - x` is the square root of the discriminant of `x`'s minimal
polynomial, so this is exactly the nondegeneracy that makes such an `x` a generator. -/
theorem apply_sub_self_ne_zero {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) : σ x - x ≠ 0 :=
  sub_ne_zero.mpr fun heq ↦ hx ((mem_range_algebraMap_iff_apply_eq_self K L hσ).mpr heq)

/-- A separable quadratic extension has a nontrivial automorphism. -/
theorem exists_algEquiv_ne_one [Algebra.IsSeparable K L] : ∃ σ : L ≃ₐ[K] L, σ ≠ 1 :=
  ((Nat.card_eq_two_iff' 1).mp (card_algEquiv_eq_two K L)).exists

/-- The automorphism group of a quadratic extension with a nontrivial automorphism `σ` consists
of the identity and `σ`. -/
theorem univ_eq_pair [DecidableEq (L ≃ₐ[K] L)] {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (Finset.univ : Finset (L ≃ₐ[K] L)) = {1, σ} :=
  (Finset.eq_univ_of_forall fun φ ↦ by simpa using algEquiv_eq_one_or_eq K L hσ φ).symm

/-! ### The quadratic character -/

open scoped Classical in
/-- **The quadratic character of a quadratic extension**: the identity goes to `1` and a
nontrivial automorphism, if there is one, to `-1`. `Gal(L/K)` has order at most two, so this is
injective, but the point of packaging it as a `MonoidHom` is that a statement which alternates in
`σ` — a Galois action twisted by the extension, as for the points of a quadratic twist — can then
be written uniformly in `σ` instead of split into a fixed and a moved branch by every consumer. -/
noncomputable def quadraticCharacter : (L ≃ₐ[K] L) →* ℤˣ where
  toFun σ := if σ = 1 then 1 else -1
  map_one' := by simp
  map_mul' σ τ := by
    rcases eq_or_ne σ 1 with rfl | hσ
    · simp
    · rcases algEquiv_eq_one_or_eq K L hσ τ with rfl | rfl <;> simp [hσ]

/-- The quadratic character detects the identity: it takes the value `1` exactly there. -/
@[simp]
theorem quadraticCharacter_eq_one_iff {σ : L ≃ₐ[K] L} :
    quadraticCharacter K L σ = 1 ↔ σ = 1 := by
  classical
  simp [quadraticCharacter]

/-- The quadratic character takes the value `-1` exactly off the identity, there being nowhere
else to go in `ℤˣ`. -/
@[simp]
theorem quadraticCharacter_eq_neg_one_iff {σ : L ≃ₐ[K] L} :
    quadraticCharacter K L σ = -1 ↔ σ ≠ 1 := by
  classical
  simp [quadraticCharacter]

end Algebra.IsQuadraticExtension

end
