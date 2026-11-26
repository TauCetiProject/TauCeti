/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.LinearAlgebra.Trace.Basic
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.Invariants
-- Non-public: a space of linear maps is finite-dimensional only when both spaces are.
import TauCeti.LinearAlgebra.FiniteDimensional.LinearMap

/-!
# Basic facts about characters

The trace character vanishes when the representation space is not finite-dimensional.
The character of the restriction of a representation along a monoid homomorphism `f` is the
composite of its character with `f` (`Representation.character_comp`).

As the character vanishes in infinite dimension, a representation whose character is nonzero at
some element is finite-dimensional
(`Representation.finiteDimensional_of_character_ne_zero`).

For two representations and a homomorphism `f : H →* G` from a finite group, for instance the
inclusion of a finite subgroup, the sum `∑ h ∈ H, χ(g f(h)) χ'((g f(h))⁻¹)` is the trace of
`σ g ∘ S`, where `σ` is the conjugation action on `W →ₗ[k] V` and `S` the sum of `σ ∘ f` over `H`
(`Representation.sum_character_mul_mul_character_mul_inv_eq_trace`); no finiteness of `V` or `W`
is needed, as the character of `linHom ρ' ρ` is `g ↦ χ'(g⁻¹) χ(g)` in any dimension
(`Representation.character_linHom`).

The trace of the action is a class function for a representation over a commutative semiring on
any additive commutative monoid (`Representation.trace_conj`). `Representation.character` and
`Representation.char_conj` ask for an additive group structure on the carrier, so this form
applies to representations such as `Representation.symmetricPower`, which is built on the
additive monoid instance of the symmetric power rather than on the one underlying its additive
group.

An element `g` acting by a scalar `c` has character `dim V · c`
(`Representation.character_eq_finrank_mul_of_apply_eq_smul`).

A commutator `g x g⁻¹ x⁻¹` acting by a scalar `a ≠ 1` forces the character to vanish at `g`
(`Representation.character_eq_zero_of_commutator_apply_eq_smul`): conjugating `g` by `x`
multiplies `ρ g` by that scalar while preserving the trace.

The `n`-th power map is a bijection of a group `G` whenever `n` is coprime to `|G|`
(`Nat.Coprime.pow_left_bijective`), so the average `|G|⁻¹ ∑_g χ(gⁿ)` of an irreducible character
`χ` equals the average `|G|⁻¹ ∑_g χ(g)`, which is the dimension of the invariants
(`Representation.card_inv_mul_sum_char_eq_finrank`). An irreducible representation has a nonzero
invariant vector only when it is the trivial line, so the average is `1` for the trivial
character and `0` otherwise (`Representation.card_inv_mul_sum_char_pow_eq_zero_iff_of_coprime`).
-/

public section

universe u v w

namespace Representation

/-- The character vanishes on a representation space that is not finite-dimensional. -/
theorem character_eq_zero_of_not_finite {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ¬ FiniteDimensional k V) :
    ρ.character = 0 := by
  funext g
  simp [character, TauCeti.LinearMap.trace_eq_zero_of_not_finite h]

/-- A representation whose character is nonzero at some element is finite-dimensional: this is the
contrapositive of `Representation.character_eq_zero_of_not_finite`. It is typically applied at
`g = 1`, for instance over a field of characteristic zero to a character whose restriction to a
subgroup is irreducible (its value at `1` is then a degree, which is nonzero in `k`). -/
theorem finiteDimensional_of_character_ne_zero {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) {g : G} (h : ρ.character g ≠ 0) :
    FiniteDimensional k V := by
  by_contra hV
  exact h (by rw [ρ.character_eq_zero_of_not_finite hV, Pi.zero_apply])

/-- The character of the restriction of `ρ` along `f : H →* G` is `ρ.character ∘ f`. -/
@[simp]
theorem character_comp {k G H V : Type*} [Field k] [Monoid G] [Monoid H] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (f : H →* G) :
    character (ρ.comp f) = ρ.character ∘ f :=
  rfl

/-- **The character of `Hom(V, W)`, in any dimension**: the character of the conjugation action
`Representation.linHom ρ σ` on `V →ₗ[k] W` is `g ↦ χ_ρ(g⁻¹) χ_σ(g)`. This is Mathlib's
`Representation.char_linHom` without its finite-dimensionality hypotheses: otherwise one of the
characters vanishes, and so does every trace on `V →ₗ[k] W`, which is then either zero or not
finite-dimensional (`Module.finite_linearMap_iff`). -/
@[simp]
theorem character_linHom {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W) (g : G) :
    (linHom ρ σ).character g = ρ.character g⁻¹ * σ.character g := by
  by_cases hfin : FiniteDimensional k V ∧ FiniteDimensional k W
  · obtain ⟨_, _⟩ := hfin
    exact char_linHom ρ σ g
  have hR : ρ.character g⁻¹ * σ.character g = 0 := by
    rcases not_and_or.mp hfin with hV | hW
    · rw [ρ.character_eq_zero_of_not_finite hV, Pi.zero_apply, zero_mul]
    · rw [σ.character_eq_zero_of_not_finite hW, Pi.zero_apply, mul_zero]
  rw [hR, character]
  by_cases hHom : Module.Finite k (V →ₗ[k] W)
  · -- `V` or `W` is zero, so `V →ₗ[k] W` is zero and so is the endomorphism `linHom ρ σ g`.
    have : Subsingleton (V →ₗ[k] W) := by
      rcases subsingleton_or_nontrivial V with hV | hV
      · infer_instance
      rcases subsingleton_or_nontrivial W with hW | hW
      · infer_instance
      exact absurd (Module.finite_linearMap_iff.mp hHom) hfin
    have h0 : linHom ρ σ g = 0 := Subsingleton.elim _ _
    rw [h0, map_zero]
  · rw [TauCeti.LinearMap.trace_eq_zero_of_not_finite hHom, LinearMap.zero_apply]

/-- **A coset sum of characters is a trace.** Let `χ` and `χ'` be the characters of `ρ` and `ρ'`,
let `σ = Representation.linHom ρ' ρ` be the action of `G` on `W →ₗ[k] V` by conjugation, and let
`f : H →* G` be a homomorphism from a finite group. Then `∑ h ∈ H, χ(g f(h)) χ'((g f(h))⁻¹)` is
the trace of `σ g ∘ S`, where `S = ∑ h ∈ H, σ (f h)` is the group sum `Representation.norm` of
`σ ∘ f`. For the inclusion `f` of a finite subgroup `N` the left side is the sum over the coset
`g N`; for `f = id` and `g = 1` it is `∑ g, χ(g) χ'(g⁻¹)`. Neither space need be
finite-dimensional (`Representation.character_linHom`). -/
theorem sum_character_mul_mul_character_mul_inv_eq_trace {k G H V W : Type*} [Field k] [Group G]
    [Group H] [Fintype H] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (ρ' : Representation k G W) (f : H →* G) (g : G) :
    ∑ h : H, ρ.character (g * f h) * ρ'.character (g * f h)⁻¹ =
      LinearMap.trace k _ (linHom ρ' ρ g * norm ((linHom ρ' ρ).comp f)) := by
  rw [Representation.norm, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  -- Each term is `σ.character (g * f h)`, the trace of `σ (g * f h) = σ g * σ (f h)`.
  rw [mul_comm (ρ.character _), ← character_linHom, character, MonoidHom.comp_apply, map_mul]

/-- The trace of the action is constant on conjugacy classes. This is `Representation.char_conj`
for a representation on an additive commutative monoid. -/
theorem trace_conj {R G M : Type*} [CommSemiring R] [Group G] [AddCommMonoid M] [Module R M]
    (ρ : Representation R G M) (g h : G) :
    LinearMap.trace R M (ρ (h * g * h⁻¹)) = LinearMap.trace R M (ρ g) := by
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]

/-- **The character at an element acting by a scalar.** If `g` acts on `V` as multiplication by
`c`, the character of `ρ` at `g` is `dim V · c`. When `V` is not finite-dimensional both sides are
`0`. -/
theorem character_eq_finrank_mul_of_apply_eq_smul {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) {g : G} {c : k}
    (h : ∀ v, ρ g v = c • v) : ρ.character g = Module.finrank k V * c := by
  by_cases hV : FiniteDimensional k V
  · have hg : ρ g = c • (1 : Module.End k V) := LinearMap.ext fun v => (h v).trans (by simp)
    simp [character, hg, mul_comm]
  · simp [character_eq_zero_of_not_finite ρ hV, Module.finrank_of_not_finite hV]

/-- **A commutator acting by a nontrivial scalar kills the character.** If the commutator
`g x g⁻¹ x⁻¹` acts on `V` as multiplication by a scalar `a ≠ 1`, then the character of `ρ`
vanishes at `g`. No finiteness of `G` or of `V` is needed. -/
theorem character_eq_zero_of_commutator_apply_eq_smul {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) {g x : G} {a : k} (ha : a ≠ 1)
    (h : ∀ v, ρ (g * x * g⁻¹ * x⁻¹) v = a • v) : ρ.character g = 0 := by
  have hc : ρ (g * x * g⁻¹ * x⁻¹) = a • (1 : Module.End k V) :=
    LinearMap.ext fun v => (h v).trans (by simp)
  have key : ρ.character g = a * ρ.character g :=
    calc ρ.character g = ρ.character (g * x * g⁻¹ * x⁻¹ * (x * g * x⁻¹)) := by
          congr 1
          group
      _ = a * ρ.character g := by
          simp [character, map_mul ρ _ (x * g * x⁻¹), hc, ← trace_conj ρ g x]
  have h1 : (1 - a) * ρ.character g = 0 := by linear_combination key
  exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm ha))

section Average

variable {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [Fintype G]
  [Invertible (Nat.card G : k)] [AddCommGroup V] [Module k V]

/-- **For an irreducible representation and `n` coprime to `|G|`, the average `|G|⁻¹ ∑_g χ(gⁿ)` is
`0` exactly when its character is nontrivial.** Over any field in which `|G|` is invertible. -/
theorem card_inv_mul_sum_char_pow_eq_zero_iff_of_coprime (ρ : Representation k G V)
    [ρ.IsIrreducible] {n : ℕ} (hn : (Nat.card G).Coprime n) :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character (g ^ n) = 0 ↔ ρ.character ≠ fun _ => 1 := by
  have : FiniteDimensional k V := ρ.asModuleEquiv.finiteDimensional
  -- The `n`-th power map permutes `G`, so the average of `χ(gⁿ)` is the dimension of the
  -- invariants.
  rw [Fintype.sum_bijective _ hn.pow_left_bijective _ (ρ.character ·)
    fun _ => rfl, card_inv_mul_sum_char_eq_finrank]
  refine ⟨fun h hχ => ?_, fun hχ => by_contra fun h => hχ ?_⟩
  · rw [← card_inv_mul_sum_char_eq_finrank, hχ, Finset.sum_const, Finset.card_univ,
      Fintype.card_eq_nat_card, nsmul_eq_mul, mul_one, inv_mul_cancel_of_invertible] at h
    exact one_ne_zero h
  · -- A nonzero invariant vector makes `ρ` the trivial line.
    have hne : ρ.invariants ≠ ⊥ := fun hb => h (by rw [hb, finrank_bot, Nat.cast_zero])
    funext g
    rw [‹ρ.IsIrreducible›.eq_trivial_of_invariants_ne_bot hne, char_trivial,
      ‹ρ.IsIrreducible›.finrank_eq_one_of_invariants_ne_bot hne, Nat.cast_one]

end Average

end Representation
