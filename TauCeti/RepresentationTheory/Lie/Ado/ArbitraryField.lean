/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Lie.Ado.CharacteristicZero
public import TauCeti.RepresentationTheory.Lie.Ado.PositiveCharacteristic
public import TauCeti.RepresentationTheory.Lie.FiniteTarget
public import TauCeti.RepresentationTheory.Lie.MatrixTarget

/-!
# The Ado–Iwasawa theorem over an arbitrary field

Every finite-dimensional Lie algebra over a field has a faithful finite-dimensional
representation, and by Hochschild's strengthening one can be chosen in which every `ad`-nilpotent
element acts nilpotently. The two characteristics are proved separately: characteristic zero by
growing a representation along a chain of subalgebras and then applying Hochschild's nilpotence
argument (`TauCeti.exists_faithful_preserving_ad_nilpotence_charZero`), prime characteristic by
left multiplication on a finite-dimensional quotient of the universal enveloping algebra
(`TauCeti.exists_faithful_preserving_ad_nilpotence_charP`). This file joins them.

The join is a dispatch on `ringChar K`, which for a field is either `0` or a prime: in the first
case `CharZero K` holds, in the second `CharP K (ringChar K)` with a prime characteristic. The
dispatch is instance plumbing only, and it is kept out of the two constructions it combines. Both
inputs already have the strengthened form, so the join is made on that form and the weaker
statements are read off from it.

Elements of the nilradical are `ad`-nilpotent
(`TauCeti.LieAlgebra.isNilpotent_ad_of_mem_nilradical`), so the representation lets the nilradical
act nilpotently. For a nilpotent `L` the nilradical is all of `L`
(`TauCeti.LieAlgebra.nilradical_eq_top_of_isNilpotent`), so the representation is then by
nilpotent endomorphisms throughout.

Transporting the representation along a basis turns it into an injective Lie homomorphism into a
matrix algebra, so a finite-dimensional Lie algebra over a field is isomorphic to a Lie
subalgebra of `Matrix (Fin n) (Fin n) K`. The two formulations are equivalent for any Lie algebra
at all (`TauCeti.faithfulRepresentation_iff_exists_injective_lieHom_matrix`): a basis converts
endomorphisms into matrices, and a matrix algebra acts on the coordinate space. Specialized to
`K = ℝ`, the matrix form is the embedding `L ↪ 𝔤𝔩_n(ℝ)` that integration of a real Lie algebra to
a Lie group consumes.

Read through `TauCeti.faithfulRepresentation_iff_finiteEnvelopingTarget`, the theorem says that the
canonical copy of `L` in `U(L)` is separated by a finite-dimensional associative target of `U(L)`.
That is residual finite dimensionality in degree one, and only in degree one: nothing here claims
that every element of `U(L)` survives in some finite-dimensional quotient.

## Main results

* `TauCeti.exists_faithful_preserving_ad_nilpotence`: **Hochschild's strengthening of the
  Ado–Iwasawa theorem**, over an arbitrary field: a faithful finite-dimensional representation in
  which every `ad`-nilpotent element acts nilpotently.
* `TauCeti.exists_faithful_nilrepresentation`: over an arbitrary field, a faithful
  finite-dimensional representation in which every element of the nilradical acts nilpotently.
* `TauCeti.adoIwasawa`: **the Ado–Iwasawa theorem**, over an arbitrary field.
* `TauCeti.exists_faithful_nilrepresentation_of_isNilpotent`: a nilpotent Lie algebra has a
  faithful finite-dimensional representation by nilpotent endomorphisms.
* `TauCeti.exists_injective_lieHom_matrix`: the matrix form of the theorem.
* `TauCeti.exists_lieSubalgebra_matrix_nonempty_equiv`: every finite-dimensional Lie algebra over a
  field is isomorphic to a Lie subalgebra of a matrix algebra.
* `TauCeti.exists_finiteEnvelopingTarget`: the canonical copy of `L` in `U(L)` is separated by a
  finite-dimensional associative target.

## References

* K. Iwasawa, *On the representation of Lie algebras*, Japanese Journal of Mathematics **19**
  (1948), 405--426.
* G. Hochschild, *An Addition to Ado's Theorem*, Proceedings of the American Mathematical Society
  **17** (1966), 531--533.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter VI.
-/

public section

namespace TauCeti

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

section General

variable (K : Type u) (L : Type v) [Field K] [LieRing L] [LieAlgebra K L]
variable [FiniteDimensional K L]

/-- **Hochschild's strengthening of the Ado–Iwasawa theorem.** A finite-dimensional Lie algebra
over an arbitrary field has a faithful finite-dimensional representation that preserves
nilpotence of the adjoint action: every `ad`-nilpotent element acts nilpotently. -/
theorem exists_faithful_preserving_ad_nilpotence :
    ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (ρ : L →ₗ⁅K⁆ Module.End K V),
      Function.Injective ρ ∧ ∀ x : L, IsNilpotent (LieAlgebra.ad K L x) → IsNilpotent (ρ x) := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hprime | hzero
  · have : Fact (ringChar K).Prime := ⟨hprime⟩
    exact exists_faithful_preserving_ad_nilpotence_charP K L (ringChar K)
  · rw [CharP.ringChar_zero_iff_CharZero] at hzero
    exact exists_faithful_preserving_ad_nilpotence_charZero K L

/-- **The Ado–Iwasawa theorem with nilpotence on the nilradical.** A finite-dimensional Lie
algebra over an arbitrary field has a faithful finite-dimensional representation in which every
element of the nilradical acts nilpotently. -/
theorem exists_faithful_nilrepresentation :
    ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (ρ : L →ₗ⁅K⁆ Module.End K V),
      Function.Injective ρ ∧ ∀ x ∈ LieAlgebra.nilradical K L, IsNilpotent (ρ x) := by
  obtain ⟨V, _, _, _, ρ, hinj, hnil⟩ := exists_faithful_preserving_ad_nilpotence K L
  exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, hinj,
    fun x hx ↦ hnil x (LieAlgebra.isNilpotent_ad_of_mem_nilradical hx)⟩

/-- **The Ado–Iwasawa theorem.** Every finite-dimensional Lie algebra over a field admits a
faithful finite-dimensional representation. -/
theorem adoIwasawa :
    ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (ρ : L →ₗ⁅K⁆ Module.End K V), Function.Injective ρ := by
  obtain ⟨V, _, _, _, ρ, hρ, -⟩ := exists_faithful_preserving_ad_nilpotence K L
  exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, hρ⟩

/-- **A finite-dimensional nilpotent Lie algebra over a field has a faithful finite-dimensional
representation by nilpotent endomorphisms.** The nilradical of a nilpotent Lie algebra is the
whole algebra, so the nilpotence supplied by `TauCeti.exists_faithful_nilrepresentation` covers
every element. -/
theorem exists_faithful_nilrepresentation_of_isNilpotent [LieRing.IsNilpotent L] :
    ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (ρ : L →ₗ⁅K⁆ Module.End K V),
      Function.Injective ρ ∧ ∀ x : L, IsNilpotent (ρ x) := by
  obtain ⟨V, _, _, _, ρ, hinj, hnil⟩ := exists_faithful_nilrepresentation K L
  exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, hinj, fun x ↦ hnil x (by simp)⟩

/-- **The matrix form of the Ado–Iwasawa theorem.** Every finite-dimensional Lie algebra over a
field embeds in `𝔤𝔩_n = Matrix (Fin n) (Fin n) K` for some `n`. Over `ℝ` this is the embedding
consumed by the integration of a real Lie algebra to a Lie group. -/
theorem exists_injective_lieHom_matrix :
    ∃ (n : ℕ) (f : L →ₗ⁅K⁆ Matrix (Fin n) (Fin n) K), Function.Injective f :=
  (faithfulRepresentation_iff_exists_injective_lieHom_matrix K L).1 (adoIwasawa K L)

/-- **Every finite-dimensional Lie algebra over a field is a matrix Lie algebra**: it is
isomorphic to a Lie subalgebra of `Matrix (Fin n) (Fin n) K` for some `n`, namely to the range of
the embedding of `TauCeti.exists_injective_lieHom_matrix`. -/
theorem exists_lieSubalgebra_matrix_nonempty_equiv :
    ∃ (n : ℕ) (H : LieSubalgebra K (Matrix (Fin n) (Fin n) K)), Nonempty (L ≃ₗ⁅K⁆ H) := by
  obtain ⟨n, f, hf⟩ := exists_injective_lieHom_matrix K L
  exact ⟨n, f.range, ⟨f.equivRangeOfInjective hf⟩⟩

end General

variable (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

/-- **Residual finite dimensionality in degree one.** The universal enveloping algebra of a
finite-dimensional Lie algebra over a field has a finite-dimensional associative target separating
the canonical copy of the Lie algebra. This is `TauCeti.adoIwasawa` read through the finite-target
equivalence `TauCeti.faithfulRepresentation_iff_finiteEnvelopingTarget`, and it is a statement
about degree one only: nothing here says that `U(L)` is residually finite dimensional. -/
theorem exists_finiteEnvelopingTarget :
    ∃ (A : Type u) (_ : Ring A) (_ : Algebra K A) (_ : FiniteDimensional K A)
      (q : UniversalEnvelopingAlgebra K L →ₐ[K] A),
      Function.Injective fun x : L ↦ q (UniversalEnvelopingAlgebra.ι K x) :=
  (faithfulRepresentation_iff_finiteEnvelopingTarget K L).1 (adoIwasawa K L)

end TauCeti
