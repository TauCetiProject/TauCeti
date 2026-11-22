/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.FieldEmbedding
public import TauCeti.Topology.Sequences.Small
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# The cardinality of `ℚ_[p]` and complex embeddings of `p`-adic coefficient fields

The field `ℚ_[p]` has the cardinality `𝔠` of the continuum: it is a complete nontrivially
normed field, so it has at least `𝔠` elements, and every element is a limit of a sequence of
rational numbers, so it has at most `ℵ₀ ^ ℵ₀ = 𝔠` elements. An algebraic extension of `ℚ_[p]`,
such as an algebraic closure of `ℚ_[p]`, then has cardinality `𝔠` as well.

Consequently an algebraically closed algebraic extension `E` of `ℚ_[p]` is abstractly isomorphic
to `ℂ`, and every complex embedding of a countable subfield `K ⊆ E`, such as a number field,
extends to a field isomorphism `E ≃+* ℂ`. Such isomorphisms are neither canonical nor
continuous; they are the isomorphisms `ι` from an algebraic closure of `ℚ_[ℓ]` to `ℂ` through
which complex absolute values of `ℓ`-adic Frobenius eigenvalues are read.

## Main results

* `TauCeti.Padic.cardinalMk_eq_continuum`: `#ℚ_[p] = 𝔠`.
* `TauCeti.Padic.cardinalMk_eq_continuum_of_isAlgebraic`: an algebraic extension of `ℚ_[p]` has
  cardinality `𝔠`.
* `TauCeti.Padic.exists_ringEquiv_complex_apply_algebraMap`: a complex embedding of a countable
  field, such as a number field, contained in an algebraically closed algebraic extension `E` of
  `ℚ_[p]` extends to an isomorphism `E ≃+* ℂ`.
* `TauCeti.Padic.nonempty_ringEquiv_complex`: such a field `E` is isomorphic to `ℂ`.

## References

* Pierre Deligne, *La conjecture de Weil. II*, Publications Mathématiques de l'IHÉS 52 (1980),
  Remarque (1.2.11).
-/

public section

universe u

open Cardinal

namespace TauCeti.Padic

variable (p : ℕ) [Fact p.Prime]

/-- The field `ℚ_[p]` of `p`-adic numbers has the cardinality of the continuum. -/
@[simp]
theorem cardinalMk_eq_continuum : #ℚ_[p] = 𝔠 := by
  refine le_antisymm ?_ (continuum_le_cardinal_of_nontriviallyNormedField ℚ_[p])
  calc #ℚ_[p] = #(closure (Set.range ((↑) : ℚ → ℚ_[p]))) := by
        rw [(Padic.denseRange_ratCast p).closure_range, mk_univ]
    _ ≤ #(Set.range ((↑) : ℚ → ℚ_[p])) ^ ℵ₀ := Set.cardinalMk_closure_le _
    _ ≤ ℵ₀ ^ ℵ₀ := power_le_power_right (mk_range_le.trans mk_le_aleph0)
    _ = 𝔠 := aleph0_power_aleph0

/-- An algebraic extension of `ℚ_[p]`, for instance an algebraic closure of `ℚ_[p]`, has the
cardinality of the continuum. -/
theorem cardinalMk_eq_continuum_of_isAlgebraic (E : Type u) [CommRing E] [IsDomain E]
    [Algebra ℚ_[p] E] [Algebra.IsAlgebraic ℚ_[p] E] : #E = 𝔠 := by
  refine le_antisymm ?_ (continuum_le_cardinal_of_module ℚ_[p] E)
  have h := Algebra.IsAlgebraic.lift_cardinalMk_le_max ℚ_[p] E
  rwa [cardinalMk_eq_continuum, lift_continuum, max_eq_left aleph0_le_continuum,
    lift_le_continuum] at h

/-- Let `E` be an algebraically closed algebraic extension of `ℚ_[p]`, for instance an algebraic
closure of `ℚ_[p]`. Every field embedding `σ : K →+* ℂ` of a countable field `K ⊆ E`, for
instance a number field (countable by `Countable.of_moduleFinite`), extends to a field
isomorphism `E ≃+* ℂ`. -/
theorem exists_ringEquiv_complex_apply_algebraMap (E : Type u) [Field E] [IsAlgClosed E]
    [Algebra ℚ_[p] E] [Algebra.IsAlgebraic ℚ_[p] E] {K : Type*} [Field K] [Countable K]
    [Algebra K E] (σ : K →+* ℂ) : ∃ ι : E ≃+* ℂ, ∀ x, ι (algebraMap K E x) = σ x := by
  let := σ.toAlgebra
  obtain ⟨φ⟩ := Complex.nonempty_algEquiv (k := K) (cardinalMk_eq_continuum_of_isAlgebraic p E)
  exact ⟨φ.toRingEquiv, φ.commutes⟩

/-- An algebraically closed algebraic extension of `ℚ_[p]`, for instance an algebraic closure
of `ℚ_[p]`, is isomorphic to `ℂ`. -/
theorem nonempty_ringEquiv_complex (E : Type u) [Field E] [IsAlgClosed E] [Algebra ℚ_[p] E]
    [Algebra.IsAlgebraic ℚ_[p] E] : Nonempty (E ≃+* ℂ) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[p] E).injective
  obtain ⟨ι, -⟩ := exists_ringEquiv_complex_apply_algebraMap p E (Rat.castHom ℂ)
  exact ⟨ι⟩

end TauCeti.Padic
