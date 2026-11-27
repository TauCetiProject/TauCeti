/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IsAlgClosed.Embedding
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Field embeddings into `ℂ` extending a given embedding

Let `k` be a countable commutative ring with an injective ring homomorphism `σ : k →+* ℂ`,
viewed as the `k`-algebra structure `σ.toAlgebra` on `ℂ`, and let `E` be a domain containing `k`.

* If `#E ≤ 𝔠`, then `σ` extends to `E`: there is a `k`-algebra homomorphism `E →ₐ[k] ℂ`,
  a field embedding when `E` is a field.
* If moreover `E` is algebraically closed with `#E = 𝔠`, then `σ` extends to a field
  isomorphism `E ≃ₐ[k] ℂ`.
* In both cases a prescribed element `α ∈ E` transcendental over `k` may be sent to any
  prescribed `z ∈ ℂ` transcendental over `k`.

The proofs extend a transcendence basis: `ℂ` has transcendence degree `𝔠` over every countable
subring, while `E` has transcendence degree at most `#E`. These embeddings are the
non-canonical and discontinuous complex embeddings of coefficient fields, such as algebraic
closures of `ℚ_[p]`, through which `ℓ`-adic Frobenius eigenvalues are compared with complex
absolute values.

## Main results

* `TauCeti.Complex.trdeg_eq_continuum`: `ℂ` has transcendence degree `𝔠` over a countable
  commutative ring acting faithfully.
* `TauCeti.Complex.nonempty_algHom`, `TauCeti.Complex.nonempty_algEquiv`: extension of a complex
  embedding of a countable commutative ring to a homomorphism, respectively an isomorphism.
* `TauCeti.Complex.exists_algHom_apply_eq`, `TauCeti.Complex.exists_algEquiv_apply_eq`: the same
  over a countable commutative ring, with a transcendental element sent to a prescribed
  transcendental complex number.

## References

* Pierre Deligne, *La conjecture de Weil. II*, Publications Mathématiques de l'IHÉS 52 (1980),
  Remarque (1.2.11).
-/

public section

universe u

open Cardinal Algebra

namespace TauCeti.Complex

/-- `ℂ` has transcendence degree `𝔠` over every countable commutative ring `k` acting faithfully
on `ℂ`. -/
@[simp]
theorem trdeg_eq_continuum {k : Type*} [CommRing k] [Countable k] [Algebra k ℂ]
    [FaithfulSMul k ℂ] : trdeg k ℂ = 𝔠 := by
  rw [trdeg_eq_cardinalMk (by rw [mk_complex]; exact aleph0_lt_continuum),
    mk_complex]

/-- A domain of cardinality `𝔠` has the same transcendence degree as `ℂ` over a
countable commutative ring acting faithfully on both. -/
private theorem lift_trdeg_eq {k : Type*} {E : Type u} [CommRing k] [Countable k]
    [Algebra k ℂ] [FaithfulSMul k ℂ] [CommRing E] [IsDomain E] [Algebra k E]
    [FaithfulSMul k E] (hE : #E = 𝔠) :
    Cardinal.lift.{0} (trdeg k E) = Cardinal.lift.{u} (trdeg k ℂ) := by
  simp [trdeg_eq_continuum, trdeg_eq_cardinalMk (hE ▸ aleph0_lt_continuum), hE]

/-- A commutative ring over which some element of `A` is transcendental acts faithfully on `A`. -/
private theorem _root_.Transcendental.faithfulSMul {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] {x : A} (hx : Transcendental R x) : FaithfulSMul R A :=
  have : Algebra.Transcendental R A := ⟨⟨x, hx⟩⟩
  (faithfulSMul_iff_algebraMap_injective R A).2 Algebra.injective_of_transcendental

section CommRing

variable {k : Type*} {E : Type u} [CommRing k] [Countable k] [Algebra k ℂ] [FaithfulSMul k ℂ]

/-- A commutative algebra of cardinality at most `𝔠` has transcendence degree at most that of
`ℂ` over a countable commutative ring acting faithfully on `ℂ`. -/
private theorem lift_trdeg_le [CommRing E] [Algebra k E] (hE : #E ≤ 𝔠) :
    Cardinal.lift.{0} (trdeg k E) ≤ Cardinal.lift.{u} (trdeg k ℂ) := by
  rw [trdeg_eq_continuum, lift_continuum, lift_le_continuum]
  -- `Algebra.trdeg` is the supremum of the cardinalities of algebraically independent subsets.
  have hle : trdeg k E ≤ #E := by
    rw [Algebra.trdeg]
    exact ciSup_le' fun s ↦ mk_set_le s.val
  exact hle.trans hE

/-- Every complex embedding of a countable commutative ring `k`, given as a faithful `k`-algebra
structure on `ℂ`, extends to every domain `E` containing `k` with `#E ≤ 𝔠`. -/
theorem nonempty_algHom [CommRing E] [IsDomain E] [Algebra k E] [FaithfulSMul k E]
    (hE : #E ≤ 𝔠) :
    Nonempty (E →ₐ[k] ℂ) :=
  let ⟨φ, _⟩ := IsAlgClosed.exists_algHom_injective_of_lift_trdeg_le (lift_trdeg_le hE); ⟨φ⟩

/-- Every complex embedding of a countable commutative ring `k`, given as a faithful `k`-algebra
structure on `ℂ`, extends to an isomorphism with `ℂ` of every algebraically closed field `E`
containing `k` with `#E = 𝔠`. -/
theorem nonempty_algEquiv [Field E] [IsAlgClosed E] [Algebra k E] [FaithfulSMul k E]
    (hE : #E = 𝔠) :
    Nonempty (E ≃ₐ[k] ℂ) :=
  IsAlgClosed.nonempty_algEquiv_of_lift_trdeg_eq (lift_trdeg_eq hE)

omit [FaithfulSMul k ℂ] in
/-- For a domain `E` over a countable commutative ring `k` with `#E ≤ 𝔠`, an element `α ∈ E`
transcendental over `k` and a complex number `z` transcendental over `k`, some `k`-algebra
homomorphism `E →ₐ[k] ℂ` sends `α` to `z`. -/
theorem exists_algHom_apply_eq [CommRing E] [IsDomain E] [Algebra k E] (hE : #E ≤ 𝔠) {α : E}
    {z : ℂ} (hα : Transcendental k α) (hz : Transcendental k z) : ∃ φ : E →ₐ[k] ℂ, φ α = z := by
  have := hz.faithfulSMul
  obtain ⟨φ, _, hφ⟩ := hα.exists_algHom_apply_eq hz (lift_trdeg_le hE)
  exact ⟨φ, hφ⟩

omit [FaithfulSMul k ℂ] in
/-- For an algebraically closed field `E` over a countable commutative ring `k` with `#E = 𝔠`,
an element `α ∈ E` transcendental over `k` and a complex number `z` transcendental over `k`, some
isomorphism `E ≃ₐ[k] ℂ` sends `α` to `z`. -/
theorem exists_algEquiv_apply_eq [Field E] [IsAlgClosed E] [Algebra k E] (hE : #E = 𝔠) {α : E}
    {z : ℂ} (hα : Transcendental k α) (hz : Transcendental k z) : ∃ φ : E ≃ₐ[k] ℂ, φ α = z := by
  have := hα.faithfulSMul
  have := hz.faithfulSMul
  exact hα.exists_algEquiv_apply_eq hz (lift_trdeg_eq hE)

end CommRing

end TauCeti.Complex
