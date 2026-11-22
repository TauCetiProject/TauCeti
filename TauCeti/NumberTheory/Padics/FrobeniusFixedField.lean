/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.Topology.Algebra.Valued.DiscreteValuationRing
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.Topology.Algebra.Valued.FrobeniusLift

/-!
# The field fixed by a Frobenius lift on a `p`-adic field

Let `K` be a field of characteristic `0`, discretely valued with residue field of characteristic
`p`, with its norm normalised by `‖p‖ = p⁻¹`. We encode this by asking that `K` be a normed
`ℚ_[p]`-algebra whose valuation ring `𝒪[K]` is a discrete valuation ring. For `q > 1`, a
`q`-Frobenius lift on `K` is a continuous ring endomorphism `σ` with `σ a ≡ a ^ q` modulo the
maximal ideal for every `a ∈ 𝒪[K]`, that is, `‖σ a - a ^ q‖ < 1` whenever `‖a‖ ≤ 1`. It need not
be surjective: when the residue field of `K` is imperfect it is not.

Frobenius structures over `K` are `σ`-semilinear, so their constants live in the fixed field
`K^σ = {x | σ x = x}`. Being fixed by a continuous endomorphism, `ℚ_[p]` lies in `K^σ`, which is
therefore an intermediate field `RingHom.padicFixedField σ p hσ` of `K / ℚ_[p]`. This file proves
that `K^σ` is a complete discretely valued field whose residue field has at most `q` elements,
hence a finite extension of `ℚ_[p]` (Tsuzuki, Lemma A.1(1)). Completeness of `K` is used only for
the completeness of `K^σ`.

When `K` is complete with algebraically closed residue field and `σ` preserves norms, the residue
field of `K^σ` has exactly `q` elements: every root of `X ^ q - X` in the residue field of `K` lifts
to `K^σ` (`RingHom.exists_apply_eq_self_and_residue_eq`), and these roots are distinct because a
`q`-Frobenius lift forces `q = 0` in the residue field. In the same situation `K^σ` has the value
group of `K` (`RingHom.exists_apply_eq_self_and_norm_eq`).

## Main definitions

* `RingHom.padicFixedField σ p hσ`: the field fixed by a continuous ring endomorphism `σ` of a
  normed `ℚ_[p]`-algebra, as an intermediate field over `ℚ_[p]`.

## Main results

* `RingHom.completeSpace_padicFixedField`: the fixed field of a continuous endomorphism of a
  complete field is complete.
* `RingHom.isDiscreteValuationRing_integer_padicFixedField`: if `𝒪[K]` is a discrete valuation
  ring, so is the valuation ring of the fixed field.
* `RingHom.finite_residueField_padicFixedField` and
  `RingHom.natCard_residueField_padicFixedField_le`: the residue field of the fixed field of a
  `q`-Frobenius lift is finite with at most `q` elements.
* `RingHom.finiteDimensional_padicFixedField`: the fixed field of a `q`-Frobenius lift on a
  discretely valued `K` is a finite extension of `ℚ_[p]`.
* `RingHom.natCard_residueField_padicFixedField`: if `K` is complete with algebraically closed
  residue field and `σ` preserves norms, the residue field of `K^σ` has exactly `q` elements.

## References

* N. Tsuzuki, *Minimal slope conjecture of F-isocrystals*, Lemma A.1.
-/

public section

open scoped NormedField Valued

namespace RingHom

variable {K : Type*} [NontriviallyNormedField K] (σ : K →+* K)

/-- The field `K^σ` of elements fixed by a continuous ring endomorphism `σ` of a normed
`ℚ_[p]`-algebra `K`, as an intermediate field of `K / ℚ_[p]`. -/
noncomputable def padicFixedField (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (hσ : Continuous σ) : IntermediateField ℚ_[p] K :=
  (σ.eqLocusField (RingHom.id K)).toIntermediateField (σ.map_algebraMap_padic_of_continuous hσ)

variable {σ} {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K] (hσ : Continuous σ)

/-- An element lies in `K^σ` exactly when `σ` fixes it. -/
@[simp]
theorem mem_padicFixedField {x : K} : x ∈ σ.padicFixedField p hσ ↔ σ x = x := Iff.rfl

/-- As a subfield, `K^σ` is the equalizer of `σ` and the identity. -/
@[simp]
theorem toSubfield_padicFixedField :
    (σ.padicFixedField p hσ).toSubfield = σ.eqLocusField (RingHom.id K) :=
  Subfield.ext fun _ ↦ Iff.rfl

/-- The fixed field of a continuous endomorphism of a complete field is closed, hence complete. -/
instance completeSpace_padicFixedField [CompleteSpace K] :
    CompleteSpace (σ.padicFixedField p hσ) :=
  -- The carrier of `K^σ` is by definition that of `σ.eqLocusField (RingHom.id K)`, the set
  -- `{x | σ x = x}`, which is `{x | σ x = id x}` by unfolding `RingHom.id`.
  (isClosed_eq hσ continuous_id : IsClosed (σ.padicFixedField p hσ : Set K)).completeSpace_coe

variable [IsUltrametricDist K]

/-- If the valuation ring of `K` is a discrete valuation ring, so is the valuation ring of the
field fixed by a continuous ring endomorphism: `K^σ` is a discretely valued field. -/
instance isDiscreteValuationRing_integer_padicFixedField [IsDiscreteValuationRing 𝒪[K]] :
    IsDiscreteValuationRing 𝒪[σ.padicFixedField p hσ] :=
  (σ.padicFixedField p hσ).val.toRingHom.isDiscreteValuationRing_integer_of_norm_map_eq
    (K := K) fun x ↦ (AddSubgroupClass.coe_norm (σ.padicFixedField p hσ) x).symm

variable {q : ℕ} (hq : 1 < q) (hσq : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ q‖ < 1)
include hq hσq

omit [IsUltrametricDist K] hq in
/-- An element of norm at most `1` fixed by a `q`-Frobenius lift is congruent to its `q`-th power
modulo the maximal ideal. -/
private theorem norm_pow_sub_lt_one_of_mem_padicFixedField (a : σ.padicFixedField p hσ)
    (ha : ‖a‖ ≤ 1) : ‖a ^ q - a‖ < 1 := by
  -- The norm of `K^σ` is that of `K` through the coercion (`SubfieldClass.toNormedField`), and
  -- the coercion commutes with `^` and `-`, so `hσq` applies to `a` and closes the goal.
  simpa [norm_sub_rev, (mem_padicFixedField hσ).1 a.property] using hσq a ha

/-- The residue field of the field fixed by a `q`-Frobenius lift is finite. -/
theorem finite_residueField_padicFixedField : _root_.Finite 𝓀[σ.padicFixedField p hσ] :=
  Valued.integer.finite_residueField_of_norm_pow_sub_lt_one hq
    (norm_pow_sub_lt_one_of_mem_padicFixedField hσ hσq)

/-- The residue field of the field fixed by a `q`-Frobenius lift has at most `q` elements. -/
theorem natCard_residueField_padicFixedField_le : Nat.card 𝓀[σ.padicFixedField p hσ] ≤ q :=
  Valued.integer.natCard_residueField_le_of_norm_pow_sub_lt_one hq
    (norm_pow_sub_lt_one_of_mem_padicFixedField hσ hσq)

/-- **Tsuzuki, Lemma A.1(1)**: if the valuation ring of `K` is a discrete valuation ring, the field
`K^σ` fixed by a `q`-Frobenius lift `σ` is a finite extension of `ℚ_[p]`. -/
theorem finiteDimensional_padicFixedField [IsDiscreteValuationRing 𝒪[K]] :
    FiniteDimensional ℚ_[p] (σ.padicFixedField p hσ) := by
  have := finite_residueField_padicFixedField (p := p) hσ hq hσq
  exact Valued.integer.finiteDimensional_of_finite_residueField (K := σ.padicFixedField p hσ) ℚ_[p]

open Polynomial in
/-- **Tsuzuki, Lemma A.1(2), residue field**: if `K` is complete with discrete valuation ring and
algebraically closed residue field, the residue field of the field `K^σ` fixed by a
norm-preserving `q`-Frobenius lift `σ` has exactly `q` elements; it is `𝔽_q`. -/
theorem natCard_residueField_padicFixedField [CompleteSpace K] [IsDiscreteValuationRing 𝒪[K]]
    [IsAlgClosed 𝓀[K]] (hσn : ∀ a, ‖σ a‖ = ‖a‖) : Nat.card 𝓀[σ.padicFixedField p hσ] = q := by
  refine le_antisymm (natCard_residueField_padicFixedField_le hσ hq hσq) ?_
  have := finite_residueField_padicFixedField (p := p) hσ hq hσq
  -- The inclusion `K^σ → K` induces an injection of residue fields whose range contains every
  -- root of `X ^ q - X`.
  let ι := (σ.padicFixedField p hσ).val.toRingHom
  have hι (x : σ.padicFixedField p hσ) : ‖ι x‖ ≤ ‖x‖ :=
    (AddSubgroupClass.coe_norm (σ.padicFixedField p hσ) x).le
  let f := IsLocalRing.ResidueField.map (ι.integerRestrict hι)
  have hroot (ξ : 𝓀[K]) (hξ : ξ ^ q = ξ) : ∃ η, f η = ξ := by
    obtain ⟨b, hb, rfl⟩ := σ.exists_apply_eq_self_and_residue_eq hσq hσn hq hξ
    let b' : 𝒪[σ.padicFixedField p hσ] :=
      ⟨⟨b, hb⟩, Valued.integer.mem_iff.2 (Valued.integer.mem_iff.1 b.property)⟩
    refine ⟨IsLocalRing.residue _ b', ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]
    exact congrArg _ (Subtype.ext (ι.coe_integerRestrict_apply hι b'))
  -- Since `q = 0` in the algebraically closed field `𝓀[K]`, `X ^ q - X` has `q` distinct roots.
  have hq₀ := Valued.integer.natCast_eq_zero_of_norm_apply_sub_pow_lt_one σ hσq hq
  have := ringChar.charP 𝓀[K]
  have hsep := galois_poly_separable (K := 𝓀[K]) _ q (ringChar.dvd hq₀)
  have hcard : Nat.card ((X ^ q - X : 𝓀[K][X]).rootSet 𝓀[K]) = q := by
    rw [Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _),
      natDegree_X_pow_sub_X hq]
  have hmem (ξ : (X ^ q - X : 𝓀[K][X]).rootSet 𝓀[K]) : ξ.val ^ q = ξ.val := by
    simpa [sub_eq_zero, X_pow_sub_X_ne_zero hq] using (mem_rootSet.1 ξ.property).2
  rw [← hcard]
  refine Nat.card_le_card_of_injective (fun ξ ↦ (hroot ξ (hmem ξ)).choose) fun ξ ξ' h ↦ ?_
  rw [Subtype.ext_iff, ← (hroot ξ (hmem ξ)).choose_spec, ← (hroot ξ' (hmem ξ')).choose_spec]
  exact congrArg f h

end RingHom
