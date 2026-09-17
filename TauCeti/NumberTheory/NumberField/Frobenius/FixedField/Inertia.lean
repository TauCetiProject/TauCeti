/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Index
public import TauCeti.GroupTheory.Index.Basic
public import TauCeti.NumberTheory.NumberField.FixedField
public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup

/-!
# Ramification and residue degrees below a fixed field

Let `H` be a subgroup of `Gal(L/K)`, let `E = L ^ H`, and let `Q` be a nonzero prime of `𝓞 L`
over `𝓞 K`. The product of the ramification index and residue degree of `Q ∩ 𝓞 E` over
`𝓞 K` is the relative index

`[D(Q) : D(Q) ∩ H]`.

Equivalently, multiplying that product by the order of `D(Q) ∩ H` gives the corresponding
product for `Q` over `𝓞 K`. The proof combines multiplicativity of ramification indices and
residue degrees in the tower `K ⊆ E ⊆ L` with the identification of the decomposition group over
`E` with `D(Q) ∩ H`. Applied to a translate `σ • Q`, this is the decomposition-group index formula
for the prime of `E` below that translate.

The ramification index alone is the relative index `[I(Q) : I(Q) ∩ H]` of inertia groups, by the
same argument with the inertia group of `Q` over `E` identified with `I(Q) ∩ H`. So the prime
below `Q` in `E` has `e = 1` exactly when `I(Q) ≤ H`, and `e = f = 1` exactly when `D(Q) ≤ H`.

If `Q` is unramified over `K`, all ramification indices in the tower are one. The general formula
then specializes to the residue-degree identity previously used in Frobenius arguments. Nothing
in either statement needs `H` cyclic: the Galois correspondence identifies
`Gal(L/E)` with `H` acting on ideals exactly as it does over `K`, so the decomposition group of `Q`
over `E` corresponds to `H ⊓ D(Q)` and in particular has as many elements, and multiplicativity of
the two local invariants does the rest.

A Frobenius `φ` at `Q` generates `D(Q)`, so the count is `Subgroup.relIndex` — the index of
`H ⊓ ⟨φ⟩` in `⟨φ⟩` — and the residue degree is one exactly when `φ ∈ H`.  At `H = ⟨φ⟩` membership
is automatic and the degree is one, which is the hypothesis of
`NumberField.restrictScalars_eq_of_inertiaDeg_eq_one` and so the step a fixed-field fibre count
runs through.

## Main results

* `Ideal.ramificationIdx_mul_inertiaDeg_under_fixedField_mul_card_inf`: the local degree below
  `L ^ H`, multiplied by the order of `D(Q) ∩ H`, is the local degree of `Q` over the base.
* `Ideal.ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex`: the local degree below
  `L ^ H` is `[D(Q) : D(Q) ∩ H]`.
* `Ideal.ramificationIdx_under_fixedField_mul_card_inf`: the ramification index below `L ^ H`,
  multiplied by the order of `I(Q) ∩ H`, is the ramification index of `Q` over the base.
* `Ideal.ramificationIdx_under_fixedField_eq_relIndex`: the ramification index below `L ^ H` is
  `[I(Q) : I(Q) ∩ H]`.
* `Ideal.inertiaDeg_under_fixedField_mul_card_inf`: the number of elements of `D(Q) ⊓ H` times the
  residue degree below `L ^ H` is the residue degree of `Q`.
* `Ideal.inertiaDeg_under_fixedField_eq_relIndex`: that residue degree is `Subgroup.relIndex`,
  the index of `H ⊓ ⟨φ⟩` in `⟨φ⟩`.
* `Ideal.isLeast_pow_mem_inertiaDeg_under_fixedField`: equivalently, it is the least `n ≥ 1` with
  `φ ^ n ∈ H`.
* `Ideal.inertiaDeg_under_fixedField_eq_one_iff`: it is one exactly when a Frobenius lies in `H`.
* `Ideal.inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt`: at `σ = φ`, it is one.

## References

The decomposition-group index formula is Neukirch, *Algebraic Number Theory*, Chapter I, §9,
and Janusz, *Algebraic Number Fields*, Chapter I. The unramified Frobenius specialization also
appears in Sharifi, *Algebraic Number Theory*, Theorem 7.2.2. The corresponding step of the
Birkbeck--Brasca Chebotarev development,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0) at
commit `55a89985d47a3befcf6069aca1da250ff088b5c7`, is the private declaration
`inertiaDeg_under_E_eq_one_of_frobenius` in `CebotarevDensity/FixedFieldDensity.lean`.  There it is
one conjunct of a triple that also records the ramification index and the residue-field count, and
it carries `orderOf σ = Nat.card Gal(L/E)` as a hypothesis; that equality is a consequence of the
Galois correspondence and is derived here rather than assumed.  Upstream states only the `σ = φ`
case; the general residue degree above is not there.
-/

public section

open IntermediateField

open scoped NumberField Pointwise

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

omit [IsGalois K L] in
/-- **The local-degree product below a fixed field.** For any subgroup `H` and `E = L ^ H`, the
ramification index times the residue degree of `Q ∩ 𝓞 E` over `𝓞 K`, multiplied by the size of
`D(Q) ∩ H`, is the ramification index times the residue degree of `Q` over `𝓞 K`.

This is the division-free form of
`Ideal.ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex`. -/
theorem ramificationIdx_mul_inertiaDeg_under_fixedField_mul_card_inf
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (H : Subgroup (L ≃ₐ[K] L)) :
    (Q.under (𝓞 ↥(fixedField H))).ramificationIdx (𝓞 K)
          * (Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K)
          * Nat.card ((MulAction.stabilizer (L ≃ₐ[K] L) Q ⊓ H : Subgroup (L ≃ₐ[K] L)))
      = Q.ramificationIdx (𝓞 K) * Q.inertiaDeg (𝓞 K) := by
  set E := fixedField H
  let _ : IsScalarTower K E L := E.isScalarTower_mid'
  let _ : IsGalois E L := IsGalois.of_fixed_field L H
  have hcard :
      Nat.card ((MulAction.stabilizer (L ≃ₐ[K] L) Q ⊓ H : Subgroup (L ≃ₐ[K] L)))
        = Q.ramificationIdx (𝓞 E) * Q.inertiaDeg (𝓞 E) := by
    rw [← card_stabilizer_fixedField_eq_card_inf Q H,
      Ideal.card_stabilizer_eq (Q.under (𝓞 E)) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 E)) Q (L ≃ₐ[E] L),
      Ideal.inertiaDegIn_eq_inertiaDeg (Q.under (𝓞 E)) Q (L ≃ₐ[E] L)]
  rw [hcard, Ideal.ramificationIdx_tower (R := 𝓞 K) (Q.under (𝓞 E)) Q,
    Ideal.inertiaDeg_tower (R := 𝓞 K) (Q.under (𝓞 E)) Q]
  ring

/-- **The decomposition-group index formula.** For any subgroup `H` of `Gal(L/K)`, the
ramification index times the residue degree of the prime below `Q` in `L ^ H` is the index of
`D(Q) ∩ H` in the decomposition group `D(Q)`.

Instantiating this theorem at `σ • Q` gives the usual double-coset formula
`e(𝔮_σ/𝔭) f(𝔮_σ/𝔭) = [σDσ⁻¹ : H ∩ σDσ⁻¹]`. -/
theorem ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (H : Subgroup (L ≃ₐ[K] L)) :
    (Q.under (𝓞 ↥(fixedField H))).ramificationIdx (𝓞 K)
        * (Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) =
      H.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) Q) := by
  let D := MulAction.stabilizer (L ≃ₐ[K] L) Q
  have hmul := ramificationIdx_mul_inertiaDeg_under_fixedField_mul_card_inf Q H
  have hcardD : Nat.card D = Q.ramificationIdx (𝓞 K) * Q.inertiaDeg (𝓞 K) := by
    rw [Ideal.card_stabilizer_eq (Q.under (𝓞 K)) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 K)) Q (L ≃ₐ[K] L),
      Ideal.inertiaDegIn_eq_inertiaDeg (Q.under (𝓞 K)) Q (L ≃ₐ[K] L)]
  have hidx := Subgroup.relIndex_inf_mul_relIndex ⊥ H D
  simp only [Subgroup.relIndex_bot_left, bot_inf_eq] at hidx
  rw [inf_comm, hcardD, ← hmul, mul_comm] at hidx
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hidx.symm

omit [IsGalois K L] in
/-- **The ramification index below a fixed field.** For any subgroup `H` and `E = L ^ H`, the
ramification index of `Q ∩ 𝓞 E` over `𝓞 K`, multiplied by the size of `I(Q) ∩ H`, is the
ramification index of `Q` over `𝓞 K`.

This is the division-free form of `Ideal.ramificationIdx_under_fixedField_eq_relIndex`. -/
theorem ramificationIdx_under_fixedField_mul_card_inf
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (H : Subgroup (L ≃ₐ[K] L)) :
    (Q.under (𝓞 ↥(fixedField H))).ramificationIdx (𝓞 K)
          * Nat.card ((Q.inertia (L ≃ₐ[K] L) ⊓ H : Subgroup (L ≃ₐ[K] L)))
      = Q.ramificationIdx (𝓞 K) := by
  set E := fixedField H
  let _ : IsScalarTower K E L := E.isScalarTower_mid'
  let _ : IsGalois E L := IsGalois.of_fixed_field L H
  rw [← card_inertia_fixedField_eq_card_inf Q H,
    Ideal.card_inertia_eq_ramificationIdx (𝓞 E) (L ≃ₐ[E] L) Q,
    Ideal.ramificationIdx_tower (R := 𝓞 K) (Q.under (𝓞 E)) Q]

/-- **The inertia-group index formula.** For any subgroup `H` of `Gal(L/K)`, the ramification
index of the prime below `Q` in `L ^ H` is the index of `I(Q) ∩ H` in the inertia group `I(Q)`.

In particular that prime is unramified over `𝓞 K` exactly when `I(Q) ≤ H`, by
`Subgroup.relIndex_eq_one`. -/
theorem ramificationIdx_under_fixedField_eq_relIndex
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (H : Subgroup (L ≃ₐ[K] L)) :
    (Q.under (𝓞 ↥(fixedField H))).ramificationIdx (𝓞 K) =
      H.relIndex (Q.inertia (L ≃ₐ[K] L)) := by
  have hidx := Subgroup.relIndex_inf_mul_relIndex ⊥ H (Q.inertia (L ≃ₐ[K] L))
  simp only [Subgroup.relIndex_bot_left, bot_inf_eq] at hidx
  rw [inf_comm, Ideal.card_inertia_eq_ramificationIdx (𝓞 K) (L ≃ₐ[K] L) Q,
    ← ramificationIdx_under_fixedField_mul_card_inf Q H, mul_comm] at hidx
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hidx.symm

omit [IsGalois K L] in
/-- **The residue degree below a fixed field.**  For any subgroup `H` and `E = L ^ H`, the residue
degree of `Q ∩ 𝓞 E` over `𝓞 K` times the size of the intersection of `H` with the decomposition
group is the residue degree of `Q` itself.  Stated as a product, so no natural-number division is
truncated. -/
theorem inertiaDeg_under_fixedField_mul_card_inf (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (H : Subgroup (L ≃ₐ[K] L)) :
    (Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K)
        * Nat.card ((MulAction.stabilizer (L ≃ₐ[K] L) Q ⊓ H : Subgroup (L ≃ₐ[K] L)))
      = Q.inertiaDeg (𝓞 K) := by
  set E := fixedField H with hE
  have : IsScalarTower K ↥E L := E.isScalarTower_mid'
  have : IsGalois ↥E L := IsGalois.of_fixed_field L H
  have : Algebra.IsUnramifiedAt (𝓞 ↥E) Q := Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 K) Q
  have htower : Q.inertiaDeg (𝓞 K)
      = (Q.under (𝓞 ↥E)).inertiaDeg (𝓞 K) * Q.inertiaDeg (𝓞 ↥E) :=
    inertiaDeg_tower (Q.under (𝓞 ↥E)) Q
  rw [htower, ← card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt Q hQ,
    card_stabilizer_fixedField_eq_card_inf Q H]

/-- **The residue degree is a relative index.**  For any subgroup `H` and `φ` a Frobenius at an
unramified `Q`, the residue degree below `L ^ H` is `Subgroup.relIndex`, Mathlib's name for the
index of `H ⊓ ⟨φ⟩` in `⟨φ⟩`. -/
theorem inertiaDeg_under_fixedField_eq_relIndex (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (H : Subgroup (L ≃ₐ[K] L)) {φ : L ≃ₐ[K] L}
    (hφ : IsArithFrobAt (𝓞 K) φ Q) :
    (Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) = H.relIndex (Subgroup.zpowers φ) := by
  have hmul := inertiaDeg_under_fixedField_mul_card_inf Q hQ H
  rw [← zpowers_eq_stabilizer_of_isArithFrobAt Q hQ hφ,
    ← orderOf_eq_inertiaDeg_of_isArithFrobAt Q hQ hφ] at hmul
  have hidx := Subgroup.relIndex_inf_mul_relIndex ⊥ H (Subgroup.zpowers φ)
  simp only [Subgroup.relIndex_bot_left, bot_inf_eq] at hidx
  rw [inf_comm, Nat.card_zpowers φ, ← hmul, mul_comm] at hidx
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hidx.symm

/-- **The residue degree is the least exponent landing in `H`.**  For `φ` a Frobenius at an
unramified `Q`, the residue degree below `L ^ H` is the smallest `n ≥ 1` with `φ ^ n ∈ H`.

This is the characterization the fixed-field fibre count uses: it turns the residue degree into a
condition on powers of the Frobenius, with no index or relative index left to unfold. -/
theorem isLeast_pow_mem_inertiaDeg_under_fixedField (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (H : Subgroup (L ≃ₐ[K] L)) {φ : L ≃ₐ[K] L}
    (hφ : IsArithFrobAt (𝓞 K) φ Q) :
    IsLeast {n : ℕ | 0 < n ∧ φ ^ n ∈ H}
      ((Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K)) := by
  have : H.IsFiniteRelIndex (Subgroup.zpowers φ) := ⟨Subgroup.index_ne_zero_of_finite⟩
  rw [inertiaDeg_under_fixedField_eq_relIndex Q hQ H hφ]
  exact Subgroup.isLeast_pow_mem_relIndex_zpowers φ H

/-- **Residue degree one is membership.**  The prime below `Q` in `L ^ H` has residue degree one
over `𝓞 K` exactly when a Frobenius at `Q` lies in `H`. -/
-- Deliberately not `@[simp]`: `φ` occurs only in the hypothesis `hφ`, never in the left-hand
-- side, so `simp` cannot infer it and the rule would never fire. The simp-NF linter rejects
-- the attribute.
theorem inertiaDeg_under_fixedField_eq_one_iff (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (H : Subgroup (L ≃ₐ[K] L)) {φ : L ≃ₐ[K] L}
    (hφ : IsArithFrobAt (𝓞 K) φ Q) :
    (Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) = 1 ↔ φ ∈ H := by
  rw [inertiaDeg_under_fixedField_eq_relIndex Q hQ H hφ, Subgroup.relIndex_eq_one,
    Subgroup.zpowers_le]

/-- **The prime below `Q` in the fixed field of a Frobenius at `Q` has degree one.**  The case
`H = ⟨σ⟩` with `σ` itself the Frobenius, where membership is automatic. -/
theorem inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1 :=
  (inertiaDeg_under_fixedField_eq_one_iff Q hQ (Subgroup.zpowers σ) hσ).2 (Subgroup.mem_zpowers σ)

end Ideal
