/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.External
public import TauCeti.RepresentationTheory.Induction.ClassFunction
public import TauCeti.RepresentationTheory.Symmetric.FrobeniusCharacteristic
import TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity

/-!
# The induction product of class functions of symmetric groups

The block embedding `Equiv.Perm.finSumPermHom m n : Sₘ × Sₙ →* S_(m+n)` lets `Sₘ` permute the first
`m` points of `Fin (m + n)` and `Sₙ` the last `n`. For class functions `f` of `Sₘ` and `g` of `Sₙ`,
the **induction product** `f ∘ g` is the class function of `S_(m+n)` induced from the block
subgroup by the external product `(σ, τ) ↦ f(σ) g(τ)`. On characters it is the character of the
representation induced from the external tensor product.

The main theorem says that the Frobenius characteristic turns the induction product into the
product of symmetric polynomials:

`ch(f ∘ g) = ch(f) · ch(g)`,

in every alphabet of at least `m + n` letters. The proof goes through the cycle-type formula
`ch(f) = (1 / n!) ∑_π f(π) p_{ρ(π)}`. Frobenius reciprocity, applied coefficientwise to the
power-sum products, replaces the average of the induced class function over `S_(m+n)` by the
average of the inducing class function over the block subgroup. On that subgroup the power-sum
product of `σ ⊕ τ` is `p_{ρ(σ)} p_{ρ(τ)}`, because the cycle type of a block permutation is the
union of the cycle types of its blocks, and the average splits as a product.

## Main definitions

* `Equiv.Perm.finSumPermEquivRange m n`: `Sₘ × Sₙ` is isomorphic to the block subgroup, the range of
  `Equiv.Perm.finSumPermHom m n`.
* `TauCeti.ClassFunction.inductionProduct f g`: the induction product of class functions of `Sₘ`
  and `Sₙ`, a class function of `S_(m+n)`.

## Main results

* `TauCeti.frobeniusCharacteristic_indClassFunction`: for a subgroup `S` of `Sₙ`, the Frobenius
  characteristic of a class function induced from `S` is the average over `S` of the power-sum
  products, `ch(Ind_S^(Sₙ) F) = (1 / |S|) ∑_(s ∈ S) F(s) p_(ρ(s))`.
* `TauCeti.psumPart_partition_finSumPerm`: the power-sum product of a block permutation is the
  product of the power-sum products of its blocks.
* `TauCeti.frobeniusCharacteristic_inductionProduct`: **the Frobenius characteristic is
  multiplicative**, `ch(f ∘ g) = ch(f) · ch(g)`.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Chapter I, Section 7,
  formula (7.3) and the proof of (7.4), where the characteristic map is shown to be a ring
  homomorphism for the induction product.
-/

public section

open Equiv MvPolynomial

namespace Equiv.Perm

variable (m n : ℕ)

/-- `Sₘ × Sₙ` is isomorphic to the block subgroup, the range of the block embedding
`Equiv.Perm.finSumPermHom m n`: the subgroup of permutations of `Fin (m + n)` preserving the first
`m` points. -/
noncomputable def finSumPermEquivRange :
    Perm (Fin m) × Perm (Fin n) ≃* (finSumPermHom m n).range :=
  MonoidHom.ofInjective (finSumPermHom_injective m n)

variable {m n}

/-- The image of a pair of permutations in the block subgroup is their block sum. -/
@[simp]
theorem coe_finSumPermEquivRange (p : Perm (Fin m) × Perm (Fin n)) :
    (finSumPermEquivRange m n p : Perm (Fin (m + n))) = finSumPerm p.1 p.2 :=
  (MonoidHom.ofInjective_apply _).trans (finSumPermHom_apply p)

/-- An element of the block subgroup is the block sum of its two blocks. -/
@[simp]
theorem finSumPerm_finSumPermEquivRange_symm (s : (finSumPermHom m n).range) :
    finSumPerm ((finSumPermEquivRange m n).symm s).1 ((finSumPermEquivRange m n).symm s).2 = s := by
  rw [← coe_finSumPermEquivRange, MulEquiv.apply_symm_apply]

end Equiv.Perm

namespace TauCeti

namespace ClassFunction

variable {k : Type*} [Semiring k] {m n : ℕ}

/-- The **induction product** of a class function `f` of `Sₘ` and a class function `g` of `Sₙ`: the
class function of `S_(m+n)` induced from the block subgroup `Sₘ × Sₙ` by the external product
`(σ, τ) ↦ f(σ) g(τ)`. -/
noncomputable def inductionProduct (f : ClassFunction k (Perm (Fin m)))
    (g : ClassFunction k (Perm (Fin n))) : ClassFunction k (Perm (Fin (m + n))) :=
  Subgroup.indClassFunction (Perm.finSumPermHom m n).range
    (comap (Perm.finSumPermEquivRange m n).symm.toMonoidHom (externalProduct f g))

/-- The induction product is induced from the external product, transported to the block
subgroup along `Equiv.Perm.finSumPermEquivRange`. -/
theorem inductionProduct_eq (f : ClassFunction k (Perm (Fin m)))
    (g : ClassFunction k (Perm (Fin n))) :
    inductionProduct f g =
      Subgroup.indClassFunction (Perm.finSumPermHom m n).range
        (comap (Perm.finSumPermEquivRange m n).symm.toMonoidHom (externalProduct f g)) :=
  (rfl)

end ClassFunction

/-! ### The Frobenius characteristic of an induced class function -/

variable {σ : Type*} [Fintype σ]

/-- The coefficient of a monomial in the power-sum product of the cycle type, as a class function
of `Sₙ`. -/
private noncomputable def coeffPsumPartClassFunction (n : ℕ) (d : σ →₀ ℕ) :
    ClassFunction ℂ (Perm (Fin n)) :=
  ⟨fun π => (psumPart σ ℂ π.partition).coeff d, ClassFunction.mem_iff.2 fun π c => by
    simp only [psumPart, Perm.parts_partition_conj]⟩

open scoped Classical in
/-- **The Frobenius characteristic of an induced class function** is the average over the
subgroup of the inducing class function weighted by the power-sum products of the cycle types:
for a subgroup `S` of `Sₙ` and a class function `F` of `S`,
`ch(Ind_S^(Sₙ) F) = (1 / |S|) ∑_(s ∈ S) F(s) p_(ρ(s))`. -/
theorem frobeniusCharacteristic_indClassFunction {n : ℕ} (h : n ≤ Fintype.card σ)
    (S : Subgroup (Perm (Fin n))) (F : ClassFunction ℂ S) :
    (frobeniusCharacteristic σ n h (Subgroup.indClassFunction S F) : MvPolynomial σ ℂ) =
      (Nat.card S : ℂ)⁻¹ • ∑ s : S, F.1 s • psumPart σ ℂ (s : Perm (Fin n)).partition := by
  have hcard : (Nat.card (Perm (Fin n)) : ℂ) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hG : IsUnit (Nat.card (Perm (Fin n)) : ℂ) :=
    hcard ▸ (Nat.cast_ne_zero.mpr n.factorial_ne_zero).isUnit
  rw [frobeniusCharacteristic_eq_sum_psumPart]
  ext d
  -- Frobenius reciprocity against the class function `π ↦ [x^d] p_(ρ(π))`
  have hd := frobenius_reciprocity_classFunction hG F (coeffPsumPartClassFunction n d)
  simp only [coeffPsumPartClassFunction, psumPart, Perm.parts_partition_inv, hcard] at hd
  simpa only [psumPart, coeff_smul, coeff_sum, smul_eq_mul, Finset.mul_sum,
    Subgroup.indClassFunction_apply] using hd

/-! ### Multiplicativity of the Frobenius characteristic -/

variable {m n : ℕ}

/-- The power-sum product of the cycle type of a block permutation is the product of the
power-sum products of the cycle types of its two blocks. -/
theorem psumPart_partition_finSumPerm (R : Type*) [CommSemiring R] (a : Perm (Fin m))
    (b : Perm (Fin n)) :
    psumPart σ R (Perm.finSumPerm a b).partition =
      psumPart σ R a.partition * psumPart σ R b.partition := by
  simp only [psumPart, Perm.parts_partition_finSumPerm, Multiset.map_add, Multiset.prod_add]

/-- **The Frobenius characteristic is multiplicative**: in an alphabet of at least `m + n` letters,
the Frobenius characteristic of the induction product of class functions `f` of `Sₘ` and `g` of
`Sₙ` is the product of their Frobenius characteristics, `ch(f ∘ g) = ch(f) · ch(g)`. -/
theorem frobeniusCharacteristic_inductionProduct (h : m + n ≤ Fintype.card σ)
    (f : ClassFunction ℂ (Perm (Fin m))) (g : ClassFunction ℂ (Perm (Fin n))) :
    (frobeniusCharacteristic σ (m + n) h (ClassFunction.inductionProduct f g) :
        MvPolynomial σ ℂ) =
      (frobeniusCharacteristic σ m ((Nat.le_add_right m n).trans h) f : MvPolynomial σ ℂ) *
        frobeniusCharacteristic σ n ((Nat.le_add_left n m).trans h) g := by
  classical
  let e := Perm.finSumPermEquivRange m n
  have hS : Nat.card (Perm.finSumPermHom m n).range = m.factorial * n.factorial := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [ClassFunction.inductionProduct_eq, frobeniusCharacteristic_indClassFunction, hS,
    frobeniusCharacteristic_eq_sum_psumPart, frobeniusCharacteristic_eq_sum_psumPart]
  -- transport the average over the block subgroup to `Sₘ × Sₙ`, where it splits as a product
  rw [Finset.sum_equiv e.toEquiv.symm (t := Finset.univ)
    (g := fun q : Perm (Fin m) × Perm (Fin n) =>
      (f.1 q.1 * g.1 q.2) • psumPart σ ℂ (Perm.finSumPerm q.1 q.2).partition)
    (fun _ => by simp) fun s _ => ?_]
  · simp only [Fintype.sum_prod_type, psumPart_partition_finSumPerm, smul_mul_smul_comm,
      Finset.sum_mul_sum, Nat.cast_mul, mul_inv]
  · obtain ⟨q, rfl⟩ := e.surjective s
    simp [e]

end TauCeti
