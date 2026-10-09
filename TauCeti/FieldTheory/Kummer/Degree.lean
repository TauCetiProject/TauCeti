/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

import Mathlib.FieldTheory.KummerExtension
import TauCeti.FieldTheory.Kummer.Extension
import TauCeti.LinearAlgebra.LinearIndependent.MonoidHom

/-!
# The degree of a Kummer extension

Let `K` be a field containing the `n`-th roots of unity, that is, with `n` distinct `n`-th roots of
unity (`HasEnoughRootsOfUnity K n`), and let `Δ` be a subgroup of `Kˣ`. Inside an extension `E` of
`K`, the **Kummer field** `K(Δ^{1/n})` is the subfield generated over `K` by every `n`-th root of
every element of `Δ` (`TauCeti.kummerField`). This file proves the main theorem of Kummer theory
for it:

* `K(Δ^{1/n})/K` is an abelian Galois extension (`TauCeti.isAbelianGalois_kummerField`), and it
  is finite when `Δ` has finite image in the power classes `Kˣ ⧸ (Kˣ)ⁿ`
  (`TauCeti.finiteDimensional_kummerField`);
* if every element of `Δ` has an `n`-th root in `E`, its degree is the index of `Δ ∩ (Kˣ)ⁿ` in
  `Δ`, that is, the order of the image of `Δ` in `Kˣ ⧸ (Kˣ)ⁿ` (`TauCeti.finrank_kummerField`).

For instance, over a number field containing the `n`-th roots of unity, the `n`-th roots of the
`S`-units, for a finite set `S` of places, generate such an extension; extensions of this kind are
used in the proof of the second inequality of global class field theory.

The degree is computed with the Kummer pairing `⟨σ, a⟩ = σ α / α`, for `σ` an automorphism of
`K(Δ^{1/n})` and `α` an `n`-th root of `a ∈ Δ`. Two roots of `a` differ by an `n`-th root of unity,
which lies in `K` (`TauCeti.exists_eq_algebraMap_mul_of_pow_eq`), so the pairing does not depend on
the choice of `α`, and it is bimultiplicative. It embeds the Galois group in the characters of
`Δ` modulo `n`-th powers, and `Δ` modulo `n`-th powers in the characters of the Galois group.
Dedekind's bound on the number of characters of a finite group (`TauCeti.natCard_monoidHom_le`)
turns these two embeddings into the equality of orders.

The Kummer character `MonoidHom.kummerCharacter` of `TauCeti.FieldTheory.Kummer.Character` takes
its values in the roots of unity of a base field that is algebraically closed in the extension; the
base field here is not, so the pairing below takes its values in the top field.

## Main definitions

* `TauCeti.kummerField`: the subfield `K(Δ^{1/n})` of `E`.

## Main results

* `TauCeti.isAbelianGalois_kummerField`: `K(Δ^{1/n})/K` is abelian Galois.
* `TauCeti.finiteDimensional_kummerField`: it is finite when `Δ ∩ (Kˣ)ⁿ` has finite index in `Δ`.
* `TauCeti.finrank_kummerField`: `[K(Δ^{1/n}) : K] = [Δ : Δ ∩ (Kˣ)ⁿ]`, when every element of `Δ`
  has an `n`-th root in `E`.
* `TauCeti.exists_eq_algebraMap_mul_of_pow_eq`: over a field containing the `n`-th roots of unity,
  two elements of an extension with the same `n`-th power differ by a factor from the base field.

## References

* S. Lang, *Algebra*, Graduate Texts in Mathematics 211, Springer (2002), Chapter VI, §8,
  Theorem 8.1.
* J. S. Milne, *Class Field Theory*, Chapter VII, §5, where these extensions are used.
-/

public section

open Polynomial IntermediateField Module

namespace TauCeti

section RootsOfUnity

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

/-- If `K` contains the `n`-th roots of unity, then every `n`-th root of unity of a domain
containing `K` lies in `K`. -/
theorem exists_algebraMap_eq_of_pow_eq_one {A : Type*} [CommRing A] [IsDomain A] [Algebra K A]
    {ξ : A} (h : ξ ^ n = 1) : ∃ z : K, algebraMap K A z = ξ := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  obtain ⟨i, -, hi⟩ := (hζ.map_of_injective (algebraMap K A).injective).eq_pow_of_pow_eq_one h
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

variable {F : Type*} [Field F] [Algebra K F]

/-- If `K` contains the `n`-th roots of unity, then two elements of an extension field of `K`
with the same `n`-th power differ by a factor from `K`. -/
theorem exists_eq_algebraMap_mul_of_pow_eq {x y : F} (hy : y ≠ 0) (h : x ^ n = y ^ n) :
    ∃ z : K, x = algebraMap K F z * y := by
  obtain ⟨z, hz⟩ := exists_algebraMap_eq_of_pow_eq_one (K := K) (n := n) (ξ := x / y)
    (by rw [div_pow, h, div_self (pow_ne_zero _ hy)])
  exact ⟨z, by rw [hz, div_mul_cancel₀ _ hy]⟩

end RootsOfUnity

variable {K : Type*} [Field K] (E : Type*) [Field E] [Algebra K E] (n : ℕ)

/-- The **Kummer field** `K(Δ^{1/n})`: the subfield of `E` generated over `K` by the `n`-th roots
in `E` of the elements of the subgroup `Δ` of `Kˣ`. -/
def kummerField (Δ : Subgroup Kˣ) : IntermediateField K E :=
  adjoin K {x : E | ∃ a ∈ Δ, x ^ n = algebraMap K E a}

variable {E n} {Δ : Subgroup Kˣ}

theorem kummerField_def :
    kummerField E n Δ = adjoin K {x : E | ∃ a ∈ Δ, x ^ n = algebraMap K E a} :=
  (rfl)

/-- An `n`-th root of an element of `Δ` lies in `K(Δ^{1/n})`. -/
theorem mem_kummerField_of_pow_eq {x : E} {a : Kˣ} (ha : a ∈ Δ)
    (hx : x ^ n = algebraMap K E a) : x ∈ kummerField E n Δ :=
  subset_adjoin _ _ ⟨a, ha, hx⟩

/-- `K(Δ^{1/n})` is the smallest subfield containing the `n`-th roots of the elements of `Δ`. -/
theorem kummerField_le_iff {F : IntermediateField K E} :
    kummerField E n Δ ≤ F ↔ ∀ a ∈ Δ, ∀ x : E, x ^ n = algebraMap K E a → x ∈ F := by
  rw [kummerField_def, adjoin_le_iff]
  exact ⟨fun h a ha x hx ↦ h ⟨a, ha, hx⟩, fun h _ ⟨a, ha, hx⟩ ↦ h a ha _ hx⟩

/-- `K(Δ^{1/n})` is monotone in `Δ`. -/
theorem kummerField_mono {Δ' : Subgroup Kˣ} (h : Δ ≤ Δ') :
    kummerField E n Δ ≤ kummerField E n Δ' :=
  kummerField_le_iff.2 fun _ ha _ hx ↦ mem_kummerField_of_pow_eq (h ha) hx

section Finite

variable [NeZero n]

private theorem ne_zero_of_pow_eq {F : Type*} [Field F] [Algebra K F] {x : F} {a : Kˣ}
    (hx : x ^ n = algebraMap K F a) : x ≠ 0 := by
  rintro rfl
  rw [zero_pow (NeZero.ne n), eq_comm, map_eq_zero] at hx
  exact a.ne_zero hx

/-- `K(Δ^{1/n})/K` is finite when `Δ ∩ (Kˣ)ⁿ` has finite index in `Δ`: it is generated by the
`n`-th roots of finitely many representatives of `Δ` modulo `n`-th powers. -/
instance finiteDimensional_kummerField
    [(powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ] :
    FiniteDimensional K (kummerField E n Δ) := by
  classical
  set P := (powMonoidHom n : Kˣ →* Kˣ).range
  have : (P.subgroupOf Δ).FiniteIndex := ⟨Subgroup.relIndex_ne_zero⟩
  -- The roots of `Xⁿ - b`, for `b` running over representatives of `Δ` modulo `n`-th powers.
  let S : Set E := ⋃ d : Δ ⧸ P.subgroupOf Δ, ((X : K[X]) ^ n - C ((d.out : Kˣ) : K)).rootSet E
  have : Finite S := (Set.finite_iUnion fun _ ↦ rootSet_finite _ _).to_subtype
  have : FiniteDimensional K (adjoin K S) := finiteDimensional_adjoin fun x hx ↦ by
    obtain ⟨d, hd⟩ := Set.mem_iUnion.1 hx
    exact (isAlgebraic_of_mem_rootSet hd).isIntegral
  have hle : kummerField E n Δ ≤ adjoin K S := by
    refine kummerField_le_iff.2 fun a ha x hx ↦ ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (P.subgroupOf Δ) ⟨a, ha⟩
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h.2
    -- `x * c` is a root of `Xⁿ - b` for the representative `b = a * cⁿ` of the class of `a`.
    have hxc : x * algebraMap K E c ∈ S := Set.mem_iUnion.2 ⟨_, by
      rw [mem_rootSet_X_pow_sub_C (NeZero.ne n), hh, mul_pow, hx]
      simp [← hc]⟩
    rw [← mul_div_cancel_right₀ x (by simp : algebraMap K E c ≠ 0)]
    exact div_mem (subset_adjoin _ _ hxc) (IntermediateField.algebraMap_mem _ _)
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

end Finite

section Galois

variable [NeZero n] [HasEnoughRootsOfUnity K n] {L : Type*} [Field L] [Algebra K L]

/-- A `K`-automorphism moves an `n`-th root of an element of `K` by a factor from `K`. -/
private theorem exists_apply_eq_algebraMap_mul (σ : L ≃ₐ[K] L) {y : L} {a : Kˣ}
    (hy : y ^ n = algebraMap K L a) : ∃ z : K, σ y = algebraMap K L z * y :=
  exists_eq_algebraMap_mul_of_pow_eq (ne_zero_of_pow_eq hy) (by rw [← map_pow, hy, σ.commutes])

/-- The Kummer pairing `σ y / y` only depends on `y ^ n`. -/
private theorem apply_div_self_eq_of_pow_eq (σ : L ≃ₐ[K] L) {y y' : L} {a : Kˣ}
    (hy : y ^ n = algebraMap K L a) (h : y' ^ n = y ^ n) : σ y' / y' = σ y / y := by
  obtain ⟨z, rfl⟩ := exists_eq_algebraMap_mul_of_pow_eq (K := K) (ne_zero_of_pow_eq hy) h
  have hz : algebraMap K L z ≠ 0 := left_ne_zero_of_mul (ne_zero_of_pow_eq (h.trans hy))
  rw [map_mul, AlgEquiv.commutes, mul_div_mul_left _ _ hz]

/-- The Kummer pairing `σ y / y` is trivial when `y ^ n` is an `n`-th power in `K`. -/
private theorem apply_div_self_eq_one_of_pow_eq (σ : L ≃ₐ[K] L) {y : L} {c : Kˣ}
    (hy : y ^ n = algebraMap K L ((c : K) ^ n)) : σ y / y = 1 := by
  rw [apply_div_self_eq_of_pow_eq (n := n) σ (y := algebraMap K L c) (a := c ^ n) (by simp)
    (by rw [hy, map_pow]), AlgEquiv.commutes, div_self (by simp)]

/-- The Kummer pairing `σ y / y` is multiplicative in `y ^ n`. -/
private theorem apply_div_self_eq_mul_of_pow_eq (σ : L ≃ₐ[K] L) {y y' w : L} {a b : Kˣ}
    (hy : y ^ n = algebraMap K L a) (hy' : y' ^ n = algebraMap K L b)
    (hw : w ^ n = algebraMap K L (a * b : Kˣ)) : σ w / w = σ y / y * (σ y' / y') := by
  rw [apply_div_self_eq_of_pow_eq (n := n) σ (y := y * y') (a := a * b)
    (by simp [mul_pow, hy, hy']) (by simp [mul_pow, hy, hy', hw]), map_mul, mul_div_mul_comm]

/-- The Kummer pairing `σ y / y` is multiplicative in `σ`. -/
private theorem mul_apply_div_self (σ τ : L ≃ₐ[K] L) {y : L} {a : Kˣ}
    (hy : y ^ n = algebraMap K L a) : (σ * τ) y / y = σ y / y * (τ y / y) := by
  obtain ⟨z, hz⟩ := exists_apply_eq_algebraMap_mul τ hy
  rw [AlgEquiv.mul_apply, hz, map_mul, AlgEquiv.commutes,
    mul_div_cancel_right₀ _ (ne_zero_of_pow_eq hy), mul_div_assoc, mul_comm]

/-- **`K(Δ^{1/n})/K` is an abelian Galois extension** when `K` contains the `n`-th roots of unity.
Each generator is a root of a separable binomial `Xⁿ - a` that splits in `K(Δ^{1/n})`, and each
automorphism multiplies each generator by a constant, so any two automorphisms commute. -/
instance isAbelianGalois_kummerField : IsAbelianGalois K (kummerField E n Δ) := by
  set M := kummerField E n Δ
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have : NeZero (n : K) := hζ.neZero'
  have hdvd {x : E} {a : Kˣ} (hx : x ^ n = algebraMap K E a) :
      minpoly K x ∣ (X : K[X]) ^ n - C (a : K) :=
    minpoly.dvd K x (by rw [map_sub, map_pow, aeval_X, aeval_C, hx, sub_self])
  have hgen {x : E} {a : Kˣ} (ha : a ∈ Δ) (hx : x ^ n = algebraMap K E a) :
      (⟨x, mem_kummerField_of_pow_eq ha hx⟩ : M) ^ n = algebraMap K M a :=
    Subtype.ext (by simpa using hx)
  have : Algebra.IsSeparable K M := (isSeparable_adjoin_iff_isSeparable K E).2
    fun x ⟨a, _, hx⟩ ↦ (separable_X_pow_sub_C (a : K) (NeZero.ne _) a.ne_zero).of_dvd (hdvd hx)
  have : Normal K M := by
    refine ⟨fun y ↦ ?_⟩
    rw [IntermediateField.minpoly_eq]
    refine splits_of_mem_adjoin K E (S := {x : E | ∃ a ∈ Δ, x ^ n = algebraMap K E a})
      (fun x ⟨a, ha, hx⟩ ↦ ⟨⟨_, monic_X_pow_sub_C (a : K) (NeZero.ne n), by
        rw [eval₂_sub, eval₂_X_pow, eval₂_C, hx, sub_self]⟩, ?_⟩) y.2
    refine Splits.of_dvd ?_ (Polynomial.map_ne_zero (X_pow_sub_C_ne_zero (NeZero.pos n) _))
      (Polynomial.map_dvd _ (hdvd hx))
    simpa using X_pow_sub_C_splits_of_isPrimitiveRoot
      (hζ.map_of_injective (algebraMap K M).injective) (hgen ha hx)
  -- Two automorphisms commute on each generator, since both move it by a constant factor.
  have hcomm (σ τ : M ≃ₐ[K] M) (y : M) {a : Kˣ} (hy : y ^ n = algebraMap K M a) :
      (σ * τ) y = (τ * σ) y := by
    obtain ⟨z, hz⟩ := exists_apply_eq_algebraMap_mul σ hy
    obtain ⟨w, hw⟩ := exists_apply_eq_algebraMap_mul τ hy
    simp only [AlgEquiv.mul_apply, hz, hw, map_mul, AlgEquiv.commutes]
    ring
  exact { is_comm := ⟨fun σ τ ↦ AlgEquiv.coe_toAlgHom_injective <|
    algHom_ext_of_eq_adjoin K kummerField_def fun x ⟨a, ha, hx⟩ ↦ hcomm σ τ _ (hgen ha hx)⟩ }

/-- In the Galois group of `K(Δ^{1/n})/K`, an automorphism is determined by how it moves one
chosen `n`-th root `r a` of each `a ∈ Δ`. -/
private theorem algEquiv_ext_of_apply_div_self_eq {r : Δ → kummerField E n Δ}
    (hr : ∀ a, r a ^ n = algebraMap K _ ((a : Kˣ) : K)) {σ τ : kummerField E n Δ ≃ₐ[K] _}
    (h : ∀ a, σ (r a) / r a = τ (r a) / r a) : σ = τ := by
  refine AlgEquiv.coe_toAlgHom_injective <|
    algHom_ext_of_eq_adjoin K kummerField_def fun x ⟨a, ha, hx⟩ ↦ ?_
  have hy : (⟨x, mem_kummerField_of_pow_eq ha hx⟩ : kummerField E n Δ) ^ n = algebraMap K _ a :=
    Subtype.ext (by simpa using hx)
  have hpow := hy.trans (hr ⟨a, ha⟩).symm
  have hσ := apply_div_self_eq_of_pow_eq σ (hr ⟨a, ha⟩) hpow
  have hτ := apply_div_self_eq_of_pow_eq τ (hr ⟨a, ha⟩) hpow
  rw [h, ← hτ, div_left_inj' (ne_zero_of_pow_eq hy)] at hσ
  exact hσ

/-- **The Galois group of `K(Δ^{1/n})/K` embeds in the characters of `Δ` modulo `n`-th powers**,
by the Kummer pairing; so its order is at most `[Δ : Δ ∩ (Kˣ)ⁿ]`. -/
private theorem natCard_algEquiv_kummerField_le
    [(powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ] {r : Δ → kummerField E n Δ}
    (hr : ∀ a, r a ^ n = algebraMap K _ ((a : Kˣ) : K)) :
    Nat.card (kummerField E n Δ ≃ₐ[K] kummerField E n Δ) ≤
      (powMonoidHom n : Kˣ →* Kˣ).range.relIndex Δ := by
  set P := (powMonoidHom n : Kˣ →* Kˣ).range
  have : (P.subgroupOf Δ).FiniteIndex := ⟨Subgroup.relIndex_ne_zero⟩
  let χ (σ : kummerField E n Δ ≃ₐ[K] _) : Δ ⧸ P.subgroupOf Δ →* kummerField E n Δ :=
    QuotientGroup.lift _
      { toFun a := σ (r a) / r a
        map_one' := apply_div_self_eq_one_of_pow_eq (n := n) σ (c := 1) (by simp [hr])
        map_mul' a b := apply_div_self_eq_mul_of_pow_eq σ (hr a) (hr b) (hr (a * b)) }
      fun a ha ↦ by
        obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 ha
        exact apply_div_self_eq_one_of_pow_eq (n := n) σ (c := c) (by simp [hr, ← hc])
  have hχ : Function.Injective χ := fun σ τ h ↦ algEquiv_ext_of_apply_div_self_eq hr
    fun a ↦ DFunLike.congr_fun h (QuotientGroup.mk a)
  exact (Nat.card_le_card_of_injective χ hχ).trans (natCard_monoidHom_le _ _)

/-- **`Δ` modulo `n`-th powers embeds in the characters of the Galois group of `K(Δ^{1/n})/K`**,
by the Kummer pairing; so `[Δ : Δ ∩ (Kˣ)ⁿ]` is at most the order of the Galois group. -/
private theorem relIndex_le_natCard_algEquiv_kummerField
    [(powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ] {r : Δ → kummerField E n Δ}
    (hr : ∀ a, r a ^ n = algebraMap K _ ((a : Kˣ) : K)) :
    (powMonoidHom n : Kˣ →* Kˣ).range.relIndex Δ ≤
      Nat.card (kummerField E n Δ ≃ₐ[K] kummerField E n Δ) := by
  set P := (powMonoidHom n : Kˣ →* Kˣ).range
  have hr0 (a : Δ) : r a ≠ 0 := ne_zero_of_pow_eq (hr a)
  have hmul (σ : kummerField E n Δ ≃ₐ[K] _) (a b : Δ) :
      σ (r (a * b)) / r (a * b) = σ (r a) / r a * (σ (r b) / r b) :=
    apply_div_self_eq_mul_of_pow_eq σ (hr a) (hr b) (hr (a * b))
  let ψ : Δ ⧸ P.subgroupOf Δ →* ((kummerField E n Δ ≃ₐ[K] _) →* kummerField E n Δ) :=
    QuotientGroup.lift _
      { toFun a :=
          { toFun σ := σ (r a) / r a
            map_one' := by simp [hr0 a]
            map_mul' σ τ := mul_apply_div_self σ τ (hr a) }
        map_one' := MonoidHom.ext fun σ ↦
          apply_div_self_eq_one_of_pow_eq (n := n) σ (c := 1) (by simp [hr])
        map_mul' a b := MonoidHom.ext fun σ ↦ hmul σ a b }
      fun a ha ↦ MonoidHom.ext fun σ ↦ by
        obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 ha
        exact apply_div_self_eq_one_of_pow_eq (n := n) σ (c := c) (by simp [hr, ← hc])
  -- If `a ∈ Δ` pairs trivially with every automorphism, its root `r a` is fixed by the Galois
  -- group, hence lies in `K`, and `a` is an `n`-th power.
  have hψ : Function.Injective ψ := by
    intro d₁ d₂ h
    induction d₁ using QuotientGroup.induction_on with | H a => ?_
    induction d₂ using QuotientGroup.induction_on with | H b => ?_
    refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
    have hfix (σ : kummerField E n Δ ≃ₐ[K] _) : σ (r (a⁻¹ * b)) = r (a⁻¹ * b) := by
      have h' : σ (r a) / r a = σ (r b) / r b := DFunLike.congr_fun h σ
      rw [← div_eq_one_iff_eq (hr0 _), hmul, ← h', ← hmul, inv_mul_cancel,
        apply_div_self_eq_one_of_pow_eq (n := n) σ (c := 1) (by simp [hr])]
    obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
    have hc0 : c ≠ 0 := by rintro rfl; exact hr0 _ (by rw [← hc, map_zero])
    refine ⟨Units.mk0 c hc0, Units.ext ((algebraMap K (kummerField E n Δ)).injective ?_)⟩
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hc, hr]
  exact (Nat.card_le_card_of_injective ψ hψ).trans (natCard_monoidHom_le _ _)

/-- **The degree of a Kummer extension.** If `K` contains the `n`-th roots of unity and every
element of `Δ` has an `n`-th root in `E`, then `[K(Δ^{1/n}) : K] = [Δ : Δ ∩ (Kˣ)ⁿ]`, the order of
the image of `Δ` in `Kˣ ⧸ (Kˣ)ⁿ`, as soon as this index is finite. -/
theorem finrank_kummerField [(powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ a ∈ Δ, ∃ x : E, x ^ n = algebraMap K E a) :
    finrank K (kummerField E n Δ) = (powMonoidHom n : Kˣ →* Kˣ).range.relIndex Δ := by
  have hr (a : Δ) : ∃ y : kummerField E n Δ, y ^ n = algebraMap K _ ((a : Kˣ) : K) := by
    obtain ⟨x, hx⟩ := hroots a a.2
    exact ⟨⟨x, mem_kummerField_of_pow_eq a.2 hx⟩, Subtype.ext (by simpa using hx)⟩
  choose r hr using hr
  rw [← IsGalois.card_aut_eq_finrank]
  exact le_antisymm (natCard_algEquiv_kummerField_le hr)
    (relIndex_le_natCard_algEquiv_kummerField hr)

end Galois

end TauCeti
