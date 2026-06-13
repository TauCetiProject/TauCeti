/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Galois.Basic
import TauCeti.NumberTheory.Multiquadratic.Degree
import TauCeti.NumberTheory.Multiquadratic.Galois

/-!
# The Galois group of a multiquadratic field is `(ℤ/2)ⁿ`

Over a field `K` in which `2 ≠ 0`, a multiquadratic field `M = K(rootᵢ : i)` (with
`rootᵢ ^ 2 = dᵢ ∈ K`) is Galois (`TauCeti.NumberTheory.Multiquadratic.Galois`). Each automorphism
sends every generator to `± rootᵢ`, so it is determined by a *sign pattern* `ι → ℤ/2`; this
assignment is an injective group homomorphism. When the radicands are square-class independent the
degree is `2ⁿ` (`TauCeti.NumberTheory.Multiquadratic.Degree`), so counting forces the homomorphism
to be an isomorphism: `Gal(M/K) ≃ (ℤ/2)ⁿ`.

## Main results

* `TauCeti.Multiquadratic.signHom`: the injective sign-pattern homomorphism `Gal(M/K) →* (ℤ/2)ⁿ`.
* `TauCeti.Multiquadratic.galoisGroupEquiv`: for square-class independent radicands, the explicit
  isomorphism `Gal(M/K) ≃* Multiplicative (ι → ℤ/2)`.

## Provenance

Generalised from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization
of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, where the
sign-change automorphisms of one concrete multiquadratic field were analysed; here the
construction is carried out for an arbitrary such tower.
-/

open Polynomial IntermediateField

attribute [local instance] Classical.propDecidable

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*} [Finite ι]
  {d : ι → K} {root : ι → L}

omit [Finite ι] in
/-- Every automorphism sends a generator to itself or to its negation. -/
theorem aut_gen_eq_self_or_eq_neg (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) :
    σ (gen root i) = gen root i ∨ σ (gen root i) = -gen root i := by
  have h1 : (σ (gen root i)) ^ 2 = (gen root i) ^ 2 := by
    rw [← map_pow, gen_sq hroot, AlgEquiv.commutes, ← gen_sq hroot]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h1

variable (root) in
/-- The sign pattern of an automorphism: `0` where it fixes a generator, `1` where it negates. -/
noncomputable def signPattern
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) : ZMod 2 :=
  if σ (gen root i) = gen root i then 0 else 1

omit [Finite ι] in
/-- An automorphism acts on each generator by the corresponding sign. -/
theorem aut_gen_eq_signPattern (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) :
    σ (gen root i) = (-1) ^ (signPattern root σ i).val * gen root i := by
  rw [signPattern]
  split_ifs with h
  · simp [h]
  · rcases aut_gen_eq_self_or_eq_neg hroot σ i with h' | h'
    · exact absurd h' h
    · -- here the sign is `1`; `(1 : ZMod 2).val = 1`, so `(-1) ^ 1 = -1` negates the generator.
      have hval : (1 : ZMod 2).val = 1 := rfl
      simp [h', hval]

omit [Finite ι] in
/-- Two automorphisms with the same sign pattern are equal. -/
theorem signPattern_injective (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    Function.Injective (signPattern (K := K) root) := by
  intro σ τ h
  refine AlgEquiv.coe_algHom_injective
    (IntermediateField.algHom_ext_of_eq_adjoin (F := K)
      (S := adjoin K (Set.range root)) (s := Set.range root) rfl ?_)
  rintro x ⟨i, rfl⟩
  have hgen : σ (gen root i) = τ (gen root i) := by
    rw [aut_gen_eq_signPattern hroot, aut_gen_eq_signPattern hroot, h]
  exact hgen

omit [Finite ι] in
/-- A generator is not equal to its own negation (the radicand is nonzero). -/
theorem gen_ne_neg [NeZero (2 : K)] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (i : ι) (hd : d i ≠ 0) :
    gen (K := K) root i ≠ -gen root i := by
  intro h
  have hcoe : root i = -root i := by simpa using congrArg Subtype.val h
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr two_ne_zero
  have hr0 : root i = 0 := by
    have h2 : (2 : L) * root i = 0 := by rw [two_mul]; nth_rewrite 1 [hcoe]; rw [neg_add_cancel]
    exact (mul_eq_zero.mp h2).resolve_left h2L
  have hd0 : d i = 0 := by
    have hh : algebraMap K L (d i) = 0 := by rw [← hroot i, hr0]; ring
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mp hh
  exact hd hd0

omit [Finite ι] in
/-- The sign is `0` exactly where the automorphism fixes the generator. -/
theorem signPattern_eq_zero
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι)
    (h : σ (gen root i) = gen root i) : signPattern root σ i = 0 := by
  simp [signPattern, h]

omit [Finite ι] in
/-- The sign is `1` where the automorphism negates a generator that differs from its negation. -/
theorem signPattern_eq_one
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι)
    (hne : gen (K := K) root i ≠ -gen root i)
    (h : σ (gen root i) = -gen root i) : signPattern root σ i = 1 := by
  have hni : σ (gen root i) ≠ gen root i := fun hh => hne (h ▸ hh.symm)
  simp [signPattern, hni]

omit [Finite ι] in
@[simp] theorem signPattern_one : signPattern (K := K) root (1 : adjoin K (Set.range root) ≃ₐ[K]
    adjoin K (Set.range root)) = 0 := by
  funext i; exact signPattern_eq_zero _ _ rfl

omit [Finite ι] in
/-- The sign pattern is additive: it is a group homomorphism to `ι → ℤ/2`. -/
theorem signPattern_mul (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hne : ∀ i, gen (K := K) root i ≠ -gen root i)
    (σ τ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) :
    signPattern root (σ * τ) = signPattern root σ + signPattern root τ := by
  funext i
  rw [Pi.add_apply]
  rcases aut_gen_eq_self_or_eq_neg hroot τ i with hτ | hτ <;>
    rcases aut_gen_eq_self_or_eq_neg hroot σ i with hσ | hσ
  · rw [signPattern_eq_zero _ _ (by rw [AlgEquiv.mul_apply, hτ, hσ]),
      signPattern_eq_zero _ _ hσ, signPattern_eq_zero _ _ hτ]; decide
  · rw [signPattern_eq_one _ _ (hne i) (by rw [AlgEquiv.mul_apply, hτ, hσ]),
      signPattern_eq_one _ _ (hne i) hσ, signPattern_eq_zero _ _ hτ]; decide
  · rw [signPattern_eq_one _ _ (hne i) (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ]),
      signPattern_eq_zero _ _ hσ, signPattern_eq_one _ _ (hne i) hτ]; decide
  · rw [signPattern_eq_zero _ _ (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ, neg_neg]),
      signPattern_eq_one _ _ (hne i) hσ, signPattern_eq_one _ _ (hne i) hτ]; decide

variable (root) in
/-- The Galois group of `M / K` maps to the sign patterns `(ℤ/2)ⁱ`. -/
noncomputable def signHom (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hne : ∀ i, gen (K := K) root i ≠ -gen root i) :
    (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) →* Multiplicative (ι → ZMod 2) where
  toFun σ := Multiplicative.ofAdd (signPattern root σ)
  map_one' := by simp
  map_mul' σ τ := by simp [signPattern_mul hroot hne, ofAdd_add]

omit [Finite ι] in
@[simp] theorem signHom_apply (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hne : ∀ i, gen (K := K) root i ≠ -gen root i)
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) :
    signHom root hroot hne σ = Multiplicative.ofAdd (signPattern root σ) := rfl

/-- **For square-class independent radicands, the Galois group of a multiquadratic field is
`(ℤ/2)ⁿ`.** -/
noncomputable def galoisGroupEquiv [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) ≃*
      Multiplicative (ι → ZMod 2) := by
  haveI := isSplittingField hroot
  haveI : FiniteDimensional K (adjoin K (Set.range root)) :=
    IsSplittingField.finiteDimensional _ (definingPolynomial d)
  haveI := isGalois hroot
  letI := Fintype.ofFinite ι
  have hd : ∀ i, d i ≠ 0 := fun i hd0 =>
    hindep {i} ⟨i, Finset.mem_singleton_self i⟩
      (by rw [Finset.prod_singleton, hd0]; exact ⟨0, by ring⟩)
  refine MulEquiv.ofBijective (signHom root hroot (fun i => gen_ne_neg hroot i (hd i))) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨signPattern_injective hroot, ?_⟩
  rw [← Nat.card_eq_fintype_card (α := adjoin K (Set.range root) ≃ₐ[K] _),
    IsGalois.card_aut_eq_finrank K (adjoin K (Set.range root)),
    finrank_adjoin_range hroot hindep]
  simp [ZMod.card]

@[simp] theorem galoisGroupEquiv_apply [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) :
    galoisGroupEquiv hroot hindep σ = Multiplicative.ofAdd (signPattern root σ) := rfl

/-- The inverse of `galoisGroupEquiv` realizes a sign pattern `ε` as the automorphism sending each
generator `rootᵢ` to `(-1)^(εᵢ) · rootᵢ`. -/
theorem galoisGroupEquiv_symm_apply_gen [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (ε : ι → ZMod 2) (i : ι) :
    ((galoisGroupEquiv hroot hindep).symm (Multiplicative.ofAdd ε)) (gen root i)
      = (-1) ^ (ε i).val * gen root i := by
  have hσ : signPattern root
      ((galoisGroupEquiv hroot hindep).symm (Multiplicative.ofAdd ε)) = ε := by
    have happ := (galoisGroupEquiv hroot hindep).apply_symm_apply (Multiplicative.ofAdd ε)
    rw [galoisGroupEquiv_apply] at happ
    exact Multiplicative.ofAdd.injective happ
  rw [aut_gen_eq_signPattern hroot, hσ]

end TauCeti.Multiquadratic
