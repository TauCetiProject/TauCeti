/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Hermitian.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.FieldTheory.Finite.PowAddSelf
import TauCeti.FieldTheory.IntermediateField.Adjoin.Transcendental

/-!
# The translations of the Hermitian function field

Let `K` have exponential characteristic `p`, let `q = p ^ n > 1`, and let `x, y` be Hermitian
coordinates on `F / K`: `F = K(x, y)` with `x` transcendental and `y ^ q + y = x ^ (q + 1)`. For
`a, b ∈ K` with

`a ^ (q ^ 2) = a` and `b ^ q + b = a ^ (q + 1)`

there is a unique `K`-automorphism `σ_{a,b}` of `F` with

`σ_{a,b} x = x + a` and `σ_{a,b} y = y + a ^ q x + b`.

Over `K = 𝔽_{q²}`, where `F` is the Hermitian function field (Stichtenoth, Section 6.4), these
automorphisms form a group of order `q³` (`natCard_hermitianTranslations` below). Its order is a
power of `p`. Classically the genus of `F` is `q (q - 1) / 2`, so for large `q` the order `q³`
exceeds `84 (g - 1)`. This is why the Hurwitz bound
`TauCeti.natCard_le_eighty_four_mul_genus_sub_one` needs its tameness hypothesis. The genus and
this comparison are not proved in this file.

The automorphism is built in two steps. On `K(x)`, the substitution `x ↦ x + a` is defined
because `x + a` is again transcendental. It extends to `F = K(x)(y)`, because the minimal
polynomial of `y` over `K(x)` is `T ^ q + T - x ^ (q + 1)`
(`TauCeti.IsHermitianCoordinates.minpoly_adjoin_x`). Its image under the substitution is
`T ^ q + T - (x + a) ^ (q + 1)`, and `y + a ^ q x + b` is a root, since raising to the power `q`
is additive. The two conditions on `(a, b)` are exactly what this needs.

Closure of the set of these automorphisms under composition and inverses is a computation on
the two generators: `σ_{a,b} ∘ σ_{a',b'} = σ_{a + a', b + b' + a a'^q}` and
`σ_{a,b}⁻¹ = σ_{-a, b^q}`. The subgroup `TauCeti.hermitianTranslations` is defined by this
action on `x` and `y`, so it makes sense with no hypothesis on `x` and `y`. Over `K = 𝔽_{q²}`
every `a` satisfies `a ^ (q ^ 2) = a`, and `c = a ^ (q + 1)` satisfies `c ^ q = c`, so
`TauCeti.FiniteField.natCard_pow_add_self_eq` gives exactly `q` choices of `b` for each of the
`q²` choices of `a`.

## Main definitions

* `TauCeti.hermitianTranslations K p n x y`: the subgroup of `K`-automorphisms `σ` of `F` with
  `σ x = x + a` and `σ y = y + a ^ q x + b` for some `a, b ∈ K` with `a ^ (q ^ 2) = a` and
  `b ^ q + b = a ^ (q + 1)`, where `q = p ^ n`.
* `TauCeti.IsHermitianCoordinates.translation`: the automorphism `σ_{a,b}`.

## Main results

* `TauCeti.IsHermitianCoordinates.translation_apply_x` and
  `TauCeti.IsHermitianCoordinates.translation_apply_y`: the values of `σ_{a,b}` on `x` and `y`.
* `TauCeti.mem_hermitianTranslations`: membership in the translation group, unfolded.
* `TauCeti.IsHermitianCoordinates.translation_mem_hermitianTranslations` and
  `TauCeti.IsHermitianCoordinates.exists_translation_eq`: the translation group consists exactly
  of the automorphisms `σ_{a,b}`.
* `TauCeti.IsHermitianCoordinates.translation_inj`: `σ_{a,b}` determines `(a, b)`.
* `TauCeti.IsHermitianCoordinates.natCard_hermitianTranslations`: over a field with `q²`
  elements, the group of translations has order `q³`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section 6.4.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section Subgroup

variable (K) (p n : ℕ) [ExpChar K p] (x y : F)

/-- The **translations of the Hermitian function field**, with `q = p ^ n`: the
`K`-automorphisms `σ` of `F` for which there are `a, b ∈ K` with `a ^ (q ^ 2) = a`,
`b ^ q + b = a ^ (q + 1)`, `σ x = x + a` and `σ y = y + a ^ q x + b`.

When `x` and `y` are Hermitian coordinates, each such pair `(a, b)` is realized
(`TauCeti.IsHermitianCoordinates.translation`) by exactly one automorphism. -/
noncomputable def hermitianTranslations : Subgroup (F ≃ₐ[K] F) where
  carrier := {σ | ∃ a b : K, a ^ (p ^ n) ^ 2 = a ∧ b ^ p ^ n + b = a ^ (p ^ n + 1) ∧
    σ x = x + algebraMap K F a ∧ σ y = y + algebraMap K F (a ^ p ^ n) * x + algebraMap K F b}
  mul_mem' := by
    rintro σ τ ⟨a, b, ha, hb, hσx, hσy⟩ ⟨a', b', ha', hb', hτx, hτy⟩
    have hfrob (u v : K) : (u + v) ^ p ^ n = u ^ p ^ n + v ^ p ^ n := add_pow_expChar_pow u v p n
    have hfrob2 (u v : K) : (u + v) ^ (p ^ n) ^ 2 = u ^ (p ^ n) ^ 2 + v ^ (p ^ n) ^ 2 := by
      rw [← pow_mul]
      exact add_pow_expChar_pow u v p (n * 2)
    refine ⟨a + a', b + b' + a * a' ^ p ^ n, ?_, ?_, ?_, ?_⟩
    · rw [hfrob2, ha, ha']
    · have ha'' : (a' ^ p ^ n) ^ p ^ n = a' := by rw [← pow_mul, ← sq, ha']
      rw [hfrob, hfrob, mul_pow, ha'', pow_succ (a + a'), hfrob]
      linear_combination hb + hb'
    · rw [AlgEquiv.mul_apply, hτx, map_add, hσx, AlgEquiv.commutes, map_add, add_assoc]
    · rw [AlgEquiv.mul_apply, hτy, map_add, map_add, map_mul, AlgEquiv.commutes,
        AlgEquiv.commutes, hσx, hσy, hfrob]
      simp only [map_add, map_mul, map_pow]
      ring
  one_mem' := by
    have hq := expChar_pow_pos K p n
    exact ⟨0, 0, zero_pow (pow_ne_zero _ hq.ne'),
      by rw [zero_pow hq.ne', zero_pow (Nat.succ_ne_zero _), add_zero], by simp,
      by simp [zero_pow hq.ne']⟩
  inv_mem' := by
    rintro σ ⟨a, b, ha, hb, hσx, hσy⟩
    have hq := expChar_pow_pos K p n
    have hfrob (u v : K) : (u + v) ^ p ^ n = u ^ p ^ n + v ^ p ^ n := add_pow_expChar_pow u v p n
    -- In exponential characteristic `p`, raising to the power `q = p ^ n` commutes with negation.
    have hneg (u : K) : (-u) ^ p ^ n = -u ^ p ^ n := by
      have := sub_pow_expChar_pow (p := p) (n := n) (0 : K) u
      rwa [zero_sub, zero_pow hq.ne', zero_sub] at this
    have hqq : a ^ (p ^ n * p ^ n) = a := by rw [← sq]; exact ha
    refine ⟨-a, b ^ p ^ n, ?_, ?_, ?_, ?_⟩
    · rw [sq, pow_mul, hneg, hneg, ← pow_mul, hqq]
    · rw [← hfrob, hb, ← pow_mul, add_mul, one_mul, pow_add, hqq, pow_succ, hneg]
      ring
    · rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, map_add, AlgEquiv.commutes, hσx, map_neg]
      ring
    · have hbF : algebraMap K F (b ^ p ^ n) + algebraMap K F b =
          algebraMap K F (a ^ p ^ n) * algebraMap K F a := by
        rw [← map_add, hb, ← map_mul, pow_succ]
      rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, map_add, map_add, map_mul, AlgEquiv.commutes,
        AlgEquiv.commutes, hσx, hσy, hneg]
      simp only [map_neg]
      linear_combination (-1 : F) * hbF

variable {K p n x y}

/-- Membership in the translation group, unfolded. -/
theorem mem_hermitianTranslations {σ : F ≃ₐ[K] F} :
    σ ∈ hermitianTranslations K p n x y ↔
      ∃ a b : K, a ^ (p ^ n) ^ 2 = a ∧ b ^ p ^ n + b = a ^ (p ^ n + 1) ∧
        σ x = x + algebraMap K F a ∧
        σ y = y + algebraMap K F (a ^ p ^ n) * x + algebraMap K F b :=
  Iff.rfl

end Subgroup

namespace IsHermitianCoordinates

variable {x y : F}

section AdjoinRoot

variable {q : ℕ} (h : IsHermitianCoordinates K q x y) (hq : 1 < q)
include h hq

/-- The identification of `F` with `K(x)[T] / (T ^ q + T - x ^ (q + 1))`. -/
private noncomputable def adjoinRootEquiv : AdjoinRoot (minpoly K⟮x⟯ y) ≃ₐ[K⟮x⟯] F :=
  (IntermediateField.adjoinRootEquivAdjoin K⟮x⟯ (h.isIntegral_adjoin_x hq)).trans
    ((IntermediateField.equivOfEq h.adjoin_adjoin_eq_top).trans IntermediateField.topEquiv)

private theorem adjoinRootEquiv_root : h.adjoinRootEquiv hq (AdjoinRoot.root _) = y := by
  simp [adjoinRootEquiv, IntermediateField.adjoinRootEquivAdjoin_apply_root]

end AdjoinRoot

variable {p n : ℕ} [ExpChar K p] (h : IsHermitianCoordinates K (p ^ n) x y) (hq : 1 < p ^ n)

include h in
/-- `y + a ^ q x + b` is a root of `T ^ q + T - (x + a) ^ (q + 1)`. -/
private theorem pow_add_self_eq {a b : K} (ha : a ^ (p ^ n) ^ 2 = a)
    (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)) :
    (y + algebraMap K F (a ^ p ^ n) * x + algebraMap K F b) ^ p ^ n +
        (y + algebraMap K F (a ^ p ^ n) * x + algebraMap K F b) =
      (x + algebraMap K F a) ^ (p ^ n + 1) := by
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  have hfrob (u v : F) : (u + v) ^ p ^ n = u ^ p ^ n + v ^ p ^ n := add_pow_expChar_pow u v p n
  have ha' : (algebraMap K F a ^ p ^ n) ^ p ^ n = algebraMap K F a := by
    rw [← map_pow, ← map_pow, ← pow_mul, ← sq, ha]
  have hb' : algebraMap K F b ^ p ^ n + algebraMap K F b = algebraMap K F a ^ (p ^ n + 1) := by
    rw [← map_pow, ← map_add, hb, map_pow]
  simp only [map_pow]
  rw [hfrob, hfrob, mul_pow, ha', pow_succ (x + algebraMap K F a), hfrob]
  linear_combination h.equation + hb'

include h hq

/-- `y + a ^ q x + b` is a root of the image of the minimal polynomial of `y` under the
substitution `x ↦ x + a`. -/
private theorem eval₂_minpoly {a b : K} (ha : a ^ (p ^ n) ^ 2 = a)
    (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)) :
    (minpoly K⟮x⟯ y).eval₂ (h.transcendental_x.algHomAdjoin (h.transcendental_x.add_algebraMap a))
      (y + algebraMap K F (a ^ p ^ n) * x + algebraMap K F b) = 0 := by
  rw [h.minpoly_adjoin_x hq, eval₂_sub, eval₂_add, eval₂_X_pow, eval₂_X, eval₂_C, RingHom.coe_coe,
    map_pow (h.transcendental_x.algHomAdjoin (h.transcendental_x.add_algebraMap a)),
    Transcendental.algHomAdjoin_gen, h.pow_add_self_eq ha hb, sub_self]

/-- The `K`-algebra endomorphism `σ_{a,b}` of `F`, before it is shown to be bijective: the
substitution `x ↦ x + a` on `K(x)`, extended to `F = K(x)[T] / (minpoly)` by `T ↦ y + a ^ q x + b`.
-/
private noncomputable def translationAlgHom {a b : K} (ha : a ^ (p ^ n) ^ 2 = a)
    (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)) : F →ₐ[K] F :=
  (AdjoinRoot.liftAlgHom _ _ _ (h.eval₂_minpoly hq ha hb)).comp
    ((h.adjoinRootEquiv hq).symm.restrictScalars K).toAlgHom

private theorem translationAlgHom_algebraMap {a b : K} (ha : a ^ (p ^ n) ^ 2 = a)
    (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)) (z : K⟮x⟯) :
    h.translationAlgHom hq ha hb (algebraMap K⟮x⟯ F z) =
      h.transcendental_x.algHomAdjoin (h.transcendental_x.add_algebraMap a) z := by
  rw [← (h.adjoinRootEquiv hq).commutes z]
  simp [translationAlgHom, AdjoinRoot.algebraMap_eq]

private theorem translationAlgHom_apply_x {a b : K} (ha : a ^ (p ^ n) ^ 2 = a)
    (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)) :
    h.translationAlgHom hq ha hb x = x + algebraMap K F a := by
  have := h.translationAlgHom_algebraMap hq ha hb (IntermediateField.AdjoinSimple.gen K x)
  rwa [IntermediateField.AdjoinSimple.algebraMap_gen, Transcendental.algHomAdjoin_gen] at this

private theorem translationAlgHom_apply_y {a b : K} (ha : a ^ (p ^ n) ^ 2 = a)
    (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)) :
    h.translationAlgHom hq ha hb y = y + algebraMap K F (a ^ p ^ n) * x + algebraMap K F b := by
  have : h.translationAlgHom hq ha hb (h.adjoinRootEquiv hq (AdjoinRoot.root _)) =
      y + algebraMap K F (a ^ p ^ n) * x + algebraMap K F b := by
    simp [translationAlgHom]
  rwa [h.adjoinRootEquiv_root hq] at this

/-- **The translation `σ_{a,b}` of the Hermitian function field**: the `K`-automorphism of `F`
with `x ↦ x + a` and `y ↦ y + a ^ q x + b`, where `q = p ^ n`, for `a ^ (q ^ 2) = a` and
`b ^ q + b = a ^ (q + 1)`. -/
noncomputable def translation {a b : K} (ha : a ^ (p ^ n) ^ 2 = a)
    (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)) : F ≃ₐ[K] F :=
  AlgEquiv.ofBijective (h.translationAlgHom hq ha hb) ⟨(h.translationAlgHom hq ha hb).injective, by
    -- The image is an intermediate field containing `x` and `y`.
    rw [← AlgHom.fieldRange_eq_top, eq_top_iff, ← h.adjoin_eq_top,
      IntermediateField.adjoin_le_iff]
    have hx : x ∈ (h.translationAlgHom hq ha hb).fieldRange := by
      have := sub_mem (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
        ((h.translationAlgHom hq ha hb).fieldRange.algebraMap_mem a)
      rwa [h.translationAlgHom_apply_x, add_sub_cancel_right] at this
    have hy : y ∈ (h.translationAlgHom hq ha hb).fieldRange := by
      have := sub_mem (sub_mem (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)
        (mul_mem ((h.translationAlgHom hq ha hb).fieldRange.algebraMap_mem (a ^ p ^ n)) hx))
        ((h.translationAlgHom hq ha hb).fieldRange.algebraMap_mem b)
      rwa [h.translationAlgHom_apply_y, sub_sub, add_assoc, add_sub_cancel_right] at this
    rintro z (rfl | rfl)
    exacts [hx, hy]⟩

/-- `σ_{a,b} x = x + a`. -/
@[simp]
theorem translation_apply_x {a b : K} (ha : a ^ (p ^ n) ^ 2 = a)
    (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)) :
    h.translation hq ha hb x = x + algebraMap K F a :=
  h.translationAlgHom_apply_x hq ha hb

/-- `σ_{a,b} y = y + a ^ q x + b`. -/
@[simp]
theorem translation_apply_y {a b : K} (ha : a ^ (p ^ n) ^ 2 = a)
    (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)) :
    h.translation hq ha hb y = y + algebraMap K F (a ^ p ^ n) * x + algebraMap K F b :=
  h.translationAlgHom_apply_y hq ha hb

/-- The translation `σ_{a,b}` lies in the translation group. -/
theorem translation_mem_hermitianTranslations {a b : K} (ha : a ^ (p ^ n) ^ 2 = a)
    (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)) :
    h.translation hq ha hb ∈ hermitianTranslations K p n x y :=
  ⟨a, b, ha, hb, h.translation_apply_x hq ha hb, h.translation_apply_y hq ha hb⟩

/-- **Faithfulness**: `σ_{a,b} = σ_{a',b'}` exactly when `a = a'` and `b = b'`. -/
theorem translation_inj {a b a' b' : K} (ha : a ^ (p ^ n) ^ 2 = a)
    (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)) (ha' : a' ^ (p ^ n) ^ 2 = a')
    (hb' : b' ^ p ^ n + b' = a' ^ (p ^ n + 1)) :
    h.translation hq ha hb = h.translation hq ha' hb' ↔ a = a' ∧ b = b' := by
  refine ⟨fun heq ↦ ?_, fun ⟨haa', hbb'⟩ ↦ by subst haa' hbb'; rfl⟩
  have hx := congrArg (· x) heq
  simp only [translation_apply_x, add_right_inj] at hx
  obtain rfl := (algebraMap K F).injective hx
  have hy := congrArg (· y) heq
  simp only [translation_apply_y, add_right_inj] at hy
  exact ⟨rfl, (algebraMap K F).injective hy⟩

/-- Every element of `TauCeti.hermitianTranslations` is a translation `σ_{a,b}`. -/
theorem exists_translation_eq {σ : F ≃ₐ[K] F} (hσ : σ ∈ hermitianTranslations K p n x y) :
    ∃ (a b : K) (ha : a ^ (p ^ n) ^ 2 = a) (hb : b ^ p ^ n + b = a ^ (p ^ n + 1)),
      h.translation hq ha hb = σ := by
  obtain ⟨a, b, ha, hb, hσx, hσy⟩ := hσ
  refine ⟨a, b, ha, hb, AlgEquiv.coe_toAlgHom_injective ?_⟩
  -- Two `K`-algebra maps out of `F = K(x, y)` agreeing on `x` and `y` are equal.
  have key := IntermediateField.algHom_ext_of_eq_adjoin K h.adjoin_eq_top.symm
    (φ₁ := (h.translation hq ha hb : F →ₐ[K] F).comp (IntermediateField.val ⊤))
    (φ₂ := (σ : F →ₐ[K] F).comp (IntermediateField.val ⊤)) (by
      rintro z (rfl | rfl) <;> simp [hσx, hσy])
  ext z
  simpa using DFunLike.congr_fun key ⟨z, IntermediateField.mem_top⟩

omit hq in
/-- **The order of the translation group**: over a field with `q²` elements, `q = p ^ n`, the
translations of the Hermitian function field form a group of order `q³`. -/
theorem natCard_hermitianTranslations [Finite K] (hK : Nat.card K = (p ^ n) ^ 2) :
    Nat.card (hermitianTranslations K p n x y) = (p ^ n) ^ 3 := by
  classical
  have := Fintype.ofFinite K
  -- A field has at least two elements, so `q > 1`.
  have hq : 1 < p ^ n := by
    have := Finite.one_lt_card (α := K)
    rw [hK] at this
    by_contra hle
    interval_cases h' : p ^ n <;> simp at this
  have hpow (a : K) : a ^ (p ^ n) ^ 2 = a := by
    rw [← hK, Nat.card_eq_fintype_card]
    exact _root_.FiniteField.pow_card a
  -- The translations are in bijection with the pairs `(a, b)` with `b ^ q + b = a ^ (q + 1)`.
  let f : {ab : K × K // ab.2 ^ p ^ n + ab.2 = ab.1 ^ (p ^ n + 1)} →
      hermitianTranslations K p n x y := fun ab ↦
    ⟨h.translation hq (hpow ab.1.1) ab.2, h.translation_mem_hermitianTranslations hq _ _⟩
  have hf : Function.Bijective f := by
    refine ⟨fun ab ab' heq ↦ ?_, fun σ ↦ ?_⟩
    · obtain ⟨h1, h2⟩ := (h.translation_inj hq _ _ _ _).mp (congrArg Subtype.val heq)
      exact Subtype.ext (Prod.ext h1 h2)
    · obtain ⟨a, b, ha, hb, hσ⟩ := h.exists_translation_eq hq σ.2
      exact ⟨⟨(a, b), hb⟩, Subtype.ext hσ⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf),
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b ↦ b ^ p ^ n + b = a ^ (p ^ n + 1)),
    Nat.card_sigma]
  -- For each `a`, the norm `a ^ (q + 1)` satisfies `c ^ q = c`, so there are `q` choices of `b`.
  have hfib (a : K) : Nat.card {b : K // b ^ p ^ n + b = a ^ (p ^ n + 1)} = p ^ n := by
    refine FiniteField.natCard_pow_add_self_eq hK ?_
    rw [← pow_mul, add_mul, one_mul, pow_add, ← sq, hpow, ← pow_succ']
  rw [Nat.card_eq_fintype_card] at hK
  simp only [hfib, Finset.sum_const, Finset.card_univ, hK, smul_eq_mul]
  ring

end IsHermitianCoordinates

end TauCeti
