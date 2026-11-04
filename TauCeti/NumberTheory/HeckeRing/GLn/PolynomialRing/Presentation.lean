/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.LeadingCoefficient
public import TauCeti.NumberTheory.HeckeRing.GLn.PolynomialRing.LeadingExponent
public import TauCeti.NumberTheory.HeckeRing.GLn.ProductSupport
import TauCeti.Algebra.Order.BigOperators.Dominance

/-!
# The `p`-local Hecke ring of `GL_n` is a polynomial ring

**Shimura's Theorem 3.20**: for `p` prime, the `p`-local Hecke ring `R_p = pLocalSubring n p` of
`(SL_n(ℤ), Δ)` is the polynomial ring `ℤ[X₁, …, Xₙ]` on the diagonal prime cosets
`heckeGen k = T(1, …, 1, p, …, p)`, with `k + 1` entries equal to `p`. Here `R_p` is spanned by
the double cosets of integral matrices with `p`-power determinant: it is the positive part of the
spherical Hecke algebra of `GL_n(ℚ_p)`, which is obtained from it by inverting the scalar coset
`T(p, …, p)`.

The proof is a leading-term argument. The monomial `∏ k, heckeGen k ^ e k` is a sum of diagonal
double cosets `T(p ^ g)` that is triangular for the dominance order of exponent vectors
(`TauCeti.Dominates`), `a` dominating `g` when the two have the same total and every leading
partial sum `∑_{j < k} a j` is at most that of `g`:

* the leading coset `T(p ^ leadingExponent e)` occurs with coefficient `1`;
* every coset that occurs is `T(p ^ g)` for a monotone `g` dominated by `leadingExponent e`.

This is proved one generator at a time, from the two halves of the statement for a product of
two diagonal cosets, `HeckeRing.GLn.diagElem_primePowDiag_mul_apply_diagCoset_add` (the
leading coefficient) and `HeckeRing.GLn.exists_primePowDiag_of_diagElem_mul_apply_ne_zero` (the
support), since dominance is compatible with adding exponent vectors. Since
`HeckeRing.GLn.leadingExponent` is injective with image the monotone vectors, the leading
cosets of distinct monomials are distinct and every coset `T(p ^ g)` of `R_p` is a leading coset.
Injectivity then follows by looking at a monomial whose leading coset is maximal, and
surjectivity by induction along the dominance order.

## Main results

* `HeckeRing.GLn.prod_heckeGen_pow_apply_diagCoset_leadingExponent`: the leading coset of a
  monomial occurs with coefficient `1`.
* `HeckeRing.GLn.exists_primePowDiag_of_prod_heckeGen_pow_apply_ne_zero`: every coset of the
  support of a monomial is `T(p ^ g)` for a monotone `g` dominated by the leading exponent vector.
* `HeckeRing.GLn.evalHom_injective`, `HeckeRing.GLn.range_evalHom`: the generators are
  algebraically independent and generate `R_p`.
* `HeckeRing.GLn.polynomialRingEquiv`: **Shimura, Theorem 3.20**, `ℤ[X₁, …, Xₙ] ≃+* R_p`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2, Theorem 3.20.
-/

public section

open Finset TauCeti

namespace HeckeRing.GLn

variable {n : ℕ}

variable [NeZero n]

attribute [local instance] commSemiringIntegralHeckeRingLocal

/-- `x` is triangular with leading coset `T(p ^ a)`: that coset occurs with coefficient `1`, and
every coset that occurs is `T(p ^ g)` for a monotone `g` dominated by `a`. -/
private def IsTriangular (p : ℕ) (a : Fin n → ℕ) (x : IntegralHeckeRing n) : Prop :=
  x (diagCoset (primePowDiag n p a)) = 1 ∧
    ∀ D, x D ≠ 0 → ∃ g, Monotone g ∧ D = diagCoset (primePowDiag n p g) ∧ Dominates a g

omit [NeZero n] in
private lemma isTriangular_one (p : ℕ) : IsTriangular p 0 (1 : IntegralHeckeRing n) := by
  classical
  have h0 : diagCoset (primePowDiag n p 0) = 1 := by
    rw [← diagCoset_one]
    exact congrArg diagCoset (funext fun i ↦ by simp)
  refine ⟨?_, fun D hD ↦ ⟨0, monotone_const, ?_, Dominates.refl 0⟩⟩
  · simp [h0, HeckeCosetModule.one_def]
  · rw [h0]
    by_contra hne
    exact hD (by simp [HeckeCosetModule.one_def, Ne.symm hne])

/-- **Triangularity passes to a product with a diagonal coset.** If `x` is triangular with
leading coset `T(p ^ a)` and `f` is monotone, then `x * T(p ^ f)` is triangular with leading coset
`T(p ^ (a + f))`. -/
private lemma IsTriangular.mul_diagElem {p : ℕ} (hp : p.Prime) {a f : Fin n → ℕ}
    (ha : Monotone a) (hf : Monotone f) {x : IntegralHeckeRing n} (hx : IsTriangular p a x) :
    IsTriangular p (a + f) (x * diagElem (primePowDiag n p f)) := by
  classical
  -- every coset in the support of `T(p ^ g) · T(p ^ f)` is dominated by `g + f`
  have key {D E : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)} (hD : x D ≠ 0)
      (hDE : (HeckeCosetModule.single ℤ D 1 * diagElem (primePowDiag n p f)) E ≠ 0) :
      ∃ g, Monotone g ∧ D = diagCoset (primePowDiag n p g) ∧ Dominates a g ∧
        ∃ h, Monotone h ∧ E = diagCoset (primePowDiag n p h) ∧ Dominates (g + f) h := by
    obtain ⟨g, hg, rfl, hag⟩ := hx.2 D hD
    rw [← diagElem_def] at hDE
    obtain ⟨h, hh, rfl, hsum, hpart⟩ :=
      exists_primePowDiag_of_diagElem_mul_apply_ne_zero hp hg hf hDE
    exact ⟨g, hg, rfl, hag, h, hh, rfl, dominates_def.2 ⟨hsum, hpart⟩⟩
  refine ⟨?_, fun E hE ↦ ?_⟩
  · rw [HeckeCosetModule.mul_def, HeckeCosetModule.mul_apply_eq_sum]
    have hmem : diagCoset (primePowDiag n p a) ∈ x.support := by
      rw [HeckeCosetModule.mem_support_iff, hx.1]
      exact one_ne_zero
    rw [sum_eq_single_of_mem _ hmem, hx.1, one_mul, ← diagElem_def, ← HeckeCosetModule.mul_def,
      diagElem_primePowDiag_mul_apply_diagCoset_add hp.pos ha hf]
    intro D hD hne
    by_contra hDE
    obtain ⟨g, hg, rfl, hag, h, hh, hE, hgh⟩ :=
      key (HeckeCosetModule.mem_support_iff.1 hD) (right_ne_zero_of_mul hDE)
    -- the occurring coset is the leading one, so `g + f` dominates `a + f`; as `a` dominates
    -- `g`, this forces `g = a`
    obtain rfl := eq_of_diagCoset_primePowDiag_eq hp.one_lt (ha.add hf) hh hE
    exact hne (by rw [hag.antisymm hgh.of_add_right])
  · rw [HeckeCosetModule.mul_def, HeckeCosetModule.mul_apply_eq_sum] at hE
    obtain ⟨D, hD, hDE⟩ := exists_ne_zero_of_sum_ne_zero hE
    obtain ⟨g, -, -, hag, h, hh, rfl, hgh⟩ :=
      key (HeckeCosetModule.mem_support_iff.1 hD) (right_ne_zero_of_mul hDE)
    exact ⟨h, hh, rfl, (hag.add_right f).trans hgh⟩

/-- The partial products of a monomial are triangular, with leading exponent vector the sum of
the exponent vectors of the generators taken. -/
private lemma isTriangular_prod_heckeGen_pow {p : ℕ} (hp : p.Prime) (e : Fin n → ℕ)
    (s : Finset (Fin n)) :
    IsTriangular p (∑ k ∈ s, e k • heckeGenExponent n k) (∏ k ∈ s, heckeGen n p k ^ e k) := by
  classical
  have hmono (s : Finset (Fin n)) : Monotone (∑ k ∈ s, e k • heckeGenExponent n k) :=
    fun i j hij ↦ by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact sum_le_sum fun k _ ↦ Nat.mul_le_mul_left _ (heckeGenExponent_monotone n k hij)
  induction s using Finset.induction_on with
  | empty => simpa using isTriangular_one (n := n) p
  | insert k s hk ih =>
    rw [sum_insert hk, prod_insert hk, add_comm, mul_comm]
    -- multiply in the generator `heckeGen k` one factor at a time
    suffices ∀ m, IsTriangular p (∑ k ∈ s, e k • heckeGenExponent n k + m • heckeGenExponent n k)
        ((∏ k ∈ s, heckeGen n p k ^ e k) * heckeGen n p k ^ m) from this (e k)
    intro m
    induction m with
    | zero => simpa using ih
    | succ m ihm =>
      have h := ihm.mul_diagElem
        (a := ∑ k ∈ s, e k • heckeGenExponent n k + m • heckeGenExponent n k) hp
        ((hmono s).add (Monotone.const_nsmul (heckeGenExponent_monotone n k) m))
        (heckeGenExponent_monotone n k)
      rwa [← heckeGenDiag_eq_primePowDiag, ← heckeGen_def, mul_assoc, ← pow_succ, add_assoc,
        ← succ_nsmul] at h

private lemma isTriangular_prod_heckeGen_pow_univ {p : ℕ} (hp : p.Prime) (e : Fin n → ℕ) :
    IsTriangular p (leadingExponent e) (∏ k, heckeGen n p k ^ e k) := by
  rw [leadingExponent_eq_sum_smul_heckeGenExponent]
  exact isTriangular_prod_heckeGen_pow hp e univ

/-- **The leading coset of a Hecke monomial has coefficient one.** For `p` prime, the coset
`T(p ^ leadingExponent e)` occurs in `∏ k, heckeGen k ^ e k` with coefficient `1`. -/
theorem prod_heckeGen_pow_apply_diagCoset_leadingExponent {p : ℕ} (hp : p.Prime)
    (e : Fin n → ℕ) :
    (∏ k, heckeGen n p k ^ e k) (diagCoset (primePowDiag n p (leadingExponent e))) = 1 :=
  (isTriangular_prod_heckeGen_pow_univ hp e).1

/-- **The support of a Hecke monomial lies below its leading coset.** For `p` prime, every
double coset occurring in `∏ k, heckeGen k ^ e k` is `T(p ^ g)` for a monotone exponent vector
`g` with total `∑ i, leadingExponent e i` whose leading partial sums are at least those of
`leadingExponent e`. -/
theorem exists_primePowDiag_of_prod_heckeGen_pow_apply_ne_zero {p : ℕ} (hp : p.Prime)
    (e : Fin n → ℕ) {D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)}
    (h : (∏ k, heckeGen n p k ^ e k) D ≠ 0) :
    ∃ g : Fin n → ℕ, Monotone g ∧ D = diagCoset (primePowDiag n p g) ∧
      ∑ i, g i = ∑ i, leadingExponent e i ∧
      ∀ (k : ℕ) (hk : k ≤ n), ∑ j : Fin k, leadingExponent e (Fin.castLE hk j) ≤
        ∑ j : Fin k, g (Fin.castLE hk j) :=
  let ⟨g, hg, hD, hdom⟩ := (isTriangular_prod_heckeGen_pow_univ hp e).2 D h
  ⟨g, hg, hD, dominates_def.1 hdom⟩

variable (n) in
/-- **The generators are algebraically independent** (Shimura, Theorem 3.20): for `p` prime,
evaluation of `ℤ[X₁, …, Xₙ]` at the generators `heckeGen k = T(1, …, 1, p, …, p)` is injective.

The image of a nonzero polynomial is nonzero at the leading coset of a monomial of its support
whose leading exponent vector is maximal for the dominance order: no other monomial of the
support reaches that coset. -/
theorem evalHom_injective {p : ℕ} (hp : p.Prime) : Function.Injective (evalHom n p) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun P hP ↦ ?_
  by_contra hP0
  obtain ⟨d, hd, hmax⟩ := P.support.exists_max_image (fun d ↦ dominanceDefect (leadingExponent ⇑d))
    (MvPolynomial.support_nonempty.2 hP0)
  have h := congrArg (· (diagCoset (primePowDiag n p (leadingExponent ⇑d)))) hP
  rw [evalHom_apply, sum_eq_single_of_mem d hd, HeckeCosetModule.zero_apply,
    prod_heckeGen_pow_apply_diagCoset_leadingExponent hp, smul_eq_mul, mul_one] at h
  · exact MvPolynomial.mem_support_iff.1 hd h
  -- every other monomial of the support vanishes at that coset
  intro d' hd' hne
  by_contra hE
  obtain ⟨g, hg, hgd, hdom⟩ := (isTriangular_prod_heckeGen_pow_univ hp ⇑d').2 _
    (right_ne_zero_of_mul (by simpa only [smul_eq_mul] using hE))
  obtain rfl := eq_of_diagCoset_primePowDiag_eq hp.one_lt (leadingExponent_monotone _) hg hgd
  rcases eq_or_ne (leadingExponent ⇑d') (leadingExponent ⇑d) with heq | heq
  · exact hne (DFunLike.coe_injective (leadingExponent_injective heq))
  · exact (hmax d' hd').not_gt (hdom.dominanceDefect_lt heq)

/-- Every generator `T(p ^ g)` of `R_p` is a polynomial in the `heckeGen k`. A coset `T(p ^ g)`
with `g` monotone is the leading coset of a monomial, whose remaining cosets lie strictly below
`T(p ^ g)` in the dominance order, so this follows by induction along that order. -/
private lemma pLocalSubring_le_evalHom_range {p : ℕ} (hp : p.Prime) :
    pLocalSubring n p ≤ (evalHom n p).range := by
  classical
  refine (pLocalSubring_le_iff n p _).2 fun g hg ↦ ?_
  induction hm : dominanceDefect g using Nat.strong_induction_on generalizing g with
  | _ m ih =>
  obtain ⟨e, rfl⟩ := exists_leadingExponent_eq_iff.2 hg
  set M : IntegralHeckeRing n := ∏ k, heckeGen n p k ^ e k
  set D₀ := diagCoset (primePowDiag n p (leadingExponent e))
  have hM : M ∈ (evalHom n p).range := ⟨∏ k, MvPolynomial.X k ^ e k, by simp [M, map_prod]⟩
  have hD₀ : M D₀ = 1 := prod_heckeGen_pow_apply_diagCoset_leadingExponent hp e
  have hmem : D₀ ∈ M.support := by
    rw [HeckeCosetModule.mem_support_iff, hD₀]
    exact one_ne_zero
  -- split the leading coset off the expansion of `M`
  have hsplit : diagElem (primePowDiag n p (leadingExponent e)) =
      M - ∑ D ∈ M.support.erase D₀, M D • HeckeCosetModule.single ℤ D 1 := by
    have h := (add_sum_erase M.support (fun D ↦ M D • HeckeCosetModule.single ℤ D 1) hmem).trans
      (HeckeCosetModule.eq_sum_smul_single M).symm
    rw [hD₀, one_smul] at h
    rw [diagElem_def]
    exact eq_sub_of_add_eq h
  rw [hsplit]
  refine sub_mem hM (sum_mem fun D hD ↦ zsmul_mem ?_ _)
  obtain ⟨hne, hD⟩ := mem_erase.1 hD
  obtain ⟨h, hh, rfl, hdom⟩ := (isTriangular_prod_heckeGen_pow_univ hp e).2 D
    (HeckeCosetModule.mem_support_iff.1 hD)
  have hne' : leadingExponent e ≠ h := by rintro rfl; exact hne rfl
  rw [← diagElem_def]
  exact ih _ (hm ▸ hdom.dominanceDefect_lt hne') h hh rfl

variable (n) in
/-- **The generators generate `R_p`** (Shimura, Theorem 3.20): for `p` prime, the polynomials in
the generators `heckeGen k` are exactly the elements of the `p`-local Hecke ring. -/
theorem range_evalHom {p : ℕ} (hp : p.Prime) : (evalHom n p).range = pLocalSubring n p :=
  le_antisymm (fun _ ⟨P, hP⟩ ↦ hP ▸ evalHom_mem_pLocalSubring n p P)
    (pLocalSubring_le_evalHom_range hp)

variable (n) in
/-- The presentation map `ℤ[X₁, …, Xₙ] → R_p` is injective, for `p` prime. -/
theorem evalHomLocal_injective {p : ℕ} (hp : p.Prime) : Function.Injective (evalHomLocal n p) :=
  fun P Q hPQ ↦ evalHom_injective n hp (by rw [← evalHomLocal_coe, ← evalHomLocal_coe, hPQ])

variable (n) in
/-- The presentation map `ℤ[X₁, …, Xₙ] → R_p` is surjective, for `p` prime. -/
theorem evalHomLocal_surjective {p : ℕ} (hp : p.Prime) :
    Function.Surjective (evalHomLocal n p) := by
  rintro ⟨y, hy⟩
  obtain ⟨f, hf⟩ := (range_evalHom n hp).ge hy
  exact ⟨f, Subtype.ext ((evalHomLocal_coe n p f).trans hf)⟩

variable (n) in
/-- **Shimura, Theorem 3.20**: for `p` prime, the `p`-local Hecke ring `R_p` of `GL_n` is the
polynomial ring `ℤ[X₁, …, Xₙ]` on the diagonal prime cosets
`heckeGen k = T(1, …, 1, p, …, p)`, with `k + 1` entries equal to `p`. -/
noncomputable def polynomialRingEquiv {p : ℕ} (hp : p.Prime) :
    MvPolynomial (Fin n) ℤ ≃+* pLocalSubring n p :=
  RingEquiv.ofBijective (evalHomLocal n p)
    ⟨evalHomLocal_injective n hp, evalHomLocal_surjective n hp⟩

/-- The presentation isomorphism is the evaluation map. -/
@[simp] lemma polynomialRingEquiv_apply {p : ℕ} (hp : p.Prime) (f : MvPolynomial (Fin n) ℤ) :
    polynomialRingEquiv n hp f = evalHomLocal n p f := (rfl)

end HeckeRing.GLn
