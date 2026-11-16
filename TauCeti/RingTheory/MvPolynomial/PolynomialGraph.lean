/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.PowerSubstitution

import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import TauCeti.Data.Finsupp.Digits

/-!
# The base-`B` Kronecker substitution `polynomialGraph`

For a commutative semiring `k` and natural numbers `m, B`, `TauCeti.polynomialGraph k m B` is the
ring homomorphism `MvPolynomial (Fin m) k →+* Polynomial k` fixing coefficients and sending the
`i`-th variable `X i` (`0 ≤ i < m`) to `X ^ (B ^ i)`. Because variables are indexed from zero, the
first coordinate `X 0` (when `m > 0`) maps to `X ^ (B ^ 0) = X`, so `polynomialGraph k m B` is
surjective for every `B` whenever `m > 0` (`TauCeti.polynomialGraph_surjective`). Over a
commutative ring `k`, its spectrum is the morphism `𝔸¹_k → 𝔸^m_k`,
`T ↦ (T, T ^ B, T ^ (B ^ 2), …, T ^ (B ^ (m - 1)))`, which is a closed immersion for `m > 0` and
passes through the origin when `B ≥ 1` (`TauCeti.constantCoeff_polynomialGraph`,
`TauCeti.eval_zero_polynomialGraph`).

The map `polynomialGraph k m B` is the underlying ring homomorphism of the Kronecker substitution
`MvPolynomial.aeval (fun i ↦ X ^ (B ^ i))` studied in `TauCeti.RingTheory.MvPolynomial.Kronecker`
for the weight `i ↦ B ^ i`, and for `m = 2` it is the underlying ring homomorphism of
`MvPolynomial.powerSubstitution B` (`TauCeti.polynomialGraph_two_vars`). Combining
`MvPolynomial.coeff_aeval_X_pow_weight` and `MvPolynomial.injOn_aeval_X_pow` with the uniqueness of
bounded base-`B` expansions (`Finsupp.injOn_weight_pow`) shows that when every exponent in the
support of `h` is strictly below `B`, every coefficient of `h` survives in `polynomialGraph k m B h`
(`TauCeti.polynomialGraph_coeff`), and `polynomialGraph k m B` is injective on the polynomials
whose individual exponents all lie below `B` (`TauCeti.injOn_polynomialGraph`). Over a finite field
where a hypersurface may contain every rational line through the origin, choosing `B ≥ 2` above all
exponents of `h` produces a polynomial graph through the origin on which `h` does not vanish
identically (`TauCeti.exists_polynomialGraph_ne_zero`).

## Main definitions and results

* `TauCeti.polynomialGraph`: the ring homomorphism `MvPolynomial (Fin m) k →+* Polynomial k`
  sending `C a ↦ C a` and `X i ↦ X ^ (B ^ i)`.
* `TauCeti.constantCoeff_polynomialGraph`, `TauCeti.eval_zero_polynomialGraph`: for `B ≥ 1`,
  `polynomialGraph k m B` preserves evaluation at the origin.
* `TauCeti.polynomialGraph_zero_vars`, `TauCeti.polynomialGraph_one_var`,
  `TauCeti.polynomialGraph_two_vars`: comparison with `MvPolynomial.constantCoeff` (`m = 0`),
  `MvPolynomial.uniqueAlgEquiv` (`m = 1`), and `MvPolynomial.powerSubstitution` (`m = 2`).
* `TauCeti.polynomialGraph_map`: naturality with respect to coefficient ring homomorphisms.
* `TauCeti.not_injective_polynomialGraph`: for `m ≥ 2` over a nontrivial semiring,
  `polynomialGraph k m B` is not injective (`X 1` and `X 0 ^ B` have the same image).
* `TauCeti.polynomialGraph_coeff`: if all exponents in `h.support` and in `e` are `< B`, then the
  coefficient of `X ^ (∑ i, e i * B ^ i)` in `polynomialGraph k m B h` equals `h.coeff e`.
* `TauCeti.injOn_polynomialGraph`, `TauCeti.polynomialGraph_eq_zero_iff`: `polynomialGraph k m B`
  is injective on polynomials all of whose exponents are `< B`.
* `TauCeti.polynomialGraph_surjective`: for `m > 0`, `polynomialGraph k m B` is surjective for
  every `B`.

## References

* M. Kisin and R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, *Annals of Mathematics* 202 (2025), no. 3 (arXiv:2103.09945v2, §§5.2–5.3, pp. 52–54).
* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  Exercise 3.5.
-/

public section

noncomputable section

namespace TauCeti

open MvPolynomial Finsupp

section CommSemiring

variable {k K : Type*} [CommSemiring k] [CommSemiring K]

/-- The **base-`B` Kronecker substitution** `k[X_0, …, X_{m-1}] →+* k[T]`, fixing constants and
sending `X_i` to `T ^ (B ^ i)` (`0 ≤ i < m`). Variables are numbered from zero, so `X_0 ↦ T` when
`m > 0`. -/
def polynomialGraph (k : Type*) [CommSemiring k] (m B : ℕ) :
    MvPolynomial (Fin m) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C fun i ↦ Polynomial.X ^ (B ^ (i : ℕ))

/-- Explicit unfolding of `polynomialGraph` in terms of `MvPolynomial.eval₂Hom`. -/
theorem polynomialGraph_def (k : Type*) [CommSemiring k] (m B : ℕ) :
    polynomialGraph k m B =
      MvPolynomial.eval₂Hom Polynomial.C fun i : Fin m ↦ Polynomial.X ^ (B ^ (i : ℕ)) :=
  (rfl)

/-- `polynomialGraph k m B` is the ring homomorphism underlying the `k`-algebra Kronecker
substitution `MvPolynomial.aeval (fun i ↦ X ^ (B ^ i))`. -/
theorem polynomialGraph_eq_aeval (k : Type*) [CommSemiring k] (m B : ℕ) :
    polynomialGraph k m B =
      (MvPolynomial.aeval
        fun i : Fin m ↦ (Polynomial.X : Polynomial k) ^ (B ^ (i : ℕ))).toRingHom := by
  apply MvPolynomial.ringHom_ext <;> intro x <;> simp [polynomialGraph_def]

/-- Pointwise form of `polynomialGraph_eq_aeval`. -/
theorem polynomialGraph_apply_eq_aeval (m B : ℕ) (h : MvPolynomial (Fin m) k) :
    polynomialGraph k m B h =
      MvPolynomial.aeval (fun i : Fin m ↦ (Polynomial.X : Polynomial k) ^ (B ^ (i : ℕ))) h :=
  DFunLike.congr_fun (polynomialGraph_eq_aeval k m B) h

/-- `polynomialGraph` fixes constants. -/
@[simp, grind =]
theorem polynomialGraph_C (m B : ℕ) (a : k) :
    polynomialGraph k m B (MvPolynomial.C a) = Polynomial.C a := by
  simp [polynomialGraph_def]

/-- Composing `polynomialGraph k m B` with the coefficient inclusion `MvPolynomial.C` yields
`Polynomial.C`. -/
@[simp]
theorem polynomialGraph_comp_C (k : Type*) [CommSemiring k] (m B : ℕ) :
    (polynomialGraph k m B).comp MvPolynomial.C = Polynomial.C :=
  RingHom.ext (polynomialGraph_C m B)

/-- `polynomialGraph k m B` sends the `i`-th variable `X i` to `X ^ (B ^ i)`. -/
@[simp, grind =]
theorem polynomialGraph_X (m B : ℕ) (i : Fin m) :
    polynomialGraph k m B (MvPolynomial.X i) = Polynomial.X ^ (B ^ (i : ℕ)) := by
  simp [polynomialGraph_def]

/-- For `m > 0`, the first variable `X ⟨0, hm⟩` maps to `X`, for every `B` including `B = 0`. -/
theorem polynomialGraph_X_zero {m : ℕ} (hm : 0 < m) (B : ℕ) :
    polynomialGraph k m B (MvPolynomial.X ⟨0, hm⟩) = Polynomial.X := by
  simp

/-- `polynomialGraph k m B` sends the monomial `a X^d` to `monomial (weight (B ^ ·) d) a`. -/
@[simp]
theorem polynomialGraph_monomial (m B : ℕ) (d : Fin m →₀ ℕ) (a : k) :
    polynomialGraph k m B (MvPolynomial.monomial d a) =
      Polynomial.monomial (Finsupp.weight (fun i : Fin m ↦ B ^ (i : ℕ)) d) a := by
  rw [polynomialGraph_apply_eq_aeval, MvPolynomial.aeval_X_pow_left_monomial]

/-- `polynomialGraph k m B` sends the monomial `a X^d` to `C a * X ^ (weight (B ^ ·) d)`. -/
theorem polynomialGraph_monomial_eq_C_mul_X_pow (m B : ℕ) (d : Fin m →₀ ℕ) (a : k) :
    polynomialGraph k m B (MvPolynomial.monomial d a) =
      Polynomial.C a * Polynomial.X ^ Finsupp.weight (fun i : Fin m ↦ B ^ (i : ℕ)) d := by
  rw [polynomialGraph_monomial, Polynomial.C_mul_X_pow_eq_monomial]

/-- Evaluating `polynomialGraph k m B h` at `t` in a `k`-algebra `K` evaluates `h` on the tuple
`i ↦ t ^ (B ^ i)`. -/
@[simp]
theorem aeval_polynomialGraph [Algebra k K] (m B : ℕ) (t : K) (h : MvPolynomial (Fin m) k) :
    Polynomial.aeval t (polynomialGraph k m B h) =
      MvPolynomial.aeval (fun i : Fin m ↦ t ^ (B ^ (i : ℕ))) h := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- Evaluating `polynomialGraph k m B h` at `t : k` evaluates `h` at `i ↦ t ^ (B ^ i)`. -/
@[simp]
theorem eval_polynomialGraph (m B : ℕ) (t : k) (h : MvPolynomial (Fin m) k) :
    (polynomialGraph k m B h).eval t = MvPolynomial.eval (fun i : Fin m ↦ t ^ (B ^ (i : ℕ))) h := by
  rw [← Polynomial.coe_aeval_eq_eval, ← MvPolynomial.aeval_eq_eval]
  exact aeval_polynomialGraph m B t h

/-- For `B ≥ 1`, `polynomialGraph k m B` preserves the constant coefficient (evaluation at the
origin). -/
theorem constantCoeff_polynomialGraph {m B : ℕ} (hB : 1 ≤ B) (h : MvPolynomial (Fin m) k) :
    Polynomial.constantCoeff (polynomialGraph k m B h) = MvPolynomial.constantCoeff h := by
  rw [Polynomial.constantCoeff_apply, Polynomial.coeff_zero_eq_eval_zero, eval_polynomialGraph,
    ← MvPolynomial.eval_zero]
  congr 2
  funext i
  exact zero_pow (Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))).ne'

/-- Ring-homomorphism form of `constantCoeff_polynomialGraph`: for `B ≥ 1`, composing
`Polynomial.constantCoeff` with `polynomialGraph k m B` yields `MvPolynomial.constantCoeff`. -/
theorem constantCoeff_comp_polynomialGraph {m B : ℕ} (hB : 1 ≤ B) :
    (Polynomial.constantCoeff (R := k)).comp (polynomialGraph k m B) =
      MvPolynomial.constantCoeff :=
  RingHom.ext (constantCoeff_polynomialGraph hB)

/-- For `B ≥ 1`, evaluating `polynomialGraph k m B h` at `0` agrees with evaluating `h` at the
origin `0 : Fin m → k`. -/
theorem eval_zero_polynomialGraph {m B : ℕ} (hB : 1 ≤ B) (h : MvPolynomial (Fin m) k) :
    (polynomialGraph k m B h).eval 0 = MvPolynomial.eval 0 h := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.constantCoeff_apply,
    constantCoeff_polynomialGraph hB, MvPolynomial.eval_zero]

/-- On zero variables, `polynomialGraph k 0 B` is `Polynomial.C ∘ MvPolynomial.constantCoeff`. -/
theorem polynomialGraph_zero_vars (k : Type*) [CommSemiring k] (B : ℕ) :
    polynomialGraph k 0 B = Polynomial.C.comp MvPolynomial.constantCoeff := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · exact fun i ↦ i.elim0

/-- Pointwise form of `polynomialGraph_zero_vars`. -/
@[simp]
theorem polynomialGraph_zero_vars_apply (B : ℕ) (h : MvPolynomial (Fin 0) k) :
    polynomialGraph k 0 B h = Polynomial.C (MvPolynomial.constantCoeff h) :=
  DFunLike.congr_fun (polynomialGraph_zero_vars k B) h

/-- On one variable, `polynomialGraph k 1 B` is the canonical isomorphism
`MvPolynomial.uniqueAlgEquiv k (Fin 1) : k[X_0] ≃ₐ[k] k[T]`, for every `B` including `B = 0`. -/
theorem polynomialGraph_one_var (k : Type*) [CommSemiring k] (B : ℕ) :
    polynomialGraph k 1 B = (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    rw [Subsingleton.elim i 0]
    simp

/-- On one variable, `polynomialGraph k 1 B` is bijective for every `B`. -/
theorem bijective_polynomialGraph_one_var (k : Type*) [CommSemiring k] (B : ℕ) :
    Function.Bijective (polynomialGraph k 1 B) := by
  rw [polynomialGraph_one_var]
  exact (MvPolynomial.uniqueAlgEquiv k (Fin 1)).bijective

/-- On two variables, `polynomialGraph k 2 B` is the ring homomorphism underlying
`MvPolynomial.powerSubstitution B` (`X 0 ↦ X`, `X 1 ↦ X ^ B`). -/
theorem polynomialGraph_two_vars (k : Type*) [CommSemiring k] (B : ℕ) :
    polynomialGraph k 2 B = (MvPolynomial.powerSubstitution (R := k) B).toRingHom := by
  rw [MvPolynomial.powerSubstitution_eq_aeval_X_pow]
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    fin_cases i <;> simp

/-- `polynomialGraph` commutes with changing coefficients along a ring homomorphism
`φ : k →+* K`. -/
@[simp]
theorem polynomialGraph_map (φ : k →+* K) (m B : ℕ) (h : MvPolynomial (Fin m) k) :
    polynomialGraph K m B (MvPolynomial.map φ h) = Polynomial.map φ (polynomialGraph k m B h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d a => simp
  | add p q hp hq => simp [hp, hq, Polynomial.map_add]

/-- Ring-homomorphism form of `polynomialGraph_map`. -/
theorem polynomialGraph_comp_map (φ : k →+* K) (m B : ℕ) :
    (polynomialGraph K m B).comp (MvPolynomial.map φ) =
      (Polynomial.mapRingHom φ).comp (polynomialGraph k m B) :=
  RingHom.ext (polynomialGraph_map φ m B)

/-- Every exponent in the support of `polynomialGraph k m B h` is the base-`B` positional weight of
some exponent in `h.support`. -/
theorem support_polynomialGraph_subset (m B : ℕ) (h : MvPolynomial (Fin m) k) :
    (polynomialGraph k m B h).support ⊆
      h.support.image (Finsupp.weight fun i : Fin m ↦ B ^ (i : ℕ)) := by
  classical
  intro n hn
  by_contra hmem
  apply Polynomial.mem_support_iff.mp hn
  conv_lhs => rw [h.as_sum]
  simp only [map_sum, polynomialGraph_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial_apply]
  exact Finset.sum_eq_zero fun d hd ↦
    ite_eq_right_iff.mpr fun heq ↦ False.elim (hmem (Finset.mem_image.mpr ⟨d, hd, heq⟩))

/-- If `B > 0` and every exponent in `h.support` has entries `< B`, then
`(polynomialGraph k m B h).natDegree < B ^ m`. -/
theorem natDegree_polynomialGraph_lt {m B : ℕ} (hB : 0 < B) {h : MvPolynomial (Fin m) k}
    (hh : ∀ d ∈ h.support, ∀ i, d i < B) :
    (polynomialGraph k m B h).natDegree < B ^ m := by
  rcases eq_or_ne (polynomialGraph k m B h) 0 with h0 | h0
  · simp [h0, pow_pos hB]
  · refine (Polynomial.natDegree_lt_iff_degree_lt h0).mpr ?_
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro n hn
    refine Polynomial.notMem_support_iff.mp fun hmem ↦ ?_
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_polynomialGraph_subset m B h hmem)
    exact hn.not_gt (Finsupp.weight_pow_lt_pow (hh d hd))

/-- Over a nontrivial semiring and in `m ≥ 2` variables, `X 1` and `X 0 ^ B` are distinct
polynomials with the same image `X ^ B`, so `polynomialGraph k m B` is not injective. -/
theorem not_injective_polynomialGraph [Nontrivial k] {m : ℕ} (hm : 2 ≤ m) (B : ℕ) :
    ¬ Function.Injective (polynomialGraph k m B) := by
  intro hinj
  have heq : (MvPolynomial.X ⟨1, hm⟩ : MvPolynomial (Fin m) k) =
      MvPolynomial.X ⟨0, by omega⟩ ^ B :=
    hinj (by simp)
  rcases eq_or_ne B 0 with rfl | hB
  · simpa using congrArg (MvPolynomial.eval 0) heq
  · simpa [zero_pow hB] using
      congrArg (MvPolynomial.eval fun i : Fin m ↦ if (i : ℕ) = 1 then (1 : k) else 0) heq

/-! ### Bounded-base coefficient preservation and injectivity -/

/-- **Coefficients survive bounded Kronecker substitution.** Over any commutative semiring `k`, if
every entry `d i` of every exponent vector `d ∈ h.support` is `< B`, then for every exponent vector
`e : Fin m →₀ ℕ` with all `e i < B` the coefficient of `X ^ (∑ i, e i * B ^ i)` in
`polynomialGraph k m B h` equals `h.coeff e`. -/
theorem polynomialGraph_coeff {k : Type*} [CommSemiring k] {m B : ℕ}
    (h : MvPolynomial (Fin m) k) (hh : ∀ d ∈ h.support, ∀ i, d i < B)
    (e : Fin m →₀ ℕ) (he : ∀ i, e i < B) :
    (polynomialGraph k m B h).coeff (Finsupp.weight (fun i : Fin m ↦ B ^ (i : ℕ)) e) =
      h.coeff e := by
  rw [polynomialGraph_apply_eq_aeval]
  exact MvPolynomial.coeff_aeval_X_pow_weight (Finsupp.injOn_weight_pow m B)
    (fun d hd ↦ hh d hd) he

/-- `polynomialGraph k m B` is injective on the polynomials whose support lies in the bounded box
`{d : Fin m →₀ ℕ | ∀ i, d i < B}`, for every `m` and `B`. -/
theorem injOn_polynomialGraph (k : Type*) [CommSemiring k] (m B : ℕ) :
    Set.InjOn (polynomialGraph k m B)
      {h : MvPolynomial (Fin m) k | ∀ d ∈ h.support, ∀ i, d i < B} := by
  rw [polynomialGraph_eq_aeval]
  refine (MvPolynomial.injOn_aeval_X_pow (R := k) (Finsupp.injOn_weight_pow m B)).mono ?_
  intro h hh
  exact (MvPolynomial.mem_restrictSupport_iff k).mpr fun d hd ↦ hh d hd

/-- For `h` with all exponents in `h.support` strictly below `B`, `polynomialGraph k m B h = 0` if
and only if `h = 0`. -/
theorem polynomialGraph_eq_zero_iff {k : Type*} [CommSemiring k] {m B : ℕ}
    {h : MvPolynomial (Fin m) k} (hh : ∀ d ∈ h.support, ∀ i, d i < B) :
    polynomialGraph k m B h = 0 ↔ h = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ by simp [h0]⟩
  exact injOn_polynomialGraph k m B hh (by simp) (by simpa using h0)

/-- A nonzero polynomial `h` all of whose exponents are `< B` has nonzero image under
`polynomialGraph k m B`. -/
theorem polynomialGraph_ne_zero {k : Type*} [CommSemiring k] {m B : ℕ}
    {h : MvPolynomial (Fin m) k} (hh : ∀ d ∈ h.support, ∀ i, d i < B) (hne : h ≠ 0) :
    polynomialGraph k m B h ≠ 0 :=
  (polynomialGraph_eq_zero_iff hh).not.mpr hne

/-- `polynomialGraph k m B` preserves `k`-linear independence of any family of polynomials whose
exponents all lie below `B`. -/
theorem linearIndependent_polynomialGraph {k ι : Type*} [CommSemiring k] {m B : ℕ}
    {φ : ι → MvPolynomial (Fin m) k}
    (hφB : ∀ j, ∀ d ∈ (φ j).support, ∀ i, d i < B) (hφ : LinearIndependent k φ) :
    LinearIndependent k fun j ↦ polynomialGraph k m B (φ j) := by
  simp only [polynomialGraph_apply_eq_aeval]
  exact MvPolynomial.linearIndependent_aeval_X_pow (Finsupp.injOn_weight_pow m B)
    (fun j d hd ↦ hφB j d hd) hφ

/-- For any nonzero polynomial `h` over a commutative semiring `k`, there exists a base `B ≥ 2`
exceeding every exponent in `h.support` such that `polynomialGraph k m B h ≠ 0`. -/
theorem exists_polynomialGraph_ne_zero {k : Type*} [CommSemiring k] {m : ℕ}
    {h : MvPolynomial (Fin m) k} (hh : h ≠ 0) :
    ∃ B : ℕ, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧ polynomialGraph k m B h ≠ 0 := by
  have hsupp : ∀ d ∈ h.support, ∀ i, d i < max 2 (h.totalDegree + 1) := fun d hd i ↦ by
    have hle : d i ≤ h.totalDegree :=
      (MvPolynomial.monomial_le_degreeOf i hd).trans (h.degreeOf_le_totalDegree i)
    omega
  exact ⟨max 2 (h.totalDegree + 1), le_max_left _ _, hsupp, polynomialGraph_ne_zero hsupp hh⟩

/-! ### Surjectivity -/

/-- Evaluating a univariate polynomial `p` at the first variable `X ⟨0, hm⟩` via
`Polynomial.eval₂ MvPolynomial.C` is a right inverse of `polynomialGraph k m B` for every `m > 0`
and every `B` (including `B = 0`). -/
@[simp]
theorem polynomialGraph_eval₂_X_zero {k : Type*} [CommSemiring k] {m : ℕ}
    (hm : 0 < m) (B : ℕ) (p : Polynomial k) :
    polynomialGraph k m B (p.eval₂ MvPolynomial.C (MvPolynomial.X ⟨0, hm⟩)) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Polynomial.eval₂_add]
  | monomial n a => simp [Polynomial.eval₂_monomial, Polynomial.C_mul_X_pow_eq_monomial]

/-- Evaluating a univariate polynomial `p` at the first variable `X ⟨0, hm⟩` via `Polynomial.aeval`
is a right inverse of `polynomialGraph k m B` for every `m > 0` and every `B`. -/
@[simp]
theorem polynomialGraph_aeval_X_zero {k : Type*} [CommSemiring k] {m : ℕ}
    (hm : 0 < m) (B : ℕ) (p : Polynomial k) :
    polynomialGraph k m B (Polynomial.aeval (MvPolynomial.X ⟨0, hm⟩) p) = p := by
  rw [Polynomial.aeval_def, MvPolynomial.algebraMap_eq]
  exact polynomialGraph_eval₂_X_zero hm B p

/-- For `m > 0`, `polynomialGraph k m B` is surjective over any commutative semiring and for every
base `B` (including `B = 0`). -/
theorem polynomialGraph_surjective {k : Type*} [CommSemiring k] {m : ℕ} (hm : 0 < m) (B : ℕ) :
    Function.Surjective (polynomialGraph k m B) := fun p ↦
  ⟨p.eval₂ MvPolynomial.C (MvPolynomial.X ⟨0, hm⟩), polynomialGraph_eval₂_X_zero hm B p⟩

/-- On zero variables over a nontrivial semiring, `polynomialGraph k 0 B` is not surjective: `X` is
not in the image of `Polynomial.C`. -/
theorem not_surjective_polynomialGraph_zero (k : Type*) [CommSemiring k] [Nontrivial k] (B : ℕ) :
    ¬ Function.Surjective (polynomialGraph k 0 B) := by
  intro hsurj
  obtain ⟨h, hh⟩ := hsurj Polynomial.X
  have h1 := congrArg (·.coeff 1) hh
  simp at h1

end CommSemiring

section CommRing

/-- For `m ≥ 2` over a commutative ring, `X 1 - X 0 ^ B` lies in the kernel of
`polynomialGraph k m B`. -/
theorem polynomialGraph_X_sub_X_pow {k : Type*} [CommRing k] {m : ℕ} (hm : 2 ≤ m) (B : ℕ) :
    polynomialGraph k m B
      (MvPolynomial.X ⟨1, hm⟩ - MvPolynomial.X ⟨0, by omega⟩ ^ B) = 0 := by
  simp

/-- Over a nontrivial commutative ring and for `m ≥ 2`, for every base `B` (including `B = 0`) the
polynomial `X 1 - X 0 ^ B` is nonzero yet vanishes under `polynomialGraph k m B`. -/
theorem exists_ne_zero_polynomialGraph_eq_zero (k : Type*) [CommRing k] [Nontrivial k] {m : ℕ}
    (hm : 2 ≤ m) (B : ℕ) :
    ∃ h : MvPolynomial (Fin m) k, h ≠ 0 ∧ polynomialGraph k m B h = 0 := by
  refine ⟨MvPolynomial.X ⟨1, hm⟩ - MvPolynomial.X ⟨0, by omega⟩ ^ B, fun h0 ↦ ?_, by simp⟩
  rcases eq_or_ne B 0 with rfl | hB
  · simpa using congrArg (MvPolynomial.eval 0) h0
  · simpa [zero_pow hB] using
      congrArg (MvPolynomial.eval fun i : Fin m ↦ if (i : ℕ) = 1 then (1 : k) else 0) h0

/-! ### Examples and negative controls -/

/-- Over `𝔽_2`, `h = X 0 ^ 2 * X 1 - X 0 * X 1 ^ 2` vanishes identically on every `𝔽_2`-rational
line `(a T, b T)` through the origin, whereas the base-`3` Kronecker graph pulls `h` back to the
nonzero polynomial `X ^ 5 + X ^ 7`. -/
example :
    (∀ a b : ZMod 2,
      MvPolynomial.eval₂Hom Polynomial.C
        ![Polynomial.C a * Polynomial.X, Polynomial.C b * Polynomial.X]
        (X 0 ^ 2 * X 1 - X 0 * X 1 ^ 2 : MvPolynomial (Fin 2) (ZMod 2)) = 0) ∧
      polynomialGraph (ZMod 2) 2 3 (X 0 ^ 2 * X 1 - X 0 * X 1 ^ 2) =
        Polynomial.X ^ 5 + Polynomial.X ^ 7 ∧
      polynomialGraph (ZMod 2) 2 3 (X 0 ^ 2 * X 1 - X 0 * X 1 ^ 2) ≠ 0 := by
  have hlin {R : Type} [CommRing R] (a b : R) (hab : a ^ 2 * b = a * b ^ 2) :
      MvPolynomial.eval₂Hom Polynomial.C
        ![Polynomial.C a * Polynomial.X, Polynomial.C b * Polynomial.X]
        (X 0 ^ 2 * X 1 - X 0 * X 1 ^ 2 : MvPolynomial (Fin 2) R) = 0 := by
    rw [map_sub]
    simp only [map_mul, map_pow, eval₂Hom_X', Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    calc (Polynomial.C a * Polynomial.X) ^ 2 * (Polynomial.C b * Polynomial.X) -
          Polynomial.C a * Polynomial.X * (Polynomial.C b * Polynomial.X) ^ 2
        = (Polynomial.C a ^ 2 * Polynomial.C b - Polynomial.C a * Polynomial.C b ^ 2) *
            Polynomial.X ^ 3 := by ring
      _ = Polynomial.C (a ^ 2 * b - a * b ^ 2) * Polynomial.X ^ 3 := by
          simp [← map_pow, ← map_mul, ← map_sub]
      _ = 0 := by simp [hab]
  have hgraph {R : Type} [CommRing R] :
      polynomialGraph R 2 3 (X 0 ^ 2 * X 1 - X 0 * X 1 ^ 2) =
        (Polynomial.X : Polynomial R) ^ 5 - Polynomial.X ^ 7 := by
    rw [map_sub]
    simp only [map_mul, map_pow, polynomialGraph_X, Fin.isValue, Fin.val_zero, Fin.val_one,
      pow_zero, pow_one]
    ring
  have hsub :
      polynomialGraph (ZMod 2) 2 3 (X 0 ^ 2 * X 1 - X 0 * X 1 ^ 2) =
        Polynomial.X ^ 5 + Polynomial.X ^ 7 := by
    rw [hgraph, CharTwo.sub_eq_add]
  refine ⟨fun a b ↦ hlin a b (by revert a b; decide), hsub, ?_⟩
  rw [hsub]
  intro h0
  have h5 := congrArg (·.coeff 5) h0
  simp [Polynomial.coeff_X_pow] at h5

/-- The strict exponent bound `< B` in `polynomialGraph_coeff` is sharp: for `h = X 1 - X 0 ^ 2`
over `ℤ`, `B = 2` annihilates `h`, whereas `B = 3` maps `h` to `X ^ 3 - X ^ 2 ≠ 0`. -/
example :
    polynomialGraph ℤ 2 2 (X 1 - X 0 ^ 2) = 0 ∧
      polynomialGraph ℤ 2 3 (X 1 - X 0 ^ 2) = Polynomial.X ^ 3 - Polynomial.X ^ 2 :=
  ⟨polynomialGraph_X_sub_X_pow (by decide) 2, by simp⟩

/-- The bound `∀ i, e i < B` on the query vector `e` in `polynomialGraph_coeff` cannot be dropped:
for `h = X 1` over `ℤ` and `B = 2`, the vector `e = single 0 2` outside the box has weight `2`,
and `(polynomialGraph ℤ 2 2 h).coeff 2 = 1` whereas `h.coeff e = 0`. -/
example :
    let h : MvPolynomial (Fin 2) ℤ := X 1
    let e : Fin 2 →₀ ℕ := Finsupp.single 0 2
    (polynomialGraph ℤ 2 2 h).coeff (Finsupp.weight (fun i : Fin 2 ↦ 2 ^ (i : ℕ)) e) = 1 ∧
      h.coeff e = 0 := by
  refine ⟨?_, ?_⟩
  · simp [Finsupp.weight_single]
  · rw [MvPolynomial.coeff_X]
    exact ite_eq_right_iff.mpr fun he ↦ by
      have := DFunLike.congr_fun he 0
      simp at this

/-- The bound `1 ≤ B` in `eval_zero_polynomialGraph` cannot be dropped: at `m = 2, B = 0` over
`ℤ`, `X 1` maps to `1`, whose value at `0` is `1 ≠ 0`. -/
example :
    (polynomialGraph ℤ 2 0 (X 1)).eval 0 = 1 ∧
      MvPolynomial.eval 0 (X 1 : MvPolynomial (Fin 2) ℤ) = 0 := by
  simp

end CommRing

end TauCeti

end
