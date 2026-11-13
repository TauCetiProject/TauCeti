/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import TauCeti.RingTheory.MvPolynomial.MultiHomogeneous

/-!
# Dehomogenization of two-coordinate blocks

When each block `h : κ` carries two coordinates `(h, 0)` and `(h, 1)`, setting every homogenizing
coordinate `X (h, 0)` to `1` and keeping `X (h, 1)` as `X h` defines the algebra map
`MvPolynomial.blockDehomogenize : MvPolynomial (κ × Fin 2) R →ₐ[R] MvPolynomial κ R`, compatible
with evaluation (`MvPolynomial.aeval_blockDehomogenize`, `MvPolynomial.eval_blockDehomogenize`),
coefficient maps (`MvPolynomial.map_blockDehomogenize`), and coordinate-`1` inclusion
(`MvPolynomial.blockDehomogenize_rename_one`). On a single block it agrees with
`TauCeti.dehomogenize 0` (`MvPolynomial.blockDehomogenize_fin_one`), and after identifying `κ ⊕ κ`
with `κ × Fin 2` it is the evaluation `X (.inl h) ↦ 1, X (.inr h) ↦ X h`
(`MvPolynomial.blockDehomogenize_rename_sumElim`) inverse to `MvPolynomial.blockHomogenize id e` on
multihomogeneous polynomials of multidegree `e`.

For any polynomial `P`, every exponent in `(blockDehomogenize P).support` is the coordinate-`1`
restriction of an exponent in `P.support`
(`MvPolynomial.exists_mem_support_of_mem_support_blockDehomogenize`). When `P` is multihomogeneous
of any multidegree `e : κ → ℕ`, the homogenizing exponent `n (h, 0) = e h - n (h, 1)` is determined
by the affine exponent `n (h, 1)`, so `blockDehomogenize` preserves coefficients at multidegree-`e`
exponents (`MvPolynomial.IsMultiHomogeneous.coeff_blockDehomogenize`), is injective on
multihomogeneous polynomials of fixed multidegree (`MvPolynomial.blockDehomogenize_injOn`),
preserves the set of nonzero coefficients
(`MvPolynomial.IsMultiHomogeneous.exists_coeff_eq_of_mem_support_blockDehomogenize`,
`MvPolynomial.IsMultiHomogeneous.exists_coeff_blockDehomogenize_eq_of_mem_support`) and nonvanishing
(`MvPolynomial.IsMultiHomogeneous.blockDehomogenize_eq_zero`), and bounds the partial degrees by `e`
(`MvPolynomial.IsMultiHomogeneous.degreeOf_blockDehomogenize_le`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), proof of Lemma 7.5.19.
* Ralf Stephan, `DiophantineApproximation/GeneralizedRothLemma.lean` in `rwst/Subspace-Theorems`,
  commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

namespace MvPolynomial

open Finset

variable {R κ : Type*} [CommSemiring R]

/-- Setting the homogenizing variable `X (h, 0)` of each two-variable block `h` to `1` and sending
the affine variable `X (h, 1)` to `X h`. -/
noncomputable def blockDehomogenize : MvPolynomial (κ × Fin 2) R →ₐ[R] MvPolynomial κ R :=
  aeval fun p ↦ ![1, X p.1] p.2

/-- Defining evaluation formula for `blockDehomogenize`. -/
theorem blockDehomogenize_def :
    blockDehomogenize (R := R) (κ := κ) = aeval fun p ↦ ![1, X p.1] p.2 :=
  (rfl)

@[simp]
theorem blockDehomogenize_X_zero (h : κ) :
    blockDehomogenize (X (h, 0) : MvPolynomial (κ × Fin 2) R) = 1 := by
  simp [blockDehomogenize_def]

@[simp]
theorem blockDehomogenize_X_one (h : κ) :
    blockDehomogenize (X (h, 1) : MvPolynomial (κ × Fin 2) R) = X h := by
  simp [blockDehomogenize_def]

/-- Evaluating `blockDehomogenize P` at `a : κ → S` evaluates `P` with each homogenizing coordinate
`(h, 0)` set to `1` and each affine coordinate `(h, 1)` set to `a h`. -/
@[simp]
theorem aeval_blockDehomogenize {S : Type*} [CommSemiring S] [Algebra R S] (a : κ → S)
    (P : MvPolynomial (κ × Fin 2) R) :
    aeval a (blockDehomogenize P) = aeval (fun p ↦ ![1, a p.1] p.2) P := by
  suffices (aeval a).comp (blockDehomogenize (R := R)) = aeval (fun p ↦ ![1, a p.1] p.2) from
    AlgHom.congr_fun this P
  ext ⟨h, i⟩ : 1
  fin_cases i <;> simp

/-- Pointwise evaluation of `blockDehomogenize P` at `a : κ → R` evaluates `P` at
`p ↦ ![1, a p.1] p.2`. -/
@[simp]
theorem eval_blockDehomogenize (a : κ → R) (P : MvPolynomial (κ × Fin 2) R) :
    eval a (blockDehomogenize P) = eval (fun p ↦ ![1, a p.1] p.2) P := by
  simpa only [aeval_eq_eval] using aeval_blockDehomogenize a P

/-- Changing coefficients along a ring homomorphism commutes with `blockDehomogenize`. -/
@[simp]
theorem map_blockDehomogenize {S : Type*} [CommSemiring S] (f : R →+* S)
    (P : MvPolynomial (κ × Fin 2) R) :
    map f (blockDehomogenize P) = blockDehomogenize (map f P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp =>
    rcases q with ⟨h, i⟩
    fin_cases i <;> simp [hp]

/-- Embedding `MvPolynomial κ R` into the coordinate-`1` variables and applying `blockDehomogenize`
is the identity. -/
@[simp]
theorem blockDehomogenize_rename_one (F : MvPolynomial κ R) :
    blockDehomogenize (rename (·, (1 : Fin 2)) F) = F := by
  suffices blockDehomogenize.comp (rename (R := R) (·, (1 : Fin 2))) =
      AlgHom.id R (MvPolynomial κ R) from AlgHom.congr_fun this F
  ext h : 1
  simp

/-- On `κ ⊕ κ`, renaming `.inl h ↦ (h, 0)` and `.inr h ↦ (h, 1)` and applying `blockDehomogenize`
is the evaluation `Sum.elim (fun _ ↦ 1) X` used in `MvPolynomial.blockHomogenize`. -/
theorem blockDehomogenize_rename_sumElim (F : MvPolynomial (κ ⊕ κ) R) :
    blockDehomogenize (rename (Sum.elim (·, 0) (·, 1)) F) = aeval (Sum.elim (fun _ ↦ 1) X) F := by
  suffices blockDehomogenize.comp (rename (R := R) (Sum.elim (·, 0) (·, 1))) =
      aeval (Sum.elim (fun _ ↦ 1) X) from AlgHom.congr_fun this F
  ext (h | h) : 1 <;> simp

/-- On a single two-variable block `Fin 1 × Fin 2`, `blockDehomogenize` agrees with
`TauCeti.dehomogenize 0` after dropping the unique block index. -/
theorem blockDehomogenize_fin_one (P : MvPolynomial (Fin 1 × Fin 2) R) :
    blockDehomogenize P = TauCeti.dehomogenize 0 (rename Prod.snd P) := by
  suffices blockDehomogenize (R := R) (κ := Fin 1) =
      (TauCeti.dehomogenize 0).comp (rename Prod.snd) from AlgHom.congr_fun this P
  ext ⟨h, i⟩ : 1
  fin_cases h
  fin_cases i <;> simp

/-- `blockDehomogenize` drops the coordinate-`0` exponents of a monomial and keeps its
coordinate-`1` exponents. -/
@[simp]
theorem blockDehomogenize_monomial (n : κ × Fin 2 →₀ ℕ) (c : R) :
    blockDehomogenize (monomial n c) =
      monomial (n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn) c := by
  set n₀ := n.comapDomain (·, 0) (Prod.mk_left_injective 0).injOn
  set n₁ := n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn
  have hn : n = n₀.mapDomain (·, 0) + n₁.mapDomain (·, 1) := by
    ext ⟨h, i⟩
    fin_cases i
    · rw [Fin.zero_eta, Finsupp.add_apply,
        Finsupp.mapDomain_apply_of_injective (Prod.mk_left_injective 0) n₀ h,
        Finsupp.mapDomain_of_notMem_range n₁ (h, 0) (by simp), add_zero (n₀ h)]
      rfl
    · rw [Fin.mk_one, Finsupp.add_apply,
        Finsupp.mapDomain_of_notMem_range n₀ (h, 1) (by simp),
        Finsupp.mapDomain_apply_of_injective (Prod.mk_left_injective 1) n₁ h, zero_add (n₁ h)]
      rfl
  have h0 : blockDehomogenize (rename (·, 0) (monomial n₀ (1 : R))) = 1 := by
    simp [blockDehomogenize_def, aeval_rename, Function.comp_def, aeval_monomial]
  conv_lhs => rw [hn, ← one_mul c]
  rw [← monomial_mul_monomial, ← rename_monomial, ← rename_monomial,
    map_mul, h0, one_mul, blockDehomogenize_rename_one]

/-- Every exponent in the support of `blockDehomogenize P` agrees with the coordinate-`1` exponents
of some exponent in the support of `P`. -/
theorem exists_mem_support_of_mem_support_blockDehomogenize {P : MvPolynomial (κ × Fin 2) R}
    {m : κ →₀ ℕ} (hm : m ∈ (blockDehomogenize P).support) :
    ∃ n ∈ P.support, ∀ h, m h = n (h, 1) := by
  classical
  by_contra! hnone
  refine mem_support_iff.mp hm ?_
  conv_lhs => rw [P.as_sum]
  rw [map_sum, coeff_sum]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  rw [blockDehomogenize_monomial, coeff_monomial, ite_eq_right]
  rintro rfl
  obtain ⟨h, hh⟩ := hnone n hn
  exact hh rfl

section MultiHomogeneous

variable [DecidableEq κ] {e : κ → ℕ} {P : MvPolynomial (κ × Fin 2) R}

private theorem add_eq_of_mem_support (hP : IsMultiHomogeneous e P)
    {n : κ × Fin 2 →₀ ℕ} (hn : n ∈ P.support) (h : κ) :
    n (h, 0) + n (h, 1) = e h := by
  have := isMultiHomogeneous_iff.mp hP n (mem_support_iff.mp hn) h
  rwa [Fin.sum_univ_two] at this

/-- For `P` multihomogeneous of multidegree `e` and any exponent `n` of multidegree `e`, the
coefficient of `P` at `n` equals the coefficient of `blockDehomogenize P` at the coordinate-`1`
restriction of `n`. -/
theorem IsMultiHomogeneous.coeff_blockDehomogenize (hP : IsMultiHomogeneous e P)
    {n : κ × Fin 2 →₀ ℕ} (hn : ∀ h, n (h, 0) + n (h, 1) = e h) :
    (blockDehomogenize P).coeff (n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn) =
      P.coeff n := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum, coeff_sum]
  simp_rw [blockDehomogenize_monomial, coeff_monomial]
  rw [Finset.sum_eq_single n]
  · simp
  · intro n' hn' hne
    refine ite_eq_right fun h ↦ hne ?_
    ext ⟨h', i⟩
    have h1 : n' (h', 1) = n (h', 1) := by simpa using DFunLike.congr_fun h h'
    have hs' := add_eq_of_mem_support hP hn' h'
    have hs := hn h'
    fin_cases i
    · dsimp
      omega
    · exact h1
  · intro hnot
    simp [notMem_support_iff.mp hnot]

/-- `blockDehomogenize` is injective on multihomogeneous polynomials of any fixed multidegree `e`:
a multihomogeneous polynomial in two-coordinate blocks is determined by its multidegree and its
dehomogenization. -/
theorem blockDehomogenize_injOn (e : κ → ℕ) :
    Set.InjOn (blockDehomogenize (R := R) (κ := κ)) {P | IsMultiHomogeneous e P} := by
  intro P hP Q hQ h
  ext n
  by_cases hn : ∀ h', n (h', 0) + n (h', 1) = e h'
  · rw [← IsMultiHomogeneous.coeff_blockDehomogenize hP hn,
      ← IsMultiHomogeneous.coeff_blockDehomogenize hQ hn, h]
  · push Not at hn
    obtain ⟨h', hh'⟩ := hn
    have hsum : ∑ i, n (h', i) ≠ e h' := by rwa [Fin.sum_univ_two]
    rw [IsMultiHomogeneous.coeff_eq_zero hP hsum, IsMultiHomogeneous.coeff_eq_zero hQ hsum]

/-- Every nonzero coefficient of `blockDehomogenize P` is a coefficient of `P`, when `P` is
multihomogeneous. -/
theorem IsMultiHomogeneous.exists_coeff_eq_of_mem_support_blockDehomogenize
    (hP : IsMultiHomogeneous e P) {m : κ →₀ ℕ} (hm : m ∈ (blockDehomogenize P).support) :
    ∃ n ∈ P.support, (blockDehomogenize P).coeff m = P.coeff n := by
  obtain ⟨n, hn, hmn⟩ := exists_mem_support_of_mem_support_blockDehomogenize hm
  have hm_eq : m = n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn := by
    ext h
    simpa using hmn h
  exact ⟨n, hn, hm_eq ▸ hP.coeff_blockDehomogenize (add_eq_of_mem_support hP hn)⟩

/-- Every nonzero coefficient of a multihomogeneous polynomial `P` occurs as a nonzero coefficient
of `blockDehomogenize P` at the corresponding affine exponent. -/
theorem IsMultiHomogeneous.exists_coeff_blockDehomogenize_eq_of_mem_support
    (hP : IsMultiHomogeneous e P) {n : κ × Fin 2 →₀ ℕ} (hn : n ∈ P.support) :
    ∃ m ∈ (blockDehomogenize P).support,
      (∀ h, m h = n (h, 1)) ∧ (blockDehomogenize P).coeff m = P.coeff n := by
  have hc := hP.coeff_blockDehomogenize (add_eq_of_mem_support hP hn)
  exact ⟨n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn,
    mem_support_iff.mpr (hc ▸ mem_support_iff.mp hn), fun _ ↦ rfl, hc⟩

/-- Dehomogenization of a multihomogeneous polynomial vanishes if and only if the polynomial itself
vanishes. -/
-- Cannot be `@[simp]` because `e` cannot be inferred by `simp` (`simpNF`).
theorem IsMultiHomogeneous.blockDehomogenize_eq_zero (hP : IsMultiHomogeneous e P) :
    blockDehomogenize P = 0 ↔ P = 0 :=
  ⟨fun h0 ↦ blockDehomogenize_injOn e hP (isMultiHomogeneous_zero e) (h0.trans (map_zero _).symm),
    fun h0 ↦ by simp [h0]⟩

grind_pattern IsMultiHomogeneous.blockDehomogenize_eq_zero =>
  IsMultiHomogeneous e P, blockDehomogenize P

/-- Dehomogenizing a multihomogeneous polynomial of multidegree `e` gives a polynomial of degree at
most `e h` in each variable `h`. -/
theorem IsMultiHomogeneous.degreeOf_blockDehomogenize_le (hP : IsMultiHomogeneous e P) (h : κ) :
    (blockDehomogenize P).degreeOf h ≤ e h := by
  rw [degreeOf_le_iff]
  intro m hm
  obtain ⟨n, hn, hmn⟩ := exists_mem_support_of_mem_support_blockDehomogenize hm
  rw [hmn h, ← add_eq_of_mem_support hP hn h]
  exact Nat.le_add_left _ _

end MultiHomogeneous

end MvPolynomial

end

namespace MvPolynomial

/-- Multihomogeneity is necessary in `IsMultiHomogeneous.blockDehomogenize_eq_zero`: the
inhomogeneous polynomial `X (0, 0) - 1` is nonzero, whereas its dehomogenization vanishes. -/
example :
    let P : MvPolynomial (Fin 1 × Fin 2) ℤ := X (0, 0) - 1
    P ≠ 0 ∧ blockDehomogenize P = 0 := by
  intro P
  refine ⟨fun h ↦ ?_, by simp [P]⟩
  have := congrArg (eval 0) h
  simp [P] at this

end MvPolynomial
