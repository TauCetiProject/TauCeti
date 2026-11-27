/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Block.Homogenize
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import TauCeti.RingTheory.MvPolynomial.MultiHomogeneous
public import TauCeti.RingTheory.MvPolynomial.RestrictSupport
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

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

For finitely many blocks the two directions are inverse linear isomorphisms: block homogenization,
written in the coordinates `κ × Fin 2`, is multihomogeneous of multidegree `e`
(`MvPolynomial.isMultiHomogeneous_rename_blockHomogenize`) and dehomogenizes back to every
polynomial of partial degrees at most `e`
(`MvPolynomial.blockDehomogenize_rename_blockHomogenize`). Together with injectivity this gives
`MvPolynomial.blockDehomogenizeEquiv e`, from the multihomogeneous polynomials of multidegree `e`
onto `restrictSupport R {m | ∀ h, m h ≤ e h}`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), proof of Lemma 7.5.19.
* Ralf Stephan, `DiophantineApproximation/FormIndex.lean`,
  `DiophantineApproximation/FormSpecialization.lean`, and
  `DiophantineApproximation/GeneralizedRothLemma.lean` in `rwst/Subspace-Theorems`, commit
  `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
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
  simp only [blockDehomogenize_def, aeval_def, algebraMap_eq]
  rw [map_eval₂]
  congr 1
  ext ⟨h, i⟩
  fin_cases i <;> simp

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
    · simpa [n₀, Finsupp.mapDomain_of_notMem_range] using
        (Finsupp.mapDomain_apply_of_injective (Prod.mk_left_injective 0) n₀ h).symm
    · simpa [n₁, Finsupp.mapDomain_of_notMem_range] using
        (Finsupp.mapDomain_apply_of_injective (Prod.mk_left_injective 1) n₁ h).symm
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
  exact hh (Finsupp.comapDomain_apply _ _ _ _)

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
    mem_support_iff.mpr (hc ▸ mem_support_iff.mp hn),
    fun _ ↦ Finsupp.comapDomain_apply _ _ _ _, hc⟩

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

section Equiv

variable [Fintype κ]

variable (e) in
/-- Block homogenization, written in the coordinates `κ × Fin 2`, is multihomogeneous of
multidegree `e`. -/
theorem isMultiHomogeneous_rename_blockHomogenize (f : MvPolynomial κ R) :
    IsMultiHomogeneous e (rename (Sum.elim (·, (0 : Fin 2)) (·, 1)) (blockHomogenize id e f)) := by
  refine isMultiHomogeneous_iff_forall_isWeightedHomogeneous.2 fun h ↦ ?_
  rw [rename_eq_aeval]
  refine (isWeightedHomogeneous_blockHomogenize id e f h).aeval fun v ↦ ?_
  cases v <;> exact isWeightedHomogeneous_X R _ _

omit [DecidableEq κ] in
/-- Dehomogenizing the block homogenization of a polynomial of partial degrees at most `e`
recovers it. -/
theorem blockDehomogenize_rename_blockHomogenize {f : MvPolynomial κ R}
    (hf : f ∈ restrictSupport R {m : κ →₀ ℕ | ∀ h, m h ≤ e h}) :
    blockDehomogenize (rename (Sum.elim (·, (0 : Fin 2)) (·, 1)) (blockHomogenize id e f)) = f := by
  rw [blockDehomogenize_rename_sumElim]
  refine aeval_blockHomogenize_one_X id e fun m hm h ↦ ?_
  rw [Finsupp.mapDomain_id]
  exact (mem_restrictSupport_iff R).1 hf hm h

variable (R e) in
/-- **Dehomogenization of two-coordinate blocks as a linear isomorphism.** The polynomials in the
variables `X (h, 0)`, `X (h, 1)` that are multihomogeneous of multidegree `e` correspond to the
polynomials in the variables `X h` of partial degree at most `e h` in each `X h`. The map sets
every homogenizing coordinate `X (h, 0)` to `1`, and its inverse is block homogenization. -/
noncomputable def blockDehomogenizeEquiv :
    multiHomogeneousSubmodule R (Fin 2) e ≃ₗ[R]
      restrictSupport R {m : κ →₀ ℕ | ∀ h, m h ≤ e h} where
  toFun P := ⟨blockDehomogenize (P : MvPolynomial (κ × Fin 2) R),
    mem_restrictSupport_iff_degreeOf_le.2
      (mem_multiHomogeneousSubmodule.1 P.property).degreeOf_blockDehomogenize_le⟩
  map_add' P Q := Subtype.ext (map_add _ _ _)
  map_smul' c P := Subtype.ext (map_smul _ _ _)
  invFun f :=
    ⟨rename (Sum.elim (·, (0 : Fin 2)) (·, 1)) (blockHomogenize id e (f : MvPolynomial κ R)),
    mem_multiHomogeneousSubmodule.2 (isMultiHomogeneous_rename_blockHomogenize e _)⟩
  left_inv P := by
    have hP : IsMultiHomogeneous e (P : MvPolynomial (κ × Fin 2) R) :=
      mem_multiHomogeneousSubmodule.1 P.property
    refine Subtype.ext (blockDehomogenize_injOn e
      (isMultiHomogeneous_rename_blockHomogenize e _) hP ?_)
    exact blockDehomogenize_rename_blockHomogenize
      (mem_restrictSupport_iff_degreeOf_le.2 hP.degreeOf_blockDehomogenize_le)
  right_inv f := Subtype.ext (blockDehomogenize_rename_blockHomogenize f.property)

@[simp]
theorem coe_blockDehomogenizeEquiv_apply (P : multiHomogeneousSubmodule R (Fin 2) e) :
    (blockDehomogenizeEquiv R e P : MvPolynomial κ R) = blockDehomogenize (P : MvPolynomial _ R) :=
  (rfl)

@[simp]
theorem coe_blockDehomogenizeEquiv_symm_apply
    (f : restrictSupport R {m : κ →₀ ℕ | ∀ h, m h ≤ e h}) :
    ((blockDehomogenizeEquiv R e).symm f : MvPolynomial (κ × Fin 2) R) =
      rename (Sum.elim (·, (0 : Fin 2)) (·, 1)) (blockHomogenize id e (f : MvPolynomial κ R)) :=
  (rfl)

/-- The block homogenization of the monomial `X^m`, `m ≤ e`, is
`∏ i, X (i, 1) ^ m i * X (i, 0) ^ (e i - m i)`. -/
theorem coe_blockDehomogenizeEquiv_symm_monomial {m : κ →₀ ℕ} (hm : ∀ h, m h ≤ e h) :
    (((blockDehomogenizeEquiv R e).symm ⟨monomial m 1, by simp [hm]⟩ :
        multiHomogeneousSubmodule R (Fin 2) e) : MvPolynomial (κ × Fin 2) R) =
      ∏ i, X (i, (1 : Fin 2)) ^ m i * X (i, 0) ^ (e i - m i) := by
  have h : (blockDehomogenizeEquiv R e).symm ⟨monomial m 1, by simp [hm]⟩ =
      ⟨_, mem_multiHomogeneousSubmodule.2
        (isMultiHomogeneous_prod_X_pow_mul_X_pow (R := R) hm (1 : Fin 2) 0)⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    simp [monomial_eq, Finsupp.prod_fintype]
  rw [h]

end Equiv

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
