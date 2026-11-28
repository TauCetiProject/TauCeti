/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import TauCeti.Data.Finsupp.MonomialOrder.Colex
public import TauCeti.RepresentationTheory.ClassicalGroups.DualWeylModule.Basic
public import TauCeti.RingTheory.MvPolynomial.HasLeadingTerm
import TauCeti.Algebra.MvPolynomial.Monomial

/-!
# Leading terms of dual Weyl vectors in the last row

Write a polynomial `f` in the `(N + 1) × n` matrix of variables as a polynomial in the variables
`y_s = x_{N,s}` of its last row, with coefficients the polynomials in the first `N` rows
(`TauCeti.DualWeylModule.lastRowEquiv`), and order the exponents of `y` colexicographically, so
that `y_{n-1}` is the largest variable (`TauCeti.MonomialOrder.colex`). For a nonzero `f` in the
dual Weyl module `∇(d)` of column degrees `d`, with leading exponent `γ` and leading coefficient
`G` in the last row, this file proves:

* `G` lies in the dual Weyl module `∇(d - γ)` of the first `N` rows
  (`TauCeti.DualWeylModule.leadingCoeff_lastRowEquiv_mem`): in the expansion, the column
  operation `x ↦ x·(1 + T·e_{st})`, `s < t`, replaces `y_t` by `y_t + T·y_s`, which only lowers
  exponents, so it fixes the leading coefficient;
* `γ i + d (i + 1) ≤ d i` for every column `i`
  (`TauCeti.DualWeylModule.degree_lastRowEquiv_add_le`), so that `d - γ` interlaces `d`. This
  rests on the lowering bound `TauCeti.DualWeylModule.coeff_columnOperation_eq_zero`: the
  operation adding `T` times the column `j` to an earlier column `i` sends `f` to a polynomial of
  degree at most `d i - d j` in `T`.
  Indeed, scaling the column `j` by `T` and subtracting the column `i` (which changes nothing,
  by invariance and homogeneity, but the factor `T ^ d j`) leaves `T` in the column `i` alone,
  where `f` has degree `d i`. Comparing the coefficient of `y ^ δ * T ^ γ i` with `δ` obtained
  from `γ` by moving `γ i` from `y_i` to `y_{i+1}` then shows `G = 0` if `γ i + d (i + 1) > d i`.

Leading terms are tracked with `MonomialOrder.HasLeadingTerm` for the colexicographic order.

## References

The argument by leading terms in one row is adapted from grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC), file
`src/Lib/GLn/SchurModule/MinorBasis.lean`: `New.GL.rowExpansion`,
`New.GL.HasLeadingTerm.leadingCoeff_mem_nabla` and `New.GL.degree_rowExpansion_mem_interlacing`.
grh-lean states these for semi-invariants of a Borel subgroup; here they are proved from the column
operations and the column degrees directly, and the interlacing bound goes through the lowering
bound above. The standard basis theorem is due to De Concini, Eisenbud and Procesi, *Young
diagrams and determinantal varieties*, Invent. Math. **56** (1980), and to Akin, Buchsbaum and
Weyman, *Schur functors and Schur complexes*, Adv. Math. **44** (1982), II.2.16.
-/

public section

namespace TauCeti

open MvPolynomial Finset

namespace DualWeylModule

variable {R : Type*} {N n : ℕ}

section CommSemiring

variable [CommSemiring R]

/-! ### Expanding in the last row -/

variable (R N n) in
/-- The polynomials in the `(N + 1) × n` matrix of variables, written as polynomials in the
variables `y_s = x_{N,s}` of the last row with coefficients the polynomials in the first `N`
rows. -/
noncomputable def lastRowEquiv :
    MvPolynomial (Fin (N + 1) × Fin n) R ≃ₐ[R]
      MvPolynomial (Fin n) (MvPolynomial (Fin N × Fin n) R) :=
  (renameEquiv R ((finSuccEquivLast.prodCongr (Equiv.refl _)).trans optionProdEquiv)).trans
    (sumAlgEquiv R (Fin n) (Fin N × Fin n))

@[simp]
theorem lastRowEquiv_X_last (s : Fin n) :
    lastRowEquiv R N n (X (Fin.last N, s)) = X s := by
  simp [lastRowEquiv, optionProdEquiv]

@[simp]
theorem lastRowEquiv_X_castSucc (a : Fin N) (s : Fin n) :
    lastRowEquiv R N n (X (a.castSucc, s)) = C (X (a, s)) := by
  simp [lastRowEquiv, optionProdEquiv]

@[simp]
theorem lastRowEquiv_C (r : R) : lastRowEquiv R N n (C r) = C (C r) := by
  simp [lastRowEquiv]

/-- The exponent of the `(N + 1) × n` matrix of variables with last row `γ` and first `N` rows
`m`. -/
noncomputable def joinRows (γ : Fin n →₀ ℕ) (m : Fin N × Fin n →₀ ℕ) : Fin (N + 1) × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => Fin.lastCases (γ p.2) (fun a => m (a, p.2)) p.1

@[simp]
theorem joinRows_last (γ : Fin n →₀ ℕ) (m : Fin N × Fin n →₀ ℕ) (s : Fin n) :
    joinRows γ m (Fin.last N, s) = γ s := by
  simp [joinRows]

@[simp]
theorem joinRows_castSucc (γ : Fin n →₀ ℕ) (m : Fin N × Fin n →₀ ℕ) (a : Fin N) (s : Fin n) :
    joinRows γ m (a.castSucc, s) = m (a, s) := by
  simp [joinRows]

theorem sum_joinRows (γ : Fin n →₀ ℕ) (m : Fin N × Fin n →₀ ℕ) (s : Fin n) :
    ∑ a, joinRows γ m (a, s) = ∑ a, m (a, s) + γ s := by
  simp [Fin.sum_univ_castSucc]

theorem lastRowEquiv_monomial (M : Fin (N + 1) × Fin n →₀ ℕ) (r : R) :
    lastRowEquiv R N n (monomial M r) =
      monomial (Finsupp.equivFunOnFinite.symm fun s => M (Fin.last N, s))
        (monomial (Finsupp.equivFunOnFinite.symm fun p => M (p.1.castSucc, p.2)) r) := by
  rw [monomial_eq, map_mul, lastRowEquiv_C, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    map_prod, Fintype.prod_prod_type, Fin.prod_univ_castSucc]
  simp only [map_pow, lastRowEquiv_X_castSucc, lastRowEquiv_X_last]
  rw [monomial_eq, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  simp only [Finsupp.coe_equivFunOnFinite_symm, map_mul, map_prod, map_pow]
  ring

/-- The coefficients of the last-row expansion are coefficients of the polynomial. -/
theorem coeff_coeff_lastRowEquiv (f : MvPolynomial (Fin (N + 1) × Fin n) R) (γ : Fin n →₀ ℕ)
    (m : Fin N × Fin n →₀ ℕ) :
    ((lastRowEquiv R N n f).coeff γ).coeff m = f.coeff (joinRows γ m) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial M r =>
    have h_iff : ((Finsupp.equivFunOnFinite.symm fun s => M (Fin.last N, s)) = γ ∧
        (Finsupp.equivFunOnFinite.symm fun p : Fin N × Fin n => M (p.1.castSucc, p.2)) = m) ↔
        M = joinRows γ m := by
      constructor
      · rintro ⟨h₁, h₂⟩
        ext ⟨a, s⟩
        induction a using Fin.lastCases with
        | last => simpa using DFunLike.congr_fun h₁ s
        | cast a => simpa using DFunLike.congr_fun h₂ (a, s)
      · rintro rfl
        constructor <;> ext <;> simp
    rw [lastRowEquiv_monomial, coeff_monomial, coeff_monomial]
    split_ifs <;> simp_all
  | add p q hp hq => simp [hp, hq]


/-! ### Degrees in `T` -/

section Lowering

variable {S : Type*} [CommSemiring S] [Algebra R S]

/-- If every monomial of `f` has degree `d i` in the column `i`, and the entries of the matrix `M`
over `S[T]` have degree at most `1` in the column `i` and `0` elsewhere, then `f(M)` has degree
at most `d i` in `T`. -/
theorem natDegree_aeval_le {f : MvPolynomial (Fin N × Fin n) R} {d : Fin n → ℕ} {i : Fin n}
    (hf : ∀ m ∈ f.support, ∑ a, m (a, i) = d i) (M : Fin N × Fin n → Polynomial S)
    (hM : ∀ p, (M p).natDegree ≤ if p.2 = i then 1 else 0) :
    (aeval M f).natDegree ≤ d i := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  rw [aeval_monomial, Polynomial.algebraMap_apply]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← hf m hm]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ p, (M p ^ m p).natDegree ≤ ∑ p : Fin N × Fin n, m p * if p.2 = i then 1 else 0 :=
        Finset.sum_le_sum fun p _ => Polynomial.natDegree_pow_le_of_le _ (hM p)
    _ = ∑ a, m (a, i) := by
        rw [Fintype.sum_prod_type]
        simp

end Lowering

/-! ### Column operations on the last-row expansion -/

section Expansion

open scoped _root_.MonomialOrder

open TauCeti.MonomialOrder (colex)

/-- **Column operations in the last-row expansion.** Apply the column operation
`x ↦ x·(1 + T·e_{st})` to `f`, then expand in the last row and substitute `z` for its variables.
The result is obtained from the last-row expansion of `f` by applying the same column operation
to the coefficients and substituting, for the variable `y_j` of the last row, `z j` plus `T` times
`z s` if `j = t`. -/
theorem eval₂_columnOperation_lastRowEquiv (s t : Fin n)
    (z : Fin n → MvPolynomial (Fin n) (MvPolynomial (Fin N × Fin n) R))
    (f : MvPolynomial (Fin (N + 1) × Fin n) R) :
    Polynomial.eval₂ ((MvPolynomial.map Polynomial.C).comp
        ((aeval z).toRingHom.comp (lastRowEquiv R N n).toRingHom)) (C Polynomial.X)
        (columnOperation R s t f) =
      eval₂ (C.comp (columnOperation R s t).toRingHom)
        (fun j => MvPolynomial.map Polynomial.C (z j) +
          if j = t then C Polynomial.X * MvPolynomial.map Polynomial.C (z s) else 0)
        (lastRowEquiv R N n f) := by
  let φ := (Polynomial.eval₂RingHom ((MvPolynomial.map Polynomial.C).comp
    ((aeval z).toRingHom.comp (lastRowEquiv R N n).toRingHom)) (C Polynomial.X)).comp
      (columnOperation R s t).toRingHom
  let ψ := (eval₂Hom (C.comp (columnOperation R s t).toRingHom)
    (fun j => MvPolynomial.map Polynomial.C (z j) +
      if j = t then C Polynomial.X * MvPolynomial.map Polynomial.C (z s) else 0)).comp
        (lastRowEquiv R N n).toRingHom
  have h_eq : φ = ψ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun ⟨a, j⟩ => ?_
    · simp [φ, ψ, Polynomial.algebraMap_apply]
    · induction a using Fin.lastCases with
      | last =>
        by_cases hj : j = t
        · simp [φ, ψ, hj]
          ring
        · simp [φ, ψ, hj]
      | cast a =>
        by_cases hj : j = t <;> simp [φ, ψ, hj, Polynomial.eval₂_X]
  exact congr($h_eq f)

variable {f : MvPolynomial (Fin (N + 1) × Fin n) R}

/-- **The leading coefficient in the last row is invariant.** If the column operation
`x ↦ x·(1 + T·e_{st})`, `s < t`, fixes `f`, it fixes the leading coefficient of the expansion of
`f` in the last row, for the colexicographic order: in the expansion, the operation replaces the
variable `y_t` of the last row by `y_t + T·y_s`, which only lowers exponents. -/
theorem columnOperation_leadingCoeff_lastRowEquiv {s t : Fin n} (hst : s < t)
    (hf : columnOperation R s t f = Polynomial.C f) :
    columnOperation R s t (colex.leadingCoeff (lastRowEquiv R N n f)) =
      Polynomial.C (colex.leadingCoeff (lastRowEquiv R N n f)) := by
  set E := lastRowEquiv R N n f
  have h := eval₂_columnOperation_lastRowEquiv s t X f
  rw [hf, Polynomial.eval₂_C, aeval_X_left, eval₂_eq'] at h
  have h' : MvPolynomial.map Polynomial.C E = ∑ d ∈ E.support,
      C (columnOperation R s t (E.coeff d)) *
        ∏ j, (X j + if j = t then C Polynomial.X * X s else 0) ^ d j := by
    simp only [map_X, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AlgHom.id_apply] at h
    exact h
  -- The variable `y_j` is sent to `u j`, whose leading term is `y_j`.
  have hX (j : Fin n) : colex.HasLeadingTerm (X j : MvPolynomial (Fin n)
      (Polynomial (MvPolynomial (Fin N × Fin n) R))) (Finsupp.single j 1) 1 := by
    have := colex.hasLeadingTerm_monomial (A := Polynomial (MvPolynomial (Fin N × Fin n) R))
      (Finsupp.single j 1) 1
    rwa [← X_pow_eq_monomial, pow_one] at this
  have hu (j : Fin n) : colex.HasLeadingTerm (X j + if j = t then C Polynomial.X * X s else 0)
      (Finsupp.single j 1) (1 : Polynomial (MvPolynomial (Fin N × Fin n) R)) := by
    by_cases hj : j = t
    · subst hj
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), C_mul_X_eq_monomial]
      refine (hX j).add_of_lt ((colex.degree_monomial_le _).trans_lt ?_)
      exact MonomialOrder.colex_single_lt_iff.mpr hst
    · simpa [hj] using hX j
  have h_lead := MonomialOrder.HasLeadingTerm.sum (m := colex) (s := E.support)
    (F := fun d => C (columnOperation R s t (E.coeff d)) *
      ∏ j, (X j + if j = t then C Polynomial.X * X s else 0) ^ d j)
    (γ := fun d => d) (a := fun d => columnOperation R s t (E.coeff d))
    (fun d => by
      have := (colex.hasLeadingTerm_monomial 0 (columnOperation R s t (E.coeff d))).mul
        (colex.hasLeadingTerm_prod_pow hu d)
      rwa [← C_apply, zero_add, mul_one] at this)
    (colex.degree E) (fun d hd hne => lt_of_le_of_ne (colex.le_degree hd)
      (colex.toSyn.injective.ne hne)) fun hγ => by simp [notMem_support_iff.mp hγ]
  have h_coeff := congrArg (fun p => p.coeff (colex.degree E)) h'
  simp only [coeff_map] at h_coeff
  rw [h_lead.coeff_eq] at h_coeff
  rw [MonomialOrder.leadingCoeff]
  exact h_coeff.symm

variable {d : Fin n → ℕ}

/-- A coefficient of the leading coefficient in the last row is a coefficient of `f`, at the
exponent with last row the leading exponent. -/
private theorem mem_support_of_mem_support_leadingCoeff {m : Fin N × Fin n →₀ ℕ}
    (hm : m ∈ (colex.leadingCoeff (lastRowEquiv R N n f)).support) :
    joinRows (colex.degree (lastRowEquiv R N n f)) m ∈ f.support := by
  rw [mem_support_iff, ← coeff_coeff_lastRowEquiv]
  exact mem_support_iff.mp hm

/-- **The leading exponent in the last row is bounded by the column degrees.** -/
theorem degree_lastRowEquiv_le (hf : f ∈ dualWeylModule R (N + 1) d) (s : Fin n) :
    colex.degree (lastRowEquiv R N n f) s ≤ d s := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  have h_ne : colex.leadingCoeff (lastRowEquiv R N n f) ≠ 0 := by
    rw [Ne, colex.leadingCoeff_eq_zero_iff, EmbeddingLike.map_eq_zero_iff]
    exact hf0
  obtain ⟨m, hm⟩ := support_nonempty.mpr h_ne
  have := sum_apply_eq_of_mem_support hf (mem_support_of_mem_support_leadingCoeff hm) s
  rw [sum_joinRows] at this
  omega

/-- **The leading coefficient in the last row is a dual Weyl vector.** If `f` lies in the dual
Weyl module of column degrees `d` for `N + 1` rows, and `γ` is the leading exponent of its
expansion in the last row for the colexicographic order, then the leading coefficient lies in
the dual Weyl module of column degrees `d - γ` for the first `N` rows. -/
theorem leadingCoeff_lastRowEquiv_mem (hf : f ∈ dualWeylModule R (N + 1) d) :
    colex.leadingCoeff (lastRowEquiv R N n f) ∈
      dualWeylModule R N fun s => d s - colex.degree (lastRowEquiv R N n f) s := by
  refine mem_dualWeylModule.mpr ⟨fun m hm s => ?_, fun s t hst =>
    columnOperation_leadingCoeff_lastRowEquiv hst (columnOperation_eq_C hf hst)⟩
  have := sum_apply_eq_of_mem_support hf (mem_support_of_mem_support_leadingCoeff hm) s
  rw [sum_joinRows] at this
  omega

/-- Moving the exponent of `y_i` to `y_{i+1}`: if two exponents become equal after this move and
the first has at most as much at `i`, then it is the same or colexicographically larger. -/
private theorem colex_lt_of_shift_eq {γ η : Fin n →₀ ℕ} {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (hσ : η.erase i + Finsupp.single j (η i) = γ.erase i + Finsupp.single j (γ i))
    (hle : η i ≤ γ i) (hne : η ≠ γ) : γ ≺[colex] η := by
  classical
  have hij' : i < j := by rw [Fin.lt_def]; omega
  -- `η` agrees with `γ` off the columns `i` and `j`, and `η i + η j = γ i + γ j`.
  have hval (l : Fin n) := DFunLike.congr_fun hσ l
  have h_off (l : Fin n) (hli : l ≠ i) (hlj : l ≠ j) : η l = γ l := by
    simpa [Finsupp.erase_ne hli, Finsupp.single_apply, Ne.symm hlj] using hval l
  have h_j : η j + η i = γ j + γ i := by
    simpa [Finsupp.erase_ne hij'.ne'] using hval j
  rcases hle.lt_or_eq with hlt | heq
  · have h_lt_j : γ j < η j := by omega
    exact MonomialOrder.colex_lt_of_eq_of_lt j (fun l hl => (h_off l
      (by rintro rfl; exact absurd (hij'.trans hl) (lt_irrefl _)) hl.ne').symm) h_lt_j
  · refine absurd (Finsupp.ext fun l => ?_) hne
    by_cases hli : l = i
    · subst hli; exact heq
    by_cases hlj : l = j
    · subst hlj; omega
    exact h_off l hli hlj

end Expansion

end CommSemiring

/-! ### The lowering bound and interlacing -/

section CommRing

open scoped _root_.MonomialOrder

open TauCeti.MonomialOrder (colex)

variable [CommRing R]

/-- **The lowering bound.** Let `f` be a dual Weyl vector of column degrees `d`, and `i < j`.
The operation `x ↦ x·(1 + T·e_{ji})`, adding `T` times the column `j` to the column `i`, sends
`f` to a polynomial in `T` of degree at most `d i - d j`, and to `0` if `d i < d j`: its
coefficient of `T ^ k` vanishes as soon as `d i < k + d j`. -/
theorem coeff_columnOperation_eq_zero {f : MvPolynomial (Fin N × Fin n) R} {d : Fin n → ℕ}
    (hf : f ∈ dualWeylModule R N d) {i j : Fin n} (hij : i < j) {k : ℕ} (hk : d i < k + d j) :
    (columnOperation R j i f).coeff k = 0 := by
  -- With `M` the matrix of the operation, scale the column `j` by `T` and subtract the column
  -- `i`: the column `j` becomes `-x_i`, so `T` only occurs in the column `i`, and
  -- `T ^ d j • (columnOperation R j i f)` has degree at most `d i`.
  let M : Fin N × Fin n → Polynomial (MvPolynomial (Fin N × Fin n) R) := fun p =>
    Polynomial.C (X p) + if p.2 = i then Polynomial.X * Polynomial.C (X (p.1, j)) else 0
  let M₁ := fun p : Fin N × Fin n => (if p.2 = j then Polynomial.X else 1) * M p
  have h_scale : aeval M₁ f = Polynomial.X ^ d j * columnOperation R j i f := by
    rw [columnOperation_def]
    exact aeval_ite_mul_eq_pow_mul_aeval (fun m hm => sum_apply_eq_of_mem_support hf hm j) M _
  have h_add := aeval_add_ite_mul_eq_aeval (columnOperation_eq_C hf hij) M₁ (-1)
  have h_deg := natDegree_aeval_le (i := i) (fun m hm => sum_apply_eq_of_mem_support hf hm i)
    (fun p => M₁ p + if p.2 = j then -1 * M₁ (p.1, i) else 0) fun p => by
      by_cases hpi : p.2 = i
      · have h_eq : M₁ p + (if p.2 = j then -1 * M₁ (p.1, i) else 0) =
            Polynomial.C (X (p.1, j)) * Polynomial.X + Polynomial.C (X p) := by
          simp only [M₁, M, hpi, hij.ne, ite_true, ite_false, one_mul, add_zero]
          ring
        rw [h_eq, ite_eq_left_of_eq_true _ _ (eq_true hpi)]
        exact Polynomial.natDegree_linear_le
      · by_cases hpj : p.2 = j
        · have h_eq : M₁ p + (if p.2 = j then -1 * M₁ (p.1, i) else 0) =
              -Polynomial.C (X (p.1, i) : MvPolynomial (Fin N × Fin n) R) := by
            obtain ⟨a, b⟩ := p
            simp only at hpj
            subst hpj
            simp [M₁, M, hij.ne, hij.ne']
            ring
          rw [h_eq]
          simp
        · simp [M₁, M, hpi, hpj]
  rw [h_add, h_scale] at h_deg
  rw [← Polynomial.coeff_X_pow_mul _ (d j)]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (h_deg.trans_lt (by omega))

variable {f : MvPolynomial (Fin (N + 1) × Fin n) R} {d : Fin n → ℕ}

/-- **Interlacing.** Let `f ≠ 0` be a dual Weyl vector of column degrees `d` for `N + 1` rows,
and `γ` the leading exponent of its expansion in the last row, for the colexicographic order.
Then `γ i + d (i + 1) ≤ d i` for every column `i`: the column degrees `d - γ` of the leading
coefficient interlace `d`. -/
theorem degree_lastRowEquiv_add_le (hf : f ∈ dualWeylModule R (N + 1) d) (hf0 : f ≠ 0)
    {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    colex.degree (lastRowEquiv R N n f) i + d j ≤ d i := by
  classical
  set E := lastRowEquiv R N n f
  set γ := colex.degree E
  have hij' : i < j := by rw [Fin.lt_def]; omega
  by_contra! h_lt
  -- The coefficient of `T ^ γ i` of `x ↦ x·(1 + T·e_{ji})` applied to `f` vanishes.
  have hP : (columnOperation R j i f).coeff (γ i) = 0 :=
    coeff_columnOperation_eq_zero hf hij' h_lt
  have hG : E.coeff γ ≠ 0 :=
    colex.coeff_degree_ne_zero_iff.mpr (by rw [Ne, EmbeddingLike.map_eq_zero_iff]; exact hf0)
  -- Expand in the last row, with `y_i` set to `0`, so that `y_i` becomes `T * y_j`.
  let z : Fin n → MvPolynomial (Fin n) (MvPolynomial (Fin N × Fin n) R) :=
    fun l => if l = i then 0 else X l
  have h := eval₂_columnOperation_lastRowEquiv j i z f
  have hv : (fun l => MvPolynomial.map Polynomial.C (z l) +
      if l = i then C Polynomial.X * MvPolynomial.map Polynomial.C (z j) else 0) =
      fun l => if l = i then C Polynomial.X * X j else X l := by
    funext l
    by_cases hl : l = i <;> simp [z, hl, hij'.ne']
  rw [hv, eval₂_eq'] at h
  simp only [prod_pow_ite_C_mul_X j] at h
  -- Compare the coefficients of `y ^ δ * T ^ γ i`, where `δ` moves `γ i` from `y_i` to `y_j`.
  set δ : Fin n →₀ ℕ := γ.erase i + Finsupp.single j (γ i)
  have h_coeff := congrArg (fun p => (p.coeff δ).coeff (γ i)) h
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def, coeff_sum, ← map_pow,
    RingHom.coe_comp, Function.comp_apply, C_mul_monomial, coeff_monomial] at h_coeff
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff] at h_coeff
  rw [Finset.sum_eq_zero (fun k _ => ?_)] at h_coeff
  · refine hG ?_
    rw [h_coeff, Finset.sum_eq_single γ]
    · simp [δ, E, Polynomial.coeff_mul_X_pow']
    · intro η hη hne
      split_ifs with hσ
      · rw [Polynomial.coeff_mul_X_pow']
        split_ifs with hle
        · exact absurd (colex.le_degree hη) (not_le_of_gt (colex_lt_of_shift_eq hij hσ hle hne))
        · rfl
      · simp
    · intro hγ
      simp [notMem_support_iff.mp hγ]
  · rw [mul_comm, coeff_C_mul, coeff_map, mul_comm, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hk
    · subst hk
      simp [hP]
    · rfl

end CommRing

end DualWeylModule

end TauCeti
