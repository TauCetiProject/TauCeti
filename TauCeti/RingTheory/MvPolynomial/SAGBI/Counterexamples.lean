/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.SAGBI.Completion
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Finsupp.Lex

/-!
# Sharpness of the hypotheses for SAGBI termination

Unlike Buchberger's S-polynomial completion for ideals (`MonomialOrder.wellFounded_sPolynomialStep`
in `TauCeti.RingTheory.MvPolynomial.Groebner.SPolynomialCompletion`), finite SAGBI completion over a
field requires both fairness of binomial processing and finite generation of the initial algebra
(`MonomialOrder.IsFairSAGBICompletion.exists_isSAGBIBasis_iff_fg_initialAlgebra`). This file shows
that neither hypothesis can be omitted, over an arbitrary field `k` (independent of characteristic),
already in two variables under the lexicographic order `X 0 > X 1`:

1. **Fairness is necessary even when the initial algebra is finitely generated.** Starting from
   `G 0 = {X 0, X 0 + X 1}` in `MvPolynomial (Fin 2) k` — whose generated subalgebra is `⊤`, so its
   initial algebra is `⊤` and hence finitely generated — repeatedly processing the toric binomials
   `((X 0 + X 1) - X 0) * (X 0 * X 1 ^ n) = X 0 * X 1 ^ (n + 1)` while ignoring the degree-`1`
   binomial `(X 0 + X 1) - X 0 = X 1` yields an infinite chain of certified `lex.BinomialSAGBIStep`s
   (`MonomialOrder.exists_infinite_binomialSAGBIStep_of_fg_initialAlgebra`).
   Consequently neither `MonomialOrder.BinomialSAGBIStep` nor `MonomialOrder.SAGBIStep` is
   well-founded (`MonomialOrder.not_wellFounded_binomialSAGBIStep`,
   `MonomialOrder.not_wellFounded_sagbiStep`).
2. **Finite generation of the initial algebra is necessary even for fair completion of a finitely
   generated subalgebra.** The Robbiano–Sweedler subalgebra
   `k[X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2] ⊆ MvPolynomial (Fin 2) k` contains `X 0 * X 1 ^ m` for
   every `m ≥ 1`, while every nonconstant element has positive `X 0`-degree in its `lex` leading
   monomial. Hence its `lex` leading-exponent monoid and initial algebra are not finitely generated
   (`MonomialOrder.not_fg_leadingExponents_adjoin_three`,
   `MonomialOrder.not_fg_initialAlgebra_adjoin_three`), it admits no finite `lex` SAGBI basis
   (`MonomialOrder.not_exists_finset_isSAGBIBasis_adjoin_three`), and every fair SAGBI completion
   starting from `{X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2}` fails to stabilize
   (`MonomialOrder.IsFairSAGBICompletion.exists_ne_of_eq_adjoin_three`).

## References

* L. Robbiano, M. Sweedler, *Subalgebra bases*, in *Commutative Algebra (Salvador, 1988)*,
  Lecture Notes in Mathematics 1430, Springer, 1990, 61–87, Example 4.11.
* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 11.
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {k : Type*} [Field k]

/-! ### Non-well-foundedness without fairness -/

/-- In `Fin 2`, `single 1 m ≺[lex] single 0 1` for every `m : ℕ` (`X 0 > X 1`). -/
private theorem fin2_single_one_lt_single_zero (m : ℕ) :
    (Finsupp.single 1 m : Fin 2 →₀ ℕ) ≺[lex] Finsupp.single 0 1 := by
  rw [lex_lt_iff, Finsupp.Lex.lt_iff]
  exact ⟨0, fun j hj ↦ (Fin.not_lt_zero j hj).elim, by simp⟩

private theorem fin2_degree_X0_add_X1 :
    lex.degree (X 0 + X 1 : MvPolynomial (Fin 2) k) = Finsupp.single 0 1 := by
  have hlt : lex.degree (X 1 : MvPolynomial (Fin 2) k) ≺[lex]
      lex.degree (X 0 : MvPolynomial (Fin 2) k) := by
    rw [lex.degree_X, lex.degree_X]
    exact fin2_single_one_lt_single_zero 1
  rw [lex.degree_add_of_lt hlt, lex.degree_X]

private theorem fin2_monic_X0_add_X1 :
    lex.Monic (X 0 + X 1 : MvPolynomial (Fin 2) k) := by
  have hlt : lex.degree (X 1 : MvPolynomial (Fin 2) k) ≺[lex]
      lex.degree (X 0 : MvPolynomial (Fin 2) k) := by
    rw [lex.degree_X, lex.degree_X]
    exact fin2_single_one_lt_single_zero 1
  rw [Monic, leadingCoeff_add_of_lt hlt]
  exact lex.monic_X

/-- The monomial `X 0 * X 1 ^ j` in `MvPolynomial (Fin 2) k` equals
`monomial (single 0 1 + single 1 j) 1`. -/
private theorem fin2_X0_mul_X1_pow_eq_monomial (j : ℕ) :
    (X 0 * X 1 ^ j : MvPolynomial (Fin 2) k) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 j) 1 := by
  rw [X, X_pow_eq_monomial, monomial_mul_monomial, mul_one]

open scoped Classical in
/-- Unfair completion family `G n = {X 0 + X 1} ∪ {X 0 * X 1 ^ j | j ≤ n}` in
`MvPolynomial (Fin 2) k`. -/
private noncomputable def unfairSAGBIChain (k : Type*) [Field k] (n : ℕ) :
    Finset (MvPolynomial (Fin 2) k) :=
  insert (X 0 + X 1) ((Finset.range (n + 1)).image fun j ↦ X 0 * X 1 ^ j)

private theorem mem_unfairSAGBIChain_iff {n : ℕ} {g : MvPolynomial (Fin 2) k} :
    g ∈ unfairSAGBIChain k n ↔ g = X 0 + X 1 ∨ ∃ j < n + 1, g = X 0 * X 1 ^ j := by
  simp only [unfairSAGBIChain, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  exact or_congr_right ⟨fun ⟨j, hj, h⟩ ↦ ⟨j, hj, h.symm⟩, fun ⟨j, hj, h⟩ ↦ ⟨j, hj, h.symm⟩⟩

private theorem monic_of_mem_unfairSAGBIChain {n : ℕ} {g : MvPolynomial (Fin 2) k}
    (hg : g ∈ unfairSAGBIChain k n) : lex.Monic g := by
  rcases mem_unfairSAGBIChain_iff.1 hg with rfl | ⟨j, -, rfl⟩
  · exact fin2_monic_X0_add_X1
  · rw [fin2_X0_mul_X1_pow_eq_monomial]
    exact lex.monic_monomial_one

private theorem adjoin_unfairSAGBIChain_zero :
    Algebra.adjoin k (unfairSAGBIChain k 0 : Set (MvPolynomial (Fin 2) k)) = ⊤ := by
  classical
  refine eq_top_iff.2 (adjoin_range_X.symm.le.trans (Algebra.adjoin_le ?_))
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Algebra.subset_adjoin (by simp [unfairSAGBIChain])
  · have hsum : (X 0 + X 1 : MvPolynomial (Fin 2) k) ∈
        Algebra.adjoin k (unfairSAGBIChain k 0 : Set (MvPolynomial (Fin 2) k)) :=
      Algebra.subset_adjoin (by simp [unfairSAGBIChain])
    have hx0 : (X 0 : MvPolynomial (Fin 2) k) ∈
        Algebra.adjoin k (unfairSAGBIChain k 0 : Set (MvPolynomial (Fin 2) k)) :=
      Algebra.subset_adjoin (by simp [unfairSAGBIChain])
    simpa using sub_mem hsum hx0

private theorem isSubduction_unfairSAGBIChain_rem (n : ℕ) :
    lex.IsSubduction
      (Subtype.val : ↥((unfairSAGBIChain k n : Set (MvPolynomial (Fin 2) k)) \ {0}) → _)
      (X 0 * X 1 ^ (n + 1)) 0 (X 0 * X 1 ^ (n + 1)) := by
  classical
  refine ⟨by simp, by simp, fun a ha hcl ↦ ?_, le_rfl⟩
  rw [fin2_X0_mul_X1_pow_eq_monomial (n + 1)] at ha
  rcases Finset.mem_singleton.1 (support_monomial_subset ha) with rfl
  have hbound : ∀ d ∈ AddSubmonoid.closure (Set.range (lex.degree ∘
      (Subtype.val : ↥((unfairSAGBIChain k n : Set (MvPolynomial (Fin 2) k)) \ {0}) → _))),
      d 1 ≤ n * d 0 := fun d hd ↦ by
    induction hd using AddSubmonoid.closure_induction with
    | mem _ hx =>
      obtain ⟨i, rfl⟩ := hx
      rcases mem_unfairSAGBIChain_iff.1 (Finset.mem_coe.1 i.2.1) with heq | ⟨j, hj, heq⟩
      · simp [heq, fin2_degree_X0_add_X1]
      · rw [Function.comp_apply, heq, fin2_X0_mul_X1_pow_eq_monomial, lex.degree_monomial]
        simp only [one_ne_zero, ↓reduceIte, Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
          Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, zero_add, mul_one]
        omega
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ =>
      simp only [Finsupp.add_apply, Nat.mul_add]
      omega
  have hbad := hbound _ hcl
  simp only [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, zero_add, mul_one] at hbad
  omega

private theorem coe_unfairSAGBIChain_succ (n : ℕ) :
    (unfairSAGBIChain k (n + 1) : Set (MvPolynomial (Fin 2) k)) =
      insert (X 0 * X 1 ^ (n + 1)) (unfairSAGBIChain k n : Set (MvPolynomial (Fin 2) k)) := by
  ext g
  simp only [Finset.mem_coe, mem_unfairSAGBIChain_iff, Set.mem_insert_iff]
  constructor
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact .inr (.inl rfl)
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hlt
      · exact .inl rfl
      · exact .inr (.inr ⟨j, hlt, rfl⟩)
  · rintro (rfl | rfl | ⟨j, hj, rfl⟩)
    · exact .inr ⟨n + 1, Nat.lt_succ_self _, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨j, Nat.lt_succ_of_lt hj, rfl⟩

private theorem binomialSAGBIStep_unfairSAGBIChain (n : ℕ) :
    lex.BinomialSAGBIStep (unfairSAGBIChain k (n + 1)) (unfairSAGBIChain k n) := by
  classical
  set G := unfairSAGBIChain k n
  let S : Set (MvPolynomial (Fin 2) k) := (G : Set (MvPolynomial (Fin 2) k)) \ {0}
  have hne {g : MvPolynomial (Fin 2) k} (hg : g ∈ G) : g ≠ 0 :=
    (monic_of_mem_unfairSAGBIChain hg).ne_zero
  have hg₁ : (X 0 + X 1 : MvPolynomial (Fin 2) k) ∈ G := mem_unfairSAGBIChain_iff.2 (.inl rfl)
  have hg₂ : (X 0 : MvPolynomial (Fin 2) k) ∈ G :=
    mem_unfairSAGBIChain_iff.2 (.inr ⟨0, Nat.zero_lt_succ n, by simp⟩)
  have hg₃ : (X 0 * X 1 ^ n : MvPolynomial (Fin 2) k) ∈ G :=
    mem_unfairSAGBIChain_iff.2 (.inr ⟨n, Nat.lt_succ_self n, rfl⟩)
  let i₁ : ↥S := ⟨X 0 + X 1, hg₁, hne hg₁⟩
  let i₂ : ↥S := ⟨X 0, hg₂, hne hg₂⟩
  let i₃ : ↥S := ⟨X 0 * X 1 ^ n, hg₃, hne hg₃⟩
  let u : ↥S →₀ ℕ := Finsupp.single i₁ 1 + Finsupp.single i₃ 1
  let v : ↥S →₀ ℕ := Finsupp.single i₂ 1 + Finsupp.single i₃ 1
  let r : MvPolynomial (Fin 2) k := X 0 * X 1 ^ (n + 1)
  have hr_monic : lex.Monic r := by
    dsimp only [r]
    rw [fin2_X0_mul_X1_pow_eq_monomial]
    exact lex.monic_monomial_one
  have huv :
      Finsupp.linearCombination ℕ (fun i : ↥S ↦ lex.degree i.1) u =
        Finsupp.linearCombination ℕ (fun i : ↥S ↦ lex.degree i.1) v := by
    simp [u, v, i₁, i₂, fin2_degree_X0_add_X1, lex.degree_X]
  have hlc_one : (fun i : ↥S ↦ (lex.leadingCoeff i.1)⁻¹) = 1 :=
    funext fun i ↦ by
      simp [(monic_of_mem_unfairSAGBIChain (Finset.mem_coe.1 i.2.1)).leadingCoeff_eq_one]
  have hf_eq :
      aeval (Subtype.val : ↥S → MvPolynomial (Fin 2) k)
        (rescale (fun i : ↥S ↦ (lex.leadingCoeff i.1)⁻¹)
          (monomial u (1 : k) - monomial v 1)) = r := by
    have hmul (a b : ↥S) :
        monomial (Finsupp.single a 1 + Finsupp.single b 1) (1 : k) = X a * X b := by
      rw [X, X, monomial_mul_monomial, mul_one]
    rw [hlc_one, rescale_one, AlgHom.id_apply, hmul i₁ i₃, hmul i₂ i₃]
    simp only [map_sub, map_mul, aeval_X, i₁, i₂, i₃, r]
    ring
  refine binomialSAGBIStep_iff.2 ⟨u, v, 0, r, huv, ?_, hr_monic.ne_zero, ?_⟩
  · rw [hf_eq]
    exact isSubduction_unfairSAGBIChain_rem n
  · rw [hr_monic.monicNormalize_eq]
    exact coe_unfairSAGBIChain_succ n

/-- **Fairness cannot be dropped.** Over any field `k`, there is an infinite sequence of certified
`lex.BinomialSAGBIStep`s in `MvPolynomial (Fin 2) k` starting from a finite family whose generated
subalgebra is `⊤` (so its initial algebra is finitely generated), because the fundamental degree-`1`
binomial `(X 0 + X 1) - X 0 = X 1` is never selected while its multiples
`((X 0 + X 1) - X 0) * (X 0 * X 1 ^ n) = X 0 * X 1 ^ (n + 1)` are processed forever. -/
theorem exists_infinite_binomialSAGBIStep_of_fg_initialAlgebra (k : Type*) [Field k] :
    ∃ G : ℕ → Finset (MvPolynomial (Fin 2) k),
      (lex.initialAlgebra (Algebra.adjoin k (G 0 : Set (MvPolynomial (Fin 2) k)))).FG ∧
      ∀ n, lex.BinomialSAGBIStep (G (n + 1)) (G n) := by
  classical
  refine ⟨unfairSAGBIChain k, ?_, binomialSAGBIStep_unfairSAGBIChain⟩
  rw [adjoin_unfairSAGBIChain_zero]
  exact (lex.exists_finset_isSAGBIBasis_iff_fg_initialAlgebra
    (⊤ : Subalgebra k (MvPolynomial (Fin 2) k))).1
    ⟨Finset.univ.image X, by simpa using (lex (σ := Fin 2)).isSAGBIBasis_range_X (R := k)⟩

/-- **Non-well-foundedness of `BinomialSAGBIStep`.** Unlike Buchberger's `SPolynomialStep` on ideals
(`MonomialOrder.wellFounded_sPolynomialStep`), `lex.BinomialSAGBIStep` on `MvPolynomial (Fin 2) k`
is not well-founded over any field `k`. -/
theorem not_wellFounded_binomialSAGBIStep (k : Type*) [Field k] :
    ¬ WellFounded (lex.BinomialSAGBIStep (σ := Fin 2) (k := k)) := by
  intro hwf
  obtain ⟨G, -, hstep⟩ := exists_infinite_binomialSAGBIStep_of_fg_initialAlgebra k
  obtain ⟨n, hn⟩ := Set.mem_range.1 (hwf.min_mem (Set.range G) ⟨G 0, ⟨0, rfl⟩⟩)
  exact hwf.not_lt_min (Set.range G) ⟨n + 1, rfl⟩ (hn ▸ hstep n)

/-- **Non-well-foundedness of `SAGBIStep`.** Unlike `MonomialOrder.wellFounded_remainderStep` for
ideals, `lex.SAGBIStep` on `MvPolynomial (Fin 2) k` is not well-founded over any field `k`. -/
theorem not_wellFounded_sagbiStep (k : Type*) [Field k] :
    ¬ WellFounded (lex.SAGBIStep (σ := Fin 2) (k := k)) :=
  fun hwf ↦ not_wellFounded_binomialSAGBIStep k (hwf.mono fun _ _ h ↦ h.toSAGBIStep)

/-! ### Non-finitely generated initial algebra of a three-generator subalgebra -/

/-- The classic Robbiano–Sweedler three-generator subalgebra
`k[X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2] ⊆ MvPolynomial (Fin 2) k`. -/
private noncomputable def threeGenSubalgebra (k : Type*) [Field k] :
    Subalgebra k (MvPolynomial (Fin 2) k) :=
  Algebra.adjoin k
    ({X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2} : Set (MvPolynomial (Fin 2) k))

private theorem X0_mul_X1_pow_mem_threeGenSubalgebra :
    ∀ m : ℕ, 1 ≤ m → (X 0 * X 1 ^ m : MvPolynomial (Fin 2) k) ∈ threeGenSubalgebra k
  | 0, hm => (Nat.not_succ_le_zero 0 hm).elim
  | 1, _ => by
    rw [pow_one]
    exact Algebra.subset_adjoin (by simp)
  | 2, _ => Algebra.subset_adjoin (by simp)
  | m + 3, _ => by
    have hm1 := X0_mul_X1_pow_mem_threeGenSubalgebra (m + 1) (by omega)
    have hm2 := X0_mul_X1_pow_mem_threeGenSubalgebra (m + 2) (by omega)
    have hg1 : (X 0 + X 1 : MvPolynomial (Fin 2) k) ∈ threeGenSubalgebra k :=
      Algebra.subset_adjoin (by simp)
    have hg2 : (X 0 * X 1 : MvPolynomial (Fin 2) k) ∈ threeGenSubalgebra k :=
      Algebra.subset_adjoin (by simp)
    have hrec : (X 0 * X 1 ^ (m + 3) : MvPolynomial (Fin 2) k) =
        (X 0 + X 1) * (X 0 * X 1 ^ (m + 2)) - (X 0 * X 1) * (X 0 * X 1 ^ (m + 1)) := by ring
    rw [hrec]
    exact sub_mem (mul_mem hg1 hm2) (mul_mem hg2 hm1)

private theorem eq_single_one_of_mem_support_of_degree_zero {f : MvPolynomial (Fin 2) k}
    (hd0 : (lex.degree f) 0 = 0) {d : Fin 2 →₀ ℕ} (hd : d ∈ f.support) :
    d = Finsupp.single 1 (d 1) := by
  have hle : d ≼[lex] lex.degree f := lex.le_degree hd
  have hd_zero : d 0 = 0 := by
    by_contra hne
    have hlt : lex.degree f ≺[lex] d := by
      rw [lex_lt_iff, Finsupp.Lex.lt_iff]
      exact ⟨0, fun j hj ↦ (Fin.not_lt_zero j hj).elim, hd0 ▸ Nat.pos_of_ne_zero hne⟩
    exact not_lt_of_ge hle hlt
  ext i
  fin_cases i <;> simp [hd_zero]

private theorem aeval_X_zero_eq_C_of_degree_zero {f : MvPolynomial (Fin 2) k}
    (hd0 : (lex.degree f) 0 = 0) :
    aeval ![Polynomial.X, (0 : Polynomial k)] f = Polynomial.C (f.coeff 0) := by
  classical
  set φ₀ : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k := aeval ![Polynomial.X, 0]
  have hf_sum : φ₀ f = ∑ d ∈ f.support, φ₀ (monomial d (f.coeff d)) := by
    rw [← map_sum, ← f.as_sum]
  rw [hf_sum]
  have hterm (d : Fin 2 →₀ ℕ) (hd : d ∈ f.support) :
      φ₀ (monomial d (f.coeff d)) = if d = 0 then Polynomial.C (f.coeff 0) else 0 := by
    have hd_eq := eq_single_one_of_mem_support_of_degree_zero hd0 hd
    rcases eq_or_ne (d 1) 0 with h1 | h1
    · have hd_zero : d = 0 := by rw [hd_eq, h1, Finsupp.single_zero]
      simp [φ₀, hd_zero]
    · have hne : d ≠ 0 := fun h0 ↦ h1 (by simp [h0])
      rw [congrArg (fun e ↦ monomial e (f.coeff d)) hd_eq]
      simp [φ₀, aeval_monomial, zero_pow h1, hne]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  by_cases h0 : (0 : Fin 2 →₀ ℕ) ∈ f.support
  · simp [h0]
  · simp [h0, notMem_support_iff.1 h0]

private theorem coeff_aeval_zero_X_of_degree_zero {f : MvPolynomial (Fin 2) k}
    (hf0 : f ≠ 0) (hd0 : (lex.degree f) 0 = 0) :
    (aeval ![(0 : Polynomial k), Polynomial.X] f).coeff ((lex.degree f) 1) =
      f.coeff (lex.degree f) := by
  classical
  set φ₁ : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k := aeval ![0, Polynomial.X]
  set m₀ := (lex.degree f) 1
  have hf_sum : φ₁ f = ∑ d ∈ f.support, φ₁ (monomial d (f.coeff d)) := by
    rw [← map_sum, ← f.as_sum]
  rw [hf_sum, ← Polynomial.lcoeff_apply, map_sum]
  have hterm (d : Fin 2 →₀ ℕ) (hd : d ∈ f.support) :
      (Polynomial.lcoeff k m₀) (φ₁ (monomial d (f.coeff d))) =
        if d = lex.degree f then f.coeff (lex.degree f) else 0 := by
    rw [Polynomial.lcoeff_apply]
    have hd_eq := eq_single_one_of_mem_support_of_degree_zero hd0 hd
    have hdeg_eq :=
      eq_single_one_of_mem_support_of_degree_zero hd0 (lex.degree_mem_support hf0)
    have hmon : φ₁ (monomial d (f.coeff d)) =
        Polynomial.C (f.coeff d) * Polynomial.X ^ (d 1) := by
      rw [congrArg (fun e ↦ monomial e (f.coeff d)) hd_eq]
      simp [φ₁, aeval_monomial]
    rw [hmon, Polynomial.coeff_C_mul_X_pow]
    split_ifs with h1 h2 h2
    · rw [← h2]
    · exact (h2 (hd_eq.trans (h1 ▸ hdeg_eq.symm))).elim
    · exact (h1 (congrArg (fun e : Fin 2 →₀ ℕ ↦ e 1) h2).symm).elim
    · rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', ite_eq_left (lex.degree_mem_support hf0)]

private theorem degree_zero_or_pos_at_zero_of_mem_threeGenSubalgebra
    {f : MvPolynomial (Fin 2) k} (hf : f ∈ threeGenSubalgebra k) (hf0 : f ≠ 0) :
    lex.degree f = 0 ∨ 1 ≤ (lex.degree f) 0 := by
  by_cases hd0 : (lex.degree f) 0 = 0
  · left
    let φ₀ : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k := aeval ![Polynomial.X, 0]
    let φ₁ : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k := aeval ![0, Polynomial.X]
    have heq_φ : φ₀ f = φ₁ f := by
      refine (AlgHom.mem_equalizer φ₀ φ₁ f).1 (Algebra.adjoin_le ?_ hf)
      rintro g (rfl | rfl | rfl) <;> simp [φ₀, φ₁]
    have hd1 : (lex.degree f) 1 = 0 := by
      by_contra h1
      have hcoeff : f.coeff (lex.degree f) = 0 := by
        rw [← coeff_aeval_zero_X_of_degree_zero hf0 hd0, ← heq_φ,
          aeval_X_zero_eq_C_of_degree_zero hd0]
        simp [Polynomial.coeff_C, h1]
      exact mem_support_iff.1 (lex.degree_mem_support hf0) hcoeff
    ext i
    fin_cases i <;> simp [hd0, hd1]
  · exact .inr (Nat.pos_of_ne_zero hd0)

/-- Over any field `k`, the `lex` leading-exponent monoid of the finitely generated subalgebra
`k[X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2] ⊆ MvPolynomial (Fin 2) k` is not finitely generated. -/
theorem not_fg_leadingExponents_adjoin_three (k : Type*) [Field k] :
    ¬ (lex.leadingExponents (Algebra.adjoin k
      ({X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2} : Set (MvPolynomial (Fin 2) k)))).FG := by
  classical
  intro hfg
  obtain ⟨S, hS, hSfin⟩ := (AddSubmonoid.fg_iff _).1 hfg
  let E := hSfin.toFinset
  have hE : AddSubmonoid.closure (E : Set (Fin 2 →₀ ℕ)) =
      lex.leadingExponents (threeGenSubalgebra k) := by
    simpa [E, threeGenSubalgebra] using hS
  let M := E.sup fun e ↦ e 1
  have hbound : ∀ d ∈ AddSubmonoid.closure (E : Set (Fin 2 →₀ ℕ)), d 1 ≤ M * d 0 := fun d hd ↦ by
    induction hd using AddSubmonoid.closure_induction with
    | mem e he =>
      obtain ⟨f, hfA, hf0, rfl⟩ :=
        lex.mem_leadingExponents_iff.1 (hE ▸ AddSubmonoid.subset_closure he)
      rcases degree_zero_or_pos_at_zero_of_mem_threeGenSubalgebra hfA hf0 with h0 | hpos
      · simp [h0]
      · calc
          (lex.degree f) 1 ≤ M :=
            Finset.le_sup (f := fun e : Fin 2 →₀ ℕ ↦ e 1) (Finset.mem_coe.1 he)
          _ = M * 1 := (Nat.mul_one M).symm
          _ ≤ M * (lex.degree f) 0 := Nat.mul_le_mul_left M hpos
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ =>
      simp only [Finsupp.add_apply, Nat.mul_add]
      omega
  have hmem : Finsupp.single 0 1 + Finsupp.single 1 (M + 1) ∈
      AddSubmonoid.closure (E : Set (Fin 2 →₀ ℕ)) := by
    rw [hE]
    have hp := X0_mul_X1_pow_mem_threeGenSubalgebra (k := k) (M + 1) (Nat.succ_pos M)
    have hmon := fin2_X0_mul_X1_pow_eq_monomial (k := k) (M + 1)
    refine lex.mem_leadingExponents_iff.2 ⟨X 0 * X 1 ^ (M + 1), hp, ?_, ?_⟩
    · rw [hmon]
      exact lex.monic_monomial_one.ne_zero
    · rw [hmon, lex.degree_monomial]
      simp
  have hbad := hbound _ hmem
  simp only [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, zero_add, mul_one] at hbad
  omega

/-- **Finite generation of the initial algebra cannot be dropped.** Over any field `k`, the
finitely generated subalgebra `k[X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2] ⊆ MvPolynomial (Fin 2) k` has
non-finitely generated `lex` initial algebra. -/
theorem not_fg_initialAlgebra_adjoin_three (k : Type*) [Field k] :
    ¬ (lex.initialAlgebra (Algebra.adjoin k
      ({X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2} : Set (MvPolynomial (Fin 2) k)))).FG :=
  (lex.fg_initialAlgebra_iff_fg_leadingExponents _).not.2
    (not_fg_leadingExponents_adjoin_three k)

/-- Over any field `k`, the finitely generated subalgebra
`k[X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2] ⊆ MvPolynomial (Fin 2) k` admits no finite `lex` SAGBI
basis. -/
theorem not_exists_finset_isSAGBIBasis_adjoin_three (k : Type*) [Field k] :
    ¬ ∃ B : Finset (MvPolynomial (Fin 2) k),
      lex.IsSAGBIBasis (B : Set (MvPolynomial (Fin 2) k))
        (Algebra.adjoin k
          ({X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2} : Set (MvPolynomial (Fin 2) k))) :=
  (lex.exists_finset_isSAGBIBasis_iff_fg_leadingExponents _).not.2
    (not_fg_leadingExponents_adjoin_three k)

/-- **Every fair completion from `{X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2}` fails to stabilize.**
Even though `⋃ n, B n` is a countable SAGBI basis of the finitely generated subalgebra
`k[X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2]`, no stage `B N` can be stationary. -/
theorem IsFairSAGBICompletion.exists_ne_of_eq_adjoin_three {B : ℕ → Finset (MvPolynomial (Fin 2) k)}
    (hB : lex.IsFairSAGBICompletion B)
    (hB0 : (B 0 : Set (MvPolynomial (Fin 2) k)) = {X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2})
    (N : ℕ) : ∃ n ≥ N, B n ≠ B N := by
  by_contra hstat
  push Not at hstat
  have hiUnion : (⋃ n, (B n : Set (MvPolynomial (Fin 2) k))) = (B N : Set _) := by
    refine le_antisymm (Set.iUnion_subset fun n ↦ ?_)
      (Set.subset_iUnion (fun n ↦ (B n : Set (MvPolynomial (Fin 2) k))) N)
    rcases le_or_gt N n with hle | hlt
    · rw [hstat n hle]
    · exact Finset.coe_subset.2 (hB.monotone hlt.le)
  have hfin : lex.IsSAGBIBasis (B N : Set (MvPolynomial (Fin 2) k))
      (Algebra.adjoin k
        ({X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2} : Set (MvPolynomial (Fin 2) k))) := by
    simpa [hiUnion, hB0] using hB.isSAGBIBasis_iUnion
  exact not_exists_finset_isSAGBIBasis_adjoin_three k ⟨B N, hfin⟩

end MonomialOrder
