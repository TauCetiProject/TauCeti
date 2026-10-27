/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import TauCeti.NumberTheory.Padics.Distribution.AnalyticStage
public import TauCeti.Topology.MetricSpace.Ultra.ContinuousMaps
import Mathlib.Algebra.CharZero.Infinite
import TauCeti.NumberTheory.Padics.Factorial
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Amice's polynomials on the discs of level `h`

For `h, n : ℕ` put `m_h(n) = ⌊n / pʰ⌋!`. Amice's basis of the analytic stage `LA_h` consists of
the polynomials

`e_{h,n}(x) = m_h(n) (x choose n)`.

On the disc `a + pʰℤ_p`, in the coordinate `w = (x - a) / pʰ`, the polynomial `e_{h,n}` is a
polynomial in `w`. Its coefficients lie in `ℤ_p`
(`TauCeti.exists_natDegree_le_and_eval_eq_factorial_mul_choose`). This is stronger than
`e_{h,n}` taking integral values, which already holds for `x choose n`, and it needs the factor
`m_h(n)`: the coefficient of `w` in `(pʰ w choose n)` is `(-1) ^ (n - 1) pʰ / n`, which is
`± p⁻¹` for `n = p ^ (h + 1)`. The proof factors
`n! (a + pʰ w choose n) = ∏_{i < n} (a - i + pʰ w)`. The factor of index `i` is divisible by
`p ^ min(v_p(a - i), h)`, and among `n` consecutive elements of `ℤ_p` at least `⌊n / pᵏ⌋` are
divisible by `pᵏ`, so the product is divisible by `p ^ (∑_{k = 1}^{h} ⌊n / pᵏ⌋)`. By Legendre's
formula this exponent is `v_p(n!) - v_p(m_h(n))`.

Hence `e_{h,n}` has an expansion in `LA_h(ℤ_p)`, and more generally `e_{h,n} • e` has one in
`LA_h(E)` for every normed `ℤ_p`-module `E`, of norm at most `‖e‖` when the action is
contractive. For complete ultrametric `E`, summing these vectors gives a continuous linear map

`TauCeti.AnalyticStage.amiceMap : C₀(ℕ, E) → LA_h(E)`,  `(cₙ) ↦ ∑ₙ e_{h,n} • cₙ`,

which does not increase norms. Followed by evaluation, it is the Mahler series with
coefficients `m_h(n) • cₙ` (`TauCeti.AnalyticStage.eval_amiceMap`). Amice's theorem, which is not
proved here, asserts that `amiceMap` is an isometric isomorphism.

## Main definitions

* `TauCeti.amicePolynomial p h n a`: the polynomial `w ↦ m_h(n) (a + pʰ w choose n)` over
  `ℤ_p`.
* `TauCeti.AnalyticStage.amiceTerm p h n e`: the expansion of `e_{h,n} • e` in `LA_h(E)`.
* `TauCeti.AnalyticStage.amiceMap p h S`: the map `C₀(ℕ, E) →L[S] LA_h(E)`, `c ↦ ∑ₙ e_{h,n} • cₙ`.

## Main results

* `TauCeti.exists_natDegree_le_and_eval_eq_factorial_mul_choose`: Amice's polynomials have
  integral coefficients on every disc.
* `TauCeti.eval_amicePolynomial`, `TauCeti.eq_amicePolynomial_of_eval`: `amicePolynomial` is the
  unique polynomial with these values.
* `TauCeti.AnalyticStage.eval_amiceTerm`: `amiceTerm` evaluates to the Mahler term of
  `m_h(n) • e`.
* `TauCeti.AnalyticStage.norm_amiceMap_le`, `TauCeti.AnalyticStage.eval_amiceMap`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter Topology Polynomial Nat
open scoped ZeroAtInfty Finset

variable {p : ℕ} [hp : Fact p.Prime]

namespace TauCeti

/-! ### Integrality of the disc coefficients -/

section Integrality

/-- The product `∏_{i < n} (a - i + pʰ X)`, whose value at `w` is `n! (a + pʰ w choose n)`. -/
private noncomputable def discProd (h n : ℕ) (a : ℤ_[p]) : ℤ_[p][X] :=
  ∏ i ∈ Finset.range n, (C (a - i) + C ((p : ℤ_[p]) ^ h) * X)

private theorem eval_discProd (h n : ℕ) (a w : ℤ_[p]) :
    (discProd h n a).eval w = n ! * Ring.choose (a + (p : ℤ_[p]) ^ h * w) n := by
  have hchoose := Ring.descPochhammer_eq_factorial_smul_choose (a + (p : ℤ_[p]) ^ h * w) n
  rw [← aeval_eq_smeval, aeval_def, ← eval_map, descPochhammer_map,
    descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at hchoose
  rw [discProd, eval_prod, ← hchoose]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp only [eval_add, eval_C, eval_mul, eval_X]
  ring

private theorem natDegree_discProd_le (h n : ℕ) (a : ℤ_[p]) : (discProd h n a).natDegree ≤ n := by
  rw [discProd]
  refine (natDegree_prod_le _ _).trans <| (Finset.sum_le_sum fun i _ ↦ ?_).trans
    (Finset.sum_const_nat (m := 1) fun _ _ ↦ rfl).le |>.trans (by simp)
  exact (natDegree_add_le _ _).trans <| max_le ((natDegree_C _).le.trans zero_le_one)
    ((natDegree_C_mul_le _ _).trans natDegree_X_le)

/-- The product `∏_{i < n} (a - i + pʰ X)` is divisible by `p ^ (∑_{k = 1}^{h} ⌊n / pᵏ⌋)`. -/
private theorem C_pow_dvd_discProd (h n : ℕ) (a : ℤ_[p]) :
    C ((p : ℤ_[p]) ^ ∑ k ∈ Finset.range h, n / p ^ (k + 1)) ∣ discProd h n a := by
  classical
  -- `d i = min(v_p(a - i), h)`, the largest `k ≤ h` with `pᵏ ∣ a - i`.
  set d : ℕ → ℕ := fun i ↦ Nat.findGreatest (fun k ↦ (p : ℤ_[p]) ^ k ∣ a - i) h
  have hd_le (i : ℕ) : d i ≤ h := Nat.findGreatest_le h
  have hd_dvd (i : ℕ) : (p : ℤ_[p]) ^ d i ∣ a - i :=
    Nat.findGreatest_spec (P := fun k ↦ (p : ℤ_[p]) ^ k ∣ a - i) (zero_le h) (by simp)
  have hfac (i : ℕ) : C ((p : ℤ_[p]) ^ d i) ∣ C (a - i) + C ((p : ℤ_[p]) ^ h) * X := by
    obtain ⟨s, hs⟩ := hd_dvd i
    refine ⟨C s + C ((p : ℤ_[p]) ^ (h - d i)) * X, ?_⟩
    rw [hs, mul_add, ← mul_assoc, ← C_mul, ← C_mul, ← pow_add, Nat.add_sub_cancel' (hd_le i)]
  -- Count the pairs `(k, i)` with `pᵏ⁺¹ ∣ a - i` in two ways.
  have hsum : ∑ k ∈ Finset.range h, n / p ^ (k + 1) ≤ ∑ i ∈ Finset.range n, d i :=
    calc ∑ k ∈ Finset.range h, n / p ^ (k + 1)
        ≤ ∑ k ∈ Finset.range h,
            #{i ∈ Finset.range n | (p : ℤ_[p]) ^ (k + 1) ∣ a - ((i : ℕ) : ℤ_[p])} :=
          Finset.sum_le_sum fun k _ ↦ a.div_pow_le_card_filter_dvd n (k + 1)
      _ = ∑ i ∈ Finset.range n, #{k ∈ Finset.range h | (p : ℤ_[p]) ^ (k + 1) ∣ a - i} := by
          simp only [Finset.card_filter]
          exact Finset.sum_comm
      _ ≤ ∑ i ∈ Finset.range n, d i := Finset.sum_le_sum fun i _ ↦ by
          calc #{k ∈ Finset.range h | (p : ℤ_[p]) ^ (k + 1) ∣ a - i}
              ≤ #(Finset.range (d i)) := Finset.card_le_card fun k hk ↦ by
                simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
                exact Nat.le_findGreatest (P := fun k ↦ (p : ℤ_[p]) ^ k ∣ a - i) hk.1 hk.2
            _ = d i := Finset.card_range _
  calc C ((p : ℤ_[p]) ^ ∑ k ∈ Finset.range h, n / p ^ (k + 1))
      ∣ C ((p : ℤ_[p]) ^ ∑ i ∈ Finset.range n, d i) := _root_.map_dvd C (pow_dvd_pow _ hsum)
    _ = ∏ i ∈ Finset.range n, C ((p : ℤ_[p]) ^ d i) := by
        rw [← map_prod, Finset.prod_pow_eq_pow_sum]
    _ ∣ discProd h n a := Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦ hfac i

/-- **Integrality of Amice's polynomials on discs.** For every centre `a ∈ ℤ_p`, the polynomial
`w ↦ ⌊n / pʰ⌋! (a + pʰ w choose n)` has coefficients in `ℤ_p`: it is the evaluation of a
polynomial over `ℤ_p` of degree at most `n`. -/
theorem exists_natDegree_le_and_eval_eq_factorial_mul_choose (h n : ℕ) (a : ℤ_[p]) :
    ∃ P : ℤ_[p][X], P.natDegree ≤ n ∧ ∀ w : ℤ_[p],
      P.eval w = ((n / p ^ h)! : ℤ_[p]) * Ring.choose (a + (p : ℤ_[p]) ^ h * w) n := by
  obtain ⟨P, hP⟩ : C (n ! : ℤ_[p]) ∣ C ((n / p ^ h)! : ℤ_[p]) * discProd h n a := by
    refine (_root_.map_dvd C (factorial_dvd_factorial_div_mul_pow h n)).trans ?_
    rw [C_mul]
    exact mul_dvd_mul_left _ (C_pow_dvd_discProd h n a)
  have hn : (n ! : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero n)
  refine ⟨P, ?_, fun w ↦ ?_⟩
  · rw [← natDegree_C_mul hn, ← hP]
    exact natDegree_C_mul_le _ _ |>.trans (natDegree_discProd_le h n a)
  · refine mul_left_cancel₀ hn ?_
    have := congrArg (eval w) hP
    rw [eval_mul, eval_mul, eval_C, eval_C, eval_discProd] at this
    rw [← this]
    ring

variable (p) in
/-- **Amice's polynomial on the disc of centre `a`.** The polynomial over `ℤ_p` whose value at
`w` is `⌊n / pʰ⌋! (a + pʰ w choose n)`: the expansion of Amice's basis polynomial
`e_{h,n}(x) = ⌊n / pʰ⌋! (x choose n)` in the coordinate `w = (x - a) / pʰ` of the disc
`a + pʰℤ_p`. -/
noncomputable def amicePolynomial (h n : ℕ) (a : ℤ_[p]) : ℤ_[p][X] :=
  (exists_natDegree_le_and_eval_eq_factorial_mul_choose h n a).choose

/-- Amice's polynomial on a disc has degree at most `n`. -/
theorem natDegree_amicePolynomial_le (h n : ℕ) (a : ℤ_[p]) :
    (amicePolynomial p h n a).natDegree ≤ n :=
  (exists_natDegree_le_and_eval_eq_factorial_mul_choose h n a).choose_spec.1

/-- The value of Amice's polynomial on the disc of centre `a` at `w` is
`⌊n / pʰ⌋! (a + pʰ w choose n)`. -/
@[simp]
theorem eval_amicePolynomial (h n : ℕ) (a w : ℤ_[p]) :
    (amicePolynomial p h n a).eval w =
      ((n / p ^ h)! : ℤ_[p]) * Ring.choose (a + (p : ℤ_[p]) ^ h * w) n :=
  (exists_natDegree_le_and_eval_eq_factorial_mul_choose h n a).choose_spec.2 w

/-- `amicePolynomial p h n a` is the only polynomial with values `⌊n / pʰ⌋! (a + pʰ w choose n)`.
-/
theorem eq_amicePolynomial_of_eval {h n : ℕ} {a : ℤ_[p]} {P : ℤ_[p][X]}
    (hP : ∀ w, P.eval w = ((n / p ^ h)! : ℤ_[p]) * Ring.choose (a + (p : ℤ_[p]) ^ h * w) n) :
    P = amicePolynomial p h n a :=
  Polynomial.funext fun w ↦ by rw [hP, eval_amicePolynomial]

/-- The coefficients of Amice's polynomial vanish above degree `n`. -/
theorem coeff_amicePolynomial_eq_zero {h n k : ℕ} (a : ℤ_[p]) (hk : n < k) :
    (amicePolynomial p h n a).coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natDegree_amicePolynomial_le h n a).trans_lt hk)

end Integrality

/-! ### Amice's vectors in the analytic stages -/

namespace AnalyticStage

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E]

/-- The coefficients of `e_{h,n} • e` vanish outside the finitely many indices of degree `≤ n`. -/
private theorem tendsto_amiceCoeff (n : ℕ) (e : E) :
    Tendsto (fun i : ZMod (p ^ h) × ℕ ↦ (amicePolynomial p h n (i.1.val : ℤ_[p])).coeff i.2 • e)
      cofinite (𝓝 0) := by
  have hfin : {i : ZMod (p ^ h) × ℕ | i.2 ≤ n}.Finite :=
    (Set.finite_univ.prod (Set.finite_Iic n)).subset fun i hi ↦ by simpa using hi
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hfin.compl_mem_cofinite] with i hi
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hi
  simp [coeff_amicePolynomial_eq_zero _ hi]

variable (p h) in
/-- **Amice's vector** `e_{h,n} • e` in `LA_h(E)`: on the disc of `a ∈ ZMod (pʰ)` its coefficient
of `wᵏ` is the `k`-th coefficient of `amicePolynomial p h n a.val`, times `e`. -/
noncomputable def amiceTerm (n : ℕ) (e : E) : AnalyticStage p h E :=
  ZeroAtInftyContinuousMap.mkOfDiscrete _ (tendsto_amiceCoeff n e)

/-- The coefficients of Amice's vector `e_{h,n} • e`. -/
@[simp]
theorem amiceTerm_apply (n : ℕ) (e : E) (i : ZMod (p ^ h) × ℕ) :
    amiceTerm p h n e i = (amicePolynomial p h n (i.1.val : ℤ_[p])).coeff i.2 • e :=
  congrFun (ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ (tendsto_amiceCoeff n e)) i

/-- Amice's vector of `0` is `0`. -/
@[simp]
theorem amiceTerm_zero (n : ℕ) : amiceTerm p h n (0 : E) = 0 := by
  ext i
  simp

/-- Amice's vector `e_{h,n} • e` is additive in `e`. -/
theorem amiceTerm_add (n : ℕ) (e f : E) :
    amiceTerm p h n (e + f) = amiceTerm p h n e + amiceTerm p h n f := by
  ext i
  simp [smul_add]

section Scalars

variable {S : Type*} [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- Amice's vector `e_{h,n} • e` commutes with scalars acting on `E` compatibly with `ℤ_p`. -/
theorem amiceTerm_smul (n : ℕ) (s : S) (e : E) :
    amiceTerm p h n (s • e) = s • amiceTerm p h n e := by
  ext i
  simp [smul_comm _ s]

end Scalars

variable [IsBoundedSMul ℤ_[p] E]

/-- Amice's vectors have norm at most `‖e‖`: their coefficients are integral multiples of `e`. -/
theorem norm_amiceTerm_le (n : ℕ) (e : E) : ‖amiceTerm p h n e‖ ≤ ‖e‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg e)).mpr fun i ↦ by
    rw [amiceTerm_apply]
    exact (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg e) (PadicInt.norm_le_one _))

variable [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- Amice's vector `e_{h,n} • e` evaluates to the Mahler term `x ↦ (x choose n) • ⌊n / pʰ⌋! • e`.
-/
@[simp]
theorem eval_amiceTerm (n : ℕ) (e : E) :
    eval S (amiceTerm p h n e) = PadicInt.mahlerTerm ((n / p ^ h)! • e) n := by
  ext x
  obtain ⟨⟨a, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  rw [PadicInt.discHomeomorph_apply, eval_natCast_val_add_mul, PadicInt.mahlerTerm_apply,
    mahler_apply,
    tsum_eq_sum (s := Finset.range (n + 1)) fun k hk ↦ by
      simp [coeff_amicePolynomial_eq_zero _ (by simpa using hk : n < k)]]
  simp only [amiceTerm_apply, smul_smul, ← Finset.sum_smul]
  rw [← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul, mul_comm (Ring.choose _ _),
    ← eval_amicePolynomial,
    eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_amicePolynomial_le h n _))]
  exact congrArg (· • e) (Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _)

private theorem summable_amiceTerm (c : C₀(ℕ, E)) : Summable fun n ↦ amiceTerm p h n (c n) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    squeeze_zero_norm (fun n ↦ norm_amiceTerm_le n (c n))
      (tendsto_zero_iff_norm_tendsto_zero.mp c.tendsto_cofinite)

variable (p h) in
/-- **Amice's map** `C₀(ℕ, E) → LA_h(E)`, `(cₙ) ↦ ∑ₙ e_{h,n} • cₙ`, sending a null sequence to
the expansion on the discs of level `h` of the series of Amice's polynomials
`e_{h,n}(x) = ⌊n / pʰ⌋! (x choose n)` with coefficients `cₙ`. -/
noncomputable def amiceMap : C₀(ℕ, E) →L[S] AnalyticStage p h E :=
  let L : C₀(ℕ, E) →ₗ[S] AnalyticStage p h E :=
    { toFun c := ∑' n, amiceTerm p h n (c n)
      map_add' c d := by
        simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, amiceTerm_add]
        exact (summable_amiceTerm c).tsum_add (summable_amiceTerm d)
      map_smul' s c := by
        simp only [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, amiceTerm_smul,
          RingHom.id_apply]
        exact (summable_amiceTerm c).tsum_const_smul s }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun c ↦ by
      rw [one_mul]
      exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg c) fun n ↦
        (norm_amiceTerm_le n (c n)).trans (c.norm_coe_le_norm n) }

/-- Amice's map is the sum of Amice's vectors `e_{h,n} • cₙ`. -/
theorem hasSum_amiceMap (c : C₀(ℕ, E)) :
    HasSum (fun n ↦ amiceTerm p h n (c n)) (amiceMap p h S c) :=
  (summable_amiceTerm c).hasSum

/-- The coordinates of Amice's map: on the disc of `a`, the coefficient of `wᵏ` in `amiceMap c` is
the sum over `n` of the `k`-th coefficient of `amicePolynomial p h n a.val`, times `cₙ`. -/
theorem hasSum_amiceMap_apply (c : C₀(ℕ, E)) (i : ZMod (p ^ h) × ℕ) :
    HasSum (fun n ↦ (amicePolynomial p h n (i.1.val : ℤ_[p])).coeff i.2 • c n)
      (amiceMap p h S c i) := by
  simpa using (hasSum_amiceMap S c).mapL (ZeroAtInftyContinuousMap.evalCLM ℤ_[p] i)

/-- The coefficient of `wᵏ` on the disc of `a` in `amiceMap c`. -/
theorem amiceMap_apply (c : C₀(ℕ, E)) (i : ZMod (p ^ h) × ℕ) :
    amiceMap p h S c i = ∑' n, (amicePolynomial p h n (i.1.val : ℤ_[p])).coeff i.2 • c n :=
  (hasSum_amiceMap_apply S c i).tsum_eq.symm

/-- Amice's map sends the coordinate vector `single n e` to Amice's vector `e_{h,n} • e`. -/
@[simp]
theorem amiceMap_single (n : ℕ) (e : E) :
    amiceMap p h S (ZeroAtInftyContinuousMap.single n e) = amiceTerm p h n e := by
  classical
  refine (hasSum_amiceMap S _).unique ?_
  convert hasSum_single n (f := fun m ↦ amiceTerm p h m (ZeroAtInftyContinuousMap.single n e m))
    fun m hm ↦ by simp [ZeroAtInftyContinuousMap.single_eq_of_ne hm]
  simp

/-- Amice's map does not increase norms. -/
theorem norm_amiceMap_le (c : C₀(ℕ, E)) : ‖amiceMap p h S c‖ ≤ ‖c‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg c) fun n ↦
    (norm_amiceTerm_le n (c n)).trans (c.norm_coe_le_norm n)

/-- Amice's map followed by evaluation is the Mahler series `x ↦ ∑ₙ (x choose n) • ⌊n / pʰ⌋! • cₙ`.
-/
theorem eval_amiceMap (c : C₀(ℕ, E)) :
    eval S (amiceMap p h S c) = PadicInt.mahlerSeries fun n ↦ (n / p ^ h)! • c n := by
  rw [PadicInt.mahlerSeries, ← ((hasSum_amiceMap S c).mapL (eval S)).tsum_eq]
  simp

end AnalyticStage

end TauCeti
