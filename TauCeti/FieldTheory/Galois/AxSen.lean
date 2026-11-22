/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.IsometricSMul

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Normal.Basic
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.Analysis.Normed.Unbundled.RootBound
import TauCeti.Data.Nat.Choose.Factorization

/-!
# The Ax–Sen lemma

Let `E` be an algebraically closed field of characteristic zero with an ultrametric norm,
algebraic over a subfield `F`, such that every `F`-automorphism of `E` is an isometry, and let `p`
be a prime with `‖p‖ < 1` in `E`. The **Ax–Sen lemma** says that an element
`α ∈ E` all of whose `F`-conjugates are close to `α` is close to an element of `F`: if
`‖σ α - α‖ ≤ r` for every `σ ∈ Gal(E/F)`, then some `a ∈ F` satisfies

`‖α - a‖ ≤ ‖p‖ ^ (-p / (p - 1) ^ 2) * r`.

In additive notation, with `v(p) = 1`, this is `v(α - a) ≥ Δ_F(α) - p / (p - 1) ^ 2` for
`Δ_F(α) = inf_σ v(σ α - α)`. The constant depends only on `p`, not on the degree of `α`.

The proof is Ax's induction on the degree `n` of `α` over `F`. For `0 < d < n`, the `d`-th Hasse
derivative `Q` of the minimal polynomial `P` of `α` has coefficients in `F`, degree `n - d` and
leading coefficient `n.choose d`. Its value at `α` is the coefficient of `Y ^ d` in
`P(α + Y) = ∏ (Y - (αᵢ - α))`, a signed elementary symmetric function of the differences
`αᵢ - α` of the conjugates `αᵢ` of `α`, so `‖Q(α)‖ ≤ r ^ (n - d)`. Factoring `Q` over `E` shows
that some root `β` of `Q`, of degree at most `n - d` over `F`, satisfies
`‖n.choose d‖ * ‖α - β‖ ^ (n - d) ≤ r ^ (n - d)`, and the conjugates of `β` are as close to `β`
as those of `α` are to `α`, up to `‖α - β‖`.

* If `n` is not a power of `p`, take `d = p ^ v` for `v` the exponent of `p` in `n`; then `p` does
  not divide `n.choose d`, which has norm one, so `‖α - β‖ ≤ r` with no loss.
* If `n = p ^ k` with `k ≥ 1`, take `d = p ^ (k - 1)`; then `n.choose d` is exactly divisible by
  `p`, and `‖α - β‖ ≤ ‖p‖ ^ (-1 / (p ^ (k - 1) (p - 1))) * r`.

Along the induction the degree drops below each power `p ^ k` at most once, so the total loss is
at most `∑_{k ≥ 1} 1 / (p ^ (k - 1) (p - 1)) = p / (p - 1) ^ 2`.

This is the approximation step in the proof of the Ax–Sen–Tate theorem: the elements of the
completion of an algebraic closure of `ℚ_p` fixed by a closed subgroup of its Galois group form the
closure of the corresponding fixed field.

## Main results

* `IsUltrametricDist.norm_natCast_eq_one_of_not_dvd`: in an ultrametric normed ring with
  `‖p‖ < 1`, a natural number not divisible by `p` has norm one.
* `IsUltrametricDist.norm_choose_prime_pow_succ`: `(p ^ (k + 1)).choose (p ^ k)` has the norm of
  `p`.
* `Polynomial.Monic.norm_eval_hasseDeriv_le`: if the roots of a split monic polynomial `P` lie
  within `r` of `α`, then `‖(hasseDeriv d P).eval α‖ ≤ r ^ (natDegree P - d)`.
* `Polynomial.Monic.exists_isRoot_hasseDeriv_norm_sub_le`: some root `β` of the `d`-th Hasse
  derivative then satisfies `‖n.choose d‖ * ‖α - β‖ ^ (n - d) ≤ r ^ (n - d)`.
* `TauCeti.exists_norm_sub_algebraMap_le_of_forall_norm_smul_sub_le`: the Ax–Sen lemma.

## References

* J. Ax, *Zeros of polynomials over local fields — the Galois action*, J. Algebra 15 (1970),
  417–428.
* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*, §4.1.1,
  Proposition 4.3 (the Ax–Sen lemma) and its proof.
* O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), §2.1.
-/

public section

open Polynomial

/-- In an ultrametric normed ring in which a prime `p` has norm less than one, every natural
number not divisible by `p` has norm one. -/
theorem IsUltrametricDist.norm_natCast_eq_one_of_not_dvd {R : Type*} [SeminormedRing R]
    [NormOneClass R] [IsUltrametricDist R] {p m : ℕ} (hp : p.Prime) (hpR : ‖(p : R)‖ < 1)
    (hm : ¬p ∣ m) : ‖(m : R)‖ = 1 := by
  refine (IsUltrametricDist.norm_natCast_le_one R m).antisymm (not_lt.mp fun hmR ↦ ?_)
  obtain ⟨u, v, huv⟩ :=
    Nat.isCoprime_iff_coprime.mpr (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hm))
  have hsum : (u : R) * m + (v : R) * p = 1 := by exact_mod_cast congrArg (Int.cast (R := R)) huv
  have hlt (z : ℤ) (n : ℕ) (hn : ‖(n : R)‖ < 1) : ‖(z : R) * n‖ < 1 :=
    (norm_mul_le _ _).trans_lt <| by
      calc ‖(z : R)‖ * ‖(n : R)‖ ≤ 1 * ‖(n : R)‖ := by
            gcongr
            simpa using IsUltrametricDist.norm_intCast_le_norm_one (R := R) z
        _ < 1 := by rwa [one_mul]
  have h := IsUltrametricDist.norm_add_le_max ((u : R) * m) ((v : R) * p)
  rw [hsum, norm_one] at h
  exact (h.trans_lt (max_lt (hlt u m hmR) (hlt v p hpR))).false

/-- In an ultrametric normed ring in which a prime `p` has norm less than one, the binomial
coefficient `(p ^ (k + 1)).choose (p ^ k)`, which is exactly divisible by `p`, has the norm of `p`.
-/
theorem IsUltrametricDist.norm_choose_prime_pow_succ {R : Type*} [SeminormedRing R]
    [NormOneClass R] [NormMulClass R] [IsUltrametricDist R] {p : ℕ} (hp : p.Prime)
    (hpR : ‖(p : R)‖ < 1) (k : ℕ) : ‖((p ^ (k + 1)).choose (p ^ k) : R)‖ = ‖(p : R)‖ := by
  have hc : (p ^ (k + 1)).choose (p ^ k) ≠ 0 :=
    (Nat.choose_pos (Nat.pow_le_pow_right hp.pos (Nat.le_succ k))).ne'
  have hfact : ((p ^ (k + 1)).choose (p ^ k)).factorization p = 1 := by
    rw [Nat.factorization_choose_prime_pow hp (Nat.pow_le_pow_right hp.pos (Nat.le_succ k))
      (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow_self hp]
    omega
  have h := Nat.ordProj_mul_ordCompl_eq_self ((p ^ (k + 1)).choose (p ^ k)) p
  have hu := Nat.not_dvd_ordCompl hp hc
  rw [hfact, pow_one] at h hu
  rw [← h, Nat.cast_mul, norm_mul, norm_natCast_eq_one_of_not_dvd hp hpR hu, mul_one]

namespace Polynomial.Monic

variable {E : Type*} [NormedField E] [IsUltrametricDist E]

/-- **Hasse derivatives near the roots.** If a monic polynomial `P` over an ultrametric normed
field splits, and all its roots lie within `r` of a point `α`, then the `d`-th Hasse derivative of
`P` at `α` has norm at most `r ^ (natDegree P - d)`. It is the coefficient of `Y ^ d` in
`P(α + Y) = ∏ (Y - (αᵢ - α))`. -/
theorem norm_eval_hasseDeriv_le {P : E[X]} (hP : P.Monic) (hsplit : P.Splits) {α : E} {r : ℝ}
    (hr : ∀ β ∈ P.roots, ‖β - α‖ ≤ r) (d : ℕ) :
    ‖(hasseDeriv d P).eval α‖ ≤ r ^ (P.natDegree - d) := by
  have hT : (taylor α P).Monic := by
    rw [Monic, leadingCoeff_taylor]
    exact hP
  -- The roots of `P(α + Y)` are the differences `β - α` for the roots `β` of `P`. The function
  -- underlying `normRingSeminorm E` is the norm itself.
  have hroots : ∀ γ ∈ (taylor α P).roots, normRingSeminorm E γ ≤ r := by
    intro γ hγ
    have h0 : P.IsRoot (γ + α) := by
      rw [IsRoot, ← taylor_eval]
      exact (mem_roots hT.ne_zero).mp hγ
    have h := hr _ ((mem_roots hP.ne_zero).mpr h0)
    rwa [add_sub_cancel_right] at h
  have h := hT.apply_coeff_le_pow_of_card_roots (f := normRingSeminorm E) (norm_one (α := E)).le
    IsUltrametricDist.isNonarchimedean_norm
    (splits_iff_card_roots.mp (hsplit.taylor α)) hroots d
  rwa [taylor_coeff, natDegree_taylor] at h

/-- **A root of a Hasse derivative near a point.** Let `P` be a monic polynomial over an
algebraically closed ultrametric normed field of characteristic zero, all of whose roots lie within
`r` of a point `α`, and let `d < natDegree P`. Then the `d`-th Hasse derivative of `P` has a root
`β` with `‖n.choose d‖ * ‖α - β‖ ^ (n - d) ≤ r ^ (n - d)`, where `n = natDegree P`. -/
theorem exists_isRoot_hasseDeriv_norm_sub_le [IsAlgClosed E] [CharZero E] {P : E[X]}
    (hP : P.Monic) {α : E} {r : ℝ} (hr : ∀ β ∈ P.roots, ‖β - α‖ ≤ r) {d : ℕ}
    (hd : d < P.natDegree) :
    ∃ β, (hasseDeriv d P).IsRoot β ∧
      ‖(P.natDegree.choose d : E)‖ * ‖α - β‖ ^ (P.natDegree - d) ≤ r ^ (P.natDegree - d) := by
  classical
  set Q := hasseDeriv d P
  set n := P.natDegree
  have hcoeff : Q.coeff (n - d) = (n.choose d : E) := by
    rw [hasseDeriv_coeff, Nat.sub_add_cancel hd.le, hP.coeff_natDegree, mul_one]
  have hchoose : (n.choose d : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hd.le).ne'
  have hdeg : Q.natDegree = n - d :=
    (natDegree_hasseDeriv_le P d).antisymm (le_natDegree_of_ne_zero (hcoeff ▸ hchoose))
  have hlead : Q.leadingCoeff = (n.choose d : E) := by rw [Polynomial.leadingCoeff, hdeg, hcoeff]
  have hsplit : Q.Splits := IsAlgClosed.splits Q
  have hne : Q.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    exact hsplit.roots_ne_zero (by omega)
  obtain ⟨β, hβ, hmin⟩ := Q.roots.toFinset.exists_min_image (fun γ ↦ ‖α - γ‖) hne
  rw [Multiset.mem_toFinset] at hβ
  refine ⟨β, (mem_roots (ne_zero_of_natDegree_gt (n := 0) (by omega))).mp hβ, ?_⟩
  have hcard : Multiset.card Q.roots = n - d := by
    rw [← hdeg, ← splits_iff_card_roots.mp hsplit]
  calc ‖(n.choose d : E)‖ * ‖α - β‖ ^ (n - d)
      = ‖(n.choose d : E)‖ * (Q.roots.map fun _ ↦ ‖α - β‖).prod := by
        rw [Multiset.map_const', Multiset.prod_replicate, hcard]
    _ ≤ ‖(n.choose d : E)‖ * (Q.roots.map fun γ ↦ ‖α - γ‖).prod := by
        gcongr
        exact Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ norm_nonneg _)
          fun γ hγ ↦ hmin γ (Multiset.mem_toFinset.mpr hγ)
    _ = ‖Q.eval α‖ := by
        rw [hsplit.eval_eq_prod_roots, norm_mul, hlead, Multiset.norm_prod, Multiset.map_map,
          Function.comp_def]
    _ ≤ r ^ (n - d) := hP.norm_eval_hasseDeriv_le (IsAlgClosed.splits P) hr d

end Polynomial.Monic

namespace TauCeti

section Exponent

/-- The loss in the Ax–Sen lemma for elements of degree at most `n`, in additive normalization:
`∑_{j < log_p n} 1 / ((p - 1) p ^ j)`, one term for each power `p ^ (j + 1) ≤ n`. -/
private noncomputable def axSenExponent (p n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log p n), 1 / ((p - 1 : ℝ) * p ^ j)

variable {p : ℕ} (hp : p.Prime)
include hp

private theorem axSenExponent_term_nonneg (j : ℕ) : 0 ≤ 1 / ((p - 1 : ℝ) * p ^ j) := by
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  positivity

private theorem axSenExponent_nonneg (n : ℕ) : 0 ≤ axSenExponent p n :=
  Finset.sum_nonneg fun j _ ↦ axSenExponent_term_nonneg hp j

private theorem axSenExponent_mono {m n : ℕ} (h : m ≤ n) : axSenExponent p m ≤ axSenExponent p n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.log_mono_right h))
    fun j _ _ ↦ axSenExponent_term_nonneg hp j

/-- Passing below the power `p ^ (k + 1) ≤ n` costs the term `1 / ((p - 1) p ^ k)`. -/
private theorem axSenExponent_add_le {k m n : ℕ} (hm : m < p ^ (k + 1)) (hn : p ^ (k + 1) ≤ n) :
    axSenExponent p m + 1 / ((p - 1 : ℝ) * p ^ k) ≤ axSenExponent p n := by
  calc axSenExponent p m + 1 / ((p - 1 : ℝ) * p ^ k)
      ≤ axSenExponent p (p ^ k) + 1 / ((p - 1 : ℝ) * p ^ k) := by
        gcongr
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · exact axSenExponent_mono hp (Nat.zero_le _)
        · unfold axSenExponent
          rw [Nat.log_pow hp.one_lt]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hm0.ne' hm)))
            fun j _ _ ↦ axSenExponent_term_nonneg hp j
    _ = axSenExponent p (p ^ (k + 1)) := by
        simp only [axSenExponent, Nat.log_pow hp.one_lt, Finset.sum_range_succ]
    _ ≤ axSenExponent p n := axSenExponent_mono hp hn

/-- The loss never exceeds `p / (p - 1) ^ 2`. -/
private theorem axSenExponent_le (n : ℕ) : axSenExponent p n ≤ p / (p - 1 : ℝ) ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hq1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 0) (n := Nat.log p n) hq0 hq1
  rw [← Finset.range_eq_Ico, pow_zero] at hgeom
  calc axSenExponent p n = (p - 1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (Nat.log p n), (p : ℝ)⁻¹ ^ j := by
        rw [axSenExponent, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [one_div, mul_inv, inv_pow]
    _ ≤ (p - 1 : ℝ)⁻¹ * (1 / (1 - (p : ℝ)⁻¹)) := by
        gcongr
    _ = p / (p - 1 : ℝ) ^ 2 := by
        field_simp

end Exponent

section AxSen

variable {F E : Type*} [Field F] [NormedField E] [Algebra F E]

/-- If `β` is within `s` of `α`, and every conjugate of `α` is within `r ≤ s` of `α`, then
every conjugate of `β` is within `s` of `β`. -/
private theorem norm_smul_sub_le_of_norm_sub_le [IsUltrametricDist E]
    [IsIsometricSMul Gal(E/F) E] {α β : E} {r s : ℝ}
    (hα : ∀ σ : Gal(E/F), ‖σ • α - α‖ ≤ r) (hαβ : ‖α - β‖ ≤ s) (hrs : r ≤ s) (σ : Gal(E/F)) :
    ‖σ • β - β‖ ≤ s := by
  rw [← dist_eq_norm] at hαβ ⊢
  calc dist (σ • β) β ≤ max (dist (σ • β) (σ • α)) (max (dist (σ • α) α) (dist α β)) :=
        (dist_triangle_max _ _ _).trans (max_le_max le_rfl (dist_triangle_max _ _ _))
    _ ≤ s := by
        rw [dist_smul, dist_comm, dist_eq_norm (σ • α)]
        exact max_le hαβ (max_le ((hα σ).trans hrs) hαβ)

/-- **A root of a Hasse derivative of the minimal polynomial.** If every conjugate of `α` lies
within `r` of `α`, and `d` is less than the degree `n` of `α`, then some `β` of degree at most
`n - d` satisfies `‖n.choose d‖ * ‖α - β‖ ^ (n - d) ≤ r ^ (n - d)`: a root of the `d`-th Hasse
derivative of the minimal polynomial of `α`. -/
private theorem exists_norm_sub_pow_le_of_lt_natDegree [IsUltrametricDist E] [CharZero E]
    [IsAlgClosed E] [Algebra.IsAlgebraic F E] {α : E} {r : ℝ}
    (hα : ∀ σ : Gal(E/F), ‖σ • α - α‖ ≤ r) {d : ℕ} (hd : d < (minpoly F α).natDegree) :
    ∃ β : E, ‖((minpoly F α).natDegree.choose d : E)‖ * ‖α - β‖ ^ ((minpoly F α).natDegree - d) ≤
      r ^ ((minpoly F α).natDegree - d) ∧
      (minpoly F β).natDegree ≤ (minpoly F α).natDegree - d := by
  have hαi := Algebra.IsIntegral.isIntegral (R := F) α
  set P := (minpoly F α).map (algebraMap F E)
  have hP : P.Monic := (minpoly.monic hαi).map _
  have hPdeg : P.natDegree = (minpoly F α).natDegree := natDegree_map _
  -- The roots of `P` are the conjugates of `α`, as `E` is normal over `F`.
  have : IsAlgClosure F E := ⟨inferInstance, inferInstance⟩
  have hr : ∀ β ∈ P.roots, ‖β - α‖ ≤ r := fun β hβ ↦ by
    rw [mem_roots (map_ne_zero (minpoly.ne_zero hαi)), IsRoot, eval_map_algebraMap] at hβ
    obtain ⟨σ, rfl⟩ := minpoly.exists_algEquiv_of_root' hαi.isAlgebraic hβ
    exact hα σ
  obtain ⟨β, hβ, hle⟩ := hP.exists_isRoot_hasseDeriv_norm_sub_le hr (hPdeg ▸ hd)
  rw [hPdeg] at hle
  refine ⟨β, hle, ?_⟩
  -- The `d`-th Hasse derivative of the minimal polynomial has coefficients in `F` and is nonzero,
  -- its coefficient of degree `n - d` being `n.choose d`.
  have hmap : (hasseDeriv d (minpoly F α)).map (algebraMap F E) = hasseDeriv d P :=
    (hasseDeriv_map _ _ _).symm
  have hne : hasseDeriv d (minpoly F α) ≠ 0 := by
    intro h0
    have hcoeff := congrArg (fun q : E[X] ↦ q.coeff ((minpoly F α).natDegree - d)) hmap
    simp only [h0, Polynomial.map_zero, coeff_zero, hasseDeriv_coeff, ← hPdeg,
      Nat.sub_add_cancel (hPdeg ▸ hd).le, hP.coeff_natDegree, mul_one] at hcoeff
    exact Nat.cast_ne_zero.mpr (Nat.choose_pos (hPdeg ▸ hd).le).ne' hcoeff.symm
  have hroot : aeval β (hasseDeriv d (minpoly F α)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hmap]
    exact hβ
  exact (natDegree_le_natDegree (minpoly.degree_le_of_ne_zero F β hne hroot)).trans
    (natDegree_hasseDeriv_le _ _)

/-- **One step of Ax's induction.** An element `α` of degree at least two whose conjugates lie
within `r` of `α` is within `‖p‖ ^ (-ℓ) * r` of an element `β` of smaller degree, where the loss
`ℓ ≥ 0` is paid for by the drop in degree. -/
private theorem exists_natDegree_minpoly_lt [IsUltrametricDist E] [CharZero E] [IsAlgClosed E]
    [Algebra.IsAlgebraic F E] {p : ℕ} (hp : p.Prime) (hpE : ‖(p : E)‖ < 1) {α : E} {r : ℝ}
    (hα : ∀ σ : Gal(E/F), ‖σ • α - α‖ ≤ r) (h2 : 2 ≤ (minpoly F α).natDegree) :
    ∃ β : E, ∃ ℓ : ℝ, 0 ≤ ℓ ∧ (minpoly F β).natDegree < (minpoly F α).natDegree ∧
      axSenExponent p (minpoly F β).natDegree + ℓ ≤ axSenExponent p (minpoly F α).natDegree ∧
      ‖α - β‖ ≤ ‖(p : E)‖ ^ (-ℓ) * r := by
  set n := (minpoly F α).natDegree
  have hαi := Algebra.IsIntegral.isIntegral (R := F) α
  have hr0 : 0 ≤ r := by simpa using hα 1
  have key (d : ℕ) (hd : d < n) : ∃ β : E,
      ‖(n.choose d : E)‖ * ‖α - β‖ ^ (n - d) ≤ r ^ (n - d) ∧ (minpoly F β).natDegree ≤ n - d :=
    exists_norm_sub_pow_le_of_lt_natDegree hα hd
  have hn0 : n ≠ 0 := (minpoly.natDegree_pos hαi).ne'
  have hvn : p ^ n.factorization p ≤ n := Nat.ordProj_le p hn0
  have hpv : 0 < p ^ n.factorization p := pow_pos hp.pos _
  rcases hvn.lt_or_eq with hlt | heq
  · -- `n` is not a power of `p`: no loss.
    obtain ⟨β, hle, hdeg⟩ := key _ hlt
    rw [IsUltrametricDist.norm_natCast_eq_one_of_not_dvd hp hpE
      (Nat.not_dvd_choose_pow_factorization hp hn0), one_mul] at hle
    have hαβ : ‖α - β‖ ≤ r := (pow_le_pow_iff_left₀ (norm_nonneg _) hr0 (by omega)).mp hle
    refine ⟨β, 0, le_rfl, by omega, ?_, by simpa using hαβ⟩
    simpa using axSenExponent_mono hp (hdeg.trans (Nat.sub_le _ _))
  · -- `n = p ^ (k + 1)`: take `d = p ^ k`, losing `1 / (n - d)`.
    obtain ⟨k, hk⟩ : ∃ k, n.factorization p = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero fun h ↦ by rw [h, pow_zero] at heq; omega
    rw [hk] at heq
    have hp1 := hp.one_lt
    have hd : p ^ k < n := heq ▸ Nat.pow_lt_pow_right hp1 (by omega)
    obtain ⟨β, hle, hdeg⟩ := key _ hd
    have hc0 : 0 < ‖(p : E)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
    rw [← heq, IsUltrametricDist.norm_choose_prime_pow_succ hp hpE, heq] at hle
    have hN : ((n - p ^ k : ℕ) : ℝ) = (p - 1 : ℝ) * p ^ k := by
      rw [Nat.cast_sub hd.le, ← heq]
      push_cast
      ring
    have hpk : 0 < p ^ k := pow_pos hp.pos k
    have hN0 : 0 < n - p ^ k := by omega
    refine ⟨β, 1 / ((p - 1 : ℝ) * p ^ k), axSenExponent_term_nonneg hp k,
      hdeg.trans_lt (by omega), axSenExponent_add_le hp (hdeg.trans_lt (by omega)) heq.le, ?_⟩
    -- From `‖p‖ * ‖α - β‖ ^ N ≤ r ^ N` with `N = n - p ^ k`.
    by_contra! hgt
    have hpow := pow_lt_pow_left₀ hgt (by positivity) hN0.ne'
    rw [mul_pow, ← Real.rpow_mul_natCast hc0.le, hN, ← hN] at hpow
    have h1 : -(1 / ((n - p ^ k : ℕ) : ℝ)) * ((n - p ^ k : ℕ) : ℝ) = -1 := by
      field_simp
    rw [h1, Real.rpow_neg_one] at hpow
    have := mul_lt_mul_of_pos_left hpow hc0
    rw [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul] at this
    exact (hle.trans_lt this).false

variable [IsUltrametricDist E] [CharZero E] [IsAlgClosed E] [Algebra.IsAlgebraic F E]
  [IsIsometricSMul Gal(E/F) E] {p : ℕ} (hp : p.Prime) (hpE : ‖(p : E)‖ < 1)
include hp hpE

/-- Ax's induction on the degree: the loss for elements of degree at most `n` is at most
`axSenExponent p n`. -/
private theorem exists_norm_sub_algebraMap_le_rpow_axSenExponent (n : ℕ) :
    ∀ (α : E) (r : ℝ), (minpoly F α).natDegree ≤ n → (∀ σ : Gal(E/F), ‖σ • α - α‖ ≤ r) →
      ∃ a : F, ‖α - algebraMap F E a‖ ≤ ‖(p : E)‖ ^ (-axSenExponent p n) * r := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α r hn hα
  have hc0 : 0 < ‖(p : E)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hr0 : 0 ≤ r := by simpa using hα 1
  have hαi := Algebra.IsIntegral.isIntegral (R := F) α
  rcases lt_or_ge (minpoly F α).natDegree 2 with h1 | h2
  · -- `α` has degree one, so it lies in `F`.
    have hdeg1 : (minpoly F α).natDegree = 1 := by
      have := minpoly.natDegree_pos hαi
      omega
    obtain ⟨a, rfl⟩ := minpoly.natDegree_eq_one_iff.mp hdeg1
    exact ⟨a, by simpa using mul_nonneg (Real.rpow_nonneg hc0.le _) hr0⟩
  · obtain ⟨β, ℓ, hℓ, hdeg, hexp, hαβ⟩ := exists_natDegree_minpoly_lt hp hpE hα h2
    have hβ := norm_smul_sub_le_of_norm_sub_le hα hαβ (le_mul_of_one_le_left hr0
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc0 hpE.le (neg_nonpos.mpr hℓ)))
    obtain ⟨a, ha⟩ := ih _ (hdeg.trans_le hn) β _ le_rfl hβ
    have hexp' := hexp.trans (axSenExponent_mono hp hn)
    have hnn := axSenExponent_nonneg hp (minpoly F β).natDegree
    refine ⟨a, ?_⟩
    calc ‖α - algebraMap F E a‖ = ‖(α - β) + (β - algebraMap F E a)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ max ‖α - β‖ ‖β - algebraMap F E a‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖(p : E)‖ ^ (-axSenExponent p n) * r := by
          refine max_le (hαβ.trans ?_) (ha.trans ?_)
          · exact mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_ge hc0 hpE.le (by linarith)) hr0
          · rw [← mul_assoc, ← Real.rpow_add hc0]
            exact mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_ge hc0 hpE.le (by linarith)) hr0

/-- **The Ax–Sen lemma.** Let `E` be an algebraically closed ultrametric normed field of
characteristic zero, algebraic over a subfield `F`, on which every `F`-automorphism acts by
isometries, and let `p` be a prime with `‖p‖ < 1` in `E`. If every conjugate `σ • α` of `α ∈ E`
over `F` lies within `r` of `α`, then `α` lies within `‖p‖ ^ (-p / (p - 1) ^ 2) * r` of an element
of `F`. In additive notation with `v(p) = 1`: `v(α - a) ≥ inf_σ v(σ α - α) - p / (p - 1) ^ 2`. -/
theorem exists_norm_sub_algebraMap_le_of_forall_norm_smul_sub_le {α : E} {r : ℝ}
    (hα : ∀ σ : Gal(E/F), ‖σ • α - α‖ ≤ r) :
    ∃ a : F, ‖α - algebraMap F E a‖ ≤ ‖(p : E)‖ ^ (-((p : ℝ) / (p - 1) ^ 2)) * r := by
  have hc0 : 0 < ‖(p : E)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hr0 : 0 ≤ r := by simpa using hα 1
  obtain ⟨a, ha⟩ := exists_norm_sub_algebraMap_le_rpow_axSenExponent hp hpE _ α r le_rfl hα
  exact ⟨a, ha.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hc0 hpE.le
    (neg_le_neg (axSenExponent_le hp _))) hr0)⟩

end AxSen

end TauCeti
