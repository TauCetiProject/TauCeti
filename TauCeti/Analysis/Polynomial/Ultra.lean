/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.Normed.Unbundled.RootBound
import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Polynomial bounds over ultrametric rings

Weighted coefficient bounds `‖p.coeff n‖ * c ^ n ≤ B` at a nonnegative radius `c` behave
predictably under polynomial operations:
* Over any seminormed ring, left scalar multiplication scales a single-degree bound by `‖a‖`
  (`Polynomial.norm_coeff_smul_mul_pow_le`), rescaling from `0 < ϱ ≤ B` on a polynomial of natural
  degree at most `d` multiplies a bound `C` by `(B / ϱ) ^ d`
  (`Polynomial.norm_coeff_mul_pow_le_of_natDegree_le`), and when `‖1‖ = 1` a linear factor
  `X - C a` with `‖a‖ ≤ c` has `c`-weighted coefficients bounded by `c`
  (`Polynomial.norm_coeff_X_sub_C_mul_pow_le`).
* Over an ultrametric seminormed ring, a common bound `B` is preserved under finite sums
  (`Polynomial.norm_coeff_sum_mul_pow_le`) and Taylor shifts `p(X + r)` by points `r` with
  `‖r‖ ≤ c` (`Polynomial.norm_coeff_taylor_mul_pow_le`), while bounds `Bp` and `Bq` multiply to
  `Bp * Bq` on `p * q` (`Polynomial.norm_coeff_mul_mul_pow_le`), give `B ^ m` on `p ^ m` when
  `‖1‖ = 1` (`Polynomial.norm_coeff_pow_mul_pow_le`,
  `Polynomial.norm_coeff_X_sub_C_pow_mul_pow_le`), and give `∏ i ∈ s, B i` on finite products when
  `R` is commutative with `‖1‖ = 1` (`Polynomial.norm_coeff_prod_mul_pow_le`).

Over an ultrametric seminormed commutative ring with `‖1‖ = 1`, let `p a` be polynomials of
degree at most one whose constant coefficients have norm at most one and whose linear
coefficients have norm at most `r a`. The `m`-th coefficient of `∏ a ∈ s, p a` is a sum of
products of `m` linear and `#s - m` constant coefficients, so the ultrametric inequality bounds
it by every common bound for the products `∏ a ∈ t, r a` over the `m`-element subsets `t` of `s`
(`TauCeti.norm_coeff_prod_le_of_natDegree_le_one`). Applied to the Leibniz expansion, this
bounds the coefficients of determinants such as `det (1 - X A)` and of the adjugate of
`1 - X A`.

An integral polynomial has norm at most one on the closed unit ball of an ultrametric
seminormed ring with `‖1‖ = 1` (`Polynomial.norm_aeval_le_one`).

Over an ultrametric seminormed integral domain with `‖1‖ = 1`, let `P` be a split monic
polynomial of degree `n` all of whose roots lie within `r` of a point `α`. The value at `α` of the
`d`-th Hasse derivative of `P` is the coefficient of `Y ^ d` in `P(α + Y) = ∏ (Y - (αᵢ - α))`, so
it has norm at most `r ^ (n - d)` (`Polynomial.Monic.norm_eval_hasseDeriv_le`). If moreover the
norm is multiplicative, that Hasse derivative splits and its leading coefficient `n.choose d` is
nonzero, the product of the distances from `α` to its roots shows that one of them, `β`,
satisfies `‖n.choose d‖ * ‖α - β‖ ^ (n - d) ≤ r ^ (n - d)`
(`Polynomial.Monic.exists_isRoot_hasseDeriv_norm_sub_le`). These are the estimates in Ax's proof
of the Ax–Sen lemma.

## References

* J. Ax, *Zeros of polynomials over local fields — the Galois action*, J. Algebra 15 (1970),
  417–428.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
-/

public section

open Finset Polynomial

namespace Polynomial

/-- An integral polynomial evaluated at a point of the closed unit ball of a non-archimedean
seminormed ring with `‖1‖ = 1` has norm at most one. -/
theorem norm_aeval_le_one {K : Type*} [SeminormedRing K] [NormOneClass K] [IsUltrametricDist K]
    (p : ℤ[X]) {x : K} (hx : ‖x‖ ≤ 1) : ‖aeval x p‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ ?_
  exact (IsUltrametricDist.norm_zsmul_le (x ^ i) (p.coeff i)).trans
    ((norm_pow_le x i).trans (pow_le_one₀ (norm_nonneg _) hx))

section WeightedCoeff

variable {R : Type*} [SeminormedRing R]

/-- Left multiplication of a polynomial by a scalar multiplies a weighted coefficient bound at a
nonnegative radius `c` by the norm of the scalar. -/
theorem norm_coeff_smul_mul_pow_le (a : R) {p : R[X]} {c B : ℝ} (hc : 0 ≤ c) {n : ℕ}
    (hp : ‖p.coeff n‖ * c ^ n ≤ B) :
    ‖(a • p).coeff n‖ * c ^ n ≤ ‖a‖ * B := by
  rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  calc ‖a * p.coeff n‖ * c ^ n ≤ ‖a‖ * ‖p.coeff n‖ * c ^ n :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (pow_nonneg hc n)
    _ = ‖a‖ * (‖p.coeff n‖ * c ^ n) := mul_assoc _ _ _
    _ ≤ ‖a‖ * B := mul_le_mul_of_nonneg_left hp (norm_nonneg a)

/-- The `c`-weighted coefficients of `X - C a` are bounded by `c` whenever `‖a‖ ≤ c`. -/
theorem norm_coeff_X_sub_C_mul_pow_le [NormOneClass R] {a : R} {c : ℝ} (ha : ‖a‖ ≤ c) (n : ℕ) :
    ‖(X - C a).coeff n‖ * c ^ n ≤ c := by
  have hc : 0 ≤ c := (norm_nonneg a).trans ha
  rcases n with _ | _ | n
  · simpa [coeff_X] using ha
  · simp [coeff_X]
  · simp [coeff_X, hc]

/-- For a polynomial `p` of natural degree at most `d`, a `ϱ`-weighted bound `C` on `p.coeff n`
(`0 < ϱ ≤ B`) rescales to the `B`-weighted bound `C * (B / ϱ) ^ d`. -/
theorem norm_coeff_mul_pow_le_of_natDegree_le {p : R[X]} {ϱ B C : ℝ} (hϱ0 : 0 < ϱ)
    (hϱB : ϱ ≤ B) {d : ℕ} (hd : p.natDegree ≤ d) {n : ℕ} (hp : ‖p.coeff n‖ * ϱ ^ n ≤ C) :
    ‖p.coeff n‖ * B ^ n ≤ C * (B / ϱ) ^ d := by
  have hC0 : 0 ≤ C := (mul_nonneg (norm_nonneg _) (pow_nonneg hϱ0.le n)).trans hp
  have hBϱ0 : 0 ≤ B / ϱ := div_nonneg (hϱ0.le.trans hϱB) hϱ0.le
  by_cases hn : n ≤ d
  · have hBϱ : B ^ n = ϱ ^ n * (B / ϱ) ^ n := by rw [← mul_pow, mul_div_cancel₀ _ hϱ0.ne']
    rw [hBϱ, ← mul_assoc]
    exact mul_le_mul hp (pow_le_pow_right₀ ((one_le_div hϱ0).2 hϱB) hn) (pow_nonneg hBϱ0 n) hC0
  · rw [coeff_eq_zero_of_natDegree_lt (hd.trans_lt (not_le.1 hn)), norm_zero, zero_mul]
    exact mul_nonneg hC0 (pow_nonneg hBϱ0 d)

variable [IsUltrametricDist R]

/-- Over an ultrametric seminormed ring, a common nonnegative bound on the `n`-th `c`-weighted
coefficients of a finite family of polynomials bounds the `n`-th `c`-weighted coefficient of their
sum. -/
theorem norm_coeff_sum_mul_pow_le {ι : Type*} (s : Finset ι) (f : ι → R[X]) {c B : ℝ}
    (hc : 0 ≤ c) (hB : 0 ≤ B) {n : ℕ} (hf : ∀ i ∈ s, ‖(f i).coeff n‖ * c ^ n ≤ B) :
    ‖(∑ i ∈ s, f i).coeff n‖ * c ^ n ≤ B := by
  rw [finsetSum_coeff]
  exact IsUltrametricDist.norm_sum_mul_le_of_forall_le (pow_nonneg hc n) hB hf

/-- Over an ultrametric seminormed ring, bounds `Bp` and `Bq` on the `c`-weighted coefficients of
`p` and `q` at `c ≥ 0` multiply to bound the `c`-weighted coefficients of `p * q`. -/
theorem norm_coeff_mul_mul_pow_le {p q : R[X]} {c Bp Bq : ℝ} (hc : 0 ≤ c)
    (hp : ∀ n, ‖p.coeff n‖ * c ^ n ≤ Bp) (hq : ∀ n, ‖q.coeff n‖ * c ^ n ≤ Bq) (n : ℕ) :
    ‖(p * q).coeff n‖ * c ^ n ≤ Bp * Bq := by
  have hBp : 0 ≤ Bp := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hp 0)
  have hpf : (p : PowerSeries R).HasGaussNorm norm c :=
    ⟨Bp, Set.forall_mem_range.2 fun k ↦ by simpa using hp k⟩
  have hqf : (q : PowerSeries R).HasGaussNorm norm c :=
    ⟨Bq, Set.forall_mem_range.2 fun k ↦ by simpa using hq k⟩
  have hp_le : (p : PowerSeries R).gaussNorm norm c ≤ Bp :=
    (PowerSeries.gaussNorm_eq norm c _).trans_le (ciSup_le fun k ↦ by simpa using hp k)
  have hq_le : (q : PowerSeries R).gaussNorm norm c ≤ Bq :=
    (PowerSeries.gaussNorm_eq norm c _).trans_le (ciSup_le fun k ↦ by simpa using hq k)
  rw [← coeff_coe, Polynomial.coe_mul]
  exact (PowerSeries.le_gaussNorm norm c _
    (TauCeti.PowerSeries.hasGaussNorm_mul hc hpf hqf) n).trans
    ((TauCeti.PowerSeries.gaussNorm_mul_le hc hpf hqf).trans
      (mul_le_mul hp_le hq_le (PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg) hBp))

/-- Over an ultrametric seminormed ring with `‖1‖ = 1`, a bound `B` on the `c`-weighted
coefficients of `p` at `c ≥ 0` gives the bound `B ^ m` on those of `p ^ m`. -/
theorem norm_coeff_pow_mul_pow_le [NormOneClass R] {p : R[X]} {c B : ℝ} (hc : 0 ≤ c)
    (hp : ∀ n, ‖p.coeff n‖ * c ^ n ≤ B) (m n : ℕ) :
    ‖(p ^ m).coeff n‖ * c ^ n ≤ B ^ m := by
  induction m generalizing n with
  | zero => rcases n with _ | n <;> simp [coeff_one]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact norm_coeff_mul_mul_pow_le hc ih hp n

/-- The `c`-weighted coefficients of `(X - C a) ^ m` are bounded by `c ^ m` whenever `‖a‖ ≤ c`. -/
theorem norm_coeff_X_sub_C_pow_mul_pow_le [NormOneClass R] {a : R} {c : ℝ} (ha : ‖a‖ ≤ c)
    (m n : ℕ) : ‖((X - C a) ^ m).coeff n‖ * c ^ n ≤ c ^ m :=
  norm_coeff_pow_mul_pow_le ((norm_nonneg a).trans ha) (norm_coeff_X_sub_C_mul_pow_le ha) m n

/-- **Taylor invariance of ultrametric Gauss bounds.** Over an ultrametric seminormed ring,
shifting `p` to `taylor r p = p(X + r)` by a point `r` with `‖r‖ ≤ c` preserves any bound on its
`c`-weighted coefficients: natural-number multiples do not increase the norm in an ultrametric
seminormed ring. -/
theorem norm_coeff_taylor_mul_pow_le {p : R[X]} {r : R} {c B : ℝ} (hr : ‖r‖ ≤ c)
    (hp : ∀ n, ‖p.coeff n‖ * c ^ n ≤ B) (n : ℕ) :
    ‖(taylor r p).coeff n‖ * c ^ n ≤ B := by
  have hc : 0 ≤ c := (norm_nonneg r).trans hr
  have hB : 0 ≤ B := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hp 0)
  rw [coeff_taylor_eq_sum (Nat.lt_succ_self p.natDegree)]
  refine IsUltrametricDist.norm_sum_mul_le_of_forall_le (pow_nonneg hc n) hB fun k _ ↦ ?_
  calc ‖(k + n).choose n • (p.coeff (k + n) * r ^ k)‖ * c ^ n
      ≤ ‖p.coeff (k + n) * r ^ k‖ * c ^ n :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_nsmul_le _ _) (pow_nonneg hc n)
    _ ≤ ‖p.coeff (k + n)‖ * c ^ k * c ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hc n)
        exact (TauCeti.norm_mul_pow_le _ _ _).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg r) hr k) (norm_nonneg _))
    _ = ‖p.coeff (k + n)‖ * c ^ (k + n) := by rw [mul_assoc, ← pow_add]
    _ ≤ B := hp (k + n)

end WeightedCoeff

/-- Over an ultrametric seminormed commutative ring with `‖1‖ = 1`, bounds `B i` on the
`c`-weighted coefficients of a finite family `f i` at `c ≥ 0` multiply to bound the `c`-weighted
coefficients of `∏ i ∈ s, f i`. -/
theorem norm_coeff_prod_mul_pow_le {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]
    [IsUltrametricDist R] (s : Finset ι) (f : ι → R[X]) {c : ℝ} {B : ι → ℝ} (hc : 0 ≤ c)
    (hf : ∀ i ∈ s, ∀ n, ‖(f i).coeff n‖ * c ^ n ≤ B i) (n : ℕ) :
    ‖(∏ i ∈ s, f i).coeff n‖ * c ^ n ≤ ∏ i ∈ s, B i := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => rcases n with _ | n <;> simp [coeff_one]
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact norm_coeff_mul_mul_pow_le hc (hf i (mem_insert_self i s))
      (ih fun j hj ↦ hf j (mem_insert_of_mem hj)) n

end Polynomial


namespace TauCeti

/-- **Coefficients of a product of linear polynomials.** Over an ultrametric seminormed
commutative ring with `‖1‖ = 1`, let `p a` be polynomials of degree at most one with
`‖(p a).coeff 0‖ ≤ 1` and `‖(p a).coeff 1‖ ≤ r a`. If `c ≥ 0` bounds `∏ a ∈ t, r a` for every
`m`-element subset `t` of `s`, then `c` bounds the `m`-th coefficient of `∏ a ∈ s, p a`. -/
theorem norm_coeff_prod_le_of_natDegree_le_one {α R : Type*}
    [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
    {s : Finset α} {p : α → R[X]} {r : α → ℝ}
    (hdeg : ∀ a ∈ s, (p a).natDegree ≤ 1) (h₀ : ∀ a ∈ s, ‖(p a).coeff 0‖ ≤ 1)
    (h₁ : ∀ a ∈ s, ‖(p a).coeff 1‖ ≤ r a) {m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ t ⊆ s, t.card = m → ∏ a ∈ t, r a ≤ c) :
    ‖(∏ a ∈ s, p a).coeff m‖ ≤ c := by
  classical
  induction s using Finset.induction_on generalizing m c with
  | empty =>
    rcases m with _ | m
    · simpa using hs ∅ (empty_subset _) rfl
    · simpa [Polynomial.coeff_one] using hc
  | insert a s ha ih =>
    have hdeg' := fun b hb ↦ hdeg b (mem_insert_of_mem hb)
    have h₀' := fun b hb ↦ h₀ b (mem_insert_of_mem hb)
    have h₁' := fun b hb ↦ h₁ b (mem_insert_of_mem hb)
    have hra : ‖(p a).coeff 1‖ ≤ r a := h₁ a (mem_insert_self a s)
    -- Multiplying by `p a = p₁ X + p₀` mixes the coefficients of `∏ b ∈ s, p b` in degrees
    -- `m` and `m - 1`; the second one is weighted by `‖p₁‖ ≤ r a`.
    have hlow : ‖(p a).coeff 0 * (∏ b ∈ s, p b).coeff m‖ ≤ c :=
      (norm_mul_le _ _).trans <| (mul_le_of_le_one_left (norm_nonneg _)
        (h₀ a (mem_insert_self a s))).trans <|
          ih hdeg' h₀' h₁' hc fun t ht htm ↦ hs t (ht.trans (subset_insert a s)) htm
    rw [prod_insert ha, eq_X_add_C_of_natDegree_le_one (hdeg a (mem_insert_self a s)), add_mul,
      coeff_add, coeff_C_mul, mul_comm (C _), mul_assoc]
    rcases m with _ | k
    · simpa using hlow
    refine IsUltrametricDist.norm_add_le_max _ _ |>.trans (max_le ?_ hlow)
    rw [coeff_X_mul, coeff_C_mul]
    refine (norm_mul_le _ _).trans <| (mul_le_mul_of_nonneg_right hra (norm_nonneg _)).trans ?_
    rcases (norm_nonneg _).trans hra |>.eq_or_lt with hr | hr
    · simpa [← hr] using hc
    rw [← le_div_iff₀' hr]
    refine ih hdeg' h₀' h₁' (div_nonneg hc hr.le) fun t ht htk ↦ ?_
    have hat : a ∉ t := fun h ↦ ha (ht h)
    rw [le_div_iff₀' hr, ← prod_insert hat]
    exact hs _ (insert_subset_insert a ht) (by rw [card_insert_of_notMem hat, htk])

end TauCeti

namespace Polynomial.Monic

variable {E : Type*} [SeminormedCommRing E] [IsDomain E] [NormOneClass E] [IsUltrametricDist E]

/-- **Hasse derivatives near the roots.** If a monic polynomial `P` over an ultrametric seminormed
integral domain with `‖1‖ = 1` splits, and all its roots lie within `r` of a point `α`, then the
`d`-th Hasse derivative of `P` at `α` has norm at most `r ^ (natDegree P - d)`. It is the
coefficient of `Y ^ d` in `P(α + Y) = ∏ (Y - (αᵢ - α))`. -/
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

variable [NormMulClass E]

/-- **A root of a Hasse derivative near a point.** Let `P` be a split monic polynomial over an
ultrametric seminormed integral domain with a multiplicative norm and `‖1‖ = 1`, all of whose
roots lie within `r` of a point `α`, and let `d < n = natDegree P`. If the `d`-th Hasse
derivative of `P` splits and its leading coefficient `n.choose d` is nonzero, then it has a root
`β` with `‖n.choose d‖ * ‖α - β‖ ^ (n - d) ≤ r ^ (n - d)`. -/
theorem exists_isRoot_hasseDeriv_norm_sub_le {P : E[X]} (hP : P.Monic) (hsplit : P.Splits)
    {α : E} {r : ℝ} (hr : ∀ β ∈ P.roots, ‖β - α‖ ≤ r) {d : ℕ} (hd : d < P.natDegree)
    (hdsplit : (hasseDeriv d P).Splits) (hchoose : (P.natDegree.choose d : E) ≠ 0) :
    ∃ β, (hasseDeriv d P).IsRoot β ∧
      ‖(P.natDegree.choose d : E)‖ * ‖α - β‖ ^ (P.natDegree - d) ≤ r ^ (P.natDegree - d) := by
  classical
  set Q := hasseDeriv d P
  set n := P.natDegree
  have hcoeff : Q.coeff (n - d) = (n.choose d : E) := by
    rw [hasseDeriv_coeff, Nat.sub_add_cancel hd.le, hP.coeff_natDegree, mul_one]
  have hdeg : Q.natDegree = n - d :=
    (natDegree_hasseDeriv_le P d).antisymm (le_natDegree_of_ne_zero (hcoeff ▸ hchoose))
  have hlead : Q.leadingCoeff = (n.choose d : E) := by rw [Polynomial.leadingCoeff, hdeg, hcoeff]
  have hne : Q.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    exact hdsplit.roots_ne_zero (by omega)
  obtain ⟨β, hβ, hmin⟩ := Q.roots.toFinset.exists_min_image (fun γ ↦ ‖α - γ‖) hne
  rw [Multiset.mem_toFinset] at hβ
  refine ⟨β, (mem_roots (ne_zero_of_natDegree_gt (n := 0) (by omega))).mp hβ, ?_⟩
  have hcard : Multiset.card Q.roots = n - d := by
    rw [← hdeg, ← splits_iff_card_roots.mp hdsplit]
  calc ‖(n.choose d : E)‖ * ‖α - β‖ ^ (n - d)
      = ‖(n.choose d : E)‖ * (Q.roots.map fun _ ↦ ‖α - β‖).prod := by
        rw [Multiset.map_const', Multiset.prod_replicate, hcard]
    _ ≤ ‖(n.choose d : E)‖ * (Q.roots.map fun γ ↦ ‖α - γ‖).prod := by
        gcongr
        exact Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ norm_nonneg _)
          fun γ hγ ↦ hmin γ (Multiset.mem_toFinset.mpr hγ)
    _ = ‖Q.eval α‖ := by
        rw [hdsplit.eval_eq_prod_roots, norm_mul, hlead, Multiset.norm_prod, Multiset.map_map,
          Function.comp_def]
    _ ≤ r ^ (n - d) := hP.norm_eval_hasseDeriv_le hsplit hr d

end Polynomial.Monic
