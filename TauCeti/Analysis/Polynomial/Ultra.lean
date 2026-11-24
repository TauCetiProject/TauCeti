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
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import TauCeti.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Taylor
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.Normed.Unbundled.RootBound

/-!
# Polynomial bounds over ultrametric rings

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

Over an ultrametric seminormed commutative ring `K`, natural-number multiples satisfy
`‖n • a‖ ≤ ‖a‖`, so formal differentiation shifts polynomial coefficients down by one degree
without introducing factorial growth. Consequently, if `‖P.coeff i‖ * r ^ i ≤ B` for some `r > 0`,
each application of `Polynomial.expDerivFactor c 1 = D + c` multiplies this weighted bound by at
most `max r⁻¹ ‖c‖` (`Polynomial.norm_coeff_expDerivFactor_mul_pow_le`, with uniform specialization
`Polynomial.norm_coeff_expDerivFactor_le` and corresponding closed-ball evaluation bounds
`Polynomial.norm_eval_expDerivFactor_le_of_mul_pow_le` and
`Polynomial.norm_eval_expDerivFactor_le`).

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
* A. Baker, *Transcendental Number Theory*, Cambridge University Press (1975), Chapter 2.
* M. Karatarakis, `ExpSeries.lean` in `mkaratarakis/mathlib4`, commit
  `65cdef5722194f07709ab40ff46eede531f52f5d`, `Mathlib/NumberTheory/Transcendental/Baker/Padic/`.
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

section ExpDerivFactor

variable {K : Type*} [SeminormedCommRing K] [IsUltrametricDist K]

/-- In an ultrametric seminormed commutative ring, if `‖P.coeff i‖ * r ^ i ≤ B` for `r > 0`, then
each step of `expDerivFactor c m` multiplies the `r`-weighted coefficient bound by at most
`max r⁻¹ ‖c‖`. -/
theorem norm_coeff_expDerivFactor_mul_pow_le (c : K) {P : K[X]} {r B : ℝ} (hr : 0 < r)
    (hP : ∀ i, ‖P.coeff i‖ * r ^ i ≤ B) (m i : ℕ) :
    ‖(expDerivFactor c m P).coeff i‖ * r ^ i ≤ max r⁻¹ ‖c‖ ^ m * B := by
  have hB : 0 ≤ B := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hP 0)
  have : 0 ≤ max r⁻¹ ‖c‖ := le_max_of_le_right (norm_nonneg c)
  induction m generalizing i with
  | zero => simpa using hP i
  | succ m ih =>
    set Q := expDerivFactor c m P
    have hderiv : ‖Q.coeff (i + 1) * ((i : K) + 1)‖ ≤ ‖Q.coeff (i + 1)‖ := by
      have hnsmul : Q.coeff (i + 1) * ((i : K) + 1) = (i + 1) • Q.coeff (i + 1) := by
        rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm]
      rw [hnsmul]
      exact IsUltrametricDist.norm_nsmul_le _ _
    rw [expDerivFactor_succ_apply, coeff_add, coeff_derivative, coeff_C_mul]
    refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _)
      (by positivity)).trans ?_
    rw [max_mul_of_nonneg _ _ (by positivity), pow_succ', mul_assoc]
    refine max_le ?_ ?_
    · calc
        ‖Q.coeff (i + 1) * ((i : K) + 1)‖ * r ^ i
            ≤ ‖Q.coeff (i + 1)‖ * r ^ i := by gcongr
        _ = ‖Q.coeff (i + 1)‖ * r ^ i * (r⁻¹ * r) := by rw [inv_mul_cancel₀ hr.ne', mul_one]
        _ = r⁻¹ * (‖Q.coeff (i + 1)‖ * r ^ (i + 1)) := by
            rw [pow_succ]
            ring
        _ ≤ r⁻¹ * (max r⁻¹ ‖c‖ ^ m * B) :=
            mul_le_mul_of_nonneg_left (ih (i + 1)) (by positivity)
        _ ≤ max r⁻¹ ‖c‖ * (max r⁻¹ ‖c‖ ^ m * B) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · calc
        ‖c * Q.coeff i‖ * r ^ i
            ≤ ‖c‖ * (‖Q.coeff i‖ * r ^ i) := by
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (by positivity)
        _ ≤ ‖c‖ * (max r⁻¹ ‖c‖ ^ m * B) :=
            mul_le_mul_of_nonneg_left (ih i) (norm_nonneg c)
        _ ≤ max r⁻¹ ‖c‖ * (max r⁻¹ ‖c‖ ^ m * B) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- In an ultrametric seminormed commutative ring, applying `expDerivFactor c m` multiplies a
uniform bound on the coefficients of `P` by at most `max 1 ‖c‖ ^ m`. -/
theorem norm_coeff_expDerivFactor_le (c : K) {P : K[X]} {B : ℝ}
    (hP : ∀ i, ‖P.coeff i‖ ≤ B) (m i : ℕ) :
    ‖(expDerivFactor c m P).coeff i‖ ≤ max 1 ‖c‖ ^ m * B := by
  simpa using norm_coeff_expDerivFactor_mul_pow_le c one_pos (by simpa using hP) m i

/-- Ultrametric evaluation bound for `expDerivFactor c m P` on the closed ball `‖x‖ ≤ r` (`r > 0`)
from an `r`-weighted coefficient bound on `P`. -/
theorem norm_eval_expDerivFactor_le_of_mul_pow_le (c : K) {P : K[X]} {r B : ℝ} (hr : 0 < r)
    (hP : ∀ i, ‖P.coeff i‖ * r ^ i ≤ B) (m : ℕ) {x : K} (hx : ‖x‖ ≤ r) :
    ‖(expDerivFactor c m P).eval x‖ ≤ max r⁻¹ ‖c‖ ^ m * B := by
  have hB : 0 ≤ B := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hP 0)
  have : 0 ≤ max r⁻¹ ‖c‖ := le_max_of_le_right (norm_nonneg c)
  rw [eval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ ↦ ?_
  calc
    ‖(expDerivFactor c m P).coeff i * x ^ i‖
        ≤ ‖(expDerivFactor c m P).coeff i‖ * ‖x‖ ^ i := TauCeti.norm_mul_pow_le _ _ _
    _ ≤ ‖(expDerivFactor c m P).coeff i‖ * r ^ i := by gcongr
    _ ≤ max r⁻¹ ‖c‖ ^ m * B := norm_coeff_expDerivFactor_mul_pow_le c hr hP m i

/-- Ultrametric evaluation bound for `expDerivFactor c m P` on the closed unit ball `‖x‖ ≤ 1`. -/
theorem norm_eval_expDerivFactor_le (c : K) {P : K[X]} {B : ℝ}
    (hP : ∀ i, ‖P.coeff i‖ ≤ B) (m : ℕ) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖(expDerivFactor c m P).eval x‖ ≤ max 1 ‖c‖ ^ m * B := by
  simpa using norm_eval_expDerivFactor_le_of_mul_pow_le c one_pos (by simpa using hP) m hx

end ExpDerivFactor

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
