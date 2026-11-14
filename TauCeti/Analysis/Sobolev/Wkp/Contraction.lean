/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Multilinear
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import Mathlib.GroupTheory.Perm.Fin

/-!
# Iterated directional derivatives, contractions, and all-order symmetry on `W^{k,p}`

`TauCeti.Wkp.lineDerivL v k` differentiates a Sobolev function in `W^{k+1,p}(Ω)` along a direction
`v : E`, landing in `W^{k,p}(Ω)`. Because `TauCeti.Wkp` records weak derivatives from the bottom up
while `TauCeti.IteratedGradient.contractL` contracts direction slots from the outside in, comparing
the highest derivative of `∂_v u` with the outer contraction `(D^{j+2} u)⟨v⟩¹` uses symmetry of
adjacent weak derivatives (`TauCeti.HasWeakLineDerivOn.comm`). Carrying this comparison through all
orders gives the full algebra of bundled directional derivatives on `W^{k,p}(Ω)`:

* **Outer contraction of iterated gradients** (`TauCeti.Wkp.iteratedGradient_lineDerivL`). For
  `u ∈ W^{j+2,p}(Ω)` and `v : E`, the highest weak derivative of `lineDerivL v (j + 1) u` is
  `(IteratedGradient.contractL j 1 v).compLp (iteratedGradient (j + 1) u)`.
* **Operator-norm bounds**. Each derivative component satisfies the bound with constant `1`
  (`TauCeti.Wkp.norm_lineDerivL_zero_apply_le`, `TauCeti.Wkp.norm_iteratedGradient_lineDerivL_le`).
  In the full Sobolev graph norm, the constant is `1` at `k = 0` and for `p = 2` at every order
  (`TauCeti.Wkp.norm_lineDerivL_two_le`), and `√2` for every `1 ≤ p ≤ ∞` and every `k`
  (`TauCeti.Wkp.norm_lineDerivL_le`, `TauCeti.Wkp.norm_lineDerivCLM_le`).
* **Iterated directional derivatives and all-order symmetry**. Iterating `lineDerivL` along a tuple
  `m : Fin j → E` defines `TauCeti.Wkp.iteratedLineDerivL` and its order-zero specialisation
  `TauCeti.Wkp.iteratedLineDerivZeroL`. Both are invariant under every permutation of the direction
  tuple (`TauCeti.Wkp.iteratedLineDerivL_comp_perm`,
  `TauCeti.Wkp.iteratedLineDerivZeroL_comp_perm`). At positive number of directions,
  `iteratedLineDerivZeroL (j + 1) m u` agrees with `(IteratedGradient.evalL j m).compLp` applied to
  `iteratedGradient j u` (`TauCeti.Wkp.iteratedLineDerivZeroL_succ_apply`), so every weak
  derivative field `iteratedGradient j u` is symmetric almost everywhere as a continuous
  multilinear form (`TauCeti.Wkp.domDomCongr_toContinuousMultilinearMapₗᵢ_iteratedGradient_ae`),
  and every directional evaluation `(D^{j+1} u)(m 0, …, m j)` of `u ∈ W^{k+j+1,p}(Ω)` is the value
  of an element of `W^{k,p}(Ω)` (`TauCeti.Wkp.value_iteratedLineDerivL_eq_evalL_compLp`).

No boundedness or boundary regularity of `Ω` is assumed.

## Main declarations

* `TauCeti.Wkp.iteratedGradient_lineDerivL`: `D^{j+1}(∂_v u) = (D^{j+2} u)⟨v⟩¹` in `Lᵖ(Ω)`.
* `TauCeti.Wkp.norm_lineDerivL_le` and `TauCeti.Wkp.norm_lineDerivL_two_le`: graph-norm bounds for
  `lineDerivL` (`√2 * ‖v‖` in general, `‖v‖` at `p = 2`).
* `TauCeti.Wkp.iteratedLineDerivL` and `TauCeti.Wkp.iteratedLineDerivZeroL`: iterated bundled
  directional derivatives along a tuple `Fin j → E`.
* `TauCeti.Wkp.iteratedLineDerivL_comp_perm`: permutation invariance of iterated directional
  derivatives.
* `TauCeti.Wkp.iteratedLineDerivZeroL_succ_apply` and
  `TauCeti.Wkp.value_iteratedLineDerivL_eq_evalL_compLp`: identification of iterated directional
  derivatives with multilinear evaluations of `Wkp.iteratedGradient`.
* `TauCeti.Wkp.domDomCongr_toContinuousMultilinearMapₗᵢ_iteratedGradient_ae`: almost-everywhere
  full symmetry of weak derivatives of arbitrary order.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.2.
* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, §4.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace ContDiff

section PermCombinator

/-- Auxiliary tuple identity expressing `m ∘ Equiv.swap 0 q.succ` via `Equiv.swap 0 1` and a tail
transposition `Equiv.swap 0 q`. -/
private theorem cons_tail_swap_eq_comp_swap_succ {α : Type*} {j : ℕ} (q : Fin (j + 1))
    (m : Fin (j + 2) → α) :
    (let m₁ := Fin.cons (α := fun _ => α) (m 0) (Fin.tail m ∘ Equiv.swap 0 q)
     let m₂ := m₁ ∘ Equiv.swap 0 1
     Fin.cons (α := fun _ => α) (m₂ 0) (Fin.tail m₂ ∘ Equiv.swap 0 q)) =
      m ∘ Equiv.swap 0 q.succ := by
  dsimp only
  funext x
  refine Fin.cases ?_ (fun y => ?_) x
  · simp [Fin.tail]
  · simp only [Fin.cons_succ, Function.comp_apply, Fin.tail]
    by_cases hy : y = q
    · subst hy
      simp [Fin.succ_zero_eq_one]
    · have hswap : Equiv.swap 0 q y ≠ 0 := by
        intro h0
        have hq := congrArg (Equiv.swap 0 q) h0
        simp only [Equiv.swap_apply_self, Equiv.swap_apply_left] at hq
        exact hy hq
      have hne1 : (Equiv.swap 0 q y).succ ≠ 1 := by
        rw [← Fin.succ_zero_eq_one]
        exact Fin.succ_inj.ne.2 hswap
      have hysucc : y.succ ≠ q.succ := Fin.succ_inj.ne.2 hy
      rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hne1, Fin.cons_succ,
        Function.comp_apply, Equiv.swap_apply_self,
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hysucc]
      rfl

/-- Any family of maps on tuples `Fin j → α` that respects permutations of `Fin.tail` and swaps of
the first two entries is invariant under every permutation of `Fin j`. -/
private theorem eq_comp_perm_of_tail_of_swap {α : Type*} {β : ℕ → Type*}
    (F : ∀ j, (Fin j → α) → β j)
    (htail : ∀ j (v : α) (m m' : Fin j → α), F j m = F j m' →
      F (j + 1) (Fin.cons v m) = F (j + 1) (Fin.cons v m'))
    (hswap : ∀ j (m : Fin (j + 2) → α), F (j + 2) (m ∘ Equiv.swap 0 1) = F (j + 2) m) :
    ∀ (j : ℕ) (m : Fin j → α) (σ : Equiv.Perm (Fin j)), F j (m ∘ σ) = F j m
  | 0, m, σ => by
      have hm : m ∘ σ = m := funext fun i => i.elim0
      rw [hm]
  | j + 1, m, σ => by
      have ih := eq_comp_perm_of_tail_of_swap F htail hswap j
      have h0 : ∀ (r : Fin (j + 1)) (m' : Fin (j + 1) → α),
          F (j + 1) (m' ∘ Equiv.swap 0 r) = F (j + 1) m' := by
        intro r
        refine Fin.cases (fun m' => by simp) (fun q m' => ?_) r
        cases j with
        | zero => exact q.elim0
        | succ j' =>
            let m₁ := Fin.cons (α := fun _ => α) (m' 0) (Fin.tail m' ∘ Equiv.swap 0 q)
            let m₂ := m₁ ∘ Equiv.swap 0 1
            have hm₁ : F (j' + 2) m₁ = F (j' + 2) m' := by
              simpa only [Fin.cons_self_tail] using
                htail (j' + 1) (m' 0) _ _ (ih (Fin.tail m') (Equiv.swap 0 q))
            have hm₂ : F (j' + 2) m₂ = F (j' + 2) m₁ := hswap j' m₁
            have hm₃ : F (j' + 2) (Fin.cons (α := fun _ => α) (m₂ 0)
                (Fin.tail m₂ ∘ Equiv.swap 0 q)) = F (j' + 2) m₂ := by
              simpa only [Fin.cons_self_tail] using
                htail (j' + 1) (m₂ 0) _ _ (ih (Fin.tail m₂) (Equiv.swap 0 q))
            rw [← cons_tail_swap_eq_comp_swap_succ q m', hm₃, hm₂, hm₁]
      set r := (Equiv.Perm.decomposeFin σ).1
      set e := (Equiv.Perm.decomposeFin σ).2
      have hσ : Equiv.Perm.decomposeFin.symm (r, e) = σ := by
        simpa only [Prod.mk.eta] using Equiv.Perm.decomposeFin.symm_apply_apply σ
      have hdecomp : m ∘ σ = Fin.cons (α := fun _ => α) ((m ∘ Equiv.swap 0 r) 0)
          (Fin.tail (m ∘ Equiv.swap 0 r) ∘ e) := by
        rw [← hσ]
        funext x
        refine Fin.cases ?_ (fun y => ?_) x <;> simp [Fin.tail]
      rw [hdecomp]
      refine (htail j ((m ∘ Equiv.swap 0 r) 0) _ _ (ih _ e)).trans ?_
      rw [Fin.cons_self_tail]
      exact h0 r m

end PermCombinator

section CompLp

private theorem compLp_comp {α F₁ F₂ F₃ : Type*} [MeasurableSpace α] {ν : Measure α}
    {p : ENNReal} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    (L₁ : F₂ →L[ℝ] F₃) (L₂ : F₁ →L[ℝ] F₂) (f : Lp F₁ p ν) :
    L₁.compLp (L₂.compLp f) = (L₁.comp L₂).compLp f := by
  apply Lp.ext
  filter_upwards [L₁.coeFn_compLp (L₂.compLp f), L₂.coeFn_compLp f,
    (L₁.comp L₂).coeFn_compLp f] with x h₁ h₂ h₁₂
  rw [h₁, h₂, h₁₂, ContinuousLinearMap.comp_apply]

end CompLp

namespace Wkp

section Sobolev

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Lowering the Sobolev order -/

/-- Every element of `W^{m,p}(Ω)` projects to an element of `W^{n,p}(Ω)` for `n ≤ m` with the same
`Lᵖ` value and norm at most `‖u‖`. -/
theorem exists_value_eq_of_le {n m : ℕ} (h : n ≤ m) (u : Wkp mu Omega p m) :
    ∃ u₀ : Wkp mu Omega p n, value m u = value n u₀ ∧ ‖u₀‖ ≤ ‖u‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact ⟨u, rfl, le_rfl⟩
  | succ k ih =>
      obtain ⟨u₀, hval, hnorm⟩ := ih (lowerOrder (n + k) u)
      exact ⟨u₀, (value_succ (n + k) u).trans hval, hnorm.trans (norm_lowerOrder_le (n + k) u)⟩

/-! ### Outer contraction of `iteratedGradient` under `lineDerivL` -/

/-- The two outermost direction slots of `iteratedGradient (j + 2) u` commute almost everywhere on
`Ω`. -/
theorem iteratedGradient_succ_swap_ae (j : ℕ) (u : Wkp mu Omega p (j + 3)) :
    ∀ᵐ x ∂mu.restrict Omega, ∀ v w : E,
      iteratedGradient (j + 2) u x v w = iteratedGradient (j + 2) u x w v := by
  have hpair (v w : E) :
      (fun x => iteratedGradient (j + 2) u x v w) =ᵐ[mu.restrict Omega]
        fun x => iteratedGradient (j + 2) u x w v := by
    have h₁ := hasWeakFDerivOn_iteratedGradient j (lowerOrder (j + 2) u)
    have h₂ := hasWeakFDerivOn_iteratedGradient (j + 1) u
    have hv := h₁.hasWeakLineDerivOn v
    have hw := h₁.hasWeakLineDerivOn w
    have hvw :=
      (h₂.clm_comp (ContinuousLinearMap.apply ℝ (IteratedGradient E j) v)).hasWeakLineDerivOn w
    have hwv :=
      (h₂.clm_comp (ContinuousLinearMap.apply ℝ (IteratedGradient E j) w)).hasWeakLineDerivOn v
    exact hwv.ae_eq (hv.comm hvw hw)
  let b := stdOrthonormalBasis ℝ E
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun l => hpair (b i) (b l)] with x hx v w
  have hvx : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have hwx : w = ∑ l, b.repr w l • b l := (b.sum_repr w).symm
  conv_lhs => rw [hvx, hwx]
  conv_rhs => rw [hvx, hwx]
  simp only [map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hx i l, mul_comm]

/-- **Outer contraction of `iteratedGradient` under `lineDerivL`.** For `u ∈ W^{j+2,p}(Ω)` and
`v : E`, the highest weak derivative of `lineDerivL v (j + 1) u` is obtained by contracting the
outermost direction slot of `iteratedGradient (j + 1) u` at `v`. -/
theorem iteratedGradient_lineDerivL (v : E) :
    ∀ (j : ℕ) (u : Wkp mu Omega p (j + 2)),
      iteratedGradient j (lineDerivL v (j + 1) u) =
        (IteratedGradient.contractL j 1 v).compLp (iteratedGradient (j + 1) u)
  | 0, u => by
      let d := lineDerivL v 1 u
      have hdval : value 1 d = (innerSL ℝ v).compLp (iteratedGradient 0 (lowerOrder 1 u)) := by
        rw [value_succ 0 d, value_zero, lowerOrder_lineDerivL, lineDerivL_zero_apply]
      have hfd : HasWeakFDerivOn mu Omega (value 1 d)
          (fun x => (innerSL ℝ v).comp (iteratedGradient 1 u x)) := by
        rw [hdval]
        exact ((hasWeakFDerivOn_iteratedGradient 0 u).clm_comp (innerSL ℝ v)).congr_ae
          ((innerSL ℝ v).coeFn_compLp' (iteratedGradient 0 (lowerOrder 1 u))).symm
      apply Lp.ext
      filter_upwards [(hasWeakFDerivOn_value d).ae_eq hfd, adjoint_iteratedGradient_one_ae_eq u,
        (IteratedGradient.contractL 0 1 v).coeFn_compLp (iteratedGradient 1 u)]
        with x heq hadj hcomp
      rw [hcomp, IteratedGradient.contractL_one_apply]
      refine ext_inner_left ℝ fun w => ?_
      have hw := congrArg (fun L : E →L[ℝ] ℝ => L w) heq
      simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at hw
      calc
        ⟪w, iteratedGradient 0 d x⟫_ℝ = ⟪iteratedGradient 0 d x, w⟫_ℝ := real_inner_comm _ _
        _ = ⟪v, iteratedGradient 1 u x w⟫_ℝ := hw
        _ = ⟪(iteratedGradient 1 u x).adjoint v, w⟫_ℝ :=
          (ContinuousLinearMap.adjoint_inner_left (iteratedGradient 1 u x) w v).symm
        _ = ⟪w, iteratedGradient 1 u x v⟫_ℝ := by rw [hadj, real_inner_comm]
  | j + 1, u => by
      let d := lineDerivL v (j + 2) u
      have hih : iteratedGradient j (lowerOrder (j + 1) d) =
          (IteratedGradient.contractL j 1 v).compLp
            (iteratedGradient (j + 1) (lowerOrder (j + 2) u)) := by
        rw [lowerOrder_lineDerivL, iteratedGradient_lineDerivL v j (lowerOrder (j + 2) u)]
      have hfd : HasWeakFDerivOn mu Omega (iteratedGradient j (lowerOrder (j + 1) d))
          (fun x => (IteratedGradient.contractL j 1 v).comp (iteratedGradient (j + 2) u x)) := by
        rw [hih]
        exact ((hasWeakFDerivOn_iteratedGradient (j + 1) u).clm_comp
          (IteratedGradient.contractL j 1 v)).congr_ae
          ((IteratedGradient.contractL j 1 v).coeFn_compLp' _).symm
      apply Lp.ext
      filter_upwards [(hasWeakFDerivOn_iteratedGradient j d).ae_eq hfd,
        iteratedGradient_succ_swap_ae j u,
        (IteratedGradient.contractL (j + 1) 1 v).coeFn_compLp (iteratedGradient (j + 2) u)]
        with x heq hswap hcomp
      rw [heq, hcomp, IteratedGradient.contractL_one_apply]
      ext w
      rw [ContinuousLinearMap.comp_apply, IteratedGradient.contractL_one_apply, hswap w v]

/-- Almost-everywhere pointwise form of `TauCeti.Wkp.iteratedGradient_lineDerivL`. -/
theorem iteratedGradient_lineDerivL_ae (v : E) (j : ℕ) (u : Wkp mu Omega p (j + 2)) :
    ∀ᵐ x ∂mu.restrict Omega,
      iteratedGradient j (lineDerivL v (j + 1) u) x = iteratedGradient (j + 1) u x v := by
  rw [iteratedGradient_lineDerivL]
  filter_upwards [(IteratedGradient.contractL j 1 v).coeFn_compLp (iteratedGradient (j + 1) u)]
    with x hx
  rw [hx, IteratedGradient.contractL_one_apply]

/-! ### Componentwise and graph-norm bounds -/

/-- At order zero, `lineDerivL v 0` is `fullContractL 0 v` applied to the weak gradient. -/
theorem lineDerivL_zero_eq_fullContractL_compLp (v : E) (u : Wkp mu Omega p 1) :
    lineDerivL v 0 u = (IteratedGradient.fullContractL 0 v).compLp (iteratedGradient 0 u) := by
  rw [IteratedGradient.fullContractL_zero, lineDerivL_zero_apply]

/-- Componentwise `Lᵖ` bound at order zero: `‖∂_v u‖_{Lᵖ} ≤ ‖v‖ ‖∇u‖_{Lᵖ}`. -/
theorem norm_lineDerivL_zero_apply_le (v : E) (u : Wkp mu Omega p 1) :
    ‖lineDerivL v 0 u‖ ≤ ‖v‖ * ‖iteratedGradient 0 u‖ := by
  rw [lineDerivL_zero_eq_fullContractL_compLp]
  have hv : ‖IteratedGradient.fullContractL 0 v‖ ≤ ‖v‖ :=
    (IteratedGradient.norm_fullContractL_le (E := E) 0 v).trans_eq (pow_one ‖v‖)
  exact ((IteratedGradient.fullContractL 0 v).norm_compLp_le _).trans
    (mul_le_mul_of_nonneg_right hv (norm_nonneg _))

/-- Operator-norm bound `‖lineDerivL v 0‖ ≤ ‖v‖` from `W^{1,p}(Ω)` to `Lᵖ(Ω)`. -/
theorem norm_lineDerivL_zero_le (v : E) :
    ‖lineDerivL (mu := mu) (Omega := Omega) (p := p) v 0‖ ≤ ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun u =>
    (norm_lineDerivL_zero_apply_le v u).trans
      (mul_le_mul_of_nonneg_left (norm_iteratedGradient_le 0 u) (norm_nonneg v))

/-- The `Lᵖ` norm of the value of `lineDerivL v k u` is at most `‖v‖` times the `Lᵖ` norm of the
weak gradient of `firstOrder k u`. -/
theorem norm_value_lineDerivL_le (v : E) (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    ‖value k (lineDerivL v k u)‖ ≤ ‖v‖ * ‖W1p.gradient (firstOrder k u)‖ := by
  rw [value_lineDerivL]
  have hv : ‖(innerSL ℝ v : E →L[ℝ] ℝ)‖ ≤ ‖v‖ := by
    rw [← IteratedGradient.fullContractL_zero]
    exact (IteratedGradient.norm_fullContractL_le (E := E) 0 v).trans_eq (pow_one ‖v‖)
  exact ((innerSL ℝ v).norm_compLp_le _).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))

/-- Componentwise `Lᵖ` bound on the highest weak derivative of `lineDerivL v (j + 1) u`. -/
theorem norm_iteratedGradient_lineDerivL_le (v : E) (j : ℕ) (u : Wkp mu Omega p (j + 2)) :
    ‖iteratedGradient j (lineDerivL v (j + 1) u)‖ ≤ ‖v‖ * ‖iteratedGradient (j + 1) u‖ := by
  rw [iteratedGradient_lineDerivL]
  have hv : ‖IteratedGradient.contractL (E := E) j 1 v‖ ≤ ‖v‖ :=
    (IteratedGradient.norm_contractL_le (E := E) j 1 v).trans_eq (pow_one ‖v‖)
  exact ((IteratedGradient.contractL j 1 v).norm_compLp_le _).trans
    (mul_le_mul_of_nonneg_right hv (norm_nonneg _))

/-- At exponent `p = 2`, `lineDerivL v k` has graph-norm bound `‖v‖ * ‖u‖` at every order `k`. -/
theorem norm_lineDerivL_two_apply_le (v : E) :
    ∀ (k : ℕ) (u : Wkp mu Omega 2 (k + 1)), ‖lineDerivL v k u‖ ≤ ‖v‖ * ‖u‖
  | 0, u =>
      (norm_lineDerivL_zero_apply_le v u).trans
        (mul_le_mul_of_nonneg_left (norm_iteratedGradient_le 0 u) (norm_nonneg v))
  | k + 1, u => by
      let d := lineDerivL v (k + 1) u
      have hlow : ‖lowerOrder k d‖ ≤ ‖v‖ * ‖lowerOrder (k + 1) u‖ := by
        rw [lowerOrder_lineDerivL]
        exact norm_lineDerivL_two_apply_le v k (lowerOrder (k + 1) u)
      have htop : ‖iteratedGradient k d‖ ≤ ‖v‖ * ‖iteratedGradient (k + 1) u‖ :=
        norm_iteratedGradient_lineDerivL_le v k u
      have hd_sq := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq k d
      have hu_sq := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq (k + 1) u
      have hlow_sq := pow_le_pow_left₀ (norm_nonneg _) hlow 2
      have htop_sq := pow_le_pow_left₀ (norm_nonneg _) htop 2
      have hsq : ‖d‖ ^ 2 ≤ (‖v‖ * ‖u‖) ^ 2 := by
        rw [mul_pow, hu_sq, mul_add]
        rw [mul_pow] at hlow_sq htop_sq
        linarith
      exact (sq_le_sq₀ (norm_nonneg d) (by positivity)).1 hsq

/-- Operator-norm bound `‖lineDerivL v k‖ ≤ ‖v‖` at `p = 2` for every order `k`. -/
theorem norm_lineDerivL_two_le (v : E) (k : ℕ) :
    ‖lineDerivL (mu := mu) (Omega := Omega) (p := 2) v k‖ ≤ ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) (norm_lineDerivL_two_apply_le v k)

private theorem norm_lineDerivL_one_apply_le (v : E) (u : Wkp mu Omega p 2) :
    ‖lineDerivL v 1 u‖ ≤ √2 * ‖v‖ * ‖u‖ := by
  let d := lineDerivL v 1 u
  have hlow : ‖lowerOrder 0 d‖ ≤ ‖v‖ * ‖lowerOrder 1 u‖ := by
    rw [lowerOrder_lineDerivL]
    exact (norm_lineDerivL_zero_apply_le v (lowerOrder 1 u)).trans
      (mul_le_mul_of_nonneg_left (norm_iteratedGradient_le 0 _) (norm_nonneg v))
  have htop : ‖iteratedGradient 0 d‖ ≤ ‖v‖ * ‖iteratedGradient 1 u‖ :=
    norm_iteratedGradient_lineDerivL_le v 0 u
  have hd := norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 d
  have hu_sq := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ 0 u
  have hsum : ‖d‖ ≤ ‖v‖ * (‖lowerOrder 1 u‖ + ‖iteratedGradient 1 u‖) := by linarith
  have hsum_sq := pow_le_pow_left₀ (norm_nonneg d) hsum 2
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt zero_le_two
  have hsq : ‖d‖ ^ 2 ≤ (√2 * ‖v‖ * ‖u‖) ^ 2 := by
    calc
      ‖d‖ ^ 2 ≤ (‖v‖ * (‖lowerOrder 1 u‖ + ‖iteratedGradient 1 u‖)) ^ 2 := hsum_sq
      _ ≤ 2 * ‖v‖ ^ 2 * (‖lowerOrder 1 u‖ ^ 2 + ‖iteratedGradient 1 u‖ ^ 2) := by
        nlinarith [sq_nonneg (‖lowerOrder 1 u‖ - ‖iteratedGradient 1 u‖), sq_nonneg ‖v‖]
      _ = (√2 * ‖v‖ * ‖u‖) ^ 2 := by
        rw [← hu_sq, mul_pow, mul_pow, h2]
  exact (sq_le_sq₀ (norm_nonneg d) (by positivity)).1 hsq

/-- **Uniform graph-norm bound for `lineDerivL`.** For every exponent `1 ≤ p ≤ ∞` and every order
`k`, `‖lineDerivL v k u‖ ≤ √2 * ‖v‖ * ‖u‖`. Because every stage from order two upwards uses a
Euclidean product norm on `(lowerOrder, iteratedGradient)`, the factor `√2` from `W^{1,p}` does not
compound at higher orders. -/
theorem norm_lineDerivL_apply_le (v : E) :
    ∀ (k : ℕ) (u : Wkp mu Omega p (k + 1)), ‖lineDerivL v k u‖ ≤ √2 * ‖v‖ * ‖u‖
  | 0, u => by
      have h1 : (1 : ℝ) ≤ √2 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt one_le_two
      calc
        ‖lineDerivL v 0 u‖ ≤ 1 * (‖v‖ * ‖u‖) := by
          rw [one_mul]
          exact (norm_lineDerivL_zero_apply_le v u).trans
            (mul_le_mul_of_nonneg_left (norm_iteratedGradient_le 0 u) (norm_nonneg v))
        _ ≤ √2 * (‖v‖ * ‖u‖) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = √2 * ‖v‖ * ‖u‖ := (mul_assoc _ _ _).symm
  | 1, u => norm_lineDerivL_one_apply_le v u
  | k + 2, u => by
      let d := lineDerivL v (k + 2) u
      have hlow : ‖lowerOrder (k + 1) d‖ ≤ √2 * ‖v‖ * ‖lowerOrder (k + 2) u‖ := by
        rw [lowerOrder_lineDerivL]
        exact norm_lineDerivL_apply_le v (k + 1) (lowerOrder (k + 2) u)
      have htop : ‖iteratedGradient (k + 1) d‖ ≤ ‖v‖ * ‖iteratedGradient (k + 2) u‖ :=
        norm_iteratedGradient_lineDerivL_le v (k + 1) u
      have hd_sq := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k d
      have hu_sq := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ (k + 1) u
      have hlow_sq := pow_le_pow_left₀ (norm_nonneg _) hlow 2
      have htop_sq := pow_le_pow_left₀ (norm_nonneg _) htop 2
      have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt zero_le_two
      have hsq : ‖d‖ ^ 2 ≤ (√2 * ‖v‖ * ‖u‖) ^ 2 := by
        have hlow_sq' : ‖lowerOrder (k + 1) d‖ ^ 2 ≤
            2 * ‖v‖ ^ 2 * ‖lowerOrder (k + 2) u‖ ^ 2 := by
          refine hlow_sq.trans_eq ?_
          rw [mul_pow, mul_pow, h2]
        have htop_sq' : ‖iteratedGradient (k + 1) d‖ ^ 2 ≤
            2 * ‖v‖ ^ 2 * ‖iteratedGradient (k + 2) u‖ ^ 2 := by
          rw [mul_pow] at htop_sq
          linarith [sq_nonneg (‖v‖ * ‖iteratedGradient (k + 2) u‖)]
        calc
          ‖d‖ ^ 2 = ‖lowerOrder (k + 1) d‖ ^ 2 + ‖iteratedGradient (k + 1) d‖ ^ 2 := hd_sq
          _ ≤ 2 * ‖v‖ ^ 2 * (‖lowerOrder (k + 2) u‖ ^ 2 + ‖iteratedGradient (k + 2) u‖ ^ 2) := by
            linarith
          _ = (√2 * ‖v‖ * ‖u‖) ^ 2 := by
            rw [← hu_sq, mul_pow, mul_pow, h2]
      exact (sq_le_sq₀ (norm_nonneg d) (by positivity)).1 hsq

/-- Uniform operator-norm bound `‖lineDerivL v k‖ ≤ √2 * ‖v‖` for every `k` and `1 ≤ p ≤ ∞`. -/
theorem norm_lineDerivL_le (v : E) (k : ℕ) :
    ‖lineDerivL (mu := mu) (Omega := Omega) (p := p) v k‖ ≤ √2 * ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_lineDerivL_apply_le v k)

/-- Uniform operator-norm bound `‖lineDerivCLM k‖ ≤ √2` for the bilinear directional derivative. -/
theorem norm_lineDerivCLM_le (k : ℕ) :
    ‖lineDerivCLM (E := E) (mu := mu) (Omega := Omega) (p := p) k‖ ≤ √2 :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2) fun v => by
    rw [lineDerivCLM_apply]
    exact norm_lineDerivL_le v k

/-! ### Iterated directional derivatives and all-order symmetry -/

/-- **Iterated bundled directional derivative.** Differentiate an element of `W^{k+j,p}(Ω)`
successively along `m 0, m 1, …, m (j - 1)`, landing in `W^{k,p}(Ω)`. -/
def iteratedLineDerivL (k : ℕ) :
    (j : ℕ) → (Fin j → E) → Wkp mu Omega p (k + j) →L[ℝ] Wkp mu Omega p k
  | 0, _ => ContinuousLinearMap.id ℝ (Wkp mu Omega p k)
  | j + 1, m => (iteratedLineDerivL k j (Fin.tail m)).comp (lineDerivL (m 0) (k + j))

@[simp]
theorem iteratedLineDerivL_zero (k : ℕ) (m : Fin 0 → E) :
    iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k 0 m =
      ContinuousLinearMap.id ℝ (Wkp mu Omega p k) :=
  (rfl)

theorem iteratedLineDerivL_succ (k j : ℕ) (m : Fin (j + 1) → E) :
    iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k (j + 1) m =
      (iteratedLineDerivL k j (Fin.tail m)).comp (lineDerivL (m 0) (k + j)) :=
  (rfl)

theorem iteratedLineDerivL_one (k : ℕ) (m : Fin 1 → E) :
    iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k 1 m = lineDerivL (m 0) k :=
  ContinuousLinearMap.ext fun _ => (rfl)

/-- **Order-zero iterated directional derivative.** Differentiate an element of `W^{j,p}(Ω)` along
`j` directions `m : Fin j → E`, landing directly in `Lᵖ(Ω)` without arithmetic casts on `0 + j`. -/
def iteratedLineDerivZeroL :
    (j : ℕ) → (Fin j → E) → Wkp mu Omega p j →L[ℝ] Lp ℝ p (mu.restrict Omega)
  | 0, _ => ContinuousLinearMap.id ℝ (Lp ℝ p (mu.restrict Omega))
  | j + 1, m => (iteratedLineDerivZeroL j (Fin.tail m)).comp (lineDerivL (m 0) j)

@[simp]
theorem iteratedLineDerivZeroL_zero (m : Fin 0 → E) :
    iteratedLineDerivZeroL (E := E) (mu := mu) (Omega := Omega) (p := p) 0 m =
      ContinuousLinearMap.id ℝ (Lp ℝ p (mu.restrict Omega)) :=
  (rfl)

theorem iteratedLineDerivZeroL_succ (j : ℕ) (m : Fin (j + 1) → E) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) (j + 1) m =
      (iteratedLineDerivZeroL j (Fin.tail m)).comp (lineDerivL (m 0) j) :=
  (rfl)

theorem iteratedLineDerivZeroL_one (m : Fin 1 → E) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) 1 m = lineDerivL (m 0) 0 :=
  ContinuousLinearMap.ext fun _ => (rfl)

/-- **Permutation invariance of `iteratedLineDerivL`.** Reordering the tuple of directions by any
permutation `σ : Equiv.Perm (Fin j)` leaves the operator unchanged. -/
theorem iteratedLineDerivL_comp_perm (k : ℕ) (j : ℕ) (m : Fin j → E) (σ : Equiv.Perm (Fin j)) :
    iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k j (m ∘ σ) =
      iteratedLineDerivL k j m := by
  refine eq_comp_perm_of_tail_of_swap
    (fun i m' => iteratedLineDerivL (mu := mu) (Omega := Omega) (p := p) k i m')
    (fun i v m₁ m₂ h => ?_) (fun i m' => ?_) j m σ
  · rw [iteratedLineDerivL_succ, iteratedLineDerivL_succ, Fin.cons_zero, Fin.cons_zero,
      Fin.tail_cons, Fin.tail_cons, h]
  · have htail : Fin.tail (Fin.tail (m' ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail m') := by
      funext r
      have hne1 : r.succ.succ ≠ 1 := by
        rw [← Fin.succ_zero_eq_one]
        exact Fin.succ_inj.ne.2 (Fin.succ_ne_zero r)
      simp [Fin.tail, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hne1]
    simp only [iteratedLineDerivL_succ, ContinuousLinearMap.comp_assoc, htail,
      Function.comp_apply, Equiv.swap_apply_left, Fin.tail, Fin.succ_zero_eq_one,
      Equiv.swap_apply_right]
    congr 1
    exact lineDerivL_comp_lineDerivL_comm (m' 0) (m' 1) (k + i)

/-- **Permutation invariance of `iteratedLineDerivZeroL`.** -/
theorem iteratedLineDerivZeroL_comp_perm (j : ℕ) (m : Fin j → E) (σ : Equiv.Perm (Fin j)) :
    iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) j (m ∘ σ) =
      iteratedLineDerivZeroL j m := by
  refine eq_comp_perm_of_tail_of_swap
    (fun i m' => iteratedLineDerivZeroL (mu := mu) (Omega := Omega) (p := p) i m')
    (fun i v m₁ m₂ h => ?_) (fun i m' => ?_) j m σ
  · rw [iteratedLineDerivZeroL_succ, iteratedLineDerivZeroL_succ, Fin.cons_zero, Fin.cons_zero,
      Fin.tail_cons, Fin.tail_cons, h]
  · have htail : Fin.tail (Fin.tail (m' ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail m') := by
      funext r
      have hne1 : r.succ.succ ≠ 1 := by
        rw [← Fin.succ_zero_eq_one]
        exact Fin.succ_inj.ne.2 (Fin.succ_ne_zero r)
      simp [Fin.tail, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hne1]
    simp only [iteratedLineDerivZeroL_succ, ContinuousLinearMap.comp_assoc, htail,
      Function.comp_apply, Equiv.swap_apply_left, Fin.tail, Fin.succ_zero_eq_one,
      Equiv.swap_apply_right]
    rw [lineDerivL_comp_lineDerivL_comm]

/-- **Iterated directional derivatives evaluate `iteratedGradient`.** Differentiating
`u ∈ W^{j+1,p}(Ω)` along `m : Fin (j + 1) → E` produces `(IteratedGradient.evalL j m).compLp`
applied to `iteratedGradient j u`. -/
theorem iteratedLineDerivZeroL_succ_apply :
    ∀ (j : ℕ) (m : Fin (j + 1) → E) (u : Wkp mu Omega p (j + 1)),
      iteratedLineDerivZeroL (j + 1) m u =
        (IteratedGradient.evalL j m).compLp (iteratedGradient j u)
  | 0, m, u => by
      rw [iteratedLineDerivZeroL_succ, ContinuousLinearMap.comp_apply, iteratedLineDerivZeroL_zero,
        ContinuousLinearMap.id_apply, lineDerivL_zero_apply, IteratedGradient.evalL_zero]
  | j + 1, m, u => by
      rw [iteratedLineDerivZeroL_succ, ContinuousLinearMap.comp_apply,
        iteratedLineDerivZeroL_succ_apply j (Fin.tail m) (lineDerivL (m 0) (j + 1) u),
        iteratedGradient_lineDerivL (m 0) j u, compLp_comp,
        IteratedGradient.evalL_comp_contractL_one, Fin.cons_self_tail]

/-- Sharp `Lᵖ` bound for `(j + 1)`-fold directional derivatives in terms of the top seminorm. -/
theorem norm_iteratedLineDerivZeroL_succ_apply_le (j : ℕ) (m : Fin (j + 1) → E)
    (u : Wkp mu Omega p (j + 1)) :
    ‖iteratedLineDerivZeroL (j + 1) m u‖ ≤ (∏ r, ‖m r‖) * ‖iteratedGradient j u‖ := by
  rw [iteratedLineDerivZeroL_succ_apply]
  exact ((IteratedGradient.evalL j m).norm_compLp_le _).trans
    (mul_le_mul_of_nonneg_right (IteratedGradient.norm_evalL_le j m) (norm_nonneg _))

/-- The `Lᵖ` value of `iteratedLineDerivL k j m u` agrees with `iteratedLineDerivZeroL j m u₀`
whenever `u` and `u₀` have the same `Lᵖ` value. -/
theorem value_iteratedLineDerivL_eq_iteratedLineDerivZeroL (k : ℕ) :
    ∀ (j : ℕ) (m : Fin j → E) {u : Wkp mu Omega p (k + j)} {u₀ : Wkp mu Omega p j},
      value (k + j) u = value j u₀ →
      value k (iteratedLineDerivL k j m u) = iteratedLineDerivZeroL j m u₀
  | 0, _, _, u₀, h => h.trans (value_zero u₀)
  | j + 1, m, _, _, h => by
      rw [iteratedLineDerivL_succ, ContinuousLinearMap.comp_apply, iteratedLineDerivZeroL_succ,
        ContinuousLinearMap.comp_apply]
      exact value_iteratedLineDerivL_eq_iteratedLineDerivZeroL k j (Fin.tail m)
        (value_lineDerivL_eq_of_value_eq h (m 0))

/-- **Multilinear evaluations of `D^{j+1} u` belong to `W^{k,p}(Ω)` when `u ∈ W^{k+j+1,p}(Ω)`.**
If `u ∈ W^{k+j+1,p}(Ω)` and `u₀ ∈ W^{j+1,p}(Ω)` share the same `Lᵖ` value (for instance via
`TauCeti.Wkp.exists_value_eq_of_le`), then `iteratedLineDerivL k (j + 1) m u ∈ W^{k,p}(Ω)` has
`Lᵖ` value `(IteratedGradient.evalL j m).compLp (iteratedGradient j u₀)`. -/
theorem value_iteratedLineDerivL_eq_evalL_compLp (k j : ℕ) (m : Fin (j + 1) → E)
    {u : Wkp mu Omega p (k + (j + 1))} {u₀ : Wkp mu Omega p (j + 1)}
    (h : value (k + (j + 1)) u = value (j + 1) u₀) :
    value k (iteratedLineDerivL k (j + 1) m u) =
      (IteratedGradient.evalL j m).compLp (iteratedGradient j u₀) := by
  rw [value_iteratedLineDerivL_eq_iteratedLineDerivZeroL k (j + 1) m h,
    iteratedLineDerivZeroL_succ_apply]

/-! ### Repeated-direction contractions -/

/-- Differentiating `i` times in a repeated direction `h` contracts the `i` outermost slots of
`iteratedGradient` at `h`. -/
theorem iteratedGradient_iteratedLineDerivL_const (k : ℕ) (h : E) :
    ∀ (i : ℕ) {u : Wkp mu Omega p (k + 1 + i)} {u' : Wkp mu Omega p (k + i + 1)},
      value (k + 1 + i) u = value (k + i + 1) u' →
      iteratedGradient k (iteratedLineDerivL (k + 1) i (fun _ => h) u) =
        (IteratedGradient.contractL k i h).compLp (iteratedGradient (k + i) u')
  | 0, u, u', hu => by
      obtain rfl := ext (k + 1) hu
      dsimp only [Nat.add_zero]
      rw [iteratedLineDerivL_zero, ContinuousLinearMap.id_apply, IteratedGradient.contractL_zero]
      apply Lp.ext
      filter_upwards [(ContinuousLinearMap.id ℝ (IteratedGradient E k)).coeFn_compLp
        (iteratedGradient k u)] with x hx
      rw [hx, ContinuousLinearMap.id_apply]
  | i + 1, u, u', hu => by
      have hd : value (k + 1 + i) (lineDerivL h (k + 1 + i) u) =
          value (k + i + 1) (lineDerivL h (k + i + 1) u') :=
        value_lineDerivL_eq_of_value_eq hu h
      have htail : Fin.tail (fun _ : Fin (i + 1) => h) = fun _ : Fin i => h := rfl
      rw [iteratedLineDerivL_succ, ContinuousLinearMap.comp_apply, htail,
        iteratedGradient_iteratedLineDerivL_const k h i hd,
        iteratedGradient_lineDerivL h (k + i) u', compLp_comp,
        IteratedGradient.contractL_one, ← IteratedGradient.contractL_succ k i h]
      rfl

/-- Differentiating `j + 1` times in a repeated direction `h` evaluates `fullContractL j h` on
`iteratedGradient j u`. -/
theorem iteratedLineDerivZeroL_succ_const_apply (j : ℕ) (h : E) (u : Wkp mu Omega p (j + 1)) :
    iteratedLineDerivZeroL (j + 1) (fun _ => h) u =
      (IteratedGradient.fullContractL j h).compLp (iteratedGradient j u) := by
  rw [iteratedLineDerivZeroL_succ_apply, IteratedGradient.evalL_const]

/-- General-order form of `TauCeti.Wkp.iteratedLineDerivZeroL_succ_const_apply`. -/
theorem value_iteratedLineDerivL_const_eq_fullContractL_compLp (k j : ℕ) (h : E)
    {u : Wkp mu Omega p (k + (j + 1))} {u₀ : Wkp mu Omega p (j + 1)}
    (hu : value (k + (j + 1)) u = value (j + 1) u₀) :
    value k (iteratedLineDerivL k (j + 1) (fun _ => h) u) =
      (IteratedGradient.fullContractL j h).compLp (iteratedGradient j u₀) := by
  rw [value_iteratedLineDerivL_eq_evalL_compLp k j (fun _ => h) hu, IteratedGradient.evalL_const]

/-! ### Full symmetry of weak derivatives at arbitrary order -/

/-- Multilinear evaluation of `iteratedGradient j u` in `Lᵖ(Ω)` is invariant under every
permutation of the `j + 1` directions. -/
theorem evalL_compLp_iteratedGradient_comp_perm (j : ℕ) (u : Wkp mu Omega p (j + 1))
    (m : Fin (j + 1) → E) (σ : Equiv.Perm (Fin (j + 1))) :
    (IteratedGradient.evalL j (m ∘ σ)).compLp (iteratedGradient j u) =
      (IteratedGradient.evalL j m).compLp (iteratedGradient j u) := by
  rw [← iteratedLineDerivZeroL_succ_apply, ← iteratedLineDerivZeroL_succ_apply,
    iteratedLineDerivZeroL_comp_perm]

/-- **Weak derivatives of arbitrary order are symmetric almost everywhere.** For every
`u ∈ W^{j+1,p}(Ω)`, at almost every `x ∈ Ω` and for every permutation
`σ : Equiv.Perm (Fin (j + 1))`, the scalar continuous multilinear map attached to
`iteratedGradient j u x` is invariant under `domDomCongr σ`. -/
theorem domDomCongr_toContinuousMultilinearMapₗᵢ_iteratedGradient_ae (j : ℕ)
    (u : Wkp mu Omega p (j + 1)) :
    ∀ᵐ x ∂mu.restrict Omega, ∀ σ : Equiv.Perm (Fin (j + 1)),
      (IteratedGradient.toContinuousMultilinearMapₗᵢ E j
        (iteratedGradient j u x)).domDomCongr σ =
        IteratedGradient.toContinuousMultilinearMapₗᵢ E j (iteratedGradient j u x) := by
  let b := stdOrthonormalBasis ℝ E
  have hbasis (σ : Equiv.Perm (Fin (j + 1))) (r : Fin (j + 1) → Fin (Module.finrank ℝ E)) :
      ∀ᵐ x ∂mu.restrict Omega,
        IteratedGradient.evalL j ((fun k => b (r k)) ∘ σ) (iteratedGradient j u x) =
          IteratedGradient.evalL j (fun k => b (r k)) (iteratedGradient j u x) := by
    have heq := evalL_compLp_iteratedGradient_comp_perm j u (fun k => b (r k)) σ
    filter_upwards [(IteratedGradient.evalL j ((fun k => b (r k)) ∘ σ)).coeFn_compLp
      (iteratedGradient j u),
      (IteratedGradient.evalL j (fun k => b (r k))).coeFn_compLp (iteratedGradient j u)]
      with x hx₁ hx₂
    rw [← hx₁, ← hx₂, heq]
  filter_upwards [ae_all_iff.2 fun σ => ae_all_iff.2 fun r => hbasis σ r] with x hx σ
  let M := IteratedGradient.toContinuousMultilinearMapₗᵢ E j (iteratedGradient j u x)
  let G := (IteratedGradient.toContinuousMultilinearMapₗᵢ E j).symm (M.domDomCongr σ - M)
  refine sub_eq_zero.1 (norm_le_zero_iff.1 ?_)
  have hG : ‖M.domDomCongr σ - M‖ = ‖G‖ :=
    ((IteratedGradient.toContinuousMultilinearMapₗᵢ E j).symm.norm_map _).symm
  rw [hG]
  refine (IteratedGradient.norm_le_sum_norm_evalL_orthonormalBasis j G b).trans ?_
  refine Finset.sum_nonpos fun r _ => ?_
  rw [← IteratedGradient.toContinuousMultilinearMapₗᵢ_apply,
    LinearIsometryEquiv.apply_symm_apply, sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  change ‖IteratedGradient.toContinuousMultilinearMapₗᵢ E j (iteratedGradient j u x)
      ((fun k => b (r k)) ∘ σ) -
      IteratedGradient.toContinuousMultilinearMapₗᵢ E j (iteratedGradient j u x)
      (fun k => b (r k))‖ ≤ 0
  rw [IteratedGradient.toContinuousMultilinearMapₗᵢ_apply,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_apply, hx σ r, sub_self, norm_zero]

/-! ### Classical `ContDiffOn` bridges -/

/-- If `u ∈ W^{k+1,p}(Ω)` is represented on `Ω` by a `C¹` function `f`, then the value of
`lineDerivL v k u` agrees almost everywhere on `Ω` with the classical directional derivative
`x ↦ fderiv ℝ f x v`. Only `C¹` regularity of `f` is needed, regardless of `k`. -/
theorem value_lineDerivL_ae_eq_of_contDiffOn (k : ℕ) (u : Wkp mu Omega p (k + 1)) (v : E)
    {f : E → ℝ} (hf : ContDiffOn ℝ 1 f Omega)
    (hu : (value (k + 1) u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (value k (lineDerivL v k u) : E → ℝ) =ᵐ[mu.restrict Omega] fun x => fderiv ℝ f x v := by
  let u₁ : Wkp mu Omega p 1 := firstOrder k u
  have hu₁ : (value 1 u₁ : E → ℝ) =ᵐ[mu.restrict Omega] f := by
    rw [value_one u₁, value_firstOrder]
    exact hu
  rw [value_lineDerivL, ← iteratedGradient_zero u₁]
  filter_upwards [(innerSL ℝ v).coeFn_compLp (iteratedGradient 0 u₁),
    iteratedGradient_ae_eq_of_contDiffOn 0 u₁ hf hu₁] with x hx hgx
  rw [hx, hgx, iteratedGradientChain_zero, gradient, innerSL_apply_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]

/-- If `u ∈ W^{j+1,p}(Ω)` is represented on `Ω` by a `C^{j+1}` function `f`, then
`iteratedLineDerivZeroL (j + 1) m u` agrees almost everywhere on `Ω` with
`x ↦ iteratedFDeriv ℝ (j + 1) f x m`. -/
theorem iteratedLineDerivZeroL_succ_ae_eq_of_contDiffOn (j : ℕ) (u : Wkp mu Omega p (j + 1))
    (m : Fin (j + 1) → E) {f : E → ℝ} (hf : ContDiffOn ℝ (j + 1) f Omega)
    (hu : (value (j + 1) u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (iteratedLineDerivZeroL (j + 1) m u : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => iteratedFDeriv ℝ (j + 1) f x m := by
  rw [iteratedLineDerivZeroL_succ_apply]
  filter_upwards [(IteratedGradient.evalL j m).coeFn_compLp (iteratedGradient j u),
    iteratedGradient_ae_eq_of_contDiffOn j u hf hu] with x hx hgx
  rw [hx, hgx, IteratedGradient.evalL_iteratedGradientChain]

/-- General-order form of `TauCeti.Wkp.iteratedLineDerivZeroL_succ_ae_eq_of_contDiffOn`: only
`C^{j+1}` regularity of `f` on `Ω` is required, even when `u` lies in `W^{k+j+1,p}(Ω)`. -/
theorem value_iteratedLineDerivL_succ_ae_eq_of_contDiffOn (k j : ℕ)
    (u : Wkp mu Omega p (k + (j + 1))) (m : Fin (j + 1) → E) {f : E → ℝ}
    (hf : ContDiffOn ℝ (j + 1) f Omega)
    (hu : (value (k + (j + 1)) u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (value k (iteratedLineDerivL k (j + 1) m u) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => iteratedFDeriv ℝ (j + 1) f x m := by
  obtain ⟨u₀, hu₀, -⟩ := exists_value_eq_of_le (Nat.le_add_left (j + 1) k) u
  rw [value_iteratedLineDerivL_eq_iteratedLineDerivZeroL k (j + 1) m hu₀]
  exact iteratedLineDerivZeroL_succ_ae_eq_of_contDiffOn j u₀ m hf (hu₀ ▸ hu)

end Sobolev

/-! ### Concrete checks -/

section Examples

private theorem fderiv_sq_real (x : ℝ) :
    fderiv ℝ (fun y : ℝ => y ^ 2) x = (2 * x) • ContinuousLinearMap.id ℝ ℝ := by
  have hd : HasFDerivAt (fun y : ℝ => y * y)
      (x • ContinuousLinearMap.id ℝ ℝ + x • ContinuousLinearMap.id ℝ ℝ) x :=
    (hasFDerivAt_id x).mul (hasFDerivAt_id x)
  have hsq : (fun y : ℝ => y ^ 2) = fun y : ℝ => y * y := funext sq
  rw [hsq, hd.fderiv, ← add_smul]
  ring_nf

-- Check 1: on Ω = (0, 1) ⊆ ℝ, u(x) = x² in W^{2,p}(Ω) differentiated in direction v = 3 has
-- value 6x almost everywhere and weak derivative 6 = (D²u)⟨3⟩¹ almost everywhere.
example {p : ENNReal} [Fact (1 ≤ p)] :
    let Ω : Opens ℝ := ⟨Set.Ioo 0 1, isOpen_Ioo⟩
    ∃ u : Wkp volume Ω p 2,
      (value 2 u : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)] (fun x : ℝ => x ^ 2) ∧
      (value 1 (lineDerivL (3 : ℝ) 1 u) : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)]
        (fun x : ℝ => 6 * x) ∧
      (iteratedGradient 0 (lineDerivL (3 : ℝ) 1 u) : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)]
        fun _ : ℝ => 6 := by
  intro Ω
  have hf : ContDiff ℝ 2 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := p) 2 isOpen_univ hf.contDiffOn isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  refine ⟨u, hu, ?_, ?_⟩
  · refine (value_lineDerivL_ae_eq_of_contDiffOn 1 u (3 : ℝ)
      (hf.contDiffOn.of_le one_le_two) hu).trans (.of_forall fun x => ?_)
    dsimp only
    rw [fderiv_sq_real]
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  · filter_upwards [iteratedGradient_lineDerivL_ae (3 : ℝ) 0 u,
      iteratedGradient_ae_eq_of_contDiffOn 1 u hf.contDiffOn hu] with x h1 h2
    rw [h1, h2, iteratedGradientChain_succ, iteratedGradientChain_zero]
    have hgrad : gradient (fun y : ℝ => y ^ 2) = fun y : ℝ => 2 * y := by
      funext y
      refine ext_inner_left ℝ fun z => ?_
      rw [gradient, real_inner_comm, InnerProductSpace.toDual_symm_apply, fderiv_sq_real]
      simp [RCLike.inner_apply, mul_comm]
    rw [hgrad]
    have hd : HasFDerivAt (fun y : ℝ => (2 : ℝ) * y)
        ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) x := by
      simpa using (hasFDerivAt_id x).const_mul (2 : ℝ)
    rw [hd.fderiv]
    change (2 : ℝ) * 3 = 6
    norm_num

private theorem restrict_Ioo_ne_zero {a b : ℝ} (hab : a < b) :
    volume.restrict (Set.Ioo a b) ≠ 0 := by
  intro h0
  have hvol := congrArg (fun μ : Measure ℝ => μ Set.univ) h0
  simp only [Measure.restrict_apply_univ, FunLike.coe_zero, Pi.zero_apply,
    Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hvol
  linarith

private theorem eLpNorm_const_mul_id_Ioo_top_le {c : ℝ} (hc : 0 ≤ c) :
    eLpNorm (fun x : ℝ => c * x) ⊤ (volume.restrict (Set.Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal c := by
  have hm : AEStronglyMeasurable (fun x : ℝ => c * x)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    (continuous_const.mul continuous_id).aestronglyMeasurable
  rw [eLpNorm_exponent_top hm]
  refine eLpNormEssSup_le_of_ae_bound (C := c) ?_
  filter_upwards [ae_restrict_mem isOpen_Ioo.measurableSet] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg hc hx.1.le)]
  nlinarith [hx.2]

-- Helper for Check 2: the L^∞ norm of `x ↦ c * x` on `(0, 1)` is `c` for `0 < c`.
private theorem lpNorm_const_mul_id_Ioo_top {c : ℝ} (hc : 0 < c) :
    lpNorm (fun x : ℝ => c * x) ⊤ (volume.restrict (Set.Ioo (0 : ℝ) 1)) = c := by
  have hm : AEStronglyMeasurable (fun x : ℝ => c * x)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    (continuous_const.mul continuous_id).aestronglyMeasurable
  have he : eLpNorm (fun x : ℝ => c * x) ⊤ (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
      ENNReal.ofReal c := by
    refine le_antisymm (eLpNorm_const_mul_id_Ioo_top_le hc.le) ?_
    by_contra! hlt
    set M := (eLpNorm (fun x : ℝ => c * x) ⊤ (volume.restrict (Set.Ioo (0 : ℝ) 1))).toReal
    have htop : eLpNorm (fun x : ℝ => c * x) ⊤ (volume.restrict (Set.Ioo (0 : ℝ) 1)) ≠ ⊤ :=
      hlt.ne_top
    have hMc : M < c := by
      have hlt' := (ENNReal.toReal_lt_toReal htop ENNReal.ofReal_ne_top).2 hlt
      rwa [ENNReal.toReal_ofReal hc.le] at hlt'
    set r := max (c / 2) ((M + c) / 2)
    have hr0 : 0 < r := lt_of_lt_of_le (half_pos hc) (le_max_left _ _)
    have hrc : r < c := max_lt (half_lt_self hc) (by linarith)
    have hMr : eLpNorm (fun x : ℝ => c * x) ⊤ (volume.restrict (Set.Ioo (0 : ℝ) 1)) <
        ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_toReal htop]
      exact ENNReal.ofReal_lt_ofReal_iff hr0 |>.2
        (lt_of_lt_of_le (by linarith) (le_max_right _ _))
    have hae : ∀ᵐ x ∂volume.restrict (Set.Ioo (0 : ℝ) 1), ‖c * x‖ₑ < ENNReal.ofReal r := by
      rw [eLpNorm_exponent_top hm, eLpNormEssSup_eq_essSup_eNorm] at hMr
      exact ae_lt_of_essSup_lt hMr
    have hsub : Set.Ioo (r / c) 1 ⊆ Set.Ioo (0 : ℝ) 1 :=
      Set.Ioo_subset_Ioo_left (div_nonneg hr0.le hc.le)
    have hae' : ∀ᵐ x ∂volume.restrict (Set.Ioo (r / c) 1),
        x ∈ Set.Ioo (r / c) 1 ∧ ‖c * x‖ₑ < ENNReal.ofReal r :=
      (ae_restrict_mem isOpen_Ioo.measurableSet).and
        (ae_restrict_of_ae_restrict_of_subset hsub hae)
    have : NeZero (volume.restrict (Set.Ioo (r / c) 1)) :=
      ⟨restrict_Ioo_ne_zero ((div_lt_one hc).2 hrc)⟩
    obtain ⟨x, hxI, hxr⟩ := hae'.exists
    have hcx_pos : 0 < c * x := mul_pos hc (lt_trans (div_pos hr0 hc) hxI.1)
    have hcx_lt : c * x < r := by
      rw [Real.eNorm_eq_ofReal hcx_pos.le] at hxr
      exact (ENNReal.ofReal_lt_ofReal_iff hr0).1 hxr
    have hrc_lt : r < x * c := (div_lt_iff₀ hc).1 hxI.1
    linarith
  rw [lpNorm, he, ENNReal.toReal_ofReal hc.le]

-- Check 2: sharpness of the componentwise bound `‖lineDerivL v 0 u‖ ≤ ‖v‖ * ‖iteratedGradient 0 u‖`
-- at `p = ⊤` for `u(x) = x²` on `Ioo 0 1` and `v = 3`: both sides equal `6`.
example :
    let Ω : Opens ℝ := ⟨Set.Ioo 0 1, isOpen_Ioo⟩
    ∃ u : Wkp volume Ω ⊤ 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)] (fun x : ℝ => x ^ 2) ∧
      ‖lineDerivL (3 : ℝ) 0 u‖ = 6 ∧
      ‖(3 : ℝ)‖ * ‖iteratedGradient 0 u‖ = 6 := by
  intro Ω
  have hf : ContDiff ℝ 1 (fun x : ℝ => x ^ 2) := (contDiff_id.pow 2).of_le one_le_two
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := ⊤) 1 isOpen_univ hf.contDiffOn isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  refine ⟨u, hu, ?_, ?_⟩
  · have hd := value_lineDerivL_ae_eq_of_contDiffOn 0 u (3 : ℝ) hf.contDiffOn hu
    rw [value_zero] at hd
    have h6 : (lineDerivL (3 : ℝ) 0 u : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)]
        fun x : ℝ => 6 * x := by
      refine hd.trans (.of_forall fun x => ?_)
      dsimp only
      rw [fderiv_sq_real]
      simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      ring
    rw [Lp.norm_def, eLpNorm_congr_ae h6, ← lpNorm]
    exact lpNorm_const_mul_id_Ioo_top (c := 6) (by norm_num)
  · rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      norm_iteratedGradient_eq_lpNorm_of_contDiffOn 0 u hf.contDiffOn hu]
    have h2 : (fun x : ℝ => ‖iteratedFDeriv ℝ 1 (fun y : ℝ => y ^ 2) x‖) =
        fun x : ℝ => ‖(2 : ℝ) * x‖ := by
      funext x
      rw [norm_iteratedFDeriv_one, fderiv_sq_real, norm_smul, ContinuousLinearMap.norm_id, mul_one]
    have hlp : lpNorm (iteratedFDeriv ℝ 1 (fun y : ℝ => y ^ 2)) ⊤
        (volume.restrict (Ω : Set ℝ)) =
        lpNorm (fun x : ℝ => (2 : ℝ) * x) ⊤ (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      rw [lpNorm, lpNorm]
      congr 1
      refine eLpNorm_congr_norm_ae
        ((ContinuousOn.continuousOn_iteratedFDeriv hf.contDiffOn Ω.isOpen
          le_rfl).aestronglyMeasurable Ω.isOpen.measurableSet)
        ((continuous_const.mul continuous_id).continuousOn.aestronglyMeasurable
          Ω.isOpen.measurableSet) ?_
      exact .of_forall (congrFun h2)
    rw [hlp, lpNorm_const_mul_id_Ioo_top (c := 2) (by norm_num)]
    norm_num

-- Check 3: on the open unit ball in ℝ², u(x) = x₀ * x₁ in W^{2,p}(B(0, 1)) satisfies
-- `lineDerivL e₀ 0 (lineDerivL e₁ 1 u) = lineDerivL e₁ 0 (lineDerivL e₀ 1 u)` and both equal `1`
-- almost everywhere.
example {p : ENNReal} [Fact (1 ≤ p)] :
    let E₂ := EuclideanSpace ℝ (Fin 2)
    let Ω : Opens E₂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
    let e₀ : E₂ := EuclideanSpace.single 0 1
    let e₁ : E₂ := EuclideanSpace.single 1 1
    ∃ u : Wkp volume Ω p 2,
      (value 2 u : E₂ → ℝ) =ᵐ[volume.restrict (Ω : Set E₂)] (fun x : E₂ => x 0 * x 1) ∧
      lineDerivL e₀ 0 (lineDerivL e₁ 1 u) = lineDerivL e₁ 0 (lineDerivL e₀ 1 u) ∧
      (lineDerivL e₀ 0 (lineDerivL e₁ 1 u) : E₂ → ℝ) =ᵐ[volume.restrict (Ω : Set E₂)]
        fun _ : E₂ => 1 := by
  intro E₂ Ω e₀ e₁
  let l₀ : E₂ →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).comp
    (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap
  let l₁ : E₂ →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).comp
    (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap
  have hl₀ (v : E₂) : l₀ v = v 0 := rfl
  have hl₁ (v : E₂) : l₁ v = v 1 := rfl
  have hf : ContDiff ℝ 2 (fun x : E₂ => l₀ x * l₁ x) := l₀.contDiff.mul l₁.contDiff
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := p) 2 isOpen_univ hf.contDiffOn (isCompact_closedBall (0 : E₂) 1)
    Metric.ball_subset_closedBall (Set.subset_univ _)
  refine ⟨u, hu, lineDerivL_comm e₀ e₁ 0 u, ?_⟩
  have hiter : lineDerivL e₀ 0 (lineDerivL e₁ 1 u) = iteratedLineDerivZeroL 2 ![e₁, e₀] u := rfl
  rw [hiter]
  refine (iteratedLineDerivZeroL_succ_ae_eq_of_contDiffOn 1 u ![e₁, e₀] hf.contDiffOn hu).trans
    (.of_forall fun x => ?_)
  change iteratedFDeriv ℝ 2 (fun y : E₂ => l₀ y * l₁ y) x ![e₁, e₀] = 1
  rw [iteratedFDeriv_two_apply]
  have hfd : fderiv ℝ (fun y : E₂ => l₀ y * l₁ y) =
      fun y => l₀ y • l₁ + l₁ y • l₀ := by
    ext y v
    have hd : HasFDerivAt (fun z : E₂ => l₀ z * l₁ z) (l₀ y • l₁ + l₁ y • l₀) y :=
      (l₀.hasFDerivAt (x := y)).mul (l₁.hasFDerivAt (x := y))
    rw [hd.fderiv]
  rw [hfd]
  have hd₂ : HasFDerivAt (fun y : E₂ => l₀ y • l₁ + l₁ y • l₀)
      (l₀.smulRight l₁ + l₁.smulRight l₀) x :=
    (l₀.hasFDerivAt.smul_const l₁).add (l₁.hasFDerivAt.smul_const l₀)
  rw [hd₂.fderiv]
  simp [hl₀, hl₁, e₀, e₁]

end Examples

end Wkp

end TauCeti
