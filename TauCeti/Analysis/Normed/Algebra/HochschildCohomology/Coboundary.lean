/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import TauCeti.RingTheory.CyclicCohomology.Cochain
import TauCeti.Algebra.BigOperators.AlternatingSum
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# The bounded Hochschild coboundary of a bounded bimodule

Let `A` be a possibly nonunital normed algebra over a nontrivially normed field `𝕜` and `E` a
normed space. A bounded bimodule structure on `E` is given by two bounded bilinear maps
`L R : A →L[𝕜] E →L[𝕜] E`, with `a · x = L a x` and `x · a = R a x`, satisfying
`L (a * b) x = L a (L b x)`, `R (a * b) x = R b (R a x)` and `L a (R b x) = R b (L a x)`.
The actions need not be contractive or unital.

A bounded Hochschild `n`-cochain of `A` with coefficients in `E` is a bounded `n`-multilinear map
`T : Aⁿ → E`, i.e. an element of `ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E`; the
`0`-cochains are the constant maps, i.e. the elements of `E`. This file constructs the bounded
Hochschild coboundary `δ : Cⁿ(A, E) → Cⁿ⁺¹(A, E)`,

`(δT)(a₀, …, aₙ) = L a₀ (T (a₁, …, aₙ)) + ∑_{j < n} (-1)ʲ⁺¹ T(a₀, …, aⱼaⱼ₊₁, …, aₙ)`
`  + (-1)ⁿ⁺¹ R aₙ (T (a₀, …, aₙ₋₁))`,

as a bounded linear map, the alternating sum of bounded cofaces `∂ᵢ`. The operator norm of `δ` is
at most `‖L‖ + n + ‖R‖`. The cofaces satisfy the cosimplicial identities, so `δ ∘ δ = 0`. In low
degrees the coboundary of a constant cochain `x` is the inner derivation `a ↦ L a x - R a x`, so
the degree-zero cocycles are the central elements of `E`, and the degree-one cocycles are the
bounded derivations `D (a * b) = L a (D b) + R b (D a)`.

The inner cofaces are the bounded versions of `TauCeti.hochschildCoface`; the algebraic
coboundary with coefficients in a bimodule over a unital algebra is
`TauCeti.hochschildBimoduleCoboundary`. The present construction keeps the actions as bounded
bilinear maps, so that it applies to nonunital Banach algebras and to bimodules whose actions are
not unital.

## Main definitions

* `ContinuousLinearMap.hochschildBimoduleCoface`: the bounded cofaces `∂ᵢ`.
* `ContinuousLinearMap.hochschildBimoduleCoboundary`: the bounded Hochschild coboundary
  `δ = ∑ᵢ (-1)ⁱ ∂ᵢ`.

## Main results

* `ContinuousLinearMap.hochschildBimoduleCoboundary_apply_eq_add_sum_add`: the explicit formula
  for `δ`.
* `ContinuousLinearMap.norm_hochschildBimoduleCoboundary_le`: `‖δ‖ ≤ ‖L‖ + n + ‖R‖`.
* `ContinuousLinearMap.hochschildBimoduleCoface_hochschildBimoduleCoface`: the cosimplicial
  identities `∂_{j+1} ∘ ∂ᵢ = ∂ᵢ ∘ ∂_j` for `i ≤ j`.
* `ContinuousLinearMap.hochschildBimoduleCoboundary_hochschildBimoduleCoboundary`: `δ (δ T) = 0`.
* `ContinuousLinearMap.hochschildBimoduleCoboundary_constOfIsEmpty_eq_zero_iff`: the degree-zero
  cocycles are the central elements.
* `ContinuousLinearMap.hochschildBimoduleCoboundary_ofSubsingleton_eq_zero_iff`: the degree-one
  cocycles are the bounded derivations.

## References

* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.8.
* A. Ya. Helemskii, *The Homology of Banach and Topological Algebras*, Chapter I.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ}

section Coface

variable (n) in
/-- The zeroth coface `(∂₀T)(a₀, …, aₙ) = L a₀ (T (a₁, …, aₙ))`. -/
private def leftCoface (L : A →L[𝕜] E →L[𝕜] E) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) E :=
  (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ A)
      E).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (compContinuousMultilinearMapL 𝕜 (fun _ : Fin n ↦ A) E E ∘L L).flip

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
private theorem leftCoface_apply (L : A →L[𝕜] E →L[𝕜] E)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) (a : Fin (n + 1) → A) :
    leftCoface n L T a = L (a 0) (T (Fin.tail a)) :=
  rfl

variable (n) in
/-- The last coface `(∂ₙ₊₁T)(a₀, …, aₙ) = R aₙ (T (a₀, …, aₙ₋₁))`. -/
private def rightCoface (R : A →L[𝕜] E →L[𝕜] E) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) E :=
  (continuousMultilinearCurryRightEquiv 𝕜 (fun _ : Fin (n + 1) ↦ A)
      E).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    compContinuousMultilinearMapL 𝕜 (fun _ : Fin n ↦ A) E (A →L[𝕜] E) R.flip

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
private theorem rightCoface_apply (R : A →L[𝕜] E →L[𝕜] E)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) (a : Fin (n + 1) → A) :
    rightCoface n R T a = R (a (Fin.last n)) (T (Fin.init a)) :=
  rfl

/-- The inner coface multiplying the entries `j` and `j + 1`, a bounded version of
`TauCeti.hochschildCoface`. -/
private def contractCoface (j : Fin (n + 1)) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) E →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 2) ↦ A) E :=
  MultilinearMap.mkContinuousLinear
    (TauCeti.hochschildCoface 𝕜 A E j.castSucc ∘ₗ ContinuousMultilinearMap.toMultilinearMapLinear)
    1 fun T a ↦ by
      rw [LinearMap.comp_apply, TauCeti.hochschildCoface_apply, one_mul,
        TauCeti.hochschildFace_castSucc]
      refine (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg T))
      -- multiplying two adjacent entries does not increase the product of the norms
      rw [← Fin.prod_contractNth_castSucc j fun k ↦ ‖a k‖]
      refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun k _ ↦ ?_
      rcases lt_trichotomy (k : ℕ) j.castSucc with h | h | h
      · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ h]
      · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_eq _ _ _ _ h]
        exact norm_mul_le _ _
      · rw [Fin.contractNth_apply_of_gt _ _ _ _ h, Fin.contractNth_apply_of_gt _ _ _ _ h]

private theorem contractCoface_apply (j : Fin (n + 1))
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) E) (a : Fin (n + 2) → A) :
    contractCoface j T a = T (Fin.contractNth j.castSucc (· * ·) a) :=
  (TauCeti.hochschildCoface_apply 𝕜 A E j.castSucc T.toMultilinearMap a).trans <|
    congrArg T (TauCeti.hochschildFace_castSucc j a)

private theorem norm_contractCoface_le (j : Fin (n + 1)) :
    ‖(contractCoface j : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) E →L[𝕜] _)‖ ≤ 1 :=
  MultilinearMap.mkContinuousLinear_norm_le _ zero_le_one _

/-- The inner cofaces of cochains with `n` arguments, indexed by `Fin n`. -/
private def innerCoface : ∀ {n : ℕ}, Fin n →
    ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) E
  | 0, j => j.elim0
  | _ + 1, j => contractCoface j

/-- The `i`-th bounded Hochschild coface, sending a bounded cochain `T` in `n` arguments to a
bounded cochain in `n + 1` arguments: the zeroth coface acts by the first entry through `L`, the
last coface acts by the last entry through `R`, and the others multiply two adjacent entries. -/
def hochschildBimoduleCoface (L R : A →L[𝕜] E →L[𝕜] E) (i : Fin (n + 2)) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) E :=
  Fin.cases (leftCoface n L) (Fin.lastCases (rightCoface n R) innerCoface) i

variable (L R : A →L[𝕜] E →L[𝕜] E)

/-- The zeroth coface acts by the first entry on the left. -/
@[simp]
theorem hochschildBimoduleCoface_zero_apply
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) (a : Fin (n + 1) → A) :
    hochschildBimoduleCoface L R 0 T a = L (a 0) (T (Fin.tail a)) :=
  leftCoface_apply L T a

/-- The last coface acts by the last entry on the right. -/
@[simp]
theorem hochschildBimoduleCoface_last_apply
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) (a : Fin (n + 1) → A) :
    hochschildBimoduleCoface L R (Fin.last (n + 1)) T a = R (a (Fin.last n)) (T (Fin.init a)) := by
  rw [hochschildBimoduleCoface, ← Fin.succ_last, Fin.cases_succ, Fin.lastCases_last,
    rightCoface_apply]

private theorem hochschildBimoduleCoface_castSucc_succ (j : Fin (n + 1)) :
    hochschildBimoduleCoface (n := n + 1) L R j.castSucc.succ = contractCoface j := by
  rw [hochschildBimoduleCoface, Fin.cases_succ, Fin.lastCases_castSucc]
  rfl

/-- The inner cofaces multiply two adjacent entries. -/
@[simp]
theorem hochschildBimoduleCoface_castSucc_succ_apply (j : Fin n)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) (a : Fin (n + 1) → A) :
    hochschildBimoduleCoface L R j.castSucc.succ T a =
      T (Fin.contractNth j.castSucc (· * ·) a) := by
  cases n with
  | zero => exact j.elim0
  | succ n => rw [hochschildBimoduleCoface_castSucc_succ, contractCoface_apply]

/-- The inner cofaces multiply two adjacent entries, with the index written as `j.succ.castSucc`
rather than `j.castSucc.succ`. -/
theorem hochschildBimoduleCoface_succ_castSucc_apply (j : Fin n)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) (a : Fin (n + 1) → A) :
    hochschildBimoduleCoface L R j.succ.castSucc T a =
      T (Fin.contractNth j.castSucc (· * ·) a) := by
  rw [← Fin.succ_castSucc, hochschildBimoduleCoface_castSucc_succ_apply]

/-- The norm of the `i`-th coface is at most `‖L‖` for the zeroth coface, `‖R‖` for the last one,
and `1` for the inner ones. -/
private theorem norm_hochschildBimoduleCoface_le (i : Fin (n + 2)) :
    ‖hochschildBimoduleCoface L R i‖ ≤
      Fin.cases ‖L‖ (Fin.lastCases ‖R‖ fun _ ↦ 1) i := by
  induction i using Fin.cases with
  | zero =>
    refine opNorm_le_bound _ (norm_nonneg L) fun T ↦ ?_
    refine ContinuousMultilinearMap.opNorm_le_bound
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun a ↦ ?_
    rw [hochschildBimoduleCoface_zero_apply, Fin.prod_univ_succ]
    calc ‖L (a 0) (T (Fin.tail a))‖ ≤ ‖L‖ * ‖a 0‖ * (‖T‖ * ∏ k : Fin n, ‖Fin.tail a k‖) :=
          (L.le_opNorm₂ _ _).trans (by gcongr; exact T.le_opNorm _)
      _ = ‖L‖ * ‖T‖ * (‖a 0‖ * ∏ k : Fin n, ‖a k.succ‖) := by simp only [Fin.tail]; ring
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.cases_succ, Fin.lastCases_last]
      refine opNorm_le_bound _ (norm_nonneg R) fun T ↦ ?_
      refine ContinuousMultilinearMap.opNorm_le_bound
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun a ↦ ?_
      rw [Fin.succ_last, hochschildBimoduleCoface_last_apply, Fin.prod_univ_castSucc]
      calc ‖R (a (Fin.last n)) (T (Fin.init a))‖ ≤
            ‖R‖ * ‖a (Fin.last n)‖ * (‖T‖ * ∏ k : Fin n, ‖Fin.init a k‖) :=
          (R.le_opNorm₂ _ _).trans (by gcongr; exact T.le_opNorm _)
        _ = ‖R‖ * ‖T‖ * ((∏ k : Fin n, ‖a k.castSucc‖) * ‖a (Fin.last n)‖) := by
          simp only [Fin.init]; ring
    | cast j =>
      rw [Fin.cases_succ, Fin.lastCases_castSucc]
      cases n with
      | zero => exact j.elim0
      | succ n =>
        rw [hochschildBimoduleCoface_castSucc_succ]
        exact norm_contractCoface_le j

/-- The cosimplicial identity `∂_{j+1} ∘ ∂ᵢ = ∂ᵢ ∘ ∂_j` for `i ≤ j`, for a bounded bimodule. -/
theorem hochschildBimoduleCoface_hochschildBimoduleCoface
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) {i j : Fin (n + 2)} (hij : i ≤ j)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) :
    hochschildBimoduleCoface L R j.succ (hochschildBimoduleCoface L R i T) =
      hochschildBimoduleCoface L R i.castSucc (hochschildBimoduleCoface L R j T) := by
  -- Each of `i` and `j` is the left coface `0`, an inner coface `k.castSucc.succ` or the right
  -- coface `Fin.last`; the six cases with `i ≤ j` reduce to identities between tuples, after
  -- rewriting each inner index into the shape `k.castSucc.succ` of
  -- `hochschildBimoduleCoface_castSucc_succ_apply`.
  ext a
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero =>
      -- `L (a₀ a₁) (T (a₂, …)) = L a₀ (L a₁ (T (a₂, …)))`
      rw [← Fin.castSucc_zero (n := n + 1), hochschildBimoduleCoface_castSucc_succ_apply]
      simp only [Fin.castSucc_zero, hochschildBimoduleCoface_zero_apply]
      rw [← Fin.cons_self_tail a, Fin.contractNth_zero_cons]
      simp only [Fin.cons_zero, Fin.tail_cons, hL]
    | succ j =>
      induction j using Fin.lastCases with
      | last =>
        -- the left and right actions commute
        simp only [Fin.succ_last, hochschildBimoduleCoface_last_apply,
          Fin.castSucc_zero, hochschildBimoduleCoface_zero_apply]
        rw [Fin.tail_init_eq_init_tail]
        exact (hLR _ _ _).symm
      | cast j =>
        -- an inner contraction commutes with dropping the first entry
        rw [Fin.succ_castSucc, hochschildBimoduleCoface_castSucc_succ_apply]
        simp only [Fin.castSucc_zero, hochschildBimoduleCoface_zero_apply,
          hochschildBimoduleCoface_succ_castSucc_apply]
        rw [Fin.contractNth_apply_of_lt _ _ _ _ (Nat.succ_pos _), Fin.castSucc_zero,
          ← Fin.succ_castSucc, Fin.tail_contractNth_succ]
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      -- `R (aₙ aₙ₊₁) (T (…)) = R aₙ₊₁ (R aₙ (T (…)))`
      rw [Fin.succ_last] at hij ⊢
      obtain rfl : j = Fin.last (n + 1) := le_antisymm (Fin.le_last _) hij
      rw [Fin.succ_last, (by rw [Fin.succ_castSucc, Fin.succ_last] :
        (Fin.last (n + 1)).castSucc = (Fin.last n).castSucc.succ),
        hochschildBimoduleCoface_castSucc_succ_apply]
      simp only [hochschildBimoduleCoface_last_apply]
      rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, Fin.init_contractNth_castSucc_last, hR,
        Fin.succ_last, Fin.init_def]
    | cast i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (not_le.2 (Fin.succ_pos _))
      | succ j =>
        induction j using Fin.lastCases with
        | last =>
          -- an inner contraction commutes with dropping the last entry
          rw [Fin.succ_last, Fin.succ_last, hochschildBimoduleCoface_succ_castSucc_apply]
          simp only [hochschildBimoduleCoface_last_apply,
            hochschildBimoduleCoface_castSucc_succ_apply]
          rw [Fin.contractNth_apply_of_gt _ _ _ _ i.2, Fin.init_contractNth_castSucc,
            Fin.succ_last]
        | cast j =>
          -- two inner contractions: the simplicial identity of `TauCeti.hochschildFace`
          rw [Fin.succ_castSucc j]
          simp only [hochschildBimoduleCoface_castSucc_succ_apply,
            hochschildBimoduleCoface_succ_castSucc_apply]
          cases n with
          | zero => exact i.elim0
          | succ n =>
            have h := TauCeti.hochschildFace_hochschildFace (i := i.castSucc) (j := j.castSucc)
              (by simpa using hij) a
            simp only [Fin.succ_castSucc, TauCeti.hochschildFace_castSucc] at h
            rw [h]

end Coface

section Coboundary

variable (L R : A →L[𝕜] E →L[𝕜] E)

/-- The bounded Hochschild coboundary `δ` on bounded cochains with coefficients in the bimodule
given by the actions `L` and `R`, the alternating sum `∑ᵢ (-1)ⁱ ∂ᵢ` of the cofaces. Explicitly
(`ContinuousLinearMap.hochschildBimoduleCoboundary_apply_eq_add_sum_add`),
`(δT)(a₀, …, aₙ) = L a₀ (T (a₁, …, aₙ)) + ∑_{j < n} (-1)ʲ⁺¹ T(a₀, …, aⱼaⱼ₊₁, …, aₙ)
  + (-1)ⁿ⁺¹ R aₙ (T (a₀, …, aₙ₋₁))`. -/
def hochschildBimoduleCoboundary (n : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) E :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • hochschildBimoduleCoface L R i

/-- The coboundary evaluates as the alternating sum of the cofaces. -/
@[simp]
theorem hochschildBimoduleCoboundary_apply
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) (a : Fin (n + 1) → A) :
    hochschildBimoduleCoboundary L R n T a =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • hochschildBimoduleCoface L R i T a := by
  simp [hochschildBimoduleCoboundary]

/-- The bounded Hochschild coboundary in explicit form. -/
theorem hochschildBimoduleCoboundary_apply_eq_add_sum_add
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) (a : Fin (n + 1) → A) :
    hochschildBimoduleCoboundary L R n T a =
      L (a 0) (T (Fin.tail a)) +
        ∑ j : Fin n, (-1 : ℤ) ^ ((j : ℕ) + 1) • T (Fin.contractNth j.castSucc (· * ·) a) +
          (-1 : ℤ) ^ (n + 1) • R (a (Fin.last n)) (T (Fin.init a)) := by
  rw [hochschildBimoduleCoboundary_apply, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp [add_assoc]

/-- The operator norm of the bounded Hochschild coboundary on `n`-cochains is at most
`‖L‖ + n + ‖R‖`. -/
theorem norm_hochschildBimoduleCoboundary_le :
    ‖hochschildBimoduleCoboundary L R n‖ ≤ ‖L‖ + n + ‖R‖ := by
  rw [hochschildBimoduleCoboundary]
  refine (norm_sum_le Finset.univ fun i : Fin (n + 2) ↦
    (-1 : ℤ) ^ (i : ℕ) • hochschildBimoduleCoface L R i).trans ?_
  calc ∑ i : Fin (n + 2), ‖(-1 : ℤ) ^ (i : ℕ) • hochschildBimoduleCoface L R i‖
      ≤ ∑ i : Fin (n + 2), (Fin.cases ‖L‖ (Fin.lastCases ‖R‖ fun _ ↦ 1) i : ℝ) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        refine (norm_zsmul_le ((-1 : ℤ) ^ (i : ℕ)) (hochschildBimoduleCoface L R i)).trans ?_
        rw [norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact norm_hochschildBimoduleCoface_le L R i
    _ = ‖L‖ + n + ‖R‖ := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
        simp only [Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last, Fin.lastCases_castSucc,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring

/-- The bounded Hochschild coboundary squares to zero. -/
@[simp]
theorem hochschildBimoduleCoboundary_hochschildBimoduleCoboundary
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) :
    hochschildBimoduleCoboundary L R (n + 1) (hochschildBimoduleCoboundary L R n T) = 0 := by
  ext a
  rw [hochschildBimoduleCoboundary_apply, hochschildBimoduleCoboundary]
  simp only [map_sum, map_zsmul, FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply,
    Pi.smul_apply, zero_apply]
  exact TauCeti.sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero
    (fun i j ↦ hochschildBimoduleCoface L R i (hochschildBimoduleCoface L R j T) a)
    fun i j hij ↦ by
      simp only [hochschildBimoduleCoface_hochschildBimoduleCoface L R hL hR hLR hij]

/-- The bounded Hochschild coboundary squares to zero, as a composite of bounded linear maps. -/
theorem hochschildBimoduleCoboundary_comp_hochschildBimoduleCoboundary
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) :
    hochschildBimoduleCoboundary L R (n + 1) ∘L hochschildBimoduleCoboundary L R n = 0 :=
  ContinuousLinearMap.ext
    (hochschildBimoduleCoboundary_hochschildBimoduleCoboundary L R hL hR hLR)

/-- The coboundary of the degree-zero cochain with value `x` is the inner derivation
`a ↦ L a x - R a x`. -/
theorem hochschildBimoduleCoboundary_constOfIsEmpty (x : E) (a : Fin 1 → A) :
    hochschildBimoduleCoboundary L R 0
        (ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 ↦ A) x) a =
      L (a 0) x - R (a 0) x := by
  rw [hochschildBimoduleCoboundary_apply_eq_add_sum_add]
  simp [sub_eq_add_neg]

/-- A degree-zero cochain is a cocycle exactly when its value lies in the centre of the
bimodule. -/
theorem hochschildBimoduleCoboundary_constOfIsEmpty_eq_zero_iff (x : E) :
    hochschildBimoduleCoboundary L R 0
        (ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 ↦ A) x) = 0 ↔
      ∀ a : A, L a x = R a x := by
  refine ⟨fun h a ↦ ?_, fun h ↦ ?_⟩
  · have ha := congrArg (fun T ↦ T fun _ ↦ a) h
    simpa only [hochschildBimoduleCoboundary_constOfIsEmpty,
      _root_.zero_apply, sub_eq_zero] using ha
  · ext a
    rw [hochschildBimoduleCoboundary_constOfIsEmpty, h, sub_self,
      _root_.zero_apply]

/-- The coboundary of a degree-one cochain `D`:
`(δD)(a₀, a₁) = L a₀ (D a₁) - D (a₀ a₁) + R a₁ (D a₀)`. -/
theorem hochschildBimoduleCoboundary_ofSubsingleton (D : A →L[𝕜] E) (a : Fin 2 → A) :
    hochschildBimoduleCoboundary L R 1 (ContinuousMultilinearMap.ofSubsingleton 𝕜 A E 0 D) a =
      L (a 0) (D (a 1)) - D (a 0 * a 1) + R (a 1) (D (a 0)) := by
  rw [hochschildBimoduleCoboundary_apply_eq_add_sum_add, Fin.sum_univ_one]
  simp only [ContinuousMultilinearMap.ofSubsingleton_apply_apply, Fin.tail_def, Fin.init_def,
    Fin.castSucc_zero, Fin.contractNth_apply_of_eq (0 : Fin 2) (· * ·) a 0 rfl]
  simp [sub_eq_add_neg]

/-- A degree-one cochain is a cocycle exactly when it is a bounded derivation into the bimodule:
`D (a * b) = L a (D b) + R b (D a)`. -/
theorem hochschildBimoduleCoboundary_ofSubsingleton_eq_zero_iff (D : A →L[𝕜] E) :
    hochschildBimoduleCoboundary L R 1 (ContinuousMultilinearMap.ofSubsingleton 𝕜 A E 0 D) = 0 ↔
      ∀ a b : A, D (a * b) = L a (D b) + R b (D a) := by
  refine ⟨fun h a b ↦ ?_, fun h ↦ ?_⟩
  · have hab := congrArg (fun T ↦ T ![a, b]) h
    simp only [hochschildBimoduleCoboundary_ofSubsingleton, _root_.zero_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hab
    rw [sub_add_eq_add_sub, sub_eq_zero] at hab
    exact hab.symm
  · ext a
    rw [hochschildBimoduleCoboundary_ofSubsingleton, h, _root_.zero_apply]
    abel

end Coboundary

end ContinuousLinearMap
