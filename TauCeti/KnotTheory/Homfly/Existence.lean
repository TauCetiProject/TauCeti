/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Braid.HeckeSkein
public import TauCeti.KnotTheory.Homfly.Specialization
public import TauCeti.KnotTheory.Jimbo.Normalization
import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# Existence of the HOMFLY polynomial

For every braid, the weighted traces of the Jimbo representations with `N` colours, for all `N`,
are the specializations `a = q ^ N`, `z = q - q⁻¹` of a single two-variable Laurent polynomial
(`TauCeti.KnotTheory.exists_homflySpecialization_eq_jimboWeightedTrace`). Writhe normalization
then gives the HOMFLY polynomial of a braid closure, `TauCeti.MarkovBraid.homfly`, as an element
of `K[a, a⁻¹, z, z⁻¹]`, represented as in `TauCeti.KnotTheory.homflySpecialization` with `z` the
inner and `a` the outer Laurent variable. It is characterized by its `sl_N` specializations, which
are the writhe-normalized Jimbo traces `TauCeti.MarkovBraid.jimboTrace`; it is invariant under
Markov equivalence and satisfies the oriented HOMFLY skein relation
`a P(L₊) - a⁻¹ P(L₋) = z P(L₀)`.

The normalization is the unreduced one inherited from the Jimbo traces: the one-strand unknot has
value `(a - a⁻¹) z⁻¹` (`TauCeti.KnotTheory.homflyUnknot`), the quantum dimension, rather than one.

The existence proof is Jones's trace argument. Modulo the Hecke skein relation, every braid on
`n + 2` strands is a combination of braids `ι b` and `ι b * σ * ι c`, where `ι` adds an uncrossed
strand and `σ` is the last elementary braid (`TauCeti.BraidGroup.strandSpan_sup_heckeSkein_eq_top`).
The weighted traces kill the Hecke skein relators, multiply by the quantum dimension under `ι`, and
send `ι b * σ * ι c` to `q ^ N` times the trace of `c * b`. Every coefficient arising this way is
the specialization of a fixed two-variable Laurent polynomial, so induction on the number of
strands produces the interpolating polynomial. Uniqueness is
`TauCeti.KnotTheory.homflySpecialization_jointly_injective`.

## Main definitions

* `TauCeti.KnotTheory.homflyUnknot K`: the unknot value `(a - a⁻¹) z⁻¹`.
* `TauCeti.MarkovBraid.homfly K β`: the HOMFLY polynomial of the closure of `β`.

## Main results

* `TauCeti.KnotTheory.exists_homflySpecialization_eq_jimboWeightedTrace`: the weighted Jimbo
  traces of a braid interpolate to a two-variable Laurent polynomial.
* `TauCeti.MarkovBraid.homflySpecialization_homfly` and
  `TauCeti.MarkovBraid.homfly_eq_of_homflySpecialization_eq`: the HOMFLY polynomial is the unique
  Laurent polynomial specializing to the normalized Jimbo traces.
* `TauCeti.MarkovEquiv.homfly_eq`: Markov-equivalent braids have the same HOMFLY polynomial.
* `TauCeti.MarkovBraid.homfly_skein` and `TauCeti.MarkovBraid.homfly_one`: the skein relation and
  the values on trivial braids.

## References

* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett, A. Ocneanu, *A new polynomial
  invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 4–6 (the trace construction of HOMFLY).
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527–553 (the `sl_N` specializations as enhanced Jimbo traces).
-/

public section

noncomputable section

open LaurentPolynomial MonoidAlgebra

namespace TauCeti

namespace KnotTheory

variable (K : Type*) [Field K]

/-- The value `(a - a⁻¹) z⁻¹` of the unreduced HOMFLY polynomial on the unknot, in
`K[a, a⁻¹, z, z⁻¹]` with `z` the inner and `a` the outer Laurent variable. Its `sl_N`
specialization is the quantum dimension `[N]_q`. -/
def homflyUnknot : LaurentPolynomial (LaurentPolynomial K) :=
  (T 1 - T (-1)) * C (T (-1))

/-- The defining formula of the unknot value. -/
theorem homflyUnknot_def : homflyUnknot K = (T 1 - T (-1)) * C (T (-1)) := (rfl)

variable {K}

/-- The outer variable `a` specializes to `q ^ N`. -/
private theorem homflySpecialization_T_one (N : ℕ) :
    homflySpecialization K N (T 1) =
      ↑((Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero) ^ N) := by
  simp

/-- The inverse outer variable `a⁻¹` specializes to `q⁻¹ ^ N`. -/
private theorem homflySpecialization_T_neg_one (N : ℕ) :
    homflySpecialization K N (T (-1)) =
      ↑((Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)⁻¹ ^ N) := by
  simp [← zpow_natCast]

/-- The inner variable `z` specializes to `q - q⁻¹`. -/
private theorem homflySpecialization_C_T_one (N : ℕ) :
    homflySpecialization K N (C (T 1)) =
      ↑(Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero) -
        ↑(Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)⁻¹ := by
  simp

/-- The unknot value specializes to the quantum dimension, the sum of the enhancement weights. -/
@[simp]
theorem homflySpecialization_homflyUnknot (N : ℕ) :
    homflySpecialization K N (homflyUnknot K) =
      ∑ a : Fin N, jimboWeight (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero) a := by
  have hz := (transcendental_ratFunc_X_sub_inv K).ne_zero
  have hC : homflySpecialization K N (C (T (-1))) = (RatFunc.X - RatFunc.X⁻¹)⁻¹ := by
    simp [homflySpecialization_C]
  have hq : (↑(Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero) -
      ↑(Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)⁻¹ : RatFunc K) =
      RatFunc.X - RatFunc.X⁻¹ := by
    simp
  rw [homflyUnknot_def, map_mul, map_sub, hC, homflySpecialization_T_one,
    homflySpecialization_T_neg_one, ← jimboWeight_sum, hq, mul_comm, inv_mul_cancel_left₀ hz]

/-! ### Interpolating the weighted traces -/

variable (K) in
/-- The weighted Jimbo trace with `N` colours at `q = X`, extended linearly over the
`N`-th HOMFLY specialization to the group algebra with HOMFLY coefficients. -/
private def traceEval (N n : ℕ) :
    (LaurentPolynomial (LaurentPolynomial K))[BraidGroup n] →+ RatFunc K :=
  liftNC (homflySpecialization K N).toAddMonoidHom fun b ↦
    jimboWeightedTrace (N := N) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero) b

private theorem traceEval_single (N n : ℕ) (b : BraidGroup n)
    (c : LaurentPolynomial (LaurentPolynomial K)) :
    traceEval K N n (single b c) = homflySpecialization K N c *
      jimboWeightedTrace (N := N) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero) b := by
  simp [traceEval, liftNC_single]

private theorem traceEval_smul (N n : ℕ) (c : LaurentPolynomial (LaurentPolynomial K))
    (x : (LaurentPolynomial (LaurentPolynomial K))[BraidGroup n]) :
    traceEval K N n (c • x) = homflySpecialization K N c * traceEval K N n x := by
  induction x using MonoidAlgebra.induction_on generalizing c with
  | of g => rw [of_apply, smul_single', traceEval_single, traceEval_single, map_mul, mul_assoc]
  | add x x' hx hx' => rw [smul_add, map_add, map_add, hx, hx', mul_add]
  | smul r x hx => rw [smul_smul, hx, hx, map_mul, mul_assoc]

/-- The weighted traces kill the Hecke skein relators with parameter `z`. -/
private theorem traceEval_heckeRelator (N n : ℕ) (b c : BraidGroup n) (i : Fin (n - 1)) :
    traceEval K N n (BraidGroup.heckeRelator _ (C (T 1)) b c i) = 0 := by
  rw [BraidGroup.heckeRelator_def, map_sub, map_sub, traceEval_single, traceEval_single,
    traceEval_single, jimboWeightedTrace_skein, homflySpecialization_C_T_one]
  simp

variable (K) in
/-- The elements of the group algebra whose extended weighted traces are, for all `N`
simultaneously, the specializations of one two-variable Laurent polynomial. -/
private def realizable (n : ℕ) :
    Submodule (LaurentPolynomial (LaurentPolynomial K))
      (LaurentPolynomial (LaurentPolynomial K))[BraidGroup n] where
  carrier := {x | ∃ P, ∀ N, homflySpecialization K N P = traceEval K N n x}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P + Q, fun N ↦ by rw [map_add, map_add, hP, hQ]⟩
  smul_mem' := by
    rintro c x ⟨P, hP⟩
    exact ⟨c * P, fun N ↦ by rw [map_mul, hP, traceEval_smul]⟩

private theorem single_mem_realizable_iff {n : ℕ} (b : BraidGroup n) :
    single b 1 ∈ realizable K n ↔ ∃ P, ∀ N, homflySpecialization K N P =
      jimboWeightedTrace (N := N) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero) b := by
  simp [realizable, traceEval_single]

/-- **The weighted Jimbo traces interpolate.** For every braid there is a two-variable Laurent
polynomial whose specialization `a = q ^ N`, `z = q - q⁻¹` is the weighted trace of the braid in
the Jimbo representation with `N` colours, for every `N`. -/
theorem exists_homflySpecialization_eq_jimboWeightedTrace {n : ℕ} (b : BraidGroup (n + 1)) :
    ∃ P : LaurentPolynomial (LaurentPolynomial K), ∀ N,
      homflySpecialization K N P =
        jimboWeightedTrace (N := N) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero) b := by
  induction n with
  | zero =>
    have hb : b = 1 := by
      have h : MonoidHom.id (BraidGroup 1) = 1 := BraidGroup.hom_ext fun i ↦ i.elim0
      exact DFunLike.congr_fun h b
    refine ⟨homflyUnknot K, fun N ↦ ?_⟩
    rw [hb, jimboWeightedTrace_one, pow_one, homflySpecialization_homflyUnknot]
  | succ m ih =>
    rw [← single_mem_realizable_iff]
    suffices h : BraidGroup.strandSpan (LaurentPolynomial (LaurentPolynomial K)) m ⊔
        BraidGroup.heckeSkein _ (C (T 1)) (m + 2) ≤ realizable K (m + 2) by
      rw [BraidGroup.strandSpan_sup_heckeSkein_eq_top] at h
      exact h Submodule.mem_top
    refine sup_le ?_ ?_
    · refine (BraidGroup.strandSpan_le_iff _).mpr ⟨fun d ↦ ?_, fun d e ↦ ?_⟩
      · -- An uncrossed strand contributes the quantum dimension.
        obtain ⟨P, hP⟩ := ih d
        refine ⟨P * homflyUnknot K, fun N ↦ ?_⟩
        rw [traceEval_single, map_one, one_mul, jimboWeightedTrace_strandIncl, map_mul, hP,
          homflySpecialization_homflyUnknot]
      · -- A single crossing with the new strand contributes `a`, by conjugation and
        -- stabilization.
        obtain ⟨P, hP⟩ := ih (e * d)
        refine ⟨T 1 * P, fun N ↦ ?_⟩
        rw [traceEval_single, map_one, one_mul, jimboWeightedTrace_mul_comm, ← mul_assoc,
          ← map_mul, jimboWeightedTrace_stabilize, map_mul, hP, homflySpecialization_T_one]
    · refine BraidGroup.heckeSkein_le_iff _ _ |>.mpr fun b c i ↦ ?_
      exact ⟨0, fun N ↦ by rw [map_zero, traceEval_heckeRelator]⟩

end KnotTheory

/-! ### The HOMFLY polynomial of a braid closure -/

namespace MarkovBraid

open KnotTheory

variable (K : Type*) [Field K]

/-- The HOMFLY polynomial of the closure of a braid, in `K[a, a⁻¹, z, z⁻¹]` with `z` the inner
and `a` the outer Laurent variable. It is the writhe normalization `a ^ (-e)`, for exponent sum
`e`, of the interpolation of the weighted Jimbo traces, so its `sl_N` specializations are the
normalized Jimbo traces (`homflySpecialization_homfly`), which determine it. The unknot has value
`(a - a⁻¹) z⁻¹`. -/
def homfly (β : MarkovBraid) : LaurentPolynomial (LaurentPolynomial K) :=
  T (-Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) *
    (exists_homflySpecialization_eq_jimboWeightedTrace (K := K) β.braid).choose

/-- **The `sl_N` specializations of the HOMFLY polynomial** are the writhe-normalized Jimbo
traces with `N` colours at `q = X`. -/
@[simp]
theorem homflySpecialization_homfly (β : MarkovBraid) (N : ℕ) :
    homflySpecialization K N (β.homfly K) =
      β.jimboTrace (N := N) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero) := by
  rw [homfly, map_mul, (exists_homflySpecialization_eq_jimboWeightedTrace β.braid).choose_spec,
    jimboTrace_def, homflySpecialization_T]
  simp [← zpow_natCast, ← zpow_mul]

/-- **Uniqueness of the HOMFLY polynomial**: a two-variable Laurent polynomial whose
positive-rank specializations are the normalized Jimbo traces of a braid is its HOMFLY
polynomial. -/
theorem homfly_eq_of_homflySpecialization_eq {β : MarkovBraid}
    {P : LaurentPolynomial (LaurentPolynomial K)}
    (h : ∀ N, homflySpecialization K (N + 1) P =
      β.jimboTrace (N := N + 1) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)) :
    β.homfly K = P :=
  homflySpecialization_jointly_injective K <| funext fun N ↦
    (homflySpecialization_homfly K β (N + 1)).trans (h N).symm

/-- The HOMFLY polynomial of the trivial braid on `n + 1` strands, whose closure is the
`(n + 1)`-component unlink. -/
@[simp]
theorem homfly_one (n : ℕ) : homfly K ⟨n, 1⟩ = homflyUnknot K ^ (n + 1) :=
  homfly_eq_of_homflySpecialization_eq K fun N ↦ by
    rw [map_pow, homflySpecialization_homflyUnknot, jimboTrace_one]

/-- **The HOMFLY skein relation** `a P(L₊) - a⁻¹ P(L₋) = z P(L₀)`, for a crossing in any braid
context. -/
theorem homfly_skein {n : ℕ} (b c : BraidGroup (n + 1)) (i : Fin n) :
    T 1 * homfly K ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ -
        T (-1) * homfly K ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ =
      C (T 1) * homfly K ⟨n, b * c⟩ := by
  refine homflySpecialization_jointly_injective K (funext fun N ↦ ?_)
  simp only [map_sub, map_mul, homflySpecialization_homfly, homflySpecialization_T_one,
    homflySpecialization_T_neg_one, homflySpecialization_C_T_one]
  exact jimboTrace_skein _ b c i

end MarkovBraid

/-- **The HOMFLY polynomial is a link invariant on braid closures**: Markov-equivalent braids
have the same HOMFLY polynomial. -/
theorem MarkovEquiv.homfly_eq (K : Type*) [Field K] {β γ : MarkovBraid} (h : MarkovEquiv β γ) :
    β.homfly K = γ.homfly K :=
  MarkovBraid.homfly_eq_of_homflySpecialization_eq K fun N ↦ by
    rw [MarkovBraid.homflySpecialization_homfly, h.jimboTrace_eq]

end TauCeti
