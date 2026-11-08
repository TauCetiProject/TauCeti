/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.FormInvariants
import TauCeti.NumberTheory.NumberField.Units.Signature.Integer
import TauCeti.NumberTheory.QuadraticForm.Global.ArchimedeanSymbol
import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula

/-!
# Orthogonal sums of systems of local invariants

The local invariants of an orthogonal sum `Q ⊥ R` of regular quadratic forms over a number field
`K` are determined by those of `Q` and `R`: ranks and real positive indices add, discriminants
multiply, and at a finite place `v` the Hasse signs satisfy

```text
s_v(Q ⊥ R) = s_v(Q) · s_v(R) · (d_v(Q), d_v(R))_v.
```

This file defines the corresponding operation `GlobalFormInvariants.prod` on abstract systems of
local invariants, and proves that `QuadraticForm.globalInvariants` carries orthogonal sums of
forms to it.

It then splits a line off an admissible system. Let `I` be an admissible system of rank
`n ≥ 4` and `c ∈ Kˣ` a unit which is positive only at real places where the positive index of `I`
is positive, and negative only at real places where its negative index is positive. Then `I` is
the sum of the system of the line `⟨c⟩` and an admissible system `J` of rank `n - 1`. The Hasse
signs of `J` are `s_v(I) · (c, d c)_v`, where `d` represents the discriminant of `I`; the
real Hasse signs change by the real symbols `(c, d c)_w`, so the product relation for `J` is that
of `I` multiplied by Hilbert's product formula for `c` and `d c`. The two small-rank exceptions of
admissibility cannot occur for `J`, because its rank is at least three. A suitable `c` exists for
every admissible `I` of rank at least four, since every pattern of signs at the real places is
realized by a unit of `K`.

Consequently, if `J` is the system of a regular form `T`, then `I` is the system of `⟨c⟩ ⊥ T`,
by `QuadraticForm.globalInvariants_prod`. By induction on the rank, realizing every admissible
system of rank at least three by a global form reduces to realizing those of rank three.

## Main definitions

* `TauCeti.NumberField.QuadraticForm.GlobalFormInvariants.prod`: the orthogonal sum of two
  systems of local invariants.

## Main results

* `QuadraticForm.globalInvariants_prod`: the system of an orthogonal sum of regular forms is the
  sum of their systems.
* `QuadraticForm.globalInvariants_weightedSumSquares_fin_one`: the system of the line `⟨c⟩`.
* `GlobalFormInvariants.IsAdmissible.exists_isAdmissible_eq_prod_iff`: an admissible system of
  rank at least four splits as the system of `⟨c⟩` plus an admissible system exactly when the
  real signs of `c` are compatible with its real signature.
* `GlobalFormInvariants.IsAdmissible.exists_eq_prod`: every admissible system of rank at least
  four splits off the system of some line.

## References

* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, §3.3, Proposition 7: the
  case `n ≥ 4` of the existence of a rational form with prescribed invariants, which splits off
  a line `⟨a⟩` with prescribed real signs in the same way.
* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1, the existence of a
  global form with prescribed local behavior over a number field.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace TauCeti
open TauCeti.NumberField.QuadraticForm (GlobalFormInvariants)

universe u v w

namespace TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

variable {K : Type u} [Field K] [NumberField K]

/-- **The orthogonal sum of two systems of local invariants**, modelled on the invariants of an
orthogonal sum of forms: ranks, discriminants and real positive indices add, and the Hasse sign at
a finite place `v` is `s_v(I) · s_v(J) · (d_v(I), d_v(J))_v`. -/
def prod (I J : GlobalFormInvariants K) : GlobalFormInvariants K where
  rank := I.rank + J.rank
  discr := I.discr + J.discr
  finiteHasse v := I.finiteHasse v * J.finiteHasse v *
    hilbertSymbolOnSquareClasses (I.discrAtFinitePlace v) (J.discrAtFinitePlace v)
  realPositiveIndex w := I.realPositiveIndex w + J.realPositiveIndex w

variable (I J : GlobalFormInvariants K)

/-- The rank of an orthogonal sum is the sum of the ranks. -/
@[simp]
theorem prod_rank : (I.prod J).rank = I.rank + J.rank :=
  (rfl)

/-- The discriminant of an orthogonal sum is the sum of the discriminants. -/
@[simp]
theorem prod_discr : (I.prod J).discr = I.discr + J.discr :=
  (rfl)

/-- The Hasse sign of an orthogonal sum at a finite place. -/
@[simp]
theorem prod_finiteHasse (v : HeightOneSpectrum (𝓞 K)) :
    (I.prod J).finiteHasse v = I.finiteHasse v * J.finiteHasse v *
      hilbertSymbolOnSquareClasses (I.discrAtFinitePlace v) (J.discrAtFinitePlace v) :=
  (rfl)

/-- The positive index of an orthogonal sum at a real place is the sum of the positive indices. -/
@[simp]
theorem prod_realPositiveIndex (w : {w : InfinitePlace K // w.IsReal}) :
    (I.prod J).realPositiveIndex w = I.realPositiveIndex w + J.realPositiveIndex w :=
  (rfl)

/-- The discriminant of an orthogonal sum at a finite place is the sum of the discriminants. -/
theorem prod_discrAtFinitePlace (v : HeightOneSpectrum (𝓞 K)) :
    (I.prod J).discrAtFinitePlace v = I.discrAtFinitePlace v + J.discrAtFinitePlace v := by
  simp only [discrAtFinitePlace_def, prod_discr, map_add]

/-- The discriminant of an orthogonal sum at a real place is the sum of the discriminants. -/
theorem prod_discrAtRealPlace (w : {w : InfinitePlace K // w.IsReal}) :
    (I.prod J).discrAtRealPlace w = I.discrAtRealPlace w + J.discrAtRealPlace w := by
  simp only [discrAtRealPlace_def, prod_discr, map_add]

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **The local invariants of an orthogonal sum.** The system of local invariants of `Q ⊥ R` is
the orthogonal sum of the systems of `Q` and `R`. -/
theorem globalInvariants_prod (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (R : _root_.QuadraticForm K W) (hR : R.Nondegenerate) :
    globalInvariants (Q.prod R) (hQ.prod hR) =
      (Q.globalInvariants hQ).prod (R.globalInvariants hR) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  refine GlobalFormInvariants.ext ?_ ?_ ?_ ?_
  · simp
  · rw [globalInvariants_discr, GlobalFormInvariants.prod_discr, globalInvariants_discr,
      globalInvariants_discr, formClass_prod, RegularFormClass.discr_add]
  · funext v
    simp only [globalInvariants_finiteHasse, GlobalFormInvariants.prod_finiteHasse,
      GlobalFormInvariants.discrAtFinitePlace_def, globalInvariants_discr]
    exact finiteHasse_prod Q hQ R hR v
  · funext w
    simp

/-- **The local invariants of a line** `⟨c⟩`: rank one, discriminant the class of `c`, trivial
Hasse sign at every finite place, and positive index `1` or `0` at a real place according to the
sign of `c` there. -/
theorem globalInvariants_weightedSumSquares_fin_one (c : Kˣ)
    (h : (QuadraticMap.weightedSumSquares K ![(c : K)]).Nondegenerate) :
    globalInvariants (QuadraticMap.weightedSumSquares K ![(c : K)]) h =
      { rank := 1, discr := squareClass c, finiteHasse := 1,
        realPositiveIndex := fun w => if 0 < embedding_of_isReal w.2 (c : K) then 1 else 0 } := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  refine GlobalFormInvariants.ext ?_ ?_ ?_ ?_
  · simp
  · have hw : (fun i => ((![c] i : Kˣ) : K)) = ![(c : K)] := by
      funext i
      fin_cases i
      rfl
    rw [globalInvariants_discr]
    convert discr_formClass_weightedSumSquares ![c] (hw ▸ h) using 3
    · rw [hw]
    · simp
  · funext v
    rw [globalInvariants_finiteHasse]
    exact finiteHasse_eq_one_of_finrank_le_one _ h (by simp) v
  · funext w
    rw [globalInvariants_realPositiveIndex, realPositiveIndex_weightedSumSquares]
    dsimp only
    split_ifs with hc <;> simp [hc]

end QuadraticForm

namespace TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

-- Hilbert's product formula, used for the residual system, is stated for number fields in `Type`.
variable {K : Type} [Field K] [NumberField K]

/-- Raising the negative index from `m` to `m + 1` multiplies the real Hasse sign `(-1)^C(m, 2)` by
`(-1)^m`, since `C(m + 1, 2) = C(m, 2) + m`. -/
private theorem neg_one_pow_succ_choose_two_mul_neg_one_pow (m : ℕ) :
    (-1 : ℤˣ) ^ (m + 1).choose 2 * (-1) ^ m = (-1) ^ m.choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm, pow_add, mul_assoc, ← pow_add,
    Even.neg_one_pow ⟨m, rfl⟩, mul_one]

/-- The system obtained from `I` by removing a line `⟨c⟩`, computed with a representative `δ` of the
discriminant of `I`: rank `n - 1`, discriminant `δ c`, Hasse signs `s_v(I) · (c, δ c)_v`, and the
positive index at a real place lowered by one where `c` is positive. -/
private def residual (I : GlobalFormInvariants K) (c δ : Kˣ) : GlobalFormInvariants K where
  rank := I.rank - 1
  discr := squareClass (δ * c)
  finiteHasse v :=
    I.finiteHasse v * hilbertSymbol (v.unitAtFinitePlace c) (v.unitAtFinitePlace (δ * c))
  realPositiveIndex w :=
    I.realPositiveIndex w - if 0 < embedding_of_isReal w.2 (c : K) then 1 else 0

variable {I : GlobalFormInvariants K}

open _root_.QuadraticForm in
/-- Removing a line `⟨c⟩` and adding it back recovers the system, provided `c` is positive only
where the positive index is. -/
private theorem eq_prod_residual (hn : 1 ≤ I.rank) {c δ : Kˣ} (hδ : squareClass δ = I.discr)
    (h : (QuadraticMap.weightedSumSquares K ![(c : K)]).Nondegenerate)
    (hpos : ∀ w, 0 < embedding_of_isReal w.2 (c : K) → 0 < I.realPositiveIndex w) :
    I = (globalInvariants (QuadraticMap.weightedSumSquares K ![(c : K)]) h).prod
      (residual I c δ) := by
  rw [globalInvariants_weightedSumSquares_fin_one]
  refine GlobalFormInvariants.ext ?_ ?_ ?_ ?_
  · simp only [prod_rank, residual]
    omega
  · simp only [prod_discr, residual, ← hδ, ← squareClass_mul]
    exact (squareClass_eq_iff_isSquare_mul _ _).mpr ⟨δ * c, by simp only [mul_comm, mul_left_comm]⟩
  · funext v
    simp only [prod_finiteHasse, residual, Pi.one_apply, one_mul, discrAtFinitePlace_def,
      ← HeightOneSpectrum.squareClass_unitAtFinitePlace, hilbertSymbolOnSquareClasses_squareClass,
      mul_assoc,
      Int.units_mul_self, mul_one]
  · funext w
    simp only [prod_realPositiveIndex, residual]
    split_ifs with hc
    · have := hpos w hc
      omega
    · omega

/-- At a real place the residual system satisfies the discriminant condition of admissibility: its
discriminant is the class of `(-1)^q` for its negative index `q`. -/
private theorem discrAtRealPlace_residual (hI : I.IsAdmissible) {c δ : Kˣ}
    (hδ : squareClass δ = I.discr)
    (hneg : ∀ w, embedding_of_isReal w.2 (c : K) < 0 → 0 < I.realNegativeIndex w)
    (hpos : ∀ w, 0 < embedding_of_isReal w.2 (c : K) → 0 < I.realPositiveIndex w)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (residual I c δ).discrAtRealPlace w =
      (residual I c δ).realNegativeIndex w • squareClass (-1 : ℝˣ) := by
  have hle := hI.realPositiveIndex_le_rank w
  have hd := hI.discrAtRealPlace_eq w
  rw [discrAtRealPlace_def, ← hδ, ← squareClass_unitAtRealPlace, realNegativeIndex_def] at hd
  simp only [discrAtRealPlace_def, realNegativeIndex_def, residual]
  rw [← squareClass_unitAtRealPlace, map_mul, squareClass_mul, hd]
  rcases ((map_ne_zero (embedding_of_isReal w.2)).mpr c.ne_zero).lt_or_gt with hc | hc
  · -- Where `c` is negative, the negative index drops by one and `[c] = [-1]`.
    have hq := hneg w hc
    rw [realNegativeIndex_def] at hq
    obtain ⟨m, hm⟩ : ∃ m, I.rank - I.realPositiveIndex w = m + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
    have hm' : I.rank - 1 - I.realPositiveIndex w = m := by omega
    simp only [hc.not_gt, ↓reduceIte, Nat.sub_zero]
    rw [hm', hm, (Units.squareClass_eq_squareClass_neg_one_iff_neg (unitAtRealPlace w c)).mpr
        (by rwa [unitAtRealPlace_apply]), succ_nsmul]
    -- The goal's addition and zero are reached from the generic ones only by unfolding instances,
    -- so `rw [add_assoc, ZModModule.add_self, add_zero]` fails; the step is a typed term.
    exact (add_assoc _ _ _).trans
      ((congrArg (_ + ·) (ZModModule.add_self (squareClass (-1 : ℝˣ)))).trans
        (add_zero (m • squareClass (-1 : ℝˣ))))
  · -- Where `c` is positive, the negative index and the discriminant are unchanged.
    have hp := hpos w hc
    have hq : I.rank - 1 - (I.realPositiveIndex w - 1) = I.rank - I.realPositiveIndex w := by
      omega
    simp only [hc, ↓reduceIte]
    rw [(Units.squareClass_eq_zero_iff_pos (unitAtRealPlace w c)).mpr
      (by rwa [unitAtRealPlace_apply]), hq]
    -- As above, `add_zero` must be stated at the explicit square class to match the goal's zero.
    exact add_zero ((I.rank - I.realPositiveIndex w) • squareClass (-1 : ℝˣ))

/-- The real Hasse sign of the residual system differs from that of `I` by the real symbol
`(c, δ c)_w`. -/
private theorem realHasse_residual (hI : I.IsAdmissible) {c δ : Kˣ} (hδ : squareClass δ = I.discr)
    (hneg : ∀ w, embedding_of_isReal w.2 (c : K) < 0 → 0 < I.realNegativeIndex w)
    (hpos : ∀ w, 0 < embedding_of_isReal w.2 (c : K) → 0 < I.realPositiveIndex w)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (residual I c δ).realHasse w =
      I.realHasse w * hilbertSymbol (unitAtRealPlace w c) (unitAtRealPlace w (δ * c)) := by
  have hle := hI.realPositiveIndex_le_rank w
  have hdc := discrAtRealPlace_residual hI hδ hneg hpos w
  simp only [discrAtRealPlace_def, realNegativeIndex_def, residual,
    ← squareClass_unitAtRealPlace] at hdc
  simp only [realHasse_def, realNegativeIndex_def, residual]
  rcases ((map_ne_zero (embedding_of_isReal w.2)).mpr c.ne_zero).lt_or_gt with hc | hc
  · -- At a place where `c` is negative the negative index drops by one, from `m + 1` to `m`,
    -- and the symbol `(c, δ c)_w` is the sign `(-1)^m` of `δ c`.
    have hq := hneg w hc
    rw [realNegativeIndex_def] at hq
    obtain ⟨m, hm⟩ : ∃ m, I.rank - I.realPositiveIndex w = m + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
    have hm' : I.rank - 1 - I.realPositiveIndex w = m := by omega
    simp only [hc.not_gt, ↓reduceIte, Nat.sub_zero] at hdc ⊢
    rw [hm', ← squareClass_pow] at hdc
    have hsym : hilbertSymbol (unitAtRealPlace w c) (unitAtRealPlace w (δ * c)) = (-1) ^ m := by
      rcases m.even_or_odd with he | ho
      · rw [he.neg_one_pow, squareClass_one, Units.squareClass_eq_zero_iff_pos] at hdc
        rw [he.neg_one_pow, hilbertSymbol_real_eq_one_iff]
        exact Or.inr hdc
      · rw [ho.neg_one_pow, Units.squareClass_eq_squareClass_neg_one_iff_neg] at hdc
        rw [ho.neg_one_pow, hilbertSymbol_real_eq_neg_one_iff]
        exact ⟨by rwa [unitAtRealPlace_apply], hdc⟩
    rw [hm', hm, hsym, neg_one_pow_succ_choose_two_mul_neg_one_pow]
  · -- At a place where `c` is positive the negative index is unchanged and the symbol is `1`.
    have hp := hpos w hc
    simp only [hc, ↓reduceIte]
    rw [(hilbertSymbol_unitAtRealPlace_eq_one_iff w c _).mpr (Or.inl hc), mul_one]
    congr 2
    omega

namespace IsAdmissible

open _root_.QuadraticForm

/-- **Splitting a line off an admissible system.** Let `I` be an admissible system of rank at least
four and `c ∈ Kˣ` a unit that is positive only at real places where the positive index of `I` is
positive, and negative only where its negative index is positive. Then `I` is the orthogonal sum
of the system of the line `⟨c⟩` and an admissible system. -/
theorem exists_isAdmissible_eq_prod (hI : I.IsAdmissible) (hn : 4 ≤ I.rank) (c : Kˣ)
    (h : (QuadraticMap.weightedSumSquares K ![(c : K)]).Nondegenerate)
    (hpos : ∀ w, 0 < embedding_of_isReal w.2 (c : K) → 0 < I.realPositiveIndex w)
    (hneg : ∀ w, embedding_of_isReal w.2 (c : K) < 0 → 0 < I.realNegativeIndex w) :
    ∃ J : GlobalFormInvariants K, J.IsAdmissible ∧
      I = (globalInvariants (QuadraticMap.weightedSumSquares K ![(c : K)]) h).prod J := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Kˣ, squareClass δ = I.discr := ⟨_, squareClass_toMul_out I.discr⟩
  refine ⟨residual I c δ, ⟨by simp only [residual]; omega, fun w => ?_,
    discrAtRealPlace_residual hI hδ hneg hpos, ?_,
    fun h1 => by simp only [residual] at h1; omega, fun h2 => by simp only [residual] at h2; omega,
    ?_⟩, eq_prod_residual (by omega) hδ h hpos⟩
  · -- Positive indices stay at most the rank.
    have hle := hI.realPositiveIndex_le_rank w
    simp only [residual]
    split_ifs with hc
    · omega
    · have hq := hneg w (lt_of_le_of_ne (not_lt.mp hc) ((map_ne_zero _).mpr c.ne_zero))
      rw [realNegativeIndex_def] at hq
      omega
  · -- Finite support of the Hasse signs.
    have := hI.hasFiniteMulSupport_finiteHasse
    simp only [residual]
    fun_prop
  · -- The product relation, from that of `I` and Hilbert's product formula for `c` and `δ c`.
    have hres : (residual I c δ).finiteHasse = fun v => I.finiteHasse v *
        hilbertSymbol (v.unitAtFinitePlace c) (v.unitAtFinitePlace (δ * c)) := rfl
    -- The finite factor splits as that of `I` times the finite symbols `(c, δ c)_v`.
    rw [hasseProduct_def, hres, finprod_mul_distrib hI.hasFiniteMulSupport_finiteHasse
      (hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace c (δ * c))]
    -- The real factor splits as that of `I` times the real symbols `(c, δ c)_w`.
    rw [Finset.prod_congr rfl fun w _ => realHasse_residual hI hδ hneg hpos w,
      Finset.prod_mul_distrib]
    -- Regroup into the Hasse product of `I`, which is `1`, times Hilbert's product formula.
    rw [mul_mul_mul_comm, ← hasseProduct_def, hI.hasseProduct_eq_one, one_mul]
    exact hilbertSymbol_productFormula c (δ * c)

/-- **Lines that split off an admissible system.** For an admissible system `I` of rank at least
four, the system of the line `⟨c⟩` is a summand of `I` with admissible complement exactly when `c`
is positive only at real places where the positive index of `I` is positive, and negative only
where its negative index is positive. -/
theorem exists_isAdmissible_eq_prod_iff (hI : I.IsAdmissible) (hn : 4 ≤ I.rank) (c : Kˣ)
    (h : (QuadraticMap.weightedSumSquares K ![(c : K)]).Nondegenerate) :
    (∃ J : GlobalFormInvariants K, J.IsAdmissible ∧
      I = (globalInvariants (QuadraticMap.weightedSumSquares K ![(c : K)]) h).prod J) ↔
      ∀ w, (0 < embedding_of_isReal w.2 (c : K) → 0 < I.realPositiveIndex w) ∧
        (embedding_of_isReal w.2 (c : K) < 0 → 0 < I.realNegativeIndex w) := by
  refine ⟨fun ⟨J, hJ, hIJ⟩ w => ?_, fun hc =>
    hI.exists_isAdmissible_eq_prod hn c h (fun w => (hc w).1) fun w => (hc w).2⟩
  have hle := hJ.realPositiveIndex_le_rank w
  subst hIJ
  simp only [realNegativeIndex_def, prod_rank, prod_realPositiveIndex,
    globalInvariants_weightedSumSquares_fin_one]
  constructor
  · intro hc
    simp [hc]
  · intro hc
    simp only [hc.not_gt, ↓reduceIte]
    omega

/-- **Every admissible system of rank at least four splits off a line**: it is the orthogonal
sum of the system of a line `⟨c⟩` and an admissible system of rank one less. -/
theorem exists_eq_prod (hI : I.IsAdmissible) (hn : 4 ≤ I.rank) :
    ∃ (c : Kˣ) (h : (QuadraticMap.weightedSumSquares K ![(c : K)]).Nondegenerate)
      (J : GlobalFormInvariants K), J.IsAdmissible ∧ J.rank + 1 = I.rank ∧
      I = (globalInvariants (QuadraticMap.weightedSumSquares K ![(c : K)]) h).prod J := by
  -- A unit positive exactly at the real places where the positive index of `I` is positive.
  obtain ⟨c, hc⟩ := GlobalNumberFields.signHom_surjective (K := K)
    fun w => if 0 < I.realPositiveIndex w then 1 else -1
  have h : (QuadraticMap.weightedSumSquares K ![(c : K)]).Nondegenerate :=
    QuadraticMap.nondegenerate_weightedSumSquares fun i => by
      fin_cases i
      simp [isRegular_iff_ne_zero]
  have hpos (w) (hw : 0 < embedding_of_isReal w.2 (c : K)) : 0 < I.realPositiveIndex w := by
    by_contra hp
    have := (GlobalNumberFields.signHom_apply_eq_one_iff c w).mpr hw
    simp only [hc, hp, ↓reduceIte] at this
    exact absurd this (by decide)
  have hneg (w) (hw : embedding_of_isReal w.2 (c : K) < 0) : 0 < I.realNegativeIndex w := by
    have hp : ¬0 < I.realPositiveIndex w := by
      intro hp
      have := (GlobalNumberFields.signHom_apply_eq_neg_one_iff c w).mpr hw
      simp only [hc, hp, ↓reduceIte] at this
      exact absurd this (by decide)
    rw [realNegativeIndex_def]
    omega
  obtain ⟨J, hJ, hIJ⟩ := hI.exists_isAdmissible_eq_prod hn c h hpos hneg
  refine ⟨c, h, J, hJ, ?_, hIJ⟩
  have := congrArg GlobalFormInvariants.rank hIJ
  simp only [prod_rank, globalInvariants_weightedSumSquares_fin_one] at this
  omega

end IsAdmissible

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants
