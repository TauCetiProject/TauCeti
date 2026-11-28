/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.ExternalProduct
public import TauCeti.NumberTheory.SecondMoment.GoodTuple
public import TauCeti.RepresentationTheory.CharacterTable.CentralIdempotent
import TauCeti.LinearAlgebra.Trace.Basic
import TauCeti.RingTheory.Polynomial.Monic.OfCoeff.Basic

/-!
# The identity coefficient of the good-label projector

In the group algebra of a product of finite groups, sum the external products of local
character idempotents indexed by good tuples of polynomial labels. The coefficient at the
identity is a sum of products of local squared character degrees divided by the local group
orders. A uniform lower bound on these local weights therefore bounds the identity coefficient
of the complementary projector, the quantity used to discard bad types in a second moment.

The estimate is the coefficient calculation of `New.re_coeff_one_sub_sum_tupleIdem_le` in
[`New/Spanning/MainTerm/BadTypes.lean`][short-proof] of lsernau/grh-lean. The local character
degrees are inputs here, independent of how the representations of a given label are constructed.

[short-proof]:
https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Spanning/MainTerm/BadTypes.lean
-/

public section

open Polynomial

namespace TauCeti.SecondMoment

variable {ι : Type*} (K : ι → Type*) [∀ w, Field (K w)] [Fintype ι] [∀ w, Finite (K w)]

/-- The finite set of tuples whose entries have degree `r`, are all allowed for `M`, and
include a primitive label. -/
noncomputable def goodLabelTuples (M r : ℕ) : Finset (∀ w, (K w)[X]) := by
  classical
  exact (Fintype.piFinset fun w ↦ TauCeti.Polynomial.monicsOfDegree (K w) r).filter (IsGoodTuple M)

/-- Characterize membership in the enumeration of good label tuples of a fixed degree. -/
@[simp] theorem mem_goodLabelTuples {M r : ℕ} {c : ∀ w, (K w)[X]} :
    c ∈ goodLabelTuples K M r ↔ (∀ w, (c w).natDegree = r) ∧ IsGoodTuple M c := by
  classical
  simp only [goodLabelTuples, Finset.mem_filter, Fintype.mem_piFinset,
    TauCeti.Polynomial.mem_monicsOfDegree]
  refine ⟨fun ⟨h, hc⟩ ↦ ⟨fun w ↦ (h w).2, hc⟩, fun ⟨h, hc⟩ ↦ ?_⟩
  exact ⟨fun w ↦ ⟨((isGoodTuple_iff.mp hc).1 w).monic, h w⟩, hc⟩

/-- Counting the enumerated good tuples gives the cardinality of the set of good tuples. -/
theorem card_goodLabelTuples (M r : ℕ) :
    (goodLabelTuples K M r).card =
      {c : ∀ w, (K w)[X] | (∀ w, (c w).natDegree = r) ∧ IsGoodTuple M c}.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext c
  exact mem_goodLabelTuples K

variable {K} {M r : ℕ} {G : ι → Type*} [∀ w, Fintype (G w)]

/-- The component of a good tuple, regarded as an allowed label of the specified degree. -/
def goodLabelComponent (c : goodLabelTuples K M r) (w : ι) :
    {p : (K w)[X] // p.natDegree = r ∧ IsAllowedLabel M p} :=
  ⟨c.val w, ((mem_goodLabelTuples K).mp c.property).1 w,
    (isGoodTuple_iff.mp ((mem_goodLabelTuples K).mp c.property).2).1 w⟩

/-- The underlying polynomial of a good tuple's component. -/
@[simp] theorem goodLabelComponent_coe (c : goodLabelTuples K M r) (w : ι) :
    (goodLabelComponent c w).val = c.val w := (rfl)

/-- Sum the external products of local group-algebra elements over the good tuples. -/
noncomputable def sumGoodLabelProducts {R : Type*} [CommSemiring R]
    (e : ∀ w, {p : (K w)[X] // p.natDegree = r ∧ IsAllowedLabel M p} →
      MonoidAlgebra R (G w)) : MonoidAlgebra R (∀ w, G w) :=
  ∑ c : goodLabelTuples K M r, MonoidAlgebra.externalProduct (fun w ↦ e w (goodLabelComponent c w))

/-- The coefficient of the good-label sum at a tuple of group elements. -/
@[simp] theorem coeff_sumGoodLabelProducts {R : Type*} [CommSemiring R]
    (e : ∀ w, {p : (K w)[X] // p.natDegree = r ∧ IsAllowedLabel M p} →
      MonoidAlgebra R (G w)) (g : ∀ w, G w) :
    (sumGoodLabelProducts e).coeff g =
      ∑ c : goodLabelTuples K M r, ∏ w, (e w (goodLabelComponent c w)).coeff (g w) := by
  simp [sumGoodLabelProducts, MonoidAlgebra.coeff_sum]

variable [∀ w, Group (G w)]

/-- Central local elements give a central good-label sum. -/
theorem sumGoodLabelProducts_mem_center {R : Type*} [CommSemiring R]
    {e : ∀ w, {p : (K w)[X] // p.natDegree = r ∧ IsAllowedLabel M p} →
      MonoidAlgebra R (G w)}
    (he : ∀ w p, e w p ∈ Subalgebra.center R (MonoidAlgebra R (G w))) :
    sumGoodLabelProducts e ∈ Subalgebra.center R (MonoidAlgebra R (∀ w, G w)) := by
  exact Subalgebra.sum_mem _ fun _ _ ↦ MonoidAlgebra.externalProduct_mem_center _ fun w ↦ he w _

/-- Local orthogonal idempotents give an idempotent good-label sum. -/
theorem isIdempotentElem_sumGoodLabelProducts {R : Type*} [CommSemiring R]
    {e : ∀ w, {p : (K w)[X] // p.natDegree = r ∧ IsAllowedLabel M p} →
      MonoidAlgebra R (G w)} (he : ∀ w, OrthogonalIdempotents (e w)) :
    IsIdempotentElem (sumGoodLabelProducts e) := by
  let f : goodLabelTuples K M r ↪ ∀ w, {p : (K w)[X] // p.natDegree = r ∧ IsAllowedLabel M p} :=
    ⟨goodLabelComponent, fun {_ _} hab ↦ Subtype.ext (funext fun w ↦
      congrArg Subtype.val (congrFun hab w))⟩
  exact ((MonoidAlgebra.orthogonalIdempotents_externalProduct he).embedding f).isIdempotentElem_sum

/-- The product of the local degrees supplies a lower bound on the identity coefficient of
each good-tuple character element. Consequently its complementary sum has real identity
coefficient at most `f * ε + exp (-L)`, where `f` is the number of places. The local
squared-degree bound is the only character degree estimate required. -/
theorem re_coeff_one_sub_sum_goodLabelTuples_le {q : ℕ} {ε L : ℝ}
    {V : ∀ w, {p : (K w)[X] // p.natDegree = r ∧ IsAllowedLabel M p} → Type*}
    [∀ w p, AddCommGroup (V w p)] [∀ w p, Module ℂ (V w p)]
    (ρ : ∀ w p, Representation ℂ (G w) (V w p))
    (hdegree : ∀ w p, (1 - r / (q : ℝ)) / (q : ℝ) ^ r ≤
      (Module.finrank ℂ (V w p) : ℝ) ^ 2 / Nat.card (G w))
    (hK : ∀ w, Nat.card (K w) = q) (hM : M ≠ 0) (hr : 0 < r)
    (hε : (1 + M + 2 * r) / q ≤ ε)
    (hL : 2 * r * (2 * r * Real.log q + 1) * L ≤ Fintype.card ι) :
    ((1 - sumGoodLabelProducts (fun w p ↦
      TauCeti.Representation.primitiveCentralIdempotent (ρ w p))).coeff 1).re ≤
      Fintype.card ι * ε + Real.exp (-L) := by
  classical
  let wt : ℝ := (1 - r / q) / (q : ℝ) ^ r
  let d (c : goodLabelTuples K M r) (w : ι) : ℝ :=
    (Module.finrank ℂ (V w (goodLabelComponent c w)) : ℝ) ^ 2 / Nat.card (G w)
  have hcoeff (c : goodLabelTuples K M r) (w : ι) :
      (TauCeti.Representation.primitiveCentralIdempotent
        (ρ w (goodLabelComponent c w))).coeff 1 = (d c w : ℂ) := by
    let p := goodLabelComponent c w
    have hc : (ρ w p).character 1 = Module.finrank ℂ (V w p) := by
      by_cases h : FiniteDimensional ℂ (V w p)
      · exact (ρ w p).char_one
      · simp [_root_.Representation.character, TauCeti.LinearMap.trace_eq_zero_of_not_finite h,
          Module.finrank_of_not_finite h]
    rw [TauCeti.Representation.primitiveCentralIdempotent_coeff, inv_one, hc]
    push_cast [d]
    ring
  simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.coeff_one_one,
    coeff_sumGoodLabelProducts, Pi.one_apply, hcoeff, ← Complex.ofReal_prod,
    ← Complex.ofReal_sum, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  by_cases hε1 : ε ≤ 1
  swap
  · have hnonneg : 0 ≤ ∑ c : goodLabelTuples K M r, ∏ w, d c w := by
      exact Finset.sum_nonneg fun c _ ↦ Finset.prod_nonneg fun w _ ↦ by dsimp [d]; positivity
    rcases isEmpty_or_nonempty ι with h | h
    · rw [Fintype.card_eq_zero, Nat.cast_zero] at hL ⊢
      have hpos : 0 < 2 * (r : ℝ) * (2 * r * Real.log q + 1) := by
        have := Real.log_natCast_nonneg q
        positivity
      have h0 := nonpos_of_mul_nonpos_right hL hpos
      have := Real.one_le_exp (neg_nonneg.mpr h0)
      linarith
    · have hf : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
      have hlarge := one_le_mul_of_one_le_of_one_le hf (le_of_not_ge hε1)
      linarith [Real.exp_pos (-L)]
  have hwt (w : ι) : 0 ≤ wt := by
    have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (hK w ▸ Nat.card_pos)
    have h := (div_le_one hq).mp (hε.trans hε1)
    have hrq : (r : ℝ) / q ≤ 1 := (div_le_one hq).mpr (by linarith [Nat.cast_nonneg (α := ℝ) M])
    exact div_nonneg (sub_nonneg.mpr hrq) (by positivity)
  have hprod (c : goodLabelTuples K M r) : wt ^ Fintype.card ι ≤ ∏ w, d c w := by
    simpa only [Finset.prod_const, Finset.card_univ] using
      (Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ ↦ wt)
        (fun w _ ↦ hwt w) (fun w _ ↦ hdegree w (goodLabelComponent c w)))
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun c _ ↦ hprod c
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe,
    card_goodLabelTuples] at hsum
  exact (sub_le_sub_left hsum 1).trans (one_sub_ncard_isGoodTuple_mul_le hK hM hr hε hε1 hL)

end TauCeti.SecondMoment
