/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Order.Filter.Cofinite
public import TauCeti.Analysis.Normed.Ring.TwoSidedIdeal
import TauCeti.Analysis.Normed.Ring.Units

/-!
# The `c₀` ideal of a bounded product

For a family of normed rings `A i`, the bounded product is `lp A ∞`. Its `c₀` ideal
`lp.c0Ideal A` consists of the bounded families whose coordinate norms tend to `0` along the
cofinite filter. It is a closed two-sided ideal, closed under `star` when the factors are normed
star rings, so for C⋆-algebras `A i` the quotient `lp A ∞ ⧸ lp.c0Ideal A` is a C⋆-algebra by
`TwoSidedIdeal.Quotient.nonUnitalCStarAlgebra` (unital when the factors are nonzero unital
C⋆-algebras, by `lp.inftyCStarAlgebra` and `TwoSidedIdeal.Quotient.cstarAlgebra`).

The quotient norm of the class of `a` is `limsup_i ‖a i‖` along the cofinite filter,
`lp.norm_mk_c0Ideal`. For unital factors with `‖1‖ = 1` and summable geometric series (in
particular, complete normed rings with `‖1‖ = 1`, such as operator algebras on nontrivial spaces),
the quotient class of `a` is a unit if and only if `a i` is eventually a unit along `cofinite` with
uniformly bounded inverse norms (`lp.isUnit_mk_c0Ideal_iff`), and the norm of the quotient inverse
is `limsup_i ‖(a i)⁻¹‖` (`lp.norm_ringInverse_mk_c0Ideal`).

## Main declarations

* `lp.c0Ideal`: the families in `lp A ∞` whose coordinate norms tend to `0` along `cofinite`.
* `lp.isClosed_c0Ideal`: the `c₀` ideal is closed.
* `lp.star_mem_c0Ideal`: the `c₀` ideal is closed under `star`.
* `lp.norm_mk_c0Ideal`: the quotient norm is the limit superior of the coordinate norms.
* `lp.norm_mk_c0Ideal_eq_one_of_forall_norm_eq_one`: a family of norm-one elements has quotient
  norm `1`.
* `lp.normOneClass_quotient_c0Ideal`: in particular, the unit of the quotient has norm `1`.
* `lp.nontrivial_quotient_c0Ideal`: over an infinite index type the quotient by the `c₀` ideal of
  a bounded product of normed rings with `‖1‖ = 1` is nonzero.
* `lp.isUnit_mk_c0Ideal_iff`: invertibility in `lp A ∞ ⧸ lp.c0Ideal A` is eventual coordinate
  invertibility along `cofinite` with uniformly bounded inverse norms.
* `lp.norm_ringInverse_mk_c0Ideal`: the norm of a quotient inverse is the limit superior of the
  coordinate inverse norms.

## References

* B. Blackadar, *Operator Algebras*, II.8.1.
* A. Böttcher, *C\*-Algebras in Numerical Analysis*, Irish Math. Soc. Bull. 45 (2000), 57–101,
  Section 7.
-/

public section

open Filter Topology
open scoped ENNReal

noncomputable section

namespace lp

section NonUnital

variable {ι : Type*} (A : ι → Type*) [∀ i, NonUnitalNormedRing (A i)]

/-- The `c₀` ideal of the bounded product `lp A ∞`: the bounded families whose coordinate norms
tend to `0` along the cofinite filter. -/
def c0Ideal : TwoSidedIdeal (lp A ∞) :=
  .mk' {a | Tendsto (fun i ↦ ‖a i‖) cofinite (𝓝 0)}
    (by simpa using tendsto_const_nhds)
    (fun {a b} ha hb ↦ squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun i ↦ by simpa using norm_add_le (a i) (b i)) (by simpa using ha.add hb))
    (fun {a} ha ↦ by simpa using ha)
    (fun {a b} hb ↦ squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun i ↦ (show ‖(a * b) i‖ ≤ ‖a i‖ * ‖b i‖ by
        simpa [infty_coeFn_mul] using norm_mul_le (a i) (b i)).trans
        (mul_le_mul_of_nonneg_right (norm_apply_le_norm ENNReal.top_ne_zero a i) (norm_nonneg _)))
      (by simpa using hb.const_mul ‖a‖))
    (fun {a b} ha ↦ squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun i ↦ (show ‖(a * b) i‖ ≤ ‖a i‖ * ‖b i‖ by
        simpa [infty_coeFn_mul] using norm_mul_le (a i) (b i)).trans
        (mul_le_mul_of_nonneg_left (norm_apply_le_norm ENNReal.top_ne_zero b i) (norm_nonneg _)))
      (by simpa using ha.mul_const ‖b‖))

variable {A}

/-- A bounded family lies in the `c₀` ideal when its coordinate norms tend to `0` along the
cofinite filter. -/
@[simp]
theorem mem_c0Ideal {a : lp A ∞} :
    a ∈ c0Ideal A ↔ Tendsto (fun i ↦ ‖a i‖) cofinite (𝓝 0) :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a

variable (A) in
/-- The `c₀` ideal is closed in the bounded product: a uniform limit of families vanishing at
infinity vanishes at infinity. -/
theorem isClosed_c0Ideal : IsClosed (c0Ideal A : Set (lp A ∞)) := by
  refine isClosed_of_closure_subset fun a ha ↦ mem_c0Ideal.2 ?_
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.1 ha (ε / 2) (half_pos hε)
  filter_upwards [Metric.tendsto_nhds.1 (mem_c0Ideal.1 hb) (ε / 2) (half_pos hε)] with i hi
  rw [Real.dist_eq, sub_zero, abs_norm] at hi ⊢
  have hi' : ‖a i - b i‖ ≤ dist a b := by
    simpa [dist_eq_norm] using norm_apply_le_norm ENNReal.top_ne_zero (a - b) i
  calc ‖a i‖ ≤ ‖a i - b i‖ + ‖b i‖ := norm_le_norm_sub_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hi'.trans hab.le) hi
    _ = ε := add_halves ε

/-- The closedness of the `c₀` ideal as an instance, so that the quotient
`lp A ∞ ⧸ c0Ideal A` is a normed ring, and a C⋆-algebra when the factors are. -/
instance : IsClosed (c0Ideal A : Set (lp A ∞)) :=
  isClosed_c0Ideal A

/-- The `c₀` ideal is closed under `star`. -/
theorem star_mem_c0Ideal [∀ i, StarRing (A i)] [∀ i, NormedStarGroup (A i)] {a : lp A ∞}
    (ha : a ∈ c0Ideal A) : star a ∈ c0Ideal A :=
  mem_c0Ideal.2 (by simpa [lp.star_apply] using mem_c0Ideal.1 ha)

/-- Over a finite index type both sides of `lp.norm_mk_c0Ideal` are `0`: every family lies in the
`c₀` ideal, and the cofinite filter is `⊥`, so the limit superior is `sInf` of all of `ℝ`, which
is `0` by `Real.sInf_of_not_bddBelow`. -/
private theorem norm_mk_c0Ideal_of_finite [Finite ι] (a : lp A ∞) :
    ‖TwoSidedIdeal.Quotient.mk (c0Ideal A) a‖ = limsup (fun i ↦ ‖a i‖) cofinite := by
  rw [TwoSidedIdeal.Quotient.eq_zero_iff_mem.2 (mem_c0Ideal.2 (by simp [cofinite_eq_bot])),
    _root_.norm_zero, cofinite_eq_bot, limsup, limsSup, map_bot]
  simp only [eventually_bot, Set.ofPred_true]
  exact (Real.sInf_of_not_bddBelow not_bddBelow_univ).symm

/-- **The quotient norm of the bounded product by the `c₀` ideal** is the limit superior of the
coordinate norms along the cofinite filter. For a finite index type both sides are `0`. -/
theorem norm_mk_c0Ideal (a : lp A ∞) :
    ‖TwoSidedIdeal.Quotient.mk (c0Ideal A) a‖ = limsup (fun i ↦ ‖a i‖) cofinite := by
  rcases finite_or_infinite ι with hι | hι
  · exact norm_mk_c0Ideal_of_finite a
  have hbdd : IsBoundedUnder (· ≤ ·) cofinite (fun i ↦ ‖a i‖) :=
    isBoundedUnder_of ⟨‖a‖, fun i ↦ norm_apply_le_norm ENNReal.top_ne_zero a i⟩
  have hcobdd : IsCoboundedUnder (· ≤ ·) cofinite (fun i ↦ ‖a i‖) :=
    (isBoundedUnder_of ⟨0, fun i ↦ norm_nonneg (a i)⟩).isCoboundedUnder_le
  set L := limsup (fun i ↦ ‖a i‖) cofinite
  have hL : 0 ≤ L := le_limsup_of_frequently_le (Frequently.of_forall fun i ↦ norm_nonneg _) hbdd
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε ↦ ?_) ?_
  · -- remove the finitely many coordinates where `‖a i‖ ≥ L + ε / 2`
    have hev : ∀ᶠ i in cofinite, ‖a i‖ < L + ε / 2 :=
      eventually_lt_of_limsup_lt (by linarith) hbdd
    classical
    let F : Set ι := {i | L + ε / 2 ≤ ‖a i‖}
    have hF : F.Finite := by simpa [F, not_lt] using hev
    let y : lp A ∞ := ⟨fun i ↦ if i ∈ F then a i else 0, memℓp_infty_iff.2
      ⟨‖a‖, by
        rintro _ ⟨i, rfl⟩
        by_cases hi : i ∈ F
        · simpa [hi] using norm_apply_le_norm ENNReal.top_ne_zero a i
        · simp [hi]⟩⟩
    have hy : y ∈ c0Ideal A := by
      refine mem_c0Ideal.2 (tendsto_const_nhds.congr' ?_)
      filter_upwards [hF.compl_mem_cofinite] with i hi
      simp [y, show i ∉ F from hi]
    have hbelow : BddBelow ((‖a + ·‖) '' (c0Ideal A : Set (lp A ∞))) :=
      ⟨0, by rintro _ ⟨z, _, rfl⟩; exact norm_nonneg _⟩
    rw [TwoSidedIdeal.Quotient.norm_mk_eq]
    refine (csInf_le hbelow ⟨-y, (c0Ideal A).neg_mem hy, rfl⟩).trans_lt
      ((norm_le_of_forall_le (by positivity) fun i ↦ ?_).trans_lt (by linarith : L + ε / 2 < L + ε))
    by_cases hi : i ∈ F
    · have h0 : (a + -y) i = 0 := by
        rw [lp.coeFn_add, lp.coeFn_neg, Pi.add_apply, Pi.neg_apply]
        simp [y, hi]
      simpa [h0] using (by positivity : (0 : ℝ) ≤ L + ε / 2)
    · have h0 : (a + -y) i = a i := by
        rw [lp.coeFn_add, lp.coeFn_neg, Pi.add_apply, Pi.neg_apply]
        simp [y, hi]
      rw [h0]
      exact (not_le.1 (show ¬ L + ε / 2 ≤ ‖a i‖ from hi)).le
  · -- every representative `a + z`, `z ∈ c₀`, has norm at least `L`
    rw [TwoSidedIdeal.Quotient.norm_mk_eq]
    refine le_csInf ⟨‖a + 0‖, 0, (c0Ideal A).zero_mem, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε ↦ limsup_le_of_le hcobdd ?_
    filter_upwards [Metric.tendsto_nhds.1 (mem_c0Ideal.1 hz) ε hε] with i hi
    rw [Real.dist_eq, sub_zero, abs_norm] at hi
    have h := norm_apply_le_norm ENNReal.top_ne_zero (a + z) i
    calc ‖a i‖ ≤ ‖a i + z i‖ + ‖z i‖ := by simpa using norm_sub_le (a i + z i) (z i)
      _ ≤ ‖a + z‖ + ε := add_le_add (by simpa using h) hi.le

/-- A bounded family of norm-one elements has quotient norm one modulo the `c₀` ideal. -/
theorem norm_mk_c0Ideal_eq_one_of_forall_norm_eq_one [Infinite ι] (a : lp A ∞)
    (ha : ∀ i, ‖a i‖ = 1) : ‖TwoSidedIdeal.Quotient.mk (c0Ideal A) a‖ = 1 := by
  simp [norm_mk_c0Ideal, ha]

end NonUnital

section Units

variable {ι : Type*} {A : ι → Type*} [∀ i, NormedRing (A i)] [∀ i, NormOneClass (A i)]

/-- Over an infinite index type, the unit of the quotient of a bounded product of normed rings
with `‖1‖ = 1` by the `c₀` ideal has norm one. -/
instance normOneClass_quotient_c0Ideal [Infinite ι] : NormOneClass (lp A ∞ ⧸ c0Ideal A) :=
  ⟨by simpa using norm_mk_c0Ideal_eq_one_of_forall_norm_eq_one (A := A) 1 fun _ ↦ by simp⟩

/-- The quotient of a bounded product of normed rings with `‖1‖ = 1`, over an infinite index type,
by the `c₀` ideal is nonzero. -/
instance nontrivial_quotient_c0Ideal [Infinite ι] : Nontrivial (lp A ∞ ⧸ c0Ideal A) :=
  NormOneClass.nontrivial

private theorem mk_mul_eq_one_iff {x y : lp A ∞} :
    TwoSidedIdeal.Quotient.mk (c0Ideal A) x * TwoSidedIdeal.Quotient.mk (c0Ideal A) y = 1 ↔
      Tendsto (fun i ↦ ‖(1 : A i) - x i * y i‖) cofinite (𝓝 0) := by
  rw [eq_comm, ← map_mul, ← TwoSidedIdeal.Quotient.mk_one (c0Ideal A), TwoSidedIdeal.Quotient.eq,
    mem_c0Ideal]
  simp only [lp.coeFn_sub, lp.infty_coeFn_one, lp.infty_coeFn_mul, Pi.sub_apply, Pi.one_apply,
    Pi.mul_apply]

private theorem mk_mul_eq_one_of_eventually {x y : lp A ∞}
    (h : ∀ᶠ i in cofinite, x i * y i = 1) :
    TwoSidedIdeal.Quotient.mk (c0Ideal A) x * TwoSidedIdeal.Quotient.mk (c0Ideal A) y = 1 :=
  mk_mul_eq_one_iff.mpr <| tendsto_const_nhds.congr' <| by
    filter_upwards [h] with i hi
    simp [hi]

/-- Build a bounded representative of the inverse and the corresponding quotient unit from an
eventual inverse-norm bound along `cofinite`. -/
private theorem exists_unit_mk_c0Ideal {a : lp A ∞} {M : ℝ}
    (hM : ∀ᶠ i in cofinite, IsUnit (a i) ∧ ‖Ring.inverse (a i)‖ ≤ M) :
    ∃ (b : lp A ∞) (u : (lp A ∞ ⧸ c0Ideal A)ˣ),
      (u : lp A ∞ ⧸ c0Ideal A) = TwoSidedIdeal.Quotient.mk (c0Ideal A) a ∧
      (↑u⁻¹ : lp A ∞ ⧸ c0Ideal A) = TwoSidedIdeal.Quotient.mk (c0Ideal A) b ∧
      ∀ᶠ i in cofinite, b i = Ring.inverse (a i) := by
  classical
  let S : Set ι := {i | IsUnit (a i) ∧ ‖Ring.inverse (a i)‖ ≤ M}
  have hS : ∀ᶠ i in cofinite, i ∈ S := hM
  let b : lp A ∞ := ⟨fun i ↦ if i ∈ S then Ring.inverse (a i) else 0, memℓp_infty ⟨max M 0, by
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte]
      exact hi.2.trans (le_max_left M 0)
    · simp [hi]⟩⟩
  refine ⟨b,
    { val := TwoSidedIdeal.Quotient.mk (c0Ideal A) a
      inv := TwoSidedIdeal.Quotient.mk (c0Ideal A) b
      val_inv := mk_mul_eq_one_of_eventually (hS.mono fun i hi ↦ by
        simp [b, hi, Ring.mul_inverse_cancel (a i) hi.1])
      inv_val := mk_mul_eq_one_of_eventually (hS.mono fun i hi ↦ by
        simp [b, hi, Ring.inverse_mul_cancel (a i) hi.1]) },
    rfl, rfl, hS.mono fun i hi ↦ by simp [b, hi]⟩

/-- A bounded family whose coordinates are eventually units along `cofinite` with uniformly bounded
inverse norms projects to a unit modulo `lp.c0Ideal`. -/
theorem isUnit_mk_c0Ideal_of_eventually {a : lp A ∞}
    (h : ∃ M : ℝ, ∀ᶠ i in cofinite, IsUnit (a i) ∧ ‖Ring.inverse (a i)‖ ≤ M) :
    IsUnit (TwoSidedIdeal.Quotient.mk (c0Ideal A) a) := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨_, u, hu, -, -⟩ := exists_unit_mk_c0Ideal hM
  exact hu ▸ u.isUnit

/-- **Invertibility in `lp A ∞ ⧸ lp.c0Ideal A`.** When each factor has `‖1‖ = 1` and summable
geometric series (in particular, when each factor is a complete normed ring with `‖1‖ = 1`), the
quotient class of `a : lp A ∞` is invertible if and only if `a i` is eventually invertible along
`cofinite` with uniformly bounded inverse norms. -/
theorem isUnit_mk_c0Ideal_iff [∀ i, HasSummableGeomSeries (A i)] {a : lp A ∞} :
    IsUnit (TwoSidedIdeal.Quotient.mk (c0Ideal A) a) ↔
      ∃ M : ℝ, ∀ᶠ i in cofinite, IsUnit (a i) ∧ ‖Ring.inverse (a i)‖ ≤ M := by
  refine ⟨fun hu ↦ ?_, isUnit_mk_c0Ideal_of_eventually⟩
  obtain ⟨q, hq₁, hq₂⟩ := isUnit_iff_exists.mp hu
  obtain ⟨b, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective (c0Ideal A) q
  have hr_ev : ∀ᶠ i in cofinite, ‖(1 : A i) - a i * b i‖ < 1 / 2 :=
    (tendsto_order.mp (mk_mul_eq_one_iff.mp hq₁)).2 (1 / 2) (by norm_num)
  have hl_ev : ∀ᶠ i in cofinite, ‖(1 : A i) - b i * a i‖ < 1 / 2 :=
    (tendsto_order.mp (mk_mul_eq_one_iff.mp hq₂)).2 (1 / 2) (by norm_num)
  refine ⟨2 * ‖b‖, (hr_ev.and hl_ev).mono fun i ⟨hr, hl⟩ ↦ ?_⟩
  obtain ⟨hu_i, hnorm_i⟩ :=
    NormedRing.isUnit_and_norm_inverse_le_two_mul_of_norm_one_sub_mul_lt hr hl
  exact ⟨hu_i, hnorm_i.trans (mul_le_mul_of_nonneg_left
    (norm_apply_le_norm ENNReal.top_ne_zero b i) zero_le_two)⟩

/-- The norm of the inverse of a unit in `lp A ∞ ⧸ lp.c0Ideal A` is the limit superior of the
coordinate inverse norms along `cofinite`. -/
theorem norm_ringInverse_mk_c0Ideal [∀ i, HasSummableGeomSeries (A i)] {a : lp A ∞}
    (ha : IsUnit (TwoSidedIdeal.Quotient.mk (c0Ideal A) a)) :
    ‖Ring.inverse (TwoSidedIdeal.Quotient.mk (c0Ideal A) a)‖ =
      limsup (fun i ↦ ‖Ring.inverse (a i)‖) cofinite := by
  obtain ⟨M, hM⟩ := isUnit_mk_c0Ideal_iff.mp ha
  obtain ⟨b, u, hu, hinv, hb_eq⟩ := exists_unit_mk_c0Ideal hM
  rw [← hu, Ring.inverse_unit, hinv, norm_mk_c0Ideal]
  exact limsup_congr (hb_eq.mono fun _ hi ↦ congrArg norm hi)

end Units

end lp
