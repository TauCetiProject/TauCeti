/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Order.Filter.Cofinite
public import TauCeti.Analysis.Normed.Ring.TwoSidedIdeal

/-!
# The `c₀` ideal of a bounded product

For a family of normed rings `A i`, the bounded product is `lp A ∞`. Its `c₀` ideal
`lp.c0Ideal A` consists of the bounded families whose coordinate norms tend to `0` along the
cofinite filter. It is a closed two-sided ideal, closed under `star` when the factors are normed
star rings, so for C⋆-algebras `A i` the quotient `lp A ∞ ⧸ lp.c0Ideal A` is a C⋆-algebra by
`TwoSidedIdeal.Quotient.nonUnitalCStarAlgebra` (unital when the factors are nonzero unital
C⋆-algebras, by `lp.inftyCStarAlgebra` and `TwoSidedIdeal.Quotient.cstarAlgebra`).

The quotient norm of the class of `a` is `limsup_i ‖a i‖` along the cofinite filter,
`lp.norm_mk_c0Ideal`. For instance, in `∏ₙ Mₙ / ⊕ₙ Mₙ`, a family of norm-one elements has
quotient norm `1`, and the family `(aₙ / n)` has quotient norm `0`.

## Main declarations

* `lp.c0Ideal`: the families in `lp A ∞` whose coordinate norms tend to `0` along `cofinite`.
* `lp.isClosed_c0Ideal`: the `c₀` ideal is closed.
* `lp.star_mem_c0Ideal`: the `c₀` ideal is closed under `star`.
* `lp.norm_mk_c0Ideal`: the quotient norm is the limit superior of the coordinate norms.

## References

* B. Blackadar, *Operator Algebras*, II.8.1.
-/

public section

open Filter Topology
open scoped ENNReal

noncomputable section

namespace lp

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

/-- **The quotient norm of the bounded product by the `c₀` ideal** is the limit superior of the
coordinate norms along the cofinite filter. The index type is infinite; for a finite one the
quotient is zero. -/
theorem norm_mk_c0Ideal [Infinite ι] (a : lp A ∞) :
    ‖TwoSidedIdeal.Quotient.mk (c0Ideal A) a‖ = limsup (fun i ↦ ‖a i‖) cofinite := by
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

end lp
