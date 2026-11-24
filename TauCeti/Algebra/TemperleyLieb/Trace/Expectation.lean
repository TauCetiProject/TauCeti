/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Dimension
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import TauCeti.RingTheory.Ideal.Quotient.Star
public import TauCeti.RingTheory.TraceFunctional.Expectation

/-!
# Conditional expectations in the Jones quotient tower

Fix a Markov trace `tr` on the Temperley–Lieb tower over a field `K`, and write
`Q_n = TL_n ⧸ R_n` for the quotient of the algebra on `n` strands by the trace radical `R_n`.
The quotients are finite-dimensional, their induced traces have nondegenerate multiplication
pairings, and strand inclusion induces maps `ι : Q_(n+1) → Q_(n+2)` along which the
unnormalized traces pick up a factor `δ`.

This file constructs the conditional expectations `E : Q_(n+2) → Q_(n+1)` of this tower,
`TauCeti.TemperleyLieb.IsMarkovTrace.quotientExpectation`. The expectation `E a` is the unique
element with `tr (E a * y) = δ⁻¹ * tr (a * ι y)` for all `y`, so for `δ ≠ 0` it preserves the
normalized traces `δ⁻ⁿ tr`. It is a `Q_(n+1)`-bimodule map, and for `δ ≠ 0` it retracts the strand
inclusion. On the tower normal form it is the scaled closure of the last strand:

`E (ι a * e * ι b) = δ⁻¹ • (a * b)`, and for `δ ≠ 0` also `E (ι a) = a`,

where `e` is the last generator, and for `δ ≠ 0` these two identities determine `E`. In
particular `E (δ⁻¹ • e) = δ⁻² • 1`, Jones's relation for the projection of the basic construction.
For `δ ≠ 0` the expectation also computes the sandwich of the tower normal form: one level up,
`e * ι x * e = δ • ι (ι (E x)) * e`, the relation `p x p = E (x) p` of the basic construction for
the Jones projection `p = δ⁻¹ • e`. At a self-adjoint loop parameter, the expectations commute
with the analytic adjoint. No positivity is assumed; at the admissible loop parameters these are
the expectations of the positive Jones quotients.

## Main definitions

* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientExpectation`: the conditional expectation from the
  quotient on `n + 2` strands to the quotient on `n + 1` strands.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientTrace_quotientExpectation_mul`: the defining
  trace identity.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientExpectation_mul_quotientStrandIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientExpectation_quotientStrandIncl_mul`: the bimodule
  identities.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientExpectation_quotientStrandIncl`: for `δ ≠ 0`, the
  expectation retracts the strand inclusion.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientExpectation_mk_strandIncl_mul_e_last_mul`: the
  expectation closes the last strand, with the factor `δ⁻¹`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.eq_quotientExpectation`: for `δ ≠ 0`, the closure
  identities on the tower normal form determine the expectation.
* `TauCeti.TemperleyLieb.IsMarkovTrace.mk_e_last_mul_quotientStrandIncl_mul_mk_e_last`: for
  `δ ≠ 0`, the basic construction relation `e * ι x * e = δ • ι (ι (E x)) * e`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientExpectation_star`: the expectations commute with
  the analytic adjoint.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25, §§3–4.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989, §2.8.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.4–4.5.
-/

public section

namespace TauCeti.TemperleyLieb.IsMarkovTrace

variable {K : Type*} [Field K] {δ : K} {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
  (htr : IsMarkovTrace K δ tr)

/-- The conditional expectation of the Jones quotient tower from `n + 2` to `n + 1` strands: the
element `E a` is determined by `tr (E a * y) = δ⁻¹ * tr (a * ι y)` for all `y`, where `ι` is the
strand map of the quotients. -/
noncomputable def quotientExpectation (n : ℕ) :
    TemperleyLieb K δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)) →ₗ[K]
      TemperleyLieb K δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1)) :=
  ((tr (n + 1)).quotientTrace (htr.map_mul_comm (n + 1))).traceExpectation
    ((tr (n + 1)).quotientTrace_nondegenerate (htr.map_mul_comm (n + 1)))
    (δ⁻¹ • (tr (n + 2)).quotientTrace (htr.map_mul_comm (n + 2))) (htr.quotientStrandIncl n)

/-- The defining trace identity of the conditional expectation. -/
@[simp]
theorem quotientTrace_quotientExpectation_mul (n : ℕ)
    (a : TemperleyLieb K δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)))
    (y : TemperleyLieb K δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    (tr (n + 1)).quotientTrace (htr.map_mul_comm (n + 1)) (htr.quotientExpectation n a * y) =
      δ⁻¹ * (tr (n + 2)).quotientTrace (htr.map_mul_comm (n + 2))
        (a * htr.quotientStrandIncl n y) := by
  simp [quotientExpectation]

/-- The defining trace identity characterizes the value of the conditional expectation. -/
theorem quotientExpectation_eq_iff {n : ℕ}
    {a : TemperleyLieb K δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))}
    {b : TemperleyLieb K δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))} :
    htr.quotientExpectation n a = b ↔
      ∀ y, (tr (n + 1)).quotientTrace (htr.map_mul_comm (n + 1)) (b * y) =
        δ⁻¹ * (tr (n + 2)).quotientTrace (htr.map_mul_comm (n + 2))
          (a * htr.quotientStrandIncl n y) := by
  simp [quotientExpectation, LinearMap.traceExpectation_eq_iff]

/-- The conditional expectation scales the quotient traces by `δ⁻¹`; equivalently, it preserves
the normalized traces `δ⁻ⁿ tr`. -/
@[simp]
theorem quotientTrace_quotientExpectation (n : ℕ)
    (a : TemperleyLieb K δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))) :
    (tr (n + 1)).quotientTrace (htr.map_mul_comm (n + 1)) (htr.quotientExpectation n a) =
      δ⁻¹ * (tr (n + 2)).quotientTrace (htr.map_mul_comm (n + 2)) a := by
  simp [quotientExpectation]

/-- The conditional expectation is right linear over the smaller quotient. -/
@[simp]
theorem quotientExpectation_mul_quotientStrandIncl (n : ℕ)
    (a : TemperleyLieb K δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)))
    (y : TemperleyLieb K δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientExpectation n (a * htr.quotientStrandIncl n y) =
      htr.quotientExpectation n a * y :=
  LinearMap.traceExpectation_mul_algHom _ _ _ _ a y

/-- The scaled quotient trace `δ⁻¹ tr` on `n + 2` strands is tracial. -/
private theorem smul_quotientTrace_mul_comm (n : ℕ)
    (a b : TemperleyLieb K δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))) :
    (δ⁻¹ • (tr (n + 2)).quotientTrace (htr.map_mul_comm (n + 2))) (a * b) =
      (δ⁻¹ • (tr (n + 2)).quotientTrace (htr.map_mul_comm (n + 2))) (b * a) := by
  simp [LinearMap.quotientTrace_mul_comm _ (htr.map_mul_comm (n + 2)) a b]

/-- The conditional expectation is left linear over the smaller quotient. -/
@[simp]
theorem quotientExpectation_quotientStrandIncl_mul (n : ℕ)
    (x : TemperleyLieb K δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1)))
    (a : TemperleyLieb K δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))) :
    htr.quotientExpectation n (htr.quotientStrandIncl n x * a) =
      x * htr.quotientExpectation n a :=
  LinearMap.traceExpectation_algHom_mul _
    (LinearMap.quotientTrace_mul_comm _ (htr.map_mul_comm (n + 1)))
    (htr.smul_quotientTrace_mul_comm n) x a

/-- For `δ ≠ 0`, the strand map carries the scaled trace `δ⁻¹ tr` back to `tr`. -/
private theorem comp_quotientStrandIncl (hδ : δ ≠ 0) (n : ℕ) :
    (δ⁻¹ • (tr (n + 2)).quotientTrace (htr.map_mul_comm (n + 2))) ∘ₗ
        (htr.quotientStrandIncl n).toLinearMap =
      (tr (n + 1)).quotientTrace (htr.map_mul_comm (n + 1)) := by
  ext x
  simp [inv_mul_cancel_left₀ hδ]

/-- For `δ ≠ 0`, the conditional expectation is unital. -/
@[simp]
theorem quotientExpectation_one (hδ : δ ≠ 0) (n : ℕ) : htr.quotientExpectation n 1 = 1 :=
  LinearMap.traceExpectation_one _ (htr.comp_quotientStrandIncl hδ n)

/-- For `δ ≠ 0`, the conditional expectation retracts the strand map of the quotients. -/
@[simp]
theorem quotientExpectation_quotientStrandIncl (hδ : δ ≠ 0) (n : ℕ)
    (x : TemperleyLieb K δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientExpectation n (htr.quotientStrandIncl n x) = x :=
  LinearMap.traceExpectation_algHom _ (htr.comp_quotientStrandIncl hδ n) x

/-- For `δ ≠ 0`, the conditional expectation of an element with no cap on the last strand is that
element on one strand fewer. -/
@[simp]
theorem quotientExpectation_mk_strandIncl (hδ : δ ≠ 0) (n : ℕ) (a : TemperleyLieb K δ (n + 1)) :
    htr.quotientExpectation n
        (Ideal.Quotient.mk ((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)))
          (strandIncl a)) =
      Ideal.Quotient.mk ((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) a := by
  rw [← htr.quotientStrandIncl_mk, quotientExpectation_quotientStrandIncl _ hδ]

/-- The last generator has conditional expectation `δ⁻¹ • 1`: closing its last strand leaves the
identity. Thus the Jones projection `δ⁻¹ • e` has conditional expectation `δ⁻² • 1`. -/
@[simp]
theorem quotientExpectation_mk_e_last (n : ℕ) :
    htr.quotientExpectation n
        (Ideal.Quotient.mk ((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)))
          (e δ (Fin.last n))) = δ⁻¹ • 1 := by
  refine htr.quotientExpectation_eq_iff.mpr fun y ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  simp only [quotientStrandIncl_mk, ← map_mul, LinearMap.quotientTrace_mk]
  rw [htr.map_mul_comm, htr.map_strandIncl_mul_e_last]
  simp

/-- The conditional expectation closes the last strand with the factor `δ⁻¹`: on the capped part
`ι a * e * ι b` of the tower normal form it gives `δ⁻¹ • (a * b)`. -/
theorem quotientExpectation_mk_strandIncl_mul_e_last_mul (n : ℕ)
    (a b : TemperleyLieb K δ (n + 1)) :
    htr.quotientExpectation n
        (Ideal.Quotient.mk ((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)))
          (strandIncl a * e δ (Fin.last n) * strandIncl b)) =
      δ⁻¹ • Ideal.Quotient.mk ((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) (a * b) := by
  rw [map_mul (Ideal.Quotient.mk _), map_mul (Ideal.Quotient.mk _), ← htr.quotientStrandIncl_mk,
    ← htr.quotientStrandIncl_mk]
  simp only [quotientExpectation_mul_quotientStrandIncl, quotientExpectation_quotientStrandIncl_mul,
    quotientExpectation_mk_e_last]
  simp

/-- The conditional expectation is the scaled closure of the last strand: for `δ ≠ 0`, a linear
map agreeing with it on the tower normal form, sending `ι a` to `a` and `ι a * e * ι b` to
`δ⁻¹ • (a * b)`, is the conditional expectation. -/
theorem eq_quotientExpectation (hδ : δ ≠ 0) (n : ℕ)
    (g : TemperleyLieb K δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)) →ₗ[K]
      TemperleyLieb K δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1)))
    (h₁ : ∀ a, g (Ideal.Quotient.mk _ (strandIncl a)) = Ideal.Quotient.mk _ a)
    (h₂ : ∀ a b, g (Ideal.Quotient.mk _ (strandIncl a * e δ (Fin.last n) * strandIncl b)) =
      δ⁻¹ • Ideal.Quotient.mk _ (a * b)) :
    g = htr.quotientExpectation n := by
  let q := (Ideal.Quotient.mkₐ K ((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)))).toLinearMap
  have hq : g ∘ₗ q = htr.quotientExpectation n ∘ₗ q := by
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top n) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · simp [q, h₁, htr.quotientExpectation_mk_strandIncl hδ]
    · simp only [q, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [h₂, quotientExpectation_mk_strandIncl_mul_e_last_mul]
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective K _ x
  exact LinearMap.congr_fun hq x

include htr in
/-- Pairing the sandwich `e * ι x * e` on `n + 3` strands with `ι (ι z)` closes it to
`δ * tr (x * ι z)`. -/
private theorem map_e_last_mul_strandIncl_mul_e_last_mul (n : ℕ)
    (x : TemperleyLieb K δ (n + 2)) (z : TemperleyLieb K δ (n + 1)) :
    tr (n + 3) (e δ (Fin.last (n + 1)) * strandIncl x * e δ (Fin.last (n + 1)) *
      strandIncl (strandIncl z)) = δ * tr (n + 2) (x * strandIncl z) := by
  have hz := (commute_e_last_strandIncl_strandIncl (δ := δ) z).eq
  calc tr (n + 3) (e δ (Fin.last (n + 1)) * strandIncl x * e δ (Fin.last (n + 1)) *
        strandIncl (strandIncl z))
      = tr (n + 3) (e δ (Fin.last (n + 1)) * (strandIncl x * e δ (Fin.last (n + 1)) *
          strandIncl (strandIncl z))) := by simp only [mul_assoc]
    _ = tr (n + 3) (strandIncl x * e δ (Fin.last (n + 1)) * strandIncl (strandIncl z) *
          e δ (Fin.last (n + 1))) := htr.map_mul_comm _ _ _
    _ = tr (n + 3) (strandIncl (x * strandIncl z) *
          (e δ (Fin.last (n + 1)) * e δ (Fin.last (n + 1)))) := by
        rw [mul_assoc (strandIncl x), hz, map_mul strandIncl]
        simp only [mul_assoc]
    _ = δ * tr (n + 2) (x * strandIncl z) := by
        rw [e_mul_self, mul_smul_comm, map_smul, htr.map_strandIncl_mul_e_last, smul_eq_mul]

/-- For `δ ≠ 0`, the element `y` of the sandwich identity `e * ι x * e = ι (ι y) * e` is `δ` times
the conditional expectation of `x`. -/
private theorem quotientExpectation_mk_of_sandwich (hδ : δ ≠ 0) {n : ℕ}
    {x : TemperleyLieb K δ (n + 2)} {y : TemperleyLieb K δ (n + 1)}
    (hy : e δ (Fin.last (n + 1)) * strandIncl x * e δ (Fin.last (n + 1)) =
      strandIncl (strandIncl y) * e δ (Fin.last (n + 1))) :
    htr.quotientExpectation n
        (Ideal.Quotient.mk ((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))) x) =
      δ⁻¹ • Ideal.Quotient.mk ((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) y := by
  refine htr.quotientExpectation_eq_iff.mpr fun z ↦ ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hyz : δ * tr (n + 1) (y * z) = δ * tr (n + 2) (x * strandIncl z) := by
    rw [← map_e_last_mul_strandIncl_mul_e_last_mul htr, hy, htr.map_strandIncl_mul_e_last_mul,
      ← map_mul strandIncl, htr.map_strandIncl]
  simp only [smul_mul_assoc, map_smul, smul_eq_mul, quotientStrandIncl_mk, ← map_mul,
    LinearMap.quotientTrace_mk, mul_left_cancel₀ hδ hyz]

/-- **The basic construction relation.** For `δ ≠ 0`, sandwiching `ι x` between two copies of the
last generator `e` gives `δ • ι (ι (E x)) * e`. In terms of the Jones projection `p = δ⁻¹ • e`,
this is `p * ι x * p = ι (ι (E x)) * p`. -/
theorem mk_e_last_mul_quotientStrandIncl_mul_mk_e_last (hδ : δ ≠ 0) (n : ℕ)
    (x : TemperleyLieb K δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))) :
    Ideal.Quotient.mk ((tr (n + 3)).traceRadical (htr.map_mul_comm (n + 3)))
          (e δ (Fin.last (n + 1))) * htr.quotientStrandIncl (n + 1) x *
        Ideal.Quotient.mk ((tr (n + 3)).traceRadical (htr.map_mul_comm (n + 3)))
          (e δ (Fin.last (n + 1))) =
      δ • htr.quotientStrandIncl (n + 1)
          (htr.quotientStrandIncl n (htr.quotientExpectation n x)) *
        Ideal.Quotient.mk ((tr (n + 3)).traceRadical (htr.map_mul_comm (n + 3)))
          (e δ (Fin.last (n + 1))) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, hy⟩ := exists_e_last_mul_strandIncl_mul_e_last_eq x
  rw [htr.quotientExpectation_mk_of_sandwich hδ hy]
  simp only [map_smul, smul_smul, mul_inv_cancel₀ hδ, one_smul, quotientStrandIncl_mk, ← map_mul,
    hy]

section Star

variable [StarRing K] [Fact (IsSelfAdjoint δ)]

/-- At a self-adjoint loop parameter, the conditional expectations commute with the analytic
adjoint. The star-stability instances of the two trace radicals are supplied by
`TauCeti.TemperleyLieb.IsMarkovTrace.isStar_traceRadical`. -/
theorem quotientExpectation_star (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar]
    (a : TemperleyLieb K δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))) :
    htr.quotientExpectation n (star a) = star (htr.quotientExpectation n a) := by
  refine LinearMap.traceExpectation_star _
    (LinearMap.quotientTrace_mul_comm _ (htr.map_mul_comm (n + 1)))
    (htr.smul_quotientTrace_mul_comm n) (fun x ↦ ?_) (fun x ↦ ?_) (fun x ↦ ?_) a
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [htr.map_star]
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [htr.map_star, star_inv₀, (Fact.out : IsSelfAdjoint δ).star_eq]
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp

end Star

end TauCeti.TemperleyLieb.IsMarkovTrace
