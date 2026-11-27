/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.DiscreteValuation
public import TauCeti.NumberTheory.LocalField.InertiaDegree
public import TauCeti.NumberTheory.NewtonPolygon.Factorization
public import TauCeti.NumberTheory.NewtonPolygon.Minpoly
public import TauCeti.NumberTheory.NewtonPolygon.Ramification

/-!
# Newton polygons over nonarchimedean local fields

Equipping a nonarchimedean local field `K` with `TauCeti.normalizedNontriviallyNormedField K` gives
a complete ultrametric nontrivially normed field with
`‖x‖ = (Nat.card 𝓀[K]) ^ (-((valuation K).realAddVal x).untop₀)` on `Kˣ`. Specialising the analytic
Newton polygon theorems to `(valuation K).realAddVal` removes all auxiliary norm hypotheses.

## Main results

* `Polynomial.forall_mem_newtonSlopes_realAddVal_eq_of_irreducible`,
  `Polynomial.existsUnique_isPureSlopeFactorization_realAddVal`, and
  `Polynomial.splits_of_nodup_newtonSlopes_realAddVal`: purity of irreducibles, unique pure slope
  factorisation, and distinct-slope splitting over a nonarchimedean local field.
* `minpoly.newtonSlopes_realAddVal_eq_replicate`: Newton slopes of a minimal polynomial in a
  compatible extension `ValuativeExtension K L` of nonarchimedean local fields.
* `Polynomial.den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq`,
  `Polynomial.den_dvd_finrank_of_forall_mem_newtonSlopes_eq`,
  `Polynomial.isTotallyRamified_of_forall_mem_newtonSlopes_eq`,
  `Polynomial.IsPureSlopeFactorization.den_dvd_ramificationIndex_of_aeval_eq_zero`, and the
  corresponding `minpoly.*` theorems: ramification and degree divisibility forced by rational
  Newton slopes over local fields.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §6.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §4 and Chapter II, §2.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField TauCeti

/-- Bundles the ultrametricity, completeness, residue-cardinality bound, and norm-valuation formula
for `normalizedNontriviallyNormedField K` needed by the analytic Newton polygon theorems. -/
private theorem localField_norm_hypotheses (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    letI := normalizedNontriviallyNormedField K
    IsUltrametricDist K ∧ CompleteSpace K ∧ 1 < (Nat.card 𝓀[K] : ℝ) ∧
      ∀ x : K, x ≠ 0 →
        ‖x‖ = (Nat.card 𝓀[K] : ℝ) ^ (-((valuation K).realAddVal x).untop₀) :=
  ⟨normalizedNormedField_isUltrametricDist K, normalizedNormedField_completeSpace K,
    Nat.one_lt_cast.mpr Finite.one_lt_card,
    fun _ hx ↦ normalizedNormedField_norm_eq_rpow_neg_realAddVal hx⟩

section SingleField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace Polynomial

/-- **Irreducible polynomials over a nonarchimedean local field are pure.** Every finite slope of
an irreducible `f : K[X]` for `(valuation K).realAddVal` equals `(v(lc f) - v(f 0)) / deg f`. -/
theorem forall_mem_newtonSlopes_realAddVal_eq_of_irreducible {f : K[X]} (hf : Irreducible f) :
    ∀ s ∈ f.newtonSlopes (valuation K).realAddVal,
      s = (((valuation K).realAddVal f.leadingCoeff).untop₀ -
        ((valuation K).realAddVal (f.coeff 0)).untop₀) / f.natDegree := by
  let _ := normalizedNontriviallyNormedField K
  obtain ⟨_, _, hb, hv⟩ := localField_norm_hypotheses K
  exact forall_mem_newtonSlopes_eq_of_irreducible hb hv hf

/-- Every `f : K[X]` with `f.coeff 0 = 1` admits a unique pure slope factorisation for
`(valuation K).realAddVal`. -/
theorem existsUnique_isPureSlopeFactorization_realAddVal {f : K[X]} (hf0 : f.coeff 0 = 1) :
    ∃! g : ℝ → K[X], f.IsPureSlopeFactorization (valuation K).realAddVal g := by
  let _ := normalizedNontriviallyNormedField K
  obtain ⟨_, _, hb, hv⟩ := localField_norm_hypotheses K
  exact existsUnique_isPureSlopeFactorization (valuation K).realAddVal hb hv hf0

/-- Any `f : K[X]` with nodup finite Newton slopes for `(valuation K).realAddVal` splits over `K`.
-/
theorem splits_of_nodup_newtonSlopes_realAddVal {f : K[X]}
    (hf : (f.newtonSlopes (valuation K).realAddVal).Nodup) : f.Splits := by
  let _ := normalizedNontriviallyNormedField K
  obtain ⟨_, _, hb, hv⟩ := localField_norm_hypotheses K
  exact splits_of_nodup_newtonSlopes (valuation K).realAddVal hb hv hf

end Polynomial

end SingleField

section Extension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

namespace Polynomial

/-- **Pure Newton slopes divide `ramificationIndex K L`.** If nonzero `f : K[X]` is pure of slope
`q` for `(valuation K).realAddVal` with a nonzero root in `L`, then `q.den ∣ ramificationIndex K L`.
-/
theorem den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ f.newtonSlopes (valuation K).realAddVal, m = q) {α : L} (hα : α ≠ 0)
    (hroot : aeval α f = 0) : q.den ∣ ramificationIndex K L := by
  rw [← ramificationIdx_valuation_eq_ramificationIndex]
  exact den_dvd_ramificationIdx_of_forall_mem_newtonSlopes_eq (valuation K) (valuation L) hf hq hα
    hroot

/-- **Pure Newton slopes divide `[L : K]`.** Under the hypotheses of
`den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq`, `q.den ∣ Module.finrank K L`. -/
theorem den_dvd_finrank_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ f.newtonSlopes (valuation K).realAddVal, m = q) {α : L} (hα : α ≠ 0)
    (hroot : aeval α f = 0) : q.den ∣ Module.finrank K L :=
  (den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq hf hq hα hroot).trans
    ⟨_, (ramificationIndex_mul_inertiaDegree K L).symm⟩

/-- **Criterion for total ramification of local fields.** If nonzero `f : K[X]` is pure of slope
`q`, has a nonzero root in `L`, and `[L : K] ≤ q.den`, then `IsTotallyRamified K L`. -/
theorem isTotallyRamified_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ f.newtonSlopes (valuation K).realAddVal, m = q) {α : L} (hα : α ≠ 0)
    (hroot : aeval α f = 0) (hdeg : Module.finrank K L ≤ q.den) :
    IsTotallyRamified K L := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  rw [isTotallyRamified_iff_ramificationIdx_eq_finrank]
  exact ramificationIdx_eq_finrank_of_forall_mem_newtonSlopes_eq (valuation K) (valuation L) hf hq
    hα hroot hdeg

/-- If `g` is a pure slope factorisation of `f : K[X]` for `(valuation K).realAddVal` and `α : L` is
a root of `g q`, then `q.den ∣ ramificationIndex K L`. -/
theorem IsPureSlopeFactorization.den_dvd_ramificationIndex_of_aeval_eq_zero {f : K[X]}
    {g : ℝ → K[X]} (hg : f.IsPureSlopeFactorization (valuation K).realAddVal g) {q : ℚ} {α : L}
    (hroot : aeval α (g q) = 0) : q.den ∣ ramificationIndex K L := by
  rw [← ramificationIdx_valuation_eq_ramificationIndex]
  exact hg.den_dvd_ramificationIdx_of_aeval_eq_zero (valuation K) (valuation L) hroot

end Polynomial

namespace minpoly

/-- In a compatible extension `L / K` of local fields, `minpoly K α` for `α ≠ 0` has the single
Newton slope `-((valuation L).extRealAddVal K α).untop₀` with multiplicity `natDegree`. -/
theorem newtonSlopes_realAddVal_eq_replicate {α : L} (hα : α ≠ 0) :
    (minpoly K α).newtonSlopes (valuation K).realAddVal =
      Multiset.replicate (minpoly K α).natDegree (-((valuation L).extRealAddVal K α).untop₀) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  let _ := normalizedNontriviallyNormedField K
  obtain ⟨_, _, hb, hv⟩ := localField_norm_hypotheses K
  exact newtonSlopes_eq_replicate hb hv
    (Valuation.extRealAddVal_algebraMap (valuation K) (valuation L))
    (Algebra.IsIntegral.isIntegral α) hα

/-- **Pure minimal-polynomial slopes divide `ramificationIndex K L`.** If `α : L` is nonzero and
`minpoly K α` is pure of slope `q`, then `q.den ∣ ramificationIndex K L`. -/
theorem den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq {α : L} (hα : α ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ (minpoly K α).newtonSlopes (valuation K).realAddVal, m = q) :
    q.den ∣ ramificationIndex K L := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  exact Polynomial.den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral α)) hq hα (minpoly.aeval K α)

/-- **Pure minimal-polynomial slopes divide `[L : K]`.** If `α : L` is nonzero and `minpoly K α` is
pure of slope `q`, then `q.den ∣ Module.finrank K L`. -/
theorem den_dvd_finrank_of_forall_mem_newtonSlopes_eq {α : L} (hα : α ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ (minpoly K α).newtonSlopes (valuation K).realAddVal, m = q) :
    q.den ∣ Module.finrank K L :=
  (den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq hα hq).trans
    ⟨_, (ramificationIndex_mul_inertiaDegree K L).symm⟩

/-- **Criterion for total ramification from a pure minimal polynomial.** If `α : L` is nonzero,
`minpoly K α` is pure of slope `q`, and `[L : K] ≤ q.den`, then `IsTotallyRamified K L`. -/
theorem isTotallyRamified_of_forall_mem_newtonSlopes_eq {α : L} (hα : α ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ (minpoly K α).newtonSlopes (valuation K).realAddVal, m = q)
    (hdeg : Module.finrank K L ≤ q.den) :
    IsTotallyRamified K L := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  exact Polynomial.isTotallyRamified_of_forall_mem_newtonSlopes_eq
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral α)) hq hα (minpoly.aeval K α) hdeg

end minpoly

end Extension

end
