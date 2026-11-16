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

Equipping a nonarchimedean local field `K` with `TauCeti.normalizedNontriviallyNormedField K` makes
`K` a complete ultrametric nontrivially normed field whose norm satisfies
`‖x‖ = (Nat.card 𝓀[K]) ^ (-((valuation K).realAddVal x))` on `Kˣ`. Specialising the analytic Newton
polygon theorems to `(ValuativeRel.valuation K).realAddVal` eliminates all auxiliary norm and base
hypotheses:

* Every irreducible polynomial over `K` has a pure Newton polygon, every constant-one polynomial
  over `K` admits a unique pure slope factorisation over `K`, and every polynomial over `K` with
  nodup finite Newton slopes splits into linear factors over `K`.
* For a compatible extension `L / K` of nonarchimedean local fields (`ValuativeExtension K L`), the
  minimal polynomial over `K` of any nonzero `α : L` has Newton slope
  `-(valuation L).extRealAddVal K α` with multiplicity `(minpoly K α).natDegree`.
* If a nonzero `f : K[X]` is pure of rational slope `q` for `(valuation K).realAddVal` and has a
  nonzero root in `L` (in particular, if `α ∈ L` is a root of the slope-`q` factor in a pure slope
  factorisation over `K`), then `q.den ∣ ramificationIndex K L` and `q.den ∣ Module.finrank K L`,
  and `[L : K] ≤ q.den` implies `IsTotallyRamified K L`.

## Main results

* `Polynomial.forall_mem_newtonSlopes_realAddVal_eq_of_irreducible`: irreducible polynomials over a
  nonarchimedean local field have pure Newton polygons.
* `Polynomial.existsUnique_isPureSlopeFactorization_realAddVal` and
  `Polynomial.splits_of_nodup_newtonSlopes_realAddVal`: unique pure slope factorisation and
  distinct-slope splitting over a nonarchimedean local field.
* `minpoly.newtonSlopes_realAddVal_eq_replicate`: Newton slopes of a minimal polynomial in a
  compatible extension of local fields.
* `Polynomial.den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq`,
  `Polynomial.den_dvd_finrank_of_forall_mem_newtonSlopes_eq`,
  `Polynomial.isTotallyRamified_of_forall_mem_newtonSlopes_eq`,
  `Polynomial.IsPureSlopeFactorization.den_dvd_ramificationIndex_of_aeval_eq_zero`,
  `minpoly.den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq`,
  `minpoly.den_dvd_finrank_of_forall_mem_newtonSlopes_eq`, and
  `minpoly.isTotallyRamified_of_forall_mem_newtonSlopes_eq`: ramification and degree divisibility
  forced by rational Newton slopes over local fields.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §6.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §4 and Chapter II, §2.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField TauCeti

section SingleField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace Polynomial

/-- **Irreducible polynomials over a nonarchimedean local field are pure.** Every finite slope of an
irreducible polynomial `f : K[X]` with respect to `(valuation K).realAddVal` equals
`(((valuation K).realAddVal f.leadingCoeff).untop₀ - ((valuation K).realAddVal (f.coeff 0)).untop₀)
  / f.natDegree`. -/
theorem forall_mem_newtonSlopes_realAddVal_eq_of_irreducible {f : K[X]} (hf : Irreducible f) :
    ∀ s ∈ f.newtonSlopes (valuation K).realAddVal,
      s = (((valuation K).realAddVal f.leadingCoeff).untop₀ -
        ((valuation K).realAddVal (f.coeff 0)).untop₀) / f.natDegree := by
  let _ : NontriviallyNormedField K := normalizedNontriviallyNormedField K
  have : IsUltrametricDist K := normalizedNormedField_isUltrametricDist K
  have : CompleteSpace K := normalizedNormedField_completeSpace K
  exact forall_mem_newtonSlopes_eq_of_irreducible (b := (Nat.card 𝓀[K] : ℝ))
    (Nat.one_lt_cast.mpr Finite.one_lt_card)
    (fun _ hx ↦ normalizedNormedField_norm_eq_rpow_neg_realAddVal hx) hf

/-- Over a nonarchimedean local field `K`, every polynomial `f : K[X]` with `f.coeff 0 = 1` admits a
unique pure slope factorisation with respect to `(valuation K).realAddVal`. -/
theorem existsUnique_isPureSlopeFactorization_realAddVal {f : K[X]} (hf0 : f.coeff 0 = 1) :
    ∃! g : ℝ → K[X], f.IsPureSlopeFactorization (valuation K).realAddVal g := by
  let _ : NontriviallyNormedField K := normalizedNontriviallyNormedField K
  have : IsUltrametricDist K := normalizedNormedField_isUltrametricDist K
  have : CompleteSpace K := normalizedNormedField_completeSpace K
  exact existsUnique_isPureSlopeFactorization (valuation K).realAddVal
    (b := (Nat.card 𝓀[K] : ℝ)) (Nat.one_lt_cast.mpr Finite.one_lt_card)
    (fun _ hx ↦ normalizedNormedField_norm_eq_rpow_neg_realAddVal hx) hf0

/-- Over a nonarchimedean local field `K`, any polynomial whose finite Newton slopes for
`(valuation K).realAddVal` have multiplicity one splits into linear factors over `K`. -/
theorem splits_of_nodup_newtonSlopes_realAddVal {f : K[X]}
    (hf : (f.newtonSlopes (valuation K).realAddVal).Nodup) : f.Splits := by
  let _ : NontriviallyNormedField K := normalizedNontriviallyNormedField K
  have : IsUltrametricDist K := normalizedNormedField_isUltrametricDist K
  have : CompleteSpace K := normalizedNormedField_completeSpace K
  exact splits_of_nodup_newtonSlopes (valuation K).realAddVal
    (b := (Nat.card 𝓀[K] : ℝ)) (Nat.one_lt_cast.mpr Finite.one_lt_card)
    (fun _ hx ↦ normalizedNormedField_norm_eq_rpow_neg_realAddVal hx) hf

end Polynomial

end SingleField

section Extension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

namespace Polynomial

/-- **Pure Newton slopes divide `ramificationIndex K L`.** In a compatible extension `L / K` of
nonarchimedean local fields, if every finite slope of a nonzero `f : K[X]` with respect to
`(valuation K).realAddVal` equals `q` and `f` has a nonzero root in `L`, then
`q.den ∣ ramificationIndex K L`. -/
theorem den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ f.newtonSlopes (valuation K).realAddVal, m = q) {α : L} (hα : α ≠ 0)
    (hroot : aeval α f = 0) : q.den ∣ ramificationIndex K L := by
  rw [← ramificationIdx_valuation_eq_ramificationIndex]
  exact den_dvd_ramificationIdx_of_forall_mem_newtonSlopes_eq (valuation K) (valuation L) hf hq hα
    hroot

/-- **Pure Newton slopes divide `[L : K]`.** Under the hypotheses of
`Polynomial.den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq`, `q.den ∣ Module.finrank K L`.
-/
theorem den_dvd_finrank_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ f.newtonSlopes (valuation K).realAddVal, m = q) {α : L} (hα : α ≠ 0)
    (hroot : aeval α f = 0) : q.den ∣ Module.finrank K L :=
  (den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq hf hq hα hroot).trans
    ⟨_, (ramificationIndex_mul_inertiaDegree K L).symm⟩

/-- **Criterion for total ramification of local fields from a pure Newton polygon.** If a nonzero
`f : K[X]` is pure of rational slope `q` for `(valuation K).realAddVal`, has a nonzero root in `L`,
and satisfies `Module.finrank K L ≤ q.den`, then `IsTotallyRamified K L`. -/
theorem isTotallyRamified_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ f.newtonSlopes (valuation K).realAddVal, m = q) {α : L} (hα : α ≠ 0)
    (hroot : aeval α f = 0) (hdeg : Module.finrank K L ≤ q.den) :
    IsTotallyRamified K L := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  rw [isTotallyRamified_iff_ramificationIdx_eq_finrank]
  exact ramificationIdx_eq_finrank_of_forall_mem_newtonSlopes_eq (valuation K) (valuation L) hf hq
    hα hroot hdeg

/-- If `g` is a pure slope factorisation of `f : K[X]` for `(valuation K).realAddVal` and `α : L` is
a root of the slope-`q` factor `g q`, then `q.den ∣ ramificationIndex K L`. -/
theorem IsPureSlopeFactorization.den_dvd_ramificationIndex_of_aeval_eq_zero {f : K[X]}
    {g : ℝ → K[X]} (hg : f.IsPureSlopeFactorization (valuation K).realAddVal g) {q : ℚ} {α : L}
    (hroot : aeval α (g q) = 0) : q.den ∣ ramificationIndex K L := by
  rw [← ramificationIdx_valuation_eq_ramificationIndex]
  exact hg.den_dvd_ramificationIdx_of_aeval_eq_zero (valuation K) (valuation L) hroot

end Polynomial

namespace minpoly

/-- In a compatible extension `L / K` of nonarchimedean local fields, the minimal polynomial over
`K` of a nonzero `α : L` has the single Newton slope `-((valuation L).extRealAddVal K α).untop₀`
with multiplicity `(minpoly K α).natDegree`. -/
theorem newtonSlopes_realAddVal_eq_replicate {α : L} (hα : α ≠ 0) :
    (minpoly K α).newtonSlopes (valuation K).realAddVal =
      Multiset.replicate (minpoly K α).natDegree (-((valuation L).extRealAddVal K α).untop₀) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  let _ : NontriviallyNormedField K := normalizedNontriviallyNormedField K
  have : IsUltrametricDist K := normalizedNormedField_isUltrametricDist K
  have : CompleteSpace K := normalizedNormedField_completeSpace K
  exact newtonSlopes_eq_replicate (b := (Nat.card 𝓀[K] : ℝ))
    (Nat.one_lt_cast.mpr Finite.one_lt_card)
    (fun _ hx ↦ normalizedNormedField_norm_eq_rpow_neg_realAddVal hx)
    (Valuation.extRealAddVal_algebraMap (valuation K) (valuation L))
    (Algebra.IsIntegral.isIntegral α) hα

/-- **Pure minimal-polynomial Newton slopes divide `ramificationIndex K L`.** In a compatible
extension `L / K` of nonarchimedean local fields, if `α : L` is nonzero and every finite slope of
`minpoly K α` with respect to `(valuation K).realAddVal` equals `q`, then
`q.den ∣ ramificationIndex K L`. -/
theorem den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq {α : L} (hα : α ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ (minpoly K α).newtonSlopes (valuation K).realAddVal, m = q) :
    q.den ∣ ramificationIndex K L := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  exact Polynomial.den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral α)) hq hα (minpoly.aeval K α)

/-- **Pure minimal-polynomial Newton slopes divide `[L : K]`.** Under the hypotheses of
`minpoly.den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq`, `q.den ∣ Module.finrank K L`. -/
theorem den_dvd_finrank_of_forall_mem_newtonSlopes_eq {α : L} (hα : α ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ (minpoly K α).newtonSlopes (valuation K).realAddVal, m = q) :
    q.den ∣ Module.finrank K L :=
  (den_dvd_ramificationIndex_of_forall_mem_newtonSlopes_eq hα hq).trans
    ⟨_, (ramificationIndex_mul_inertiaDegree K L).symm⟩

/-- **Criterion for total ramification of local fields from a pure minimal polynomial.** In a
compatible extension `L / K` of nonarchimedean local fields, if `α : L` is nonzero, `minpoly K α`
is pure of rational slope `q` for `(valuation K).realAddVal`, and `Module.finrank K L ≤ q.den`,
then `IsTotallyRamified K L`. -/
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
