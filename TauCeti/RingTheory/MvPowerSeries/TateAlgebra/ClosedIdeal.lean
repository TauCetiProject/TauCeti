/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
public import TauCeti.Analysis.Normed.Group.Quotient

import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner

/-!
# Closed ideals and residue Gauss norms of Tate algebras

Every left ideal `I` of a restricted power-series algebra `K⟨X₁/c₁, …, Xₙ/cₙ⟩` in finitely many
variables over a complete ultrametric division ring `K` is closed for the Gauss norm, and in fact
*strictly closed*: every residue class in `K⟨X₁/c₁, …, Xₙ/cₙ⟩ ⧸ I` has a representative attaining
its quotient Gauss norm (`Ideal.exists_mk_eq_and_norm_eq_isRestricted_subring`), even when `K` is
trivially normed or not spherically complete. At unit polyradius, every quotient norm is the norm
of a scalar in `K` (`Ideal.exists_norm_eq_norm_quotient_isRestricted_subring`).

When `K` is commutative, `isClosed_ideal_isRestrictedSubring` makes Mathlib's
`Ideal.Quotient.normedCommRing` apply to every quotient of a Tate algebra. Together with
`Ideal.Quotient.normedAlgebra`, `Submodule.Quotient.completeSpace` and
`Submodule.Quotient.instIsUltrametricDist`, the residue Gauss norm on such a quotient is a complete
ultrametric algebra norm whose values at unit polyradius lie in `‖K‖`.

## Main results

* `TauCeti.MvPowerSeries.isClosed_ideal_isRestrictedSubring`: every left ideal of a finite-variable
  Tate algebra over a complete ultrametric division ring is closed.
* `Ideal.exists_norm_sub_eq_norm_mk_isRestricted_subring` and
  `Ideal.exists_mk_eq_and_norm_eq_isRestricted_subring`: every coset has a least-norm element, so
  every residue class has a representative attaining its quotient norm.
* `Ideal.exists_norm_eq_norm_quotient_isRestricted_subring`: at unit polyradius, every quotient
  Gauss norm is the norm of an element of `K`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§5.2.6–5.2.7 and §6.1.1, Proposition 2.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)]

/-- Every left ideal of a finite-variable restricted power-series algebra over a complete
ultrametric division ring is closed for the Gauss norm. -/
instance isClosed_ideal_isRestrictedSubring (I : Ideal (IsRestricted.subring (R := K) c)) :
    IsClosed (I : Set (IsRestricted.subring (R := K) c)) :=
  isClosed_ideal_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    (fun x y hx ↦ ⟨y * x⁻¹, 0, by rw [add_zero, inv_mul_cancel_right₀ hx], by simp, Or.inl rfl⟩) I

/-- **Least-norm coset adjustment for ideals of Tate algebras.** For every series `f` and left ideal
`I`, some `g ∈ I` makes `‖f - g‖` equal to the quotient Gauss norm of `f` modulo `I`. -/
theorem _root_.Ideal.exists_norm_sub_eq_norm_mk_isRestricted_subring
    (I : Ideal (IsRestricted.subring (R := K) c)) (f : IsRestricted.subring (R := K) c) :
    ∃ g ∈ I, ‖f - g‖ = ‖(Submodule.Quotient.mk f : IsRestricted.subring (R := K) c ⧸ I)‖ := by
  obtain ⟨g, hg, hle⟩ := I.exists_norm_sub_le_isRestricted_subring f
  exact ⟨g, hg, (Submodule.Quotient.norm_sub_eq_norm_mk_iff hg).mpr hle⟩

/-- **Exact quotient-norm representatives for ideals of Tate algebras** ([Bosch, Güntzer, Remmert,
*Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.2.7, Proposition 2). Every class in
`K⟨X/c⟩ ⧸ I` is represented by a restricted series of the same norm. -/
theorem _root_.Ideal.exists_mk_eq_and_norm_eq_isRestricted_subring
    (I : Ideal (IsRestricted.subring (R := K) c)) (q : IsRestricted.subring (R := K) c ⧸ I) :
    ∃ f : IsRestricted.subring (R := K) c, Submodule.Quotient.mk f = q ∧ ‖f‖ = ‖q‖ :=
  Submodule.Quotient.exists_mk_eq_and_norm_eq_iff.mpr I.exists_norm_sub_le_isRestricted_subring q

/-- **Values of the residue Gauss norm at unit polyradius** ([Bosch, Güntzer, Remmert,
*Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.1, Proposition 2). Every residue class in
`K⟨X⟩ ⧸ I` has quotient Gauss norm equal to the norm of a scalar in `K`. -/
theorem _root_.Ideal.exists_norm_eq_norm_quotient_isRestricted_subring
    (I : Ideal (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)))
    (q : IsRestricted.subring (R := K) (fun _ : σ ↦ 1) ⧸ I) :
    ∃ a : K, ‖a‖ = ‖q‖ := by
  obtain ⟨f, -, hfq⟩ := I.exists_mk_eq_and_norm_eq_isRestricted_subring q
  obtain ⟨t, ht⟩ := exists_norm_coeff_eq_norm f
  exact ⟨coeff t (f : MvPowerSeries σ K), ht.trans hfq⟩

end TauCeti.MvPowerSeries
