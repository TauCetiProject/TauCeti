/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree

/-!
# Genus-zero function fields with a divisor of degree one

Let `F / k` be an algebraic function field with exact constant field.  If `F` has genus zero
and admits a divisor of degree one, then `F` is a rational function field over `k`.  This is the
nontrivial implication of Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
Proposition 1.6.3.

The degree-one hypothesis is deliberately stated for an arbitrary divisor, not for a rational
place.  Riemann--Roch gives a nonzero section of that divisor.  Translating the section by its
principal divisor produces an effective divisor of degree one, whose support contains a rational
place.  At that place, the genus-zero prescribed-pole theorem produces a function with one simple
pole.  The product formula identifies the degree of the resulting rational subfield with one, so
Mathlib's `RatFunc.algEquivOfTranscendental` extends to the required equivalence.

The converse direction requires transporting the function-field place and divisor theory across
an algebra equivalence.  The model calculation `TauCeti.genus_ratFunc` is already available, but
that transport API is not yet part of the function-field development; this module therefore
records the mathematically substantial forward implication without weakening the roadmap's
degree-one-divisor hypothesis to the existence of a rational place.

## Main results

* `TauCeti.Divisor.exists_place_degree_eq_one_of_isEffective_of_degree_eq_one`: an effective
  degree-one divisor contains a rational place.
* `TauCeti.exists_place_degree_eq_one_of_genus_eq_zero_of_divisor_degree_eq_one`: genus zero and
  a degree-one divisor produce a rational place.
* `TauCeti.nonempty_algEquiv_ratFunc_of_genus_eq_zero_of_divisor_degree_eq_one`: genus zero and a
  degree-one divisor make the function field rational.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.6.3 and Remark 1.6.4.
-/

public section

noncomputable section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Divisor

/-- An effective divisor of degree one on an algebraic function field contains a rational place.

Indeed, any place in its support contributes at least its positive residue degree to the total
degree, so both that residue degree and its coefficient must equal one. -/
theorem exists_place_degree_eq_one_of_isEffective_of_degree_eq_one
    (hF : IsFunctionField k F) {D : Divisor k F} (hD : 0 ≤ D) (hdeg : degree D = 1) :
    ∃ P : Place k F, P ∈ D.support ∧ P.degree = 1 := by
  have hD0 : D ≠ 0 := by
    rintro rfl
    simp at hdeg
  obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.mpr hD0
  refine ⟨P, hP, ?_⟩
  have hle : (P.degree : ℤ) ≤ 1 := by
    rw [← hdeg]
    exact degree_le_degree_of_coeff_ne_zero hD (WeilDivisor.mem_support_iff.mp hP)
  have hone : 1 ≤ P.degree := P.one_le_degree_of_isFunctionField hF
  omega

end Divisor

/-- A genus-zero function field with a divisor of degree one has a rational place.

Riemann--Roch gives dimension two for the degree-one divisor.  A nonzero section translates it
to a linearly equivalent effective divisor, still of degree one, and such a divisor contains a
rational place. -/
theorem exists_place_degree_eq_one_of_genus_eq_zero_of_divisor_degree_eq_one
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 0)
    (hdegree : ∃ D : Divisor k F, Divisor.degree D = 1) :
    ∃ P : Place k F, P.degree = 1 := by
  obtain ⟨D, hD⟩ := hdegree
  have hhigh : 2 * (genus k F : ℤ) - 1 ≤ Divisor.degree D := by
    rw [hg, hD]
    norm_num
  have hdim :=
    Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree
      hF hex hhigh
  have hone : 1 ≤ Divisor.dim D := by
    rw [hD, hg] at hdim
    omega
  obtain ⟨z, hzD, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF D).mp hone)
  let E : Divisor k F := Divisor.principal hF (Units.mk0 z hz0) + D
  have hE : 0 ≤ E := by
    exact (mem_riemannRochSpace_units_iff hF).mp hzD
  have hEdeg : Divisor.degree E = 1 := by
    simp [E, hD]
  obtain ⟨P, _, hP⟩ :=
    Divisor.exists_place_degree_eq_one_of_isEffective_of_degree_eq_one hF hE hEdeg
  exact ⟨P, hP⟩

/-- **Genus zero plus a divisor of degree one implies rationality** (the nontrivial direction of
Stichtenoth, Proposition 1.6.3).

The conclusion is an equivalence of `k`-algebras `F ≃ₐ[k] RatFunc k`.  No perfectness,
separability, or rational-place hypothesis is added: exactness of the constant field is the only
extra hypothesis required by Riemann--Roch. -/
theorem nonempty_algEquiv_ratFunc_of_genus_eq_zero_of_divisor_degree_eq_one
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 0)
    (hdegree : ∃ D : Divisor k F, Divisor.degree D = 1) :
    Nonempty (F ≃ₐ[k] RatFunc k) := by
  obtain ⟨P, hP⟩ :=
    exists_place_degree_eq_one_of_genus_eq_zero_of_divisor_degree_eq_one hF hex hg hdegree
  obtain ⟨z, hpoles⟩ :=
    P.exists_poles_eq_natCast_zsmul_ofPoint hF hex (n := 1) (by simp [hg])
  have hpoles' : Divisor.poles hF z = WeilDivisor.ofPoint P := by
    simpa using hpoles
  have hz : Transcendental k (z : F) := by
    intro hzalg
    have hpoles0 : Divisor.poles hF z = 0 := by
      apply WeilDivisor.ext
      intro Q
      rw [Divisor.coeff_poles, Q.ord_eq_zero_of_isAlgebraic hzalg,
        WeilDivisor.coeff_zero]
      norm_num
    have hpoint0 : (WeilDivisor.ofPoint P : Divisor k F) = 0 := hpoles'.symm.trans hpoles0
    have := congrArg (fun D : Divisor k F ↦ D.coeff P) hpoint0
    simp at this
  let _ : FiniteDimensional k⟮(z : F)⟯ F := hF.finiteDimensional_adjoin hz
  have hfinrank : Module.finrank k⟮(z : F)⟯ F = 1 := by
    have hdeg := Divisor.degree_poles hF z hz
    rw [hpoles', Divisor.degree_ofPoint, hP] at hdeg
    exact_mod_cast hdeg.symm
  have htop : k⟮(z : F)⟯ = (⊤ : IntermediateField k F) :=
    IntermediateField.finrank_eq_one_iff_eq_top.mp hfinrank
  let e : RatFunc k ≃ₐ[k] F :=
    (RatFunc.algEquivOfTranscendental (z : F) hz).trans
      ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
  exact ⟨e.symm⟩

end TauCeti
