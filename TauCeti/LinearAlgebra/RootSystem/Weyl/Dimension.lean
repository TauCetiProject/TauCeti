/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Numerator
public import TauCeti.RingTheory.PowerSeries.CoeffProd
public import TauCeti.RingTheory.PowerSeries.Exp

/-!
# The Weyl dimension formula for a root pairing

The Weyl character formula `ch · Δ = N(λ)` is an identity in the group algebra `ℤ[M]` of the
weight space of a root pairing, between a formal character `ch`, the Weyl denominator
`Δ = ∏_{α>0}(1 - e^{-α})` and the Weyl numerator `N(λ) = ∑_w sgn(w) e^{w ⬝ λ}`. The **Weyl
dimension formula** extracts from it the sum of the coefficients of `ch`, the dimension of the
module whose character it is:

`dim · ∏_{α>0} ⟨ρ, α^∨⟩ = ∏_{α>0} ⟨λ + ρ, α^∨⟩`.

This file proves the extraction with no Lie algebra in sight, for any `f ∈ ℤ[M]` with
`f · Δ = N(λ)`, given an invariant form on the root pairing. The character formula for the zero
weight, `g · Δ = N(0)`, is taken as a second input rather than assumed to be the denominator
identity `Δ = N(0)`: that identity is proved here only over ordered coefficient rings
(`TauCeti.weylDenominator_eq_weylNumerator_zero`), whereas a Lie algebra over an algebraically
closed field supplies `g = ch L(0)` from the character formula itself. The conclusion is then
`(∑ f) · ∏ ⟨ρ, α^∨⟩ = (∑ g) · ∏ ⟨λ + ρ, α^∨⟩`, and `∑ g = 1` in the application.

## The argument

Apply the exponential specialization `θ_μ = AddMonoidAlgebra.expAlgHom (B μ)` along the
invariant form, `e^ν ↦ e^{⟨μ, ν⟩ X}`, which is a ring homomorphism `ℤ[M] → R⟦X⟧`.

* `θ_μ(Δ) = ∏_{α>0} (1 - e^{-⟨μ, α⟩ X})` is a product of `|Φ⁺|` series with zero
  constant coefficient and linear coefficient `⟨μ, α⟩`, so any multiple `h · θ_μ(Δ)` has coefficient
  `h(0) · ∏_{α>0} ⟨μ, α⟩` in degree `|Φ⁺|`
  (`TauCeti.coeff_card_mul_expAlgHom_weylDenominator`).
* `e^{⟨μ, ρ⟩ X} θ_μ(N(λ)) = ∑_w sgn(w) e^{⟨μ, w(λ+ρ)⟩ X}` is symmetric in `μ` and `λ + ρ`, by the
  Weyl invariance of the form and the reindexing `w ↦ w⁻¹`
  (`TauCeti.rescale_mul_expAlgHom_weylNumerator_eq`).

With `μ = ρ` the second point turns `θ_ρ(f) θ_ρ(Δ) = θ_ρ(N(λ))` into
`e^{⟨ρ, ρ⟩ X} θ_ρ(f) θ_ρ(Δ) = e^{⟨λ+ρ, ρ⟩ X} θ_{λ+ρ}(N(0)) = e^{⟨λ+ρ, ρ⟩ X} θ_{λ+ρ}(g) θ_{λ+ρ}(Δ)`,
and the first point reads off the coefficients of degree `|Φ⁺|` on both sides:
`(∑ f) ∏_{α>0} ⟨ρ, α⟩ = (∑ g) ∏_{α>0} ⟨λ+ρ, α⟩`. The normalisation
`2 ⟨x, α⟩ = ⟨x, α^∨⟩ ⟨α, α⟩` of the form against the coroots
(`RootPairing.InvariantForm.two_mul_apply_root`) converts this to the coroot form.

## Main results

* `TauCeti.sum_coeff_mul_prod_form_weylVector_root_eq`: the dimension formula in terms of the
  invariant form, `(∑ f) ∏_{α>0} ⟨ρ, α⟩ = (∑ g) ∏_{α>0} ⟨λ+ρ, α⟩`.
* `TauCeti.sum_coeff_mul_prod_coroot'_weylVector_eq`: **the Weyl dimension formula** in its
  coroot form, `(∑ f) ∏_{α>0} ⟨ρ, α^∨⟩ = (∑ g) ∏_{α>0} ⟨λ+ρ, α^∨⟩`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §24.3, where
  the dimension formula is obtained from the character formula by the homomorphism
  `e^ν ↦ e^{⟨ν, ρ⟩ X}` and the symmetry of `∑_w sgn(w) e^{⟨μ, w ν⟩ X}` in `μ` and `ν`.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §24.2.
-/

public section

namespace TauCeti

open AddMonoidAlgebra PowerSeries

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base) [Algebra ℚ R]

/-! ### The exponential specialization of the Weyl denominator -/

section Denominator

/-- **The exponential specialization of the Weyl denominator** along an additive map `φ` is
`∏_{α>0} (1 - e^{-φ(α) X})`. -/
theorem expAlgHom_weylDenominator (φ : M →+ R) :
    expAlgHom (k := ℤ) φ (weylDenominator P b)
      = ∏ i ∈ posRootsFinset P b, (1 - rescale (-φ (P.root i)) (exp R)) := by
  rw [weylDenominator_def, map_prod]
  simp only [map_sub, map_one, expAlgHom_single, map_neg, one_mul]

/-- **The lowest coefficient of a multiple of the specialized Weyl denominator.** Each factor
`1 - e^{-φ(α) X}` has zero constant coefficient and linear coefficient `φ(α)`, so `h · θ_φ(Δ)` has
coefficient `h(0) ∏_{α>0} φ(α)` in degree `|Φ⁺|`. -/
theorem coeff_card_mul_expAlgHom_weylDenominator (φ : M →+ R) (h : R⟦X⟧) :
    PowerSeries.coeff (posRootsFinset P b).card (h * expAlgHom (k := ℤ) φ (weylDenominator P b))
      = constantCoeff h * ∏ i ∈ posRootsFinset P b, φ (P.root i) := by
  rw [expAlgHom_weylDenominator, coeff_card_mul_prod_of_constantCoeff_eq_zero _ (by simp)]
  simp

end Denominator

/-! ### The exponential specialization of the Weyl numerator -/

section Numerator

variable [IsDomain R] [Invertible (2 : R)] [P.IsCrystallographic] [P.IsReduced]
  [Fintype P.weylGroup]

/-- **The exponential specialization of the Weyl numerator**, after multiplication by
`e^{φ(ρ) X}`, is the alternating sum `∑_w sgn(w) e^{φ(w(λ+ρ)) X}` over the *linear* orbit of
`λ + ρ`: the `ρ`-shift of the dot action is absorbed by the exponential. -/
theorem rescale_mul_expAlgHom_weylNumerator (φ : M →+ R) (lam : M) :
    rescale (φ (weylVector P b)) (exp R) * expAlgHom (k := ℤ) φ (weylNumerator P b lam)
      = ∑ w : P.weylGroup,
          ((weylSign P b w : ℤ) : R⟦X⟧) * rescale (φ (w • (lam + weylVector P b))) (exp R) := by
  rw [weylNumerator_def, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [expAlgHom_single, eq_intCast, mul_left_comm, exp_mul_exp_eq_exp_add, ← map_add,
    dotAction_def, add_sub_cancel]

omit [Invertible (2 : R)] in
/-- **The symmetry of the alternating exponential sum.** For an invariant form `B`, the sum
`∑_w sgn(w) e^{⟨μ, w ν⟩ X}` is symmetric in `μ` and `ν`: Weyl invariance moves `w` across the
form, where it becomes `w⁻¹`, and inversion permutes the Weyl group without changing signs. -/
theorem sum_weylSign_mul_rescale_form_smul_comm (B : P.InvariantForm) (mu nu : M) :
    ∑ w : P.weylGroup, ((weylSign P b w : ℤ) : R⟦X⟧) * rescale (B.form mu (w • nu)) (exp R)
      = ∑ w : P.weylGroup,
          ((weylSign P b w : ℤ) : R⟦X⟧) * rescale (B.form nu (w • mu)) (exp R) := by
  refine Fintype.sum_equiv (Equiv.inv P.weylGroup) _ _ fun w ↦ ?_
  have hsymm : B.form (w • nu) mu = B.form mu (w • nu) := B.symm.eq _ _
  rw [Equiv.inv_apply, map_inv, Int.units_inv_eq_self,
    ← RootPairing.InvariantForm.apply_weylGroup_smul P (B := B) w nu (w⁻¹ • mu), smul_inv_smul,
    hsymm]

/-- **The exponential specialization of the Weyl numerator is symmetric in `μ` and `λ + ρ`**:
`e^{⟨μ, ρ⟩ X} θ_μ(N(λ)) = e^{⟨λ+ρ, ρ⟩ X} θ_{λ+ρ}(N(μ - ρ))`, both sides being the alternating sum
`∑_w sgn(w) e^{⟨μ, w(λ+ρ)⟩ X}`. -/
theorem rescale_mul_expAlgHom_weylNumerator_eq (B : P.InvariantForm) (mu lam : M) :
    rescale (B.form mu (weylVector P b)) (exp R) *
        expAlgHom (k := ℤ) (B.form mu).toAddMonoidHom (weylNumerator P b lam)
      = rescale (B.form (lam + weylVector P b) (weylVector P b)) (exp R) *
          expAlgHom (k := ℤ) (B.form (lam + weylVector P b)).toAddMonoidHom
            (weylNumerator P b (mu - weylVector P b)) := by
  have h₁ := rescale_mul_expAlgHom_weylNumerator P b (B.form mu).toAddMonoidHom lam
  have h₂ := rescale_mul_expAlgHom_weylNumerator P b
    (B.form (lam + weylVector P b)).toAddMonoidHom (mu - weylVector P b)
  simp only [LinearMap.toAddMonoidHom_coe, sub_add_cancel] at h₁ h₂
  rw [h₁, h₂]
  exact sum_weylSign_mul_rescale_form_smul_comm P b B mu (lam + weylVector P b)

end Numerator

/-! ### The dimension formula -/

section Dimension

variable [IsDomain R] [Invertible (2 : R)] [P.IsCrystallographic] [P.IsReduced]
  [Fintype P.weylGroup]

/-- **The Weyl dimension formula, in terms of an invariant form.** If `f · Δ = N(λ)` and
`g · Δ = N(0)` in `ℤ[M]`, then the sums of the coefficients of `f` and `g` satisfy
`(∑ f) ∏_{α>0} ⟨ρ, α⟩ = (∑ g) ∏_{α>0} ⟨λ+ρ, α⟩`. -/
theorem sum_coeff_mul_prod_form_weylVector_root_eq (B : P.InvariantForm)
    {f g : AddMonoidAlgebra ℤ M} {lam : M} (hf : f * weylDenominator P b = weylNumerator P b lam)
    (hg : g * weylDenominator P b = weylNumerator P b 0) :
    ((f.coeff.sum fun _ n ↦ n : ℤ) : R) *
        ∏ i ∈ posRootsFinset P b, B.form (weylVector P b) (P.root i)
      = ((g.coeff.sum fun _ n ↦ n : ℤ) : R) *
          ∏ i ∈ posRootsFinset P b, B.form (lam + weylVector P b) (P.root i) := by
  set ρ := weylVector P b
  -- Specialize the two character identities and compare them through the symmetry lemma.
  have key : rescale (B.form ρ ρ) (exp R) * expAlgHom (k := ℤ) (B.form ρ).toAddMonoidHom f *
        expAlgHom (k := ℤ) (B.form ρ).toAddMonoidHom (weylDenominator P b)
      = rescale (B.form (lam + ρ) ρ) (exp R) *
          expAlgHom (k := ℤ) (B.form (lam + ρ)).toAddMonoidHom g *
            expAlgHom (k := ℤ) (B.form (lam + ρ)).toAddMonoidHom (weylDenominator P b) := by
    rw [mul_assoc, ← map_mul, hf, rescale_mul_expAlgHom_weylNumerator_eq P b B ρ lam, sub_self,
      ← hg, map_mul, mul_assoc]
  have hcoeff := congrArg (PowerSeries.coeff (posRootsFinset P b).card) key
  rw [coeff_card_mul_expAlgHom_weylDenominator, coeff_card_mul_expAlgHom_weylDenominator,
    map_mul, map_mul, constantCoeff_rescale, constantCoeff_exp, constantCoeff_expAlgHom,
    constantCoeff_rescale, constantCoeff_exp, constantCoeff_expAlgHom, one_mul, one_mul] at hcoeff
  simpa only [LinearMap.toAddMonoidHom_coe, eq_intCast] using hcoeff

/-- **The Weyl dimension formula.** If `f · Δ = N(λ)` and `g · Δ = N(0)` in `ℤ[M]`, then the
sums of the coefficients of `f` and `g` satisfy

`(∑ f) ∏_{α>0} ⟨ρ, α^∨⟩ = (∑ g) ∏_{α>0} ⟨λ+ρ, α^∨⟩`.

For the formal character `f = ch L(λ)` of an irreducible module and `g = ch L(0) = 1` this is
`dim L(λ) ∏_{α>0} ⟨ρ, α^∨⟩ = ∏_{α>0} ⟨λ+ρ, α^∨⟩`, the division-free form of
`dim L(λ) = ∏_{α>0} ⟨λ+ρ, α^∨⟩ / ⟨ρ, α^∨⟩`. An invariant form on the root pairing is needed for
the proof, though it does not appear in the statement. -/
theorem sum_coeff_mul_prod_coroot'_weylVector_eq (B : P.InvariantForm)
    {f g : AddMonoidAlgebra ℤ M} {lam : M} (hf : f * weylDenominator P b = weylNumerator P b lam)
    (hg : g * weylDenominator P b = weylNumerator P b 0) :
    ((f.coeff.sum fun _ n ↦ n : ℤ) : R) * ∏ i ∈ posRootsFinset P b, P.coroot' i (weylVector P b)
      = ((g.coeff.sum fun _ n ↦ n : ℤ) : R) *
          ∏ i ∈ posRootsFinset P b, P.coroot' i (lam + weylVector P b) := by
  have h := sum_coeff_mul_prod_form_weylVector_root_eq P b B hf hg
  -- Clear the root lengths: `2 ⟨x, α⟩ = ⟨x, α^∨⟩ ⟨α, α⟩`, and the lengths are nonzero.
  have hlen : ∏ i ∈ posRootsFinset P b, B.form (P.root i) (P.root i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ B.ne_zero i
  have h2 : ∀ x : M, (2 : R) ^ (posRootsFinset P b).card *
      ∏ i ∈ posRootsFinset P b, B.form x (P.root i)
        = (∏ i ∈ posRootsFinset P b, P.coroot' i x) *
          ∏ i ∈ posRootsFinset P b, B.form (P.root i) (P.root i) := fun x ↦ by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ B.two_mul_apply_root x i
  refine mul_right_cancel₀ hlen (mul_left_cancel₀ (pow_ne_zero (posRootsFinset P b).card
    (two_ne_zero (α := R))) ?_)
  linear_combination ((2 : R) ^ (posRootsFinset P b).card) ^ 2 * h -
    (2 : R) ^ (posRootsFinset P b).card * ((f.coeff.sum fun _ n ↦ n : ℤ) : R) *
      h2 (weylVector P b) +
    (2 : R) ^ (posRootsFinset P b).card * ((g.coeff.sum fun _ n ↦ n : ℤ) : R) *
      h2 (lam + weylVector P b)

end Dimension

end TauCeti
