/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Basic
-- Proof-only: the quadratic extension `K[T] / (T² + a₁ T + n)`, its irreducibility, its power
-- basis, and its separability, read off the generator.
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.AdjoinRoot
-- Proof-only: the trace and norm of a quadratic irrationality, read off its quadratic equation.
import TauCeti.FieldTheory.Quadratic
-- Proof-only: `isMinimal_of_valuation_c₄_eq_one` and the transfer of split multiplicative
-- reduction along a change of variables between minimal models.
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
-- Proof-only: split multiplicative reduction read on the reduced model's node polynomial.
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial

/-!
# A quadratic twist splits a nonsplit multiplicative reduction

Let `R` be a discrete valuation ring with fraction field `K` and let `E` be an elliptic curve over
`K`, given by a minimal equation with multiplicative reduction. The node of the reduced curve has
two tangent directions, the roots of the node polynomial
`c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`, and the reduction is split when they are rational
over the residue field. This file proves that a separable quadratic twist makes the reduction
split, in every characteristic of `K` and of the residue field.

The twist is explicit. Since `c₄` is a unit, the node polynomial is `c₄ · (T² + a₁ T + n)` with
`n = coeff₀ / c₄` integral (`nodePolynomial_eq_C_mul`), and the twist to take is the one by
`(t, n) = (-a₁, n)`, the trace and norm of a root `θ` of `T² + a₁ T + n`. The node polynomial of
that twist is `D² c₄ · (T - (a₁² - 2n)) · (T - 2n)` with `D = a₁² - 4n`
(`nodePolynomial_quadraticTwistOf_neg_a₁`), so its roots lie in `R`. As `c₄ D = -c₆` and both `c₄`
and `c₆` are units at a multiplicative reduction, `D` is a unit: the twisted equation is integral
with unit `c₄`, hence minimal, its discriminant `D⁶ Δ` has the valuation of `Δ`, and its node
polynomial splits over the residue field (`hasSplitMultiplicativeReduction_quadraticTwistOf`).

When the reduction of `E` is nonsplit, `T² + a₁ T + n` has no root in the residue field, hence,
`R` being integrally closed, none in `K`. So `L = K[T] / (T² + a₁ T + n)` is a quadratic field
extension, separable because `D ≠ 0`. The twist `E.quadraticTwist L` agrees with the explicit twist
up to a change of variables over `K`, and split multiplicative reduction transfers between minimal
models related by a change of variables (`exists_quadraticTwist_hasSplitMultiplicativeReduction`).

Away from residue characteristic two, splitting is the condition that `-c₆` be a square in the
residue field, and the classical choice of twist is by `K(√-c₆)`. Twisting by the node quadratic
itself removes the restriction on the characteristic.

## Main results

* `WeierstrassCurve.hasSplitMultiplicativeReduction_quadraticTwistOf`: the explicit twist by
  `(-a₁, coeff₀ / c₄)` of a curve with multiplicative reduction has split multiplicative
  reduction.
* `WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction`: a curve with
  nonsplit multiplicative reduction acquires split multiplicative reduction after a separable
  quadratic twist.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5 and X.2.

## Provenance

The statement of `exists_quadraticTwist_hasSplitMultiplicativeReduction` is the headline of the
FLT project's PR #1088, "Quadratic twist to split multiplicative reduction"
(`ImperialCollegeLondon/FLT` @ `bc2fe8ff7396`, Apache-2.0, by Kevin Buzzard), from which the
minimal-model and node-polynomial results used here were ported (`MinimalModel/Basic.lean`,
`NodePolynomial.lean`). The proof in this file was written against those ported results, not
adapted from the source's proof of the headline.
-/

public section

namespace WeierstrassCurve

open Polynomial IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

universe u

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K] {E : WeierstrassCurve K}

variable (R) in
/-- The constant term `n = coeff₀ / c₄` of the monic node quadratic `T² + a₁ T + n` of a curve with
multiplicative reduction is integral: it is the image of an element `n₀` of `R` with
`c₄ n₀ = coeff₀` on the integral model, where `c₄` is a unit. The discriminant `a₁² - 4 n₀` of the
node quadratic is a unit too, since `c₄ (a₁² - 4 n₀) = -c₆`. -/
private lemma exists_algebraMap_eq_nodePolynomial_coeff_zero_div
    [hE : E.HasMultiplicativeReduction R] :
    IsUnit (E.integralModel R).c₄ ∧ ∃ n₀ : R,
      (E.integralModel R).c₄ * n₀ = (E.integralModel R).nodePolynomial.coeff 0 ∧
        IsUnit ((E.integralModel R).a₁ ^ 2 - 4 * n₀) ∧
          algebraMap R K n₀ = E.nodePolynomial.coeff 0 / E.c₄ := by
  set I := E.integralModel R
  have hu : IsUnit I.c₄ := by
    have := hE.reduction_c₄_ne_zero R
    rwa [reduction, map_c₄, IsLocalRing.residue_ne_zero_iff_isUnit] at this
  have hc₆ : IsUnit I.c₆ := by
    have := hE.reduction_c₆_ne_zero R
    rwa [reduction, map_c₆, IsLocalRing.residue_ne_zero_iff_isUnit] at this
  set n₀ := I.nodePolynomial.coeff 0 * hu.unit⁻¹
  have hn₀ : I.c₄ * n₀ = I.nodePolynomial.coeff 0 := by
    rw [mul_left_comm, IsUnit.mul_val_inv, mul_one]
  have hD : IsUnit (I.a₁ ^ 2 - 4 * n₀) := by
    have hdisc := I.discrim_nodePolynomial
    rw [← nodePolynomial_coeff_zero, ← hn₀, discrim] at hdisc
    have h : I.c₄ * (I.a₁ ^ 2 - 4 * n₀) = -I.c₆ :=
      hu.mul_left_cancel (by linear_combination hdisc)
    exact isUnit_of_mul_isUnit_right (h ▸ hc₆.neg)
  refine ⟨hu, n₀, hn₀, hD, ?_⟩
  have hc₄ : algebraMap R K (E.integralModel R).c₄ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hu.ne_zero
  rw [← integralModel_c₄_eq R E, eq_div_iff hc₄, ← map_mul, mul_assoc, IsUnit.val_inv_mul,
    mul_one]
  conv_rhs => rw [← baseChange_integralModel_eq R E]
  rw [WeierstrassCurve.baseChange, map_nodePolynomial, coeff_map]

variable (R) in
/-- **The explicit twist with split multiplicative reduction.** If `E` has multiplicative
reduction, the twist of `E` by the trace `-a₁` and norm `n = coeff₀ / c₄` of a root of the node
quadratic `T² + a₁ T + n` has split multiplicative reduction: its node polynomial has the roots
`a₁² - 2n` and `2n` (`nodePolynomial_quadraticTwistOf_neg_a₁`). No hypothesis on the
characteristic of `K` or of the residue field is needed, and none on whether the reduction of `E`
is split. -/
theorem hasSplitMultiplicativeReduction_quadraticTwistOf [hE : E.HasMultiplicativeReduction R] :
    (E.quadraticTwistOf (-E.a₁) (E.nodePolynomial.coeff 0 / E.c₄)).HasSplitMultiplicativeReduction
      R := by
  obtain ⟨hu, n₀, hn₀, hD, hn₀K⟩ := exists_algebraMap_eq_nodePolynomial_coeff_zero_div R (E := E)
  set I := E.integralModel R
  set J := I.quadraticTwistOf (-I.a₁) n₀
  -- The twisted curve is the base change of `J`, which is integral with unit `c₄`.
  have hJK : J.baseChange K = E.quadraticTwistOf (-E.a₁) (E.nodePolynomial.coeff 0 / E.c₄) := by
    rw [baseChange_quadraticTwistOf, baseChange_integralModel_eq, map_neg, integralModel_a₁_eq,
      hn₀K]
  set E' := E.quadraticTwistOf (-E.a₁) (E.nodePolynomial.coeff 0 / E.c₄)
  have : IsIntegral R E' := ⟨⟨J, hJK.symm⟩⟩
  have hint : E'.integralModel R = J :=
    map_injective (IsFractionRing.injective R K) ((baseChange_integralModel_eq R E').trans hJK.symm)
  have hDK : valuation K (maximalIdeal R) (algebraMap R K (I.a₁ ^ 2 - 4 * n₀)) = 1 :=
    (valuation_eq_one_iff_notMem _).mpr (IsLocalRing.notMem_maximalIdeal.mpr hD)
  have hc₄ : valuation K (maximalIdeal R) E'.c₄ = 1 := by
    rw [← integralModel_c₄_eq R E', hint, c₄_quadraticTwistOf, neg_sq]
    exact (valuation_eq_one_iff_notMem _).mpr
      (IsLocalRing.notMem_maximalIdeal.mpr ((hD.pow 2).mul hu))
  have : IsMinimal R E' := isMinimal_of_valuation_c₄_eq_one R E' hc₄
  have hmult : E'.HasMultiplicativeReduction R :=
    { badReduction := by
        rw [← integralModel_Δ_eq R E', hint, Δ_quadraticTwistOf, neg_sq, map_mul, map_mul,
          map_pow, map_pow, hDK, one_pow, one_mul, integralModel_Δ_eq]
        exact hE.badReduction
      multiplicativeReduction := hc₄ }
  refine (hmult.splits_nodePolynomial_reduction_iff R).mp ?_
  rw [reduction, map_nodePolynomial, hint, nodePolynomial_quadraticTwistOf_neg_a₁ I n₀ hn₀]
  exact (((Splits.X_sub_C _).C_mul _).mul (Splits.X_sub_C _)).map _

/-- **Quadratic twist to split multiplicative reduction.** Over the fraction field `K` of a
discrete valuation ring `R`, a curve with multiplicative but nonsplit reduction acquires split
multiplicative reduction after a separable quadratic twist. As `HasMultiplicativeReduction`
extends `IsMinimal`, the hypothesis is about a minimal equation; the conclusion is about Mathlib's
chosen minimal equation `.minimal R` of the twist. The field `L` is found in the universe of `K`.
-/
theorem exists_quadraticTwist_hasSplitMultiplicativeReduction [E.IsElliptic]
    [E.HasMultiplicativeReduction R] (h : ¬ E.HasSplitMultiplicativeReduction R) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra.IsQuadraticExtension K L)
      (_ : Algebra.IsSeparable K L),
      ((E.quadraticTwist L).minimal R).HasSplitMultiplicativeReduction R := by
  obtain ⟨-, n₀, hn₀, hD, hn₀K⟩ := exists_algebraMap_eq_nodePolynomial_coeff_zero_div R (E := E)
  set I := E.integralModel R
  set n := E.nodePolynomial.coeff 0 / E.c₄
  set q : K[X] := X ^ 2 + C E.a₁ * X + C n
  have hq : q.Monic := by unfold q; monicity!
  have hqdeg : q.natDegree = 2 := by unfold q; compute_degree!
  -- A root of `q` in `K` is integral over `R`, hence in `R`, and would split the reduced node
  -- polynomial.
  have hroot : ∀ x : K, ¬ q.IsRoot x := by
    intro x hx
    have hx' : x ^ 2 + E.a₁ * x + n = 0 := by simpa [q] using hx
    have hxint : _root_.IsIntegral R x := by
      refine ⟨X ^ 2 + C I.a₁ * X + C n₀, by monicity!, ?_⟩
      simp [eval₂_add, ← hx', hn₀K, I, integralModel_a₁_eq]
    obtain ⟨x₀, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxint
    have hx₀ : x₀ ^ 2 + I.a₁ * x₀ + n₀ = 0 := IsFractionRing.injective R K (by
      rw [map_zero, ← hx']; simp [I, integralModel_a₁_eq, hn₀K])
    -- So the node quadratic factors over `R` with the roots `x₀` and `-a₁ - x₀`.
    have hfac : X ^ 2 + C I.a₁ * X + C n₀ = (X - C x₀) * (X - C (-I.a₁ - x₀)) := by
      have hC := congrArg C hx₀
      simp only [map_add, map_mul, map_pow, map_zero] at hC
      simp only [map_sub, map_neg]
      linear_combination hC
    refine h ((HasMultiplicativeReduction.splits_nodePolynomial_reduction_iff R
      inferInstance).mp ?_)
    rw [reduction, map_nodePolynomial, nodePolynomial_eq_C_mul I hn₀, hfac]
    exact (((Splits.X_sub_C _).mul (Splits.X_sub_C _)).C_mul _).map _
  have hirr : Irreducible q :=
    irreducible_of_degree_le_three_of_not_isRoot (by rw [hqdeg]; decide) hroot
  have : Fact (Irreducible q) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hq.ne_zero
  have hmin : minpoly K (AdjoinRoot.root q) = q := AdjoinRoot.minpoly_powerBasis_gen_of_monic hq
  have : Algebra.IsQuadraticExtension K (AdjoinRoot q) :=
    { finrank_eq_two' := by rw [pb.finrank, AdjoinRoot.powerBasis_dim, hqdeg] }
  -- The root `θ` generates, and it is separable because `q` has unit discriminant.
  have hθ : AdjoinRoot.root q ∉ Set.range (algebraMap K (AdjoinRoot q)) := by
    rintro ⟨c, hc⟩
    refine hroot c ((map_eq_zero_iff _ (algebraMap K (AdjoinRoot q)).injective).mp ?_)
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval, hc, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hsep : IsSeparable K (AdjoinRoot.root q) := by
    have hD : E.a₁ ^ 2 - 4 * n ≠ 0 := by
      rw [← hn₀K, ← integralModel_a₁_eq R E, ← map_pow, ← map_ofNat (algebraMap R K),
        ← map_mul, ← map_sub]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hD.ne_zero
    have hdisc : IsUnit (discrim 1 E.a₁ n) := isUnit_iff_ne_zero.mpr (by rwa [discrim, mul_one])
    rw [IsSeparable, hmin]
    simpa [q] using separable_quadratic_of_isUnit_discrim hdisc
  -- `K⟮θ⟯ = ⊤`, so the whole extension is separable.
  have : Algebra.IsSeparable K (AdjoinRoot q) := by
    have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K (AdjoinRoot q)).mpr hsep
    rw [IntermediateField.adjoin_root_eq_top] at this
    exact .of_algHom K _ IntermediateField.topEquiv.symm.toAlgHom
  refine ⟨AdjoinRoot q, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  -- The twist by `L` is the explicit twist up to a change of variables over `K`.
  -- `θ² = -a₁ θ - n`, so `θ` has trace `-a₁` and norm `n`.
  have hθ2 : AdjoinRoot.root q * AdjoinRoot.root q =
      algebraMap K (AdjoinRoot q) (-E.a₁) * AdjoinRoot.root q - algebraMap K (AdjoinRoot q) n := by
    have h := AdjoinRoot.mk_self (f := q)
    rw [← AdjoinRoot.aeval_eq] at h
    simp only [q, map_add, map_mul, map_pow, aeval_X, aeval_C] at h
    rw [map_neg]
    linear_combination h
  obtain ⟨C₁, hC₁⟩ := E.exists_smul_quadraticTwist_eq hθ
  rw [TauCeti.Algebra.trace_eq_of_mul_self_eq hθ hθ2,
    TauCeti.Algebra.norm_eq_of_mul_self_eq hθ hθ2] at hC₁
  obtain ⟨C₂, hC₂⟩ := (E.quadraticTwist (AdjoinRoot q)).exists_smul_eq_minimal R
  have : (E.quadraticTwistOf (-E.a₁) n).IsElliptic := hC₁ ▸ inferInstance
  exact (hasSplitMultiplicativeReduction_quadraticTwistOf R (E := E)).of_isMinimal_smul R
    (C₂ * C₁⁻¹) (by rw [mul_smul, ← hC₁, inv_smul_smul, hC₂])

end WeierstrassCurve
