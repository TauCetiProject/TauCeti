/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Henselian
public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Basic
-- Proof-only: the quadratic extension `K[T] / (T² + a₁ T + n)`, its irreducibility, its power
-- basis, and its separability, read off the generator.
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.AdjoinRoot
-- Proof-only: the multiplicative-reduction criterion on the integral model, and the transfer of
-- split multiplicative reduction along a change of variables between minimal models.
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
-- Proof-only: an integral model is determined by its base change.
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
-- Proof-only: split multiplicative reduction read on the reduced model's node polynomial.
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
-- Proof-only: Hensel lifting of a tangent slope, the classification of twists with given `j`, and
-- `j = 1728 ↔ c₆ = 0`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Henselian
import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Classification
import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Quadratic twists and split multiplicative reduction

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

Conversely, over a Henselian `R` a curve with split multiplicative reduction is determined up to
isomorphism over `K` by its `j`-invariant. By Hensel's lemma the reduction is split exactly when
the node polynomial has a root in `K`, a rational tangent slope. Two curves with the same `j` are
isomorphic over `K` or quadratic twists of each other (`QuadraticTwist/Classification.lean`), and a
nontrivial quadratic twist of a curve with a rational tangent slope has none
(`not_isRoot_nodePolynomial_quadraticTwist`). So a curve with multiplicative reduction is the twist
by its node quadratic of every curve with split multiplicative reduction and the same `j`.

## Main results

* `WeierstrassCurve.exists_algebraMap_eq_nodePolynomial_coeff_zero_div`: the constant term of
  the monic node quadratic is integral and the discriminant is a unit.
* `WeierstrassCurve.exists_quadraticExtension_root_nodeQuadratic`: at nonsplit multiplicative
  reduction the monic node quadratic generates a separable quadratic extension.
* `WeierstrassCurve.hasSplitMultiplicativeReduction_minimal_quadraticTwist_of_root_nodeQuadratic`:
  any such quadratic extension gives a twist with split multiplicative reduction.
* `WeierstrassCurve.integralModel_quadraticTwistOf_algebraMap`: the integral model of a twist by
  integral parameters is the twist of the integral model.
* `WeierstrassCurve.hasMultiplicativeReduction_quadraticTwistOf_algebraMap`: a twist by integral
  parameters of unit discriminant keeps multiplicative reduction.
* `WeierstrassCurve.hasSplitMultiplicativeReduction_quadraticTwistOf`: the explicit twist by
  `(-a₁, coeff₀ / c₄)` of a curve with multiplicative reduction has split multiplicative
  reduction.
* `WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction`: a curve with
  nonsplit multiplicative reduction acquires split multiplicative reduction after a separable
  quadratic twist.
* `HasMultiplicativeReduction.hasSplitMultiplicativeReduction_iff_exists_isRoot_nodePolynomial`:
  over a Henselian ring, the reduction is split exactly when the node polynomial has a root in `K`.
* `WeierstrassCurve.exists_smul_eq_of_j_eq_of_hasSplitMultiplicativeReduction`: over a Henselian
  ring, curves with split multiplicative reduction and the same `j` are isomorphic over `K`.
* `WeierstrassCurve.exists_smul_eq_quadraticTwistOf_of_j_eq_of_hasMultiplicativeReduction`: a curve
  with multiplicative reduction is the twist by its node quadratic of any curve with split
  multiplicative reduction and the same `j`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5 and X.2.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Theorem V.5.3,
  whose proof of uniqueness for split curves with given `j` this file follows in spirit; the
  argument here replaces the square-class test on `-c₆` by rational tangent slopes, so that it
  holds in residue characteristic `2`.

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

variable (R E) in
/-- The constant term `n = coeff₀ / c₄` of the monic node quadratic `T² + a₁ T + n` of a curve with
multiplicative reduction is integral: it is the image of an element `n₀` of `R` with
`c₄ n₀ = coeff₀` on the integral model, where `c₄` is a unit. The discriminant `a₁² - 4 n₀` of the
node quadratic is a unit too, since `c₄ (a₁² - 4 n₀) = -c₆`. -/
theorem exists_algebraMap_eq_nodePolynomial_coeff_zero_div
    [hE : E.HasMultiplicativeReduction R] :
    ∃ n₀ : R,
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
  refine ⟨n₀, hn₀, hD, ?_⟩
  have hc₄ : algebraMap R K (E.integralModel R).c₄ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hu.ne_zero
  rw [← integralModel_c₄_eq R E, eq_div_iff hc₄, ← map_mul, mul_assoc, IsUnit.val_inv_mul,
    mul_one]
  conv_rhs => rw [← baseChange_integralModel_eq R E]
  rw [WeierstrassCurve.baseChange, map_nodePolynomial, coeff_map]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- A twist by parameters `t, n ∈ R` of a curve with integral coefficients has integral
coefficients: it is the base change of the twist of the integral model. -/
instance isIntegral_quadraticTwistOf_algebraMap [IsIntegral R E] (t n : R) :
    IsIntegral R (E.quadraticTwistOf (algebraMap R K t) (algebraMap R K n)) :=
  ⟨⟨(E.integralModel R).quadraticTwistOf t n,
    by rw [baseChange_quadraticTwistOf, baseChange_integralModel_eq]⟩⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
variable (R) in
/-- The integral model of a twist by parameters `t, n ∈ R` is the twist of the integral model. -/
theorem integralModel_quadraticTwistOf_algebraMap [IsIntegral R E] (t n : R) :
    (E.quadraticTwistOf (algebraMap R K t) (algebraMap R K n)).integralModel R =
      (E.integralModel R).quadraticTwistOf t n :=
  integralModel_eq_of_baseChange_eq (by
    rw [baseChange_quadraticTwistOf, baseChange_integralModel_eq])

variable (R) in
/-- **Unit-discriminant twists keep multiplicative reduction.** If `E` has multiplicative reduction
and `t, n ∈ R` have `t² - 4n` a unit, the twist of `E` by `(t, n)` has multiplicative reduction:
it is the base change of the twist of the integral model, whose `c₄` and `Δ` are those of `E`
scaled by the unit `(t² - 4n)²` and `(t² - 4n)⁶`. -/
theorem hasMultiplicativeReduction_quadraticTwistOf_algebraMap
    [hE : E.HasMultiplicativeReduction R] {t n : R} (hD : IsUnit (t ^ 2 - 4 * n)) :
    (E.quadraticTwistOf (algebraMap R K t) (algebraMap R K n)).HasMultiplicativeReduction R := by
  have hE' := (hasMultiplicativeReduction_iff_not_isUnit_integralModel_Δ_and_isUnit_c₄ R E).mp hE
  rw [hasMultiplicativeReduction_iff_not_isUnit_integralModel_Δ_and_isUnit_c₄,
    integralModel_quadraticTwistOf_algebraMap, Δ_quadraticTwistOf, c₄_quadraticTwistOf]
  exact ⟨fun h ↦ hE'.1 (isUnit_of_mul_isUnit_right h), (hD.pow 2).mul hE'.2⟩

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
  obtain ⟨n₀, hn₀, hD, hn₀K⟩ := E.exists_algebraMap_eq_nodePolynomial_coeff_zero_div R
  set I := E.integralModel R
  -- The twisted curve is the twist by `(-I.a₁, n₀)` with parameters in `R`.
  rw [← integralModel_a₁_eq R E, ← map_neg, ← hn₀K]
  have hmult := hasMultiplicativeReduction_quadraticTwistOf_algebraMap R (E := E) (t := -I.a₁)
    (n := n₀) (by rwa [neg_sq])
  refine (hmult.splits_nodePolynomial_reduction_iff R).mp ?_
  rw [reduction, map_nodePolynomial, integralModel_quadraticTwistOf_algebraMap,
    nodePolynomial_quadraticTwistOf_neg_a₁ I n₀ hn₀]
  exact (((Splits.X_sub_C _).C_mul _).mul (Splits.X_sub_C _)).map _

variable (R) in
/-- If the elliptic curve `E` has multiplicative reduction and `L/K` is a separable quadratic
extension generated by a root `θ ∉ K` of the monic node quadratic, the chosen minimal equation
of `E.quadraticTwist L` has split multiplicative reduction. -/
theorem hasSplitMultiplicativeReduction_minimal_quadraticTwist_of_root_nodeQuadratic
    [E.IsElliptic] [E.HasMultiplicativeReduction R]
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L]
    [Algebra.IsSeparable K L] {θ : L} (hθ : θ ∉ Set.range (algebraMap K L))
    (hroot : θ ^ 2 + algebraMap K L E.a₁ * θ +
      algebraMap K L (E.nodePolynomial.coeff 0 / E.c₄) = 0) :
    ((E.quadraticTwist L).minimal R).HasSplitMultiplicativeReduction R := by
  obtain ⟨C₁, hC₁⟩ := E.exists_smul_quadraticTwist_eq hθ
  rw [_root_.Algebra.IsQuadraticExtension.trace_eq_neg_of_sq_add_mul_add_eq_zero hθ hroot,
    _root_.Algebra.IsQuadraticExtension.norm_eq_of_sq_add_mul_add_eq_zero hθ hroot] at hC₁
  obtain ⟨C₂, hC₂⟩ := (E.quadraticTwist L).exists_smul_eq_minimal R
  have : (E.quadraticTwistOf (-E.a₁) (E.nodePolynomial.coeff 0 / E.c₄)).IsElliptic :=
    hC₁ ▸ inferInstance
  exact (hasSplitMultiplicativeReduction_quadraticTwistOf R (E := E)).of_isMinimal_smul R
    (C₂ * C₁⁻¹) (by rw [mul_smul, ← hC₁, inv_smul_smul, hC₂])

/-- At nonsplit multiplicative reduction the monic node quadratic generates a separable quadratic
extension. Its root is a generator outside the ground field. -/
theorem exists_quadraticExtension_root_nodeQuadratic
    [E.HasMultiplicativeReduction R] (h : ¬ E.HasSplitMultiplicativeReduction R) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra.IsQuadraticExtension K L)
      (_ : Algebra.IsSeparable K L), ∃ θ : L,
      θ ∉ Set.range (algebraMap K L) ∧
        θ ^ 2 + algebraMap K L E.a₁ * θ +
          algebraMap K L (E.nodePolynomial.coeff 0 / E.c₄) = 0 := by
  obtain ⟨n₀, hn₀, hD, hn₀K⟩ := E.exists_algebraMap_eq_nodePolynomial_coeff_zero_div R
  set I := E.integralModel R
  set n := E.nodePolynomial.coeff 0 / E.c₄
  set q : K[X] := X ^ 2 + C E.a₁ * X + C n
  have hq : q.Monic := by unfold q; monicity!
  have hqdeg : q.natDegree = 2 := by unfold q; compute_degree!
  -- A root of `q` in `K` is integral over `R`, hence in `R`, and would split the reduced node
  -- polynomial.
  have hroot : ∀ x : K, ¬ q.IsRoot x := fun x hx ↦
    false_of_isRoot_nodeQuadratic R h hn₀ hn₀K (by simpa [q] using hx)
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
  refine ⟨AdjoinRoot q, inferInstance, inferInstance, inferInstance, inferInstance,
    AdjoinRoot.root q, hθ, ?_⟩
  have hθeq : AdjoinRoot.root q ^ 2 + algebraMap K (AdjoinRoot q) E.a₁ * AdjoinRoot.root q +
      algebraMap K (AdjoinRoot q) n = 0 := by
    have h := AdjoinRoot.mk_self (f := q)
    rw [← AdjoinRoot.aeval_eq] at h
    simpa only [q, map_add, map_mul, map_pow, aeval_X, aeval_C] using h
  exact hθeq

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
  obtain ⟨L, _, _, _, _, θ, hθ, hroot⟩ := exists_quadraticExtension_root_nodeQuadratic h
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    hasSplitMultiplicativeReduction_minimal_quadraticTwist_of_root_nodeQuadratic R hθ hroot⟩

variable (R) in
/-- **Split multiplicative reduction means a rational tangent slope.** Over the fraction field of
a Henselian discrete valuation ring, a curve with multiplicative reduction has split
multiplicative reduction exactly when its node polynomial has a root in `K`. -/
theorem HasMultiplicativeReduction.hasSplitMultiplicativeReduction_iff_exists_isRoot_nodePolynomial
    [HenselianLocalRing R] [hE : E.HasMultiplicativeReduction R] :
    E.HasSplitMultiplicativeReduction R ↔ ∃ x : K, E.nodePolynomial.IsRoot x := by
  obtain ⟨n₀, hn₀, hD, hn₀K⟩ := E.exists_algebraMap_eq_nodePolynomial_coeff_zero_div R
  have hu := ((hasMultiplicativeReduction_iff_not_isUnit_integralModel_Δ_and_isUnit_c₄ R E).mp hE).2
  set I := E.integralModel R
  have hc₄ : E.c₄ ≠ 0 := hE.c₄_ne_zero R
  -- over `K`, the node polynomial is `c₄ (T² + a₁ T + n)` with `n = coeff₀ / c₄`
  have hroot (x : K) : E.nodePolynomial.IsRoot x ↔
      x ^ 2 + E.a₁ * x + E.nodePolynomial.coeff 0 / E.c₄ = 0 := by
    rw [IsRoot, E.nodePolynomial_eq_C_mul (mul_div_cancel₀ _ hc₄)]
    simp [hc₄]
  refine ⟨fun hs ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · -- a root of the reduced node quadratic `T² + a₁ T + n₀` lifts by Hensel's lemma
    have hsplit := (hE.splits_nodePolynomial_reduction_iff R).mpr hs
    rw [reduction, map_nodePolynomial, nodePolynomial_eq_C_mul I hn₀, Polynomial.map_mul,
      Polynomial.map_C, splits_mul_iff_right
        (C_ne_zero.mpr ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu)) (Splits.C _)]
      at hsplit
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul,
      Polynomial.map_C] at hsplit
    have hdeg : (X ^ 2 + C (IsLocalRing.residue R I.a₁) * X + C (IsLocalRing.residue R n₀) :
        (IsLocalRing.ResidueField R)[X]).degree = 2 := by
      compute_degree!
    obtain ⟨t₀, ht₀⟩ := hsplit.exists_eval_eq_zero (by rw [hdeg]; decide)
    obtain ⟨t₀, rfl⟩ := IsLocalRing.residue_surjective t₀
    -- `T² + a₁ T + n₀` is the tangent quadratic of the model with `a₂ = -n₀`, whose `b₂` is the
    -- unit discriminant `a₁² - 4 n₀`
    obtain ⟨α, hα, -⟩ := exists_tangentQuadratic_eq_zero
      ({ a₁ := I.a₁, a₂ := -n₀, a₃ := 0, a₄ := 0, a₆ := 0 } : WeierstrassCurve R)
      (by convert hD using 1; simp [b₂]; ring) (t₀ := t₀)
      (by
        rw [← IsLocalRing.residue_eq_zero_iff]
        simpa using ht₀)
    refine ⟨algebraMap R K α, (hroot _).mpr ?_⟩
    rw [← hn₀K, ← integralModel_a₁_eq R E]
    simpa using congrArg (algebraMap R K) hα
  · exact by_contra fun h ↦ false_of_isRoot_nodeQuadratic R h hn₀ hn₀K ((hroot x).mp hx)

variable (R) in
/-- **Curves with split multiplicative reduction and the same `j`-invariant are isomorphic.**
Over the fraction field of a Henselian discrete valuation ring, two elliptic curves with split
multiplicative reduction and equal `j`-invariants are isomorphic over `K`. No hypothesis on the
characteristic of `K` or of the residue field is needed. The Henselian hypothesis is needed: over
`ℤ_(p)`, `p` odd, the twist by `ℚ(√d)` for a nonsquare `d ≡ 1 mod p` keeps split reduction. -/
theorem exists_smul_eq_of_j_eq_of_hasSplitMultiplicativeReduction [HenselianLocalRing R]
    {E' : WeierstrassCurve K} [E.IsElliptic] [E'.IsElliptic]
    [hE : E.HasSplitMultiplicativeReduction R] [hE' : E'.HasSplitMultiplicativeReduction R]
    (hj : E'.j = E.j) :
    ∃ C : VariableChange K, C • E' = E := by
  have hc₄ := hE.c₄_ne_zero R
  have hc₆ := hE.c₆_ne_zero R
  obtain ⟨ρ, hρ⟩ :=
    (HasMultiplicativeReduction.hasSplitMultiplicativeReduction_iff_exists_isRoot_nodePolynomial
      R).mp hE
  obtain ⟨x, hx⟩ :=
    (HasMultiplicativeReduction.hasSplitMultiplicativeReduction_iff_exists_isRoot_nodePolynomial
      R).mp hE'
  rcases E.exists_smul_eq_or_exists_smul_eq_quadraticTwist_of_j_eq (Ω := SeparableClosure K)
      (by rwa [Ne, j_eq_zero_iff]) (by rwa [Ne, j_eq_1728_iff]) E' hj with h | ⟨L, _, C, hC⟩
  · exact h
  -- `C • E'` has the rational tangent slope `(x - s) / u`, which the twist of `E` cannot have
  refine (E.not_isRoot_nodePolynomial_quadraticTwist (L := L) hc₄ hc₆ hρ ((x - C.s) / C.u)
    ?_).elim
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  rw [← hC, IsRoot, variableChange_nodePolynomial, eval_mul, eval_comp]
  simp [mul_div_cancel₀ _ hu, hx.eq_zero]

variable (R) in
/-- **A curve with multiplicative reduction is a twist of any split one with the same `j`.** Over
the fraction field of a Henselian discrete valuation ring, let `E` have multiplicative reduction
and `E'` split multiplicative reduction, with `j(E') = j(E)`. Then `E` is isomorphic over `K` to
the twist of `E'` by the trace `-a₁` and norm `n = coeff₀ / c₄` of a root of the node quadratic
`T² + a₁ T + n` of `E`. This quadratic has integral coefficients and unit discriminant, so the
twist is unramified; it has a root in `K`, and the twist is trivial, exactly when the reduction of
`E` is split, by
`HasMultiplicativeReduction.hasSplitMultiplicativeReduction_iff_exists_isRoot_nodePolynomial`. -/
theorem exists_smul_eq_quadraticTwistOf_of_j_eq_of_hasMultiplicativeReduction [HenselianLocalRing R]
    {E' : WeierstrassCurve K} [E.IsElliptic] [E'.IsElliptic] [E.HasMultiplicativeReduction R]
    [E'.HasSplitMultiplicativeReduction R] (hj : E'.j = E.j) :
    ∃ C : VariableChange K,
      C • E = E'.quadraticTwistOf (-E.a₁) (E.nodePolynomial.coeff 0 / E.c₄) := by
  set n := E.nodePolynomial.coeff 0 / E.c₄
  -- the twist `E₁` of `E` by the node quadratic has split multiplicative reduction
  have h₁ := hasSplitMultiplicativeReduction_quadraticTwistOf R (E := E)
  set E₁ := E.quadraticTwistOf (-E.a₁) n
  have hD : (-E.a₁) ^ 2 - 4 * n ≠ 0 := by
    have hc₄ := h₁.c₄_ne_zero R
    rw [c₄_quadraticTwistOf] at hc₄
    exact (pow_ne_zero_iff two_ne_zero).mp (left_ne_zero_of_mul hc₄)
  have : E₁.IsElliptic := E.isElliptic_quadraticTwistOf _ _ hD
  -- so `E₁ ≅ E'`, and twisting back gives `E ≅ E₁^θ ≅ E'^θ`
  obtain ⟨C₁, hC₁⟩ :=
    exists_smul_eq_of_j_eq_of_hasSplitMultiplicativeReduction R (E := E') (E' := E₁)
    ((E.j_quadraticTwistOf _ _ this).trans hj.symm)
  obtain ⟨C₂, hC₂⟩ := E₁.exists_smul_quadraticTwistOf_eq_quadraticTwistOf_smul (-E.a₁) n C₁
  obtain ⟨C₃, hC₃⟩ :=
    E.exists_smul_eq_quadraticTwistOf_quadraticTwistOf (-E.a₁) n (isUnit_iff_ne_zero.mpr hD)
  exact ⟨C₂ * C₃, by rw [mul_smul, hC₃, hC₂, hC₁]⟩

end WeierstrassCurve



