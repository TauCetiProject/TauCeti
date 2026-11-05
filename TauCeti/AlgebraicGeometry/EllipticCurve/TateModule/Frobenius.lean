/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel.ValuativeExtension
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
-- Proof-only: a Frobenius element satisfies `X² - a_q X + q` on prime-to-`u` torsion.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Frobenius.Reduction
-- Proof-only: a multiplicative reduction is a nodal cubic.
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
-- Proof-only: local-field structures on finite subextensions, and descent of points to them.
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Inertia

/-!
# Frobenius on torsion prime to `p` at good and multiplicative reduction

Let `K` be a nonarchimedean local field whose residue field `k` has `q` elements, and let `W` be
an elliptic curve over `K` given by a minimal equation with good reduction. Its reduction is an
elliptic curve over `k` with Frobenius trace `a_q = q + 1 - #W_k(k)`. This file proves that an
arithmetic Frobenius element satisfies `X² - a_q X + q` on the torsion of `W` of order prime to
`p = char k` (Silverman AEC V.2.3.1 and VII.7.1):

`σ (σ P) = a_q • σ P - q • P`.

At multiplicative reduction the reduction is a nodal cubic, whose Frobenius trace `a_q` is `1` at a
split and `-1` at a nonsplit node. Over a finite extension `L/K`, an automorphism acting on the
residue field of `L` as the `q`-power map then acts as multiplication by `a_q q` on the torsion of
order prime to `p` with nonsingular reduction, that is, in the subgroup `E₀(L)`:

`τ P = (a_q q) • P`.

The general statements (`WeierstrassCurve.Affine.Point.map_map_eq_of_nsmul_eq_zero` and
`WeierstrassCurve.Affine.Point.map_eq_zsmul_of_nsmul_eq_zero`, proved alongside the reduction of
Frobenius elements) are over the fraction field `L` of a Dedekind domain, at a height-one prime `u`
of good or multiplicative reduction, for an endomorphism `τ` of `L` acting on the
residues at `u` as the `q`-power map. Reduction carries `τ` to the `q`-power map `Fr` on the points
of the reduced curve
(`WeierstrassCurve.Affine.Point.cast_nonsingularReductionHom_map_eq_map_frobeniusAlgHom`, and
`WeierstrassCurve.Affine.Point.cast_reductionHom_map_eq_map_frobeniusAlgHom` at good reduction).
At good reduction the reduced curve is elliptic and `Fr` satisfies `Fr² - a_q Fr + q = 0` there
(`TauCeti.Isogeny.map_frobeniusAlgHom_map_frobeniusAlgHom`), so `τ (τ P) - a_q • τ P + q • P`
reduces to the point at infinity. At multiplicative reduction the reduced curve is a nodal cubic,
and on its nonsingular points `Fr` is multiplication by `a_q q`
(`WeierstrassCurve.Affine.Point.map_frobeniusAlgHom_eq_zsmul`), so `τ P - (a_q q) • P` reduces to
the point at infinity for `P` in `E₀`. In both cases that point is killed by the order of `P`,
which is prime to `u`, and reduction is injective on such torsion
(`WeierstrassCurve.Affine.Point.eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero`). A finite
extension `L/K` of local fields is the fraction field of the discrete valuation ring `𝒪[L]`, and
an automorphism of `L/K` acting on the residue field of `L` as `x ↦ x ^ q` is such a `τ`. Over
`K^{alg}`, a point is defined over a finite normal subextension, on which an arithmetic Frobenius
lift of `Gal(K^{alg}/K)` restricts to such an automorphism
(`TauCeti.IsArithFrobeniusLift.restrictNormal_smul_residueField_eq_pow`).

Read on the Tate module `T_ℓ E`, for `ℓ ≠ p`, this says that a Frobenius lift is a root of
`X² - a_q X + q` there. Two values of `a_q` that both satisfy this on a point of order `ℓ` are
congruent modulo `ℓ`. Since this holds for arbitrarily large primes `ℓ`, the Galois action on the
prime-to-`p` torsion determines the integer `a_q`; this is what makes `a_q` an isogeny invariant
(`TauCeti.Isogeny.frobeniusTrace_reduction_eq`). At multiplicative reduction, the relation
`τ P = (a_q q) • P` at a point `P` and at its image under an isogeny compares the signs of the two
nodes (`TauCeti.Isogeny.frobeniusTrace_reduction_eq_of_hasMultiplicativeReduction`).

## Main results

* `WeierstrassCurve.Affine.Point.map_map_eq_of_hasGoodReduction`: over a finite extension `L/K`,
  an automorphism acting on the residue field of `L` as the `q`-power map satisfies
  `τ (τ P) = a_q • τ P - q • P` on the torsion of `W(L)` of order prime to `p`.
* `WeierstrassCurve.Affine.Point.map_eq_zsmul_of_hasMultiplicativeReduction`: at multiplicative
  reduction, over a finite extension `L/K`, such an automorphism satisfies `τ P = (a_q q) • P` on
  the torsion of `E₀(L)` of order prime to `p`.
* `WeierstrassCurve.Affine.Point.map_map_eq_of_isArithFrobeniusLift`: an arithmetic Frobenius
  lift satisfies `σ (σ P) = a_q • σ P - q • P` on the torsion of `W(K^{alg})` of order prime to
  `p`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.2.3.1, VII.3.1, VII.5 and
  VII.7.
-/

public section

open ValuativeRel IsLocalRing TauCeti

namespace WeierstrassCurve

section FiniteExtension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

/-! The proofs over a finite extension `L/K` apply the statements over the fraction field of a
Dedekind domain to the discrete valuation ring `𝒪[L]`, at its maximal ideal
`TauCeti.maximalPrime L`. The valuation ring `B` of its adic valuation is `𝒪[L]` again, and
`WeierstrassCurve.integralModel_valuationSubring_maximalPrime` gives the integral model of `W` over
`B`. The private declarations below supply its reduction and the action of a Frobenius on the
residues of `B`. -/

omit [Module.Finite K L] in
/-- The reduction of the base change of `W` over the valuation ring of `L` is the reduction of `W`
over `𝒪[K]`, base changed to the residue field. -/
private theorem integralModel_map_residue_maximalPrime (W : WeierstrassCurve K)
    [IsMinimal 𝒪[K] W] :
    (integralModel ((maximalPrime L).valuation L).valuationSubring (W⁄L)).map
        (residue ((maximalPrime L).valuation L).valuationSubring) =
      (W.reduction 𝒪[K]).baseChange
        (ResidueField ((maximalPrime L).valuation L).valuationSubring) := by
  rw [integralModel_valuationSubring_maximalPrime, WeierstrassCurve.reduction,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  exact congrArg _ (RingHom.ext fun x ↦ (ResidueField.algebraMap_residue x).symm)

/-- An automorphism of `L/K` acting on the residue field of `L` as the `q`-power map acts so on
the residues of the adic valuation of the maximal ideal of `𝒪[L]`
(`AlgEquiv.valuation_apply_sub_pow_lt_one`, read through the equivalent valuation). -/
private theorem valuation_maximalPrime_sub_pow_lt_one {τ : Gal(L/K)}
    (hτ : ∀ x : 𝓀[L], τ • x = x ^ Nat.card 𝓀[K]) (x : L)
    (hx : (maximalPrime L).valuation L x ≤ 1) :
    (maximalPrime L).valuation L (τ.toAlgHom x - x ^ Nat.card 𝓀[K]) < 1 :=
  (isEquiv_valuation_maximalPrime L).lt_one_iff_lt_one.mpr <|
    τ.valuation_apply_sub_pow_lt_one hτ ((isEquiv_valuation_maximalPrime L).le_one_iff_le_one.mp hx)

variable [DecidableEq L] {W : WeierstrassCurve K} [IsMinimal 𝒪[K] W]

/-- **Frobenius on prime-to-`p` torsion at good reduction, over a finite extension.** Let `W` be a
minimal equation with good reduction over a nonarchimedean local field `K` whose residue field
has `q` elements, let `L/K` be a finite extension, and let `τ` be an automorphism of `L/K` acting
on the residue field of `L` as `x ↦ x ^ q`. If `n • P = 0` for a point `P` of `W(L)` and an `n`
nonzero in the residue field of `K`, then `τ (τ P) = a_q • τ P - q • P`, where `a_q` is the
Frobenius trace of the reduction of `W`. -/
theorem Affine.Point.map_map_eq_of_hasGoodReduction (h : W.HasGoodReduction 𝒪[K])
    {τ : Gal(L/K)} (hτ : ∀ x : 𝓀[L], τ • x = x ^ Nat.card 𝓀[K]) {n : ℕ}
    (hn : (n : 𝓀[K]) ≠ 0) {P : (W⁄L).toAffine.Point} (hP : n • P = 0) :
    Affine.Point.map τ.toAlgHom (Affine.Point.map τ.toAlgHom P) =
      (W.reduction 𝒪[K]).frobeniusTrace • Affine.Point.map τ.toAlgHom P -
        Nat.card 𝓀[K] • P := by
  classical
  let := Fintype.ofFinite 𝓀[K]
  have : (integralModel 𝒪[K] W).IsElliptic :=
    ⟨(hasGoodReduction_iff_isUnit_integralModel_Δ 𝒪[K] W).mp h⟩
  have : (integralModel ((maximalPrime L).valuation L).valuationSubring (W⁄L)).IsElliptic := by
    rw [integralModel_valuationSubring_maximalPrime]
    infer_instance
  exact Affine.Point.map_map_eq_of_nsmul_eq_zero (maximalPrime L)
    (integralModel_map_residue_maximalPrime W)
    (by simpa only [Nat.card_eq_fintype_card] using valuation_maximalPrime_sub_pow_lt_one hτ)
    (natCast_notMem_maximalPrime hn) hP

/-- **Frobenius on prime-to-`p` torsion at multiplicative reduction, over a finite extension.** Let
`W` be an elliptic curve over a nonarchimedean local field `K` whose residue field has `q`
elements, given by a minimal equation with multiplicative reduction, let `L/K` be a finite
extension, and let `τ` be an automorphism of `L/K` acting on the residue field of `L` as
`x ↦ x ^ q`. If `P` is a point of `W(L)` with nonsingular reduction and `n • P = 0` for an `n`
nonzero in the residue field of `K`, then `τ P = (a_q q) • P`, where the Frobenius trace `a_q` of
the reduction of `W` is `1` at split and `-1` at nonsplit multiplicative reduction. -/
theorem Affine.Point.map_eq_zsmul_of_hasMultiplicativeReduction [W.IsElliptic]
    (h : W.HasMultiplicativeReduction 𝒪[K]) {τ : Gal(L/K)}
    (hτ : ∀ x : 𝓀[L], τ • x = x ^ Nat.card 𝓀[K]) {n : ℕ} (hn : (n : 𝓀[K]) ≠ 0)
    {P : (W⁄L).toAffine.Point} (hP₀ : P ∈ (W⁄L).toAffine.nonsingularReduction (valuation L))
    (hP : n • P = 0) :
    Affine.Point.map τ.toAlgHom P = ((W.reduction 𝒪[K]).frobeniusTrace * Nat.card 𝓀[K]) • P := by
  classical
  let := Fintype.ofFinite 𝓀[K]
  rw [Affine.nonsingularReduction_congr _ (isEquiv_valuation_maximalPrime L).symm] at hP₀
  exact Affine.Point.map_eq_zsmul_of_nsmul_eq_zero (maximalPrime L)
    (integralModel_map_residue_maximalPrime W)
    ((reduction_Δ_eq_zero_iff 𝒪[K]).2 (h.not_hasGoodReduction 𝒪[K]))
    (h.reduction_c₄_ne_zero 𝒪[K])
    (by simpa only [Nat.card_eq_fintype_card] using valuation_maximalPrime_sub_pow_lt_one hτ)
    (natCast_notMem_maximalPrime hn) hP₀ hP

end FiniteExtension

section AlgebraicClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DecidableEq (AlgebraicClosure K)] {W : WeierstrassCurve K}
  [IsMinimal 𝒪[K] W]

/-- **Frobenius on prime-to-`p` torsion at good reduction** (Silverman AEC V.2.3.1 and VII.7.1).
Let `W` be a minimal equation with good reduction over a nonarchimedean local field `K` whose
residue field has `q` elements, and let `σ` be an arithmetic Frobenius lift in `Gal(K^{alg}/K)`.
If `n • P = 0` for a point `P` of `W(K^{alg})` and an `n` nonzero in the residue field of `K`, then
`σ (σ P) = a_q • σ P - q • P`, where `a_q` is the Frobenius trace of the reduction of `W`. -/
theorem Affine.Point.map_map_eq_of_isArithFrobeniusLift (h : W.HasGoodReduction 𝒪[K])
    {σ : Gal(AlgebraicClosure K/K)} (hσ : IsArithFrobeniusLift K σ) {n : ℕ}
    (hn : (n : 𝓀[K]) ≠ 0) {P : (W⁄(AlgebraicClosure K)).toAffine.Point} (hP : n • P = 0) :
    Affine.Point.map σ.toAlgHom (Affine.Point.map σ.toAlgHom P) =
      (W.reduction 𝒪[K]).frobeniusTrace • Affine.Point.map σ.toAlgHom P -
        Nat.card 𝓀[K] • P := by
  classical
  -- `P` is defined over a finite normal subextension `M` of `K^{alg}/K`.
  obtain ⟨M, _, _, hM⟩ := Affine.Point.exists_finiteDimensional_normal_map_val_eq P
  obtain ⟨Q, rfl⟩ := hM
  let := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M
  let := finiteIntermediateFieldTopology K (AlgebraicClosure K) M
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) M
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M
  have hQ : n • Q = 0 :=
    Affine.Point.map_injective M.val (by rw [map_nsmul, hP, _root_.map_zero])
  -- On `M`, `σ` acts through its restriction, a Frobenius on the residue field of `M`.
  have key := Affine.Point.map_map_eq_of_hasGoodReduction h
    (hσ.restrictNormal_smul_residueField_eq_pow M) hn hQ
  rw [Affine.Point.map_map_val_eq_map_val_map_restrictNormal,
    Affine.Point.map_map_val_eq_map_val_map_restrictNormal, key, map_sub, map_zsmul, map_nsmul]

end AlgebraicClosure

end WeierstrassCurve
