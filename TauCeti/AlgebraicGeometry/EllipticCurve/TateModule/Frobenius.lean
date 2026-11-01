/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
-- Proof-only: a Frobenius element satisfies `X² - a_q X + q` on prime-to-`u` torsion.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Frobenius.Reduction
-- Proof-only: the valuation of a maximal ideal recovers its valuation ring.
import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring
-- Proof-only: local-field structures on finite subextensions, and descent of points to them.
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Inertia

/-!
# Frobenius on torsion prime to `p` at good reduction

Let `K` be a nonarchimedean local field whose residue field `k` has `q` elements, and let `W` be
an elliptic curve over `K` given by a minimal equation with good reduction. Its reduction is an
elliptic curve over `k` with Frobenius trace `a_q = q + 1 - #W_k(k)`. This file proves that an
arithmetic Frobenius element satisfies `X² - a_q X + q` on the torsion of `W` of order prime to
`p = char k` (Silverman AEC V.2.3.1 and VII.7.1):

`σ (σ P) = a_q • σ P - q • P`.

The general statement (`WeierstrassCurve.Affine.Point.map_map_eq_of_nsmul_eq_zero`, proved
alongside the reduction of Frobenius elements) is over the fraction field `L` of a Dedekind
domain, at a height-one prime `u` of good reduction, for an endomorphism `τ` of `L` acting on the
residues at `u` as the `q`-power map. Reduction carries `τ` to the `q`-power map on the points of
the reduced curve (`WeierstrassCurve.Affine.Point.cast_reductionHom_map_eq_map_frobeniusAlgHom`),
which satisfies `Fr² - a_q Fr + q = 0` there
(`TauCeti.Isogeny.map_frobeniusAlgHom_map_frobeniusAlgHom`). So `τ (τ P) - a_q • τ P + q • P`
reduces to the point at infinity; it is killed by the order of `P`, which is prime to `u`, and
reduction is injective on such torsion
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
(`TauCeti.Isogeny.frobeniusTrace_reduction_eq`).

## Main results

* `WeierstrassCurve.Affine.Point.map_map_eq_of_hasGoodReduction`: over a finite extension `L/K`,
  an automorphism acting on the residue field of `L` as the `q`-power map satisfies
  `τ (τ P) = a_q • τ P - q • P` on the torsion of `W(L)` of order prime to `p`.
* `WeierstrassCurve.Affine.Point.map_map_eq_of_isArithFrobeniusLift`: an arithmetic Frobenius
  lift satisfies `σ (σ P) = a_q • σ P - q • P` on the torsion of `W(K^{alg})` of order prime to
  `p`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.2.3.1, VII.3.1 and VII.7.
-/

public section

open ValuativeRel IsLocalRing TauCeti

namespace WeierstrassCurve

section FiniteExtension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [DecidableEq L] {W : WeierstrassCurve K} [IsMinimal 𝒪[K] W]

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
  -- The proof reduces to `Affine.Point.map_map_eq_of_nsmul_eq_zero` for the adic valuation of the
  -- maximal ideal `u` of the discrete valuation ring `A = 𝒪[L]`, whose valuation ring `B` is `A`
  -- again, as in `Affine.Point.map_eq_self_of_mem_lowerRamificationGroup_zero`. It supplies, in
  -- turn: good reduction over `B`, the residue field of `K` inside that of `B`, the reduction over
  -- `B` as a base change of the reduction over `𝒪[K]`, the action of `τ` on the residues of `B`,
  -- and `n ∉ u`.
  set A := (valuation L).valuationSubring
  have : IsDiscreteValuationRing A := inferInstanceAs (IsDiscreteValuationRing 𝒪[L])
  set u := IsDiscreteValuationRing.maximalIdeal A
  set B := (u.valuation L).valuationSubring
  have hB : B = A := Place.valuationSubring_valuation_maximalIdeal A
  have hequiv : (u.valuation L).IsEquiv (valuation L) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).2 hB
  -- the integral model of `W` over `𝒪[K]` maps into `B`
  have hKB (r : 𝒪[K]) : algebraMap K L r ∈ B := by
    rw [hB, ← TauCeti.coe_algebraMap_integerRing]
    exact (algebraMap 𝒪[K] 𝒪[L] r).2
  let : Algebra 𝒪[K] B :=
    (((algebraMap K L).comp (algebraMap 𝒪[K] K)).codRestrict B hKB).toAlgebra
  have hRS : (algebraMap B L).comp (algebraMap 𝒪[K] B) =
      (algebraMap K L).comp (algebraMap 𝒪[K] K) := rfl
  have := IsIntegral.baseChange hRS W
  have : (integralModel 𝒪[K] W).IsElliptic :=
    ⟨(hasGoodReduction_iff_isUnit_integralModel_Δ 𝒪[K] W).mp h⟩
  have : (integralModel B (W⁄L)).IsElliptic := by
    rw [integralModel_baseChange hRS W]
    infer_instance
  -- `𝒪[K] → B` is local, so the residue field of `K` maps to that of `B`
  have : IsLocalHom (algebraMap 𝒪[K] B) := ⟨fun r hr ↦ by
    by_contra hr'
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hr'
    rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one] at hr
    have h₁ : valuation L (algebraMap K L r) < 1 :=
      (Valuation.HasExtension.val_map_lt_one_iff (vR := valuation K) (vA := valuation L) _).mpr hr'
    exact (hequiv.lt_one_iff_lt_one.mpr h₁).ne hr⟩
  -- the reduction of `W` over `B` is the reduction over `𝒪[K]`, base changed to the residue field
  have hC : (integralModel B (W⁄L)).map (residue B) =
      (W.reduction 𝒪[K]).baseChange (ResidueField B) := by
    rw [integralModel_baseChange hRS W, WeierstrassCurve.reduction, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    exact congrArg _ (RingHom.ext fun x ↦ (ResidueField.algebraMap_residue x).symm)
  -- `τ` acts on the residues of `B` as the `q`-power map
  have hτ' (x : L) (hx : u.valuation L x ≤ 1) :
      u.valuation L (τ.toAlgHom x - x ^ Fintype.card 𝓀[K]) < 1 := by
    have hxA : x ∈ A := hB ▸ (Valuation.mem_valuationSubring_iff _ _).mpr hx
    have h₁ := hτ (residue 𝒪[L] ⟨x, hxA⟩)
    rw [← ResidueField.residue_smul, ← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      Nat.card_eq_fintype_card] at h₁
    have h₂ := (Valuation.mem_maximalIdeal_iff (v := valuation L)).mp h₁
    rw [hequiv.lt_one_iff_lt_one]
    simpa [AlgEquiv.coe_smul_integerRing] using h₂
  -- `n` is a unit of `𝒪[K]`, hence of `A`.
  have hn' : (n : A) ∉ u.asIdeal := fun h ↦
    ((Valuation.mem_maximalIdeal_iff (v := valuation L)).mp h).ne
      (by simpa using valuation_natCast_eq_one_of_residueField_natCast_ne_zero (L := L) hn)
  exact Affine.Point.map_map_eq_of_nsmul_eq_zero u hC hτ' hn' hP

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
