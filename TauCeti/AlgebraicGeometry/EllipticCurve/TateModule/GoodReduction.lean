/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Unramified
public import TauCeti.NumberTheory.LocalField.Unramified.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Bound
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Inertia
import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.NumberTheory.LocalField.Henselian

/-!
# Good reduction from an unramified Tate module

Let `K` be a nonarchimedean local field with residue field `k`, let `W` be an elliptic curve over
`K` given by a minimal equation, and let `ℓ` be a prime different from the characteristic of `k`.
This file proves the criterion of Néron, Ogg and Shafarevich (Silverman AEC VII.7.1): `W` has good
reduction exactly when the inertia subgroup `I_K` of `Gal(K^{alg}/K)` acts trivially on the
`ℓ`-adic Tate module `T_ℓ E`. Good reduction gives an unramified Tate module by
`WeierstrassCurve.tateModuleGaloisRepresentation_eq_one_of_mem_inertiaSubgroup`; this file proves
the converse and assembles the equivalence.

The converse is a counting argument over unramified extensions. Suppose that the reduction is bad.

* Tate's algorithm stops on an integral model of `W` at a reduction symbol `s ≠ I₀`.
* Over a finite unramified extension `L/K` a uniformiser `ϖ` of `K` stays a uniformiser, so the
  algorithm stops at the same symbol `s` over `L` (`WeierstrassCurve.isTateTerminal_map_iff`), and
  the index `[E(L) : E₀(L)]` of the points with nonsingular reduction is at most the number of
  components of `s` (`WeierstrassCurve.Affine.index_nonsingularReduction_le_componentCount`), a
  bound independent of `L`.
* If `E(L)` has all `n²` points of order dividing `n`, for `n` prime to the residue characteristic,
  then `n` divides that index, because at bad reduction the points of `E₀(L)[n]` reduce injectively
  into the `n`-torsion of the nonsingular points of a singular cubic, of order dividing `n`
  (`WeierstrassCurve.Affine.Point.dvd_index_nonsingularReduction`). This is
  `WeierstrassCurve.le_componentCount_of_natCard_torsionBy_eq`.
* If `I_K` acts trivially on `T_ℓ E`, every division field `K(E[ℓ ^ k])` is unramified over `K`
  (`WeierstrassCurve.isUnramified_divisionField_pow_of_tateModuleGaloisRepresentation_eq_one`), and
  `E` has all its `ℓ ^ (2k)` points of order dividing `ℓ ^ k` over it. Taking `ℓ ^ k` larger than
  the number of components of `s` contradicts the previous step.

## Main results

* `WeierstrassCurve.le_componentCount_of_natCard_torsionBy_eq`: over a finite unramified extension
  `L/K`, if Tate's algorithm stops on the integral model of `W` at a symbol `s ≠ I₀` and `E(L)` has
  `n²` points of order dividing `n`, with `n` prime to the residue characteristic, then `n` is at
  most the number of components of `s`.
* `WeierstrassCurve.hasGoodReduction_of_tateModuleGaloisRepresentation_eq_one`: a minimal equation
  on whose `ℓ`-adic Tate module inertia acts trivially has good reduction.
* `WeierstrassCurve.hasGoodReduction_iff_tateModuleGaloisRepresentation_eq_one`: the criterion of
  Néron, Ogg and Shafarevich.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6.1 and VII.7.1.
* J.-P. Serre and J. Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968),
  492–517.
-/

public section

open ValuativeRel IsLocalRing TauCeti

namespace WeierstrassCurve

section FiniteExtension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [IsUnramified K L]
  [DecidableEq L] {W : WeierstrassCurve K} [W.IsElliptic] [IsIntegral 𝒪[K] W]

/-- **Full torsion over an unramified extension is bounded at bad reduction** (Silverman AEC
VII.7.1). Let `L/K` be an unramified extension of nonarchimedean local fields, and suppose that
Tate's algorithm, run with a uniformiser `ϖ` of `K`, stops on the integral model of `W` at a
reduction symbol `s ≠ I₀`, so that `W` has bad reduction. If `E(L)` has `n²` points of order
dividing `n`, for an integer `n` that is nonzero in the residue field of `K`, then `n` is at most
the number of components of `s`. -/
theorem le_componentCount_of_natCard_torsionBy_eq {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    {s : ReductionSymbol} (hs : (integralModel 𝒪[K] W).IsTateTerminal ϖ s) (hs₀ : s ≠ .I 0)
    {n : ℕ} (hn : (n : 𝓀[K]) ≠ 0)
    (h : Nat.card (AddSubgroup.torsionBy (W⁄L).toAffine.Point n) = n ^ 2) :
    n ≤ s.componentCount := by
  -- The valuation ring `A` of `L` is a discrete valuation ring, and the adic valuation of its
  -- maximal ideal `u` has valuation ring `B = A` again.
  set A := (valuation L).valuationSubring
  have : IsDiscreteValuationRing A := inferInstanceAs (IsDiscreteValuationRing 𝒪[L])
  set u := IsDiscreteValuationRing.maximalIdeal A
  set B := (u.valuation L).valuationSubring
  have hB : B = A := Place.valuationSubring_valuation_maximalIdeal A
  have hequiv : (u.valuation L).IsEquiv (valuation L) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).2 hB
  have : HenselianLocalRing B := hB ▸ inferInstanceAs (HenselianLocalRing 𝒪[L])
  -- The integral model of `W` over `𝒪[K]` gives one of `W⁄L` over `B`.
  have hKB (r : 𝒪[K]) : algebraMap K L r ∈ B := by
    rw [hB, ← TauCeti.coe_algebraMap_integerRing]
    exact (algebraMap 𝒪[K] 𝒪[L] r).2
  let : Algebra 𝒪[K] B :=
    (((algebraMap K L).comp (algebraMap 𝒪[K] K)).codRestrict B hKB).toAlgebra
  have hRS : (algebraMap B L).comp (algebraMap 𝒪[K] B) =
      (algebraMap K L).comp (algebraMap 𝒪[K] K) := rfl
  have := IsIntegral.baseChange hRS W
  have hmodel := integralModel_baseChange hRS W
  -- Divisibility by powers of `ϖ` is read off valuations, which `L` and `K` compare alike.
  have hf (k : ℕ) (x : 𝒪[K]) :
      algebraMap 𝒪[K] B ϖ ^ k ∣ algebraMap 𝒪[K] B x ↔ ϖ ^ k ∣ x := by
    rw [← map_pow, (Valuation.valuationSubring.integers _).dvd_iff_le,
      (Valuation.integer.integers _).dvd_iff_le, hequiv.le_iff_le]
    exact Valuation.HasExtension.val_map_le_iff (vR := valuation K) (vA := valuation L) _ _
  -- Since `L/K` is unramified, `ϖ` is still a uniformiser of `B`.
  have hϖB : maximalIdeal B = Ideal.span {algebraMap 𝒪[K] B ϖ} := by
    have : IsDiscreteValuationRing B := hB ▸ inferInstanceAs (IsDiscreteValuationRing 𝒪[L])
    refine Irreducible.maximalIdeal_eq ?_
    let e : B ≃+* 𝒪[L] := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hB)
    have he : e (algebraMap 𝒪[K] B ϖ) = algebraMap 𝒪[K] 𝒪[L] ϖ := by
      ext
      rfl
    exact (MulEquiv.irreducible_iff e.toMulEquiv).1 (he ▸ IsUnramified.irreducible_algebraMap hϖ)
  -- Tate's algorithm stops at `s` on the integral model over `B`.
  have hsB : (integralModel B (W⁄L)).IsTateTerminal (algebraMap 𝒪[K] B ϖ) s := by
    rw [hmodel]
    exact (isTateTerminal_map_iff _ hf).2 hs
  -- The reduction over `B` is singular, since `ϖ` divides the discriminant.
  have hΔ : u.valuation L (W⁄L).Δ < 1 := by
    have hint := Valuation.valuationSubring.integers (u.valuation L)
    have hdvd : algebraMap 𝒪[K] B ϖ ∣ (integralModel B (W⁄L)).Δ := by
      rw [hmodel, map_Δ]
      exact map_dvd _ ((hs.dvd_Δ_iff hϖ.prime).2 hs₀)
    have hunit : ¬ IsUnit (algebraMap 𝒪[K] B ϖ) :=
      (mem_maximalIdeal _).1 (hϖB ▸ Ideal.mem_span_singleton_self _)
    rw [← integralModel_Δ_eq B (W⁄L)]
    exact (hint.le_of_dvd hdvd).trans_lt <| lt_of_le_of_ne (hint.2 _)
      (mt hint.isUnit_iff_valuation_eq_one.2 hunit)
  -- `n` is nonzero in the residue field of `L`, so it lies outside `u`.
  have hn' : (n : A) ∉ u.asIdeal := by
    have hnL : (n : 𝓀[L]) ≠ 0 := by
      rwa [← map_natCast (algebraMap 𝓀[K] 𝓀[L]),
        map_ne_zero_iff _ (algebraMap 𝓀[K] 𝓀[L]).injective]
    rwa [← map_natCast (residue 𝒪[L]), ne_eq, residue_eq_zero_iff] at hnL
  have hfin := Affine.finiteIndex_nonsingularReduction_of_isTateTerminal (u.valuation L) hϖB hsB
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hfin.index_ne_zero)
    (Affine.Point.dvd_index_nonsingularReduction u hΔ hn' h)).trans
    (Affine.index_nonsingularReduction_le_componentCount (u.valuation L) hϖB hsB)

end FiniteExtension

section Galois

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (W : WeierstrassCurve K) [W.IsElliptic] [IsMinimal 𝒪[K] W]

open scoped Classical in
/-- **An unramified Tate module forces good reduction** (Néron, Ogg, Shafarevich; Silverman AEC
VII.7.1). Let `W` be an elliptic curve over a nonarchimedean local field `K`, given by a minimal
equation, and let `ℓ` be a prime different from the residue characteristic of `K`. If the inertia
subgroup of `Gal(K^{alg}/K)` acts trivially on the `ℓ`-adic Tate module of `W`, then `W` has good
reduction. -/
theorem hasGoodReduction_of_tateModuleGaloisRepresentation_eq_one {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : (ℓ : 𝓀[K]) ≠ 0)
    (h : ∀ σ ∈ inertiaSubgroup K, W.tateModuleGaloisRepresentation ℓ σ = 1) :
    W.HasGoodReduction 𝒪[K] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  -- Tate's algorithm stops at some symbol `s` on the integral model of `C • W`, for a change of
  -- variables `C` over `𝒪[K]`.
  have : IsMinimal 𝒪[K] ((integralModel 𝒪[K] W).baseChange K) := by
    rw [baseChange_integralModel_eq]
    infer_instance
  have hΔ₀ : (integralModel 𝒪[K] W).Δ ≠ 0 := fun h₀ ↦ W.isUnit_Δ.ne_zero <| by
    rw [← integralModel_Δ_eq 𝒪[K] W, h₀, map_zero]
  obtain ⟨C, s, hs⟩ := exists_isTateTerminal (K := K) hϖ _ hΔ₀
  rw [← integralModel_baseChange_smul] at hs
  -- Suppose that `ϖ` divides the discriminant, so that `s ≠ I₀`.
  rw [hasGoodReduction_iff_isUnit_integralModel_Δ]
  by_contra hunit
  have hΔ : ϖ ∣ (integralModel 𝒪[K] W).Δ := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact (mem_maximalIdeal _).2 hunit
  have hs₀ : s ≠ .I 0 := by
    rw [← hs.dvd_Δ_iff hϖ.prime, integralModel_baseChange_smul, variableChange_Δ]
    exact dvd_mul_of_dvd_right hΔ _
  -- Let `n = ℓ ^ k` with `k` the number of components of `s`, and `M = K(E[n])`.
  set k := s.componentCount
  set n := ℓ ^ k
  have hℓK : (ℓ : K) ≠ 0 := fun h₀ ↦ hℓ <| by
    have : (ℓ : 𝒪[K]) = 0 := Subtype.ext (by simpa using h₀)
    rw [← map_natCast (residue 𝒪[K]), this, map_zero]
  have hnK : (n : K) ≠ 0 := by simpa [n] using pow_ne_zero k hℓK
  have : NeZero n := ⟨pow_ne_zero k (Fact.out : ℓ.Prime).ne_zero⟩
  set M := W.divisionField n
  let := finiteIntermediateFieldValuativeRel K (SeparableClosure K) M
  let := finiteIntermediateFieldTopology K (SeparableClosure K) M
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) M
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) M
  -- `M/K` is unramified, and `E(M)` has all `n²` points of order dividing `n`, as does
  -- `(C • W)(M)`.
  have : IsUnramified K M :=
    W.isUnramified_divisionField_pow_of_tateModuleGaloisRepresentation_eq_one hℓK h k
  have hcard : Nat.card (AddSubgroup.torsionBy ((C.baseChange K • W)⁄M).toAffine.Point n) =
      n ^ 2 := by
    rw [← natCard_torsionBy_of_divisionField_le hnK (le_refl M), baseChange,
      ← map_variableChange]
    exact Nat.card_congr
      (AddEquiv.torsionByCongr (Affine.Point.addEquivVariableChange _ _) n).toEquiv
  -- So `ℓ ^ k ≤ k`, which is absurd.
  have hn : (n : 𝓀[K]) ≠ 0 := by simpa [n] using pow_ne_zero k hℓ
  exact (Nat.lt_pow_self (Fact.out : ℓ.Prime).one_lt).not_ge
    (le_componentCount_of_natCard_torsionBy_eq (L := M) hϖ hs hs₀ hn hcard)

open scoped Classical in
/-- **The criterion of Néron, Ogg and Shafarevich** (Silverman AEC VII.7.1). Let `W` be an elliptic
curve over a nonarchimedean local field `K`, given by a minimal equation, and let `ℓ` be a prime
different from the residue characteristic of `K`. Then `W` has good reduction exactly when the
inertia subgroup of `Gal(K^{alg}/K)` acts trivially on the `ℓ`-adic Tate module of `W`. -/
theorem hasGoodReduction_iff_tateModuleGaloisRepresentation_eq_one {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : (ℓ : 𝓀[K]) ≠ 0) :
    W.HasGoodReduction 𝒪[K] ↔
      ∀ σ ∈ inertiaSubgroup K, W.tateModuleGaloisRepresentation ℓ σ = 1 := by
  refine ⟨fun hW σ hσ ↦ ?_, W.hasGoodReduction_of_tateModuleGaloisRepresentation_eq_one hℓ⟩
  have : (integralModel 𝒪[K] W).IsElliptic :=
    ⟨(hasGoodReduction_iff_isUnit_integralModel_Δ 𝒪[K] W).1 hW⟩
  exact W.tateModuleGaloisRepresentation_eq_one_of_mem_inertiaSubgroup hℓ hσ

end Galois

end WeierstrassCurve

end
