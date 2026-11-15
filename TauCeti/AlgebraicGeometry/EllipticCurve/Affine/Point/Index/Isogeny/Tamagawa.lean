/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Ratio
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MinimalRealPeriod
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product

import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.DedekindDomain.Factorization
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Index
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AdicCompletion
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GlobalExistence
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Isogeny

/-!
# Local Kummer ratios via Tamagawa numbers and the global period–Tamagawa formula

Let `φ : E₁ → E₂` be an isogeny of elliptic curves over the fraction field `F` of a Dedekind
domain `A`, pulling the invariant differential back as `φ^*ω₂ = c ω₁`. At a height-one prime `u`
with finite residue field `κ(u) = A ⧸ u` (assuming `2 ≠ 0` in `F` and `deg φ ≠ 0` in `A`), the
deep formal-filtration comparison
`TauCeti.Isogeny.eventually_index_range_pointMapHom_mul_index_formalPointFiltration` equates the
local Kummer ratio `[E₂(F_u) : φ E₁(F_u)] / #E₁(F_u)[φ]` on locally minimal equations with the
ratio `[E₂(F_u) : E_j(F_u)] / [E₁(F_u) : E_k(F_u)]` where `j - k = ord_u(c)`. Expanding both
formal-filtration indices via `WeierstrassCurve.index_formalPointFiltration_eq_mul_tamagawaNumber`
and cancelling the common nonsingular reduction count (`TauCeti.Isogeny.natCard_point_reduction_eq`,
at good and bad reduction alike) yields

`φ.finiteKummerRatio u = (#κ(u))^(-log v_u(c u₂ / u₁)) · c_u(E₂) / c_u(E₁)`,

where `C₁`, `C₂` carry `E₁`, `E₂` to locally minimal equations at `u` with scaling factors `u₁`,
`u₂`, and `c_u(Eᵢ)` are the local Tamagawa numbers.

Over `ℚ`, combining this finite-place formula across all primes of `ℤ` with the archimedean period
identity `TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul` cancels the global
scaling factor `|c u₂ / u₁|` by prime-ideal factorisation over `ℤ`.
Consequently, the product `φ.kummerRatioProduct` of local Kummer ratios over all places of `ℚ`
depends only on the real periods and Tamagawa products of `E₁` and `E₂`:

`(φ.kummerRatioProduct : ℝ) · Ω(E₁) · ∏_p c_p(E₁) = Ω(E₂) · ∏_p c_p(E₂)`.

In particular, `φ.kummerRatioProduct` is independent of the choice of isogeny `E₁ → E₂`, equals
`1` for every endomorphism-isogeny `E → E` over `ℚ`, and is inverted by passing to the dual
isogeny `φ.dual`.

## Main results

* `TauCeti.Isogeny.kummerRatio_variableChangeIsogeny`,
  `TauCeti.Isogeny.finiteKummerRatio_variableChangeIsogeny`,
  `TauCeti.Isogeny.realKummerRatio_variableChangeIsogeny`, and
  `TauCeti.Isogeny.kummerRatioProduct_variableChangeIsogeny`: changes of Weierstrass variables
  have local and global Kummer ratio `1`.
* `TauCeti.Isogeny.kummerRatio_eq_of_isMinimal_adicCompletionIntegers`: local Kummer ratio of an
  isogeny between minimal equations over `O_u` in terms of `#(A ⧸ u)` and local Tamagawa numbers.
* `TauCeti.Isogeny.finiteKummerRatio_eq` and
  `TauCeti.Isogeny.finiteKummerRatio_eq_tamagawaNumberAt`: the finite local Kummer ratio of an
  isogeny between arbitrary equations over `F`, expressed via any locally minimal changes of
  variables at `u`.
* `TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_realKummerRatio`: the archimedean counterpart,
  `|c u₂ / u₁| Ω(E₁) · φ.realKummerRatio = Ω(E₂)`.
* `TauCeti.Isogeny.finprod_finiteKummerRatio_eq`: the product of `φ.finiteKummerRatio v` over all
  finite primes of `ℤ` equals `|c u₂ / u₁| · tamagawaProduct E₂ / tamagawaProduct E₁`.
* `TauCeti.Isogeny.kummerRatioProduct_mul_minimalRealPeriod_mul_tamagawaProduct` and
  `TauCeti.Isogeny.cast_kummerRatioProduct_eq`: the global period–Tamagawa formula over `ℚ`.
* `TauCeti.Isogeny.kummerRatioProduct_eq`, `TauCeti.Isogeny.kummerRatioProduct_self`,
  `TauCeti.Isogeny.kummerRatioProduct_mul_dual`, and `TauCeti.Isogeny.kummerRatioProduct_dual`:
  invariance under changing the isogeny, triviality on endomorphisms, and duality.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199, §2 (equations (2.4)–(2.11)).
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5, VII.5–6, X.4.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), §3.
-/

public noncomputable section

open IsDedekindDomain IsLocalRing WeierstrassCurve WeierstrassCurve.Affine ValuativeRel

namespace TauCeti.Isogeny

/-! ### Changes of Weierstrass variables -/

section VariableChange

variable {F K : Type*} [Field F] [Field K]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The isomorphism induced by a change of Weierstrass variables has Kummer ratio one. -/
@[simp]
theorem kummerRatio_variableChangeIsogeny (C : VariableChange F) (h : C • W₁ = W₂) :
    (variableChangeIsogeny C h).kummerRatio = 1 := by
  have h' : C⁻¹ • W₂ = W₁ := by rw [← h, inv_smul_smul]
  refine kummerRatio_eq_one_of_comp_eq_id (variableChangeIsogeny_inv_comp C h h') ?_
  rw [variableChangeIsogeny_comp C⁻¹ C h' h]
  convert variableChangeIsogeny_one (one_smul _ W₂) using 2
  exact mul_inv_cancel C

/-- Base-changing the isomorphism of a change of variables preserves Kummer ratio one. -/
@[simp]
theorem kummerRatio_map_variableChangeIsogeny (C : VariableChange F) (h : C • W₁ = W₂)
    (f : F →+* K) :
    ((variableChangeIsogeny C h).map f).kummerRatio = 1 := by
  have h' : C⁻¹ • W₂ = W₁ := by rw [← h, inv_smul_smul]
  have hcomp : (variableChangeIsogeny C h).comp (variableChangeIsogeny C⁻¹ h') = id W₂ := by
    rw [variableChangeIsogeny_comp C⁻¹ C h' h]
    convert variableChangeIsogeny_one (one_smul _ W₂) using 2
    exact mul_inv_cancel C
  refine kummerRatio_eq_one_of_comp_eq_id (ψ := (variableChangeIsogeny C⁻¹ h').map f) ?_ ?_
  · rw [← comp_map, variableChangeIsogeny_inv_comp C h h', id_map]
  · rw [← comp_map, hcomp, id_map]

/-- A change of variables has finite local Kummer ratio one at every height-one prime. -/
@[simp]
theorem finiteKummerRatio_variableChangeIsogeny {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R F] [IsFractionRing R F] {V₁ V₂ : WeierstrassCurve F} [V₁.IsElliptic] [V₂.IsElliptic]
    (C : VariableChange F) (h : C • V₁.toAffine = V₂.toAffine) (v : HeightOneSpectrum R) :
    (variableChangeIsogeny C h).finiteKummerRatio v = 1 := by
  rw [finiteKummerRatio_def, kummerRatio_map_variableChangeIsogeny]

/-- A change of variables over `ℚ` has real local Kummer ratio one. -/
@[simp]
theorem realKummerRatio_variableChangeIsogeny {E₁ E₂ : WeierstrassCurve ℚ}
    [E₁.IsElliptic] [E₂.IsElliptic] (C : VariableChange ℚ) (h : C • E₁.toAffine = E₂.toAffine) :
    (variableChangeIsogeny C h).realKummerRatio = 1 := by
  rw [realKummerRatio_def, kummerRatio_map_variableChangeIsogeny]

/-- A change of variables over `ℚ` has global product of local Kummer ratios one. -/
@[simp]
theorem kummerRatioProduct_variableChangeIsogeny {E₁ E₂ : WeierstrassCurve ℚ}
    [E₁.IsElliptic] [E₂.IsElliptic] (C : VariableChange ℚ) (h : C • E₁.toAffine = E₂.toAffine) :
    (variableChangeIsogeny C h).kummerRatioProduct = 1 := by
  simp [kummerRatioProduct_def]

end VariableChange

/-! ### Finite places: formal filtrations and local Tamagawa numbers -/

section FinitePlace

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]

/-- **The local Kummer ratio on minimal equations over `O_u`.** Let `V₁`, `V₂` be minimal elliptic
equations over `O_u = u.adicCompletionIntegers F` at a height-one prime `u` with finite residue
field, and let `φ : V₁ → V₂` be an isogeny over `F_u` with `φ^*ω₂ = c ω₁`, `2 ≠ 0` in `F_u`, and
`deg φ ≠ 0` in `A`. Then
`φ.kummerRatio = #(A ⧸ u)^(-log v(c)) · c_u(V₂) / c_u(V₁)`. -/
theorem kummerRatio_eq_of_isMinimal_adicCompletionIntegers
    (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]
    {V₁ V₂ : WeierstrassCurve (u.adicCompletion F)} [V₁.IsElliptic] [V₂.IsElliptic]
    [IsMinimal (u.adicCompletionIntegers F) V₁] [IsMinimal (u.adicCompletionIntegers F) V₂]
    (φ : Isogeny V₁.toAffine V₂.toAffine) {c : u.adicCompletion F}
    (hc : φ.pullbackDifferential (invariantDifferential V₂.toAffine) =
      c • invariantDifferential V₁.toAffine)
    (h2 : (2 : u.adicCompletion F) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    φ.kummerRatio =
      (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ (-WithZero.log (Valued.v c)) *
        (V₂.tamagawaNumber (valuation (u.adicCompletion F)) : ℚ) /
        V₁.tamagawaNumber (valuation (u.adicCompletion F)) := by
  classical
  let O_u := u.adicCompletionIntegers F
  let F_u := u.adicCompletion F
  let R_u := (Valued.v : Valuation F_u (WithZero (Multiplicative ℤ))).valuationSubring
  obtain ⟨C₁, rfl⟩ := (inferInstance : IsIntegral O_u V₁).integral
  obtain ⟨C₂, rfl⟩ := (inferInstance : IsIntegral O_u V₂).integral
  -- `c * c' = deg φ ≠ 0` in `F_u`, so `Valued.v c ≠ 0`
  obtain ⟨c', hc', -⟩ := φ.dual.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hn_Fu : (φ.degree : F_u) ≠ 0 := by
    rw [← map_natCast (algebraMap F F_u), ← map_natCast (algebraMap A F),
      map_ne_zero_iff _ (algebraMap F F_u).injective,
      map_ne_zero_iff _ (IsFractionRing.injective A F)]
    exact hn
  have hc0 : c ≠ 0 := left_ne_zero_of_mul
    (by rwa [φ.mul_eq_degree_of_pullbackDifferential_eq_smul hc hc'])
  have hvc : Valued.v c ≠ 0 := (Valued.v : Valuation F_u _).ne_zero_iff.mpr hc0
  -- Choose deep formal levels `k = k₀ + 1` and `j = j₀ + 1` with `j₀ = k₀ - log (v c)`.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_index_range_pointMapHom_mul_index_formalPointFiltration u
      (C₁ := C₁) (C₂ := C₂) hc h2 hn)
  set m : ℤ := WithZero.log (Valued.v c)
  let k₀ : ℕ := N + m.natAbs
  let j₀ : ℕ := ((k₀ : ℤ) - m).toNat
  have hj₀ : (j₀ : ℤ) = (k₀ : ℤ) - m := Int.toNat_of_nonneg (by omega)
  have hjk : Valued.v c * WithZero.exp ((j₀ + 1 : ℕ) : ℤ) = WithZero.exp ((k₀ + 1 : ℕ) : ℤ) := by
    rw [← WithZero.exp_log hvc, ← WithZero.exp_add, WithZero.exp_inj]
    change m + ((j₀ : ℤ) + 1) = (k₀ : ℤ) + 1
    omega
  have hdeep := hN (k₀ + 1) (by omega) (j₀ + 1) hjk
  -- Expand both formal filtration indices and identify the nonsingular reduction counts.
  rw [C₁.index_formalPointFiltration_eq_mul_tamagawaNumber u k₀,
    C₂.index_formalPointFiltration_eq_mul_tamagawaNumber u j₀] at hdeep
  have hcard : Nat.card ((integralModel R_u (C₁.baseChange F_u)).map (residue R_u)).toAffine.Point =
      Nat.card ((integralModel R_u (C₂.baseChange F_u)).map (residue R_u)).toAffine.Point :=
    (C₁.natCard_point_reduction_baseChange_adicCompletion_of_isMinimal).symm.trans
      (φ.natCard_point_reduction_eq.trans
        C₂.natCard_point_reduction_baseChange_adicCompletion_of_isMinimal)
  have hres : Nat.card (ResidueField O_u) = Nat.card (A ⧸ u.asIdeal) :=
    (Nat.card_congr (u.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv).symm
  let : IsDiscreteValuationRing (valuation F_u).valuationSubring :=
    inferInstanceAs (IsDiscreteValuationRing 𝒪[F_u])
  have hequiv := (ValuativeRel.isEquiv (valuation F_u)
    (Valued.v : Valuation F_u (WithZero (Multiplicative ℤ)))).symm
  have htam₁ : (C₁.baseChange F_u).tamagawaNumber Valued.v =
      (C₁.baseChange F_u).tamagawaNumber (valuation F_u) :=
    (C₁.baseChange F_u).tamagawaNumber_congr Valued.v hequiv
  have htam₂ : (C₂.baseChange F_u).tamagawaNumber Valued.v =
      (C₂.baseChange F_u).tamagawaNumber (valuation F_u) :=
    (C₂.baseChange F_u).tamagawaNumber_congr Valued.v hequiv
  rw [hres, hcard, htam₁, htam₂] at hdeep
  -- Positivity of the cancelled factors: residue cardinality, reduced points, kernel, Tamagawa.
  have : Finite (ResidueField R_u) := inferInstanceAs (Finite (ResidueField O_u))
  have := (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  let : HenselianLocalRing (valuation F_u).valuationSubring :=
    inferInstanceAs (HenselianLocalRing 𝒪[F_u])
  let : Finite (ResidueField (valuation F_u).valuationSubring) :=
    inferInstanceAs (Finite 𝓀[F_u])
  have hq0 : (Nat.card (A ⧸ u.asIdeal) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hqpow : (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ k₀ ≠ 0 := pow_ne_zero k₀ hq0
  have hred0 : (Nat.card
      ((integralModel R_u (C₂.baseChange F_u)).map (residue R_u)).toAffine.Point : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hker0 : (Nat.card (Hom.ofIsogeny φ).pointMapHom.ker : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have htam₁0 : ((C₁.baseChange F_u).tamagawaNumber (valuation F_u) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (tamagawaNumber_pos _ _).ne'
  have hdeepQ := congrArg (Nat.cast (R := ℚ)) hdeep
  push_cast at hdeepQ
  have hjpow : (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ j₀ =
      (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ k₀ * (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ (-m) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0, hj₀, sub_eq_add_neg]
  rw [hjpow] at hdeepQ
  rw [kummerRatio_def, div_eq_div_iff hker0 htam₁0]
  exact mul_right_cancel₀ (mul_ne_zero hqpow hred0) (by linear_combination hdeepQ)

/-- **The finite local Kummer ratio of an isogeny between arbitrary equations.** Let `φ : W₁ → W₂`
be an isogeny over `F` with `φ^*ω₂ = c ω₁`, and let `C₁`, `C₂` carry `W₁`, `W₂` to locally minimal
equations over `A_(u)` at a height-one prime `u` with finite residue field, assuming `2 ≠ 0` in `F`
and `deg φ ≠ 0` in `A`. Then
`φ.finiteKummerRatio u = #(A ⧸ u)^(-log v_u(c u₂ / u₁)) · c_u(W₂) / c_u(W₁)`. -/
theorem finiteKummerRatio_eq {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]
    {c : F} (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    {C₁ C₂ : VariableChange F}
    (hC₁ : IsMinimal (Localization.AtPrime u.asIdeal) (C₁ • W₁))
    (hC₂ : IsMinimal (Localization.AtPrime u.asIdeal) (C₂ • W₂))
    (h2 : (2 : F) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    φ.finiteKummerRatio u =
      (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ (-WithZero.log (u.valuation F (c * C₂.u / C₁.u))) *
        ((W₂.baseChange (u.adicCompletion F)).tamagawaNumber
          (valuation (u.adicCompletion F)) : ℚ) /
        (W₁.baseChange (u.adicCompletion F)).tamagawaNumber
          (valuation (u.adicCompletion F)) := by
  let i₁ : Isogeny (C₁ • W₁).toAffine W₁.toAffine :=
    variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ W₁.toAffine)
  let i₂ : Isogeny W₂.toAffine (C₂ • W₂).toAffine := variableChangeIsogeny C₂ rfl
  let ψ : Isogeny (C₁ • W₁).toAffine (C₂ • W₂).toAffine := i₂.comp (φ.comp i₁)
  have hψ_ratio : ψ.finiteKummerRatio u = φ.finiteKummerRatio u := by
    simp [ψ, i₁, i₂]
  have hψ_deg : ψ.degree = φ.degree := by
    simp [ψ, i₁, i₂]
  have hψ_diff : ψ.pullbackDifferential (invariantDifferential (C₂ • W₂).toAffine) =
      (c * C₂.u / C₁.u) • invariantDifferential (C₁ • W₁).toAffine := by
    dsimp only [ψ, i₁, i₂]
    rw [pullbackDifferential_comp, LinearMap.comp_apply,
      pullbackDifferential_variableChangeIsogeny_invariantDifferential, map_smul,
      pullbackDifferential_comp, LinearMap.comp_apply, hc, map_smul,
      pullbackDifferential_variableChangeIsogeny_invariantDifferential,
      VariableChange.inv_def, Units.val_inv_eq_inv_val, smul_smul, smul_smul]
    congr 1
    ring
  have h2_Fu : (2 : u.adicCompletion F) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (u.adicCompletion F)) 2,
      map_ne_zero_iff _ (algebraMap F (u.adicCompletion F)).injective]
    exact h2
  have hn_ψ : ((ψ.map (algebraMap F (u.adicCompletion F))).degree : A) ≠ 0 := by
    rwa [degree_map, hψ_deg]
  have : IsMinimal (u.adicCompletionIntegers F) ((C₁ • W₁).baseChange (u.adicCompletion F)) := by
    have := hC₁; infer_instance
  have : IsMinimal (u.adicCompletionIntegers F) ((C₂ • W₂).baseChange (u.adicCompletion F)) := by
    have := hC₂; infer_instance
  have hval : Valued.v (algebraMap F (u.adicCompletion F) (c * C₂.u / C₁.u)) =
      u.valuation F (c * C₂.u / C₁.u) := by
    rw [u.algebraMap_adicCompletion (K := F), Function.comp_apply,
      u.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]
  have hk := kummerRatio_eq_of_isMinimal_adicCompletionIntegers u
    (V₁ := (C₁ • W₁).baseChange (u.adicCompletion F))
    (V₂ := (C₂ • W₂).baseChange (u.adicCompletion F))
    (ψ.map (algebraMap F (u.adicCompletion F)))
    (map_pullbackDifferential_invariantDifferential_eq_smul ψ _ hψ_diff) h2_Fu hn_ψ
  have hk' : ψ.finiteKummerRatio u =
      (Nat.card (A ⧸ u.asIdeal) : ℚ) ^
          (-WithZero.log (Valued.v (algebraMap F (u.adicCompletion F) (c * C₂.u / C₁.u)))) *
        (((C₂ • W₂).baseChange (u.adicCompletion F)).tamagawaNumber
          (valuation (u.adicCompletion F)) : ℚ) /
        ((C₁ • W₁).baseChange (u.adicCompletion F)).tamagawaNumber
          (valuation (u.adicCompletion F)) := by
    rw [finiteKummerRatio_def]
    exact hk
  rw [← hψ_ratio, hk', hval, ← baseChange_smul_baseChange, ← baseChange_smul_baseChange,
    tamagawaNumber_smul, tamagawaNumber_smul]

/-- **The finite local Kummer ratio on locally minimal equations.** When `W₁` and `W₂` are already
minimal over `A_(u)`, no scaling-factor correction `u₂ / u₁` appears. -/
theorem finiteKummerRatio_eq_of_isMinimal {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
    (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]
    [h₁ : IsMinimal (Localization.AtPrime u.asIdeal) W₁]
    [h₂ : IsMinimal (Localization.AtPrime u.asIdeal) W₂]
    {c : F} (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    (h2 : (2 : F) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    φ.finiteKummerRatio u =
      (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ (-WithZero.log (u.valuation F c)) *
        ((W₂.baseChange (u.adicCompletion F)).tamagawaNumber
          (valuation (u.adicCompletion F)) : ℚ) /
        (W₁.baseChange (u.adicCompletion F)).tamagawaNumber
          (valuation (u.adicCompletion F)) := by
  have hC₁ : IsMinimal (Localization.AtPrime u.asIdeal) ((1 : VariableChange F) • W₁) := by
    simpa only [one_smul] using h₁
  have hC₂ : IsMinimal (Localization.AtPrime u.asIdeal) ((1 : VariableChange F) • W₂) := by
    simpa only [one_smul] using h₂
  simpa [VariableChange.one_def] using φ.finiteKummerRatio_eq u hc hC₁ hC₂ h2 hn

/-- **The finite local Kummer ratio in terms of `WeierstrassCurve.tamagawaNumberAt`**, over a
Dedekind domain with finite quotients. -/
theorem finiteKummerRatio_eq_tamagawaNumberAt [Ring.HasFiniteQuotients A]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (u : HeightOneSpectrum A) {c : F}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    {C₁ C₂ : VariableChange F}
    (hC₁ : IsMinimal (Localization.AtPrime u.asIdeal) (C₁ • W₁))
    (hC₂ : IsMinimal (Localization.AtPrime u.asIdeal) (C₂ • W₂))
    (h2 : (2 : F) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    φ.finiteKummerRatio u =
      (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ (-WithZero.log (u.valuation F (c * C₂.u / C₁.u))) *
        (W₂.tamagawaNumberAt u : ℚ) / W₁.tamagawaNumberAt u := by
  have : Finite (A ⧸ u.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient u.ne_bot
  simp only [tamagawaNumberAt_def, φ.finiteKummerRatio_eq u hc hC₁ hC₂ h2 hn]

/-- **The finite local Kummer ratio on locally minimal equations via `tamagawaNumberAt`.** -/
theorem finiteKummerRatio_eq_tamagawaNumberAt_of_isMinimal [Ring.HasFiniteQuotients A]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (u : HeightOneSpectrum A)
    [h₁ : IsMinimal (Localization.AtPrime u.asIdeal) W₁]
    [h₂ : IsMinimal (Localization.AtPrime u.asIdeal) W₂]
    {c : F} (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    (h2 : (2 : F) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    φ.finiteKummerRatio u =
      (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ (-WithZero.log (u.valuation F c)) *
        (W₂.tamagawaNumberAt u : ℚ) / W₁.tamagawaNumberAt u := by
  have : Finite (A ⧸ u.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient u.ne_bot
  simp only [tamagawaNumberAt_def, φ.finiteKummerRatio_eq_of_isMinimal u hc h2 hn]

/-- **The finite local Kummer ratio on globally minimal equations via `tamagawaNumberAt`.** -/
theorem finiteKummerRatio_eq_tamagawaNumberAt_of_isGlobalMinimal [Ring.HasFiniteQuotients A]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (u : HeightOneSpectrum A) {c : F}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    (h₁ : IsGlobalMinimal A W₁) (h₂ : IsGlobalMinimal A W₂)
    (h2 : (2 : F) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    φ.finiteKummerRatio u =
      (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ (-WithZero.log (u.valuation F c)) *
        (W₂.tamagawaNumberAt u : ℚ) / W₁.tamagawaNumberAt u := by
  have := h₁.isMinimal u
  have := h₂.isMinimal u
  exact φ.finiteKummerRatio_eq_tamagawaNumberAt_of_isMinimal u hc h2 hn

end FinitePlace

/-! ### The real place and the global period–Tamagawa formula over `ℚ` -/

section Rational

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **The real Kummer ratio of an isogeny over `ℚ` via minimal real periods.** If `φ^*ω₂ = c ω₁`
and `C₁`, `C₂` carry `E₁`, `E₂` to globally minimal equations with scaling factors `u₁`, `u₂`, then
`|c u₂ / u₁| Ω(E₁) · φ.realKummerRatio = Ω(E₂)`. -/
theorem abs_mul_minimalRealPeriod_mul_realKummerRatio (φ : Isogeny E₁.toAffine E₂.toAffine)
    {c : ℚ} (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod * (φ.realKummerRatio : ℝ) =
      E₂.minimalRealPeriod := by
  classical
  have h := φ.abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul hc hC₁ hC₂
  have := (Hom.ofIsogeny (φ.baseChange ℝ)).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have hker : (Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hrk : (φ.realKummerRatio : ℝ) =
      ((Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index : ℝ) /
        Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker := by
    rw [realKummerRatio_def, kummerRatio_def]
    push_cast
    rfl
  rw [hrk, ← mul_div_assoc, h, mul_div_cancel_left₀ _ hker]

/-- **The real Kummer ratio of an isogeny between global minimal equations over `ℚ`.** -/
theorem abs_mul_minimalRealPeriod_mul_realKummerRatio_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    |(c : ℝ)| * E₁.minimalRealPeriod * (φ.realKummerRatio : ℝ) = E₂.minimalRealPeriod := by
  have hC₁ : IsGlobalMinimal ℤ ((1 : VariableChange ℚ) • E₁) := by simpa only [one_smul] using h₁
  have hC₂ : IsGlobalMinimal ℤ ((1 : VariableChange ℚ) • E₂) := by simpa only [one_smul] using h₂
  simpa [VariableChange.one_def] using
    φ.abs_mul_minimalRealPeriod_mul_realKummerRatio hc hC₁ hC₂

/-- For a nonzero integer `a`, `#(ℤ ⧸ v) ^ (-log v(a))` equals the absolute norm of
`v.maxPowDividing (Ideal.span {a})` at every height-one prime `v` of `ℤ`. -/
private theorem card_quotient_zpow_neg_log_valuation_int {a : ℤ} (ha : a ≠ 0)
    (v : HeightOneSpectrum ℤ) :
    (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation ℚ (a : ℚ))) =
      (Ideal.absNorm (v.maxPowDividing (Ideal.span ({a} : Set ℤ))) : ℚ) := by
  change (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^
    (-WithZero.log (v.valuation ℚ (algebraMap ℤ ℚ a))) = _
  rw [v.valuation_of_algebraMap, v.intValuation_if_neg ha, WithZero.log_exp, neg_neg,
    zpow_natCast, HeightOneSpectrum.maxPowDividing, map_pow, Ideal.absNorm_eq_natCard,
    Nat.cast_pow]

/-- The prime-power factor `p ^ ord_p(a)` of a nonzero integer `a` has finite multiplicative
support over `HeightOneSpectrum ℤ`. -/
private theorem hasFiniteMulSupport_card_quotient_zpow_int {a : ℤ} (ha : a ≠ 0) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum ℤ ↦
      (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation ℚ (a : ℚ))) := by
  have hJ : (Ideal.span ({a} : Set ℤ) : Ideal ℤ) ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using ha
  refine (Ideal.hasFiniteMulSupport hJ).subset fun v hv h1 ↦ ?_
  rw [Function.mem_mulSupport, card_quotient_zpow_neg_log_valuation_int ha v] at hv
  exact hv (by simp [h1])

/-- The product over all primes `v` of `ℤ` of `#(ℤ ⧸ v) ^ (-log v(a))` equals `|a|` for any nonzero
integer `a`. -/
private theorem finprod_card_quotient_zpow_int {a : ℤ} (ha : a ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum ℤ,
      (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation ℚ (a : ℚ)))) = |(a : ℚ)| := by
  have hJ : (Ideal.span ({a} : Set ℤ) : Ideal ℤ) ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using ha
  have hcast : (∏ᶠ v : HeightOneSpectrum ℤ,
      (Ideal.absNorm (v.maxPowDividing (Ideal.span ({a} : Set ℤ))) : ℚ)) =
      (Ideal.absNorm (∏ᶠ v : HeightOneSpectrum ℤ,
        v.maxPowDividing (Ideal.span ({a} : Set ℤ))) : ℚ) :=
    (((Nat.castRingHom ℚ).toMonoidHom.comp Ideal.absNorm.toMonoidHom).map_finprod
      (Ideal.hasFiniteMulSupport hJ)).symm
  simp_rw [card_quotient_zpow_neg_log_valuation_int ha]
  rw [hcast, Ideal.finprod_heightOneSpectrum_factorization hJ, Ideal.absNorm_eq_natCard,
    Nat.card_congr (Int.quotientSpanEquivZMod a).toEquiv, Nat.card_zmod, Nat.cast_natAbs,
    Int.cast_abs]

/-- At every prime `v` of `ℤ`, `#(ℤ ⧸ v) ^ (-log v(x))` splits as numerator divided by denominator
for any nonzero rational `x`. -/
private theorem card_quotient_zpow_neg_log_valuation_rat {x : ℚ} (hx : x ≠ 0)
    (v : HeightOneSpectrum ℤ) :
    (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation ℚ x)) =
      (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation ℚ (x.num : ℚ))) /
        (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation ℚ ((x.den : ℤ) : ℚ))) := by
  have : Finite (ℤ ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have hq0 : (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have ha : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hb : (x.den : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
  have hva : v.valuation ℚ (x.num : ℚ) ≠ 0 :=
    (v.valuation ℚ).ne_zero_iff.mpr (Int.cast_ne_zero.mpr ha)
  have hvb : v.valuation ℚ ((x.den : ℤ) : ℚ) ≠ 0 :=
    (v.valuation ℚ).ne_zero_iff.mpr (Int.cast_ne_zero.mpr hb)
  have hxab : x = (x.num : ℚ) / ((x.den : ℤ) : ℚ) := by simpa using (Rat.num_div_den x).symm
  conv_lhs => rw [hxab]
  rw [map_div₀, WithZero.log_div hva hvb, neg_sub, ← zpow_sub₀ hq0, sub_eq_add_neg, add_comm,
    ← sub_neg_eq_add]

/-- The prime-power factor `p ^ ord_p(x)` of a nonzero rational `x` has finite multiplicative
support over `HeightOneSpectrum ℤ`. -/
private theorem hasFiniteMulSupport_card_quotient_zpow_neg_log_valuation {x : ℚ} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum ℤ ↦
      (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation ℚ x)) := by
  have hnum := hasFiniteMulSupport_card_quotient_zpow_int (Rat.num_ne_zero.mpr hx)
  have hden := hasFiniteMulSupport_card_quotient_zpow_int (Nat.cast_ne_zero.mpr x.den_nz)
  refine (hnum.union hden).subset fun v hv ↦ ?_
  rw [Function.mem_mulSupport, card_quotient_zpow_neg_log_valuation_rat hx v] at hv
  rw [Set.mem_union, Function.mem_mulSupport, Function.mem_mulSupport]
  by_contra! h
  exact hv (by rw [h.1, h.2, div_one])

/-- The product over all primes `v` of `ℤ` of `#(ℤ ⧸ v) ^ (-log v(x))` equals `|x|` for any nonzero
rational `x`. -/
private theorem finprod_card_quotient_zpow_neg_log_valuation {x : ℚ} (hx : x ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum ℤ,
      (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation ℚ x))) = |x| := by
  have ha : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hb : (x.den : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
  simp_rw [card_quotient_zpow_neg_log_valuation_rat hx]
  rw [finprod_div_distrib (hasFiniteMulSupport_card_quotient_zpow_int ha)
      (hasFiniteMulSupport_card_quotient_zpow_int hb),
    finprod_card_quotient_zpow_int ha, finprod_card_quotient_zpow_int hb, ← abs_div]
  congr 1
  simpa using Rat.num_div_den x

/-- **The product of finite local Kummer ratios over `ℚ`.** If `φ^*ω₂ = c ω₁` and `C₁`, `C₂` carry
`E₁`, `E₂` to globally minimal equations over `ℤ` with scaling factors `u₁`, `u₂`, then
`∏_p φ.finiteKummerRatio p = |c u₂ / u₁| · tamagawaProduct E₂ / tamagawaProduct E₁`. -/
theorem finprod_finiteKummerRatio_eq (φ : Isogeny E₁.toAffine E₂.toAffine)
    {c : ℚ} (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    (∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) =
      |c * C₂.u / C₁.u| * (E₂.tamagawaProduct (R := ℤ) : ℚ) /
        E₁.tamagawaProduct (R := ℤ) := by
  set x : ℚ := c * C₂.u / C₁.u
  have hx : x ≠ 0 := div_ne_zero
    (mul_ne_zero (φ.ne_zero_of_pullbackDifferential_eq_smul hc) C₂.u.ne_zero) C₁.u.ne_zero
  have hfactor (v : HeightOneSpectrum ℤ) : φ.finiteKummerRatio v =
      (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation ℚ x)) *
        (E₂.tamagawaNumberAt v : ℚ) / E₁.tamagawaNumberAt v :=
    φ.finiteKummerRatio_eq_tamagawaNumberAt v hc (hC₁.isMinimal v) (hC₂.isMinimal v)
      two_ne_zero (Nat.cast_ne_zero.mpr φ.degree_pos.ne')
  have hfq := hasFiniteMulSupport_card_quotient_zpow_neg_log_valuation hx
  have hft₁ : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum ℤ ↦ (E₁.tamagawaNumberAt v : ℚ)) :=
    (E₁.hasFiniteMulSupport_tamagawaNumberAt (R := ℤ)).subset fun v hv h1 ↦
      hv (by simp [h1])
  have hft₂ : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum ℤ ↦ (E₂.tamagawaNumberAt v : ℚ)) :=
    (E₂.hasFiniteMulSupport_tamagawaNumberAt (R := ℤ)).subset fun v hv h1 ↦
      hv (by simp [h1])
  have hfq₂ : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum ℤ ↦
      (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation ℚ x)) *
        (E₂.tamagawaNumberAt v : ℚ)) :=
    (hfq.union hft₂).subset fun v hv ↦ by
      rw [Function.mem_mulSupport] at hv
      rw [Set.mem_union, Function.mem_mulSupport, Function.mem_mulSupport]
      by_contra! h
      exact hv (by rw [h.1, h.2, mul_one])
  have hprod₁ : (∏ᶠ v : HeightOneSpectrum ℤ, (E₁.tamagawaNumberAt v : ℚ)) =
      E₁.tamagawaProduct (R := ℤ) := by
    rw [E₁.tamagawaProduct_def]
    exact ((Nat.castRingHom ℚ).toMonoidHom.map_finprod
      (E₁.hasFiniteMulSupport_tamagawaNumberAt (R := ℤ))).symm
  have hprod₂ : (∏ᶠ v : HeightOneSpectrum ℤ, (E₂.tamagawaNumberAt v : ℚ)) =
      E₂.tamagawaProduct (R := ℤ) := by
    rw [E₂.tamagawaProduct_def]
    exact ((Nat.castRingHom ℚ).toMonoidHom.map_finprod
      (E₂.hasFiniteMulSupport_tamagawaNumberAt (R := ℤ))).symm
  simp_rw [hfactor]
  rw [finprod_div_distrib hfq₂ hft₁, finprod_mul_distrib hfq hft₂,
    finprod_card_quotient_zpow_neg_log_valuation hx, hprod₂, hprod₁]

/-- **The product of finite local Kummer ratios between globally minimal equations over `ℚ`.** -/
theorem finprod_finiteKummerRatio_eq_of_isGlobalMinimal (φ : Isogeny E₁.toAffine E₂.toAffine)
    {c : ℚ} (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    (∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) =
      |c| * (E₂.tamagawaProduct (R := ℤ) : ℚ) / E₁.tamagawaProduct (R := ℤ) := by
  have hC₁ : IsGlobalMinimal ℤ ((1 : VariableChange ℚ) • E₁) := by simpa only [one_smul] using h₁
  have hC₂ : IsGlobalMinimal ℤ ((1 : VariableChange ℚ) • E₂) := by simpa only [one_smul] using h₂
  simpa [VariableChange.one_def] using φ.finprod_finiteKummerRatio_eq hc hC₁ hC₂

/-- **The global period–Tamagawa formula for `kummerRatioProduct` over `ℚ`** (Cassels, 1965):
multiplying the product of all local Kummer ratios of `φ : E₁ → E₂` by `Ω(E₁) · ∏_p c_p(E₁)`
yields `Ω(E₂) · ∏_p c_p(E₂)`. No choice of invariant-differential scalar or minimal equations
appears in the statement. -/
theorem kummerRatioProduct_mul_minimalRealPeriod_mul_tamagawaProduct
    (φ : Isogeny E₁.toAffine E₂.toAffine) :
    (φ.kummerRatioProduct : ℝ) * E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) =
      E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  obtain ⟨C₁, hC₁⟩ := exists_isGlobalMinimal_smul ℤ E₁
  obtain ⟨C₂, hC₂⟩ := exists_isGlobalMinimal_smul ℤ E₂
  have ht₁ : (E₁.tamagawaProduct (R := ℤ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (E₁.tamagawaProduct_pos (R := ℤ)).ne'
  have hreal := φ.abs_mul_minimalRealPeriod_mul_realKummerRatio hc hC₁ hC₂
  have hfin := congrArg (Rat.cast (K := ℝ)) (φ.finprod_finiteKummerRatio_eq hc hC₁ hC₂)
  calc (φ.kummerRatioProduct : ℝ) * E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ)
    _ = (φ.realKummerRatio : ℝ) *
          (|((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₂.tamagawaProduct (R := ℤ) /
            E₁.tamagawaProduct (R := ℤ)) *
          E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) := by
        rw [φ.kummerRatioProduct_def, Rat.cast_mul, hfin]
        push_cast
        rfl
    _ = (|((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod * (φ.realKummerRatio : ℝ)) *
          E₂.tamagawaProduct (R := ℤ) := by
        field_simp [ht₁]
    _ = E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by
        rw [hreal]

/-- **Ratio form of the global period–Tamagawa formula over `ℚ`**: `(φ.kummerRatioProduct : ℝ)` is
the ratio of `Ω(E₂) · ∏_p c_p(E₂)` to `Ω(E₁) · ∏_p c_p(E₁)`. -/
theorem cast_kummerRatioProduct_eq (φ : Isogeny E₁.toAffine E₂.toAffine) :
    (φ.kummerRatioProduct : ℝ) =
      E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) /
        (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ)) := by
  have hden : E₁.minimalRealPeriod * (E₁.tamagawaProduct (R := ℤ) : ℝ) ≠ 0 :=
    mul_ne_zero E₁.minimalRealPeriod_pos.ne'
      (Nat.cast_ne_zero.mpr (E₁.tamagawaProduct_pos (R := ℤ)).ne')
  rw [eq_div_iff hden, ← mul_assoc, φ.kummerRatioProduct_mul_minimalRealPeriod_mul_tamagawaProduct]

/-- **The global product of local Kummer ratios over `ℚ` depends only on `E₁` and `E₂`**, not on
the choice of isogeny `E₁ → E₂`. -/
theorem kummerRatioProduct_eq (φ ψ : Isogeny E₁.toAffine E₂.toAffine) :
    φ.kummerRatioProduct = ψ.kummerRatioProduct :=
  Rat.cast_injective (α := ℝ)
    (φ.cast_kummerRatioProduct_eq.trans ψ.cast_kummerRatioProduct_eq.symm)

/-- **Every endomorphism-isogeny `φ : E → E` over `ℚ` has global Kummer ratio product one.** -/
theorem kummerRatioProduct_self (φ : Isogeny E₁.toAffine E₁.toAffine) :
    φ.kummerRatioProduct = 1 :=
  (kummerRatioProduct_eq φ (Isogeny.id E₁.toAffine)).trans (kummerRatioProduct_id E₁)

/-- **Product reciprocity of `kummerRatioProduct` with the dual isogeny over `ℚ`.** -/
theorem kummerRatioProduct_mul_dual (φ : Isogeny E₁.toAffine E₂.toAffine) :
    φ.kummerRatioProduct * φ.dual.kummerRatioProduct = 1 := by
  rw [← kummerRatioProduct_comp, kummerRatioProduct_self]

/-- **The dual isogeny over `ℚ` inverts `kummerRatioProduct`.** -/
theorem kummerRatioProduct_dual (φ : Isogeny E₁.toAffine E₂.toAffine) :
    φ.dual.kummerRatioProduct = (φ.kummerRatioProduct)⁻¹ :=
  eq_inv_of_mul_eq_one_right φ.kummerRatioProduct_mul_dual

end Rational

end TauCeti.Isogeny
