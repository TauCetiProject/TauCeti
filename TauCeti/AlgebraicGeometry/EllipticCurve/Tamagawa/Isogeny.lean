/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Ratio
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MinimalRealPeriod
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AdicCompletion
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DefectIdeal
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Index
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GlobalExistence
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Isogeny
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# Local Kummer ratios, Tamagawa numbers, and minimal real periods under an isogeny

Let `φ : E₁ → E₂` be an isogeny of elliptic curves pulling the invariant differential back as
`φ^*ω₂ = c ω₁`. This file relates the local Kummer ratios
`[E₂(K_v) : φ E₁(K_v)] / #E₁(K_v)[φ]` to local Tamagawa numbers, Weierstrass defect ideals, and
(over `ℚ`) the minimal real period `Ω(E)`, proving Cassels' local-global product formula for the
period–Tamagawa product.

At a height-one prime `u` of a Dedekind domain `A` with finite residue field `κ(u)` of size `q`,
assuming `2 ≠ 0` in the completion `F_u` and `(deg φ : A) ≠ 0`, an isogeny between minimal
Weierstrass equations over `O_u` maps the deep formal-group level `E_k(F_u)` onto `E_j(F_u)` with
`j = k - log(v_u c)` (`TauCeti.Isogeny.eventually_map_pointMapHom_formalPointFiltration_eq`).
Expanding the level indices into the formal power `q^k`, the reduced nonsingular point count
`#E_ns(κ(u))`, and the local Tamagawa number `c_u` (`WeierstrassCurve.index_formalPointFiltration`),
and cancelling the isogeny-invariant count `#E_ns(κ(u))`
(`TauCeti.Isogeny.natCard_point_reduction_eq`), yields the local identity

`q ^ log(v_u c) · c_u(E₁) · ([E₂(F_u) : φ E₁(F_u)] / #E₁(F_u)[φ]) = c_u(E₂)`.

Passing from arbitrary Weierstrass equations over a global fraction field `K` to local minimal
models introduces the local obstruction exponents `f_v(E_i)`, which assemble over a number field
`K` (of arbitrary class number) into the absolute norms of the Weierstrass defect ideals `𝔍_{E_i}`.
Combining all finite places via the number-field product formula gives the exact rational identity

`(∏ᶠ v, finiteKummerRatio φ v) · N(𝔍_{E₁}) · ∏_v c_v(E₁) = |N_{K/ℚ}(c)| · N(𝔍_{E₂}) · ∏_v c_v(E₂)`.

Over `ℚ`, every elliptic curve admits a global minimal equation over `ℤ`, and combining the finite
primes with the real-period transformation `|c u₂ / u₁| Ω(E₁) · realKummerRatio φ = Ω(E₂)` cancels
the differential scaling factor completely:

`kummerRatioProduct φ · (Ω(E₁) · ∏_p c_p(E₁)) = Ω(E₂) · ∏_p c_p(E₂)`.

In particular, `kummerRatioProduct φ` depends only on the source and target curves `E₁` and `E₂`,
equals `1` for every endomorphism isogeny, and satisfies `kummerRatioProduct φ̂ =
(kummerRatioProduct φ)⁻¹`. No claim about global Selmer or Tate–Shafarevich groups is made here;
this file supplies the unconditional period–Tamagawa–Kummer half of Cassels' isogeny-invariance
calculation.

## Main results

* `TauCeti.Isogeny.kummerRatio_variableChangeIsogeny`,
  `TauCeti.Isogeny.finiteKummerRatio_variableChangeIsogeny`,
  `TauCeti.Isogeny.realKummerRatio_variableChangeIsogeny`,
  `TauCeti.Isogeny.kummerRatioProduct_variableChangeIsogeny`: a Weierstrass change of variables has
  local and global Kummer ratios equal to `1`.
* `TauCeti.Isogeny.zpow_log_valued_mul_tamagawaNumber_mul_kummerRatio_of_isMinimal` and
  `TauCeti.Isogeny.zpow_log_valued_mul_tamagawaNumber_mul_kummerRatio`: the local Kummer-ratio and
  Tamagawa-number formula over an adic completion `u.adicCompletion F`.
* `TauCeti.Isogeny.zpow_log_valuation_mul_tamagawaNumberAt_mul_finiteKummerRatio` and
  `TauCeti.Isogeny.adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio`: the finite-place formula
  over the fraction field of a Dedekind domain with finite quotients, in both `ℚ` and `ℝ`.
* `TauCeti.Isogeny.finprod_finiteKummerRatio_mul_absNorm_weierstrassDefectIdeal_mul_tamagawaProduct`
  and `TauCeti.Isogeny.finprod_finiteKummerRatio_mul_tamagawaProduct`: the finite-place product
  formula over an arbitrary number field `K`.
* `TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_realKummerRatio`: the real-place counterpart for
  elliptic curves over `ℚ`.
* `TauCeti.Isogeny.kummerRatioProduct_mul_minimalRealPeriod_mul_tamagawaProduct`,
  `TauCeti.Isogeny.cast_kummerRatioProduct`, `TauCeti.Isogeny.kummerRatioProduct_eq`,
  `TauCeti.Isogeny.kummerRatioProduct_self`, and `TauCeti.Isogeny.kummerRatioProduct_dual`: the
  global period–Tamagawa transformation and invariance consequences over `ℚ`.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199, §2–3.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), 79–114, §3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, III.5, VII.6, VIII.8,
  and Appendix C.16.
-/

public noncomputable section

open Filter IsDedekindDomain IsLocalRing ValuativeRel WeierstrassCurve WeierstrassCurve.Affine
open scoped NumberField NNReal WithZero

namespace TauCeti.Isogeny

/-! ### Change-of-variables isogenies -/

section VariableChange

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- If `(deg φ : F) ≠ 0` and `φ^*ω₂ = c ω₁`, then `φ` is separable and hence `c ≠ 0`. -/
private theorem ne_zero_of_pullbackDifferential_eq_smul_of_degree_ne_zero
    [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁ W₂) {c : F}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    (hdeg : (φ.degree : F) ≠ 0) : c ≠ 0 :=
  (isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul φ hc).mp
    (φ.isSeparable_dual_and_self_iff.2 hdeg).2

/-- A Weierstrass change of variables induces a point-group bijection and hence has Kummer ratio
one. -/
@[simp]
theorem kummerRatio_variableChangeIsogeny [W₁.IsElliptic] [W₂.IsElliptic]
    (C : VariableChange F) (h : C • W₁ = W₂) :
    (variableChangeIsogeny C h).kummerRatio = 1 :=
  kummerRatio_eq_one_of_degree_eq_one (degree_variableChangeIsogeny C h)

/-- Sandwiching an isogeny `φ : W₁ → W₂` between changes of variables `C₁⁻¹ : W₁' → W₁` and
`C₂ : W₂ → W₂'` scales its invariant-differential constant `c` to `c · C₂.u / C₁.u`. -/
theorem pullbackDifferential_variableChangeIsogeny_comp_invariantDifferential
    {W₁' W₂' : WeierstrassCurve.Affine F} (φ : Isogeny W₁ W₂) {c : F}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    (C₁ C₂ : VariableChange F) (h₁ : C₁⁻¹ • W₁' = W₁) (h₂ : C₂ • W₂ = W₂') :
    ((variableChangeIsogeny C₂ h₂).comp
        (φ.comp (variableChangeIsogeny C₁⁻¹ h₁))).pullbackDifferential
        (invariantDifferential W₂') =
      (c * C₂.u / C₁.u) • invariantDifferential W₁' := by
  rw [pullbackDifferential_comp, pullbackDifferential_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, pullbackDifferential_variableChangeIsogeny_invariantDifferential,
    map_smul, hc, map_smul, map_smul,
    pullbackDifferential_variableChangeIsogeny_invariantDifferential, smul_smul, smul_smul,
    show (C₁⁻¹.u : F) = (C₁.u : F)⁻¹ by simp [VariableChange.inv_def]]
  congr 1
  ring

end VariableChange

section GlobalVariableChange

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

/-- A Weierstrass change of variables has finite local Kummer ratio one at every prime. -/
@[simp]
theorem finiteKummerRatio_variableChangeIsogeny (C : VariableChange K) (h : C • W₁ = W₂)
    (v : HeightOneSpectrum R) : (variableChangeIsogeny C h).finiteKummerRatio v = 1 :=
  finiteKummerRatio_eq_one_of_degree_eq_one (degree_variableChangeIsogeny C h) v

end GlobalVariableChange

section RationalVariableChange

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- A Weierstrass change of variables over `ℚ` has real Kummer ratio one. -/
@[simp]
theorem realKummerRatio_variableChangeIsogeny (C : VariableChange ℚ) (h : C • E₁ = E₂) :
    (variableChangeIsogeny C h).realKummerRatio = 1 :=
  realKummerRatio_eq_one_of_degree_eq_one (degree_variableChangeIsogeny C h)

/-- A Weierstrass change of variables over `ℚ` has global Kummer ratio product one. -/
@[simp]
theorem kummerRatioProduct_variableChangeIsogeny (C : VariableChange ℚ) (h : C • E₁ = E₂) :
    (variableChangeIsogeny C h).kummerRatioProduct = 1 :=
  kummerRatioProduct_eq_one_of_degree_eq_one (degree_variableChangeIsogeny C h)

end RationalVariableChange

/-! ### Local Kummer ratio and Tamagawa numbers over an adic completion -/

section AdicCompletion

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "R_u" =>
  Valuation.valuationSubring
    (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))

private local instance : IsDiscreteValuationRing R_u :=
  inferInstanceAs (IsDiscreteValuationRing O_u)

omit [Finite (A ⧸ u.asIdeal)] in
/-- The reduced curve over `R_u` and the reduction over `𝒪[F_u]` have equally many nonsingular
points, since `R_u` and `(ValuativeRel.valuation F_u).valuationSubring` are equal as valuation
subrings of `F_u`. -/
private theorem natCard_point_reduction_adicCompletion (V : WeierstrassCurve F_u)
    [IsIntegral R_u V] [hM : IsMinimal 𝒪[F_u] V] :
    Nat.card ((integralModel R_u V).map (residue R_u)).toAffine.Point =
      Nat.card (V.reduction 𝒪[F_u]).toAffine.Point := by
  have hT : ∀ (T : ValuationSubring F_u) [IsDiscreteValuationRing T] [IsMinimal T V], R_u = T →
      Nat.card ((integralModel R_u V).map (residue R_u)).toAffine.Point =
        Nat.card (V.reduction T).toAffine.Point := by
    rintro T _ _ rfl
    rfl
  exact @hT (ValuativeRel.valuation F_u).valuationSubring
    (inferInstanceAs (IsDiscreteValuationRing 𝒪[F_u])) hM
    (ValuationSubring.toSubring_injective (u.integer_eq_adicCompletionIntegers (K := F)).symm)

variable {W₁ W₂ : WeierstrassCurve (u.adicCompletion F)} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The local Kummer ratio of an isogeny between minimal equations over an adic completion.**
Let `φ : W₁ → W₂` be an isogeny between minimal Weierstrass equations over `O_u` pulling the
invariant differential back as `φ^*ω₂ = c ω₁`, with `2 ≠ 0` in `F_u` and `(deg φ : A) ≠ 0`. Then

`(#𝓀[F_u]) ^ log(v_u c) · c_u(W₁) · kummerRatio φ = c_u(W₂)`. -/
theorem zpow_log_valued_mul_tamagawaNumber_mul_kummerRatio_of_isMinimal
    [IsMinimal O_u W₁] [IsMinimal O_u W₂] (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F_u}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    (Nat.card 𝓀[F_u] : ℚ) ^ WithZero.log (Valued.v c) *
        W₁.tamagawaNumber (ValuativeRel.valuation F_u) * φ.kummerRatio =
      W₂.tamagawaNumber (ValuativeRel.valuation F_u) := by
  classical
  obtain ⟨C₁, rfl⟩ : ∃ C₁ : WeierstrassCurve O_u, C₁.baseChange F_u = W₁ :=
    ⟨W₁.integralModel O_u, baseChange_integralModel_eq O_u W₁⟩
  obtain ⟨C₂, rfl⟩ : ∃ C₂ : WeierstrassCurve O_u, C₂.baseChange F_u = W₂ :=
    ⟨W₂.integralModel O_u, baseChange_integralModel_eq O_u W₂⟩
  have hdeg0 : (φ.degree : F_u) ≠ 0 := fun h ↦ hn <| IsFractionRing.injective A F <|
    (algebraMap F F_u).injective <| by
      rw [map_natCast, map_natCast, map_zero, map_zero]
      exact h
  have hvc : Valued.v c ≠ 0 := (Valued.v : Valuation F_u ℤᵐ⁰).ne_zero_iff.mpr
    (ne_zero_of_pullbackDifferential_eq_smul_of_degree_ne_zero φ hc hdeg0)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_index_range_pointMapHom_mul_index_formalPointFiltration u hc h2 hn)
  set k₀ : ℕ := N + (WithZero.log (Valued.v c)).natAbs
  set j₀ : ℕ := ((k₀ : ℤ) - WithZero.log (Valued.v c)).toNat
  have hj₀ : (j₀ : ℤ) = (k₀ : ℤ) - WithZero.log (Valued.v c) := Int.toNat_of_nonneg (by omega)
  have hjk : Valued.v c * WithZero.exp ((j₀ + 1 : ℕ) : ℤ) = WithZero.exp ((k₀ + 1 : ℕ) : ℤ) := by
    rw [← WithZero.exp_log hvc, ← WithZero.exp_add]
    congr 1
    push_cast
    omega
  have hidx := hN (k₀ + 1) (by omega) (j₀ + 1) hjk
  rw [C₁.index_formalPointFiltration_eq_mul_tamagawaNumber u k₀,
    C₂.index_formalPointFiltration_eq_mul_tamagawaNumber u j₀] at hidx
  have hq : Nat.card (ResidueField O_u) = Nat.card 𝓀[F_u] :=
    Nat.card_congr
      (ResidueField.mapEquiv (u.integerEquivAdicCompletionIntegers (K := F)).symm).toEquiv
  have : IsMinimal 𝒪[F_u] (C₁.baseChange F_u) :=
    (isMinimal_integer_adicCompletion_iff u _).mpr inferInstance
  have : IsMinimal 𝒪[F_u] (C₂.baseChange F_u) :=
    (isMinimal_integer_adicCompletion_iff u _).mpr inferInstance
  have hm :
      Nat.card ((integralModel R_u (C₁.baseChange F_u)).map (residue R_u)).toAffine.Point =
        Nat.card ((integralModel R_u (C₂.baseChange F_u)).map (residue R_u)).toAffine.Point := by
    rw [natCard_point_reduction_adicCompletion u (C₁.baseChange F_u),
      natCard_point_reduction_adicCompletion u (C₂.baseChange F_u)]
    exact φ.natCard_point_reduction_eq
  have hequiv := ValuativeRel.isEquiv (ValuativeRel.valuation F_u) (Valued.v : Valuation F_u ℤᵐ⁰)
  rw [hq, hm, ← (C₁.baseChange F_u).tamagawaNumber_congr hequiv,
    ← (C₂.baseChange F_u).tamagawaNumber_congr hequiv] at hidx
  have hidxQ := congrArg (Nat.cast (R := ℚ)) hidx
  push_cast at hidxQ
  have : Finite (ResidueField R_u) := inferInstanceAs (Finite (ResidueField O_u))
  have hq0 : (Nat.card 𝓀[F_u] : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  set m : ℕ := Nat.card ((integralModel R_u (C₂.baseChange F_u)).map (residue R_u)).toAffine.Point
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have : Finite (Hom.ofIsogeny φ).pointMapHom.ker :=
    (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  have hker0 : (Nat.card (Hom.ofIsogeny φ).pointMapHom.ker : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hzpow : (Nat.card 𝓀[F_u] : ℚ) ^ WithZero.log (Valued.v c) * (Nat.card 𝓀[F_u] : ℚ) ^ j₀ =
      (Nat.card 𝓀[F_u] : ℚ) ^ k₀ := by
    rw [← zpow_natCast (Nat.card 𝓀[F_u] : ℚ) j₀, ← zpow_natCast (Nat.card 𝓀[F_u] : ℚ) k₀,
      ← zpow_add₀ hq0]
    congr 1
    omega
  refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero j₀ hq0) hm0) hker0) ?_
  rw [kummerRatio_def]
  calc
    _ = (((Hom.ofIsogeny φ).pointMapHom.range.index : ℚ) /
          Nat.card (Hom.ofIsogeny φ).pointMapHom.ker *
          Nat.card (Hom.ofIsogeny φ).pointMapHom.ker) *
        (((Nat.card 𝓀[F_u] : ℚ) ^ WithZero.log (Valued.v c) * (Nat.card 𝓀[F_u] : ℚ) ^ j₀) * m *
          (C₁.baseChange F_u).tamagawaNumber (ValuativeRel.valuation F_u)) := by ring
    _ = ((Hom.ofIsogeny φ).pointMapHom.range.index : ℚ) *
        ((Nat.card 𝓀[F_u] : ℚ) ^ k₀ * m *
          (C₁.baseChange F_u).tamagawaNumber (ValuativeRel.valuation F_u)) := by
        rw [div_mul_cancel₀ _ hker0, hzpow]
    _ = _ := by rw [hidxQ]; ring

/-- **The local Kummer ratio of an isogeny between arbitrary Weierstrass equations over an adic
completion.** If `C₁` and `C₂` carry `W₁` and `W₂` to minimal equations over `O_u`, then `c` is
replaced by `c · C₂.u / C₁.u`, the constant of `φ` read between those minimal models. -/
theorem zpow_log_valued_mul_tamagawaNumber_mul_kummerRatio
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F_u}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    {C₁ C₂ : VariableChange F_u} [IsMinimal O_u (C₁ • W₁)] [IsMinimal O_u (C₂ • W₂)]
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    (Nat.card 𝓀[F_u] : ℚ) ^ WithZero.log (Valued.v (c * C₂.u / C₁.u)) *
        W₁.tamagawaNumber (ValuativeRel.valuation F_u) * φ.kummerRatio =
      W₂.tamagawaNumber (ValuativeRel.valuation F_u) := by
  let ψ : Isogeny (C₁ • W₁).toAffine (C₂ • W₂).toAffine :=
    (variableChangeIsogeny C₂ (rfl : C₂ • W₂ = C₂ • W₂)).comp
      (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ W₁)))
  have hdeg : ψ.degree = φ.degree := by simp [ψ, degree_comp]
  have hkr : ψ.kummerRatio = φ.kummerRatio := by simp [ψ]
  have h := zpow_log_valued_mul_tamagawaNumber_mul_kummerRatio_of_isMinimal u ψ
    (pullbackDifferential_variableChangeIsogeny_comp_invariantDifferential φ hc C₁ C₂
      (inv_smul_smul C₁ W₁) rfl) h2 (hdeg ▸ hn)
  rwa [hkr, tamagawaNumber_smul, tamagawaNumber_smul] at h

end AdicCompletion

/-! ### Finite-place Kummer ratios over a Dedekind domain with finite quotients -/

section FinitePlace

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]

private local instance (v : HeightOneSpectrum R) : Finite (R ⧸ v.asIdeal) :=
  Ring.HasFiniteQuotients.finiteQuotient v.ne_bot

/-- In `ℝ`, `(absNorm v) ^ log(v c)` for `c ≠ 0` is the normalized `v`-adic absolute value
`NumberField.HeightOneSpectrum.adicAbv K v c`. -/
private theorem absNorm_zpow_log_valuation_eq_adicAbv (v : HeightOneSpectrum R) {c : K}
    (hc : c ≠ 0) :
    (Ideal.absNorm v.asIdeal : ℝ) ^ WithZero.log (v.valuation K c) =
      NumberField.HeightOneSpectrum.adicAbv K v c := by
  have hv : v.valuation K c ≠ 0 := (v.valuation K).ne_zero_iff.mpr hc
  rw [NumberField.HeightOneSpectrum.adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply (NumberField.HeightOneSpectrum.absNorm_ne_zero v) hv]
  push_cast
  rfl

private theorem finprod_cast_tamagawaNumberAt (E : WeierstrassCurve K) [E.IsElliptic] :
    (∏ᶠ v : HeightOneSpectrum R, (E.tamagawaNumberAt v : ℝ)) = E.tamagawaProduct (R := R) := by
  rw [E.tamagawaProduct_def]
  exact (((Nat.castRingHom ℝ).toMonoidHom).map_finprod_of_preimage_one
    (fun _ hx ↦ Nat.cast_injective (hx.trans Nat.cast_one.symm)) _).symm

omit [Ring.HasFiniteQuotients R] in
private theorem finprod_cast_finiteKummerRatio (φ : Isogeny E₁.toAffine E₂.toAffine) :
    (∏ᶠ v : HeightOneSpectrum R, (φ.finiteKummerRatio v : ℝ)) =
      ((∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v : ℚ) : ℝ) :=
  (((Rat.castHom ℝ).toMonoidHom).map_finprod_of_preimage_one
    (fun _ hx ↦ Rat.cast_injective (hx.trans Rat.cast_one.symm)) _).symm

/-- **Finite-place Kummer ratio between locally minimal equations (`ℚ`-valued).** -/
theorem zpow_log_valuation_mul_tamagawaNumberAt_mul_finiteKummerRatio_of_isMinimal
    (v : HeightOneSpectrum R) [IsMinimal (Localization.AtPrime v.asIdeal) E₁]
    [IsMinimal (Localization.AtPrime v.asIdeal) E₂] (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    (Ideal.absNorm v.asIdeal : ℚ) ^ WithZero.log (v.valuation K c) *
        E₁.tamagawaNumberAt v * φ.finiteKummerRatio v =
      E₂.tamagawaNumberAt v := by
  have h2' : (2 : v.adicCompletion K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]
    exact (algebraMap K (v.adicCompletion K)).injective.ne h2
  have hdeg : ((φ.baseChange (v.adicCompletion K)).degree : R) ≠ 0 := by
    change ((φ.map (algebraMap K (v.adicCompletion K))).degree : R) ≠ 0
    rwa [degree_map]
  have h := zpow_log_valued_mul_tamagawaNumber_mul_kummerRatio_of_isMinimal v
    (W₁ := E₁.baseChange (v.adicCompletion K)) (W₂ := E₂.baseChange (v.adicCompletion K))
    (φ.baseChange (v.adicCompletion K))
    (map_pullbackDifferential_invariantDifferential_eq_smul φ
      (algebraMap K (v.adicCompletion K)) hc) h2' hdeg
  have hvc : Valued.v (algebraMap K (v.adicCompletion K) c) = v.valuation K c := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, HeightOneSpectrum.adicCompletion.valued_coe]
  rw [v.natCard_residueField_adicCompletion_eq_absNorm, hvc, ← tamagawaNumberAt_def,
    ← tamagawaNumberAt_def] at h
  rwa [finiteKummerRatio_def]

/-- **Finite-place Kummer ratio with local minimalizing changes of variables (`ℚ`-valued).** -/
theorem zpow_log_valuation_mul_tamagawaNumberAt_mul_finiteKummerRatio
    (v : HeightOneSpectrum R) (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange K} [IsMinimal (Localization.AtPrime v.asIdeal) (C₁ • E₁)]
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₂ • E₂)]
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    (Ideal.absNorm v.asIdeal : ℚ) ^ WithZero.log (v.valuation K (c * C₂.u / C₁.u)) *
        E₁.tamagawaNumberAt v * φ.finiteKummerRatio v =
      E₂.tamagawaNumberAt v := by
  let ψ : Isogeny (C₁ • E₁).toAffine (C₂ • E₂).toAffine :=
    (variableChangeIsogeny C₂ (rfl : C₂ • E₂ = C₂ • E₂)).comp
      (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ E₁)))
  have hdeg : ψ.degree = φ.degree := by simp [ψ, degree_comp]
  have hkr : ψ.finiteKummerRatio v = φ.finiteKummerRatio v := by simp [ψ]
  have h := zpow_log_valuation_mul_tamagawaNumberAt_mul_finiteKummerRatio_of_isMinimal v ψ
    (pullbackDifferential_variableChangeIsogeny_comp_invariantDifferential φ hc C₁ C₂
      (inv_smul_smul C₁ E₁) rfl) h2
    (hdeg ▸ hφ)
  rwa [hkr, tamagawaNumberAt_smul, tamagawaNumberAt_smul] at h

/-- **Finite-place Kummer ratio in terms of `adicAbv` (`ℝ`-valued).** -/
theorem adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio
    (v : HeightOneSpectrum R) (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange K} [IsMinimal (Localization.AtPrime v.asIdeal) (C₁ • E₁)]
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₂ • E₂)]
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv K v (c * C₂.u / C₁.u) *
        E₁.tamagawaNumberAt v * (φ.finiteKummerRatio v : ℝ) =
      E₂.tamagawaNumberAt v := by
  have hdeg0 : (φ.degree : K) ≠ 0 := fun h ↦ hφ <| IsFractionRing.injective R K <| by
    rw [map_natCast, map_zero]
    exact h
  have hc0 := ne_zero_of_pullbackDifferential_eq_smul_of_degree_ne_zero φ hc hdeg0
  have hc'0 : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have h := congrArg (Rat.cast (K := ℝ))
    (zpow_log_valuation_mul_tamagawaNumberAt_mul_finiteKummerRatio v φ hc
      (C₁ := C₁) (C₂ := C₂) h2 hφ)
  push_cast at h
  rwa [absNorm_zpow_log_valuation_eq_adicAbv v hc'0] at h

/-- **Finite-place Kummer ratio between locally minimal equations (`ℝ`-valued).** -/
theorem adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio_of_isMinimal
    (v : HeightOneSpectrum R) [IsMinimal (Localization.AtPrime v.asIdeal) E₁]
    [IsMinimal (Localization.AtPrime v.asIdeal) E₂] (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv K v c *
        E₁.tamagawaNumberAt v * (φ.finiteKummerRatio v : ℝ) =
      E₂.tamagawaNumberAt v := by
  have : IsMinimal (Localization.AtPrime v.asIdeal) ((1 : VariableChange K) • E₁) := by
    rwa [one_smul]
  have : IsMinimal (Localization.AtPrime v.asIdeal) ((1 : VariableChange K) • E₂) := by
    rwa [one_smul]
  simpa using adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio v φ hc
    (C₁ := 1) (C₂ := 1) h2 hφ

/-- **Finite-place Kummer ratio for arbitrary equations via local obstruction exponents.** No
choice of local minimalizing changes of variables appears in the statement: the local scaling ratio
`v(C₂.u / C₁.u)` is canonically recorded by `obstructionExponentAt R v E₁ -
obstructionExponentAt R v E₂`. -/
theorem adicAbv_mul_zpow_obstructionExponentAt_mul_tamagawaNumberAt_mul_finiteKummerRatio
    (v : HeightOneSpectrum R) (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv K v c *
        (Ideal.absNorm v.asIdeal : ℝ) ^
          (obstructionExponentAt R v E₁ - obstructionExponentAt R v E₂) *
        E₁.tamagawaNumberAt v * (φ.finiteKummerRatio v : ℝ) =
      E₂.tamagawaNumberAt v := by
  obtain ⟨C₁, hC₁⟩ := E₁.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal)
  obtain ⟨C₂, hC₂⟩ := E₂.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal)
  have hmin₁ : IsMinimal (Localization.AtPrime v.asIdeal) (C₁ • E₁) := hC₁.symm ▸ inferInstance
  have hmin₂ : IsMinimal (Localization.AtPrime v.asIdeal) (C₂ • E₂) := hC₂.symm ▸ inferInstance
  have hord₁ : (v.valuation K).ord (C₁.u : K) = obstructionExponentAt R v E₁ := by
    have h0 := (obstructionExponentAt_eq_zero_iff_isMinimal R v (C₁ • E₁)).mpr hmin₁
    rw [obstructionExponentAt_smul] at h0
    omega
  have hord₂ : (v.valuation K).ord (C₂.u : K) = obstructionExponentAt R v E₂ := by
    have h0 := (obstructionExponentAt_eq_zero_iff_isMinimal R v (C₂ • E₂)).mpr hmin₂
    rw [obstructionExponentAt_smul] at h0
    omega
  have hlog (u : Kˣ) :
      NumberField.HeightOneSpectrum.adicAbv K v (u : K) =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-(v.valuation K).ord (u : K)) := by
    rw [← absNorm_zpow_log_valuation_eq_adicAbv v u.ne_zero, Valuation.ord_def, neg_neg]
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have h := adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio v φ hc
    (C₁ := C₁) (C₂ := C₂) h2 hφ
  rw [map_div₀, map_mul, mul_div_assoc, hlog C₁.u, hlog C₂.u, hord₁, hord₂, ← zpow_sub₀ hq0,
    neg_sub_neg] at h
  exact h

end FinitePlace

/-! ### Finite-place product over a number field -/

section NumberField

variable {K : Type*} [Field K] [NumberField K]
  {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]

private theorem hasFiniteMulSupport_adicAbv {c : K} (hc : c ≠ 0) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦
      NumberField.HeightOneSpectrum.adicAbv K v c).HasFiniteMulSupport := by
  have heq : (fun v : HeightOneSpectrum (𝓞 K) ↦ NumberField.HeightOneSpectrum.adicAbv K v c) =
      (fun w : NumberField.FinitePlace K ↦ w c) ∘
        NumberField.FinitePlace.equivHeightOneSpectrum.symm := by
    ext v
    simp [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply,
      NumberField.FinitePlace.norm_embedding]
  rw [heq]
  exact Function.HasFiniteMulSupport.comp_of_injective
    NumberField.FinitePlace.equivHeightOneSpectrum.symm.injective
    (NumberField.FinitePlace.hasFiniteMulSupport hc)

private theorem finprod_adicAbv_eq_inv_abs_norm {c : K} (hc : c ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), NumberField.HeightOneSpectrum.adicAbv K v c) =
      (|(Algebra.norm ℚ c : ℝ)|)⁻¹ := by
  rw [← Rat.cast_abs, ← Rat.cast_inv, ← NumberField.FinitePlace.prod_eq_inv_abs_norm hc,
    ← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm]
  exact finprod_congr fun v ↦ by
    rw [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply,
      NumberField.FinitePlace.norm_embedding]

/-- The absolute norm of the Weierstrass defect ideal is the finite product of the local defect
powers `(absNorm v) ^ f_v(E)`. -/
private theorem absNorm_weierstrassDefectIdeal (E : WeierstrassCurve K) [E.IsElliptic]
    [IsIntegral (𝓞 K) E] :
    (Ideal.absNorm (weierstrassDefectIdeal (𝓞 K) E) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (Ideal.absNorm v.asIdeal : ℝ) ^ (obstructionExponentAt (𝓞 K) v E).toNat := by
  rw [weierstrassDefectIdeal_def]
  have hmap := ((Nat.castRingHom ℝ).toMonoidHom.comp
    Ideal.absNorm.toMonoidHom).map_finprod_of_preimage_one
      (by simp [Ideal.absNorm_eq_one_iff])
      (fun v : HeightOneSpectrum (𝓞 K) ↦
        v.asIdeal ^ (obstructionExponentAt (𝓞 K) v E).toNat)
  simpa using hmap

/-- Local cleared-denominator form of the finite-place Kummer-ratio identity for integral
equations over `𝓞 K`. -/
private theorem adicAbv_mul_absNorm_pow_obstructionExponentAt_toNat
    [IsIntegral (𝓞 K) E₁] [IsIntegral (𝓞 K) E₂]
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.HeightOneSpectrum.adicAbv K v c *
        ((Ideal.absNorm v.asIdeal : ℝ) ^ (obstructionExponentAt (𝓞 K) v E₁).toNat *
          E₁.tamagawaNumberAt v * (φ.finiteKummerRatio v : ℝ)) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (obstructionExponentAt (𝓞 K) v E₂).toNat *
        E₂.tamagawaNumberAt v := by
  have : IsIntegral (Localization.AtPrime v.asIdeal) E₁ :=
    IsIntegral.of_isScalarTower (R := 𝓞 K) E₁
  have : IsIntegral (Localization.AtPrime v.asIdeal) E₂ :=
    IsIntegral.of_isScalarTower (R := 𝓞 K) E₂
  have hf₁ : ((obstructionExponentAt (𝓞 K) v E₁).toNat : ℤ) =
      obstructionExponentAt (𝓞 K) v E₁ :=
    Int.toNat_of_nonneg (obstructionExponentAt_nonneg_of_isIntegral (𝓞 K) v E₁)
  have hf₂ : ((obstructionExponentAt (𝓞 K) v E₂).toNat : ℤ) =
      obstructionExponentAt (𝓞 K) v E₂ :=
    Int.toNat_of_nonneg (obstructionExponentAt_nonneg_of_isIntegral (𝓞 K) v E₂)
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hv := adicAbv_mul_zpow_obstructionExponentAt_mul_tamagawaNumberAt_mul_finiteKummerRatio
    v φ hc two_ne_zero (Nat.cast_ne_zero.mpr φ.degree_pos.ne')
  rw [← hf₁, ← hf₂, zpow_sub₀ hq0, zpow_natCast, zpow_natCast] at hv
  have hd0 : (Ideal.absNorm v.asIdeal : ℝ) ^ (obstructionExponentAt (𝓞 K) v E₂).toNat ≠ 0 :=
    pow_ne_zero _ hq0
  calc
    _ = (NumberField.HeightOneSpectrum.adicAbv K v c *
          ((Ideal.absNorm v.asIdeal : ℝ) ^ (obstructionExponentAt (𝓞 K) v E₁).toNat /
            (Ideal.absNorm v.asIdeal : ℝ) ^ (obstructionExponentAt (𝓞 K) v E₂).toNat) *
          E₁.tamagawaNumberAt v * (φ.finiteKummerRatio v : ℝ)) *
        (Ideal.absNorm v.asIdeal : ℝ) ^ (obstructionExponentAt (𝓞 K) v E₂).toNat := by
      field_simp [hd0]
    _ = _ := by rw [hv, mul_comm]

/-- **Finite-place Kummer-ratio product over a number field of arbitrary class number.** For any
isogeny `φ : E₁ → E₂` between integral elliptic curves over `𝓞 K` pulling the invariant
differential back as `φ^*ω₂ = c ω₁`,

`(∏ᶠ v, finiteKummerRatio φ v) · N(𝔍_{E₁}) · ∏_v c_v(E₁) = |N_{K/ℚ}(c)| · N(𝔍_{E₂}) · ∏_v c_v(E₂)`.
-/
theorem finprod_finiteKummerRatio_mul_absNorm_weierstrassDefectIdeal_mul_tamagawaProduct
    [IsIntegral (𝓞 K) E₁] [IsIntegral (𝓞 K) E₂]
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), φ.finiteKummerRatio v) *
        Ideal.absNorm (weierstrassDefectIdeal (𝓞 K) E₁) * E₁.tamagawaProduct (R := 𝓞 K) =
      |Algebra.norm ℚ c| *
        Ideal.absNorm (weierstrassDefectIdeal (𝓞 K) E₂) * E₂.tamagawaProduct (R := 𝓞 K) := by
  have hc0 : c ≠ 0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  have hdegK : (φ.degree : K) ≠ 0 := Nat.cast_ne_zero.mpr φ.degree_pos.ne'
  have hsup_def (E : WeierstrassCurve K) [E.IsElliptic] [IsIntegral (𝓞 K) E] :
      (fun v : HeightOneSpectrum (𝓞 K) ↦
        (Ideal.absNorm v.asIdeal : ℝ) ^
          (obstructionExponentAt (𝓞 K) v E).toNat).HasFiniteMulSupport := by
    have heq : (fun v : HeightOneSpectrum (𝓞 K) ↦
        (Ideal.absNorm v.asIdeal : ℝ) ^ (obstructionExponentAt (𝓞 K) v E).toNat) =
        fun v ↦ (Ideal.absNorm (v.asIdeal ^ (obstructionExponentAt (𝓞 K) v E).toNat) : ℝ) := by
      ext v
      rw [map_pow, Nat.cast_pow]
    rw [heq]
    exact Function.HasFiniteMulSupport.fun_comp
      (g := fun I : Ideal (𝓞 K) ↦ (Ideal.absNorm I : ℝ))
      (hasFiniteMulSupport_pow_obstructionExponentAt_toNat (𝓞 K) E) (by simp)
  have hsup_tam (E : WeierstrassCurve K) [E.IsElliptic] :
      (fun v : HeightOneSpectrum (𝓞 K) ↦ (E.tamagawaNumberAt v : ℝ)).HasFiniteMulSupport :=
    Function.HasFiniteMulSupport.fun_comp
      (E.hasFiniteMulSupport_tamagawaNumberAt (R := 𝓞 K)) Nat.cast_one
  have hsup_kr :
      (fun v : HeightOneSpectrum (𝓞 K) ↦ (φ.finiteKummerRatio v : ℝ)).HasFiniteMulSupport :=
    Function.HasFiniteMulSupport.fun_comp
      (φ.hasFiniteMulSupport_finiteKummerRatio (R := 𝓞 K) hdegK) Rat.cast_one
  have hprod := finprod_congr (adicAbv_mul_absNorm_pow_obstructionExponentAt_toNat φ hc)
  rw [finprod_mul_distrib (hasFiniteMulSupport_adicAbv hc0)
        (Function.HasFiniteMulSupport.fun_mul
          (Function.HasFiniteMulSupport.fun_mul (hsup_def E₁) (hsup_tam E₁)) hsup_kr),
    finprod_mul_distrib (Function.HasFiniteMulSupport.fun_mul (hsup_def E₁) (hsup_tam E₁))
      hsup_kr,
    finprod_mul_distrib (hsup_def E₁) (hsup_tam E₁),
    finprod_mul_distrib (hsup_def E₂) (hsup_tam E₂),
    finprod_adicAbv_eq_inv_abs_norm hc0, ← absNorm_weierstrassDefectIdeal E₁,
    ← absNorm_weierstrassDefectIdeal E₂, finprod_cast_tamagawaNumberAt E₁,
    finprod_cast_tamagawaNumberAt E₂, finprod_cast_finiteKummerRatio φ] at hprod
  have hnorm0 : |(Algebra.norm ℚ c : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hc0))
  apply Rat.cast_injective (α := ℝ)
  push_cast
  calc
    _ = |(Algebra.norm ℚ c : ℝ)| * (|(Algebra.norm ℚ c : ℝ)|⁻¹ *
          (Ideal.absNorm (weierstrassDefectIdeal (𝓞 K) E₁) *
            E₁.tamagawaProduct (R := 𝓞 K) *
            ((∏ᶠ v : HeightOneSpectrum (𝓞 K), φ.finiteKummerRatio v : ℚ) : ℝ))) := by
        field_simp [hnorm0]
    _ = _ := by rw [hprod]; ring

/-- **Finite-place Kummer-ratio product between globally minimal equations over a number field.** -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal (𝓞 K) E₁) (h₂ : IsGlobalMinimal (𝓞 K) E₂) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := 𝓞 K) =
      |Algebra.norm ℚ c| * E₂.tamagawaProduct (R := 𝓞 K) := by
  have := h₁.isIntegral
  have := h₂.isIntegral
  have hd₁ : weierstrassDefectIdeal (𝓞 K) E₁ = ⊤ :=
    (weierstrassDefectIdeal_eq_top_iff_isGlobalMinimal E₁).mpr h₁
  have hd₂ : weierstrassDefectIdeal (𝓞 K) E₂ = ⊤ :=
    (weierstrassDefectIdeal_eq_top_iff_isGlobalMinimal E₂).mpr h₂
  simpa [hd₁, hd₂] using
    finprod_finiteKummerRatio_mul_absNorm_weierstrassDefectIdeal_mul_tamagawaProduct φ hc

/-- **Finite-place Kummer-ratio product over a number field via global minimalizing changes of
variables.** -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange K} (hC₁ : IsGlobalMinimal (𝓞 K) (C₁ • E₁))
    (hC₂ : IsGlobalMinimal (𝓞 K) (C₂ • E₂)) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := 𝓞 K) =
      |Algebra.norm ℚ (c * C₂.u / C₁.u)| * E₂.tamagawaProduct (R := 𝓞 K) := by
  let ψ : Isogeny (C₁ • E₁).toAffine (C₂ • E₂).toAffine :=
    (variableChangeIsogeny C₂ (rfl : C₂ • E₂ = C₂ • E₂)).comp
      (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ E₁)))
  have hkr : (fun v : HeightOneSpectrum (𝓞 K) ↦ ψ.finiteKummerRatio v) =
      (fun v ↦ φ.finiteKummerRatio v) := by
    ext v
    simp [ψ]
  have h := finprod_finiteKummerRatio_mul_tamagawaProduct_of_isGlobalMinimal ψ
    (pullbackDifferential_variableChangeIsogeny_comp_invariantDifferential φ hc C₁ C₂
      (inv_smul_smul C₁ E₁) rfl) hC₁ hC₂
  rwa [hkr, tamagawaProduct_smul, tamagawaProduct_smul] at h

end NumberField

/-! ### Global Kummer-ratio, period, and Tamagawa formulas over `ℚ` -/

section Rational

/-- Transporting `adicAbv ℚ` along `Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ` preserves every local
absolute value on `ℚ`. -/
private theorem adicAbv_equivOfRingEquiv_ringOfIntegersEquiv
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) :
    NumberField.HeightOneSpectrum.adicAbv ℚ
        (HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv v) x =
      NumberField.HeightOneSpectrum.adicAbv ℚ v x := by
  set e := Rat.ringOfIntegersEquiv
  set w := HeightOneSpectrum.equivOfRingEquiv e v
  have hvw : w.asIdeal = Ideal.map e v.asIdeal :=
    HeightOneSpectrum.asIdeal_equivOfRingEquiv e v
  have hnorm : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal :=
    hvw ▸ Ideal.absNorm_map_of_ringEquiv e v.asIdeal
  have hval : w.valuation ℚ x = v.valuation ℚ x := by
    have hσ : IsFractionRing.ringEquivOfRingEquiv (K := ℚ) (L := ℚ) e x = x :=
      RingHom.congr_fun
        (Subsingleton.elim (IsFractionRing.ringEquivOfRingEquiv (K := ℚ) (L := ℚ) e).toRingHom
          (RingHom.id ℚ)) x
    simpa only [hσ] using
      HeightOneSpectrum.valuation_ringEquivOfRingEquiv (K := ℚ) (K' := ℚ) e hvw x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← absNorm_zpow_log_valuation_eq_adicAbv (R := ℤ) w hx,
      ← absNorm_zpow_log_valuation_eq_adicAbv (R := 𝓞 ℚ) v hx, hnorm, hval]

private theorem hasFiniteMulSupport_adicAbv_rat {c : ℚ} (hc : c ≠ 0) :
    (fun v : HeightOneSpectrum ℤ ↦
      NumberField.HeightOneSpectrum.adicAbv ℚ v c).HasFiniteMulSupport := by
  let ev := HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv
  have heq : (fun v : HeightOneSpectrum ℤ ↦ NumberField.HeightOneSpectrum.adicAbv ℚ v c) =
      (fun v : HeightOneSpectrum (𝓞 ℚ) ↦ NumberField.HeightOneSpectrum.adicAbv ℚ v c) ∘
        ev.symm := by
    ext v
    rw [Function.comp_apply, ← adicAbv_equivOfRingEquiv_ringOfIntegersEquiv (ev.symm v) c,
      ev.apply_symm_apply]
  rw [heq]
  exact Function.HasFiniteMulSupport.comp_of_injective ev.symm.injective
    (hasFiniteMulSupport_adicAbv hc)

/-- The product of the `p`-adic absolute values over `HeightOneSpectrum ℤ` of a nonzero rational
number `c` is `|c|⁻¹`. -/
private theorem finprod_adicAbv_rat {c : ℚ} (hc : c ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum ℤ, NumberField.HeightOneSpectrum.adicAbv ℚ v c) = |(c : ℝ)|⁻¹ := by
  rw [← finprod_comp_equiv (HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv),
    show (fun v : HeightOneSpectrum (𝓞 ℚ) ↦
        NumberField.HeightOneSpectrum.adicAbv ℚ
          (HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv v) c) =
      fun v ↦ NumberField.HeightOneSpectrum.adicAbv ℚ v c by
      ext v
      exact adicAbv_equivOfRingEquiv_ringOfIntegersEquiv v c,
    finprod_adicAbv_eq_inv_abs_norm hc, Algebra.norm_self, MonoidHom.id_apply]

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **The real-place Kummer ratio and the minimal real period over `ℚ`.** If `φ^*ω₂ = c ω₁` and
`C₁`, `C₂` carry `E₁`, `E₂` to global minimal equations over `ℤ`, then
`|c · C₂.u / C₁.u| · Ω(E₁) · realKummerRatio φ = Ω(E₂)`. -/
theorem abs_mul_minimalRealPeriod_mul_realKummerRatio
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod * (φ.realKummerRatio : ℝ) =
      E₂.minimalRealPeriod := by
  classical
  have h := abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul φ hc hC₁ hC₂
  have : Finite (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker :=
    (Hom.ofIsogeny (φ.baseChange ℝ)).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have hker0 : (Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hkr : (φ.realKummerRatio : ℝ) =
      (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index /
        Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker := by
    rw [realKummerRatio_def, ← baseChange, kummerRatio_def]
    push_cast
    rfl
  rw [hkr]
  exact mul_right_cancel₀ hker0 <| by
    calc
      _ = |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod *
            (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index := by
          field_simp [hker0]
      _ = _ := by rw [h, mul_comm]

/-- **The real-place Kummer ratio between global minimal equations over `ℚ`.** -/
theorem abs_mul_minimalRealPeriod_mul_realKummerRatio_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    |(c : ℝ)| * E₁.minimalRealPeriod * (φ.realKummerRatio : ℝ) = E₂.minimalRealPeriod := by
  simpa using abs_mul_minimalRealPeriod_mul_realKummerRatio φ hc (C₁ := 1) (C₂ := 1)
    (by simpa using h₁) (by simpa using h₂)

/-- **Finite-place Kummer-ratio product over `ℤ` for elliptic curves over `ℚ`.** -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_rat
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    (∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := ℤ) =
      |c * C₂.u / C₁.u| * E₂.tamagawaProduct (R := ℤ) := by
  have hc0 : c ≠ 0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  set c' : ℚ := c * C₂.u / C₁.u
  have hc'0 : c' ≠ 0 := div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have hdegZ : (φ.degree : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr φ.degree_pos.ne'
  have hloc (v : HeightOneSpectrum ℤ) :
      NumberField.HeightOneSpectrum.adicAbv ℚ v c' *
        ((E₁.tamagawaNumberAt v : ℝ) * (φ.finiteKummerRatio v : ℝ)) =
      E₂.tamagawaNumberAt v := by
    have := hC₁.isMinimal v
    have := hC₂.isMinimal v
    simpa only [mul_assoc] using adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio v φ hc
      (C₁ := C₁) (C₂ := C₂) two_ne_zero hdegZ
  have hsup_tam₁ :
      (fun v : HeightOneSpectrum ℤ ↦ (E₁.tamagawaNumberAt v : ℝ)).HasFiniteMulSupport :=
    Function.HasFiniteMulSupport.fun_comp
      (E₁.hasFiniteMulSupport_tamagawaNumberAt (R := ℤ)) Nat.cast_one
  have hsup_kr :
      (fun v : HeightOneSpectrum ℤ ↦ (φ.finiteKummerRatio v : ℝ)).HasFiniteMulSupport :=
    Function.HasFiniteMulSupport.fun_comp
      φ.hasFiniteMulSupport_finiteKummerRatio_rat Rat.cast_one
  have hprod := finprod_congr hloc
  rw [finprod_mul_distrib (hasFiniteMulSupport_adicAbv_rat hc'0)
        (Function.HasFiniteMulSupport.fun_mul hsup_tam₁ hsup_kr),
    finprod_mul_distrib hsup_tam₁ hsup_kr, finprod_adicAbv_rat hc'0,
    finprod_cast_tamagawaNumberAt E₁, finprod_cast_tamagawaNumberAt E₂,
    finprod_cast_finiteKummerRatio φ] at hprod
  have habs0 : |(c' : ℝ)| ≠ 0 := abs_ne_zero.mpr (Rat.cast_ne_zero.mpr hc'0)
  apply Rat.cast_injective (α := ℝ)
  push_cast
  change ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ) *
      E₁.tamagawaProduct (R := ℤ) = |(c' : ℝ)| * E₂.tamagawaProduct (R := ℤ)
  calc
    _ = |(c' : ℝ)| * (|(c' : ℝ)|⁻¹ * (E₁.tamagawaProduct (R := ℤ) *
          ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ))) := by
        field_simp [habs0]
    _ = |(c' : ℝ)| * E₂.tamagawaProduct (R := ℤ) := by rw [hprod]

/-- **Finite-place Kummer-ratio product between global minimal equations over `ℚ`.** -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_rat_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    (∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := ℤ) =
      |c| * E₂.tamagawaProduct (R := ℤ) := by
  simpa using finprod_finiteKummerRatio_mul_tamagawaProduct_rat φ hc (C₁ := 1) (C₂ := 1)
    (by simpa using h₁) (by simpa using h₂)

/-- **Cassels' period–Tamagawa–Kummer product formula over `ℚ`.** For every isogeny `φ : E₁ → E₂`
of elliptic curves over `ℚ`, the product of local Kummer ratios over the real place and all finite
primes transforms `Ω(E₁) · ∏_p c_p(E₁)` into `Ω(E₂) · ∏_p c_p(E₂)`:

`kummerRatioProduct φ · (Ω(E₁) · ∏_p c_p(E₁)) = Ω(E₂) · ∏_p c_p(E₂)`. -/
theorem kummerRatioProduct_mul_minimalRealPeriod_mul_tamagawaProduct
    (φ : Isogeny E₁.toAffine E₂.toAffine) :
    (φ.kummerRatioProduct : ℝ) * (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ)) =
      E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  obtain ⟨C₁, hC₁⟩ := E₁.exists_isGlobalMinimal_smul (O := ℤ)
  obtain ⟨C₂, hC₂⟩ := E₂.exists_isGlobalMinimal_smul (O := ℤ)
  have hc0 : c ≠ 0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  set c' : ℚ := c * C₂.u / C₁.u
  have habs0 : |(c' : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr
      (div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero))
  have hreal : |(c' : ℝ)| * E₁.minimalRealPeriod * (φ.realKummerRatio : ℝ) =
      E₂.minimalRealPeriod :=
    abs_mul_minimalRealPeriod_mul_realKummerRatio φ hc hC₁ hC₂
  have hfin : ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ) *
      E₁.tamagawaProduct (R := ℤ) = |(c' : ℝ)| * E₂.tamagawaProduct (R := ℤ) := by
    have h := congrArg (Rat.cast (K := ℝ))
      (finprod_finiteKummerRatio_mul_tamagawaProduct_rat φ hc hC₁ hC₂)
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs] using h
  rw [kummerRatioProduct_def, Rat.cast_mul]
  calc
    _ = (|(c' : ℝ)| * E₁.minimalRealPeriod * (φ.realKummerRatio : ℝ)) *
          (((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ) *
            E₁.tamagawaProduct (R := ℤ)) / |(c' : ℝ)| := by
        field_simp [habs0]
    _ = (E₂.minimalRealPeriod * (|(c' : ℝ)| * E₂.tamagawaProduct (R := ℤ))) / |(c' : ℝ)| := by
        rw [hreal, hfin]
    _ = E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by
        field_simp [habs0]

/-- **The global Kummer-ratio product over `ℚ` as the ratio of period–Tamagawa products.** -/
theorem cast_kummerRatioProduct (φ : Isogeny E₁.toAffine E₂.toAffine) :
    (φ.kummerRatioProduct : ℝ) =
      (E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ)) /
        (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ)) := by
  have hd : E₁.minimalRealPeriod * (E₁.tamagawaProduct (R := ℤ) : ℝ) ≠ 0 :=
    mul_ne_zero E₁.minimalRealPeriod_pos.ne'
      (Nat.cast_ne_zero.mpr (E₁.tamagawaProduct_pos (R := ℤ)).ne')
  exact eq_div_of_mul_eq hd (kummerRatioProduct_mul_minimalRealPeriod_mul_tamagawaProduct φ)

/-- **Two isogenies between the same elliptic curves over `ℚ` have the same global Kummer-ratio
product.** -/
theorem kummerRatioProduct_eq (φ ψ : Isogeny E₁.toAffine E₂.toAffine) :
    φ.kummerRatioProduct = ψ.kummerRatioProduct :=
  Rat.cast_injective (α := ℝ) ((cast_kummerRatioProduct φ).trans (cast_kummerRatioProduct ψ).symm)

/-- **Every endomorphism isogeny of an elliptic curve over `ℚ` has global Kummer-ratio product
equal to `1`.** -/
theorem kummerRatioProduct_self {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (φ : Isogeny E.toAffine E.toAffine) :
    φ.kummerRatioProduct = 1 :=
  (kummerRatioProduct_eq φ (Isogeny.id E.toAffine)).trans (kummerRatioProduct_id E)

/-- **The global Kummer-ratio products of an isogeny over `ℚ` and its dual multiply to `1`.** -/
@[simp]
theorem kummerRatioProduct_mul_dual (φ : Isogeny E₁.toAffine E₂.toAffine) :
    φ.kummerRatioProduct * φ.dual.kummerRatioProduct = 1 := by
  rw [← kummerRatioProduct_comp]
  exact kummerRatioProduct_self (φ.comp φ.dual)

/-- **The global Kummer-ratio product of the dual isogeny over `ℚ` is the inverse of that of `φ`.**
-/
theorem kummerRatioProduct_dual (φ : Isogeny E₁.toAffine E₂.toAffine) :
    φ.dual.kummerRatioProduct = (φ.kummerRatioProduct)⁻¹ :=
  eq_inv_of_mul_eq_one_right
    (mul_comm φ.kummerRatioProduct φ.dual.kummerRatioProduct ▸ kummerRatioProduct_mul_dual φ)

end Rational

end TauCeti.Isogeny

end
