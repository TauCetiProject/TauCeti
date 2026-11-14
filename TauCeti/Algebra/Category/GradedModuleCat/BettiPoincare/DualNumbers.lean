/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DualNumber
public import TauCeti.Algebra.Category.GradedModuleCat.BettiPoincare.Connected
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Coordinate
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Resolution
public import TauCeti.Algebra.DualNumber.Basic
public import TauCeti.Algebra.DualNumber.Grading
public import TauCeti.RingTheory.PowerSeries.Geometric

/-!
# Betti Poincaré series of the residue module over linearly graded dual numbers

Let `k` be a commutative ring and equip the dual numbers `A = k[ε]` (`ε² = 0`) with the degree-one
grading `TauCeti.dualNumberLinearIntegerGrade` (`deg ε = 1`, modelling the exterior algebra on one
degree-one generator). Multiplication by `ε` shifts internal degrees by `1`, giving the infinite
`ε`-periodic minimal graded free resolution

```text
⋯ ⟶ A{2} --ε--> A{1} --ε--> A ⟶ S ⟶ 0
```

of the graded residue module `S = A / (ε)`, concentrated in degree zero. Every `n`th term `A{n}` is
generated in internal degree `n`, so this resolution is **linear** (`IsLinear`) as well as minimal.

Over a field `k`, expanding in the regular projective basis `[A]` of `K₀^gr(proj A)` gives the
Betti Poincaré formal power series

```text
B(S; q, t) = ∑_{n ≥ 0} qⁿ tⁿ = (1 - q t)⁻¹ ∈ (ℤ[q, q⁻¹])⟦t⟧.
```

Its bidegree coefficients equal `1` along the diagonal `d = n` and vanish for `d ≠ n`, witnessing
Koszul linearity of `S`, while infinitely many nonzero terms make `B(S; q, t)` a genuine formal
power series not arising from any polynomial in `t`. Correspondingly, `S` admits no finite
resolution by finite graded projectives: the graded Cartan image of `[A]` has graded dimension
`1 + q`, which is not a unit in `ℤ[q, q⁻¹]`.

## Main definitions

* `TauCeti.dualNumberLinearResidue`: the graded residue module `S = k[ε] / (ε)` in
  `GradedModuleCat (dualNumberLinearIntegerGrade k)`.
* `TauCeti.dualNumberLinearResolution`: the `ε`-periodic linear minimal graded projective
  resolution `⋯ ⟶ A{2} ⟶ A{1} ⟶ A ⟶ S ⟶ 0`.
* `TauCeti.dualNumberLinearRegularProjectiveBasis`: the `Unit`-indexed basis `[A]` of
  `K₀^gr(proj A)` over a field `k`.

## Main results

* `TauCeti.isLinear_dualNumberLinearResolution` and `TauCeti.isMinimal_dualNumberLinearResolution`:
  the periodic resolution is both linear and minimal.
* `TauCeti.coeff_bettiPoincarePowerSeries_dualNumberLinearResolution` and
  `TauCeti.bettiPoincarePowerSeries_dualNumberLinearResolution_mul_one_sub`:
  `B(S; q, t) = ∑_{n ≥ 0} qⁿ tⁿ` satisfies `B(S; q, t) * (1 - q t) = 1`.
* `TauCeti.coeff_coeff_bettiPoincarePowerSeries_dualNumberLinearResolution`: diagonal bidegree
  support `(d = n ? 1 : 0)`.
* `TauCeti.not_exists_polynomial_bettiPoincarePowerSeries_dualNumberLinearResolution`: `B(S; q, t)`
  is not a polynomial in `t`.
* `TauCeti.not_admitsFiniteResolution_dualNumberLinearResidue`: `S` admits no finite resolution by
  finite graded projectives.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial TrivSqZeroExt DualNumber
open scoped Pointwise

universe u

attribute [local instance] dualNumberLinearIntegerGradedAlgebra

section CommRing

variable (k : Type u) [CommRing k]

/-- **The graded residue module `S = k[ε] / (ε)`** over the dual numbers with `deg ε = 1`,
concentrated in degree zero. -/
abbrev dualNumberLinearResidue : GradedModuleCat.{u} (dualNumberLinearIntegerGrade k) :=
  gradedConnectedResidue (dualNumberLinearIntegerGrade k)

/-- The positive-degree ideal `A₊` in `TauCeti.dualNumberLinearIntegerGrade` consists of dual
numbers with zero scalar coordinate. -/
private theorem mem_gradedPositiveMulIdeal_linear_one_iff {x : DualNumber k} :
    x ∈ gradedPositiveMulIdeal (dualNumberLinearIntegerGrade k) 1 ↔ fst x = 0 := by
  constructor
  · intro hx
    have hle : gradedPositiveMulIdeal (dualNumberLinearIntegerGrade k) 1 ≤
        RingHom.ker (TrivSqZeroExt.fstHom k k k) := by
      refine (gradedPositiveMulIdeal_le_iff _).2 fun p hp y hy => ?_
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp.le
      rw [dualNumberLinearIntegerGrade_ofNat] at hy
      rw [mul_one, RingHom.mem_ker, TrivSqZeroExt.fstHom_apply]
      rcases eq_or_ne n 1 with rfl | h1
      · exact (mem_dualNumberLinearGrade_one k).1 hy
      · rw [dualNumberLinearGrade_eq_bot k (by omega) h1, Submodule.mem_bot] at hy
        rw [hy, TrivSqZeroExt.fst_zero]
    simpa using hle hx
  · intro hx
    obtain ⟨y, rfl⟩ := fst_eq_zero_iff_eps_dvd.1 hx
    rw [mul_comm]
    exact Ideal.mul_mem_left _ y (by
      simpa using mul_mem_gradedPositiveMulIdeal (e := 1) (dualNumberLinearIntegerGrade k) one_pos
        (eps_mem_dualNumberLinearIntegerGrade_one k))

/-- **The `ε`-periodic linear graded projective resolution** `⋯ ⟶ A{2} ⟶ A{1} ⟶ A ⟶ S ⟶ 0` of
`TauCeti.dualNumberLinearResidue`, where `deg ε = 1` and the `n`th term is `A{n}`. -/
def dualNumberLinearResolution :
    GradedProjectiveResolution.{u, u, u, u} (dualNumberLinearIntegerGrade k)
      (dualNumberLinearResidue k).grading where
  X _ := DualNumber k
  grading n :=
    ((GradedModuleCat.regular (𝒜 := dualNumberLinearIntegerGrade k)).shiftObj (n : ℤ)).grading
  gradedSMul n :=
    ((GradedModuleCat.regular (𝒜 := dualNumberLinearIntegerGrade k)).shiftObj (n : ℤ)).gradedSMul
  projective _ := inferInstanceAs (Module.Projective (DualNumber k) (DualNumber k))
  d _ := LinearMap.toSpanSingleton _ _ ε
  π := (gradedPositiveMulQuotientMk (SetLike.one_mem_graded (dualNumberLinearIntegerGrade k))).comp
    (LinearMap.id.codRestrict _ fun _ => by simp)
  isHomogeneous_d n := LinearMap.isHomogeneous_def.2 fun p x hx => by
    have hx' : x ∈ dualNumberLinearIntegerGrade k (p - (n + 1 : ℕ)) := by
      simpa [sub_eq_add_neg] using hx
    have h := SetLike.GradedMul.mul_mem hx' (eps_mem_dualNumberLinearIntegerGrade_one k)
    have hdeg : p - (n + 1 : ℕ) + 1 = p + 0 + -(n : ℤ) := by omega
    rw [hdeg] at h
    simpa using h
  isHomogeneous_π := LinearMap.isHomogeneous_def.2 fun p x hx =>
    (mem_gradedPositiveMulQuotient_piece_iff _).2 ⟨⟨x, by simp⟩, by simpa using hx, rfl⟩
  surjective_π y := by
    obtain ⟨x, rfl⟩ := gradedPositiveMulQuotientMk_surjective _ y
    exact ⟨x, rfl⟩
  exact_d_π x := by
    rw [LinearMap.comp_apply, gradedPositiveMulQuotientMk_eq_zero_iff, LinearMap.codRestrict_apply,
      LinearMap.id_apply, mem_gradedPositiveMulIdeal_linear_one_iff, fst_eq_zero_iff_eps_dvd]
    refine ⟨fun ⟨y, hy⟩ => ⟨y, by simp [hy, mul_comm]⟩, fun ⟨y, hy⟩ => ⟨y, ?_⟩⟩
    rw [← hy, LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  exact_d_d _ := dualNumber_mul_eps_exact

instance moduleFinite_dualNumberLinearResolution_X (n : ℕ) :
    Module.Finite (DualNumber k) ((dualNumberLinearResolution k).X n) :=
  inferInstanceAs (Module.Finite (DualNumber k) (DualNumber k))

/-- The `n`th term of `TauCeti.dualNumberLinearResolution` is the shifted regular module `A{n}`. -/
@[simp]
theorem dualNumberLinearResolution_termObj (n : ℕ) :
    (dualNumberLinearResolution k).termObj n =
      (GradedModuleCat.regular (𝒜 := dualNumberLinearIntegerGrade k)).shiftObj (n : ℤ) :=
  (rfl)

private theorem dualNumberLinearResolution_d_apply (n : ℕ)
    (x : (dualNumberLinearResolution k).X (n + 1)) :
    (dualNumberLinearResolution k).d n x = ((ε : DualNumber k) • x : DualNumber k) :=
  mul_comm (G := DualNumber k) x ε

/-- **The periodic resolution for `deg ε = 1` is linear**: the `n`th term `A{n}` is generated by
`1` in internal degree `n`. -/
theorem isLinear_dualNumberLinearResolution : (dualNumberLinearResolution k).IsLinear := by
  rw [GradedProjectiveResolution.isLinear_iff]
  intro n
  unfold dualNumberLinearResolution
  refine (((GradedModuleCat.regular (𝒜 := dualNumberLinearIntegerGrade k)).shiftObj
    (n : ℤ)).grading.isGeneratedInDegree_iff (A := DualNumber k) n).2 fun x => ?_
  have h1 : (1 : DualNumber k) ∈
      ((GradedModuleCat.regular (𝒜 := dualNumberLinearIntegerGrade k)).shiftObj
        (n : ℤ)).grading.piece n := by
    simpa using one_mem_dualNumberLinearIntegerGrade_zero k
  have hsmul := Submodule.smul_mem (Submodule.span (DualNumber k) _) x (Submodule.subset_span h1)
  rwa [smul_eq_mul, mul_one] at hsmul

/-- **The periodic resolution for `deg ε = 1` is minimal**: every differential is multiplication by
`ε ∈ A_1 ⊆ A₊`. -/
theorem isMinimal_dualNumberLinearResolution : (dualNumberLinearResolution k).IsMinimal :=
  GradedProjectiveResolution.isMinimal_iff.2 fun n x => by
    rw [dualNumberLinearResolution_d_apply]
    exact Submodule.smul_mem_smul
      (Submodule.mem_iSup_of_mem 1 (Submodule.mem_iSup_of_mem one_pos
        (eps_mem_dualNumberLinearIntegerGrade_one k))) Submodule.mem_top

end CommRing

section Field

variable (k : Type u) [Field k]

/-- The `Unit`-indexed basis `[A]` of `K₀^gr(proj A)` over `ℤ[q,q⁻¹]` for `A = k[ε]` with
`deg ε = 1`. -/
def dualNumberLinearRegularProjectiveBasis :
    Module.Basis Unit (LaurentPolynomial ℤ)
      (LaurentK0.{u} (gradedFiniteProjectiveModulesExactStructure
        (dualNumberLinearIntegerGrade k))) :=
  connectedRegularProjectiveBasis
    (fun _ => dualNumberLinearIntegerGrade_eq_bot_of_neg k)
    (dualNumberLinearIntegerGrade_zero_eq_span_one k).le

/-- **Homological degree-`n` coefficient of the Betti Poincaré series**: the `n`th resolution term
`A{n}` has coordinate `qⁿ`. -/
theorem coeff_bettiPoincarePowerSeries_dualNumberLinearResolution (n : ℕ) (u : Unit) :
    PowerSeries.coeff n
        ((dualNumberLinearResolution k).bettiPoincarePowerSeries
          (dualNumberLinearRegularProjectiveBasis k) u) =
      T (n : ℤ) := by
  rw [GradedProjectiveResolution.coeff_bettiPoincarePowerSeries,
    dualNumberLinearRegularProjectiveBasis]
  have hterm : (dualNumberLinearResolution k).finiteProjectiveTerm n =
      ⟨(GradedModuleCat.regular (𝒜 := dualNumberLinearIntegerGrade k)).shiftObj (n : ℤ),
        gradedFiniteProjectiveModules_shiftObj
          (gradedRegularProjective (dualNumberLinearIntegerGrade k)).property (n : ℤ)⟩ :=
    ObjectProperty.FullSubcategory.ext
      (((dualNumberLinearResolution k).finiteProjectiveTerm_obj n).trans
        (dualNumberLinearResolution_termObj k n))
  rw [hterm, connectedRegularProjectiveBasis_repr_of_shiftObj]

/-- **Explicit geometric-series form of the Betti Poincaré series**:
`B(S; q, t) = ∑_{n ≥ 0} qⁿ tⁿ`. -/
theorem bettiPoincarePowerSeries_dualNumberLinearResolution_eq_mk_pow (u : Unit) :
    (dualNumberLinearResolution k).bettiPoincarePowerSeries
        (dualNumberLinearRegularProjectiveBasis k) u =
      PowerSeries.mk fun n => (T 1 : LaurentPolynomial ℤ) ^ n := by
  ext n
  rw [coeff_bettiPoincarePowerSeries_dualNumberLinearResolution, PowerSeries.coeff_mk, T_pow,
    mul_one]

/-- `B(S; q, t)` is the `q`-rescaling of `(1 - t)⁻¹ = ∑_{n ≥ 0} tⁿ`. -/
theorem bettiPoincarePowerSeries_dualNumberLinearResolution_eq_rescale (u : Unit) :
    (dualNumberLinearResolution k).bettiPoincarePowerSeries
        (dualNumberLinearRegularProjectiveBasis k) u =
      PowerSeries.rescale (T 1 : LaurentPolynomial ℤ) (PowerSeries.mk 1) := by
  ext n
  rw [coeff_bettiPoincarePowerSeries_dualNumberLinearResolution, PowerSeries.coeff_rescale,
    PowerSeries.coeff_mk, Pi.one_apply, mul_one, T_pow, mul_one]

/-- **Closed-form rational identity `(1 - q t)⁻¹` in `(ℤ[q,q⁻¹])⟦t⟧`.** The Betti Poincaré power
series of `S = k[ε] / (ε)` (`deg ε = 1`) is the multiplicative inverse of `1 - q t`. -/
theorem bettiPoincarePowerSeries_dualNumberLinearResolution_mul_one_sub (u : Unit) :
    (dualNumberLinearResolution k).bettiPoincarePowerSeries
        (dualNumberLinearRegularProjectiveBasis k) u *
      (1 - PowerSeries.C (T 1 : LaurentPolynomial ℤ) * PowerSeries.X) = 1 := by
  rw [bettiPoincarePowerSeries_dualNumberLinearResolution_eq_mk_pow]
  exact powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (T 1 : LaurentPolynomial ℤ)

/-- **Bidegree Betti numbers of `S = k[ε] / (ε)` (`deg ε = 1`).** The `(n, d)` Betti number is `1`
on the diagonal `d = n` and `0` off the diagonal. -/
theorem coeff_coeff_bettiPoincarePowerSeries_dualNumberLinearResolution (u : Unit) (n : ℕ)
    (d : ℤ) :
    (PowerSeries.coeff n
        ((dualNumberLinearResolution k).bettiPoincarePowerSeries
          (dualNumberLinearRegularProjectiveBasis k) u)).coeff d =
      if d = n then 1 else 0 := by
  rw [coeff_bettiPoincarePowerSeries_dualNumberLinearResolution, T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

/-- Specializing `q = 1` in `B(S; q, t)` yields the ungraded geometric series `∑_{n ≥ 0} tⁿ`. -/
@[simp]
theorem map_laurentEval_one_bettiPoincarePowerSeries_dualNumberLinearResolution (u : Unit) :
    PowerSeries.map (laurentEval (R := ℤ) (1 : ℤˣ) : LaurentPolynomial ℤ →+* ℤ)
        ((dualNumberLinearResolution k).bettiPoincarePowerSeries
          (dualNumberLinearRegularProjectiveBasis k) u) =
      PowerSeries.mk 1 := by
  ext n
  rw [PowerSeries.coeff_map, coeff_bettiPoincarePowerSeries_dualNumberLinearResolution,
    PowerSeries.coeff_mk, Pi.one_apply]
  simp

/-- **Genuine infinite formal power series.** The Betti Poincaré series of `S = k[ε] / (ε)` is not
the coercion of any polynomial in `t` over `ℤ[q,q⁻¹]`. -/
theorem not_exists_polynomial_bettiPoincarePowerSeries_dualNumberLinearResolution (u : Unit) :
    ¬ ∃ p : Polynomial (LaurentPolynomial ℤ),
      (p : PowerSeries (LaurentPolynomial ℤ)) =
        (dualNumberLinearResolution k).bettiPoincarePowerSeries
          (dualNumberLinearRegularProjectiveBasis k) u := by
  rintro ⟨p, hp⟩
  have h := congrArg (fun f => (PowerSeries.coeff (p.natDegree + 1) f).coeff (p.natDegree + 1 : ℕ))
    hp
  rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _),
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
    coeff_coeff_bettiPoincarePowerSeries_dualNumberLinearResolution] at h
  simp at h

private theorem smulGradedDimension_regular_dualNumberLinear :
    letI : Module.Finite k (GradedModuleCat.regular (𝒜 := dualNumberLinearIntegerGrade k)) :=
      inferInstanceAs (Module.Finite k (DualNumber k))
    (GradedModuleCat.regular (𝒜 := dualNumberLinearIntegerGrade k)).smulGradedDimension 1 =
      1 + T 1 := by
  let _ : Module.Finite k (GradedModuleCat.regular (𝒜 := dualNumberLinearIntegerGrade k)) :=
    inferInstanceAs (Module.Finite k (DualNumber k))
  ext p
  rw [GradedModuleCat.coeff_smulGradedDimension, one_smul (DualNumber k),
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← mul_one (T 1 : LaurentPolynomial ℤ),
    coeff_T_mul, coeff_one, coeff_one]
  have hpiece :
      (GradedModuleCat.regular (𝒜 := dualNumberLinearIntegerGrade k)).grading.piece p =
        dualNumberLinearIntegerGrade k p := by simp
  rw [hpiece]
  rcases lt_or_ge p 0 with hp | hp
  · rw [dualNumberLinearIntegerGrade_eq_bot_of_neg k hp, finrank_bot]
    simp [hp.ne, show p - 1 ≠ 0 by omega]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [dualNumberLinearIntegerGrade_ofNat]
  rcases eq_or_ne n 0 with rfl | h0
  · simp [(dualNumberLinearGradeZeroEquiv k).finrank_eq]
  rcases eq_or_ne n 1 with rfl | h1
  · simp [(dualNumberLinearGradeOneEquiv k).finrank_eq]
  rw [dualNumberLinearGrade_eq_bot k h0 h1, finrank_bot]
  simp [h0, show (n : ℤ) - 1 ≠ 0 by omega]

/-- **No finite graded projective resolution.** Over a field `k`, the graded residue module
`S = k[ε] / (ε)` (`deg ε = 1`) admits no finite resolution by finite graded projectives: otherwise
`[S]` would lie in the image of the graded Cartan map, forcing `1 + q` to divide `1` in
`ℤ[q, q⁻¹]`. -/
theorem not_admitsFiniteResolution_dualNumberLinearResidue :
    ¬ (gradedModuleCanonicalExactStructure (dualNumberLinearIntegerGrade k)).admitsFiniteResolution
      (gradedFiniteProjectiveModules (dualNumberLinearIntegerGrade k))
      (dualNumberLinearResidue k) := by
  intro hS
  set 𝒜 := dualNumberLinearIntegerGrade k
  let x : LaurentK0.{u} (gradedFiniteProjectiveModulesExactStructure 𝒜) :=
    (gradedModuleResolutionEquiv 𝒜).symm
      (LaurentK0.of.{u} (gradedFiniteProjectiveResolutionExactStructure 𝒜)
        ⟨dualNumberLinearResidue k, hS⟩)
  have hCartan : gradedCartanMap 𝒜 x =
      LaurentK0.of.{u} (gradedFiniteModulesExactStructure 𝒜)
        ⟨dualNumberLinearResidue k,
          gradedAdmitsFiniteProjectiveResolution_le_finiteModules 𝒜 _ hS⟩ := by
    rw [gradedCartanMap_apply, LinearEquiv.apply_symm_apply,
      fromGradedFiniteProjectiveResolution_of]
  set bP := dualNumberLinearRegularProjectiveBasis k with hbP
  have hx : x = bP.repr x () •
      LaurentK0.of.{u} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (gradedRegularProjective 𝒜) := by
    conv_lhs => rw [← bP.sum_repr x]
    rw [Finset.univ_unique, Finset.sum_singleton, hbP, dualNumberLinearRegularProjectiveBasis,
      connectedRegularProjectiveBasis_apply]
  set coord := gradedIdempotentCoordinate (𝒜 := 𝒜)
    (IsIdempotentElem.one : IsIdempotentElem (1 : DualNumber k))
    (one_mem_dualNumberLinearIntegerGrade_zero k) with hcoord
  have hLHS : coord (gradedCartanMap 𝒜 x) = bP.repr x () * (1 + T 1) := by
    conv_lhs => rw [hx]
    rw [LinearMap.map_smul, LinearMap.map_smul, gradedCartanMap_of, smul_eq_mul]
    congr 1
    rw [hcoord, gradedIdempotentCoordinate_of]
    exact smulGradedDimension_regular_dualNumberLinear k
  have hRHS : coord (LaurentK0.of.{u} (gradedFiniteModulesExactStructure 𝒜)
      ⟨dualNumberLinearResidue k,
        gradedAdmitsFiniteProjectiveResolution_le_finiteModules 𝒜 _ hS⟩) = 1 := by
    rw [hcoord, gradedIdempotentCoordinate_of]
    simpa using smulGradedDimension_gradedIdempotentHead
      (I := Unit) (e := fun _ => (1 : DualNumber k))
      (fun _ => dualNumberLinearIntegerGrade_eq_bot_of_neg k)
      (CompleteOrthogonalIdempotents.unique_iff.2 rfl).toOrthogonalIdempotents
      (fun _ => SetLike.one_mem_graded 𝒜)
      (by rw [Set.range_const, dualNumberLinearIntegerGrade_zero_eq_span_one])
      () () one_ne_zero
  have hunit : bP.repr x () * (1 + T 1) = 1 :=
    hLHS.symm.trans ((congrArg coord hCartan).trans hRHS)
  have heval := congrArg (laurentEval (R := ℤ) (-1 : ℤˣ)) hunit
  simp only [map_mul, map_add, map_one, laurentEval_T_one, Units.val_neg, Units.val_one,
    add_neg_cancel, mul_zero] at heval
  exact zero_ne_one heval

end Field

end TauCeti
