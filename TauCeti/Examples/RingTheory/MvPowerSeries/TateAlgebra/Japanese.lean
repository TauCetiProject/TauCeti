/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basis
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Japanese
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeaklyStable

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import TauCeti.RingTheory.MvPowerSeries.Order

/-!
# Non-vacuous field-extension examples for Tate algebras

In at least one variable, the Gauss-normed fraction field `F := GaussFractionField σ K c` of a
restricted-series ring `T := K{X / c}` admits genuine nontrivial finite extensions of both types:

* a degree-`2` separable extension defined by `Y ^ 2 + Xᵢ ^ 2 * Y + Xᵢ` (valid in every
  characteristic, including characteristic `2`), and
* in prime characteristic `p`, a nontrivial purely inseparable extension obtained by adjoining a
  `p`-th root of `Xᵢ`.

This file exercises both `TauCeti.MvPowerSeries.isWeaklyStable_gaussFractionField` (spectral-norm
comparison against a power basis over `[Countable σ] [NormedField K]`) and
`TauCeti.MvPowerSeries.isJapanese_isRestricted_subring` (finiteness of `integralClosure T L` over
`[Finite σ] [NormedField K]`) on both extensions.
-/

public section

namespace TauCeti.Examples

open _root_.MvPowerSeries TauCeti.MvPowerSeries
open scoped IntermediateField

universe u₁ u₂

private theorem sq_add_X_sq_mul_add_X_mul_sq_ne_zero {σ R : Type*}
    [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] (i : σ)
    {A B : _root_.MvPowerSeries σ R} (hB : B ≠ 0) :
    A ^ 2 + X i ^ 2 * A * B + X i * B ^ 2 ≠ 0 := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [sq, zero_mul, mul_zero, zero_mul, zero_add, zero_add]
    have hX : (X i : _root_.MvPowerSeries σ R) ≠ 0 := fun h ↦ by
      simpa using congrArg (coeff (Finsupp.single i 1)) h
    exact mul_ne_zero hX (pow_ne_zero 2 hB)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (order_eq_top_iff.not.mpr hA)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (order_eq_top_iff.not.mpr hB)
  have ho1 : (A ^ 2).order = ((2 * a : ℕ) : ℕ∞) := by
    rw [order_pow, ← ha, nsmul_eq_mul]; norm_cast
  have ho2 : (X i * B ^ 2).order = ((1 + 2 * b : ℕ) : ℕ∞) := by
    rw [order_mul, order_X, order_pow, ← hb, nsmul_eq_mul]; norm_cast
  have ho3 : (X i ^ 2 * A * B).order = ((2 + a + b : ℕ) : ℕ∞) := by
    rw [order_mul, order_mul, order_pow, order_X, ← ha, ← hb, nsmul_eq_mul]; norm_cast
  have hne12 : (A ^ 2).order ≠ (X i * B ^ 2).order := by rw [ho1, ho2, ne_eq, Nat.cast_inj]; omega
  have hmin_cast (x y : ℕ) : (min (x : ℕ∞) (y : ℕ∞)) = ((min x y : ℕ) : ℕ∞) :=
    (Monotone.map_min (fun _ _ ↦ Nat.cast_le.mpr)).symm
  have ho12 : (A ^ 2 + X i * B ^ 2).order = ((min (2 * a) (1 + 2 * b) : ℕ) : ℕ∞) := by
    rw [order_add_of_order_ne hne12, ho1, ho2, hmin_cast]
  have hne_sum : (A ^ 2 + X i * B ^ 2).order ≠ (X i ^ 2 * A * B).order := by
    rw [ho12, ho3, ne_eq, Nat.cast_inj]; omega
  rw [add_right_comm, ne_eq, ← order_eq_top_iff, order_add_of_order_ne hne_sum, ho12, ho3,
    hmin_cast]
  exact ENat.natCast_ne_top _

private theorem sq_add_algebraMap_X_sq_mul_add_algebraMap_X_ne_zero
    (σ K : Type*) [NormedField K] [IsUltrametricDist K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)] (i : σ) (z : GaussFractionField σ K c) :
    z ^ 2 + (algebraMap (IsRestricted.subring (R := K) c) (GaussFractionField σ K c)
        ⟨X i, isRestricted_X c i⟩) ^ 2 * z +
      algebraMap (IsRestricted.subring (R := K) c) (GaussFractionField σ K c)
        ⟨X i, isRestricted_X c i⟩ ≠ 0 := by
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let X₀ : T := ⟨X i, isRestricted_X c i⟩
  intro hz
  obtain ⟨A, B, hB_mem, rfl⟩ := IsFractionRing.div_surjective T z
  have hB_F_ne : algebraMap T F B ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hB_mem
  have hclear : algebraMap T F (A ^ 2 + X₀ ^ 2 * A * B + X₀ * B ^ 2) = 0 := by
    have hmul := congrArg (· * (algebraMap T F B) ^ 2) hz
    simp only [zero_mul, map_add, map_mul, map_pow] at hmul ⊢
    dsimp only [X₀, T, F] at hmul hB_F_ne ⊢
    field_simp [hB_F_ne] at hmul
    linear_combination hmul
  have hT0 : A ^ 2 + X₀ ^ 2 * A * B + X₀ * B ^ 2 = 0 :=
    (map_eq_zero_iff _ (IsFractionRing.injective T F)).mp hclear
  exact sq_add_X_sq_mul_add_X_mul_sq_ne_zero i
    (Subtype.coe_ne_coe.mpr (nonZeroDivisors.ne_zero hB_mem))
    (by simpa only [Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow,
      ZeroMemClass.coe_zero] using congrArg Subtype.val hT0)

private theorem exists_separable_quadratic_extension (σ : Type u₁) (K : Type u₂)
    [Nonempty σ] [NormedField K] [IsUltrametricDist K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    let T := IsRestricted.subring (R := K) c
    let F := GaussFractionField σ K c
    ∃ (L : Type (max u₁ u₂)) (_ : Field L) (_ : Algebra T L) (_ : Algebra F L)
      (_ : IsScalarTower T F L) (_ : FiniteDimensional F L) (_ : Algebra.IsSeparable F L)
      (n : ℕ) (_ : NeZero n) (_ : Module.Basis (Fin n) F L),
      Module.finrank F L = 2 := by
  classical
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let i₀ : σ := Classical.arbitrary σ
  let x₀ : F := algebraMap T F ⟨X i₀, isRestricted_X c i₀⟩
  have hx₀_ne : x₀ ≠ 0 := by
    rw [← norm_pos_iff, norm_algebraMap_gaussFractionField_X]; exact Fact.out
  let P : Polynomial F := Polynomial.X ^ 2 + Polynomial.C (x₀ ^ 2) * Polynomial.X + Polynomial.C x₀
  have hP_deg : P.natDegree = 2 := by dsimp only [P]; compute_degree!
  have hP_monic : P.Monic := by dsimp only [P]; monicity!
  have hP_irr : Irreducible P :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hP_deg]; decide)
      fun z hz ↦ sq_add_algebraMap_X_sq_mul_add_algebraMap_X_ne_zero σ K c i₀ z <| by
        simpa only [P, x₀, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow,
          Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] using hz
  have hP_sep : P.Separable := by
    rw [Polynomial.separable_iff_derivative_ne_zero hP_irr]
    exact fun hderiv ↦ hx₀_ne (by simpa [P] using congrArg (Polynomial.eval 0) hderiv)
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (P.map (algebraMap F (AlgebraicClosure F)))
    (by rw [Polynomial.degree_map_eq_of_injective (algebraMap F _).injective,
          Polynomial.degree_eq_natDegree hP_monic.ne_zero, hP_deg]; decide)
  have hβ_aeval : Polynomial.aeval β P = 0 := by rwa [Polynomial.aeval_def, ← Polynomial.eval_map]
  have hmin : minpoly F β = P := (minpoly.eq_of_irreducible_of_monic hP_irr hβ_aeval hP_monic).symm
  have hβ_int : IsIntegral F β := ⟨P, hP_monic, hβ_aeval⟩
  have hβ_sep : IsSeparable F β := by rwa [IsSeparable, hmin]
  let L := F⟮β⟯
  have : Algebra.IsSeparable F L :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F (AlgebraicClosure F)).mpr hβ_sep
  have : FiniteDimensional F L := IntermediateField.adjoin.finiteDimensional hβ_int
  have hfin : Module.finrank F L = 2 := by
    rw [IntermediateField.adjoin.finrank hβ_int, hmin, hP_deg]
  let pb := IntermediateField.adjoin.powerBasis hβ_int
  have : NeZero pb.dim := ⟨by rw [IntermediateField.adjoin.powerBasis_dim, hmin, hP_deg]; decide⟩
  let _ : Algebra T L := ((algebraMap F L).comp (algebraMap T F)).toAlgebra
  have : IsScalarTower T F L := ⟨fun t a y ↦ by
    rw [Algebra.smul_def t a, mul_smul, Algebra.smul_def t (a • y),
      RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← Algebra.smul_def]⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, pb.dim, inferInstance, pb.basis, hfin⟩

private theorem exists_purelyInseparable_root_extension (σ : Type u₁) (K : Type u₂)
    [Nonempty σ] [NormedField K] [IsUltrametricDist K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    let T := IsRestricted.subring (R := K) c
    let F := GaussFractionField σ K c
    ∃ (M : Type (max u₁ u₂)) (_ : Field M) (_ : Algebra T M) (_ : Algebra F M)
      (_ : IsScalarTower T F M) (_ : FiniteDimensional F M) (_ : IsPurelyInseparable F M)
      (n : ℕ) (_ : NeZero n) (_ : Module.Basis (Fin n) F M),
      1 < Module.finrank F M := by
  classical
  have hp : p.Prime := Fact.out
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  have : ExpChar K p := .prime hp
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let i₀ : σ := Classical.arbitrary σ
  let x₀ : F := algebraMap T F ⟨X i₀, isRestricted_X c i₀⟩
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) x₀) hp.pos
  have hα_int : IsIntegral F α :=
    ⟨Polynomial.X ^ p - Polynomial.C x₀, Polynomial.monic_X_pow_sub_C x₀ hp.ne_zero, by simp [hα]⟩
  let M := F⟮α⟯
  have : IsPurelyInseparable F M := by
    rw [← le_perfectClosure_iff, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
      SetLike.mem_coe, mem_perfectClosure_iff_pow_mem p]
    exact ⟨1, x₀, by rw [pow_one, hα]⟩
  have : FiniteDimensional F M := IntermediateField.adjoin.finiteDimensional hα_int
  have hfin_gt : 1 < Module.finrank F M := by
    by_contra! hle
    obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp
      (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp (le_antisymm hle Module.finrank_pos))
    exact pow_ne_algebraMap_gaussFractionField_X σ K c i₀ hp.ne_one z
      ((algebraMap F (AlgebraicClosure F)).injective (by rw [map_pow, hz, hα]))
  let pb := IntermediateField.adjoin.powerBasis hα_int
  have : NeZero pb.dim := ⟨by
    rw [IntermediateField.adjoin.powerBasis_dim, ← IntermediateField.adjoin.finrank hα_int]
    exact (zero_lt_one.trans hfin_gt).ne'⟩
  let _ : Algebra T M := ((algebraMap F M).comp (algebraMap T F)).toAlgebra
  have : IsScalarTower T F M := ⟨fun t a y ↦ by
    rw [Algebra.smul_def t a, mul_smul, Algebra.smul_def t (a • y),
      RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← Algebra.smul_def]⟩
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, pb.dim, inferInstance, pb.basis, hfin_gt⟩

/-- In any characteristic (including `2`), `Y ^ 2 + Xᵢ ^ 2 * Y + Xᵢ` defines a degree-`2` separable
extension of `GaussFractionField σ K c` on which `spectralNorm` is equivalent to the power-basis
coordinate norm. -/
theorem exists_separable_quadratic_basis_norm_comparison (σ : Type u₁) (K : Type u₂)
    [Countable σ] [Nonempty σ] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    ∃ (L : Type (max u₁ u₂)) (_ : Field L) (_ : Algebra (GaussFractionField σ K c) L)
      (_ : FiniteDimensional (GaussFractionField σ K c) L)
      (_ : Algebra.IsSeparable (GaussFractionField σ K c) L)
      (n : ℕ) (_ : NeZero n) (b : Module.Basis (Fin n) (GaussFractionField σ K c) L),
      Module.finrank (GaussFractionField σ K c) L = 2 ∧
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ y,
        b.norm y ≤ C * spectralNorm (GaussFractionField σ K c) L y ∧
        spectralNorm (GaussFractionField σ K c) L y ≤ D * b.norm y := by
  obtain ⟨L, _, _, _, _, _, _, n, _, b, hfin⟩ := exists_separable_quadratic_extension σ K c
  obtain ⟨C, D, hC, hD, hCD⟩ :=
    (isWeaklyStable_gaussFractionField σ K c).exists_basis_norm_comparison b
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, n, inferInstance, b,
    hfin, C, D, hC, hD, hCD⟩

/-- In prime characteristic `p`, adjoining a `p`-th root of a coordinate variable `Xᵢ` produces a
nontrivial finite purely inseparable extension of `GaussFractionField σ K c` on which `spectralNorm`
is equivalent to the power-basis coordinate norm. -/
theorem exists_purelyInseparable_root_basis_norm_comparison (σ : Type u₁) (K : Type u₂)
    [Countable σ] [Nonempty σ] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    ∃ (M : Type (max u₁ u₂)) (_ : Field M) (_ : Algebra (GaussFractionField σ K c) M)
      (_ : FiniteDimensional (GaussFractionField σ K c) M)
      (_ : IsPurelyInseparable (GaussFractionField σ K c) M)
      (n : ℕ) (_ : NeZero n) (b : Module.Basis (Fin n) (GaussFractionField σ K c) M),
      1 < Module.finrank (GaussFractionField σ K c) M ∧
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ y,
        b.norm y ≤ C * spectralNorm (GaussFractionField σ K c) M y ∧
        spectralNorm (GaussFractionField σ K c) M y ≤ D * b.norm y := by
  obtain ⟨M, _, _, _, _, _, _, n, _, b, hfin⟩ := exists_purelyInseparable_root_extension σ K p c
  obtain ⟨C, D, hC, hD, hCD⟩ :=
    (isWeaklyStable_gaussFractionField σ K c).exists_basis_norm_comparison b
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, n, inferInstance, b,
    hfin, C, D, hC, hD, hCD⟩

/-- In any characteristic (including `2`), `Y ^ 2 + Xᵢ ^ 2 * Y + Xᵢ` defines a degree-`2` separable
extension `L` of the fraction field of `T := K⟨X₁, …, Xₙ⟩` in which `integralClosure T L` is a
finite `T`-module. -/
theorem exists_separable_quadratic_finite_integralClosure (σ : Type u₁) (K : Type u₂)
    [Finite σ] [Nonempty σ] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    ∃ (L : Type (max u₁ u₂)) (_ : Field L)
      (_ : Algebra (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) L)
      (_ : Algebra (GaussFractionField σ K (fun _ : σ ↦ 1)) L)
      (_ : IsScalarTower (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))
        (GaussFractionField σ K (fun _ : σ ↦ 1)) L)
      (_ : FiniteDimensional (GaussFractionField σ K (fun _ : σ ↦ 1)) L)
      (_ : Algebra.IsSeparable (GaussFractionField σ K (fun _ : σ ↦ 1)) L),
      Module.finrank (GaussFractionField σ K (fun _ : σ ↦ 1)) L = 2 ∧
      Module.Finite (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))
        (integralClosure (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) L) := by
  obtain ⟨L, _, _, _, _, _, _, _, _, _, hfin⟩ :=
    exists_separable_quadratic_extension σ K (fun _ : σ ↦ 1)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hfin,
    Ring.IsJapanese.finite_integralClosure (GaussFractionField σ K (fun _ ↦ 1)) L⟩

/-- In prime characteristic `p`, adjoining a `p`-th root of `Xᵢ` produces a nontrivial finite purely
inseparable extension `M` of the fraction field of `T := K⟨X₁, …, Xₙ⟩` in which
`integralClosure T M` is a finite `T`-module. -/
theorem exists_purelyInseparable_root_finite_integralClosure (σ : Type u₁) (K : Type u₂)
    [Finite σ] [Nonempty σ] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ (M : Type (max u₁ u₂)) (_ : Field M)
      (_ : Algebra (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) M)
      (_ : Algebra (GaussFractionField σ K (fun _ : σ ↦ 1)) M)
      (_ : IsScalarTower (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))
        (GaussFractionField σ K (fun _ : σ ↦ 1)) M)
      (_ : FiniteDimensional (GaussFractionField σ K (fun _ : σ ↦ 1)) M)
      (_ : IsPurelyInseparable (GaussFractionField σ K (fun _ : σ ↦ 1)) M),
      1 < Module.finrank (GaussFractionField σ K (fun _ : σ ↦ 1)) M ∧
      Module.Finite (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))
        (integralClosure (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) M) := by
  obtain ⟨M, _, _, _, _, _, _, _, _, _, hfin⟩ :=
    exists_purelyInseparable_root_extension σ K p (fun _ : σ ↦ 1)
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hfin,
    Ring.IsJapanese.finite_integralClosure (GaussFractionField σ K (fun _ ↦ 1)) M⟩

end TauCeti.Examples
