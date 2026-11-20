/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.WeaklyStable
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import TauCeti.Analysis.Normed.Module.Dual.Bounded
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basis
import TauCeti.RingTheory.MvPowerSeries.Basic
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.PurelyInseparable

/-!
# Characteristic-free weak stability of Gauss-normed Tate fraction fields

Let `K` be a complete ultrametric normed field of arbitrary characteristic (trivially or
nontrivially normed), `σ` a countable variable type, and `c : σ → ℝ` a positive polyradius. This
file proves that the Gauss-normed fraction field `GaussFractionField σ K c` of the
restricted-series algebra `K{X / c}` is weakly stable
(`TauCeti.MvPowerSeries.isWeaklyStable_gaussFractionField`): on every finite extension
`L / GaussFractionField σ K c`, every linear functional is bounded by `spectralNorm`.

With no variables (`[IsEmpty σ]`), `GaussFractionField σ K c` is isometrically `K`-isomorphic to
`K`, so its spectral norms and weak stability coincide with those of `K` even without completeness.

## Proof outline

By `TauCeti.IsWeaklyStable.of_isPurelyInseparable`, it suffices to prove boundedness of linear
functionals on every finite purely inseparable extension `M` of `F := GaussFractionField σ K c`.
In `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.PurelyInseparable`,
`TauCeti.MvPowerSeries.exists_dual_norm_le_spectralNorm_of_isPurelyInseparable` constructs
separating spectrally bounded `F`-linear functionals on `M`, concluding directly by
`Module.Dual.exists_bound_of_forall_exists_ne_zero`.

## Main results

* `TauCeti.MvPowerSeries.spectralNorm_gaussFractionField_of_isEmpty` and
  `TauCeti.MvPowerSeries.isWeaklyStable_gaussFractionField_iff_of_isEmpty`: zero-variable agreement
  with extensions of `K`.
* `TauCeti.MvPowerSeries.isWeaklyStable_gaussFractionField`: characteristic-free weak stability of
  `GaussFractionField σ K c` for `[Countable σ]` over any complete ultrametric normed field.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.5.3 and 5.3.1,
  Theorem 1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter
open scoped Topology IntermediateField

section Empty

variable (σ K : Type*) [NormedField K] [IsUltrametricDist K] [IsEmpty σ]
  (c : σ → ℝ) [∀ i, Fact (0 < c i)]

/-- With no variables, the spectral norm of an extension over `GaussFractionField σ K c` coincides
with its spectral norm over `K`. -/
@[simp]
theorem spectralNorm_gaussFractionField_of_isEmpty (L : Type*) [Field L]
    [Algebra K L] [Algebra (GaussFractionField σ K c) L]
    [IsScalarTower K (GaussFractionField σ K c) L] (y : L) :
    spectralNorm (GaussFractionField σ K c) L y = spectralNorm K L y := by
  refine ((gaussFractionFieldIsEmptyAlgEquiv σ K c).toRingEquiv.spectralNorm_eq_of_norm_eq
    (norm_gaussFractionFieldIsEmptyAlgEquiv σ K c) (RingEquiv.refl L) ?_ y).symm
  ext z
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
    RingHom.coe_coe, RingEquiv.refl_apply]
  rw [IsScalarTower.algebraMap_apply K (GaussFractionField σ K c) L,
    ← gaussFractionFieldIsEmptyAlgEquiv_symm_apply, AlgEquiv.symm_apply_apply]

/-- With no variables, `GaussFractionField σ K c` is weakly stable if and only if `K` is weakly
stable. -/
@[simp]
theorem isWeaklyStable_gaussFractionField_iff_of_isEmpty :
    IsWeaklyStable (GaussFractionField σ K c) ↔ IsWeaklyStable K :=
  (gaussFractionFieldIsEmptyAlgEquiv σ K c).toRingEquiv.isWeaklyStable_iff_of_norm_eq
    (norm_gaussFractionFieldIsEmptyAlgEquiv σ K c)

end Empty

section WeaklyStable

/-- **Characteristic-free weak stability of Gauss-normed Tate fraction fields.**
For any complete ultrametric normed field `K` (of arbitrary characteristic, trivially or
nontrivially normed), countable variable type `σ`, and positive polyradius `c : σ → ℝ`, the
Gauss-normed fraction field `GaussFractionField σ K c` is weakly stable
([bosch-guntzer-remmert], §5.3.1, Theorem 1). -/
theorem isWeaklyStable_gaussFractionField (σ K : Type*) [Countable σ]
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    IsWeaklyStable (GaussFractionField σ K c) := by
  refine IsWeaklyStable.of_isPurelyInseparable fun M _ _ _ _ ψ ↦ ?_
  refine Module.Dual.exists_bound_of_forall_exists_ne_zero ψ (spectralNorm _ M) fun x₀ hx₀ ↦ ?_
  obtain ⟨φ, C, -, hφ_bound, -, hφ_ne⟩ :=
    exists_dual_norm_le_spectralNorm_of_isPurelyInseparable (σ := σ) (K := K) (c := c) M hx₀
  exact ⟨φ, ⟨C, hφ_bound⟩, hφ_ne⟩

end WeaklyStable

section Examples

/-!
### Non-vacuous instances of weak stability over `GaussFractionField`

In at least one variable, `GaussFractionField σ K c` has genuine nontrivial finite extensions of
both types:
* a degree-`2` separable extension defined by `Y ^ 2 + Xᵢ ^ 2 * Y + Xᵢ` (valid in every
  characteristic, including characteristic `2`), and
* in prime characteristic `p`, a nontrivial purely inseparable extension obtained by adjoining a
  `p`-th root of `Xᵢ`.

In both cases `isWeaklyStable_gaussFractionField` yields equivalence between `spectralNorm` and the
power-basis coordinate norm.
-/

universe u₁ u₂

private theorem sq_add_X_sq_mul_add_X_mul_sq_ne_zero {σ R : Type*}
    [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] (i : σ)
    {A B : _root_.MvPowerSeries σ R} (hB : B ≠ 0) :
    A ^ 2 + X i ^ 2 * A * B + X i * B ^ 2 ≠ 0 := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [sq, zero_mul, mul_zero, zero_mul, zero_add, zero_add]
    exact mul_ne_zero (X_ne_zero i) (pow_ne_zero 2 hB)
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

/-- For any coordinate variable `x₀ = X i` in `GaussFractionField σ K c`, the quadratic polynomial
`Y ^ 2 + x₀ ^ 2 * Y + x₀` has no root in `GaussFractionField σ K c`. -/
private theorem not_isRoot_X_sq_add_C_sq_mul_X_add_C {σ K : Type*}
    [NormedField K] [IsUltrametricDist K] {c : σ → ℝ} [∀ i, Fact (0 < c i)]
    (i : σ) (z : GaussFractionField σ K c) :
    let x₀ := algebraMap (IsRestricted.subring (R := K) c) (GaussFractionField σ K c)
      ⟨X i, isRestricted_X c i⟩
    ¬ (Polynomial.X ^ 2 + Polynomial.C (x₀ ^ 2) * Polynomial.X + Polynomial.C x₀).IsRoot z := by
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let X₀ : T := ⟨X i, isRestricted_X c i⟩
  intro x₀ hz
  rw [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_C] at hz
  obtain ⟨A, B, hB_mem, rfl⟩ := IsFractionRing.div_surjective T z
  have hB_F_ne : algebraMap T F B ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hB_mem
  have hclear : algebraMap T F (A ^ 2 + X₀ ^ 2 * A * B + X₀ * B ^ 2) = 0 := by
    have hmul := congrArg (· * (algebraMap T F B) ^ 2) hz
    simp only [zero_mul, map_add, map_mul, map_pow] at hmul ⊢
    dsimp only [x₀, X₀, T, F] at hmul hB_F_ne ⊢
    field_simp [hB_F_ne] at hmul
    linear_combination hmul
  have hT0 : A ^ 2 + X₀ ^ 2 * A * B + X₀ * B ^ 2 = 0 :=
    (map_eq_zero_iff _ (IsFractionRing.injective T F)).mp hclear
  exact sq_add_X_sq_mul_add_X_mul_sq_ne_zero i
    (Subtype.coe_ne_coe.mpr (nonZeroDivisors.ne_zero hB_mem))
    (by simpa only [Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow,
      ZeroMemClass.coe_zero] using congrArg Subtype.val hT0)

/-- In any characteristic (including `2`), `Y ^ 2 + Xᵢ ^ 2 * Y + Xᵢ` defines a degree-`2` separable
extension of `GaussFractionField σ K c` on which `spectralNorm` is equivalent to the power-basis
coordinate norm. -/
example (σ : Type u₁) (K : Type u₂) [Countable σ] [Nonempty σ]
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    let F := GaussFractionField σ K c
    ∃ (L : Type (max u₁ u₂)) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
      (_ : Algebra.IsSeparable F L) (n : ℕ) (_ : NeZero n) (b : Module.Basis (Fin n) F L),
      Module.finrank F L = 2 ∧
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ y,
        b.norm y ≤ C * spectralNorm F L y ∧ spectralNorm F L y ≤ D * b.norm y := by
  classical
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let i₀ : σ := Classical.arbitrary σ
  let X₀ : T := ⟨X i₀, isRestricted_X c i₀⟩
  let x₀ : F := algebraMap T F X₀
  have hx₀_ne : x₀ ≠ 0 := by
    rw [← norm_pos_iff, norm_algebraMap_gaussFractionField_X]; exact Fact.out
  let P : Polynomial F := Polynomial.X ^ 2 + Polynomial.C (x₀ ^ 2) * Polynomial.X + Polynomial.C x₀
  have hP_deg : P.natDegree = 2 := by dsimp only [P]; compute_degree!
  have hP_monic : P.Monic := by dsimp only [P]; monicity!
  have hP_irr : Irreducible P :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hP_deg]; decide)
      (not_isRoot_X_sq_add_C_sq_mul_X_add_C i₀)
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
  have hfin : Module.finrank F L = 2 := by
    rw [IntermediateField.adjoin.finrank hβ_int, hmin, hP_deg]
  let pb := IntermediateField.adjoin.powerBasis hβ_int
  have : NeZero pb.dim := ⟨by rw [IntermediateField.adjoin.powerBasis_dim, hmin, hP_deg]; decide⟩
  obtain ⟨C, D, hC, hD, hCD⟩ :=
    (isWeaklyStable_gaussFractionField σ K c).exists_basis_norm_comparison pb.basis
  exact ⟨L, inferInstance, inferInstance, IntermediateField.adjoin.finiteDimensional hβ_int,
    inferInstance, pb.dim, inferInstance, pb.basis, hfin, C, D, hC, hD, hCD⟩

/-- In prime characteristic `p`, adjoining a `p`-th root of a coordinate variable `Xᵢ` produces a
nontrivial finite purely inseparable extension of `GaussFractionField σ K c` on which `spectralNorm`
is equivalent to the power-basis coordinate norm. -/
example (σ : Type u₁) (K : Type u₂) [Countable σ] [Nonempty σ]
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    let F := GaussFractionField σ K c
    ∃ (M : Type (max u₁ u₂)) (_ : Field M) (_ : Algebra F M) (_ : FiniteDimensional F M)
      (_ : IsPurelyInseparable F M) (n : ℕ) (_ : NeZero n) (b : Module.Basis (Fin n) F M),
      1 < Module.finrank F M ∧
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ y,
        b.norm y ≤ C * spectralNorm F M y ∧ spectralNorm F M y ≤ D * b.norm y := by
  classical
  have hp : p.Prime := Fact.out
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  have : ExpChar K p := .prime hp
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let i₀ : σ := Classical.arbitrary σ
  let X₀ : T := ⟨X i₀, isRestricted_X c i₀⟩
  let x₀ : F := algebraMap T F X₀
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
  obtain ⟨C, D, hC, hD, hCD⟩ :=
    (isWeaklyStable_gaussFractionField σ K c).exists_basis_norm_comparison pb.basis
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    pb.dim, inferInstance, pb.basis, hfin_gt, C, D, hC, hD, hCD⟩

end Examples

end TauCeti.MvPowerSeries
