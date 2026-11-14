/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.DiscriminantCharacter
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Translation
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp

/-!
# Coset theta series on the discriminant group

Let `L` be a lattice in a real inner product space `E`, with dual lattice `L^∨ = ZLattice.dual L`
and discriminant group `A_L = L^∨ ⧸ (L ∩ L^∨)` (`ZLattice.DiscriminantGroup L`). The theta series
`θ_{γ+L}` of a translate depends only on the class of `γ` modulo `L`
(`ZLattice.thetaCoset_eq_of_sub_mem`), so the coset theta series descend to a family
`(θ_γ)_{γ ∈ A_L}` indexed by the discriminant group, `ZLattice.thetaCosetClass L`. This descent
needs no hypothesis on `L`. This is the family that the vector-valued inversion law of coset theta
series is stated for. It satisfies `θ_0 = Θ_L` and `θ_{-γ} = θ_γ`; in particular, whenever
`A_L` has an element `γ ≠ -γ`, the family is not linearly independent.

For an even lattice `L` (in arbitrary dimension, without discreteness or fullness), every coset
theta series `θ_γ` (`γ ∈ A_L`) has period `level L` and is invariant under `T ^ level L` in every
weight (`ZLattice.IsEven.thetaCosetClass_slash_T_pow_level`), descending from the
representative-level invariance `ZLattice.IsEven.thetaCoset_slash_T_pow_level`. When `L` is an even
full lattice, the modular translation `T : τ ↦ τ + 1` acts on `θ_γ` with eigenvalue `e(q_L(γ))`
(`ZLattice.IsEven.thetaCosetClass_slash_T`), where `e(q_L(γ))` is
`ZLattice.IsEven.discriminantQuadraticChar`, and `level L` is the least positive exponent killing
all of these eigenvalues (`ZLattice.IsEven.level_dvd_iff_discriminantQuadraticChar_pow_eq_one`).

Whenever `L` is discrete and `A_L` is finite, the sum lattice `L ⊔ L^∨` is discrete and splitting
`L ⊔ L^∨` into cosets of `L` via `ZLattice.discriminantGroupEquivQuotientSup` gives
`Θ_{L ⊔ L^∨} = ∑_{γ ∈ A_L} θ_γ` (`ZLattice.thetaSeries_sup_dual_eq_sum`). When `L` is integral,
`L ⊔ L^∨ = L^∨`, recovering `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ`
(`ZLattice.IsIntegral.thetaSeries_dual_eq_sum`).
Conversely, on the imaginary axis `re τ = 0`, sublattice monotonicity yields
`re Θ_{L^∨}(τ) ≤ ∑_{γ ∈ A_L} re θ_γ(τ)` (`ZLattice.re_thetaSeries_dual_le_sum`), and the identity
`Θ_{L^∨}(τ) = ∑_{γ ∈ A_L} θ_γ(τ)` holds if and only if `L` is integral
(`ZLattice.thetaSeries_dual_eq_sum_iff_isIntegral`). In particular, when `L^∨ < L` the discriminant
group is trivial so the coset sum collapses to `Θ_L`, while `Θ_{L^∨}(τ) ≠ Θ_L(τ)` on the imaginary
axis (`ZLattice.thetaSeries_dual_ne_thetaSeries_of_dual_lt`): for `L = 2⁻¹ ℤ ⊆ ℝ`, `L^∨ = 2 ℤ < L`,
`Θ_{2ℤ}(i) ≠ Θ_{2⁻¹ℤ}(i)` (`ZLattice.thetaSeries_span_two_ne_thetaSeries_span_inv_two_I`), and
`Θ_{L^∨}(i) ≠ ∑_{γ ∈ A_L} θ_γ(i)` (`ZLattice.thetaSeries_dual_span_inv_two_ne_sum_I`).

## Main definitions

* `ZLattice.thetaCosetClass L`: the coset theta series `θ_γ` of a class `γ` of the discriminant
  group of `L`.

## Main statements

* `ZLattice.thetaCosetClass_mk`: `θ_γ` is the theta series of the translate `γ + L`.
* `ZLattice.thetaCosetClass_zero`, `ZLattice.thetaCosetClass_neg`: `θ_0 = Θ_L`, `θ_{-γ} = θ_γ`.
* `ZLattice.IsEven.thetaCosetClass_slash_T_pow_level`: `θ_γ` is invariant under `T ^ level L` in
  every weight.
* `ZLattice.IsEven.thetaCosetClass_slash_T`, `ZLattice.IsEven.thetaCosetClass_slash_T_zpow`:
  `θ_γ ∣[k] T ^ n = e(q_L(γ))^n • θ_γ` for an even full lattice `L`.
* `ZLattice.thetaSeries_sup_dual_eq_sum`: `Θ_{L ⊔ L^∨} = ∑_{γ ∈ A_L} θ_γ` whenever `L` is discrete
  and `A_L` is finite.
* `ZLattice.IsIntegral.thetaSeries_dual_eq_sum`: `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` for integral `L`.
* `ZLattice.thetaSeries_dual_eq_sum_iff_isIntegral`: on the imaginary axis,
  `Θ_{L^∨}(τ) = ∑_{γ ∈ A_L} θ_γ(τ)` holds if and only if `L` is integral.
* `ZLattice.thetaSeries_span_two_ne_thetaSeries_span_inv_two_I`,
  `ZLattice.thetaSeries_dual_span_inv_two_ne_sum_I`: for `L = 2⁻¹ ℤ ⊆ ℝ`, `Θ_{2ℤ}(i) ≠ Θ_{2⁻¹ℤ}(i)`
  and the dual decomposition fails at `i`.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 2.
* J.-P. Serre, *A Course in Arithmetic*, Springer, 1973, Chapter VII, §6.
-/

public section

open Complex Submodule
open scoped Real ModularForm UpperHalfPlane

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coset theta series `θ_γ = θ_{γ+L}` of a class `γ` of the discriminant group
`L^∨ ⧸ (L ∩ L^∨)` of `L`: the theta series `thetaCoset L x` of the translate by any representative
`x ∈ L^∨` of `γ` (`thetaCosetClass_mk`). -/
noncomputable def thetaCosetClass (L : Submodule ℤ E) (γ : DiscriminantGroup L) : ℍ → ℂ :=
  Quotient.liftOn' γ (fun x : dual L => thetaCoset L (x : E)) fun x y h =>
    thetaCoset_eq_of_sub_mem L ((discriminantGroup_mk_eq_mk_iff x y).mp (Quotient.sound' h))

variable (L : Submodule ℤ E)

/-- The coset theta series of the class of `x ∈ L^∨` is the theta series of the translate
`x + L`. -/
@[simp]
theorem thetaCosetClass_mk (x : dual L) :
    thetaCosetClass L (Submodule.Quotient.mk x) = thetaCoset L (x : E) :=
  (rfl)

/-- The coset theta series of the zero class is the theta series of `L`. -/
@[simp]
theorem thetaCosetClass_zero : thetaCosetClass L 0 = thetaSeries L := by
  rw [← Submodule.Quotient.mk_zero, thetaCosetClass_mk, ZeroMemClass.coe_zero, thetaCoset_zero]

/-- The coset theta series of the classes `-γ` and `γ` agree. -/
@[simp]
theorem thetaCosetClass_neg (γ : DiscriminantGroup L) :
    thetaCosetClass L (-γ) = thetaCosetClass L γ := by
  induction γ using Submodule.Quotient.induction_on with
  | H x => rw [← Submodule.Quotient.mk_neg, thetaCosetClass_mk, thetaCosetClass_mk,
      NegMemClass.coe_neg, thetaCoset_neg]

/-! ### Translation invariance at the level -/

section LevelTranslation

variable {L}

namespace IsEven

/-- For an even lattice `L` and `γ : DiscriminantGroup L`, every integer multiple of `level L` is a
period of `θ_γ`. -/
theorem thetaCosetClass_intCast_vadd_of_level_dvd (hL : IsEven L) (γ : DiscriminantGroup L)
    {N : ℤ} (hN : (level L : ℤ) ∣ N) (τ : ℍ) :
    thetaCosetClass L γ ((N : ℝ) +ᵥ τ) = thetaCosetClass L γ τ := by
  induction γ using Submodule.Quotient.induction_on with
  | H x => exact hL.thetaCoset_intCast_vadd_of_level_dvd x.2 hN τ

/-- For an even lattice `L` and `γ : DiscriminantGroup L`, `θ_γ` has period `level L`. -/
@[simp]
theorem thetaCosetClass_level_vadd (hL : IsEven L) (γ : DiscriminantGroup L) (τ : ℍ) :
    thetaCosetClass L γ ((level L : ℝ) +ᵥ τ) = thetaCosetClass L γ τ := by
  simpa using hL.thetaCosetClass_intCast_vadd_of_level_dvd γ dvd_rfl τ

/-- For an even lattice `L` and `γ : DiscriminantGroup L`, `θ_γ` is invariant under `T ^ N` in
every weight whenever `(level L : ℤ) ∣ N`. -/
theorem thetaCosetClass_slash_T_zpow_of_level_dvd (hL : IsEven L) (γ : DiscriminantGroup L)
    (k : ℤ) {N : ℤ} (hN : (level L : ℤ) ∣ N) :
    thetaCosetClass L γ ∣[k] (ModularGroup.T ^ N) = thetaCosetClass L γ := by
  induction γ using Submodule.Quotient.induction_on with
  | H x => exact hL.thetaCoset_slash_T_zpow_of_level_dvd x.2 k hN

/-- For an even lattice `L` and `γ : DiscriminantGroup L`, `θ_γ` is invariant under
`T ^ (level L : ℤ)` in every weight. -/
theorem thetaCosetClass_slash_T_zpow_level (hL : IsEven L) (γ : DiscriminantGroup L) (k : ℤ) :
    thetaCosetClass L γ ∣[k] (ModularGroup.T ^ (level L : ℤ)) = thetaCosetClass L γ :=
  hL.thetaCosetClass_slash_T_zpow_of_level_dvd γ k dvd_rfl

/-- For an even lattice `L` and `γ : DiscriminantGroup L`, `θ_γ` is invariant under `T ^ level L`
in every weight. -/
@[simp]
theorem thetaCosetClass_slash_T_pow_level (hL : IsEven L) (γ : DiscriminantGroup L) (k : ℤ) :
    thetaCosetClass L γ ∣[k] (ModularGroup.T ^ level L) = thetaCosetClass L γ := by
  rw [← zpow_natCast, hL.thetaCosetClass_slash_T_zpow_level γ k]

end IsEven

end LevelTranslation

/-! ### Coset decomposition and integrality -/

section DualDecomposition

variable {L}

/-- When `L^∨ ≤ L`, the discriminant group is trivial and the sum of the coset theta series
collapses to `θ_0 = Θ_L`. -/
theorem sum_thetaCosetClass_eq_thetaSeries_of_dual_le (h : dual L ≤ L)
    [Fintype (DiscriminantGroup L)] (τ : ℍ) :
    ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ = thetaSeries L τ := by
  have : Subsingleton (DiscriminantGroup L) := subsingleton_discriminantGroup_iff.mpr h
  rw [Fintype.sum_subsingleton _ 0, thetaCosetClass_zero]

variable [FiniteDimensional ℝ E]

/-- Whenever `L` is discrete and its discriminant group `A_L = L^∨ ⧸ (L ∩ L^∨)` is finite, the sum
lattice `L ⊔ L^∨` is discrete and its theta series is the sum of the coset theta series over `A_L`:
`Θ_{L ⊔ L^∨} = ∑_{γ ∈ A_L} θ_γ`. -/
theorem thetaSeries_sup_dual_eq_sum [DiscreteTopology L] [Fintype (DiscriminantGroup L)] (τ : ℍ) :
    thetaSeries (L ⊔ dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ := by
  have : Fintype (↥(L ⊔ dual L) ⧸ L.submoduleOf (L ⊔ dual L)) :=
    Fintype.ofEquiv _ (discriminantGroupEquivQuotientSup L).toEquiv
  rw [← (hasSum_thetaCoset_out (L ⊔ dual L) le_sup_left τ).tsum_eq, tsum_fintype,
    ← (discriminantGroupEquivQuotientSup L).toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  induction γ using Submodule.Quotient.induction_on with
  | H x =>
    rw [LinearEquiv.coe_toEquiv, discriminantGroupEquivQuotientSup_mk, thetaCosetClass_mk]
    refine congrFun (thetaCoset_eq_of_sub_mem L ?_) τ
    have hq : Submodule.Quotient.mk
        (Quotient.out (Submodule.Quotient.mk (⟨x, mem_sup_right x.2⟩ : ↥(L ⊔ dual L)) :
          ↥(L ⊔ dual L) ⧸ L.submoduleOf (L ⊔ dual L))) =
        Submodule.Quotient.mk (⟨x, mem_sup_right x.2⟩ : ↥(L ⊔ dual L)) :=
      Submodule.Quotient.mk_out _
    simpa [submoduleOf] using (Submodule.Quotient.eq _).mp hq

/-- For an integral lattice `L`, the theta series of the dual lattice is the sum of the coset theta
series over the discriminant group `L^∨ ⧸ L`: `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ`. For an integral full
lattice the discriminant group is finite (`IsIntegral.finite_discriminantGroup`), so a `Fintype`
instance is always available. -/
theorem IsIntegral.thetaSeries_dual_eq_sum (h : IsIntegral L) [Fintype (DiscriminantGroup L)]
    (τ : ℍ) : thetaSeries (dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ := by
  have := h.discreteTopology
  rw [← sup_eq_right.mpr (isIntegral_iff_le_dual.mp h), thetaSeries_sup_dual_eq_sum]

/-- On the imaginary axis, the real part of `Θ_{L^∨}(τ)` is at most the sum of the real parts of
the coset theta series over the discriminant group. -/
theorem re_thetaSeries_dual_le_sum [DiscreteTopology L] [Fintype (DiscriminantGroup L)]
    {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries (dual L) τ).re ≤ ∑ γ : DiscriminantGroup L, (thetaCosetClass L γ τ).re := by
  refine (re_thetaSeries_mono (L := L ⊔ dual L) le_sup_right hτ).trans_eq ?_
  rw [thetaSeries_sup_dual_eq_sum, Complex.re_sum]

/-- On the imaginary axis, `(thetaSeries (dual L) τ).re < ∑_{γ ∈ A_L} (thetaCosetClass L γ τ).re`
holds if and only if `L` is not integral. -/
theorem re_thetaSeries_dual_lt_sum_iff_not_isIntegral [DiscreteTopology L]
    [Fintype (DiscriminantGroup L)] {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries (dual L) τ).re < ∑ γ : DiscriminantGroup L, (thetaCosetClass L γ τ).re ↔
      ¬ IsIntegral L := by
  rw [← Complex.re_sum, ← thetaSeries_sup_dual_eq_sum,
    re_thetaSeries_lt_iff_lt (L := L ⊔ dual L) le_sup_right hτ, le_sup_right.lt_iff_ne, ne_eq,
    eq_comm, sup_eq_right, ← isIntegral_iff_le_dual]

/-- On the imaginary axis, the dual decomposition `Θ_{L^∨}(τ) = ∑_{γ ∈ A_L} θ_γ(τ)` holds if and
only if `L` is integral. -/
theorem thetaSeries_dual_eq_sum_iff_isIntegral [DiscreteTopology L] [Fintype (DiscriminantGroup L)]
    {τ : ℍ} (hτ : τ.re = 0) :
    thetaSeries (dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ ↔ IsIntegral L := by
  rw [← thetaSeries_sup_dual_eq_sum,
    thetaSeries_eq_iff_eq_of_re_eq_zero (L := L ⊔ dual L) le_sup_right hτ, eq_comm, sup_eq_right,
    ← isIntegral_iff_le_dual]

/-- When `L^∨ < L` and `L` is discrete, `Θ_{L^∨}(τ) ≠ Θ_L(τ)` at every point of the imaginary
axis. -/
theorem thetaSeries_dual_ne_thetaSeries_of_dual_lt [DiscreteTopology L] (h : dual L < L)
    {τ : ℍ} (hτ : τ.re = 0) : thetaSeries (dual L) τ ≠ thetaSeries L τ :=
  thetaSeries_ne_of_lt_of_re_eq_zero h hτ

end DualDecomposition

/-! ### Even full lattices -/

section EvenFull

variable [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] {L}

namespace IsEven

/-- The translation law of a coset theta series on the discriminant group of an even full lattice:
for `γ : DiscriminantGroup L` and `n : ℤ`, `θ_γ(τ + n) = e(q_L(γ))^n θ_γ(τ)`. -/
theorem thetaCosetClass_intCast_vadd (hL : IsEven L) (γ : DiscriminantGroup L) (n : ℤ) (τ : ℍ) :
    thetaCosetClass L γ ((n : ℝ) +ᵥ τ) =
      hL.discriminantQuadraticChar γ ^ n * thetaCosetClass L γ τ := by
  induction γ using Submodule.Quotient.induction_on with
  | H x =>
    rw [thetaCosetClass_mk, hL.thetaCoset_intCast_vadd x.2, hL.discriminantQuadraticChar_mk,
      ← Complex.exp_int_mul]
    congr 2
    ring

/-- For an even full lattice `L` and `γ : DiscriminantGroup L`,
`θ_γ(τ + 1) = e(q_L(γ)) θ_γ(τ)`. -/
theorem thetaCosetClass_one_vadd (hL : IsEven L) (γ : DiscriminantGroup L) (τ : ℍ) :
    thetaCosetClass L γ ((1 : ℝ) +ᵥ τ) =
      hL.discriminantQuadraticChar γ * thetaCosetClass L γ τ := by
  simpa using hL.thetaCosetClass_intCast_vadd γ 1 τ

/-- In slash form, `θ_γ ∣[k] T ^ n = e(q_L(γ))^n • θ_γ` for an even full lattice `L` and
`γ : DiscriminantGroup L`. -/
theorem thetaCosetClass_slash_T_zpow (hL : IsEven L) (γ : DiscriminantGroup L) (k n : ℤ) :
    thetaCosetClass L γ ∣[k] (ModularGroup.T ^ n) =
      (hL.discriminantQuadraticChar γ ^ n) • thetaCosetClass L γ := by
  induction γ using Submodule.Quotient.induction_on with
  | H x =>
    rw [thetaCosetClass_mk, hL.thetaCoset_slash_T_zpow x.2, hL.discriminantQuadraticChar_mk,
      ← Complex.exp_int_mul]
    congr 2
    ring

/-- In slash form, `θ_γ ∣[k] T = e(q_L(γ)) • θ_γ` for an even full lattice `L` and
`γ : DiscriminantGroup L`. -/
theorem thetaCosetClass_slash_T (hL : IsEven L) (γ : DiscriminantGroup L) (k : ℤ) :
    thetaCosetClass L γ ∣[k] ModularGroup.T =
      hL.discriminantQuadraticChar γ • thetaCosetClass L γ := by
  simpa using hL.thetaCosetClass_slash_T_zpow γ k 1

end IsEven

end EvenFull

/-! ### Non-integral failure for `2⁻¹ ℤ` -/

section HalfInt

/-- On the imaginary axis, `re Θ_{2ℤ}(τ) < re Θ_{2⁻¹ℤ}(τ)`. -/
theorem re_thetaSeries_span_two_lt_span_inv_two {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) τ).re <
      (thetaSeries (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) τ).re := by
  have : DiscreteTopology (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) :=
    discreteTopology_of_norm_sq_mem_int_mul (c := 4⁻¹) (by norm_num) fun x hx ↦ by
      obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hx
      refine ⟨m ^ 2, ?_⟩
      simp only [zsmul_eq_mul, Real.norm_eq_abs, mul_pow, sq_abs, Int.cast_pow]
      ring
  exact re_thetaSeries_strictMono span_two_lt_span_inv_two hτ

/-- On the imaginary axis, `Θ_{2ℤ}(τ) ≠ Θ_{2⁻¹ℤ}(τ)`. -/
theorem thetaSeries_span_two_ne_thetaSeries_span_inv_two {τ : ℍ} (hτ : τ.re = 0) :
    thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) τ ≠
      thetaSeries (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) τ :=
  fun h ↦ (re_thetaSeries_span_two_lt_span_inv_two hτ).ne (congrArg Complex.re h)

/-- At `τ = i`, `Θ_{2ℤ}(i) ≠ Θ_{2⁻¹ℤ}(i)`. -/
theorem thetaSeries_span_two_ne_thetaSeries_span_inv_two_I :
    thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) UpperHalfPlane.I ≠
      thetaSeries (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) UpperHalfPlane.I :=
  thetaSeries_span_two_ne_thetaSeries_span_inv_two (by simp)

/-- On the imaginary axis, the non-integral lattice `L = 2⁻¹ ℤ ⊆ ℝ` violates the dual coset
decomposition `Θ_{L^∨}(τ) = ∑_{γ ∈ A_L} θ_γ(τ)`. -/
theorem thetaSeries_dual_span_inv_two_ne_sum {τ : ℍ} (hτ : τ.re = 0) :
    thetaSeries (dual (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ)) τ ≠
      ∑ γ : DiscriminantGroup (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ),
        thetaCosetClass (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) γ τ := by
  rw [sum_thetaCosetClass_eq_thetaSeries_of_dual_le
    (dual_span_inv_two.trans_le span_two_lt_span_inv_two.le), dual_span_inv_two]
  exact thetaSeries_span_two_ne_thetaSeries_span_inv_two hτ

/-- At `τ = i`, the non-integral lattice `L = 2⁻¹ ℤ ⊆ ℝ` violates the dual coset decomposition
`Θ_{L^∨}(i) = ∑_{γ ∈ A_L} θ_γ(i)`. -/
theorem thetaSeries_dual_span_inv_two_ne_sum_I :
    thetaSeries (dual (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ)) UpperHalfPlane.I ≠
      ∑ γ : DiscriminantGroup (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ),
        thetaCosetClass (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) γ UpperHalfPlane.I :=
  thetaSeries_dual_span_inv_two_ne_sum (by simp)

end HalfInt

end ZLattice
