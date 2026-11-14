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

For an integral full lattice, `A_L = L^∨ ⧸ L` is finite and the theta series of the dual lattice is
the sum of the coset theta series, `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ`
(`ZLattice.IsIntegral.thetaSeries_dual_eq_sum`), by splitting `L^∨` into the cosets of `L`.
Integrality is needed: whenever `L^∨ ≤ L` the discriminant group is trivial, so the sum over `A_L`
reduces to `θ_0 = Θ_L`, and for discrete `L` the identity `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` holds if
and only if `L` is integral (`ZLattice.thetaSeries_dual_eq_sum_iff_isIntegral_of_re_eq_zero`,
`ZLattice.forall_thetaSeries_dual_eq_sum_iff_isIntegral`). Concretely, for `L = ½ ℤ ⊆ ℝ` the dual
`L^∨ = 2 ℤ` is a proper sublattice of `L`, the discriminant group is trivial, and
`Θ_{2ℤ}(i) ≠ Θ_{½ℤ}(i)` (`ZLattice.thetaSeries_span_two_I_ne_thetaSeries_span_one_half_I`,
`ZLattice.thetaSeries_dual_span_one_half_I_ne_sum`).

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
* `ZLattice.IsIntegral.thetaSeries_dual_eq_sum`: `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` for integral `L`.
* `ZLattice.finsum_thetaCosetClass_of_dual_le`, `ZLattice.sum_thetaCosetClass_of_dual_le`: when
  `L^∨ ≤ L`, the sum of `θ_γ` over `A_L` reduces to `Θ_L`.
* `ZLattice.thetaSeries_dual_eq_sum_iff_isIntegral_of_re_eq_zero`,
  `ZLattice.forall_thetaSeries_dual_eq_sum_iff_isIntegral`: when `L^∨ ≤ L`, the dual decomposition
  `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` holds if and only if `L` is integral.
* `ZLattice.dual_span_one_half`, `ZLattice.dual_span_one_half_lt`,
  `ZLattice.instUniqueDiscriminantGroupSpanOneHalf`,
  `ZLattice.thetaSeries_span_two_I_ne_thetaSeries_span_one_half_I`,
  `ZLattice.thetaSeries_dual_span_one_half_I_ne_sum`: for `L = ½ ℤ ⊆ ℝ`, `L^∨ = 2 ℤ < L`, `A_L`
  is trivial, and `Θ_{2ℤ}(i) ≠ Θ_{½ℤ}(i)`.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 2.
-/

public section

open Complex Submodule
open scoped Pointwise Real ModularForm UpperHalfPlane

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

/-! ### Full lattices -/

section FullLattice

variable [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] {L}

/-- For an integral lattice `L`, the theta series of the dual lattice is the sum of the coset theta
series over the finite discriminant group `L^∨ ⧸ L`: `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ`. The discriminant
group of an integral lattice is finite (`IsIntegral.finite_discriminantGroup`), so a `Fintype`
instance is always available. -/
theorem IsIntegral.thetaSeries_dual_eq_sum (h : IsIntegral L) [Fintype (DiscriminantGroup L)]
    (τ : ℍ) : thetaSeries (dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ := by
  rw [← (hasSum_thetaCoset_out (dual L) (isIntegral_iff_le_dual.mp h) τ).tsum_eq, tsum_fintype]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← thetaCosetClass_mk, Submodule.Quotient.mk_out]

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

end FullLattice

/-! ### Dual contained in the lattice -/

section DualLe

variable {L}

/-- When `L^∨ ≤ L`, the finitely supported sum of the coset theta series over `A_L` is `Θ_L`. -/
theorem finsum_thetaCosetClass_of_dual_le (h : dual L ≤ L) (τ : ℍ) :
    ∑ᶠ γ : DiscriminantGroup L, thetaCosetClass L γ τ = thetaSeries L τ := by
  have : Subsingleton (DiscriminantGroup L) := subsingleton_discriminantGroup_iff.mpr h
  rw [finsum_eq_single _ (0 : DiscriminantGroup L) fun γ hγ => (hγ (Subsingleton.elim γ 0)).elim,
    thetaCosetClass_zero]

/-- When `L^∨ ≤ L`, the finite sum of the coset theta series over `A_L` is `Θ_L`. -/
theorem sum_thetaCosetClass_of_dual_le [Fintype (DiscriminantGroup L)] (h : dual L ≤ L) (τ : ℍ) :
    ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ = thetaSeries L τ := by
  rw [← finsum_eq_sum_of_fintype, finsum_thetaCosetClass_of_dual_le h]

variable [FiniteDimensional ℝ E] [DiscreteTopology L]

/-- If `L^∨ ≤ L` and `L` is not integral, then `re Θ_{L^∨}(τ) < re Θ_L(τ)` on the imaginary
axis. -/
theorem re_thetaSeries_dual_lt_of_dual_le_of_not_isIntegral (h : dual L ≤ L)
    (hL : ¬ IsIntegral L) {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries (dual L) τ).re < (thetaSeries L τ).re :=
  re_thetaSeries_lt_re_thetaSeries_of_lt (lt_of_le_not_ge h (mt isIntegral_iff_le_dual.mpr hL)) hτ

/-- For a discrete subgroup `L` with `L^∨ ≤ L`, at any point `τ` of the imaginary axis the identity
`Θ_{L^∨}(τ) = ∑ᶠ γ, θ_γ(τ)` holds if and only if `L` is integral. -/
theorem thetaSeries_dual_eq_finsum_iff_isIntegral_of_re_eq_zero (h : dual L ≤ L) {τ : ℍ}
    (hτ : τ.re = 0) :
    thetaSeries (dual L) τ = (∑ᶠ γ : DiscriminantGroup L, thetaCosetClass L γ τ) ↔
      IsIntegral L := by
  rw [finsum_thetaCosetClass_of_dual_le h, thetaSeries_eq_iff_of_le_of_re_eq_zero h hτ,
    isIntegral_iff_le_dual]
  exact ⟨fun heq => heq.ge, h.antisymm⟩

/-- For a discrete subgroup `L` with `L^∨ ≤ L`, at any point `τ` of the imaginary axis the identity
`Θ_{L^∨}(τ) = ∑ γ, θ_γ(τ)` holds if and only if `L` is integral. -/
theorem thetaSeries_dual_eq_sum_iff_isIntegral_of_re_eq_zero [Fintype (DiscriminantGroup L)]
    (h : dual L ≤ L) {τ : ℍ} (hτ : τ.re = 0) :
    thetaSeries (dual L) τ = (∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ) ↔ IsIntegral L := by
  rw [← finsum_eq_sum_of_fintype,
    thetaSeries_dual_eq_finsum_iff_isIntegral_of_re_eq_zero h hτ]

/-- For a discrete subgroup `L` with `L^∨ ≤ L`, the dual decomposition
`∀ τ, Θ_{L^∨}(τ) = ∑ᶠ γ, θ_γ(τ)` holds if and only if `L` is integral. -/
theorem forall_thetaSeries_dual_eq_finsum_iff_isIntegral (h : dual L ≤ L) :
    (∀ τ : ℍ, thetaSeries (dual L) τ = ∑ᶠ γ : DiscriminantGroup L, thetaCosetClass L γ τ) ↔
      IsIntegral L :=
  ⟨fun hall => (thetaSeries_dual_eq_finsum_iff_isIntegral_of_re_eq_zero h UpperHalfPlane.I_re).mp
    (hall UpperHalfPlane.I),
    fun hL τ => by
      rw [finsum_thetaCosetClass_of_dual_le h, h.antisymm (isIntegral_iff_le_dual.mp hL)]⟩

/-- For a discrete subgroup `L` with `L^∨ ≤ L`, the dual decomposition
`∀ τ, Θ_{L^∨}(τ) = ∑ γ, θ_γ(τ)` holds if and only if `L` is integral. -/
theorem forall_thetaSeries_dual_eq_sum_iff_isIntegral [Fintype (DiscriminantGroup L)]
    (h : dual L ≤ L) :
    (∀ τ : ℍ, thetaSeries (dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ) ↔
      IsIntegral L := by
  simp_rw [← finsum_eq_sum_of_fintype]
  exact forall_thetaSeries_dual_eq_finsum_iff_isIntegral h

end DualLe

/-! ### Non-integral rank-one boundary example -/

section NonIntegralBoundary

/-- The dual of the rank-one lattice `½ ℤ ⊆ ℝ` is `2 ℤ`. -/
theorem dual_span_one_half :
    dual (span ℤ {1 / 2} : Submodule ℤ ℝ) = span ℤ {2} := by
  rw [dual_span_singleton (by norm_num)]
  norm_num

/-- In `ℝ`, `2 ℤ` is a proper sublattice of `½ ℤ`. -/
theorem span_two_lt_span_one_half :
    (span ℤ {2} : Submodule ℤ ℝ) < span ℤ {1 / 2} := by
  refine lt_of_le_not_ge
    (span_le.mpr (Set.singleton_subset_iff.mpr (mem_span_singleton.mpr ⟨4, ?_⟩))) fun h => ?_
  · rw [zsmul_eq_mul]
    norm_num
  · obtain ⟨n, hn⟩ := mem_span_singleton.mp (h (mem_span_singleton_self (1 / 2)))
    rw [zsmul_eq_mul] at hn
    have h4 : (4 : ℝ) * n = 1 := by linarith
    have h4' : 4 * n = 1 := by exact_mod_cast h4
    omega

/-- The dual `2 ℤ` of `½ ℤ ⊆ ℝ` is strictly contained in `½ ℤ`. -/
theorem dual_span_one_half_lt :
    dual (span ℤ {1 / 2} : Submodule ℤ ℝ) < span ℤ {1 / 2} :=
  dual_span_one_half ▸ span_two_lt_span_one_half

/-- The lattice `½ ℤ ⊆ ℝ` is not integral. -/
theorem not_isIntegral_span_one_half :
    ¬ IsIntegral (span ℤ {1 / 2} : Submodule ℤ ℝ) :=
  mt isIntegral_iff_le_dual.mp dual_span_one_half_lt.not_ge

/-- The discriminant group `(½ ℤ)^∨ ⧸ ((½ ℤ) ∩ (½ ℤ)^∨)` of `½ ℤ ⊆ ℝ` has a single element, the
zero class. -/
noncomputable instance instUniqueDiscriminantGroupSpanOneHalf :
    Unique (DiscriminantGroup (span ℤ {1 / 2} : Submodule ℤ ℝ)) :=
  have : Subsingleton (DiscriminantGroup (span ℤ {1 / 2} : Submodule ℤ ℝ)) :=
    subsingleton_discriminantGroup_iff.mpr dual_span_one_half_lt.le
  uniqueOfSubsingleton 0

/-- The discriminant group of `½ ℤ ⊆ ℝ` has cardinality `1`. -/
theorem card_discriminantGroup_span_one_half :
    Nat.card (DiscriminantGroup (span ℤ {1 / 2} : Submodule ℤ ℝ)) = 1 :=
  Nat.card_unique

/-- On the imaginary axis, `re Θ_{2ℤ}(τ) < re Θ_{½ℤ}(τ)`. -/
theorem re_thetaSeries_span_two_lt_re_thetaSeries_span_one_half {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries (span ℤ {2} : Submodule ℤ ℝ) τ).re <
      (thetaSeries (span ℤ {1 / 2} : Submodule ℤ ℝ) τ).re := by
  have : NeZero (1 / 2 : ℝ) := ⟨by norm_num⟩
  have hsmul : (span ℤ {1 / 2} : Submodule ℤ ℝ) = (1 / 2 : ℝ) • span ℤ {1} := by
    simp [smul_span]
  have : DiscreteTopology (span ℤ {1 / 2} : Submodule ℤ ℝ) := by
    rw [hsmul]
    infer_instance
  exact re_thetaSeries_lt_re_thetaSeries_of_lt span_two_lt_span_one_half hτ

/-- At `τ = i`, `Θ_{2ℤ}(i) ≠ Θ_{½ℤ}(i)`. -/
theorem thetaSeries_span_two_I_ne_thetaSeries_span_one_half_I :
    thetaSeries (span ℤ {2} : Submodule ℤ ℝ) UpperHalfPlane.I ≠
      thetaSeries (span ℤ {1 / 2} : Submodule ℤ ℝ) UpperHalfPlane.I := fun h =>
  (re_thetaSeries_span_two_lt_re_thetaSeries_span_one_half UpperHalfPlane.I_re).ne
    (congrArg Complex.re h)

/-- The theta series `Θ_{2ℤ}` and `Θ_{½ℤ}` are distinct functions on `ℍ`. -/
theorem thetaSeries_span_two_ne_thetaSeries_span_one_half :
    thetaSeries (span ℤ {2} : Submodule ℤ ℝ) ≠
      thetaSeries (span ℤ {1 / 2} : Submodule ℤ ℝ) := fun h =>
  thetaSeries_span_two_I_ne_thetaSeries_span_one_half_I (congrFun h UpperHalfPlane.I)

/-- For `L = ½ ℤ ⊆ ℝ`, `Θ_{L^∨}(i) ≠ ∑ᶠ γ : A_L, θ_γ(i)`: the dual theta decomposition fails
without integrality of `L`. -/
theorem thetaSeries_dual_span_one_half_I_ne_finsum :
    thetaSeries (dual (span ℤ {1 / 2} : Submodule ℤ ℝ)) UpperHalfPlane.I ≠
      ∑ᶠ γ : DiscriminantGroup (span ℤ {1 / 2} : Submodule ℤ ℝ),
        thetaCosetClass (span ℤ {1 / 2}) γ UpperHalfPlane.I := by
  rw [dual_span_one_half, finsum_thetaCosetClass_of_dual_le dual_span_one_half_lt.le]
  exact thetaSeries_span_two_I_ne_thetaSeries_span_one_half_I

/-- For `L = ½ ℤ ⊆ ℝ`, `Θ_{L^∨}(i) ≠ ∑ γ : A_L, θ_γ(i)`: `IsIntegral.thetaSeries_dual_eq_sum`
fails without the hypothesis `IsIntegral L`. -/
theorem thetaSeries_dual_span_one_half_I_ne_sum :
    thetaSeries (dual (span ℤ {1 / 2} : Submodule ℤ ℝ)) UpperHalfPlane.I ≠
      ∑ γ : DiscriminantGroup (span ℤ {1 / 2} : Submodule ℤ ℝ),
        thetaCosetClass (span ℤ {1 / 2}) γ UpperHalfPlane.I := by
  rw [← finsum_eq_sum_of_fintype]
  exact thetaSeries_dual_span_one_half_I_ne_finsum

end NonIntegralBoundary

end ZLattice
