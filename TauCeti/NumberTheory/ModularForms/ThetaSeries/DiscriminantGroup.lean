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

For any discrete subgroup `L` with finite discriminant group `A_L`, the second isomorphism theorem
identifies `A_L` with `(L + L^∨) ⧸ L`, so the sum `∑_{γ ∈ A_L} θ_γ` is always the theta series of
`L + L^∨` (`ZLattice.thetaSeries_sup_dual_eq_sum`). When `L` is integral, `L + L^∨ = L^∨`, giving
`Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` (`ZLattice.IsIntegral.thetaSeries_dual_eq_sum`). Conversely, when `L`
is not integral, `L^∨ < L + L^∨`, so on the imaginary axis `Θ_{L^∨}` is strictly smaller than
`∑_{γ ∈ A_L} θ_γ` (`ZLattice.re_thetaSeries_dual_lt_sum_of_not_isIntegral`), and the dual
decomposition `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` holds if and only if `L` is integral
(`ZLattice.thetaSeries_dual_eq_sum_iff_isIntegral`). In particular, for `L = ½ ℤ ⊆ ℝ` the dual
`L^∨ = 2 ℤ` lies strictly inside `L`, the discriminant group is trivial, and `Θ_{2ℤ}(i) ≠ Θ_{½ℤ}(i)`
(proved in `TauCeti/NumberTheory/ModularForms/ThetaSeries/RankOne.lean`).

## Main definitions

* `ZLattice.thetaCosetClass L`: the coset theta series `θ_γ` of a class `γ` of the discriminant
  group of `L`.

## Main statements

* `ZLattice.thetaCosetClass_mk`: `θ_γ` is the theta series of the translate `γ + L`.
* `ZLattice.thetaCosetClass_zero`, `ZLattice.thetaCosetClass_neg`,
  `ZLattice.sum_thetaCosetClass_of_subsingleton`: `θ_0 = Θ_L`, `θ_{-γ} = θ_γ`, and
  `∑_{γ ∈ A_L} θ_γ = Θ_L` when `A_L` is trivial.
* `ZLattice.IsEven.thetaCosetClass_slash_T_pow_level`: `θ_γ` is invariant under `T ^ level L` in
  every weight.
* `ZLattice.IsEven.thetaCosetClass_slash_T`, `ZLattice.IsEven.thetaCosetClass_slash_T_zpow`:
  `θ_γ ∣[k] T ^ n = e(q_L(γ))^n • θ_γ` for an even full lattice `L`.
* `ZLattice.thetaSeries_sup_dual_eq_sum`: `Θ_{L + L^∨} = ∑_{γ ∈ A_L} θ_γ` whenever `L` is discrete
  and `A_L` is finite.
* `ZLattice.IsIntegral.thetaSeries_dual_eq_sum`: `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` for integral `L`.
* `ZLattice.re_thetaSeries_dual_le_sum`, `ZLattice.re_thetaSeries_dual_lt_sum_of_not_isIntegral`,
  `ZLattice.thetaSeries_dual_apply_eq_sum_iff_isIntegral`,
  `ZLattice.thetaSeries_dual_eq_sum_iff_isIntegral`: on the imaginary axis
  `Θ_{L^∨} ≤ ∑_{γ ∈ A_L} θ_γ` with equality if and only if `L` is integral.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 2.
-/

public section

open Complex
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

/-- When the discriminant group `A_L` is trivial (`L^∨ ≤ L`), the sum of the coset theta series
over `A_L` reduces to the single zero-class term `θ_0 = Θ_L`. -/
theorem sum_thetaCosetClass_of_subsingleton [Fintype (DiscriminantGroup L)]
    [Subsingleton (DiscriminantGroup L)] :
    ∑ γ : DiscriminantGroup L, thetaCosetClass L γ = thetaSeries L := by
  let : Unique (DiscriminantGroup L) := ⟨⟨0⟩, fun _ ↦ Subsingleton.elim _ _⟩
  rw [Fintype.sum_unique, show (default : DiscriminantGroup L) = 0 from rfl, thetaCosetClass_zero]

/-- Pointwise form of `ZLattice.sum_thetaCosetClass_of_subsingleton`. -/
theorem sum_thetaCosetClass_apply_of_subsingleton [Fintype (DiscriminantGroup L)]
    [Subsingleton (DiscriminantGroup L)] (τ : ℍ) :
    ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ = thetaSeries L τ := by
  simpa using congrFun (sum_thetaCosetClass_of_subsingleton L) τ

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

/-! ### Dual coset decomposition and full lattices -/

variable [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] {L}

omit [IsZLattice ℝ L] in
/-- For a discrete subgroup `L` of a finite-dimensional real inner product space whose discriminant
group `A_L = L^∨ ⧸ (L ∩ L^∨)` is finite, `L + L^∨` is discrete and its theta series is the sum of
the coset theta series over `A_L`: `Θ_{L + L^∨} = ∑_{γ ∈ A_L} θ_γ`. -/
theorem thetaSeries_sup_dual_eq_sum [Fintype (DiscriminantGroup L)] (τ : ℍ) :
    thetaSeries (L ⊔ dual L : Submodule ℤ E) τ =
      ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ := by
  have : DiscreteTopology (L ⊔ dual L : Submodule ℤ E) :=
    discreteTopology_sup_dual_of_finite_discriminantGroup
  let : Fintype ((L ⊔ dual L : Submodule ℤ E) ⧸ L.submoduleOf (L ⊔ dual L)) :=
    Fintype.ofEquiv _ (discriminantGroupEquivSupQuotient L).toEquiv
  rw [← (hasSum_thetaCoset_out (L ⊔ dual L) le_sup_left τ).tsum_eq, tsum_fintype,
    ← (discriminantGroupEquivSupQuotient L).toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  induction γ using Submodule.Quotient.induction_on with
  | H x =>
    rw [LinearEquiv.coe_toEquiv, discriminantGroupEquivSupQuotient_mk, thetaCosetClass_mk]
    refine congrFun (thetaCoset_eq_of_sub_mem L ?_) τ
    have hout := (Submodule.Quotient.eq _).mp (Submodule.Quotient.mk_out (Submodule.Quotient.mk
      (p := L.submoduleOf (L ⊔ dual L)) ⟨(x : E), Submodule.mem_sup_right x.2⟩))
    simpa [Submodule.submoduleOf] using hout

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- For an integral lattice `L`, the theta series of the dual lattice is the sum of the coset theta
series over the finite discriminant group `L^∨ ⧸ L`: `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ`. The discriminant
group of an integral full lattice is finite (`IsIntegral.finite_discriminantGroup`), so a `Fintype`
instance is always available. -/
theorem IsIntegral.thetaSeries_dual_eq_sum (h : IsIntegral L) [Fintype (DiscriminantGroup L)]
    (τ : ℍ) : thetaSeries (dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ := by
  have := h.discreteTopology
  rw [← sup_eq_right.mpr (isIntegral_iff_le_dual.mp h), thetaSeries_sup_dual_eq_sum]

omit [IsZLattice ℝ L] in
/-- On the imaginary axis, the theta series of `L^∨` never exceeds the sum of the coset theta
series over a finite discriminant group `A_L`: `L^∨ ≤ L + L^∨`, and `∑_{γ ∈ A_L} θ_γ` is the theta
series of `L + L^∨` (`ZLattice.thetaSeries_sup_dual_eq_sum`). -/
theorem re_thetaSeries_dual_le_sum [Fintype (DiscriminantGroup L)] {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries (dual L) τ).re ≤
      (∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ).re := by
  have : DiscreteTopology (L ⊔ dual L : Submodule ℤ E) :=
    discreteTopology_sup_dual_of_finite_discriminantGroup
  rw [← thetaSeries_sup_dual_eq_sum]
  exact re_thetaSeries_mono le_sup_right hτ

omit [IsZLattice ℝ L] in
/-- On the imaginary axis, if `L` is not integral and `A_L` is finite, the theta series of `L^∨`
is strictly smaller than `∑_{γ ∈ A_L} θ_γ`: then `L^∨ < L + L^∨`, so `L + L^∨` contributes
strictly more positive Gaussian terms than `L^∨`. -/
theorem re_thetaSeries_dual_lt_sum_of_not_isIntegral [Fintype (DiscriminantGroup L)]
    (h : ¬ IsIntegral L) {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries (dual L) τ).re <
      (∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ).re := by
  have : DiscreteTopology (L ⊔ dual L : Submodule ℤ E) :=
    discreteTopology_sup_dual_of_finite_discriminantGroup
  have hlt : dual L < L ⊔ dual L :=
    lt_of_le_of_ne le_sup_right fun heq ↦
      h (isIntegral_iff_le_dual.mpr (le_sup_left.trans_eq heq.symm))
  rw [← thetaSeries_sup_dual_eq_sum]
  exact re_thetaSeries_strictMono hlt hτ

omit [IsZLattice ℝ L] in
/-- At any point of the imaginary axis, the dual coset decomposition
`Θ_{L^∨}(τ) = ∑_{γ ∈ A_L} θ_γ(τ)` holds if and only if `L` is integral. -/
theorem thetaSeries_dual_apply_eq_sum_iff_isIntegral [Fintype (DiscriminantGroup L)] {τ : ℍ}
    (hτ : τ.re = 0) :
    thetaSeries (dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ ↔
      IsIntegral L :=
  ⟨fun heq ↦ by_contra fun hni ↦
      (re_thetaSeries_dual_lt_sum_of_not_isIntegral hni hτ).ne (congrArg Complex.re heq),
    fun h ↦ h.thetaSeries_dual_eq_sum τ⟩

omit [IsZLattice ℝ L] in
/-- For a discrete subgroup `L` with finite discriminant group `A_L`, the dual coset decomposition
`Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` holds if and only if `L` is integral. -/
theorem thetaSeries_dual_eq_sum_iff_isIntegral [Fintype (DiscriminantGroup L)] :
    thetaSeries (dual L) = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ ↔ IsIntegral L :=
  ⟨fun h ↦ (thetaSeries_dual_apply_eq_sum_iff_isIntegral UpperHalfPlane.I_re).mp <| by
      simpa using congrFun h UpperHalfPlane.I,
    fun h ↦ funext fun τ ↦ by simpa using h.thetaSeries_dual_eq_sum τ⟩

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

end ZLattice
