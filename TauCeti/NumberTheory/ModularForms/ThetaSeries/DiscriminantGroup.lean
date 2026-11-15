/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.DiscriminantCharacter
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Translation
import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Algebra.Module.Submodule.Quotient
import TauCeti.Algebra.Module.ZLattice.Summable
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

Whenever `A_L` is finite (in arbitrary dimension, without discreteness or fullness), the second
isomorphism theorem identifies `A_L` with `(L ⊔ L^∨) ⧸ L` and the sum of the coset theta series
over `A_L` is `Θ_{L ⊔ L^∨}` (`ZLattice.thetaSeries_sup_dual_eq_sum`). When `L` is integral
(`L ≤ L^∨`), `L ⊔ L^∨ = L^∨` and this gives `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ`
(`ZLattice.IsIntegral.thetaSeries_dual_eq_sum`). Conversely, in finite dimension with finite `A_L`,
`Θ_{L^∨}(τ) = ∑_{γ ∈ A_L} θ_γ(τ)` at any point `τ` on the imaginary axis holds if and only if `L`
is integral (`ZLattice.thetaSeries_dual_eq_sum_iff_of_re_eq_zero`,
`ZLattice.thetaSeries_dual_eq_sum_iff`): when `L` is discrete and not integral, `L^∨ < L ⊔ L^∨` and
`Re Θ_{L^∨}(τ) < Re ∑_{γ ∈ A_L} θ_γ(τ)` (`ZLattice.re_thetaSeries_dual_lt_re_sum_thetaCosetClass`),
while when `L` is not discrete, `L^∨` is still discrete (`|A_L| < ∞`) so `Θ_{L^∨}(τ) ≠ 0 = ∑ θ_γ`.
For instance, for `L = ½ ℤ ⊆ ℝ` the dual `L^∨ = 2 ℤ` lies strictly inside `L`, `A_L` is trivial,
and `Θ_{2ℤ}(i) ≠ Θ_{½ℤ}(i)`.

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
* `ZLattice.thetaSeries_sup_dual_eq_sum`: `Θ_{L ⊔ L^∨} = ∑_{γ ∈ A_L} θ_γ` whenever `A_L` is finite.
* `ZLattice.IsIntegral.thetaSeries_dual_eq_sum`,
  `ZLattice.thetaSeries_dual_eq_sum_iff_of_re_eq_zero`, `ZLattice.thetaSeries_dual_eq_sum_iff`:
  `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` holds for integral `L`, and in finite dimension characterizes
  integrality.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 2.
-/

public section

open Complex
open scoped Real ModularForm RealInnerProductSpace UpperHalfPlane

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

/-! ### Coset decomposition over the discriminant group -/

section CosetDecomposition

variable {L}

/-- If `DiscriminantGroup L` is finite and `δ ∈ dual L`, shifting `γ` by `δ` preserves absolute
summability of `θ_{γ+L}(τ)`: with `d = |DiscriminantGroup L| ≥ 1`, `d • δ ∈ L` and every `v ∈ L`
satisfies either `‖γ + v‖² - d ‖δ‖² ≤ ‖γ + δ + v‖²` or `‖γ + (v + d • δ)‖² ≤ ‖γ + δ + v‖²`. -/
private theorem summable_norm_thetaCoset_add_of_mem_dual [Finite (DiscriminantGroup L)]
    {γ δ : E} (hδ : δ ∈ dual L) {τ : ℍ}
    (hs : Summable fun v : L ↦ ‖cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ)‖) :
    Summable fun v : L ↦ ‖cexp (π * I * (‖γ + δ + (v : E)‖ ^ 2 : ℝ) * τ)‖ := by
  set d := Nat.card (DiscriminantGroup L)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.card_pos
  have hdL : d • δ ∈ L := card_nsmul_mem_of_mem_dual hδ
  have hdom : Summable fun v : L ↦ Real.exp (π * τ.im * d * ‖δ‖ ^ 2) *
      ‖cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ)‖ +
      ‖cexp (π * I * (‖γ + ((v + ⟨d • δ, hdL⟩ : L) : E)‖ ^ 2 : ℝ) * τ)‖ :=
    (hs.mul_left _).add ((Equiv.addRight (⟨d • δ, hdL⟩ : L)).summable_iff.mpr hs)
  refine .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun v ↦ ?_) hdom
  let w : E := γ + (v : E)
  have hw : γ + δ + (v : E) = δ + w := by dsimp only [w]; abel
  have hwd : γ + ((v + ⟨d • δ, hdL⟩ : L) : E) = w + (d : ℝ) • δ := by
    dsimp only [w]
    rw [AddMemClass.coe_add, Nat.cast_smul_eq_nsmul, add_assoc]
  have hpy : 0 < π * τ.im := mul_pos Real.pi_pos τ.im_pos
  rcases le_or_gt 0 (2 * ⟪δ, w⟫ + ((d : ℝ) + 1) * ‖δ‖ ^ 2) with hge | hlt
  · have hsq : ‖w‖ ^ 2 - (d : ℝ) * ‖δ‖ ^ 2 ≤ ‖δ + w‖ ^ 2 := by linarith [norm_add_sq_real δ w]
    refine le_add_of_le_of_nonneg ?_ (norm_nonneg _)
    rw [hw, norm_exp_pi_mul_I_mul_ofReal_mul, norm_exp_pi_mul_I_mul_ofReal_mul,
      UpperHalfPlane.coe_im, ← Real.exp_add, Real.exp_le_exp]
    nlinarith
  · have hsq : ‖w + (d : ℝ) • δ‖ ^ 2 ≤ ‖δ + w‖ ^ 2 := by
      have h1 := norm_add_sq_real w ((d : ℝ) • δ)
      rw [real_inner_smul_right, real_inner_comm δ w, norm_smul,
        Real.norm_of_nonneg (Nat.cast_nonneg d), mul_pow] at h1
      nlinarith [norm_add_sq_real δ w]
    refine le_add_of_nonneg_of_le (by positivity) ?_
    rw [hw, hwd, norm_exp_pi_mul_I_mul_ofReal_mul, norm_exp_pi_mul_I_mul_ofReal_mul,
      UpperHalfPlane.coe_im, Real.exp_le_exp]
    nlinarith

/-- When `DiscriminantGroup L` is finite, `Θ_{L ⊔ L^∨}(τ)` is absolutely summable if and only if
`Θ_L(τ)` is: `(L ⊔ L^∨) ⧸ L` is finite and each fiber has the same summability as `L`. -/
private theorem summable_norm_thetaSeries_sup_dual_iff [Finite (DiscriminantGroup L)] (τ : ℍ) :
    (Summable fun v : (L ⊔ dual L : Submodule ℤ E) ↦
      ‖cexp (π * I * (‖(v : E)‖ ^ 2 : ℝ) * τ)‖) ↔
    Summable fun v : L ↦ ‖cexp (π * I * (‖(v : E)‖ ^ 2 : ℝ) * τ)‖ := by
  refine ⟨fun hs ↦ (hs.comp_injective
    (Submodule.inclusion_injective (le_sup_left : L ≤ L ⊔ dual L))).congr (fun _ ↦ rfl),
    fun hs0 ↦ ?_⟩
  let M : Submodule ℤ E := L ⊔ dual L
  let Q := M ⧸ L.submoduleOf M
  have : Finite Q := Finite.of_equiv _ (discriminantGroupEquivSupQuotient L).toEquiv
  refine (summable_partition (fun _ ↦ norm_nonneg _)
    (s := fun q : Q ↦ Submodule.Quotient.mk ⁻¹' {q})
    (fun v ↦ ⟨_, rfl, fun _ h ↦ h.symm⟩)).mpr ⟨fun q ↦ ?_, Summable.of_finite⟩
  obtain ⟨u, hu, x, hx, hux⟩ := Submodule.mem_sup.mp (Quotient.out q).2
  have hsx := summable_norm_thetaCoset_add_of_mem_dual (γ := 0) hx
    (hs0.congr fun v ↦ by rw [zero_add])
  have hsz : Summable fun v : L ↦
      ‖cexp (π * I * (‖((Quotient.out q : M) : E) + (v : E)‖ ^ 2 : ℝ) * τ)‖ := by
    refine (Equiv.addLeft (⟨-u, neg_mem hu⟩ : L)).summable_iff.mp (hsx.congr fun v ↦ ?_)
    have hv : ((Quotient.out q : M) : E) + ((Equiv.addLeft (⟨-u, neg_mem hu⟩ : L) v : L) : E) =
        0 + x + (v : E) := by
      rw [Equiv.coe_addLeft, AddMemClass.coe_add, Subtype.coe_mk, ← hux, zero_add, add_comm u x,
        add_assoc, add_neg_cancel_left]
    simp only [Function.comp_def, hv]
  exact (L.quotientFiberEquivOfLe le_sup_left q).summable_iff.mp (hsz.congr fun _ ↦ by simp)

/-- **Coset decomposition over the discriminant group.** For any `ℤ`-submodule `L` with finite
discriminant group `A_L = L^∨ ⧸ (L ∩ L^∨)`, the sum of the coset theta series over `A_L` is the
theta series of `L ⊔ L^∨`: `Θ_{L ⊔ L^∨} = ∑_{γ ∈ A_L} θ_γ`. -/
theorem thetaSeries_sup_dual_eq_sum [Fintype (DiscriminantGroup L)] (τ : ℍ) :
    thetaSeries (L ⊔ dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ := by
  by_cases hs0 : Summable fun v : L ↦ ‖cexp (π * I * (‖(v : E)‖ ^ 2 : ℝ) * τ)‖
  · have hsM : Summable fun v : (L ⊔ dual L : Submodule ℤ E) ↦
        cexp (π * I * (‖(v : E)‖ ^ 2 : ℝ) * τ) :=
      ((summable_norm_thetaSeries_sup_dual_iff τ).mpr hs0).of_norm
    have hfib : HasSum (fun q : (L ⊔ dual L : Submodule ℤ E) ⧸ L.submoduleOf (L ⊔ dual L) ↦
        thetaCoset L ((Quotient.out q : (L ⊔ dual L : Submodule ℤ E)) : E) τ)
        (thetaSeries (L ⊔ dual L) τ) := by
      rw [← funext (fun q ↦ tsum_thetaTerm_fiber (L ⊔ dual L) le_sup_left q τ), thetaSeries_apply]
      exact hsM.hasSum.tsum_fiberwise _
    rw [← hfib.tsum_eq, ← (discriminantGroupEquivSupQuotient L).toEquiv.tsum_eq, tsum_fintype]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    induction γ using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearEquiv.coe_toEquiv, discriminantGroupEquivSupQuotient_mk, thetaCosetClass_mk]
      refine congrFun (thetaCoset_eq_of_sub_mem L ?_) τ
      have hout := (Submodule.Quotient.eq _).mp
        (Submodule.Quotient.mk_out
          (Submodule.Quotient.mk (p := L.submoduleOf (L ⊔ dual L))
            ⟨(x : E), Submodule.mem_sup_right x.2⟩))
      rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        AddSubgroupClass.coe_sub] at hout
  · have hM0 : thetaSeries (L ⊔ dual L) τ = 0 := by
      rw [thetaSeries_apply]
      exact tsum_eq_zero_of_not_summable fun hsM ↦
        hs0 ((summable_norm_thetaSeries_sup_dual_iff τ).mp hsM.norm)
    rw [hM0, eq_comm]
    refine Finset.sum_eq_zero fun γ _ ↦ ?_
    induction γ using Submodule.Quotient.induction_on with
    | H x =>
      rw [thetaCosetClass_mk, thetaCoset_apply]
      refine tsum_eq_zero_of_not_summable fun hsx ↦ ?_
      have h0 := summable_norm_thetaCoset_add_of_mem_dual (γ := (x : E)) (neg_mem x.2) hsx.norm
      exact hs0 (h0.congr fun v ↦ by rw [add_neg_cancel, zero_add])

/-- For an integral lattice `L`, the theta series of the dual lattice is the sum of the coset theta
series over the finite discriminant group `L^∨ ⧸ L`: `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ`. The discriminant
group of an integral full lattice is finite (`IsIntegral.finite_discriminantGroup`), so a `Fintype`
instance is always available there. -/
theorem IsIntegral.thetaSeries_dual_eq_sum (h : IsIntegral L) [Fintype (DiscriminantGroup L)]
    (τ : ℍ) : thetaSeries (dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ := by
  rw [← thetaSeries_sup_dual_eq_sum, sup_eq_right.mpr (isIntegral_iff_le_dual.mp h)]

variable [FiniteDimensional ℝ E]

/-- When a discrete subgroup `L` in a finite-dimensional space is not integral, `L^∨` is a strict
sublattice of `L ⊔ L^∨`, so on the imaginary axis
`Re Θ_{L^∨}(τ) < Re (∑_{γ ∈ A_L} θ_γ(τ))`. -/
theorem re_thetaSeries_dual_lt_re_sum_thetaCosetClass [DiscreteTopology L] (h : ¬ IsIntegral L)
    [Fintype (DiscriminantGroup L)] {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries (dual L) τ).re < (∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ).re := by
  have := discreteTopology_sup_dual_of_finite_discriminantGroup (L := L)
  have hlt : dual L < L ⊔ dual L :=
    lt_of_le_of_ne le_sup_right fun heq ↦
      h (isIntegral_iff_le_dual.mpr (le_sup_left.trans heq.symm.le))
  rw [← thetaSeries_sup_dual_eq_sum]
  exact re_thetaSeries_lt_re_thetaSeries (L ⊔ dual L) hlt hτ

/-- In a finite-dimensional space, at any point `τ` on the imaginary axis,
`Θ_{L^∨}(τ) = ∑_{γ ∈ A_L} θ_γ(τ)` holds if and only if `L` is integral. -/
theorem thetaSeries_dual_eq_sum_iff_of_re_eq_zero [Fintype (DiscriminantGroup L)] {τ : ℍ}
    (hτ : τ.re = 0) :
    thetaSeries (dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ ↔ IsIntegral L := by
  refine ⟨fun heq ↦ ?_, fun h ↦ h.thetaSeries_dual_eq_sum τ⟩
  by_cases hL : DiscreteTopology L
  · exact by_contra fun hni ↦
      (re_thetaSeries_dual_lt_re_sum_thetaCosetClass hni hτ).ne (congrArg re heq)
  · have : DiscreteTopology (dual L) := discreteTopology_dual_of_finite_discriminantGroup
    refine (thetaSeries_ne_zero_of_re_eq_zero (dual L) hτ (heq.trans ?_)).elim
    refine Finset.sum_eq_zero fun γ _ ↦ ?_
    induction γ using Submodule.Quotient.induction_on with
    | H x =>
      rw [thetaCosetClass_mk, thetaCoset_eq_zero_of_forall_not_summable L x fun y hy hs ↦
        hL (discreteTopology_of_summable_exp_neg_mul_norm_add_sq L x (by positivity) hs),
        Pi.zero_apply]

/-- In a finite-dimensional space, the dual decomposition `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` holds across
the upper half-plane if and only if `L` is integral. -/
theorem thetaSeries_dual_eq_sum_iff [Fintype (DiscriminantGroup L)] :
    (∀ τ : ℍ, thetaSeries (dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ) ↔
      IsIntegral L :=
  ⟨fun h ↦ (thetaSeries_dual_eq_sum_iff_of_re_eq_zero UpperHalfPlane.I_re).mp (h _),
    fun h ↦ h.thetaSeries_dual_eq_sum⟩

end CosetDecomposition

/-! ### Full lattices -/

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

end ZLattice
