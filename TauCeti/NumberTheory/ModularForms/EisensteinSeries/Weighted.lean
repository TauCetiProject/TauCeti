/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
public import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Eisenstein series weighted by a function of residues

For a level `N`, a weight `k` and a function `W : (Fin 2 → ZMod N) → ℂ`, the series
`∑_{v ∈ ℤ²} W(v mod N) · (v₀ z + v₁)^(-k)`.

Mathlib's `eisensteinSeries` sums over the *coprime* pairs in one residue class. The Eisenstein
series with character of Diamond–Shurman §4.5 are instead built from the sums
`G_k^{a}(z) = ∑_{v ≡ a mod N} (v₀ z + v₁)^(-k)` over *all* pairs in a residue class, weighted by
character values; every such combination is the series of this file for a suitable `W`
(`G_k^{a}` itself is the indicator function of `a`). Allowing an arbitrary weight keeps the
analytic input in one place.

For `3 ≤ k` the series converges absolutely and locally uniformly, and slashing by
`γ ∈ SL(2, ℤ)` only changes the weight, to `a ↦ W (a ᵥ* γ⁻¹)`
(`weightedEisensteinSeries_slash_apply`). Hence the series is a modular form of level `Γ(N)`
(`weightedEisensteinSeriesMF`); the character is then read off from the transformation of the
weight under `Γ₀(N)`.

## Main definitions

* `TauCeti.EisensteinSeries.weightedEisensteinSeries`: the weighted series, as a function.
* `TauCeti.EisensteinSeries.weightedEisensteinSeriesSIF`: it is slash invariant of level `Γ(N)`.
* `TauCeti.EisensteinSeries.weightedEisensteinSeriesMF`: for `3 ≤ k`, a modular form of level
  `Γ(N)`.

## Main results

* `TauCeti.EisensteinSeries.weightedEisensteinSeries_slash_apply`: the slash action on the series.
* `TauCeti.EisensteinSeries.weightedEisensteinSeries_smul`,
  `TauCeti.EisensteinSeries.weightedEisensteinSeries_add`: linearity in the weight.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.2, §4.5.
* The analytic arguments follow Mathlib's
  `EisensteinSeries.eisensteinSeries_tendstoLocallyUniformly`,
  `EisensteinSeries.eisensteinSeriesSIF_mdifferentiable` and
  `EisensteinSeries.isBoundedAtImInfty_eisensteinSeriesSIF` (Chris Birkbeck), with the sum over a
  coprime residue class replaced by a sum over all pairs with bounded weights.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Complex Filter Set
open EisensteinSeries

open scoped MatrixGroups Topology Manifold

namespace TauCeti.EisensteinSeries

variable {N : ℕ} (W : (Fin 2 → ZMod N) → ℂ) (k : ℤ)

/-- The Eisenstein series of weight `k` weighted by `W : (Fin 2 → ZMod N) → ℂ`:
`∑' v : ℤ², W (v mod N) * (v 0 * z + v 1) ^ (-k)`. -/
def weightedEisensteinSeries (z : ℍ) : ℂ :=
  ∑' v : Fin 2 → ℤ, W ((↑) ∘ v) * eisSummand k v z

lemma weightedEisensteinSeries_def (z : ℍ) :
    weightedEisensteinSeries W k z = ∑' v : Fin 2 → ℤ, W ((↑) ∘ v) * eisSummand k v z :=
  (rfl)

/-- The series is linear in the weight: scalar multiples. -/
lemma weightedEisensteinSeries_smul (c : ℂ) :
    weightedEisensteinSeries (c • W) k = c • weightedEisensteinSeries W k := by
  ext z
  simp [weightedEisensteinSeries, mul_assoc, tsum_mul_left]

/-- Reduction modulo `N` commutes with right multiplication by `γ ∈ SL(2, ℤ)`. -/
lemma intCast_comp_vecMul (v : Fin 2 → ℤ) (γ : SL(2, ℤ)) :
    ((↑) : ℤ → ZMod N) ∘ (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) =
      ((↑) ∘ v) ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  ext i
  simp [vecMul, dotProduct]

/-- Right multiplication by `γ ∈ SL(2, ℤ)`, as a permutation of `ℤ²`. -/
private def vecMulEquiv (γ : SL(2, ℤ)) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun v := v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)
  invFun v := v ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  left_inv v := by simp [vecMul_vecMul, Matrix.mul_adjugate]
  right_inv v := by simp [vecMul_vecMul, Matrix.adjugate_mul]

/-- **The slash action on a weighted Eisenstein series.** Slashing by `γ ∈ SL(2, ℤ)` replaces
the weight `W` by `a ↦ W (a ᵥ* γ⁻¹)`. -/
theorem weightedEisensteinSeries_slash_apply (γ : SL(2, ℤ)) :
    weightedEisensteinSeries W k ∣[k] γ =
      weightedEisensteinSeries (fun a ↦
        W (a ᵥ* (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) k := by
  ext1 z
  simp_rw [SL_slash_apply, zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z), weightedEisensteinSeries,
    eisSummand_SL2_apply, mul_left_comm _ (_ ^ k), tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  rw [← (vecMulEquiv γ).symm.tsum_eq]
  refine tsum_congr fun v ↦ ?_
  simp only [vecMulEquiv, Equiv.coe_fn_symm_mk, ← intCast_comp_vecMul]
  congr 2
  simp [vecMul_vecMul, Matrix.adjugate_mul]

/-- The weighted Eisenstein series as a slash invariant form of level `Γ(N)`: an element of
`Γ(N)` reduces to the identity modulo `N`, so it does not change the weight. -/
def weightedEisensteinSeriesSIF : SlashInvariantForm Γ(N) k where
  toFun := weightedEisensteinSeries W k
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ Γ(N)), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, weightedEisensteinSeries_slash_apply,
      Gamma_mem'.mp (inv_mem hA)]

@[simp]
lemma coe_weightedEisensteinSeriesSIF :
    ⇑(weightedEisensteinSeriesSIF W k) = weightedEisensteinSeries W k := (rfl)

/-! ### Analytic properties -/

variable [NeZero N]

/-- A bound for the absolute values of the weights. -/
private lemma norm_le_sum_norm (a : Fin 2 → ZMod N) : ‖W a‖ ≤ ∑ b, ‖W b‖ :=
  Finset.single_le_sum (f := fun b ↦ ‖W b‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ a)

variable {k}

/-- The weighted series is absolutely convergent for `3 ≤ k`. -/
lemma summable_norm_weightedEisensteinSummand (hk : 3 ≤ k) (z : ℍ) :
    Summable fun v : Fin 2 → ℤ ↦ ‖W ((↑) ∘ v) * eisSummand k v z‖ :=
  ((summable_norm_eisSummand hk z).mul_left (∑ b, ‖W b‖)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun v ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_le_sum_norm W _) (norm_nonneg _)

/-- The series is linear in the weight: sums. -/
lemma weightedEisensteinSeries_add (hk : 3 ≤ k) (W' : (Fin 2 → ZMod N) → ℂ) :
    weightedEisensteinSeries (W + W') k =
      weightedEisensteinSeries W k + weightedEisensteinSeries W' k := by
  ext z
  simp only [weightedEisensteinSeries, Pi.add_apply, add_mul]
  exact (summable_norm_weightedEisensteinSummand W hk z).of_norm.tsum_add
    (summable_norm_weightedEisensteinSummand W' hk z).of_norm

/-- The partial sums of the weighted series converge locally uniformly on `ℍ`. -/
theorem weightedEisensteinSeries_tendstoLocallyUniformly (hk : 3 ≤ k) :
    TendstoLocallyUniformly
      (fun s : Finset (Fin 2 → ℤ) ↦ (∑ v ∈ s, W ((↑) ∘ v) * eisSummand k v ·))
      (weightedEisensteinSeries W k ·) atTop := by
  have hk' : (2 : ℝ) < k := by norm_cast
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, weightedEisensteinSeries]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  refine (tendstoUniformlyOn_tsum (hu := ((summable_one_div_norm_rpow hk').mul_left
    (r ⟨⟨A, B⟩, hB⟩ ^ (-k : ℝ))).mul_left (∑ b, ‖W b‖)) (fun v z hz ↦ ?_)).mono HABK
  rw [norm_mul]
  refine mul_le_mul (norm_le_sum_norm W _) ?_ (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  simpa only [eisSummand, one_div, ← zpow_neg, norm_zpow, ← Real.rpow_intCast,
    Int.cast_neg] using summand_bound_of_mem_verticalStrip (by positivity) v hB hz

/-- The weighted series is holomorphic on `ℍ`. -/
theorem weightedEisensteinSeries_mdifferentiable (hk : 3 ≤ k) :
    MDiff (weightedEisensteinSeriesSIF W k) := by
  intro τ
  suffices DifferentiableAt ℂ (↑ₕweightedEisensteinSeriesSIF W k) τ.1 by
    convert!
      MDifferentiableAt.comp τ (DifferentiableAt.mdifferentiableAt this) τ.mdifferentiable_coe
    exact funext fun z ↦ (comp_ofComplex (weightedEisensteinSeriesSIF W k) z).symm
  refine DifferentiableOn.differentiableAt ?_ (isOpen_upperHalfPlaneSet.mem_nhds τ.2)
  have hloc : TendstoLocallyUniformlyOn (fun s : Finset (Fin 2 → ℤ) ↦
      ↑ₕ(fun z : ℍ ↦ ∑ v ∈ s, W ((↑) ∘ v) * eisSummand k v z))
        (↑ₕ(weightedEisensteinSeriesSIF W k)) atTop {z : ℂ | 0 < z.im} := by
    rw [← upperHalfPlaneSet, ← range_coe, ← image_univ]
    apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _
      (OpenPartialHomeomorph.continuousOn_symm _)
    · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
      exact weightedEisensteinSeries_tendstoLocallyUniformly W hk
    · simp only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.top_eq_univ,
        mapsTo_range_iff, Set.mem_univ, forall_const]
  exact hloc.differentiableOn (Eventually.of_forall fun s ↦ DifferentiableOn.fun_sum
    fun v _ ↦ (eisSummand_extension_differentiableOn k v).const_mul _) isOpen_upperHalfPlaneSet

/-- Every `SL(2, ℤ)`-translate of the weighted series is bounded at `i∞`. -/
theorem isBoundedAtImInfty_weightedEisensteinSeriesSIF (hk : 3 ≤ k) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (weightedEisensteinSeriesSIF W k ∣[k] γ) := by
  set W' : (Fin 2 → ZMod N) → ℂ :=
    fun a ↦ W (a ᵥ* (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))
  have hk' : (2 : ℝ) < k := by norm_cast
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨(∑ b, ‖W' b‖) * ∑' v : Fin 2 → ℤ, r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖v‖ ^ (-k), 2,
    fun z hz ↦ ?_⟩
  obtain ⟨n, hn⟩ := ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N)
  rw [coe_weightedEisensteinSeriesSIF, weightedEisensteinSeries_slash_apply,
    ← coe_weightedEisensteinSeriesSIF,
    ← SlashInvariantForm.T_zpow_width_invariant N k n (weightedEisensteinSeriesSIF W' k) z,
    coe_weightedEisensteinSeriesSIF, weightedEisensteinSeries,
    ← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm (summable_norm_weightedEisensteinSummand W' hk _)).trans ?_
  have hsum : Summable fun v : Fin 2 → ℤ ↦ r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖v‖ ^ (-k) := by
    exact_mod_cast (summable_one_div_norm_rpow hk').mul_left (r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k))
  refine (summable_norm_weightedEisensteinSummand W' hk _).tsum_le_tsum (fun v ↦ ?_)
    (hsum.mul_left _)
  rw [norm_mul]
  refine mul_le_mul (norm_le_sum_norm W' _) ?_ (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  simp_rw [eisSummand, norm_zpow]
  exact_mod_cast summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le v two_pos
    (verticalStrip_anti_right N hz hn)

/-- **The weighted Eisenstein series is a modular form** of weight `k ≥ 3` and level `Γ(N)`. -/
def weightedEisensteinSeriesMF (hk : 3 ≤ k) : ModularForm Γ(N) k where
  toSlashInvariantForm := weightedEisensteinSeriesSIF W k
  holo' := weightedEisensteinSeries_mdifferentiable W hk
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ _ ↦ isBoundedAtImInfty_weightedEisensteinSeriesSIF W hk γ

@[simp]
lemma coe_weightedEisensteinSeriesMF (hk : 3 ≤ k) :
    ⇑(weightedEisensteinSeriesMF W hk) = weightedEisensteinSeries W k := (rfl)

end TauCeti.EisensteinSeries
