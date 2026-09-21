/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

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
* `TauCeti.EisensteinSeries.weightedEisensteinSeries_eq_tsum_eisensteinSeries`: the series in
  terms of Mathlib's coprime-pair `eisensteinSeries`, through the `gammaSet` decomposition by gcd
  and residue class.
* `TauCeti.EisensteinSeries.weightedEisensteinSeries_smul`,
  `TauCeti.EisensteinSeries.weightedEisensteinSeries_add`: linearity in the weight.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.2, §4.5.
* The uniform-convergence argument follows Mathlib's
  `EisensteinSeries.eisensteinSeries_tendstoLocallyUniformly` (Chris Birkbeck and David Loeffler),
  while the holomorphy and boundedness arguments follow
  `EisensteinSeries.eisensteinSeriesSIF_mdifferentiable` and
  `EisensteinSeries.isBoundedAtImInfty_eisensteinSeriesSIF` (Chris Birkbeck), with the sum over
  a coprime residue class replaced by a sum over all pairs with bounded weights.
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
  let e : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    Matrix.toLinearEquivRight'OfInv
      (M := ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      (M' := (γ : Matrix (Fin 2) (Fin 2) ℤ))
      (by simp [Matrix.adjugate_mul]) (by simp [Matrix.mul_adjugate])
  rw [← e.symm.tsum_eq]
  refine tsum_congr fun v ↦ ?_
  simp only [e, ← intCast_comp_vecMul]
  congr 2
  exact e.apply_symm_apply v

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

/-- The coprime integer pairs are the disjoint union of the coprime pairs in each residue class. -/
private def gammaSetOneSigmaEquiv (N : ℕ) :
    gammaSet 1 1 0 ≃ Σ a : Fin 2 → ZMod N, gammaSet N 1 a where
  toFun y := ⟨(↑) ∘ y.1, y.1, rfl, y.2.2⟩
  invFun p := ⟨p.2.1, Subsingleton.elim _ _, p.2.2.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨a, x, rfl, hx⟩
    rfl

/-- **The weighted series in terms of Mathlib's `eisensteinSeries`.** Writing each nonzero pair as
its gcd `r` times a coprime pair and sorting the coprime pairs by residue class,
`∑_v W(v) (v₀ z + v₁)^(-k) = ∑_r r^(-k) ∑_a W(r a) eisensteinSeries a k z`. -/
theorem weightedEisensteinSeries_eq_tsum_eisensteinSeries (hk : 3 ≤ k) (z : ℍ) :
    weightedEisensteinSeries W k z =
      ∑' r : ℕ, ((r : ℂ) ^ k)⁻¹ * ∑ a, W (r • a) * eisensteinSeries a k z := by
  have hS := (summable_norm_weightedEisensteinSummand W hk z).of_norm
  have hσ := gammaSetDivGcdSigmaEquiv.symm.summable_iff.mpr hS
  rw [Function.comp_def] at hσ
  -- sort all pairs by their gcd `r`
  rw [weightedEisensteinSeries, ← gammaSetDivGcdSigmaEquiv.symm.tsum_eq, hσ.tsum_sigma]
  refine tsum_congr fun r ↦ ?_
  simp only [gammaSetDivGcdSigmaEquiv_symm_eq]
  rcases eq_or_ne r 0 with rfl | hr
  · have hk0 : k ≠ 0 := by omega
    have h0 (x : gammaSet 1 0 0) : x.1 = 0 := by
      simpa using gammaSet_eq_gcd_mul_divIntMap x.2
    simp [h0, eisSummand, zero_zpow _ hk0, zero_zpow _ (neg_ne_zero.mpr hk0)]
  have : NeZero r := ⟨hr⟩
  -- write each pair of gcd `r` as `r` times a coprime pair
  rw [← (gammaSetDivGcdEquiv r).symm.tsum_eq]
  have hmul (y : gammaSet 1 1 0) : ((gammaSetDivGcdEquiv r).symm y).1 = r • y.1 := by
    conv_lhs => rw [gammaSet_eq_gcd_mul_divIntMap ((gammaSetDivGcdEquiv r).symm y).2]
    rw [← gammaSetDivGcdEquiv_eq, Equiv.apply_symm_apply]
  simp_rw [hmul]
  -- the factor `r` comes out of the summand as `r^(-k)`
  have hsmul (x : Fin 2 → ℤ) :
      W ((↑) ∘ (r • x)) * eisSummand k (r • x) z =
        ((r : ℂ) ^ k)⁻¹ * (W (r • ((↑) ∘ x)) * eisSummand k x z) := by
    have hcast : ((↑) ∘ (r • x) : Fin 2 → ZMod N) = r • ((↑) ∘ x) := by
      ext i
      simp
    rw [hcast]
    simp only [eisSummand, Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast,
      mul_assoc, ← mul_add, mul_zpow, zpow_neg]
    ring
  simp_rw [hsmul, tsum_mul_left]
  congr 1
  -- sort the coprime pairs by residue class
  have hsub := ((summable_norm_weightedEisensteinSummand (fun a ↦ W (r • a)) hk z).subtype
    (gammaSet 1 1 0)).of_norm
  have hσ' := (gammaSetOneSigmaEquiv N).symm.summable_iff.mpr hsub
  rw [Function.comp_def] at hσ'
  rw [← (gammaSetOneSigmaEquiv N).symm.tsum_eq, hσ'.tsum_sigma, tsum_fintype]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [eisensteinSeries, ← tsum_mul_left]
  refine tsum_congr fun x ↦ ?_
  simp [gammaSetOneSigmaEquiv, x.2.1]

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

@[simp]
lemma weightedEisensteinSeriesMF_zero (hk : 3 ≤ k) :
    weightedEisensteinSeriesMF (0 : (Fin 2 → ZMod N) → ℂ) hk = 0 := by
  ext z
  simp [weightedEisensteinSeries]

@[simp]
lemma weightedEisensteinSeriesMF_add (hk : 3 ≤ k) (W' : (Fin 2 → ZMod N) → ℂ) :
    weightedEisensteinSeriesMF (W + W') hk =
      weightedEisensteinSeriesMF W hk + weightedEisensteinSeriesMF W' hk := by
  ext z
  exact congrFun (weightedEisensteinSeries_add W hk W') z

@[simp]
lemma weightedEisensteinSeriesMF_smul (hk : 3 ≤ k) (c : ℂ) :
    weightedEisensteinSeriesMF (c • W) hk = c • weightedEisensteinSeriesMF W hk := by
  ext z
  exact congrFun (weightedEisensteinSeries_smul W k c) z

end TauCeti.EisensteinSeries
