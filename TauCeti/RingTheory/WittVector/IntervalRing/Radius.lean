/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.IntervalRing.Basic
public import TauCeti.RingTheory.WittVector.RadiusRing
public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty

/-!
# Radius rings inside interval rings

For `0 < ρ₁ ≤ ρ₂ < 1`, the radius ring with Gauss norm `λ_{ρ₂}` embeds isometrically in
the interval ring with norm `max(λ_{ρ₁}, λ_{ρ₂})`. On Witt vectors, and hence after inverting
`[ϖ]`, the maximum is `λ_{ρ₂}`. Completing therefore gives a closed coefficient ring in
the interval ring. Adjoining the inverse of `p` to this coefficient ring gives a dense subring.
These maps are the coefficient maps used in restricted-series presentations of interval rings.
Quantitatively, every element of `𝕎 O[1/(p [ϖ])]` is a polynomial in `p⁻¹` with coefficients in
`𝕎 O[1/[ϖ]]` whose weighted norms are bounded by its interval norm (Kedlaya's estimate (4.9.1)).
If `v(ϖ)^b ≤ ρ₁^a` with `a ≠ 0`, evaluation at `[ϖ]^b/p^a` defines a continuous map from the
one-variable restricted series ring over the radius ring with dense image in the interval ring.
The constructions use Mathlib’s `UniformSpace.Completion.mapRingHom` and
`TauCeti.Huber.existsUnique_continuous_ringHom_weightedRestrictedSubring`.

The parameters are the coefficient weights in `λ_ρ(∑ [xₙ] pⁿ) = supₙ v(xₙ) ρⁿ`; they
are related to Kedlaya's parameter `r` by `ρ = p^(-1/r)`.

## Main results

* `TauCeti.WittVector.RadiusRing.isometry_toIntervalRing` : the radius ring embeds isometrically
  in the interval ring.
* `TauCeti.WittVector.RadiusRing.existsUnique_continuous_denseRange_restrictedSeries_toIntervalRing`
  : evaluation at `[ϖ]^b/p^a` out of `A^{ρ₂}⟨X⟩` has dense image.
* `TauCeti.WittVector.IntervalLocalization.exists_sum_eq_mul_inv_pow` : Kedlaya's estimate (4.9.1).

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016,
  arXiv:1410.5160v3, Definitions 2.4 and 4.2 and Lemma 4.9.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti.WittVector

open _root_.WittVector UniformSpace

variable (p : ℕ) [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K]
  [CharP O p] [PerfectRing O p] {v : Valuation K ℝ≥0} {ϖ : O}
  (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1)
  {ρ₁ ρ₂ : ℝ≥0} (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)

local notation "𝕎" => _root_.WittVector p
local notation "A₀" => RadiusLocalization p hv hϖ hϖ' hρ₂
local notation "B₀" => IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂
local notation "A" => RadiusRing p hv hϖ hϖ' hρ₂
local notation "B" => IntervalRing p hv hϖ hϖ' hρ₁ hρ₂

namespace RadiusLocalization

/-- The map `W(O)[1/[ϖ]] → W(O)[1/(p[ϖ])]`, before completion. -/
def toIntervalLocalization : A₀ →ₐ[𝕎 O] B₀ :=
  IsLocalization.Away.liftAlgHom (teichmuller p ϖ)
    (f := Algebra.ofId (𝕎 O) B₀)
    (IntervalLocalization.isUnit_algebraMap_teichmuller p hv hϖ hϖ' hρ₁ hρ₂)

private theorem gaussValuationAway_toIntervalLocalization_mk'
    {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1) (x : 𝕎 O)
    (s : Submonoid.powers (teichmuller p ϖ)) :
    gaussValuationAway p hv hϖ ρ hρ B₀
        (toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ (IsLocalization.mk' A₀ x s)) =
      gaussValuation p hv ρ hρ.2 x * (gaussValuation p hv ρ hρ.2 s)⁻¹ := by
  -- Normalize the coefficient homomorphism so the lift's unit proof has the expected type.
  dsimp only [toIntervalLocalization, Algebra.ofId]
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift,
    IsLocalization.lift_mk', map_mul, map_units_inv]
  simp [IsUnit.coe_liftRight, gaussValuationAway_algebraMap]

/-- For ordered radii, inverting `[ϖ]` preserves the radius norm in the interval norm. -/
@[simp]
theorem norm_toIntervalLocalization (hρ : ρ₁ ≤ ρ₂) (x : A₀) :
    ‖toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ x‖ = ‖x‖ := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (teichmuller p ϖ)) x
  obtain ⟨n, hn : teichmuller p ϖ ^ n = s⟩ := s.property
  rw [IntervalLocalization.norm_def, norm_mk',
    gaussValuationAway_toIntervalLocalization_mk' p hv hϖ hϖ' hρ₁ hρ₂ hρ₁,
    gaussValuationAway_toIntervalLocalization_mk' p hv hϖ hϖ' hρ₁ hρ₂ hρ₂]
  simp only [← hn, map_pow, gaussValuation_teichmuller, NNReal.coe_mul, NNReal.coe_inv]
  apply max_eq_right
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast gaussValuation_mono hv hρ₁.2 hρ₂.2 hρ a) (by positivity)

/-- For ordered radii, the map of uncompleted localisations is an isometry. -/
theorem isometry_toIntervalLocalization (hρ : ρ₁ ≤ ρ₂) :
    Isometry (toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :=
  (AddMonoidHomClass.isometry_iff_norm _).mpr
    (norm_toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ hρ)

end RadiusLocalization

namespace IntervalLocalization

/-- **Kedlaya's estimate (4.9.1)** in the normalisation `λ_ρ(p) = ρ`. Every
`d ∈ 𝕎 O[1/(p [ϖ])]` is a polynomial `∑_{i ≤ m} zᵢ p^(-(m - i))` in `p⁻¹` whose coefficients `zᵢ`
lie in `𝕎 O[1/[ϖ]]` and satisfy `λ_{ρ₂}(zᵢ) ρ₁^(-(m - i)) ≤ λ_{[ρ₁, ρ₂]}(d)`. Writing
`d = y / (p [ϖ]) ^ m` and splitting `y = ∑_{i < m} [yᵢ] pⁱ + pᵐ b`, one takes `zᵢ = [yᵢ] / [ϖ] ^ m`
for `i < m` and `zₘ = b / [ϖ] ^ m`. -/
theorem exists_sum_eq_mul_inv_pow (d : B₀) :
    ∃ (m : ℕ) (z : ℕ → A₀),
      (∀ i ≤ m, ‖z i‖ * (ρ₁ : ℝ)⁻¹ ^ (m - i) ≤ ‖d‖) ∧
      d = ∑ i ∈ Finset.range (m + 1),
        RadiusLocalization.toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ (z i) *
          ((isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂).unit⁻¹ : B₀ˣ) ^ (m - i) := by
  obtain ⟨⟨y, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers ((p : 𝕎 O) * teichmuller p ϖ)) d
  obtain ⟨m, hm⟩ := s.2
  obtain ⟨b, hb⟩ := exists_eq_sum_teichmullerCoeff_add_pow_mul y m
  set t : ℕ → 𝕎 O := fun i ↦ if i < m then teichmuller p (y.teichmullerCoeff i) else b
  let w : Submonoid.powers (teichmuller p ϖ) := ⟨teichmuller p ϖ ^ m, m, rfl⟩
  refine ⟨m, fun i ↦ IsLocalization.mk' A₀ (t i) w, fun i hi ↦ ?_, ?_⟩
  · set V := v (algebraMap O K ϖ)
    have hs {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1) :
        gaussValuation p hv ρ hρ.2 (s : 𝕎 O) = (ρ * V) ^ m := by
      rw [← hm]
      simp [V]
    have hw : gaussValuation p hv ρ₂ hρ₂.2 (w : 𝕎 O) = V ^ m := by
      simp [w, V]
    rw [RadiusLocalization.norm_mk', norm_def, gaussValuationAway_mk', gaussValuationAway_mk',
      hs hρ₁, hs hρ₂, hw]
    -- the bound holds in `ℝ≥0`
    suffices h : gaussValuation p hv ρ₂ hρ₂.2 (t i) * (V ^ m)⁻¹ * ρ₁⁻¹ ^ (m - i) ≤
        max (gaussValuation p hv ρ₁ hρ₁.2 y * ((ρ₁ * V) ^ m)⁻¹)
          (gaussValuation p hv ρ₂ hρ₂.2 y * ((ρ₂ * V) ^ m)⁻¹) by
      exact_mod_cast h
    rcases hi.lt_or_eq with hi | rfl
    · -- a coefficient `[yᵢ] / [ϖ] ^ m` with `i < m`
      simp only [t, hi, ite_true, gaussValuation_teichmuller]
      refine le_max_of_le_left ?_
      calc v (algebraMap O K (y.teichmullerCoeff i)) * (V ^ m)⁻¹ * ρ₁⁻¹ ^ (m - i)
          = v (algebraMap O K (y.teichmullerCoeff i)) * ρ₁ ^ i * ((ρ₁ * V) ^ m)⁻¹ := by
            have : ρ₁ ^ i ≠ 0 := pow_ne_zero _ hρ₁.1.ne'
            rw [inv_pow, mul_pow, ← pow_mul_pow_sub ρ₁ hi.le]
            field_simp
        _ ≤ _ := by gcongr; exact le_gaussValuation hv hρ₁.2 y i
    · -- the tail coefficient `b / [ϖ] ^ m`, using `λ_{ρ₂}(b) ρ₂ᵐ ≤ λ_{ρ₂}(y)`
      simp only [t, lt_self_iff_false, ite_false, Nat.sub_self, pow_zero, mul_one]
      refine le_max_of_le_right ?_
      rw [mul_pow, mul_inv, ← mul_assoc]
      gcongr
      exact (le_mul_inv_iff₀ (pow_pos hρ₂.1 i)).mpr
        (gaussValuation_mul_pow_le_of_eq_sum_add_pow_mul hv hρ₂.2 hb)
  · -- multiply by the unit `s = (p [ϖ]) ^ m`: both sides become `y`
    set g := RadiusLocalization.toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂
    set u := (isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂).unit
    have hgw (x : 𝕎 O) : g (IsLocalization.mk' A₀ x w) *
        algebraMap (𝕎 O) B₀ (teichmuller p ϖ) ^ m = algebraMap (𝕎 O) B₀ x := by
      simpa only [w, map_mul, map_pow, AlgHom.commutes] using
        congrArg g (IsLocalization.mk'_spec A₀ x w)
    have hpu : (p : B₀) * (u⁻¹ : B₀ˣ) = 1 := by
      simp [u]
    have hpow (i : ℕ) (hi : i ≤ m) :
        (p : B₀) ^ m * ((u⁻¹ : B₀ˣ) : B₀) ^ (m - i) = (p : B₀) ^ i := by
      rw [← pow_mul_pow_sub (p : B₀) hi, mul_assoc, ← mul_pow, hpu, one_pow, mul_one]
    have hterm (i : ℕ) (hi : i ≤ m) :
        g (IsLocalization.mk' A₀ (t i) w) * ((u⁻¹ : B₀ˣ) : B₀) ^ (m - i) *
            algebraMap (𝕎 O) B₀ (s : 𝕎 O) =
          algebraMap (𝕎 O) B₀ (t i * (p : 𝕎 O) ^ i) := by
      rw [← hm]
      simp only [map_mul, map_pow, map_natCast]
      linear_combination ((u⁻¹ : B₀ˣ) : B₀) ^ (m - i) * (p : B₀) ^ m * hgw (t i) +
        algebraMap (𝕎 O) B₀ (t i) * hpow i hi
    apply (IsLocalization.map_units B₀ s).mul_right_cancel
    rw [IsLocalization.mk'_spec, Finset.sum_mul,
      Finset.sum_congr rfl fun i hi ↦ hterm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
      ← map_sum, Finset.sum_range_succ]
    conv_lhs => rw [hb]
    congr 2
    · exact Finset.sum_congr rfl fun i hi ↦ by simp [t, Finset.mem_range.mp hi]
    · simp [t, mul_comm]

end IntervalLocalization

namespace RadiusRing

/-- The coefficient map from the radius ring with weight `ρ₂` to the interval ring with
endpoint weights `ρ₁ ≤ ρ₂`, obtained by completing the localisation map. -/
def toIntervalRing (hρ : ρ₁ ≤ ρ₂) : A →+* B :=
  Completion.mapRingHom (RadiusLocalization.toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂).toRingHom
    (RadiusLocalization.isometry_toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ hρ).continuous

/-- The completed coefficient map agrees with the map of uncompleted localisations. -/
@[simp]
theorem toIntervalRing_coe (hρ : ρ₁ ≤ ρ₂) (x : A₀) :
    toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ (x : A) =
      (RadiusLocalization.toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ x : B₀) :=
  Completion.mapRingHom_coe
    (RadiusLocalization.isometry_toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ hρ).continuous x

/-- The completed coefficient map respects the maps from Witt vectors. -/
@[simp]
theorem toIntervalRing_algebraMap (hρ : ρ₁ ≤ ρ₂) (x : 𝕎 O) :
    toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ (algebraMap (𝕎 O) A x) = algebraMap (𝕎 O) B x := by
  simp [Completion.algebraMap_def]

/-- The radius ring embeds isometrically in the interval ring. -/
theorem isometry_toIntervalRing (hρ : ρ₁ ≤ ρ₂) :
    Isometry (toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ) :=
  Completion.isometry_mapRingHom
    (RadiusLocalization.isometry_toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ hρ)

/-- The coefficient map preserves norms. -/
@[simp]
theorem norm_toIntervalRing (hρ : ρ₁ ≤ ρ₂) (x : A) :
    ‖toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ x‖ = ‖x‖ :=
  (AddMonoidHomClass.isometry_iff_norm _).mp
    (isometry_toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ) x

/-- The image of the radius ring is a closed coefficient ring in the interval ring. -/
theorem isClosed_range_toIntervalRing (hρ : ρ₁ ≤ ρ₂) :
    IsClosed (Set.range (toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ)) :=
  (isometry_toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ).isClosedEmbedding.isClosed_range

/-- Every element of the uncompleted interval localisation becomes a coefficient after
multiplication by a power of `p`. -/
theorem exists_coe_mul_natCast_pow_eq_toIntervalRing (hρ : ρ₁ ≤ ρ₂) (x : B₀) :
    ∃ (n : ℕ) (a : A),
      (x : B) * (p : B) ^ n = toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ a := by
  obtain ⟨n, y, hy⟩ := IsLocalization.Away.surj ((p : 𝕎 O) * teichmuller p ϖ) x
  let t : Submonoid.powers (teichmuller p ϖ) :=
    ⟨teichmuller p ϖ ^ n, ⟨n, rfl⟩⟩
  let a := IsLocalization.mk' A₀ y t
  have ha : RadiusLocalization.toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ a *
      algebraMap (𝕎 O) B₀ (teichmuller p ϖ) ^ n = algebraMap (𝕎 O) B₀ y := by
    simpa only [t, map_mul, map_pow, AlgHom.commutes] using
      congrArg (RadiusLocalization.toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)
        (IsLocalization.mk'_spec A₀ y t)
  have hx : x * (p : B₀) ^ n =
      RadiusLocalization.toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ a := by
    apply ((IntervalLocalization.isUnit_algebraMap_teichmuller
      p hv hϖ hϖ' hρ₁ hρ₂).pow n).mul_right_cancel
    rw [ha]
    simpa only [map_mul, map_natCast, mul_pow, mul_assoc] using hy
  refine ⟨n, (a : A), ?_⟩
  rw [toIntervalRing_coe]
  have h := congrArg (Completion.coeRingHom : B₀ →+* B) hx
  simp only [map_mul, map_pow, map_natCast] at h
  -- Mathlib does not expose an application lemma for `Completion.coeRingHom`.
  convert h using 1 <;> rfl

/-- Adjoining `p⁻¹` to the image of the radius ring gives a dense subring of the interval
ring. Equivalently, elements which become coefficients after multiplication by some power
of `p` are dense. -/
theorem dense_setOf_exists_mul_natCast_pow_eq_toIntervalRing (hρ : ρ₁ ≤ ρ₂) :
    Dense {x : B | ∃ (n : ℕ) (a : A),
      x * (p : B) ^ n = toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ a} := by
  apply Dense.mono _ (Completion.denseRange_coe (α := B₀))
  rintro _ ⟨x, rfl⟩
  exact exists_coe_mul_natCast_pow_eq_toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ x

open TauCeti.Huber in
/-- Evaluation at `[ϖ]^b/p^a`, for `a ≠ 0`, gives a unique continuous map with dense image from
the one-variable restricted series ring over the radius ring to the interval ring, whenever the
variable has norm at most one at both endpoints, that is, `v(ϖ)^b ≤ ρ₁^a`. Uniqueness requires
only continuity and the coefficient and variable equations. -/
theorem existsUnique_continuous_denseRange_restrictedSeries_toIntervalRing (hρ : ρ₁ ≤ ρ₂)
    {a b : ℕ} (ha : a ≠ 0) (hab : v (algebraMap O K ϖ) ^ b ≤ ρ₁ ^ a) :
    ∃ ψ : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A))
        isWeightFamily_one_weight →+* B,
      Continuous ψ ∧ DenseRange ψ ∧
      (∀ c, ψ (weightedC _ isWeightFamily_one_weight c) =
        toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ c) ∧
      ψ (weightedX _ isWeightFamily_one_weight 0) * (p : B) ^ a =
        algebraMap (𝕎 O) B (teichmuller p ϖ ^ b) ∧
      ∀ g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A))
          isWeightFamily_one_weight →+* B,
        Continuous g →
        (∀ c, g (weightedC _ isWeightFamily_one_weight c) =
          toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ c) →
        g (weightedX _ isWeightFamily_one_weight 0) * (p : B) ^ a =
          algebraMap (𝕎 O) B (teichmuller p ϖ ^ b) → g = ψ := by
  let f := toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ
  have hpa : IsUnit ((p : B) ^ a) :=
    (isPseudoUniformizer_natCast_intervalRing p hv hϖ hϖ' hρ₁ hρ₂).isUnit.pow a
  obtain ⟨z, hz, hzp⟩ := exists_norm_le_one_algebraMap_eq_mul_intervalRing p hv hϖ hϖ' hρ₁ hρ₂
    (y := (p : 𝕎 O) ^ a) (x := teichmuller p ϖ ^ b)
    (by simpa using (IntervalLocalization.isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂).pow a)
    (by simpa using hab) (by simpa using hab.trans (pow_le_pow_left₀ zero_le hρ a))
  have hz' : IsPowerBounded z :=
    (isPowerBounded_iff_norm_le_one_intervalRing p hv hϖ hϖ' hρ₁ hρ₂).mpr hz
  obtain ⟨ψ, ⟨hψ, hC, hX⟩, huniq⟩ := existsUnique_continuous_ringHom_weightedRestrictedSubring
    isWeightFamily_one_weight
    (isometry_toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ).continuous.continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded f (fun _ : Fin 1 ↦ z)).mpr
      (fun _ ↦ hz'))
  have hzp' : z * (p : B) ^ a = algebraMap (𝕎 O) B (teichmuller p ϖ ^ b) := by
    simpa using hzp.symm
  refine ⟨ψ, hψ, ?_, hC, (congrArg (fun x : B ↦ x * (p : B) ^ a) (hX 0)).trans hzp', ?_⟩
  · -- The image contains every coefficient divided by a power of `p`.
    apply Dense.mono _ (dense_setOf_exists_mul_natCast_pow_eq_toIntervalRing
      p hv hϖ hϖ' hρ₁ hρ₂ hρ)
    rintro x ⟨m, c, hc⟩
    have hu : IsUnit (algebraMap (𝕎 O) A (teichmuller p ϖ ^ b)) := by
      rw [Completion.algebraMap_def, map_pow]
      -- Relate the completion coercion to its bundled ring homomorphism.
      convert ((RadiusLocalization.isUnit_algebraMap_teichmuller p hv hϖ hϖ' hρ₂).pow b).map
        (Completion.coeRingHom : A₀ →+* A) using 1
      rfl
    let u := hu.unit
    -- `c / p ^ m = c p ^ ((a - 1) m) [ϖ] ^ (-b m) z ^ m`, since `z p ^ a = [ϖ] ^ b`.
    refine ⟨weightedC _ isWeightFamily_one_weight
      (c * (p : A) ^ ((a - 1) * m) * (↑u⁻¹ : A) ^ m) *
        weightedX _ isWeightFamily_one_weight 0 ^ m, ?_⟩
    apply ((isPseudoUniformizer_natCast_intervalRing
      p hv hϖ hϖ' hρ₁ hρ₂).isUnit.pow m).mul_right_cancel
    rw [hc]
    simp only [map_mul, map_pow, map_natCast, hC, hX]
    have hm : (p : B) ^ ((a - 1) * m) * (p : B) ^ m = ((p : B) ^ a) ^ m := by
      rw [← pow_add, ← pow_mul, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr ha)]
    have hc' : c * (↑u⁻¹ : A) ^ m * algebraMap (𝕎 O) A (teichmuller p ϖ ^ b) ^ m = c := by
      rw [mul_assoc, ← mul_pow]
      simp only [u, hu.val_inv_mul, one_pow, mul_one]
    calc f c * (p : B) ^ ((a - 1) * m) * f ↑u⁻¹ ^ m * z ^ m * (p : B) ^ m
        = f c * f ↑u⁻¹ ^ m * (z * (p : B) ^ a) ^ m := by
          rw [mul_pow z, ← hm]; ring
      _ = f c := by
          rw [hzp', ← toIntervalRing_algebraMap p hv hϖ hϖ' hρ₁ hρ₂ hρ (teichmuller p ϖ ^ b)]
          simpa only [map_mul, map_pow] using congrArg f hc'
  · intro g hg hgC hgX
    apply huniq g
    refine ⟨hg, hgC, fun i ↦ ?_⟩
    rw [Subsingleton.elim i 0]
    exact hpa.mul_right_cancel (hgX.trans hzp'.symm)

end RadiusRing

end TauCeti.WittVector
